{- TODO:

  * Check that there are no redundant clauses in handlers (those that
    don't match up with any of the declared operations are just
    ignored).

  * Sugar for handler extension?

  * McBride handlers?

  * Closure conversion? Perhaps not feasible using Template Haskell.
 -}

{- Examples -}
{-
  State operations:

    [operation|Get s :: s|]
    [operation|Put s :: s -> ()|]

  These elaborate to:

    data Get s = Get
    type instance Return (Get s) = s
    get :: forall h s.(h `Handles` Get) => Comp h s
    get = doOp Get

    newtype Put s = Put s
    type instance Return (Put s) = ()
    put :: forall h s :: (h `Handles` Put) => s -> Comp h ()
    put s = doOp (Put s)

  A non-forwarding state handler:

    [handler|
      StateHandler s a :: s -> a handles {Get s, Put s} where
        Get      k s -> k s s
        Put s    k _ -> k () s
        Return x   _ -> x
    |]

  This elaborates to:

    newtype StateHandler s a = StateHandler s
    type instance Result (StateHandler s a) = a
    instance (StateHandler s a `Handles` Get s) where
      clause Get     k' (StateHandler s) = k s s
        where
          k v s = k' v (StateHandler s)
    instance (StateHandler s a `Handles` Put s) where
      clause (Put s) k' _                = k () s
        where
          k v s = k' v (StateHandler s)
    stateHandler s comp = handle comp (\x _ -> x) (StateHandler s)

  A forwarding state handler:

    [handler|
      forward h.FStateHandler s a :: s -> a handles {Get s, Put s} where
        Get      k s -> k s s
        Put s    k _ -> k () s
        Return x   _ -> return x
    |]

  This prepends h to the list of FStateHandler's type variables yielding:

    newtype FStateHandler h s a = FStateHandler s
    type instance Result (FStateHandler h s a) = a
    instance (FStateHandler h s a `Handles` Get s) where
      clause Get     k' (FStateHandler s) = k s s
        where
          k v s = k' v (FStateHandler s)
    instance (FStateHandler h s a `Handles` Put s) where
      clause (Put s) k' _                 = k () s
        where
          k v s = k' v (FStateHandler s)
    fStateHandler s comp = handle comp (\x _ -> return x) (FStateHandler s)

  and additionally generates the following forwarding instances:

    instance (h `Handles` op) => (PVHandler h a `Handles` op) where
      clause op k h = doOp op >>= (\x -> k x h)
    instance (h `PolyHandles` op) => (PVHandler h a `PolyHandles` op) where
      polyClause op k h = polyDoOp op >>= (\x -> k x h)

  A polymorphic operation:

    [operation|Failure :: forall a.a|]

  This elaborates to:

    data Failure a = Failure
    type instance Return (Failure a) = a
    failure :: forall h a.(h `Handles` Failure a) => Comp h a
    failure = doPolyOp Failure

  A handler for a polymorphic operation:

    [handler|
       MaybeHandler a :: Maybe a polyhandles {Failure} where
         Failure  k -> Nothing
         Return x   -> Just x
    |]

  This elaborates to

    newtype MaybeHandler a = MaybeHandler
    type instance Result (MaybeHandler a) = a
    instance (MaybeHandler a `PolyHandles` Failure) where
      polyClause Failure k = Nothing
    maybeHandler comp = handle comp (\x _ -> Just) MaybeHandler

  The collection of operations in the curly braces includes only those
  operations whoses clauses are defined up-front. Further clauses can
  be added later using explicit instances of the Handles type
  class.

  Any clauses that reference operations not declared in curly braces
  are currently ignored.

-}

{-# LANGUAGE FlexibleContexts #-}

module DesugarHandlers where

import ParseHandlers(parseOpDef, parseHandlerDef, HandlerDef, OpDef, QuantifierKind(..), OpKind(..))

import Language.Haskell.TH
import Language.Haskell.TH.Quote

import qualified Language.Haskell.Exts.Parser as Exts
import Language.Haskell.Exts.Extension (Extension(..))

--import Language.Haskell.SyntaxTrees.ExtsToTH
import qualified Language.Haskell.Meta.Parse as MetaParse
import Language.Haskell.Meta.Syntax.Translate (toType)

import Data.List
import Data.Char(toUpper,toLower)

{- Handler definitions -}
handler = QuasiQuoter { quoteExp = undefined, quotePat = undefined,
                        quoteType = undefined, quoteDec = handlerParser}

handlerParser :: String -> Q [Dec]
handlerParser s = makeHandlerDef (parseHandlerDef s)

makeHandlerDef :: HandlerDef -> Q [Dec]
makeHandlerDef (h, name, ts, sigs, r, cs) =
  do 
    let sig     = [s | (Plain, ss) <- sigs, s <- ss]
        polySig = [s | (Poly,  ss) <- sigs, s <- ss]
        monoSig = [s | (Mono,  ss) <- sigs, s <- ss]
        
        cname = mkName (let (c:cs) = name in toUpper(c) : cs)
        fname = mkName (let (c:cs) = name in toLower(c) : cs)
        
        (args, result') = splitFunType True (parseType (r ++ " -> ()"))
        (tyvars, constraint, result) =
          case h of
            Just (h, c) -> ([h'] ++ map mkName ts, c, result)
              where
                h' = mkName h
                result = appType (ConT (mkName "Comp")) [VarT h', result']
            Nothing     -> (map mkName ts, Nothing, result')
        
        plainHandles = mkName "Handles"
        polyHandles  = mkName "PolyHandles"
        monoHandles  = mkName "MonoHandles"
        happ = ConT cname `appType` map VarT tyvars
        
        handlerType =
          DataD [] cname
                    (map PlainTV tyvars)
                    [NormalC cname (map (\arg -> (NotStrict, arg)) args)]
                    []
        resultInstance =
          TySynInstD (mkName "Result")
          [appType (ConT cname) (map VarT tyvars)] result
        
        CaseE _ cases = parseExp ("case undefined of\n" ++ cs)
        
        unWrap :: Pat -> Pat
        unWrap (ParensP p) = unWrap p
        unWrap p           = p
        
        delve :: (String -> Bool) -> Pat -> Bool
        delve pred p | ConP op _ <- unWrap p = pred (nameBase op)
        
        matchOp :: (String -> Bool) -> Match -> Bool
        matchOp pred (Match pat _ _) = delve pred pat
        
        opCases = filter (matchOp (/= "Return")) cases
        retCases =
          case filter (matchOp (== "Return")) cases of
            []       -> error "No return clause"
            retCases -> retCases
        
        
        clauseInstance :: OpKind -> (String, [String]) -> Q Dec
        clauseInstance opKind (opName, tvs) =
          do
            let ctx =
                  case constraint of
                    Nothing -> []
                    Just s | ForallT [] ctx _ <- parseType (s ++ " => ()") -> ctx
        
                opType tvs = ConT (mkName opName) `appType` map (VarT . mkName) tvs
                handles =
                  case opKind of
                    Plain -> ConT plainHandles `appType` [happ, opType tvs]
                    Poly  -> ConT polyHandles  `appType` [happ, opType tvs]
                    Mono  -> ConT monoHandles  `appType` [happ, opType (init tvs), extra] 
                      where
                        extra = VarT (mkName (last tvs))
                
                clauseName =
                  case opKind of
                    Plain -> "clause" 
                    Poly  -> "polyClause"
                    Mono  -> "monoClause"
            
                makeClauseDecs :: [Match] -> Q [Dec]
                makeClauseDecs cases =
                  do
                    clauses <- mapM makeClause cases
                    return [FunD (mkName clauseName) clauses]
            
                makeClause :: Match -> Q Clause
                makeClause (Match pat body wdecs) =
                  do
                    let ConP op pats = unWrap pat
                        (opArgs, VarP k, handlerArgs) = split pats
                    k' <- newName "k"
                    let ps = [ConP op opArgs, VarP k', ConP cname handlerArgs]
                    v <- newName "v"
                    hs <- mapM (\_ -> newName "h") handlerArgs
                    let wdecs' = (FunD
                                  k
                                  [Clause ([VarP v] ++ (map VarP hs))
                                  (NormalB (appExp (VarE k') [VarE v, appExp (ConE cname) (map VarE hs)]))
                                  []]) : wdecs
                    return (Clause ps body wdecs')
        
                  
                split :: [Pat] -> ([Pat], Pat, [Pat])
                split ps = (opArgs, k, handlerArgs)
                  where
                    (k:handlerArgs) = reverse (take (length args + 1) (reverse ps))
                    opArgs          = reverse (drop (length args + 1) (reverse ps))
            
            decs <- makeClauseDecs (filter (matchOp (== opName)) opCases)          
            return (InstanceD ctx handles decs)
            
        retDec = FunD (mkName "ret") (map makeClause retCases)
          where
            makeClause :: Match -> Clause
            makeClause (Match pat body wdecs) =
              Clause ps body wdecs
                where
                  ConP op (v:hs) = unWrap pat
                  ps = [v,ConP cname hs]
        
        forwardInstance handles extra decs =
          InstanceD pre (ConT handles `appType` ([happ, op] ++ extra)) decs
            where
              op  = VarT (mkName "op")
              pre = [ClassP handles ([VarT (head tyvars), op] ++ extra)]
        
        ds = parseDecs cs
    opClauses   <- mapM (clauseInstance Plain) sig
    polyClauses <- mapM (clauseInstance Poly) polySig
    monoClauses <- mapM (clauseInstance Mono) monoSig

      -- It's tempting to try to give handler functions signatures that abstract away
      -- from the handler type. But this doesn't appear to be feasible, as the
      -- explicit handler type seems essential for working around the limitations of
      -- the GHC type system.
      --
      -- In particular there seems to be no other way of encoding
      -- subtraction of operations by a handler.
      -- 
      -- handlerFunSig =
      --   SigD fname
      --   (ForallT
      --    (map PlainTV tyvars)
      --    []
      --    (makeFunType (AppT (AppT ArrowT compType) result) args))
      --   where
      --     cs = map (opConstraint False) sig ++ map (opConstraint True) polySig
      --     compType = ForallT [PlainTV h] cs (ConT (mkName "Comp") `appType` [VarT h, result])
      --     opConstraint poly (opName, tvs) = ClassP handles [VarT h, op]
      --       where
      --         op = ConT (mkName opName) `appType` map (VarT . mkName) tvs
      --         handles = if poly then polyHandles else monoHandles
      --     h = mkName "handler" -- HACK: hopefully "handler" is fresh
      --
      -- makeFunType result [] = result
      -- makeFunType result (t:ts) = AppT (AppT ArrowT t) (makeFunType result ts)

    handlerFun <-
      do
        xs <- mapM (\_ -> newName "x") args
        let ret = mkName "ret"
            handle = mkName "handle"
            handlerArgs = map VarP xs
            comp = mkName "comp"
            body = NormalB (appExp
                            (VarE handle)
                            [VarE comp,
                             VarE ret,
                             appExp (ConE cname) (map VarE xs)])
        return (FunD fname [Clause (handlerArgs ++ [VarP comp]) body [retDec]])
          
    -- If this is a forwarding handler then generate the appropriate
    -- type class instances to forward monomorphic and polymorphic
    -- operations to the parent handler.
    forwardClauses <-
          case h of
            Nothing -> return []
            Just _  ->
              do
                let plain = parseDecs "clause     op k h = doOp op     >>= (\\x -> k x h)"
                    poly  = parseDecs "polyClause op k h = polyDoOp op >>= (\\x -> k x h)"
                    mono  = parseDecs "monoClause op k h = monoDoOp op >>= (\\x -> k x h)"
                optype <- newName "optype"
                return
                  ([forwardInstance plainHandles []            plain,
                    forwardInstance polyHandles  []            poly,
                    forwardInstance monoHandles  [VarT optype] mono])
    
    return ([handlerType, resultInstance] ++
            opClauses ++ polyClauses ++ monoClauses ++ forwardClauses ++
            [handlerFun])


{- Operation definitions -}
operation = QuasiQuoter { quoteExp = undefined, quotePat = undefined,
                          quoteType = undefined, quoteDec = opParser}


opParser :: String -> Q [Dec]
opParser s = makeOpDefs (parseOpDef s)

makeOpDefs :: OpDef -> Q [Dec]
makeOpDefs (poly, name, ts, sig) =
  do
    let (args, result) = splitFunType True (parseType (sig ++ " -> ()"))
    let f = parseType sig

    let cname = mkName (let (c:cs) = name in toUpper(c) : cs)
    let fname = mkName (let (c:cs) = name in toLower(c) : cs)
      
    let (lift, tyvars) =
          case poly of
            Just (Forall, a) ->
              (mkName "polyDoOp", map mkName ts ++ [mkName a])
            Just (Exists, a) ->
              (mkName "monoDoOp", map mkName ts ++ [mkName a])
            Nothing ->
              (mkName "doOp", map mkName ts)
    let opType =
          case args of
            [_] ->
                NewtypeD [] cname
                    (map PlainTV tyvars)
                    (NormalC cname (map (\arg -> (NotStrict, arg)) args))
                    []
            _ ->
                DataD [] cname
                    (map PlainTV tyvars)
                    [NormalC cname (map (\arg -> (NotStrict, arg)) args)]
                    []
    let returnInstance =
          TySynInstD (mkName "Return")
          [appType (ConT cname) (map VarT tyvars)] result
    xs <- mapM (\_ -> newName "x") args
    let (handles, happ) =
          case poly of
            Just (Forall, _) ->
              (ClassP (mkName "PolyHandles"),
               ConT cname `appType` map VarT (init tyvars))
            Just (Exists, _) ->
              (\xs -> ClassP (mkName "MonoHandles") (xs ++ [VarT (last tyvars)]),
               ConT cname `appType` map VarT (init tyvars))
            Nothing          ->
              (ClassP (mkName "Handles"),
               ConT cname `appType` map VarT tyvars)
    opFunSig <-
      do
        h <- newName "handler"
        let makeFunType h [] = appType (ConT (mkName "Comp")) [VarT h, result]
            makeFunType h (t:ts) = AppT (AppT ArrowT t) (makeFunType h ts)
        return (SigD fname
                (ForallT
                 (PlainTV h:map PlainTV tyvars)
                 [handles [VarT h, happ]]
                 (makeFunType h args)))
          
    let opFun = FunD fname
                [Clause (map VarP xs)
                 (NormalB (AppE
                           (VarE lift)
                           (appExp (ConE cname) (map VarE xs)))) []]
    return [opType, returnInstance, opFunSig, opFun]

{- Utilities -}

-- This doesn't quite work because it doesn't seem to have access to
-- the appropriate context. It might be a better bet eventually,
-- though, as it does parse unit types properly.
--
-- Perhaps it will work properly if we correctly lift everything into
-- the Q monad.
--
-- parseType :: String -> Type
-- parseType s =
--     case parseToTH ("undefined :: (" ++ s ++ ")") of
--       Right (SigE (VarE _) t) -> t

-- parseType :: String -> Type
-- parseType s | Right t <- MetaParse.parseType s = t 

parseType :: String -> Type
parseType s =
  toType (Exts.fromParseResult
          (Exts.parseTypeWithMode
           (Exts.ParseMode "" [MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, TypeOperators] True True Nothing)
           s))

parseDecs :: String -> [Dec]
parseDecs s | Right ds <- MetaParse.parseDecs s = ds

parseExp :: String -> Exp
parseExp s | Right e <- MetaParse.parseExp s = e

appExp f []     = f
appExp f (e:es) = appExp (AppE f e) es

appType f []     = f
appType f (t:ts) = appType (AppT f t) ts

splitFunType :: Bool -> Type -> ([Type], Type)
splitFunType dummy f = (reverse ts, massageUnit t)
    where
      (t : ts) =
          if dummy then
              -- ignore the dummy return type
              tail (split [] f)
          else
              split [] f

      -- HACK: GHC.Type.() is what gets parsed for "()", and that
      -- leads to kinding problems. We should really look for units
      -- elsewhere in types.  This might be a bug in the parseType
      -- function.
      massageUnit (ConT name) | nameBase name == "()" = TupleT 0
      massageUnit t = t

      split :: [Type] -> Type -> [Type]
      split ts (AppT (AppT ArrowT t) body) = split (t:ts) body
      split ts t = (t:ts)

