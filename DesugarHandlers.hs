{- TODO:

  * Check that there are no redundant clauses in handlers (those that
    don't match up with any of the declared operations are just
    ignored).

  * Generate type signatures for operation functions.

  * Sugar for return clauses?

  * Sugar for handler extension?

  * McBride handlers?

  * Closure conversion? Perhaps not feasible using Template Haskell.
 -}

{- Examples -}
{-
  State operations:

    [operation|Get s : s|]
    [operation|Put s : s -> ()|]

  These elaborate to:

    data Get s = Get
    type instance Return (Get s) = s
    get = doOp Get

    newtype Put s = Put s
    type instance Return (Put s) = ()
    put s = doOp (Put s)

  If one of the parameters to an operation has a fancy type then it is
  sometimes necessary to add a type annotation on the generated
  operation function. This is perfectly possible. We might improve
  usability by outputting a type-signature (as it should always be
  fully known anyway).

  A non-forwarding state handler:

    [handler|StateHandler s a : s -> a handles {Get s, Put s} where
      clause (StateHandler s) Get k = k (StateHandler s) s
      clause _ (Put s) k = k (StateHandler s) ()
    |]

  This elaborates to:

    newtype StateHandler s a = StateHandler s
    type instance Result (StateHandler s a) = a
    instance (StateHandler s a `Handles` Get s) where
      clause (StateHandler s) Get k = k (StateHandler s) s
    instance (StateHandler s a `Handles` Put s) where
      clause _ (Put s) k = k (StateHandler s) ()

  A forwarding state handler:

    [handler|forward h.FStateHandler s a : s -> a handles {Get s, Put s} where
      clause (FStateHandler s) Get k = k (FStateHandler s) s
      clause _ (Put s) k = k (FStateHandler s) ()
    |]

  This prepends h to the list of FStateHandler's type variables yielding:

    newtype FStateHandler h s a = FStateHandler s
    type instance Result (FStateHandler h s a) = a
    instance (FStateHandler h s a `Handles` Get s) where
      clause (FStateHandler s) Get k = k (FStateHandler s) s
    instance (FStateHandler h s a `Handles` Put s) where
      clause _ (Put s) k = k (FStateHandler s) ()

  and additionally generates the following forwarding instances:

    instance (h `Handles` op) => (PVHandler h a `Handles` op) where
      clause h op k = doOp op >>= k h
    instance (h `PolyHandles` op) => (PVHandler h a `PolyHandles` op) where
      polyClause h op k = polyDoOp op >>= k h

  A polymorphic operation:

    [operation|Failure : forall a.a|]

  This elaborates to:

    data Failure a = Failure
    type instance Return (Failure a) = a
    failure = doPolyOp Failure

  A polymorphic handler:

    [handler|MaybeHandler a : Maybe a handles {Failure} where
       polyClause _ Failure k = Nothing
    |]

  This elaborates to

    newtype MaybeHandler a = MaybeHandler
    type instance Result (MaybeHandler a) = a
    instance (MaybeHandler a `PolyHandles` Failure) where
      polyClause _ Failure k = Nothing

  The collection of operations in the curly braces includes only those
  operations whoses clauses are defined up-front. Further clauses can
  be added later using explicit instances of the Handles type
  class. Sometimes we have to do this when we require an explicit
  class constraint.

  Any clauses that reference operations not declared in curly braces
  are currently ignored.

  We might consider adapting the sugar to inline handler parameters as
  curried arguments to the clauses and the continuation. For instance:

    [handler|StateHandler s a : s -> a handles {Get s, Put s} where
      clause s Get     k = k s s
      clause s (Put s) k = k s ()
    |]

  would elaborate to:

    newtype StateHandler s a = StateHandler s
    type instance Result (StateHandler s a) = a
    instance (StateHandler s a `Handles` Get s) where
      clause (StateHandler s) Get k' = k s s
        where
          k s = k' (StateHandler s)
    instance (StateHandler s a `Handles` Put s) where
      clause _ (Put s) k' = k s ()
        where
          k s = k' (StateHandler s)

  We might also generate a wrapper function for the handler:

    stateHandler comp s r = handle comp (StateHandler s) r

  Doing something like this for McBride handlers might make sense.

  If we have a wrapper function, then we could add sugar for a fixed
  return clause which is always supplied to the handler by the wrapper
  function.

-}

{-# LANGUAGE FlexibleContexts #-}

module DesugarHandlers where

import ParseHandlers(parseOpDef, parseHandlerDef, HandlerDef)

import Language.Haskell.TH
import Language.Haskell.TH.Quote

import qualified Language.Haskell.Exts.Parser as Exts
import Language.Haskell.Exts.Extension (Extension(..))

--import Language.Haskell.SyntaxTrees.ExtsToTH
import qualified Language.Haskell.Meta.Parse as MetaParse
import Language.Haskell.Meta.Syntax.Translate (toType)

import Data.Char(toUpper,toLower)

{- Handler definitions -}
handler = QuasiQuoter { quoteExp = undefined, quotePat = undefined,
                        quoteType = undefined, quoteDec = handlerParser}

handlerParser :: String -> Q [Dec]
handlerParser s = return (makeHandlerDef (parseHandlerDef s))

makeHandlerDef :: HandlerDef -> [Dec]
makeHandlerDef (h, name, ts, (sig, polySig), r, cs) = [handlerType, resultInstance] ++ opClauses ++ polyClauses ++ forwardClauses ++ [handlerFun]
    where
      cname = mkName (let (c:cs) = name in toUpper(c) : cs)
      fname = mkName (let (c:cs) = name in toLower(c) : cs)

      (tyvars, constraint) =
          (case h of
             Just (h, Nothing) -> ([mkName h] ++ map mkName ts, Nothing)
             Just (h, Just c)  -> ([mkName h] ++ map mkName ts, Just c)
             Nothing           -> (map mkName ts, Nothing))

      (args, result) = splitFunType (parseType r)
      
      handlerType =
          DataD [] cname
                    (map PlainTV tyvars)
                    [NormalC cname (map (\arg -> (NotStrict, arg)) args)]
                    []
      resultInstance =
          TySynInstD (mkName "Result")
                         [appType (ConT cname) (map VarT tyvars)] result
      ds = parseDecs cs
      opClauses = map (clauseInstance False) sig
      polyClauses = map (clauseInstance True) polySig

      handlerFun =
        FunD fname [Clause (handlerArgs ++ [VarP comp]) body retDecs]
          where
            xs = vars 0 args
            vars i []       = []
            vars i (_:args) = mkName ("x" ++ show i) : vars (i+1) args
            ret = mkName "ret"
            handle = mkName "handle"
            handlerArgs = map VarP xs
            comp = mkName "comp"
            body = NormalB (appExp
                            (VarE handle)
                            [VarE comp,
                             VarE ret,
                             appExp (ConE cname) (map VarE xs)])

      forwardClauses =
          case h of
            Nothing -> []
            Just _  -> [forwardInstance False, forwardInstance True]

      funName p (FunD f _) = p(nameBase f)

      opDecs = filter (funName (/= "ret")) ds
      retDecs  =
        case filter (funName (== "ret")) ds of
          []      -> error "No return clause"
          retDecs -> retDecs

      lookupDecs :: String -> Dec -> [Dec]
      lookupDecs opName (d@(FunD clauseName clauses)) =
          case filter (matchClause opName) clauses of
            [] -> []
            cs -> [FunD clauseName cs]

      matchClause :: String -> Clause -> Bool
      matchClause opName (Clause (p:_) _ _) = delve p
          where
            delve (ParensP p) = delve p
            delve (ConP op _) = opName == nameBase op

      monoHandles = mkName "Handles"
      polyHandles = mkName "PolyHandles"
      happ = ConT cname `appType` map VarT tyvars

      ctx =
        case constraint of
          Nothing -> []
          Just s | ForallT [] ctx _ <- parseType (s ++ " => ()") -> ctx

      clauseInstance :: Bool -> (String, [String]) -> Dec
      clauseInstance poly (opName, tvs) = InstanceD ctx (AppT (AppT handles happ) op) decs
          where
            op = ConT (mkName opName) `appType` map (VarT . mkName) tvs
            decs = concat [lookupDecs opName d | d <- opDecs]
            handles = ConT (if poly then polyHandles else monoHandles)

      forwardInstance poly =
          InstanceD pre (AppT (AppT (ConT handles) happ) op) decs
              where
                op = VarT (mkName "op")
                pre = [ClassP handles [VarT (head tyvars), op]]
                (handles, decs) =
                    if poly then
                        (polyHandles, parseDecs "polyClause op k h = polyDoOp op >>= (\\x -> k x h)")
                    else
                        (monoHandles, parseDecs "clause op k h = doOp op >>= (\\x -> k x h)")    

{- Operation definitions -}
operation = QuasiQuoter { quoteExp = undefined, quotePat = undefined,
                          quoteType = undefined, quoteDec = opParser}


opParser :: String -> Q [Dec]
opParser s = makeOpDefs (parseOpDef s)

makeOpDefs :: (Maybe String, String, [String], String) -> Q [Dec]
makeOpDefs (poly, name, ts, sig) = return [opType, returnInstance, opFun]
    where
      f = parseType sig

      cname = mkName (let (c:cs) = name in toUpper(c) : cs)
      fname = mkName (let (c:cs) = name in toLower(c) : cs)
      
      (lift, tyvars) =
          case poly of
            Just a ->
              (mkName "polyDoOp", map mkName ts ++ [mkName a])
            Nothing ->
              (mkName "doOp", map mkName ts)
      (args, result) = splitFunType f
      opType =
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
      returnInstance =
          TySynInstD (mkName "Return")
                         [appType (ConT cname) (map VarT tyvars)] result
      xs = vars 0 args
      vars i []       = []
      vars i (_:args) = mkName ("x" ++ show i) : vars (i+1) args
      opFun =
          FunD fname
               [Clause (map VarP xs)
                (NormalB (AppE
                          (VarE lift)
                          (appExp (ConE cname) (map VarE xs)))) []]

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
           (Exts.ParseMode "" [FlexibleContexts, TypeOperators] True True Nothing)
           s))

parseDecs :: String -> [Dec]
parseDecs s | Right ds <- MetaParse.parseDecs s = ds

parseExp :: String -> Exp
parseExp s | Right e <- MetaParse.parseExp s = e

appExp f []     = f
appExp f (e:es) = appExp (AppE f e) es

appType f []     = f
appType f (t:ts) = appType (AppT f t) ts

splitFunType :: Type -> ([Type], Type)
splitFunType f = (reverse ts, t)
    where
      (t : ts) = split [] f

      split :: [Type] -> Type -> [Type]
      split ts (AppT (AppT ArrowT t) body) = split (t:ts) body
      -- HACK: GHC.Type.() is what gets parsed for "()", and that
      -- leads to kinding problems. We should really look for units
      -- elsewhere in types.  This might be a bug in the parseType
      -- function.
      split ts (ConT name) | nameBase name == "()" = (TupleT 0:ts)
      split ts t = (t:ts)
