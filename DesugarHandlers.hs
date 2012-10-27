module DesugarHandlers where

import ParseHandlers(parseOpDef, parseHandlerDef, HandlerDef)

import Language.Haskell.TH
import Language.Haskell.TH.Quote

--import Language.Haskell.SyntaxTrees.ExtsToTH
import qualified Language.Haskell.Meta.Parse as MetaParse

import Data.Char(toUpper,toLower)

{- Handler definitions -}
handler = QuasiQuoter { quoteExp = undefined, quotePat = undefined,
                        quoteType = undefined, quoteDec = handlerParser}

handlerParser :: String -> Q [Dec]
handlerParser s = return (makeHandlerDef (parseHandlerDef s))

makeHandlerDef :: HandlerDef -> [Dec]
makeHandlerDef (h, name, ts, sig, r, cs) = [handlerType, resultInstance] ++ opClauses ++ forwardClauses
    where
      cname = mkName (let (c:cs) = name in toUpper(c) : cs)
      fname = mkName (let (c:cs) = name in toLower(c) : cs)

      tyvars =
          (case h of
             Just h  -> [mkName h]
             Nothing -> []) ++ map mkName ts

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
      opClauses = map clauseInstance sig

      forwardClauses =
          case h of
            Nothing -> []
            Just _  -> [forwardInstance False, forwardInstance True]

      funName s (FunD f _) = nameBase f == s

      monoDecs = filter (funName "clause") ds
      polyDecs = filter (funName "polyClause") ds

      lookupDecs :: String -> Dec -> [Dec]
      lookupDecs opName (d@(FunD clauseName clauses)) =
          case filter (matchClause opName) clauses of
            [] -> []
            cs -> [FunD clauseName cs]

      matchClause :: String -> Clause -> Bool
      matchClause opName (Clause (h:p:_) _ _) = delve p
          where
            delve (ParensP p) = delve p
            delve (ConP op _) = opName == nameBase op

      monoHandles = mkName "Handles"
      polyHandles = mkName "PolyHandles"
      happ = ConT cname `appType` map VarT tyvars

      clauseInstance :: (String, [String]) -> Dec
      clauseInstance (opName, tvs) = InstanceD [] (AppT (AppT handles happ) op) decs
          where
            op = ConT (mkName opName) `appType` map (VarT . mkName) tvs
            monos = concat [lookupDecs opName d | d <- monoDecs]
            polys = concat [lookupDecs opName d | d <- polyDecs]
            (handles, decs) =
                case (monos, polys) of
                  ([], []) -> undefined
                  (_, [])  -> (ConT monoHandles, monos)
                  ([], _)  -> (ConT polyHandles, polys)

      forwardInstance poly =
          InstanceD pre (AppT (AppT (ConT handles) happ) op) decs
              where
                op = VarT (mkName "op")
                pre = [ClassP handles [VarT (head tyvars), op]]
                (handles, decs) =
                    if poly then
                        (polyHandles, parseDecs "polyClause h op k = polyDoOp op >>= k h")
                    else
                        (monoHandles, parseDecs "clause h op k = doOp op >>= k h")    

{- Operation definitions -}
operation = QuasiQuoter { quoteExp = undefined, quotePat = undefined,
                          quoteType = undefined, quoteDec = opParser}


opParser :: String -> Q [Dec]
opParser s = makeOpDefs (parseOpDef s)

makeOpDefs :: (String, [String], String) -> Q [Dec]
makeOpDefs (name, ts, sig) = return [opType, returnInstance, opFun]
    where
      (poly, f) =
          case parseType sig of
            (ForallT [PlainTV a] [] f) -> (Just a, f)
            (ForallT _ _ f)            -> undefined
            f                          -> (Nothing, f)

      cname = mkName (let (c:cs) = name in toUpper(c) : cs)
      fname = mkName (let (c:cs) = name in toLower(c) : cs)
      
      (lift, tyvars) =
          case poly of
            Just a ->
              (mkName "polyDoOp", map mkName ts ++ [a])
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

parseType :: String -> Type
parseType s | Right t <- MetaParse.parseType s = t 

parseDecs :: String -> [Dec]
parseDecs s | Right ds <- MetaParse.parseDecs s = ds

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
