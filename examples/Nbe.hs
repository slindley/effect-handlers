{- Normalisation by evaluation for the computational lambda calculus +
   sums using handlers.

   Based on the paper 'Accumulating bindings' by Sam Lindley:

     http://homepages.inf.ed.ac.uk/slindley/papers/nbe-sums.pdf
   
   TODO: use typed HOAS as in the above paper (should be completely
   straightforward)
-}

{-# LANGUAGE TypeFamilies,
    GADTs,
    NoMonomorphismRestriction,
    RankNTypes,
    MultiParamTypeClasses,
    QuasiQuotes,
    FlexibleInstances,
    FlexibleContexts,
    OverlappingInstances,
    UndecidableInstances,
    ConstraintKinds,
    TypeOperators,
    ScopedTypeVariables #-}

import Handlers
import TopLevel
import DesugarHandlers

import Data.Maybe

type Var = String

-- FOAS
data Exp = Var Var
         | Lam Var Exp
         | App Exp Exp
         | Inl Exp
         | Inr Exp
         | Case Exp Var Exp Var Exp
         | Let Var Exp Exp

instance Show Exp where
    show (Var x) = x
    show (Lam x e) = "\\" ++ x ++ " -> " ++ show e
    show (App e e') = "(" ++ show e ++ ") (" ++ show e' ++ ")"
    show (Inl e) = "Left (" ++ show e ++ ")"
    show (Inr e) = "Right (" ++ show e ++ ")"
    show (Case e x1 e1 x2 e2) =
         "case (" ++ show e ++ ") of Left " ++
                  x1 ++ " -> (" ++ show e1 ++"); Right " ++
                  x2 ++ " -> (" ++ show e2 ++ ")"
    show (Let x e e') = "let " ++ x ++ " = (" ++ show e ++ ") in " ++ "(" ++ show e' ++ ")"

-- HOAS
class CompLam exp where
  lam :: (exp -> exp) -> exp
  app :: exp -> exp -> exp
  inl :: exp -> exp
  inr :: exp -> exp
  case_ :: exp -> (exp -> exp) -> (exp -> exp) -> exp
  let_ :: exp -> (exp -> exp) -> exp

-- the type of closed HOAS terms
type Hoas = forall exp . CompLam exp => exp

-- convert a closed HOAS term to the
-- corresponding FOAS term
hoasToExp :: Hoas -> Exp
hoasToExp v = handlePure (evalNames (unGen v))

[operation|NextName :: String|]

type GenComp h a = ([handles|h {NextName}|]) => Comp h a
newtype Gen a = Gen {unGen :: forall h.GenComp h a}

instance CompLam (Gen Exp) where
    lam f = Gen$ do x <- nextName
                    e <- unGen$ f (Gen$ return (Var x))
                    return (Lam x e)
    v1 `app` v2 = Gen$ do e1 <- unGen$ v1
                          e2 <- unGen$ v2
                          return (App e1 e2)
    inl v = Gen$ do e <- unGen$ v
                    return (Inl e)
    inr v = Gen$ do e <- unGen$ v
                    return (Inr e)
    case_ v l r = Gen$ do e <- unGen$ v
                          x1 <- nextName
                          x2 <- nextName
                          e1 <- unGen$ l (Gen$ return (Var x1))
                          e2 <- unGen$ r (Gen$ return (Var x2))
                          return (Case e x1 e1 x2 e2)
    let_ v f = Gen$ do e <- unGen$ v
                       x <- nextName
                       e' <- unGen$ f (Gen$ return (Var x))
                       return (Let x e e')

infixl 9 :+:
infixr 5 :->

-- Types
data Type :: * where
  Base :: Type
  (:->) :: Type -> Type -> Type
  (:+:) :: Type -> Type -> Type
  deriving Show

--- environments
type Env a = [(String, a)]

empty :: Env a
empty = []

extend :: [(String, a)] -> String -> a -> [(String, a)]
extend env x v = (x, v):env

[operation|Bind    :: Exp -> String|]
[operation|Binds   :: Exp -> Either String String|]

-- Morally Collect is a handler, but it's convenient to make it an
-- operation so we can abstract over it.
[operation|Collect :: ResComp Exp -> Exp|]

-- the type of an abstract residualising computation
type ResComp a = ([handles|h {NextName}|],
                  [handles|h {Bind}|], [handles|h {Binds}|],
                  [handles|h {Collect}|]) => Comp h a

-- The canonical continuation-based interpretation of residualising
-- computations.
--
-- As handlers give us direct access to the current continuation
-- anyway we don't actually need to explicitly introduce a
-- continuation monad, so the return type of the handler is just Exp.
[handler|
  forward h handles {NextName}.
    ResCont :: Exp
      handles {Bind, Binds, Collect} where
        Return x     -> return x
        Bind e     k ->
          do x <- nextName
             e' <- k x
             return (Let x e e')
        Binds e    k ->
          do x1 <- nextName
             x2 <- nextName
             e1 <- k (Left x1)
             e2 <- k (Right x2)
             return (Case e x1 e1 x2 e2)
        Collect c  k ->
          do e <- resCont c
             k e
|] 


-- We now give some approximation to an accumulation-based
-- residualising interpretation.
--
-- It's a little strange because we use the free monad structure of
-- abstract computations to encode the free monad over binding trees.

[operation|LetB :: String -> Exp -> ()|]
[operation|CaseB :: Exp -> String -> String -> Bool|]
letB' x e e' = do letB x e; e'
caseB' e x1 e1 x2 e2 = do b <- caseB e x1 x2;
                          if b then e1 else e2

-- As we encode the binding tree structure using operations, the
-- return type of the handler is again just Exp.
[handler|
  forward h handles {NextName, LetB, CaseB}.
    ResAcc :: Exp
      handles {Bind, Binds, Collect} where
        Return x     -> return x
        Bind e     k ->
          do x <- nextName
             letB' x e (k x)
        Binds e    k ->
          do x1 <- nextName
             x2 <- nextName
             e1 <- k (Left x1)
             e2 <- k (Right x2)
             caseB' e x1 (k (Left x1)) x2 (k (Left x2))
        Collect c  k ->
          do e <- resCont c
             k e
|] 

-- Convert a binding tree (represented as an abstract computation over
-- LetB and CaseB) into the corresponding syntax.
[handler|
  forward h.
    Flatten :: Exp
      handles {LetB, CaseB} where
        Return x         -> return x
        LetB x e       k ->
          do e' <- k ()
             return (Let x e e')
        CaseB e x1 x2  k ->
          do e1 <- k True
             e2 <- k False
             return (Case e x1 e1 x2 e2)
|]

--- semantics

-- values and computations
data SemV = Neutral Exp | Fun (SemV -> SemC) | Sum (Either SemV SemV)
type SemC = ResComp SemV

-- This function generates an abstract computation for performing
-- normalisation by evaluation.
abstractNorm :: Type -> Hoas -> ResComp Exp
abstractNorm a e = reifyC a (eval empty (hoasToExp e))

normCont :: Type -> Hoas -> Exp
normCont a e = handlePure (evalNames (resCont (abstractNorm a e)))

normAcc :: Type -> Hoas -> Exp
normAcc a e = handlePure (evalNames (flatten (resAcc (abstractNorm a e))))

test1 = normCont ((Base :+: (Base :-> Base)) :-> (Base :+: (Base :-> Base))) (lam id)
test2 = normAcc ((Base :+: (Base :-> Base)) :-> (Base :+: (Base :-> Base))) (lam id)

-- reify a computation
reifyC :: Type -> SemC -> ResComp Exp
reifyC a c = collect (do v <- c; reifyV a v)

-- reify a value
reifyV :: Type -> SemV -> ResComp Exp
reifyV Base (Neutral e) = return e
reifyV (a :-> b) (Fun f) =
    do x <- nextName
       e <- reifyC b (do v <- reflectV a x; f v)
       return (Lam x e)
reifyV (a :+: b) (Sum (Left v)) =
    do e <- reifyV a v
       return (Inl e)
reifyV (a :+: b) (Sum (Right v)) =
    do e <- reifyV b v
       return (Inr e)

-- reflect a neutral computation expression (i.e. application) as a computation
reflectC :: Type -> String -> Exp -> SemC
reflectC a x e =
    do x <- bind (App (Var x) e)
       reflectV a x   

-- reflect a neutral value expression (i.e. variable) as a computation
reflectV :: Type -> String -> SemC
reflectV Base x = return (Neutral (Var x))
reflectV (a :-> b) x =
    return (Fun (\v -> do e <- reifyV a v; reflectC b x e))
reflectV (a :+: b) x =
    do v <- binds (Var x)
       case v of
         Left x1 ->
             do v1 <- reflectV a x1
                return (Sum (Left v1))
         Right x2 ->
             do v2 <- reflectV b x2
                return (Sum (Right v2))

--- An evaluator
eval :: Env SemV -> Exp -> ResComp SemV
eval env (Var x) =
  return (fromJust (lookup x env))
eval env (Lam x e) =
  return (Fun (\v -> eval (extend env x v) e))
eval env (App e1 e2) =
    do
      (Fun v1) <- eval env e1
      v2       <- eval env e2
      v1 v2
eval env (Let x e1 e2) =
    do 
      v <- eval env e1
      eval (extend env x v) e2
eval env (Inl e) =
    do
      v <- eval env e
      return (Sum (Left v))
eval env (Inr e) =
    do
      v <- eval env e
      return (Sum (Right v))
eval env (Case e x1 e1 x2 e2) =
    do
      (Sum s) <- eval env e
      case s of
        Left v  -> eval (extend env x1 v) e1
        Right v -> eval (extend env x2 v) e2

-- interpret nextName using get and put
evalNames = evalState 0 . stateNames
[handler|
  forward h handles {Get (Int), Put (Int)}.
    StateNames a :: a
      handles {NextName} where
        Return x   -> return x
        NextName k -> do {i <- get; put (i+1) ; k ("x" ++ show i)}
|]

-- standard state interpretation of get and put
[operation|Get s :: s|]
[operation|Put s :: s -> ()|]
[handler| 
  forward h.
    EvalState s a :: s -> a 
      handles {Get s, Put s} where
        Return  x     _ -> return x
        Get        k  s -> k s  s
        Put     s  k  _ -> k () s
|]
