{- Normalisation by evaluation for the computational lambda calculus +
   sums using handlers.

   Based on the paper 'Accumulating bindings' by Sam Lindley:

     http://homepages.inf.ed.ac.uk/slindley/papers/nbe-sums.pdf

   This version uses handlers pervasively, including in the evaluator,
   which presents some interesting issues.
-}

{-# LANGUAGE TypeFamilies,
    GADTs,
    RankNTypes,
    MultiParamTypeClasses,
    QuasiQuotes,
    FlexibleInstances,
    FlexibleContexts,
    OverlappingInstances,
    UndecidableInstances,
    ConstraintKinds,
    TypeOperators,
    DataKinds,
    PolyKinds,
    ScopedTypeVariables #-}

import Handlers
import TopLevel
import DesugarHandlers

import Data.Maybe

import Unsafe.Coerce

type Var = String

-- FOAS
data Exp = Var Var
         | Lam Var Exp
         | App Exp Exp
         | Inl Exp
         | Inr Exp
         | Case Exp Var Exp Var Exp
         | Let Var Exp Exp
  deriving Eq

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


[operation|NextName :: String|]

type NamesComp a = ([handles|h {NextName}|]) => Comp h a

infixl 9 :+:
infixr 5 :->

-- We build up simple types from: abstract base types (A,B,C), the
-- function type constructor (->), and the sum type constructor (Either).

-- some abstract base types
data A
data B
data C

-- syntactic sugar for sums
type a :+: b = Either a b

-- a GADT of simple type representations
data Rep :: * -> * where
     A :: Rep A
     B :: Rep B
     C :: Rep C
     (:->) :: Rep a -> Rep b -> Rep (a->b)
     (:+:) :: Rep a -> Rep b -> Rep (a:+:b)

instance Show (Rep a) where
    show A = "A"
    show B = "B"
    show C = "C"
    show (r1 :-> r2) = "(" ++ show r1 ++ "->" ++ show r2 ++ ")"
    show (r1 :+: r2) = "(" ++ show r1 ++ ":+:" ++ show r2 ++ ")"

-- The Representable type class allows us to smoothly bridge the gap between
-- metalanguage types and object language type representations.
--
-- Note that this type class is closed by construction, as the Rep GADT
-- only admits simple type representations.
class Representable a where
    rep :: Rep a

instance Representable A where rep = A
instance Representable B where rep = B
instance Representable C where rep = C

instance (Representable a, Representable b) => Representable (a->b) where
    rep = rep :-> rep

instance (Representable a, Representable b) => Representable (a:+:b) where
    rep = rep :+: rep

-- Typed HOAS
class CompLam exp where
  lam :: (Representable a, Representable b) => (exp a -> exp b) -> exp (a->b)
  app :: (Representable a, Representable b) => exp (a->b) -> exp a -> exp b
  inl :: (Representable a, Representable b) => exp a -> exp (a:+:b)
  inr :: (Representable a, Representable b) => exp b -> exp (a:+:b)
  case_ :: (Representable a, Representable b, Representable c) =>
            exp (a:+:b) -> (exp a -> exp c) -> (exp b -> exp c) -> exp c
  let_ :: (Representable a, Representable b) => exp a -> (exp a -> exp b) -> exp b

-- the type of closed HOAS terms of type a
type Hoas a = forall (exp :: * -> *). CompLam exp => exp a

-- convert a typed closed HOAS term to the
-- corresponding FOAS term
hoasToExp :: Hoas a -> Exp
hoasToExp v = handlePure (evalNames (unT v))

-- expressions with names and a phantom type attached
newtype T a = T {unT :: NamesComp Exp}

instance CompLam T where
    lam f = T$ do x <- nextName
                  e <- unT$ f (T$ return (Var x))
                  return (Lam x e)
    v1 `app` v2 = T$ do e1 <- unT v1
                        e2 <- unT v2
                        return (App e1 e2)
    inl v = T$ do e <- unT v
                  return (Inl e)
    inr v = T$ do e <- unT v
                  return (Inr e)
    case_ v l r = T$ do e <- unT v
                        x1 <- nextName
                        x2 <- nextName
                        e1 <- unT$ l (T$ return (Var x1))
                        e2 <- unT$ r (T$ return (Var x2))
                        return (Case e x1 e1 x2 e2)
    let_ v f = T$ do e <- unT v
                     x <- nextName
                     e' <- unT$ f (T$ return (Var x))
                     return (Let x e e')

[operation|Bind  :: Exp -> String|]
[operation|Binds :: Exp -> Either String String|]

-- One might think that Collect should be a handler, but it's
-- convenient to make it an operation so we can abstract over it in
-- the same way as Bind and Binds.
--
-- Collect can in fact be seen as a rather generic operation for
-- delimiting a chunk of computation. It is also used by the
-- aspect-oriented programming example, where it is called Suspend.
--
-- In our current implementation, Collect typically leads to
-- boilerplate for each handler as we need to recursively invoke the
-- handler on the argument.
[operation|Collect h a :: Comp h a -> a|]

-- interface to residualising computations
type ResConstraints h =
  ([handles|h {NextName}|],
   [handles|h {Bind}|], [handles|h {Binds}|],
   [handles|h {Collect h (Exp)}|])

-- The canonical continuation-based interpretation of residualising
-- computations.
--
-- As handlers give us direct access to the current continuation
-- anyway we don't actually need to explicitly introduce a
-- continuation monad, so the return type of the handler is just Exp.
[handler|
  forward h handles {NextName}.
    ResCont :: Exp
      handles {Bind, Binds, Collect (ResCont h) (Exp)} where
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
  forward h handles {NextName, LetB, CaseB, Collect h a}.
    ResAcc a :: a
      handles {Bind, Binds, Collect (ResAcc h a) a} where
        Return x     -> return x
        Bind e     k ->
          do x <- nextName
             letB' x e (k x)
        Binds e    k ->
          do x1 <- nextName
             x2 <- nextName
             caseB' e x1 (k (Left x1)) x2 (k (Right x2))
        Collect c  k ->
          do e <- collect (resAcc c)
             k e
|] 

-- Convert a binding tree (represented as an abstract computation over
-- LetB and CaseB) into the corresponding syntax.
[handler|
  forward h.
    Flatten :: Exp
      handles {LetB, CaseB, Collect (Flatten h) (Exp)} where
        Return x          -> return x
        LetB x e        k ->
          do e' <- k ()
             return (Let x e e')
        CaseB e x1 x2   k ->
          do e1 <- k True
             e2 <- k False
             return (Case e x1 e1 x2 e2)
        Collect c       k ->
          do e <- flatten c
             k e
|]

--- semantics

-- values and computations
data SemV h = Neutral Exp | Fun (SemV h -> SemC h) | Sum (SemV h :+: SemV h)
type SemC h = Comp h (SemV h)

-- this function generates an abstract computation for performing
-- normalisation by evaluation.
abstractNorm :: (ResConstraints h, EvalConstraints h) => Rep a -> Hoas a -> Comp h Exp
abstractNorm a e = reifyC a (eval (hoasToExp e))

normCont :: Rep a -> Hoas a -> Exp
normCont a e = handlePure (evalNames (undefinedFailure (resCont (listEnv [] (abstractNorm a e)))))

normAcc :: Rep a -> Hoas a -> Exp
normAcc a e = handlePure (evalNames (undefinedFailure (flatten (resAcc (listEnv [] (abstractNorm a e))))))
  
test1 = normCont ((A :+: (B :-> C)) :-> (A :+: (B :-> C))) (lam id)
test2 = normAcc  ((A :+: (B :-> C)) :-> (A :+: (B :-> C))) (lam id)

-- reify a computation
reifyC :: ResConstraints h => Rep a -> SemC h -> Comp h Exp
reifyC a c = collect (do v <- c; reifyV a v)

-- reify a value
reifyV :: ResConstraints h => Rep a -> SemV h -> Comp h Exp
reifyV A (Neutral e) = return e
reifyV B (Neutral e) = return e
reifyV C (Neutral e) = return e
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

-- reflect a neutral computation expression (i.e. application) as a
-- computation
reflectC :: ResConstraints h => Rep a -> String -> Exp -> SemC h
reflectC a x e =
    do x <- bind (App (Var x) e)
       reflectV a x   

-- reflect a neutral value expression (i.e. variable) as a computation
reflectV :: ResConstraints h => Rep a -> String -> SemC h
reflectV A x = return (Neutral (Var x))
reflectV B x = return (Neutral (Var x))
reflectV C x = return (Neutral (Var x))
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

-- environments
[operation|Find k v   :: k -> v|]
[operation|Extend k v :: k -> v -> ()|]

type EnvConstraints h k v = ([handles|h {Find k v}|], [handles|h {Extend k v}|])

-- non-recursive list environment
--
-- [handler|
--   forward h handles {Failure}.
--     ListEnv v a :: [(String, v)] -> a handles {Find (String) v, Extend (String) v} where
--       Return x     env -> return x
--       Find x     k env -> case lookup x env of
--                             Nothing -> failure
--                             Just v  -> k v env
--       Extend x v k env -> k () ((x,v) : env)
-- |]

-- recursive list environment
--
-- [handler|
--   forward h handles {Failure}.
--     ListEnv a :: [(String, SemV (ListEnv h a))] -> a
--       handles {Find (String) (SemV (ListEnv h a)), Extend (String) (SemV (ListEnv h a))} where
--         Return x     env -> return x
--         Find x     k env -> case lookup x env of
--                               Nothing -> failure
--                               Just v  -> k v env
--         Extend x v k env -> k () ((x,v) : env)
-- |]

-- recursive list environment that recursively handles Collect
-- operations
[handler|
  forward h handles {Failure, Collect h a}.
    ListEnv a :: [(String, SemV (ListEnv h a))] -> a
      handles {Find   (String) (SemV (ListEnv h a)),
               Extend (String) (SemV (ListEnv h a)),
               Collect (ListEnv h a) a} where
        Return x     env -> return x
        Find x     k env -> case lookup x env of
                              Nothing -> failure
                              Just v  -> k v env
        Extend x v k env -> k () ((x,v) : env)
        Collect c  k env -> do e <- collect (listEnv env c)
                               k e env
|]

--- If we're not carefull then any effects in eval screw things up
--- because they leak into the environment, which persists.
---
--- We solve this problem by:
---
---   * being careful to define an explicitly recursive type
---   for an environment handler
---
---   * ensuring that we handle the eval effects at a type not
---   involving the effects, i.e., Exp.

type EvalConstraints h = EnvConstraints h String (SemV h)

--- An effectful evaluator that abstracts over the implementation of
--- environments
eval :: EvalConstraints h => Exp -> SemC h
eval (Var x) = find x
eval (Lam x e) =
  return (Fun (\v ->
                do extend x v
                   eval e))
eval (App e1 e2) =
    do
      (Fun v1) <- eval e1
      v2 <- eval e2
      v1 v2
eval (Let x e1 e2) =
    do 
      v <- eval e1
      extend x v
      eval e2
eval (Inl e) =
    do
      v <- eval e
      return (Sum (Left v))
eval (Inr e) =
    do
      v <- eval e
      return (Sum (Right v))
eval (Case e x1 e1 x2 e2) =
    do
      (Sum s) <- eval e
      case s of
        Left v  ->
          do extend x1 v
             eval e1
        Right v ->
          do extend x2 v
             eval e2

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

-- failure
[operation|forall a.Failure :: a|]
[handler|
  forward h.
    UndefinedFailure a :: a handles {Failure} where
      Return x   -> return x
      Failure  k -> undefined    
|]
