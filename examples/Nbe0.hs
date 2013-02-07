{- Normalisation by evaluation for the computational lambda calculus +
   sums using handlers.

   Based on the paper 'Accumulating bindings' by Sam Lindley:

     http://homepages.inf.ed.ac.uk/slindley/papers/nbe-sums.pdf
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

--- environments
type Env a = [(String, a)]

empty :: Env a
empty = []

extend :: [(String, a)] -> String -> a -> [(String, a)]
extend env x v = (x, v):env

[operation|Bind    :: Exp -> String|]
[operation|Binds   :: Exp -> Either String String|]

-- One might think that Collect should be a handler, but it's
-- convenient to make it an operation so we can abstract over it in
-- the same way as Bind and Binds.
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
             caseB' e x1 (k (Left x1)) x2 (k (Right x2))
        Collect c  k ->
          do e <- flatten (resAcc c)
             k e
|] 

-- Convert a binding tree (represented as an abstract computation over
-- LetB and CaseB) into the corresponding syntax.
[handler|
  forward h.
    Flatten :: Exp
      handles {LetB, CaseB} where
        Return x          -> return x
        LetB x e        k ->
          do e' <- k ()
             return (Let x e e')
        CaseB e x1 x2   k ->
          do e1 <- k True
             e2 <- k False
             return (Case e x1 e1 x2 e2)
|]

--- semantics

-- values and computations
data SemV = Neutral Exp | Fun (SemV -> SemC) | Sum (Either SemV SemV)
type SemC = ResComp SemV

-- this function generates an abstract computation for performing
-- normalisation by evaluation.
abstractNorm :: Rep a -> Hoas a -> ResComp Exp
abstractNorm a e = reifyC a (eval empty (hoasToExp e))

normCont :: Rep a -> Hoas a -> Exp
normCont a e = handlePure (evalNames (resCont (abstractNorm a e)))

normAcc :: Rep a -> Hoas a-> Exp
normAcc a e = handlePure (evalNames (flatten (resAcc (abstractNorm a e))))

test1 = normCont ((A :+: (B :-> C)) :-> (A :+: (B :-> C))) (lam id)
test2 = normAcc ((A :+: (B :-> C)) :-> (A :+: (B :-> C))) (lam id)

-- reify a computation
reifyC :: Rep a -> SemC -> ResComp Exp
reifyC a c = collect (do v <- c; reifyV a v)

-- reify a value
reifyV :: Rep a -> SemV -> ResComp Exp
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

-- reflect a neutral computation expression (i.e. application) as a computation
reflectC :: Rep a -> String -> Exp -> SemC
reflectC a x e =
    do x <- bind (App (Var x) e)
       reflectV a x   

-- reflect a neutral value expression (i.e. variable) as a computation
reflectV :: Rep a -> String -> SemC
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
