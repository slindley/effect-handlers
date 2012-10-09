{- Primitive recursion using handlers -}
{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction #-}

import Data.Either
import Control.Monad
import Handlers

data Step = Step
instance Op Step where
  type Param Step = ()
  type Return Step = ()
step = applyOp Step ()

-- natural numbers can be encoded as computations over the Step operation
type Nat = Comp (Step, ()) ()

zero  = return ()
suc n = step >> n

one   = suc zero
two   = suc one
three = suc two
four  = suc three
five  = suc four
six   = suc five

toInt :: Nat -> Int
toInt n =
  handle n
  ((Step |-> \p k -> 1+k p) :<: Empty,
   \_ -> 0)

plus :: Nat -> Nat -> Nat
plus m n = m >> n

times :: Nat -> Nat -> Nat
times m n =
  handle m
  ((Step |-> \p k -> plus n (k p)) :<: Empty,
   return)

fact :: Nat -> Nat
fact n =
  snd
  (handle n
   ((Step |-> \() k ->
      let (p, q) = k () in
      (suc p, times (suc p) q)) :<: Empty,
    \() -> (zero, one)))

-- A System T recursor
rec :: Nat -> a -> (a -> Nat -> a) -> a
rec n v f =
  snd
  (handle n
   ((Step |-> \() k ->
      let (p, q) = k () in
      (suc p, f q (suc p))) :<: Empty,
    \() -> (zero, v)))

-- predecessor function
pred :: Nat -> Nat
pred n =
  fst (rec n (zero, zero) (\ (_, x) _ -> (x, suc x)))
