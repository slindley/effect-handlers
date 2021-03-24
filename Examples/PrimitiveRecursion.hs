{- Primitive recursion using handlers -}

{-# LANGUAGE TypeFamilies,
    GADTs,
    RankNTypes,
    MultiParamTypeClasses,
    QuasiQuotes,
    FlexibleContexts,
    ScopedTypeVariables #-}

import Data.Either
import Control.Monad

import Handlers
import DesugarHandlers

[operation|Step :: ()|]

-- natural numbers can be encoded as computations over the Step operation
type Nat = [handles|h {Step}|] => Comp h ()

-- wrapping and unwrapping is necessary to work around
-- deficiencies in GHCs handling of polymorphism
newtype WrappedNat = Wrap {unWrap :: Nat}

zero :: Nat
zero  = return ()

suc :: Nat -> Nat
suc n = step >> n

one, two, three, four, five, six :: Nat
one   = suc zero
two   = suc one
three = suc two
four  = suc three
five  = suc four
six   = suc five

plus :: Nat -> Nat -> Nat
plus m n = m >> n

[handler|
  ToInt :: Int
    handles {Step} where
      Return x   -> 0
      Step     k -> 1+(k ())
|]

-- an iterator
iter :: Nat -> a -> (a -> a) -> a
iter n v f = iterator v f n
[handler|
  Iterator a :: a -> (a -> a) -> a
    handles {Step} where
      Return ()   v _ -> v
      Step      k v f -> f (k () v f)
|]

times :: Nat -> Nat -> Nat
times m n = unWrap (iter n (Wrap m) (\(Wrap x) -> Wrap (plus x n)))

-- predecessor function using iteration
predIter :: Nat -> Nat
predIter n =
  unWrap (fst (iter n (Wrap zero, Wrap zero) (\ (_, Wrap x) -> (Wrap x, Wrap (suc x)))))

-- -- A System T recursor
-- rec :: Nat -> a -> (a -> Nat -> a) -> a
-- rec n v f = snd (recursor v f n)
-- [handler|
--   Recursor a :: a -> (a -> Nat -> a) -> (WrappedNat, a)
--     handles {Step} where
--       Return ()   v _ -> (Wrap zero, v)
--       Step      k v f -> let (Wrap p, q) = k () v f in
--                            (Wrap (suc p), f q p)
-- |]

-- -- predecessor function using recursion
-- predRec :: Nat -> Nat
-- predRec n =
--   unWrap (rec n (Wrap zero) (\_ m -> Wrap m))

-- factorial :: Nat -> Nat
-- factorial n = unWrap (rec n (Wrap zero) (\(Wrap x) m -> Wrap (times x m)))
