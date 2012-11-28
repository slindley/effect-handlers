-- delimited continuations with effect handlers

{-# LANGUAGE TypeFamilies,
             FlexibleContexts, TypeOperators,
             MultiParamTypeClasses,
             OverlappingInstances, UndecidableInstances,
             FlexibleInstances,
             QuasiQuotes,
             DataKinds,
             GADTs,
             RankNTypes
  #-}

module DelimitedContinuations where

import DesugarHandlers
import Handlers

-- [operation|forall a.Shift0 r :: ((a -> r) -> r) -> a|]
-- [handler|
--   Reset0 r a :: r handles {Shift0 r} where
--     Return x   -> x
--     Shift0 p k -> p k
-- |]
data Shift0 (e :: *) (u :: *) where
  Shift0 :: ((a -> r) -> r) -> Shift0 r a
type instance Return (Shift0 r a) = a
shift0 :: (h `Handles` Shift0) r => ((a -> r) -> r) -> Comp h a
shift0 p = doOp (Shift0 p)

data Reset0 (r :: *) (a :: *) = Reset0
type instance Result (Reset0 r a) = r
instance (Reset0 r a `Handles` Shift0) r where
  clause (Shift0 p) k Reset0 = p (\x -> k x Reset0)

-- reset0WithReturn :: DelimComp r a -> (r -> Reset0 r a -> r) -> r
-- reset0WithReturn comp ret = handle comp ret Reset0

reset0 :: DelimComp r a -> r
reset0 comp = handle comp (\x _ -> x) Reset0

reset0' :: DelimComp' r r -> r
reset0' comp = handle comp (\x _ -> x) Reset0

type DelimComp' r a = ([handles|h {Shift0 r}|]) => Comp h a
type DelimComp r a = Comp (Reset0 r a) r

[operation|forall a.Shift h r :: ((a -> r) -> Comp (Reset h r a) r) -> a|]
[handler|
  Reset h r a :: r handles {Shift h r} where
    Return x   -> x
    Shift p  k -> reset (p k)
|]

-- Note that reset requires recursion (both in the terms and the
-- types), but reset0 does not.

-- We can define versions of reset0 and reset that forward other
-- operations...  This is a matter of replacing each of the 'raw'
-- instances of r in the types of Shift0 and Shift0 with Comp h r.
[operation|forall a.Shift0F h r :: ((a -> Comp h r) -> Comp h r) -> a|]
[handler|
  forward h.
    Reset0F r a :: r handles {Shift0F h r} where
      Return x    -> return x
      Shift0F p k -> p k
|]

[operation|forall a.ShiftF h r :: ((a -> Comp h r) -> Comp (ResetF h r a) r) -> a|]
[handler|
  forward h. 
    ResetF r a :: r handles {ShiftF h r} where
      Return x    -> return x
      ShiftF p  k -> resetF (p k)
|]
