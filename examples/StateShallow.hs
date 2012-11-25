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

import ShallowFreeHandlers

data Get = Get
type instance Return Get = Int
get = doOp Get

newtype Put = Put Int
type instance Return Put = ()
put s = doOp (Put s)

newtype SimpleState a = SimpleState Int
type instance Result (SimpleState a) = a
type instance Inner (SimpleState a) = a
instance (SimpleState a `Handles` Put) where
  clause (Put s) k h = simpleState s (k ())
instance (SimpleState a `Handles` Get) where
  clause Get k (SimpleState s) = simpleState s (k s)
simpleState s comp = handle comp (\x _ -> x) (SimpleState s)
--simpleState' s comp = simpleState s (Comp (\k -> comp >>= k))


countH =
    do {i <- get;
        if i == 0 then return i
        else do {put (i-1); countH}}


test5 = print (simpleState 10000000 countH)

main = test5
