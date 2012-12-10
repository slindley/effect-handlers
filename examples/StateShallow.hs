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
import DesugarHandlers

[operation|Get s :: s|]
[operation|Put s :: s -> ()|]

-- data Get = Get
-- type instance Return Get = Int
-- get = doOp Get

-- data Put = Put Int
-- type instance Return Put = ()
-- put s = doOp (Put s)

[shallowHandler|
  SimpleState s a :: s -> a
    handles {Get s, Put s} where
      Return  x     _ -> x
      Get        k  s -> simpleState s (k s)
      Put     s  k  _ -> simpleState s (k ())
|]


-- newtype SimpleState a = SimpleState Int
-- type instance Result (SimpleState a) = a
-- type instance Inner (SimpleState a) = a
-- instance (SimpleState a `Handles` Put) () where
--   clause (Put s) k h = simpleState s (k ())
-- instance (SimpleState a `Handles` Get) () where
--   clause Get k (SimpleState s) = simpleState s (k s)
-- simpleState s comp = handle comp (\x _ -> x) (SimpleState s)
-- --simpleState' s comp = simpleState s (Comp (\k -> comp >>= k))


countH =
    do {i <- get;
        if i == 0 then return i
        else do {put (i-1); countH}}


test5 = print (simpleState 100000000 countH)

main = test5
