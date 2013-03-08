{-# LANGUAGE TypeFamilies,
    GADTs,
    NoMonomorphismRestriction,
    RankNTypes,
    MultiParamTypeClasses,
    QuasiQuotes,
    FlexibleInstances,
    FlexibleContexts,
    OverlappingInstances,
    UndecidableInstances #-}

module Examples.ShallowState where

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


[shallowHandler|
  forward h.
    ForwardState s a :: s -> a 
      handles {Get s, Put s} where
        Return  x     _ -> return x
        Get        k  s -> forwardState s (k s)
        Put     s  k  _ -> forwardState s (k ())
|]


[operation|PrintLine :: String -> ()|]
[shallowHandler|
  PrintHandler a :: IO a
    handles {PrintLine} where
      Return x      -> return x
      PrintLine s k -> do {putStrLn s; printHandler (k ())}
|]


count =
    do {i <- get;
        if i == 0 then return i
        else do {put (i-1); count}}

iterations = 100000000

simple n  = simpleState n count
forward n = printHandler (forwardState n count)

main = forward iterations
