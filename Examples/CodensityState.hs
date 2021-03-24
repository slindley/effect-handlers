{-# LANGUAGE TypeFamilies,
    GADTs,
    RankNTypes,
    MultiParamTypeClasses,
    QuasiQuotes,
    FlexibleInstances,
    FlexibleContexts,
    OverlappingInstances,
    UndecidableInstances #-}

module Examples.CodensityState where

import CodensityHandlers
import DesugarHandlers

[operation|Get s :: s|]
[operation|Put s :: s -> ()|]

type SComp s a = forall h.
  ([handles|h {Get s}|], [handles|h {Put s}|]) => Comp h a

[handler|
  SimpleState s a :: s -> a 
    handles {Get s, Put s} where
      Return  x     _ -> x
      Get        k  s -> k s  s
      Put     s  k  _ -> k () s
|]

[handler|
  forward h.ForwardState s a :: s -> a 
    handles {Get s, Put s} where
      Return  x     _ -> return x
      Get        k  s -> k s  s
      Put     s  k  _ -> k () s
|]

[operation|PrintLine :: String -> ()|]
[handler|
  PrintHandler a :: IO a handles {PrintLine} where
    Return x      -> return x
    PrintLine s k -> do {putStrLn s; k ()}
|]

count :: SComp Int Int
count =
    do {i <- get;
        if i == 0 then return i
        else do {put (i-1); count}}

simple  n = simpleState n count
forward n = printHandler (forwardState n count)
