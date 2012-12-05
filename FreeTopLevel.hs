{- Free top-level handlers -}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses,
    GADTs,
    TypeOperators,
    RankNTypes,
    FlexibleContexts,
    QuasiQuotes
  #-}

module FreeTopLevel where

import FreeHandlers
import DesugarHandlers

[handler|
  HandlePure a :: a handles {} where
    Return x -> x
|]
handlePure :: (forall h.Comp h a) -> a

[operation|forall a.Io :: IO a -> a|]
[handler|
  HandleIO a :: IO a handles {Io} where
    Return x -> return x
    Io m k   -> do {x <- m; k x}
|]
