{- Top-level handlers -}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses,
    GADTs,
    TypeOperators,
    RankNTypes,
    FlexibleContexts,
    QuasiQuotes
  #-}

module TopLevel where

import Handlers
import DesugarHandlers

[handler|
  HandlePure a :: a handles {} where
    Return x -> x
|]
handlePure' :: (forall h.Comp h a) -> a
handlePure' c = handlePure c

[operation|forall a.Io :: IO a -> a|]
[handler|
  HandleIO a :: IO a handles {Io} where
    Return x -> return x
    Io m k   -> do {x <- m; k x}
|]
