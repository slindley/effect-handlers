{- 
   This example (due to Oscar Key) illustrates the limitations of our
encoding of effect typing in Haskell. The effects have been replaced
by concrete handlers Up and Down which are different types.

Tested with ghc 7.8.4.
 -}

{-# LANGUAGE TypeFamilies, GADTs, NoMonomorphismRestriction, RankNTypes,
    MultiParamTypeClasses, FlexibleInstances, OverlappingInstances,
    FlexibleContexts, UndecidableInstances,
    QuasiQuotes
  #-}

module Examples.UpDown where

import ShallowFreeHandlers
import DesugarHandlers

[operation|Move :: ()|]
 
[shallowHandler|
  Down a :: a
    handles {Move} where
      Return x   -> x
      Move     k -> up (k ()) |]

[shallowHandler|
  Up a :: a
    handles {Move} where
      Return x -> x
      Move k   -> down (k ()) |]

