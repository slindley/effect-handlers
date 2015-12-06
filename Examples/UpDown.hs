{- An implementation of part of Gabriel Gonzalez's Pipes library using
shallow handlers. The original library is here:

    http://hackage.haskell.org/package/pipes
 -}

{-# LANGUAGE TypeFamilies, GADTs, NoMonomorphismRestriction, RankNTypes,
    MultiParamTypeClasses, FlexibleInstances, OverlappingInstances,
    FlexibleContexts, UndecidableInstances,
    QuasiQuotes
  #-}

module Examples.ShallowPipes where

import Control.Monad

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

