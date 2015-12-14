{-# LANGUAGE TypeFamilies,
    GADTs,
    RankNTypes,
    MultiParamTypeClasses,
    QuasiQuotes,
    FlexibleInstances,
    FlexibleContexts,
    OverlappingInstances,
    UndecidableInstances,
    ConstraintKinds, 
    NoMonomorphismRestriction #-}

module Examples.State where

import Control.Monad
import Data.IORef
import Handlers
import TopLevel
import DesugarHandlers

import Criterion.Main
import Criterion.Config

[operation|Put s :: s -> ()|]

type SComp s a = ([handles|h {Put s}|]) => Comp h a

[handler|
  Update s a :: (Maybe s, a)
    handles {Put s} where
      Return  x     -> (Nothing, x)
      Put     s  k  -> case k () of
                         (Nothing, x) -> (Just s,  x)
                         (s', x) -> (s', x)
|] 

foo1 = do put 32
          return ()

{- heterogenous case would allow 
foo2 = do put 32
          put "hello"
          return ()
-}
