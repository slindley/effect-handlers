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

import Data.Monoid

import Criterion.Main
import Criterion.Config

[operation|Tell s :: s -> ()|]

type SComp s a = ([handles|h {Tell s}|]) => Comp h a

[handler|
  ListWriter s a :: (a, [s])
    handles {Tell s} where
      Return  x    -> (x, [])
      Tell   s  k  -> let (a, ss) = k () in (a, s : ss)
|] 

[handler|
  MonoidWriter s a :: Monoid s => (a, s)
    handles {Tell s} where
      Return  x    -> (x, mempty)
      Tell    s  k -> let (a, s') = k () in (a, s `mappend` s')
|] 

example1 = do tell 1
              tell 2
              tell 3
              return ()

example1a = listWriter example1

instance Monoid Int where
    mempty = 0
    mappend = (+)

example2a = (monoidWriter example1)::((), Int)



