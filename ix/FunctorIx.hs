{-# LANGUAGE
    DataKinds, PolyKinds, TypeOperators, RankNTypes 
 #-}

module FunctorIx where

type a :-> b = forall i. a i -> b i

-- GHC 7.4 doesn't allow polymorphic kind annotations
--class FunctorIx f where

class FunctorIx (f :: (i -> *) -> (o -> *)) where
  mapIx :: (a :-> b) -> (f a :-> f b)

