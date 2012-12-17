{-# LANGUAGE
    DataKinds, PolyKinds, TypeOperators, RankNTypes 
 #-}

module FunctorIx where

type a :-> b = forall i. a i -> b i

class FunctorIx (f :: (i -> *) -> (o -> *)) where
  mapIx :: (a :-> b) -> (f a :-> f b)

