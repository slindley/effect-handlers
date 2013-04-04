{-# LANGUAGE
    DataKinds, PolyKinds, TypeOperators, RankNTypes 
 #-}

module FunctorIx where

type a :-> b = forall i. a i -> b i

class FunctorIx (f :: (v -> *) -> (w -> *)) where
  mapIx :: (a :-> b) -> (f a :-> f b)

