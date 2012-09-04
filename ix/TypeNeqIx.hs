-- Kind-polymorphic type unequality: x =/= y iff x and y are different types

{-# LANGUAGE PolyKinds, MultiParamTypeClasses, TypeFamilies, FunctionalDependencies,
    UndecidableInstances, FlexibleInstances, FlexibleContexts, TypeOperators
  #-}

module TypeNeqIx ((:=/=:)) where

data T = T
data F = F

class TypeEq (x :: k) (y :: k) b | x y -> b
instance b ~ T => TypeEq x x b
instance b ~ F => TypeEq x y b

class TypeEq x y F => x :=/=: y
instance TypeEq x y F => x :=/=: y
