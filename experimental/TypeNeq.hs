-- Type unequality: x =/= y iff x and y are different types

{-# LANGUAGE MultiParamTypeClasses, TypeFamilies, FunctionalDependencies,
    UndecidableInstances, FlexibleInstances, FlexibleContexts, TypeOperators
  #-}

module TypeNeq ((:=/=:)) where

data T = T
data F = F

class TypeEq x y b | x y -> b
instance b ~ T => TypeEq x x b
instance b ~ F => TypeEq x y b

class (TypeEq x y F) => x :=/=: y
instance TypeEq x y F => x :=/=: y
