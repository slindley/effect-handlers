{- Shallow handlers using a free monad -}

{-# LANGUAGE TypeFamilies, RankNTypes,
    MultiParamTypeClasses, FlexibleContexts,
    TypeOperators, GADTs #-}

module ShallowFreeHandlers where

type family Return op :: *
type family Result h :: *
type family Inner h :: *     

class Handles h op where
  clause :: op -> (Return op -> Comp h (Inner h)) -> h -> Result h

data Comp h a where
  Ret :: a -> Comp h a
  Do  :: (h `Handles` op) => op -> (Return op -> Comp h a) -> Comp h a

instance Monad (Comp h) where
  return        = Ret
  Ret v   >>= f = f v
  Do op k >>= f = Do op (\x -> k x >>= f)

instance Functor (Comp h) where
  fmap f c = c >>= \x -> return (f x)

doOp :: (h `Handles` op) => op -> Comp h (Return op)
doOp op = Do op return

handle :: Comp h (Inner h) -> (Inner h -> h -> Result h) -> h -> Result h
handle (Ret v) r h   = r v h
handle (Do op k) r h = clause op k h

-- pure handlers
data PureHandler a = PureHandler
type instance Result (PureHandler a) = a
type instance Inner (PureHandler a) = a

handlePure :: Comp (PureHandler a) a -> a
handlePure comp = handle comp (\x _ -> x) PureHandler

data IOHandler a = IOHandler
type instance Result (IOHandler a) = IO a
type instance Inner (IOHandler a) = a

handleIO :: Comp (IOHandler a) a -> IO a
handleIO comp = handle comp (\x _ -> return x) IOHandler 

