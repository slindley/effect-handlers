{- Parameterised monad handlers

   A generalisation of handlers to support Bob Atkey's parameterised
notions of computation:

     http://bentnib.org/paramnotions-jfp.pdf
 -}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses,
    FlexibleInstances,
    FlexibleContexts,
    GADTs,
    TypeOperators,
    RankNTypes,
    PolyKinds,
    ScopedTypeVariables
  #-}

module PaHandlers where

class PaMonad (m :: w -> w -> * -> *) where
  paReturn :: a -> m i i a
  paExtend :: (a -> m j k b) -> (m i j a  -> m i k b)

(=>=) :: PaMonad m => m i j a -> (a -> m j k b) -> m i k b
(=>=) = flip paExtend

type family Return (opApp :: *) :: *
type family Result (hApp :: *)  :: *
class ((h :: w -> *) `Handles` (op :: w -> w -> *)) where
  clause :: op i j -> (Return (op i j) -> h j -> Result (h j)) -> h i -> Result (h i)
newtype Comp h i j a = Comp {handle :: (a -> h j -> Result (h j)) -> h i -> Result (h i)}

doOp :: (h `Handles` op) => op i j -> Comp h i j (Return (op i j))
doOp op = Comp (\k h -> clause op k h)

instance PaMonad (Comp h) where
  paReturn v          = Comp (\k h -> k v h)
  paExtend f (Comp c) = Comp (\k h -> c (\x h' -> handle (f x) k h') h)

instance Functor (Comp h i j) where
  fmap f c = c =>= \x -> paReturn (f x)

data Get (i :: *) (o :: *) where
  Get :: Get i i
type instance Return (Get i i) = i
get :: (h `Handles` Get) => Comp h i i i
get = doOp Get

data Put (i :: *) (o :: *) where
  Put :: o -> Put i o
type instance Return (Put i o) = ()
put :: (h `Handles` Put) => o -> Comp h i o ()
put s = doOp (Put s)

data State (a :: *) (s :: *) where
  State :: s -> State a s

type instance Result (State a s) = a
instance (State a `Handles` Get) where
  clause Get     k (State s) = k s (State s)
instance (State a `Handles` Put) where
  clause (Put s) k (State _) = k () (State s)


comp1 :: (h `Handles` Get, h `Handles` Put) => Comp h Int Char String
comp1 = get =>= (\n ->
        put 'a' =>= (\() ->
        get =>= (\c ->
        paReturn (show (n+1) ++ ":" ++ show c))))

test1 = handle comp1 (\s _ -> s) (State 20)

-- Forwarding is where things start to get interesting. Here's a
-- useless example of forwarding. This approach isn't going to scale
-- because it doesn't allow states to be transmitted across the
-- handler stack.
data Forward (h :: w -> *) (a :: *) (t :: w) (s :: w) where
  Forward :: Forward h a t s

type instance Result (Forward h a t s) = Comp h s t a
instance (h `Handles` op) => (Forward h a t `Handles` op) where
  clause op k Forward = doOp op =>= (\x -> k x Forward)
