{- Handlers for parameterised notions of computation.

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

{- Now we can implement the fully general form of shift0 (in which the
return type can change) -}
data Shift0 (a :: *) (i :: *) (o :: *) where
  Shift0 :: ((a -> o) -> i) -> Shift0 a i o
type instance Return (Shift0 a i o) = a

shift0 :: Handles h (Shift0 a) => ((a -> j) -> i) -> Comp h i j a
shift0 c = doOp (Shift0 c)

data Reset0 (a :: *) where
  Reset0 :: Reset0 a

type instance Result (Reset0 a) = a
instance (Reset0 `Handles` Shift0 a) where
   clause (Shift0 p) k Reset0 = p (\x -> k x Reset0)

reset0 :: Comp Reset0 i j j -> i
reset0 m = handle m (\x _ -> x) Reset0

comp2 :: Comp Reset0 Char Bool Bool
comp2 = shift0 (\k -> if k 42 then 'a' else 'b') =>= (\z ->
        paReturn $ z > 0)
test2 = reset0 comp2


comp3 :: (Int -> Bool) -> Comp Reset0 String Char Char
comp3 k = shift0 (\l -> (l $ if k 42 then "abc" else "xyz") : "def") =>= (\s ->
          paReturn $ head s)
comp3' :: Comp Reset0 (Comp Reset0 String Char Char) Bool Bool
comp3' = shift0 (\k -> comp3 k) =>= (\x ->
         paReturn $ x > 0)
comp3'' :: Comp Reset0 String Char Char
comp3'' = reset0 comp3'
test3' :: String
test3' = reset0 comp3''
test3 = reset0
         (reset0
           (shift0 (\k ->
              shift0 (\l -> (l $ if k 32 then "abc" else "xyz") : "def") =>= \s ->
              paReturn $ head s) =>= \x ->
            paReturn $ x > 0))


comp4 :: (Int -> Bool) -> Comp Reset0 Int String String
comp4 k = shift0 (\l -> length (l $ if k 42 then 'a' else 'x')) =>= \c ->
          paReturn $ [c, c]
comp4' :: Comp Reset0 (Comp Reset0 Int String String) Bool Bool
comp4' = shift0 (\k -> comp4 k) =>= \x ->
         paReturn $ x > 0
comp4'' :: Comp Reset0 Int String String
comp4'' = reset0 comp4' =>= \y -> paReturn $ y ++ y
test4' :: Int
test4' = reset0 comp4''
test4 = reset0
         (reset0
           (shift0 (\k ->
              shift0 (\l -> length (l $ if k 42 then 'a' else 'x')) =>= \s ->
              paReturn [s,s]) =>= \x ->
            paReturn $ x > 0) =>= \y ->
          paReturn $ y ++ y)


-- Forwarding is where things start to get interesting. Here's a
-- useless example of forwarding. This approach isn't going to scale
-- because it doesn't allow states to be transmitted across the
-- handler stack.
data Forward (h :: w -> *) (a :: *) (t :: w) (s :: w) where
  Forward :: Forward h a t s

type instance Result (Forward h a t s) = Comp h s t a
instance (h `Handles` op) => (Forward h a t `Handles` op) where
  clause op k Forward = doOp op =>= (\x -> k x Forward)
