{- Open handlers -}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses, FlexibleInstances,
    TypeOperators, ScopedTypeVariables, RankNTypes,
    NoMonomorphismRestriction #-}

module OpenHandlers where

-- Operations live in the Op type class.
--   Param is the parameter type of the operation.
--   Return is the return type of the operation.
class Op op where
  type Param op :: *
  type Return op :: *

class Handler h where
  type Result h :: *
  type Inner h :: *
  ret :: h -> Inner h -> Result h

class (Op op, Handler h) => Handles h op where
  clause :: op -> h -> Param op -> (Return op -> Result h) -> Result h

data Comp h a = Comp {unComp :: h -> (a -> Result h) -> Result h}

instance Monad (Comp h) where
  return v     = Comp (\_ f -> f v)
  Comp c >>= f = Comp (\h k -> c h (\x -> unComp (f x) h k))

instance Functor (Comp h) where
  fmap f c = c >>= return . f

applyOp :: (h `Handles` op) => op -> Param op -> Comp h (Return op)
applyOp m p = Comp (\h k -> clause m h p k)

handle :: (Handler h) => Comp h (Inner h) -> h -> Result h
handle (Comp c) h = c h (ret h)


data Get s = Get
instance Op (Get s) where
  type Param  (Get s) = ()
  type Return (Get s) = s
get = applyOp Get ()

data Put s = Put
instance Op (Put s) where
  type Param  (Put s) = s
  type Return (Put s) = ()
put = applyOp Put


data StateHandler s a = StateHandler
instance Handler (StateHandler s a) where
  type Result (StateHandler s a) = s -> a
  type Inner (StateHandler s a)  = a
  ret _ x = \s -> x

instance (StateHandler s a `Handles` Put s) where
  clause _ _ s k = (\_ -> k () s)

instance (StateHandler s a `Handles` Get s) where
  clause _ _ _ k = (\s -> k s s)

count =
    do {n <- get;
        if n == (0 :: Int) then return ()
        else do {put (n-1); count}}


data ForwardHandler h a = ForwardHandler
instance Handler (ForwardHandler h a) where
  type Result (ForwardHandler h a) = Comp h a
  type Inner (ForwardHandler h a)  = a
  ret _ = return

instance (h `Handles` op) => ForwardHandler h a `Handles` op where
  clause m h p k =
    Comp (\h' k' ->
           clause m h' p (\x -> unComp (k x) h' k'))

                   
data Choice = Choice
instance Op Choice where
  type Param Choice = ()
  type Return Choice = Bool
choice = applyOp Choice ()



data HandleAll h a = HandleAll
instance Handler (HandleAll h a) where
  type Result (HandleAll h a) = Comp h [a]
  type Inner (HandleAll h a)  = a
  ret _ x = return [x]

instance (HandleAll h a `Handles` Choice) where
  clause _ _ p k = do {x <- k True; y <- k False; return $ x ++ y}
  
instance (h `Handles` op) => HandleAll h a `Handles` op where
  clause m h p k =
    Comp (\h' k' ->
           clause m h' p (\x -> unComp (k x) h' k'))

--chooseFood :: Monad m => m Bool -> m String
chooseFood =
  do
    x <- choice
    fruit <- if x then get 
             else return $ "orange"
    y <- choice
    let form = if y then "raw " else "cooked "
    return (form ++ fruit)


