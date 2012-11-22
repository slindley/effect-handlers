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
  type Result h :: * -> *
  ret :: h -> a -> Result h a

class (Op op, Handler h) => Handles h op where
  clause :: op -> h -> Param op -> (Return op -> Result h a) -> Result h a

newtype Comp h a = Comp {unComp :: forall b.h -> (a -> Result h b) -> Result h b}

instance Monad (Comp h) where
  return v     = Comp (\_ f -> f v)
  Comp c >>= f = Comp (\h k -> c h (\x -> case (f x) of
                                               Comp g -> g h k))

instance Functor (Comp h) where
  fmap f c = c >>= return . f

applyOp :: (h `Handles` op) => op -> Param op -> Comp h (Return op)
applyOp m p = Comp (\h k -> clause m h p k)

handle :: (Handler h) => Comp h a -> h -> Result h a
handle (Comp c) h = c h (ret h)


data Get s = Get
instance Op (Get s) where
  type Param  (Get s) = ()
  type Return (Get s) = s
get = applyOp Get

data Put s = Put
instance Op (Put s) where
  type Param  (Put s) = s
  type Return (Put s) = ()
put = applyOp Put


newtype Reader s a = Reader {unReader :: s -> a}

data StateHandler s = StateHandler
instance Handler (StateHandler s) where
  type Result (StateHandler s) = Reader s
  ret _ x = Reader $ \s -> x

instance (StateHandler s `Handles` Put s) where
  clause _ _ s k = Reader (\_ -> unReader (k ()) s)

instance (StateHandler s `Handles` Get s) where
  clause _ _ _ k = Reader (\s -> unReader (k s) s)

count =
    do {n <- get ();
        if n == (0 :: Int) then return ()
        else do {put (n-1); count}}


data ForwardHandler h = ForwardHandler
instance Handler (ForwardHandler h) where
  type Result (ForwardHandler h) = Comp h
  ret _ = return

instance (h `Handles` op) => ForwardHandler h `Handles` op where
  clause m h p k =
    Comp (\h' k' ->
           clause m h' p (\x -> unComp (k x) h' k'))

                   
data Choice = Choice
instance Op Choice where
  type Param Choice = ()
  type Return Choice = Bool
choice = applyOp Choice ()


newtype CompList h a = CompList {unCompList :: Comp h [a]}

data HandleAll h = HandleAll
instance Handler (HandleAll h) where
  type Result (HandleAll h) = CompList h
  ret _ x = CompList $ return [x]

instance (HandleAll h `Handles` Choice) where
  clause _ _ p k = CompList (do {x <- unCompList $ k True; y <- unCompList $ k False; return (x ++ y)})

instance (h `Handles` op) => HandleAll h `Handles` op where
  clause m h p k =
    CompList
    (Comp (\h' k' ->
            clause m h' p (\x -> unComp (unCompList (k x)) h' k')))

--chooseFood :: Monad m => m Bool -> m String
chooseFood =
  do
    x <- choice
    fruit <- if x then get() 
             else return $ "orange"
    y <- choice
    let form = if y then "raw " else "cooked "
    return (form ++ fruit)


