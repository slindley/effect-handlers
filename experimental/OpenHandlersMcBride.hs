{- Parameterised open McBride handlers -}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses,
    TypeOperators, GADTs,
    NoMonomorphismRestriction #-}

module OpenHandlersMcBride where

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

-- newtype Comp h a = Comp {handle :: (a -> h -> Result h) -> h -> Result h}

-- instance Monad (Comp h) where
--   return v = Comp (\k -> k v)
--   (>>=)  = undefined
-- --   return v     = Comp (\f k h -> k (f v) h)
-- --   Comp c >>= g = Comp (\f k h -> c (\x -> undefined) undefined h)
-- --  return v     = Comp (\f k h -> k (f v) h)
-- --  Comp c >>= g = Comp (\f k h -> c (\a -> handle (g a) f k h) undefined h) --f (\x h' -> handle (g x) f k h') h)


-- doOp :: (h `Handles` op) => op -> Comp h (Return op)
-- doOp op = Comp (\k h -> clause op (\x -> Comp (\k' -> k x)) h)
--doOp op = Comp (\k h -> clause op (\x -> return (k x h)) h) -- Comp (\k' h' -> k x h')) h)
--doOp op = Comp (\k h -> clause op (\x -> return (k x h)) h)
--doOp op = Comp (\f k h -> clause op (\x -> return (k x h)) h)


-- newtype Comp h a = Comp {handle :: (Inner h -> h -> Result h) -> (a -> Inner h) -> h -> Inner h}

--newtype Comp h a = Comp {handle :: (((a -> Inner h) -> Inner h) -> h -> Result h) -> h -> Result h}

-- newtype Comp h a = Comp {handle :: (a -> (Inner h -> h -> Result h) -> h -> Result h)) -> (Inner h -> h -> Result h) -> h -> Result h}


-- instance Monad (Comp h) where
--   return = undefined
--   (>>=)  = undefined
--   return v     = Comp (\f k h -> k (f v) h)
--   Comp c >>= g = Comp (\f k h -> c (\a -> handle (g a) f k h) undefined h) --f (\x h' -> handle (g x) f k h') h)

-- instance Functor (Comp h) where
--   fmap f c = c >>= \x -> return (f x)

-- doOp :: (h `Handles` op) => op -> Comp h (Return op)
-- doOp op = Comp (\k h -> clause op (\x -> return (k x h)) h)
-- doOp op = Comp (\f k h -> clause op (\x -> return (k x h)) h)

-- -- forward :: (h `Handles` op) => op -> h' -> (h' -> Return op -> Comp h a) -> Comp h a
-- -- forward op h k = doOp op >>= k h

-- -- polymorphic operations
-- class (h `PolyHandles` op) where
--   polyClause :: op a -> (Return (op a) -> h -> Inner h) -> h -> Result h

-- polyDoOp :: (h `PolyHandles` op) => op a -> Comp h (Return (op a))
-- polyDoOp op = Comp (\_ k h -> polyClause op (\x -> return (k x h)) h)

-- -- pure handlers
-- data PureHandler a = PureHandler
-- type instance Result (PureHandler a) = a
-- type instance Inner  (PureHandler a) = a

-- handlePure :: Comp (PureHandler a) a -> a
-- handlePure c = handle c (\x _ -> x) (\x _ -> x) PureHandler 

-- data Get s = Get
-- type instance Return (Get s) = s
-- get = doOp Get

-- newtype Put s = Put s
-- type instance Return (Put s) = ()
-- put s = doOp (Put s)

-- -- newtype StateHandler s a = StateHandler s
-- -- type instance Result (StateHandler s a) = a
-- -- instance (StateHandler s a `Handles` Put s) where
-- --   clause (Put s) k h = stateHandler s (k ())
-- -- instance (StateHandler s a `Handles` Get s) where
-- --   clause Get k (StateHandler s) = stateHandler s (k s)
-- -- stateHandler s comp = handle comp (\x _ -> x) (StateHandler s)

-- -- countTest =
-- --     do {n <- get;
-- --         if n == (0 :: Int) then return ()
-- --         else do {put (n-1); countTest}}
