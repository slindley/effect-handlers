{- Handlers using a free monad -}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses,
    GADTs,
    TypeOperators,
    RankNTypes,
    FunctionalDependencies,
    TypeSynonymInstances,
    FlexibleInstances,
    FlexibleContexts,
    ScopedTypeVariables,
    PolyKinds
  #-}

module FreeHandlers where

type family Return (opApp :: *) :: *
type family Result (h :: *) :: *
class ((h :: *) `Handles` (op :: j -> k -> *)) (e :: j) | h op -> e where
  clause :: op e u -> (Return (op e u) -> h -> Result h) -> h -> Result h

data Comp h a where
  Ret :: a -> Comp h a
  Do  :: (h `Handles` op) e => op e u -> (Return (op e u) -> Comp h a) -> Comp h a
instance Monad (Comp h) where
  return        = Ret
  Ret v   >>= f = f v
  Do op k >>= f = Do op (\x -> k x >>= f)

doOp :: (h `Handles` op) e => op e u -> Comp h (Return (op e u))
doOp op = Do op return

handle :: Comp h a -> (a -> h -> Result h) -> h -> Result h
handle (Ret v) r h   = r v h
handle (Do op k) r h = clause op (\v h' -> handle (k v) r h') h


-- pure handlers
data PureHandler a = PureHandler
type instance Result (PureHandler a) = a

handlePure :: Comp (PureHandler a) a -> a
handlePure comp = handle comp (\x _ -> x) PureHandler

-- [handler|IOHandler a :: IO a where
--   Return x -> return x
-- |]
data IOHandler (a :: *) = IOHandler
type instance Result (IOHandler a) = IO a

handleIO :: Comp (IOHandler a) a -> IO a
handleIO comp = handle comp (\x _ -> return x) IOHandler 

-- [operation|Get s :: s|]
-- -- data Get (e :: *) (u :: *) where
-- --   Get :: Get s ()
-- -- type instance Return (Get s '()) = s
-- -- get :: ((h `Handles` Get) s) => Comp h s
-- -- get = doOp Get

-- [operation|Put s :: s -> ()|]
-- -- data Put (e :: *) (u :: *) where
-- --   Put :: s -> Put s '()
-- -- type instance Return (Put s '()) = ()
-- --put :: ((h `Handles` Put) s) => s -> Comp h ()
-- --put s = doOp (Put s)

-- -- [handles| h {Get s, Put s}|]

-- --type SComp s a = ((h `Handles` Get) s, (h `Handles` Put) s) => Comp h a
-- --type SComp s a = (Handles h Get s, Handles h Put s) => Comp h a
-- type SComp s a = ([handles|h {Get s}|], [handles|h {Put s}|]) => Comp h a

-- -- unfortunately this doesn't work...  We have a choice of parsing a
-- -- type or a declaration. A single constraint is a type,
-- -- but a collection of constraints is a predicate.

-- -- type SComp s a = ([handles|h {Get s, Put s}|]) => Comp h a

-- [handler|
--   StateHandler s a :: s -> a handles {Get s, Put s} where
--     Return x   _ -> x
--     Get      k s -> k s s
--     Put s    k _ -> k () s 
-- |]
-- -- newtype StateHandler (s :: *) (a :: *) = StateHandler s
-- -- type instance Result (StateHandler s a) = a
-- -- instance ((StateHandler s a `Handles` Get) s) where
-- --   clause Get k (StateHandler s) = k s (StateHandler s)
-- -- instance ((StateHandler s a `Handles` Put) s) where
-- --   clause (Put s) k _ = k () (StateHandler s)

-- countTest :: () -> SComp Int ()
-- countTest () =
--     do {n <- get;
--         if n == 0 then return ()
--         else do {put (n-1); countTest ()}}
