{- Parameterised open handlers factored through the continuation monad -}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses,
    TypeOperators,
    NoMonomorphismRestriction, 
    GeneralizedNewtypeDeriving
  #-}

module OpenHandlersCont where

import Control.Monad.Cont

type family Return op :: *
type family Result h :: *
class h `Handles` op where clause :: op -> (Return op -> h -> Result h) -> h -> Result h
newtype Comp h a = Comp {runComp :: Cont (h -> Result h) a}
  deriving (Functor, Monad)
doOp :: (h `Handles` op) => op -> Comp h (Return op)
doOp op = Comp (cont (\k h -> clause op k h))
handle comp = runCont (runComp comp)

-- polymorphic operations
class h `PolyHandles` op where polyClause :: op a -> (Return (op a) -> h -> Result h) -> h -> Result h
polyDoOp :: (h `PolyHandles` op) => op a -> Comp h (Return (op a))
polyDoOp op = Comp (cont (\k h -> polyClause op k h))

-- pure handlers
data PureHandler a = PureHandler
type instance Result (PureHandler a) = a

handlePure :: Comp (PureHandler a) a -> a
handlePure comp = handle comp (\x _ -> x) PureHandler

data IOHandler a = IOHandler
type instance Result (IOHandler a) = IO a

handleIO :: Comp (IOHandler a) a -> IO a
handleIO comp = handle comp (\x _ -> return x) IOHandler 

data Get s = Get
type instance Return (Get s) = s
get = doOp Get

newtype Put s = Put s
type instance Return (Put s) = ()
put s = doOp (Put s)

newtype StateHandler s a = StateHandler s
type instance Result (StateHandler s a) = a
instance (StateHandler s a `Handles` Get s) where
  clause Get k (StateHandler s) = k s (StateHandler s)
instance (StateHandler s a `Handles` Put s) where
  clause (Put s) k _ = k () (StateHandler s)

countTest =
    do {n <- get;
        if n == (0 :: Int) then return ()
        else do {put (n-1); countTest}}
