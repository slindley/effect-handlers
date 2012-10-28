{- Just for the hell of it, here's a slightly refactored version of
the standard OpenHandlers library, that makes explicit use of the
continuation monad.

It isn't so convenient to use in this form, but it yields a five line
implementation of handlers in GHC.

 -}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses,
    TypeOperators,
    NoMonomorphismRestriction #-}

module OpenHandlers where

import Control.Monad.Cont

{- Five line handlers library :-) -}
type family Return op :: *
type family Result h :: *
class h `Handles` op where doOp :: op -> Comp h (Return op)
type Comp h a = Cont (h -> Result h) a
handle = runCont
{----------------------------------}

-- polymorphic operations
class h `PolyHandles` op where polyDoOp :: op a -> Comp h (Return (op a))

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
  doOp Get = cont (\k (StateHandler s) -> k s (StateHandler s))
instance (StateHandler s a `Handles` Put s) where
  doOp (Put s) = cont (\k _ -> k () (StateHandler s))

countTest =
    do {n <- get;
        if n == (0 :: Int) then return ()
        else do {put (n-1); countTest}}
