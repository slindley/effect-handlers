{- Encoding lists as computations -}

{-# LANGUAGE TypeFamilies,
    RankNTypes, GADTs,
    MultiParamTypeClasses, QuasiQuotes, FlexibleInstances,
    OverlappingInstances, UndecidableInstances,
    FlexibleContexts #-}

import Control.Monad
import Handlers
import TopLevel
import DesugarHandlers

[operation|Choose :: Bool|]
[operation|Element a :: a -> ()|]

[operation|forall r.Singleton a :: a -> r|]
[operation|forall r.Nil :: r|]

-- helper functions: choose and element are really just CPS versions
-- of append and cons

append xs ys = do b <- choose; if b then xs else ys
cons x xs = do element x; xs

type AppendList a =
  forall h r.
    ([handles|h {Choose}|],    [handles|h {Singleton a}|], [handles|h {Nil}|]) => Comp h r
type ConsList a =
  forall h r.
    ([handles|h {Element a}|], [handles|h {Nil}|]) => Comp h r
-- work-around for limitations in GHC type inference
newtype WrappedList a = Wrap {unWrap :: ConsList a}

-- flatten an append list into a cons list
--
-- this is really just a CPS version of a standard flattening function
[handler|
  FlattenIt a :: WrappedList a -> WrappedList a handles {Choose, Singleton a, Nil} where
    Return x      xs -> undefined
    Choose      k xs -> k True (k False xs)
    Singleton x k xs -> Wrap $ cons x (unWrap xs)
    Nil         k xs -> xs
|]
flatten :: AppendList a -> ConsList a
flatten t = unWrap (flattenIt (Wrap nil) t)

-- convert a cons list computation into a vanilla GHC list
[handler|
  AsList a :: [a] handles {Element a, Nil} where
    Return x      -> undefined
    Element x   k -> x : k ()
    Nil         k -> []
|]

test1 = asList (flatten (append (append (singleton 1) (singleton 2)) (singleton 3)))
