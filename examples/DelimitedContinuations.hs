-- delimited continuations with effect handlers

{-# LANGUAGE TypeFamilies,
             FlexibleContexts, TypeOperators,
             MultiParamTypeClasses,
             OverlappingInstances, UndecidableInstances,
             FlexibleInstances,
             QuasiQuotes
  #-}

import DesugarHandlers
import Handlers

[operation|forall a.Shift0 r :: ((a -> r) -> r) -> a|]
[handler|
  Reset0 r a :: r polyhandles {Shift0 r} where
    Return x   -> x
    Shift0 p k -> p k
|]

[operation|forall a.Shift h r :: ((a -> r) -> Comp (Reset h r a) r) -> a|]
[handler|
  Reset h r a :: r polyhandles {Shift h r} where
    Return x   -> x
    Shift p  k -> reset (p k)
|]

-- Note that reset requires recursion (both in the terms and the
-- types), but reset0 does not.

-- We can define versions of reset0 and reset that forward other
-- operations...  This is a matter of replacing each of the 'raw'
-- instances of r in the types of Shift0 and Shift0 with Comp h r.
[operation|forall a.Shift0F h r :: ((a -> Comp h r) -> Comp h r) -> a|]
[handler|
  forward h.
    Reset0F r a :: r polyhandles {Shift0F h r} where
      Return x    -> return x
      Shift0F p k -> p k
|]

[operation|forall a.ShiftF h r :: ((a -> Comp h r) -> Comp (ResetF h r a) r) -> a|]
[handler|
  forward h. 
    ResetF r a :: r polyhandles {ShiftF h r} where
      Return x    -> return x
      ShiftF p  k -> resetF (p k)
|]
