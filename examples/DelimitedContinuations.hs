-- delimited continuations with effect handlers

{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction,
             FlexibleContexts, TypeOperators #-}

import Handlers

--- shift/reset
data Shift r a e = Shift
instance Op (Shift r a e) where
  type Param (Shift r a e) = (a -> r) -> Comp (Shift r a e, e) r
  type Return (Shift r a e) = a

shift :: (Shift r a e `In` e') => ((a -> r) -> Comp (Shift r a e, e) r) -> Comp e' a
shift = applyOp Shift

reset :: Comp (Shift r a (), ()) r -> r
reset = resetH Empty

resetH :: (Shift r a e `NotIn` e) => OpHandler e r -> Comp (Shift r a e, e) r -> r
resetH h c = handle c (Shift |-> (\p k -> resetH h (p k)) :<: h, id)

-- Note that reset requires recursion, but reset0 defined below does
-- not. Also, because the operation clause for shift wraps a handler
-- around the body, it is necessary to add an additional effect
-- parameter to Shift.

--- shift0/reset0
data Shift0 r a = Shift0
instance Op (Shift0 r a) where
  type Param (Shift0 r a) = (a -> r) -> r
  type Return (Shift0 r a) = a

shift0 :: (Shift0 r a `In` e) => ((a -> r) -> r) -> Comp e a
shift0 = applyOp Shift0

reset0 :: Comp (Shift0 r a, ()) r -> r
reset0 = reset0H Empty

reset0H :: (Shift0 r a `NotIn` e) => OpHandler e r -> Comp (Shift0 r a, e) r -> r
reset0H h c = handle c (Shift0 |-> (\p k -> p k) :<: h, id)
