-- delimited continuations with recursive effect handlers

{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction,
             FlexibleContexts, TypeOperators #-}

import RecursiveHandlers

-- prompt0H does not require recursion, but promptH, shift0H, shiftH
-- all do.

--- shift0/reset0
data Shift0 r a = Shift0
instance Op (Shift0 r a) where
  type Param (Shift0 r a) = (a -> r) -> r
  type Return (Shift0 r a) = a

shift0 :: (Shift0 r a `In` e) => ((a -> r) -> r) -> Comp e a
shift0 = applyOp Shift0

reset0 :: Comp (Shift0 r a, ()) r -> r
reset0 = reset0H Empty

reset0H :: (Shift0 r a `NotIn` e) => OpHandler e (Comp (Shift0 r a, e) r) r -> Comp (Shift0 r a, e) r -> r
reset0H h c = handle c (Shift0 |-> (\p k -> p (\v -> reset0H h $ k v)) :<: h, id)

--- shift/reset
data Shift r a e = Shift
instance Op (Shift r a e) where
  type Param (Shift r a e) = (a -> r) -> Comp (Shift r a e, e) r
  type Return (Shift r a e) = a

shift :: (Shift r a e `In` e') => ((a -> r) -> Comp (Shift r a e, e) r) -> Comp e' a
shift = applyOp Shift

reset :: Comp (Shift r a (), ()) r -> r
reset = resetH Empty

resetH :: (Shift r a e `NotIn` e) => OpHandler e (Comp (Shift r a e, e) r) r -> Comp (Shift r a e, e) r -> r
resetH h c = handle c (Shift |-> (\p k -> resetH h (p (\v -> resetH h $ k v))) :<: h, id)

--- control0/prompt0
data Control0 r a e = Control0
instance Op (Control0 r a e) where
  type Param (Control0 r a e) = (a -> Comp (Control0 r a e, e) r) -> r
  type Return (Control0 r a e) = a

control0 :: (Control0 r a e `In` e') => ((a -> Comp (Control0 r a e, e) r) -> r) -> Comp e' a
control0 = applyOp Control0

prompt0 :: Comp (Control0 r a (), ()) r -> r
prompt0 = prompt0H Empty

prompt0H :: (Control0 r a e `NotIn` e) => OpHandler e (Comp (Control0 r a e, e) r) r ->
                                            Comp (Control0 r a e, e) r -> r
prompt0H h c = handle c (Control0 |-> (\p k -> p k) :<: h, id)

--- control/prompt
data Control r a e = Control
instance Op (Control r a e) where
  type Param (Control r a e) = (a -> Comp (Control r a e, e) r) -> Comp (Control r a e, e) r
  type Return (Control r a e) = a

control :: (Control r a e `In` e') => ((a -> Comp (Control r a e, e) r) -> Comp (Control r a e, e) r) -> Comp e' a
control = applyOp Control

prompt :: Comp (Control r a (), ()) r -> r
prompt = promptH Empty

promptH :: (Control r a e `NotIn` e) => OpHandler e (Comp (Control r a e, e) r) r -> Comp (Control r a e, e) r -> r
promptH h c = handle c (Control |-> (\p k -> promptH h (p k)) :<: h, id)
