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

shift' :: (Shift r a e `NotIn` e) =>
          ((a -> r) -> Comp (Shift r a e, e) r) -> Comp (Shift r a e, e) a
shift' = shift

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

shift0' :: (Shift0 r a `NotIn` e) => ((a -> r) -> r) -> Comp (Shift0 r a, e) a
shift0' = shift0


reset0 :: Comp (Shift0 r a, ()) r -> r
reset0 = reset0H Empty

reset0H :: (Shift0 r a `NotIn` e) => OpHandler e r -> Comp (Shift0 r a, e) r -> r
reset0H h c = handle c (Shift0 |-> (\p k -> p k) :<: h, id)

data H a b = H a (a -> b) | HV b

--prompt0 e  = hr_prop (reset0 (do {v <- e; return $ HV v}))
prompt0 e  = hr_prop (reset (do {v <- e; return $ HV v}))
control0 c = shift' (\k -> return $ H (hs_prop' . k) c)

hr_stop (H f x) = reset $ x f
hr_stop (HV x)  = reset $ x

hs_stop = hr_stop

hr_prop (H f x) = x f
hr_prop (HV x)  = x

-- hs_prop
--   :: NotIn (Shift0 (H (a -> b) ((a -> b) -> b) c) b) e =>
--      (H (a -> b) ((a -> b) -> b) c -> b)
--      -> H (a -> b) ((a -> b) -> b) b
--      -> Comp (Shift0 (H (a -> b) ((a -> b) -> b) c) b, e) b
-- hs_prop q (H f x) = shift0' (\g -> H (q . g . f) x)
-- hs_prop q (HV x)  = return x

newtype Bar a e = Bar {unBar ::
                           Comp (Shift (H (a -> Bar a e) (Bar a e))
                                           (Bar a e) e, e) (Bar a e)}

hs_prop'
  :: NotIn (Shift (H (a -> Bar a e) (Bar a e)) (Bar a e) e) e =>
       H (a -> Bar a e) (Bar a e) ->
       Bar a e
-- -- hs_prop'
-- --   :: NotIn (Shift (H (a -> Bar a e) ((a -> Bar a e) -> Bar a e) (Bar a e)) (Bar a e) e) e =>
-- --      (H (a -> Bar a e) ((a -> Bar a e) -> Bar a e) (Bar a e) -> Bar a e)
-- --      -> H (a -> Bar a e) ((a -> Bar a e) -> Bar a e) (Bar a e)
-- --      -> Comp (Shift (H (a -> Bar a e) ((a -> Bar a e) -> Bar a e) (Bar a e)) (Bar a e) e, e) (Bar a e)
-- -- hs_prop'
-- --   :: NotIn (Shift (H (a -> b) ((a -> b) -> b) b) b e) e =>
-- --      (H (a -> b) ((a -> b) -> b) b -> b)
-- --      -> H (a -> b) ((a -> b) -> b) b
-- --      -> Comp (Shift (H (a -> b) ((a -> b) -> b) b) b e, e) b
hs_prop' (H f x) = Bar $ shift' (\g -> return $ H (hs_prop' . g . f) x)
hs_prop' (HV x)  = Bar $ return x