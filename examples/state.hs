{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction,
             FlexibleContexts, TypeOperators #-}

import Handlers

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

getClause :: Monad m => OpClause (Get s) (m (s -> m a))
getClause = Get |-> (\() k -> return (\v -> do { f <- k v; f v}))

-- note that because we have access to the continuation we can
-- interpret Put using a type that looks like the type of a reader
-- monad

putClause :: Monad m => OpClause (Put s) (m (s -> a))
putClause = Put |-> (\p k -> do { f <- k (); return (\_ -> f p)})

-- handle state in the standard way
handleState :: Monad m => s -> Comp (Get s, (Put s, ())) a -> m a
handleState = handleStateWith Empty

-- The handleStateWith function generalises handleState to support
-- horizontal composition, either for throwing other effects or for
-- composing with compatible effects such as random choice.
handleStateWith :: (Get s `NotIn` e, Put s `NotIn` e, Monad m) =>
                     OpHandler e (m (s -> m a)) -> s -> Comp (Get s, (Put s, e)) a -> m a
handleStateWith h s comp =
  do
    f <-
      (handle comp
       (getClause :<: putClause :<: h,
        \s -> return (\_ -> return s)))
    f s
