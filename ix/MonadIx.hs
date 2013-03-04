{-# LANGUAGE
    DataKinds, PolyKinds, TypeOperators, RankNTypes, GADTs,
    FlexibleInstances, UndecidableInstances
 #-}

module MonadIx where

import Unsafe.Coerce

import FunctorIx

class FunctorIx m => MonadIx (m :: (i -> *) -> (i -> *)) where
  returnIx :: a :-> m a
  extendIx :: (a :-> m b) -> (m a :-> m b)

seqIx :: MonadIx m => (a :-> m b) -> (b :-> m c) -> (a :-> m c)
seqIx f g = extendIx g . f

(?>=) :: MonadIx m => m s i -> (s :-> m t) -> m t i
(?>=) = flip extendIx

(?>>) :: MonadIx m => m s i -> (forall j.m t j)  -> m t i
p ?>> q = p ?>= (\_ -> q)

-- instance MonadIx m => FunctorIx (m :: (i -> *) -> (i -> *)) where
--   mapIx f c = c ?>= (returnIx . f)

infix 3 :=
data (:=) :: * -> i -> i -> * where
  V :: a -> (a := x) x
  
ret ::  MonadIx m => forall (a :: *) (i :: i) . a -> m (a := i) i
ret a = returnIx (V a)

-- The type of knownState expands to:
--
--   (a -> t i) -> (forall j.(a := i) j -> t j)
--
-- The reason knownState is well-typed is that although the second
-- argument is defined for (a := i) j for every j, the only
-- inhabitants of this family of types (of the form V x) have type (a
-- := i) j with j == i, at which point applying f to x returns a
-- value of type t i == t j.
knownState :: (a -> t i) -> (a := i) :-> t
knownState f (V x) = f x

(=>=) :: MonadIx m => m (a := j) i -> (a -> m t j) -> m t i
c =>= f = c ?>= knownState f

----- parameterised monads
-- Every monad on indexed types gives rise to a parameterised monad
-- over ordinary types.
class PaMonad (m :: w -> w -> * -> *) where
  paReturn :: a -> m i i a
  paExtend :: (a -> m j k b) -> (m i j a  -> m i k b)

newtype PaMonadIx m i j a = PaMonadIx {unPaMonadIx :: (m (a := j) i)}
instance MonadIx m => PaMonad (PaMonadIx m) where
  paReturn v               = PaMonadIx (returnIx (V v))
  paExtend f (PaMonadIx c) = PaMonadIx $ c =>= (\x -> unPaMonadIx (f x))

type Atkey m i j a = m (a := j) i
returnP :: MonadIx m => a -> Atkey m i i a
returnP v = returnIx (V v)

extendP :: MonadIx m => (a -> Atkey m j k b) -> Atkey m i j a -> Atkey m i k b
extendP f c = c =>= f
-----

-- Note that the name of the kind variable (w) must be distinct from
-- the names of the type variable (i) as the former is bound in the
-- function definitions.
class FunctorIx m => ApplicativeP (m :: (w -> *) -> (w -> *)) where
  pure  :: x -> Atkey m i i x
  (|*|) :: Atkey m i j (s -> t) -> Atkey m j k s -> Atkey m i k t

-- data (p :>>: q) r i = p i :& (q :-> r)

-- instance FunctorIx (p :>>: q) where
--   mapIx h (p :& k) = p :& (h . k)


----- path stuff
data Path :: ((i,i) -> *) -> ((i,i) -> *) where
  Nil :: Path r '(i,i)
  (:-:) :: r '(i,j) -> Path r '(j,k) -> Path r '(i,k)

instance FunctorIx Path where
  mapIx f Nil = Nil
  mapIx f (r :-: rs) = f r :-: mapIx f rs

(+-+) :: Path r '(i,j) -> Path r '(j,k) -> Path r '(i,k)
Nil        +-+ ps = ps
(r :-: rs) +-+ ps = r :-: (rs +-+ ps)

instance MonadIx Path where
  returnIx              = splip $ \ r -> r :-: Nil
  extendIx f (r :-: rs) = f r +-+ extendIx f rs
  extendIx f Nil        = Nil

-- The unsafeCoerce is required because GHC makes things unnecessarily
-- complicated by adding a special 'Any' type to every kind.
splip :: forall (s :: (i,j) -> *) (t :: (i,j) -> *) .
           (forall i j . s '(i,j) -> t '(i,j)) -> s :-> t
splip = unsafeCoerce
-----
