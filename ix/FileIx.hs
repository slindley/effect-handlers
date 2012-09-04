{-# LANGUAGE
    DataKinds, PolyKinds, TypeOperators, RankNTypes, GADTs,
    FlexibleInstances, UndecidableInstances, ScopedTypeVariables,
    NoMonomorphismRestriction
 #-}

module FileIx where
       
import System.IO
import Control.Exception

import FunctorIx
import MonadIx       

data State :: * where
  Open   :: State
  Closed :: State

data SState :: State -> * where
  SOpen   :: SState 'Open
  SClosed :: SState 'Closed

infix 2 :>>:
data (p :>>: q) r i = p i :& (q :-> r)

instance FunctorIx (p :>>: q) where
  mapIx h (p :& k) = p :& (h . k)

infixr 1 :+:
data (f :+: g) p i = InL (f p i) | InR (g p i)
instance (FunctorIx f, FunctorIx g) => FunctorIx (f :+: g) where
  mapIx h (InL fp) = InL (mapIx h fp)
  mapIx h (InR gp) = InR (mapIx h gp)

type FH  -- :: (State -> *) -> (State -> *)
     =   FilePath := 'Closed :>>: SState
     :+: ()       := 'Open   :>>: Maybe Char := 'Open
     :+: ()       := 'Open   :>>: () := Closed 
         
data (:*) :: ((i -> *) -> (i -> *)) -> (i -> *) -> (i -> *) where
  Ret :: p i          -> (f :* p) i
  Do  :: f (f :* p) i -> (f :* p) i
  
instance FunctorIx f => MonadIx ((:*) f) where
  returnIx = Ret
  extendIx g (Ret p)  = g p
  extendIx g (Do ffp) = Do (mapIx (extendIx g) ffp)
  
instance FunctorIx f => FunctorIx ((:*) f) where
  mapIx f = extendIx (returnIx . f)

--pattern FOpen s k = Do (InL (V s :& k))
--pattern FGetC   k = Do (InR (InL (V () :& k)))
--pattern FClose  k = Do (InR (InR (V () :& k)))

fOpen :: FilePath -> (FH :* SState) 'Closed
fOpen s = Do (InL (V s :& Ret))
fGetC :: (FH :* (Maybe Char := 'Open)) 'Open
fGetC = Do (InR (InL (V () :& Ret)))
fClose :: (FH :* (() := 'Closed)) 'Open
fClose = Do (InR (InR (V () :& Ret)))

runFH :: (FH :* (a := 'Closed)) 'Closed -> IO a
runFH (Ret (V a)) = return a
runFH (Do (InL (V s :& k))) = catch
  (openFile s ReadMode >>= openFH (k SOpen))
  (\(_ :: IOException) -> runFH (k SClosed))
  where
    openFH :: (FH :* (a := 'Closed)) 'Open -> Handle -> IO a
    openFH (Do (InR (InR (V () :& k)))) h = hClose h >> runFH (k (V ()))
    openFH (Do (InR (InL (V () :& k)))) h = catch
      (hGetChar h >>= \c -> openFH (k (V (Just c))) h)
      (\(_ :: IOException) -> openFH (k (V Nothing)) h)

instance FunctorIx f => ApplicativeP ((:*) f) where
  pure      = returnP
  mf |*| ms = mf =>= \f -> ms =>= \s -> returnP (f s)

fileContents :: FilePath -> (FH :* (Maybe String := 'Closed)) 'Closed
fileContents p = fOpen p >>- \b -> case b of
  SClosed -> pure Nothing
  SOpen   -> pure (\s _ -> Just s) |*| readOpenFile |*| fClose

readOpenFile :: (FH :* (String := 'Open)) 'Open
readOpenFile = fGetC =>= \x -> case x of
  Nothing -> pure ""
  Just c  -> pure (c:) |*| readOpenFile
