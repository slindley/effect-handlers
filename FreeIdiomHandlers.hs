{- Handlers for idioms -}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses,
    GADTs, FlexibleContexts, FlexibleInstances, UndecidableInstances,
    TypeOperators,
    RankNTypes,
    FunctionalDependencies,
    DataKinds, PolyKinds
  #-}

module FreeIdiomHandlers where

import Data.Maybe
import Control.Applicative

type family Return (opApp :: *) :: *
type family Result (h :: *) :: * -> *
class ((h :: *) `Handles` (op :: j -> k -> *)) (e :: j) | h op -> e where
  clause :: op e u -> (h -> Result h (Return (op e u) -> a)) -> h -> Result h a

{- type lists as right-nested products -}
type family RProd (ts :: [*]) :: *
type instance RProd '[]       = ()
type instance RProd (t ': ts) = (t, RProd ts)

{-
   heterogeneous lists wrt a functor f:
     
      FList f [a1,...,an] == [f a1,  ..., f ak]
-}
data FList (h :: *) (ts :: [*]) where
  FNil ::                                               FList f '[]
  (:>) :: (h `Handles` op) e => op e u -> FList h ts -> FList h (Return (op e u) ': ts)

{- type list concatenation -}
type family (ts :: [*]) :++: (ts' :: [*]) :: [*]
type instance '[]       :++: ts' = ts'
type instance (t ': ts) :++: ts' = t ': (ts :++: ts')

{- FList concatenation -}
(/++/) :: FList h ts -> FList h ts' -> FList h (ts :++: ts')
FNil      /++/ cs' = cs' 
(c :> cs) /++/ cs' = c :> (cs /++/ cs')

{- the free applicative functor -}
data FreeApp h a where
  FreeApp :: FList h ts -> (RProd ts -> a) -> FreeApp h a

instance Functor (FreeApp h) where
  fmap g (FreeApp cs f) = FreeApp cs (g . f)
  
instance Applicative (FreeApp h) where
  pure v                         = FreeApp FNil (\() -> v)
  FreeApp cs f <*> FreeApp cs' g =
     FreeApp (cs /++/ cs')
       (\xs -> let (ys, zs) = split cs cs' xs in f ys (g zs))

{- split an FList into two parts.

   The first two arguments direct where to split the list. Both are
necessary for type inference even though the second is never
deconstructed.
-}
split :: FList h ts -> f ts' ->
           RProd (ts :++: ts') -> (RProd ts, RProd ts')
split FNil      _    xs      = ((), xs)
split (c :> cs) cs'  (x, xs) = ((x, ys), zs) where
  (ys, zs) = split cs cs' xs

type Comp h a = FreeApp h a

doOp :: (h `Handles` op) e => op e u -> Comp h (Return (op e u))
doOp op = FreeApp (op :> FNil) fst

handle :: Comp h a -> (forall a.a -> h -> Result h a) -> h -> Result h a
handle (FreeApp FNil p)        r h = r (p ()) h
handle (FreeApp (op :> ops) p) r h =
  clause op (handle (FreeApp ops (\xs x -> p (x, xs))) r) h

{- formlets -}
data Text (e :: *) (u :: *) where 
  Text :: String -> Text () ()
type instance Return (Text () ()) = ()
text :: (h `Handles` Text) () => String -> Comp h ()
text s = doOp (Text s)

data Input (e :: *) (u :: *) where 
  Input :: String -> Input () ()
type instance Return (Input () ()) = String
input :: (h `Handles` Input) () => String -> Comp h String
input s = doOp (Input s)

data Elem (e :: *) (u :: *) where 
  Elem :: String -> Atts -> Comp h a -> Elem h a
type instance Return (Elem h a) = a
elem :: (h `Handles` Elem) h => String -> Atts -> Comp h a -> Comp h a
elem s atts body = doOp (Elem s atts body)

type Atts = [(String, String)]
data HtmlNode = HText String | HElem String Atts Html
type Html = [HtmlNode]
type Env = [(String, String)]

newtype Formlet a = Formlet {unF :: Int -> (Html, Env -> a, Int)}
data FormHandler = FormHandler
type instance Result FormHandler = Formlet

formHandler :: Comp FormHandler a -> Formlet a
formHandler comp = handle comp (\x h -> Formlet (\n -> ([], const x, n))) FormHandler

instance (FormHandler `Handles` Text) () where
  clause (Text s) k FormHandler =
    Formlet (\n -> let (xs, c, n') = unF (k FormHandler) n in
                       (HText s : xs,
                        \env -> c env (),
                        n'))
      
instance (FormHandler `Handles` Input) () where
  clause (Input s) k FormHandler =
    Formlet (\n -> let name = "x" ++ show n in
                   let (xs, c, n') = unF (k FormHandler) (n+1) in
                       (HElem "input" [("name", name)] [] : xs,
                        \env -> c env (fromJust (lookup name env)),
                        n'))

instance (FormHandler `Handles` Elem) FormHandler where
  clause (Elem s atts body) k FormHandler =
      Formlet (\n -> let (xs, c, n')   = unF (formHandler body) n in
                     let (ys, c', n'') = unF (k FormHandler) n' in
                         (HElem s atts xs : ys,
                          \env -> c' env (c env),
                          n''))

{- formlets with a parameterised handler -}
newtype Formlet' a = Formlet' {unF' :: (Html, Env -> a, Int)}
data FormHandler' = FormHandler' Int
type instance Result FormHandler' = Formlet'

formHandler' :: Int -> Comp FormHandler' a -> Formlet' a
formHandler' n comp =
  handle comp
        (\x (FormHandler' n') -> Formlet' ([], const x, n'))
        (FormHandler' n)

instance (FormHandler' `Handles` Text) () where
  clause (Text s) k (FormHandler' n) =
    Formlet' (let (xs, c, n') = unF' (k (FormHandler' n)) in
                  (HText s : xs,
                   \env -> c env (),
                   n'))

instance (FormHandler' `Handles` Input) () where
  clause (Input s) k (FormHandler' n) =
    Formlet' (let name = "x" ++ show n in
              let (xs, c, n') = unF' (k (FormHandler' (n+1))) in
                  (HElem "input" [("name", name)] [] : xs,
                   \env -> c env (fromJust (lookup name env)),
                   n'))

instance (FormHandler' `Handles` Elem) FormHandler' where
  clause (Elem s atts body) k (FormHandler' n) =
      Formlet' (let (xs, c,  n')  = unF' (formHandler' n body) in
                let (ys, c', n'') = unF' (k (FormHandler' n')) in
                    (HElem s atts xs : ys,
                     \env -> c' env (c env),
                     n''))
