{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction, RankNTypes,
    MultiParamTypeClasses, FlexibleInstances, OverlappingInstances,
    FlexibleContexts, TypeOperators, UndecidableInstances,
    QuasiQuotes
  #-}

import Control.Monad

import Handlers
import DesugarHandlers

[operation|forall a.Fail :: a|]
[operation|forall a.Choose :: [a] -> a|]

type Logic a = (h `PolyHandles` Fail, h `PolyHandles` Choose) => Comp h a


[handler|
  forward h.  LHandler a ::  [ a ]
    polyhandles {Fail, Choice} where
      Fail _ -> return []
      Choice l k -> mapM k l
      Return x            -> return [x]
|]

allResults :: Logic a -> Comp h a 
allResults comp = lHandler comp

