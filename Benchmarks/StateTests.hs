import Criterion.Main
import Criterion.Config

import qualified Examples.PlainState as P
import qualified Examples.State as H
import qualified Examples.ShallowState as S
import qualified Examples.CodensityState as C
import qualified Examples.FreeState as F

iterations = 100000

pure    n = bench "pure"    $ whnf P.pure    n
monadic n = bench "monadic" $ whnf P.monadic n 

cont n = bgroup "cont"
         [ bench "simple"  $ whnf H.simple  n
         , bench "forward" $ whnf H.forward n ]
free n = bgroup "free"
         [ bench "simple"  $ whnf F.simple  n
         , bench "forward" $ whnf F.forward n ]
codensity n = bgroup "codensity"
              [ bench "simple"  $ whnf C.simple  n
              , bench "forward" $ whnf C.forward n ]
shallow n = bgroup "shallow"
            [ bench "simple"  $ whnf    S.simple  n
            , bench "forward" $ whnfIO (S.forward n) ]

comp n = [bcompare [pure n, monadic n, cont n, free n, codensity n, shallow n]]

main = defaultMain [bgroup (show iterations)      (comp iterations),
                    bgroup (show (10*iterations)) (comp (10*iterations))]
