import Criterion.Main

-- SL: it seems that the fast version of Pipes no longer exists in the pipes library

import qualified Examples.PipesPipes as P
-- import qualified Examples.PipesPipesFast as R
import qualified Examples.Pipes as H
import qualified Examples.FreePipes as F
import qualified Examples.CodensityPipes as C
import qualified Examples.ShallowPipes as S

iterExp = 6
nestingDepth = 9

simple m = bgroup ("simple (10^" ++ show m ++ ")")
               [ bench "original"           $ whnf P.simple n
               -- , bench "original+rewrites"  $ whnf R.simple n
               , bench "handlers"           $ whnf H.simple n
               , bench "free"               $ whnf F.simple n
               , bench "codensity"          $ whnf C.simple n
               , bench "shallow"            $ whnf S.simple n ]
           where
             n = 10^m

nested n = bgroup ("nested (" ++ show n ++ ")")
               [ bench "original"           $ whnf P.nested n
               -- , bench "original+rewrites"  $ whnf R.nested n
               , bench "handlers"           $ whnf H.nested n
               , bench "free"               $ whnf F.nested n
               , bench "codensity"          $ whnf C.nested n
               , bench "shallow"            $ whnf S.nested n ]

main = defaultMain ([simple m|m <- [iterExp..iterExp+2]] ++
                    [nested d|d <- [nestingDepth..nestingDepth+4]])
