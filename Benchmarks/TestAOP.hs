import Criterion.Main
import Criterion.Config

import qualified Examples.AOP as H
import Benchmarks.AOPTestExprs as HE

import qualified Benchmarks.MRI_code.Interpreters as M
import Benchmarks.MRITestExprs as ME

b1024 = bgroup "1024" [ bgroup "log" [ bcompare [ bench "mixins"   $ whnf last (M.logtest ME.e1024)
                                                , bench "handlers" $ whnf last (H.logtest HE.e1024) ] ]
                      , bgroup "logdump" [ bcompare [ bench "mixins"   $ whnf last (M.logdumptest ME.e1024)
                                                    , bench "handlers" $ whnf last (H.logdumptest HE.e1024) ] ] ]

b2048 = bgroup "2048" [ bgroup "log" [ bcompare [ bench "mixins"   $ whnf last (M.logtest ME.e2048)
                                                , bench "handlers" $ whnf last (H.logtest HE.e2048) ] ]
                      , bgroup "logdump" [ bcompare [ bench "mixins"   $ whnf last (M.logdumptest ME.e2048)
                                                    , bench "handlers" $ whnf last (H.logdumptest HE.e2048) ] ] ]

b4096 = bgroup "4096" [ bgroup "log" [ bcompare [ bench "mixins"   $ whnf last (M.logtest ME.e4096)
                                                , bench "handlers" $ whnf last (H.logtest HE.e4096) ] ]
                      , bgroup "logdump" [ bcompare [ bench "mixins"   $ whnf last (M.logdumptest ME.e4096)
                                                    , bench "handlers" $ whnf last (H.logdumptest HE.e4096) ] ] ]

main = defaultMain ([b1024, b2048, b4096])
