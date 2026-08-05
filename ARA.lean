/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import ARA.Infrastructure.SimpAttr
import ARA.Infrastructure.Tactics
import ARA.Infrastructure.Randomness.LawfulRandMonad
import ARA.Infrastructure.Randomness.Prob
import ARA.Infrastructure.Randomness.RandVec
import ARA.Infrastructure.Randomness.SPMF
import ARA.Infrastructure.Randomness.Geometric
import ARA.Infrastructure.Complexity.TimeMT
import ARA.Infrastructure.Complexity.MonadCost
import ARA.Infrastructure.Complexity.TimedSemantics
import ARA.Infrastructure.Complexity.ExpectedCost
import ARA.Infrastructure.Complexity.SamplerCosts
import ARA.Infrastructure.Complexity.Variance
import ARA.Infrastructure.Complexity.TailBounds
import ARA.Infrastructure.Correctness.Correctness
import ARA.Infrastructure.Correctness.Amplify
import ARA.Helpers.Partition
import ARA.Helpers.MultiGraph
import ARA.Helpers.HarmonicSums
import ARA.Helpers.Counting
import ARA.Algorithms.Tutorial
import ARA.Algorithms.Quicksort.Quicksort
import ARA.Algorithms.Quickselect.Quickselect
import ARA.Algorithms.Karger.Karger
import ARA.Algorithms.Karger.KargerVariants
import ARA.Algorithms.Karger.KargerOrder
import ARA.Algorithms.Karger.KargerEnum
import ARA.Algorithms.Karger.KargerFresh
import ARA.Algorithms.KargerStein.KargerStein
import ARA.Algorithms.ReservoirSampling.ReservoirSampling
import ARA.Algorithms.Freivalds.Freivalds
import ARA.Algorithms.SchwartzZippel.SchwartzZippel
import ARA.Algorithms.CouponCollector.CouponCollector
import ARA.Algorithms.FisherYates.FisherYates
import ARA.Algorithms.Treap.Treap

/-!
# ARA — Analysis of Randomized Algorithms

This root module imports the whole framework; `lake build` builds
everything. The library is organized in three layers:

* `ARA/Infrastructure/`:
  the cost transformer (`TimeMT`), the randomness interface
  (`RandMonad`/`LawfulRandMonad`), abstract cost ticks (`MonadCost`),
  expected cost and output-functional expectations (`ExpectedCost`),
  Markov tail bounds (`TailBounds`), the success-amplification
  combinator (`Amplify`),
  the correctness recipes (`Correctness`), and the simp sets/tactics
  (`SimpAttr`, `Tactics`).

* `ARA/Helpers/`: shared mathematics used by several algorithms
  (e.g. `Partition`: pivot-partition list lemmas and rank reindexing).

* `ARA/Algorithms/`: some case studies proving the framework usable,
  and `Tutorial`, a self-contained tutorial on how to use the framework.
-/
