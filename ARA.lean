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
import ARA.Algorithms.KargerStein.KargerStein
import ARA.Algorithms.ReservoirSampling.ReservoirSampling
import ARA.Algorithms.Freivalds.Freivalds
import ARA.Algorithms.SchwartzZippel.SchwartzZippel
import ARA.Algorithms.CouponCollector.CouponCollector
import ARA.Algorithms.FisherYates.FisherYates
import ARA.Algorithms.Treap.Treap

/-!
# ARA — Analysis of Randomized Algorithms

A framework for analyzing randomized algorithms in Lean 4, designed so
that one algorithm definition serves both as an executable program and
as the object of formal correctness and complexity proofs.

This root module imports the whole framework; `lake build` builds
everything. The library is organized in three layers:

* `ARA/Infrastructure/` — the engine a user never has to modify:
  the cost transformer (`TimeMT`), the randomness interface
  (`RandMonad`/`LawfulRandMonad`), abstract cost ticks (`MonadCost`),
  expected cost and output-functional expectations (`ExpectedCost`),
  Markov tail bounds (`TailBounds`), the success-amplification
  combinator (`Amplify`),
  the correctness recipes (`Correctness`), and the simp sets/tactics
  (`SimpAttr`, `Tactics`).
* `ARA/Helpers/` — shared mathematics used by several algorithms
  (e.g. `Partition`: pivot-partition list lemmas and rank reindexing).
* `ARA/Algorithms/` — the case studies proving the framework usable,
  and `Tutorial`, the copy-me template for verifying your own
  algorithm. **Start there.**

## Design

The design rationale — the shallow no-embedding choice, `PMF` and the
Giry monad, the one-definition-four-readings architecture, the
correctness tiers, and the known limitations — lives in `DESIGN.md`
at the repository root. The user-facing walkthrough is
`ARA/Algorithms/Tutorial.lean`.
-/
