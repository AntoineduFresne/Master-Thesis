/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.Infrastructure.TimeMT
import ARA.Infrastructure.SimpAttr
import ARA.Infrastructure.Tactics
import ARA.Infrastructure.MonadCost
import ARA.Infrastructure.LawfulRandMonad
import ARA.Infrastructure.ExpectedCost
import ARA.Infrastructure.Correctness
import ARA.Helpers.Partition
import ARA.Algorithms.Tutorial
import ARA.Algorithms.Quicksort
import ARA.Algorithms.Quickselect
import ARA.Algorithms.Karger
import ARA.Algorithms.ReservoirSampling
import ARA.Algorithms.Freivalds
import ARA.Algorithms.Treap

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
