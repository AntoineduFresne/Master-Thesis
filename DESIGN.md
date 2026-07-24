# ARA — Design notes

Why the framework looks the way it does. The README says *what* is
here; this file says *why*.

## Where we sit in the design space

Formal reasoning about randomized algorithms spans a spectrum:

* **deep embeddings** — programs are syntax trees in an embedded
  probabilistic language; running time can be extracted *by
  construction*, but every algorithm and every proof fights the
  embedding;
* **no embedding / shallow** — algorithms are ordinary functions of
  the logic returning probability distributions; maximally expressive,
  but nothing connects the code to a cost model automatically;
* **hybrids** — deep programs related to distributions specified in
  the logic.

ARA is a **shallow, no-embedding** framework: an algorithm is an
ordinary Lean function written in `do`-notation, and its randomness is
abstracted by a typeclass. We get the full expressiveness of Lean
(recursion, dependent types, Mathlib) and pay one price the fact that **cost
annotations (`tick`) are trusted**. The `tick` calls state the cost
model; nothing checks that they match an operational semantics. This is
the same trade-off made by `TimeM` in cslib. A formal correspondence
between ticks and code structure is possible future work, but the
pragmatic gain — six verified algorithms with exact constants — comes
precisely from not paying the deep-embedding tax.

## Probability in the logic: `PMF` and the Giry monad

A distribution over `α` is a `PMF α`: a function `α → ℝ≥0∞` whose
values sum to `1` (Mathlib). Any such function induces a probability
measure (`PMF.toOuterMeasure`, `PMF.toMeasure`), and conversely a
measure with measurable singletons induces a `PMF`; the two views are
inverse to each other. What makes `PMF` a *programming* object is its
monad structure — the discrete Giry monad:

- `pure : α → PMF α` which takes a value and returns the distribution that is
  concentrated on that value (the Dirac distribution) i.e. assigns 1 to that
  value and 0 to all other values.

- `bind : PMF α → (α → PMF β) → PMF β` which for two types α and β:
  Takes (P,f) where :
  * P is a distribution over α, P : PMF α,
  * f is a function that assigns to each elements of α a distribution over β, f : α → PMF β
  Returns:
  the distribution over β obtained by "sampling" from the first distribution and
  then "sampling" from the second distribution. That is the probability of obtaining
  b in β from P.bind f is the sum over all a in α of the probability of a from P
  times the probability of obtaining b from f a, i.e. assigns b : β to the probability:
  ∑ a : α, P a * (f a) b

  It used concretely like this : pure x for pure x and P >>= f (or P.bind f) for bind (P,f).

The main advantage of having probability distributions in the logic is its
expressiveness and flexibility: 
we can state that an algorithm's output **is** a given distribution (not
merely that some property holds almost surely), compare two
differently-structured algorithms by proving their output or cost
distributions equal, and reuse all of Mathlib's `tsum`/`ENNReal`
machinery in the proofs.

## One definition, multiple readings (here four)

An algorithm is written once, polymorphic over
`{M} [Monad M] [RandMonad M] [MonadCost ℕ M]`:

* `RandMonad` supplies one primitive, uniform `randFin n` (every
  finite choice factors through it; `randIdx` is derived);
* `MonadCost` supplies `tick`, a no-op by default and accumulating in
  `TimeMT`;
* `LawfulRandMonad` gives the semantics: an interpretation `toPMF`
  respecting `pure`/`bind` and sending `randFin` to the uniform
  distribution. Proofs are stated against `toPMF`, so they hold for
  every lawful instance at once.

Instantiating `M` yields: `IO` (run it), `PMF` (the specification),
`TimeMT ℕ IO` (benchmark), and `TimeMT ℕ PMF` — the joint
distribution over (output, cost) pairs, which is where all expected
cost analysis happens. `TimeMT` is a writer-style transformer; the
earlier idea of a bespoke joint-distribution monad ("Rnd") became
unnecessary once cost was layered as a transformer over `PMF`.

## Correctness comes in tiers

Practice produced a classification we now build the API around:

1. **Dirac** (Las Vegas): the output distribution is a point mass at
   the spec — Quicksort, Quickselect. Automated by
   `toPMF_randIdx_bind_dirac` + `dirac_finish`; the user supplies only
   `@[spec_transport]` lemmas.
2. **Exact distribution**: the output law itself is the theorem —
   reservoir sampling's uniformity.
3. **Support + probability** (Monte Carlo): one-sided error via the
   support, plus a success-probability bound — Karger, Freivalds,
   treap shape analysis (via `expVal` for structural measures).

Costs likewise: upper bounds live in `ℝ≥0∞` (no summability
bookkeeping), exact formulas descend to `ℝ` via `toReal` with
finiteness supplied by the coarse bound. On top of expectations sits
the tail-bound tier (`TailBounds.lean`): Markov's inequality upgrades
any expected-cost theorem to `ℙ[cost m > k] ≤ 𝔼_{`Complexity/SamplerCosts`, not with the samplers):

```
cslib.TimeM ← Complexity/TimeMT ← Complexity/MonadCost ──────┐
Mathlib.PMF ← SimpAttr ← Tactics ← Randomness/LawfulRandMonad ┤
                                        │                     │
                                        ├← Randomness/Prob    └←──┬← Complexity/TimedSemantics
                                        │      │                  │           │
                                        │      ├← Randomness/Geometric        │
                                        │      ├← Randomness/RandVec          │
                                        │      │       (+ Helpers/Partition)  │
                                        │      ├← Complexity/Variance         │
                                        │      └← Complexity/ExpectedCost ←───┘
                                        │                │
                                        │                ├← Complexity/SamplerCosts (+ RandVec)
                                        │                ├← Complexity/TailBounds   (+ Variance)
                                        │                └← Correctness/Amplify     (+ Correctness)
                                        └←──┬← Correctness/Correctness
                 Complexity/MonadCost ←─────┘
Helpers/*     ← Mathlib only (pure mathematics, no Infrastructure;
                Infrastructure may consume Helpers — RandVec uses
                Partition's counting lemma)
Algorithms/*  ← Infrastructure + Helpers + fine-grained Mathlib extras
                (Treap consumes the Fisher–Yates shuffle; SchwartzZippel
                consumes Mathlib's `MvPolynomial.schwartz_zippel_totalDegree`)
```

`Prob.lean` is deliberately the lowest probability layer: a
pure-distribution study (`Geometric`, `CouponCollector`) uses
`expVal`, `𝔼[·}[cost m]/(k+1)`
for free — since costs are `ℕ`-valued, the strict form divides by
`k + 1` and needs no `k ≠ 0` hypothesis. The second-moment upgrade is
`Variance.lean` (`Var = E[g²] − E[g]²` and Chebyshev, with the
`ℝ≥0∞`-symmetric deviation `absSub`), and beyond the expectation the
running time has a *law*: `costPMF`. That third reading is what a
*determinism* claim needs — `schwartzZippel_costPMF` and
`costPMF_shuffle` say those algorithms cost `1` and `0` on **every**
run, which no expectation can express — and the coupon collector
studies the same tier from the other side, building a cost law
directly out of `geometric` stages composed by `bind`.

## Module dependency structure

Folders are thematic and the *folder* order is strictly layered —
`Randomness/` (what a random program means) below `Complexity/` (what
it costs) below `Correctness/` (what it outputs, incl. amplification);
the file DAG is acyclic, points strictly downward, and no Randomness
file imports a Complexity or Correctness file (the sampler *cost*
facts live]`, `prob` and the `ℙ[·]` notation without importing
any cost machinery, and the samplers (`RandVec`) sit at the same
cost-free level — their "the samplers are free" theorems are
cost-tier facts and live in `Complexity/SamplerCosts`.

## Known limitations

* `PMF` forces total mass 1: algorithms must terminate with
  probability 1, so genuine retry-until-success loops need fuel or,
  one day, sub-probability distributions.
* Continuous distributions would mean `MeasureTheory.Measure`,
  sigma-algebras and measurability side conditions everywhere — far
  future.
* Ticks are trusted, as discussed above.
