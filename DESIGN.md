# ARA — Design notes

## Why the framework looks the way it does.

Formal reasoning about randomized algorithms spans a spectrum:

* Deep embeddings: programs are syntax trees in an embedded
  probabilistic language; running time can be extracted by
  construction, but every algorithm and every proof fights the
  obvious (?) complexity of such an embedding;

* no embedding / shallow: algorithms are ordinary functions of
  the logic returning probability distributions; maximally expressive,
  but nothing connects (automatically) the code to a cost model;

* hybrids: the algorithm exists twice, as a syntax tree in a small
  embedded probabilistic language and as a distribution defined in the
  logic, with an adequacy theorem tying the two together. The deep side
  carries an operational semantics, so cost is read off the syntax by
  construction; the shallow side keeps the mathematics tractable. The
  price is that every construct must be given twice and the bridge theorem
  maintained, so the embedded language stays small and the full
  expressiveness of the logic is available only on one side of the bridge.

ARA is a shallow to let's say no-embedding framework: an algorithm is an
ordinary Lean function written in what is hopefully a "standard" `do`-notation,
and its randomness is abstracted by a typeclass.

From there, we get the full expressiveness of Lean (recursion, dependent
types, Mathlib and other libraries...) but pay one price: the fact that
the cost annotations are trusted. A cost annotation is a call to `tick`,
the single operation of the `MonadCost C M` class: `MonadCost.tick c`, where `c : C`
is a value of the cost type. It is a statement inside the algorithm's `do`-block
that charges `c` units of cost at that point. The class
itself demands nothing of `C`, but the timed reading does, and
exactly what one expects: `0` to give `pure` no cost, `+` to add times through
`bind`, and the monoid laws for those to be lawful. Everything here uses `C = ℕ`.

It has two readings, chosen by the monad `M` the algorithm is instantiated at.

- At the default instance `tick` is `pure ()` and the annotation disappears;

- at `TimeMT ℕ M`, a transformer whose values carry a `(result : α, time : ℕ)` pair,
`tick c` adds `c` to the accumulated time and `bind` adds the times of its two halves.

The same text is therefore both the untimed program and the cost model. What is trusted
is the placement of such ticks. Nothing checks that a `tick n` corresponds to the work the
surrounding Lean code actually does: writing `tick 0` in Quicksort's partition step would
let the framework prove that Quicksort is free, and the theorem would be true of the cost
model as written. A reader must thus trust the Lean kernel and audit where the ticks sit:
connect the semantics of the computation to the ticks that have been placed in the
text of the algorithm. Literally, if someone "proves the complexity of a certain algorithm"
and ships you the code, not only will you have to trust (as always) the Lean kernel, but
also the way the ticks have been placed in it.

Notes:

- This is the same trade-off cslib makes with `TimeM`, whose values are pairs ⟨ret, time⟩
  accumulated by `bind` and whose `tick` is equally an annotation rather than a consequence
  of a semantics. `TimeMT` is that object turned into a transformer, threading the same
  accumulation through an arbitrary base monad; that is what lets cost and randomness
  coexist in `TimeMT ℕ PMF`. We build on their file, so we inherit their design and their
  trust assumption.

- A formal correspondence between ticks and code structure is possible future work, but
  the pragmatic gain here comes surely from not paying the deep-embedding tax: that is
  here we formalised roughly 10 easy-to-complex probabilistic algorithms and much more can
  be done using AI-tools that will surely one-shot or two-shot them (roughly).

- Such a broader picture is already being tackled. Loom (Verified Systems Engineering Lab,
  January 2026) is a Lean 4 framework for building foundational multi-modal program verifiers,
  based on a monadic shallow embedding of an executable program semantics
  with weakest-precondition generation via monad-transformer algebras; because the
  verifier is itself formalised in Lean it need not be trusted, and Velvet
  (imperative) and Veil (distributed protocols) are instances of it. Lean-native foundational C
  verification (LeanCP) points the same way, and cslib's Boole pillar lists a time-complexity
  back end among its wanted contributions. This matters to us directly: once the semantics of a
  program is formalised and executable, a cost model attached to that semantics is checked
  rather than trusted.

## Probability in the logic: `PMF` and the Giry monad

A distribution over a type `α` is a `PMF α`: a function `α → ℝ≥0∞` whose
values sum to `1` (Mathlib). Any such function induces a probability
measure (`PMF.toOuterMeasure`, `PMF.toMeasure`) where singletons are measurable,
and conversely, on a countable type, a probability measure with measurable singletons
induces a `PMF`; the two views are inverse to each other. What makes `PMF` a
_programming_ object is its monad structure, which follows the so-called discrete
Giry monad:

- `pure : α → PMF α` which takes a value and returns the distribution that is
  concentrated on that exact value (the Dirac distribution), i.e. assigns 1 to that
  value and 0 to all other values.

- `bind : PMF α → (α → PMF β) → PMF β` which for two types α and β:
  Takes (P, f) where:
  * P is a distribution over α, P : PMF α,
  * f is a function that assigns to each element of α a distribution over β, f : α → PMF β
  Returns:
  the distribution over β obtained by "sampling" from the first distribution and
  then "sampling" from the second distribution. That is, the probability of obtaining b in β from (bind P f) is the sum over all e in α of the probability of obtaining e from P times the probability of obtaining b from f e, i.e. assigns b : β to the probability:
  ∑ e : α, P e * (f e) b

  It is used concretely like this:
  * we write `pure x` for `PMF.pure x`;
  * `P >>= f` for `bind P f` (which can also be written `P.bind f`)

The main advantage of having probability distributions in the logic is its
expressiveness and flexibility: we can state that an algorithm's output is
a given distribution (not merely that some property holds almost surely),
compare two differently-structured algorithms by proving their output or cost
distributions equal, and reuse all of Mathlib's `tsum`/`ENNReal`
machinery in the proofs.

## One definition, multiple readings (here four)

An algorithm is written once and is polymorphic over
`{M} [Monad M] [RandMonad M] [MonadCost ℕ M]`:

* `RandMonad` supplies one primitive, uniform `randFin n` (every
  finite choice factors through it);

* `MonadCost` supplies `tick`, which by default is a no-op: the default
  instance defines `tick _ := pure ()`, returning the trivial value and
  doing nothing; at `TimeMT` the same call accumulates the cost;

The first two bullets are the programming interface, what an algorithm may call.
The third is the semantic layer, used only by proofs:

* `LawfulRandMonad` extends `RandMonad` with an interpretation `toPMF : M α → PMF α`
  and the equations making it a monad morphism: `toPMF (pure a)` is the Dirac at `a`,
  `toPMF (x >>= f)` is the corresponding `bind`, and `toPMF (randFin n)` is uniform on
  `Fin n`. `PMF` and `TimeMT ℕ PMF` are lawful; `IO` deliberately is not. Proofs are
  stated against `toPMF`, so they hold for every lawful instance at once. (In Lean a class
  provides operations and its `Lawful` companion provides the equations they must satisfy,
  `Monad`/`LawfulMonad` being the archetype. The split is deliberate: a type may implement
  the operations without the equations being provable, which is the case for `IO`; when
  they are provable, lawfulness is what lets a proof use them.)

Instantiating different `M` yields: `M=IO` (run it), `M=PMF` (the specification),
`M = TimeMT ℕ IO` (benchmark), and `M = TimeMT ℕ PMF` the joint distribution over
`(output, cost)` pairs, which is where all expected cost analysis happens. `TimeMT`
is a writer-style transformer: `TimeMT C M α` wraps `M (TimeM C α)` where `TimeM C α`
is the pair `⟨ret, time⟩`; `pure a` costs `0` and `bind` adds the times of its two halves.
Being a transformer, parameterised by an arbitrary base monad, is what makes the readings
compose: over `PMF` it yields `PMF (TimeM ℕ α)`, a distribution over `(output, cost)`
pairs and precisely the joint law an expected-cost analysis needs, while over `IO` it yields
an executable benchmark.

## Correctness comes in tiers

Practice of algorithm formalisation produced a classification of the different forms of "correctness" one talks about when speaking about correctness of algorithms. We built the API around this classification:

1. Dirac (Las Vegas): the output distribution is a point mass at the specification,
  an ordinary deterministic Lean function written independently of the algorithm that
  computes the intended answer (`L.mergeSort (· ≤ ·)` for Quicksort, `orderStat L k` for
  Quickselect). For example, the statement `𝒟_{M}[Quicksort L] = PMF.pure (L.mergeSort (· ≤ ·))`
  says the randomness changes the running time but never the answer, or more simply that the
  distribution is a Dirac at a certain deterministic answer that satisfies the specification.

  We tried to automate such correctness proofs:
   `toPMF_randIdx_bind_dirac` + `dirac_finish`; but a new user must supply the @[spec_transport] lemmas,
   which carry the actual mathematics of the algorithm. `dirac_correct` inducts along the algorithm, and in each branch the induction hypothesis has already replaced every recursive call by its specification; what remains is a deterministic equation between the branch and the global spec: for example in Quicksort, `sort (filter (< p) rest) ++ p :: sort (filter (≥ p) rest) = sort L`, that is, sorting both sides of a partition and concatenating gives the sorted list. Nothing probabilistic survives at that point, and no tactic can invent such a fact: it is the reason the algorithm is correct. Tagging it @[spec_transport] adds it to the simp set that `dirac_finish` uses to discharge the branch; by convention it is stated ℕ-indexed, oriented branch = spec so that `simp` matches the goal, with hypotheses shaped like the branch guards.

2. Exact distribution: the output law itself is the theorem, for example the
   reservoir sampling's uniformity.

3. Support + probability (Monte Carlo): two separate claims about an algorithm that is allowed to be wrong.
  The support of a distribution is the set of values it can actually return, `{a | p a ≠ 0}`, so a statement
  about the support holds on every run with no probability attached. This is where one-sided error is
  expressed: every output of Karger is a genuine cut whose reported value never undershoots the true minimum, so the algorithm can only err by reporting too large a value. Freivalds has the same shape, always answering "equal" on equal matrices.

  The second claim attaches a probability to being exactly right: Karger reports the true minimum with probability at least `2/(n(n−1))`, Freivalds errs with probability at most `1/2`. Together they are what makes repetition work: because the error is one-sided, running `k` times and keeping the best answer is sound, and the failure probability falls to `(1−p)^k` (`Correctness/Amplify`).

  The treap algorithm sits in this tier from another angle. It is never wrong: every output is a valid binary search tree, which is a support claim holding on every run, so there is no success probability to state. What the randomness affects is the shape of the output, and the theorem is therefore an expectation rather than a probability: `𝔼[height] ≤ 3·log₂(n+3) + 4`. This uses `expVal`, the expectation of a function of the output (same machinery as expected cost), applied to a measure of the result instead of the running time.

Costs follow the same layering. Upper bounds are stated in `ℝ≥0∞`, the extended non-negative reals `[0, ∞]`, because every sum of non-negative terms converges there, possibly to `∞`, so no series needs a convergence proof before it can be manipulated. Exact closed forms are more natural in `ℝ`, and `toReal` moves a value there; since `toReal` sends `∞` to `0`, it may only be used once the value is known to be finite, and that finiteness comes from first proving a crude bound such as Quicksort's `≤ C(n,2)`.

On top of expectations sits the tail-bound tier (`TailBounds.lean`). Markov's inequality turns any expected-cost theorem into a tail bound for free: `ℙ_{M}[cost m > k] ≤ 𝔼_{M}[cost m]/(k+1)`. Because costs are ℕ-valued, cost `> k` is the same event as cost `≥ k+1`, so the strict form divides by `k+1` (so is free of any `k ≠ 0` side condition).

A cost analysis admits three readings of increasing strength, and the framework supplies all three from the same tick-annotated definition.
- The expectation `𝔼_{M}[cost m]`
- Tail bound `ℙ_{M}[cost m > k]`
- Cost law `costPMF m` is the whole distribution of the running time. For example `costPMF m = PMF.pure c` says
  the algorithm costs exactly `c` on every run.

## Module dependency structure

The import graph, whose nodes are files and whose edges point from a file to each file it imports:
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
                Infrastructure may consume Helpers)
Algorithms/*  ← Infrastructure + Helpers + fine-grained Mathlib extras.
```

`Prob.lean` is the lowest probability layer: a
pure-distribution study (`Geometric`, `CouponCollector`) uses
`expVal`, `𝔼[·]`, `prob` and the `ℙ[·]` notation without importing
any cost machinery, and the samplers (`RandVec`) sit at the same
cost-free level — their "the samplers are free" theorems are
cost-tier facts and live in `Complexity/SamplerCosts`.

## Known limitations

* `PMF` forces total mass 1, so a genuine retry-until-success loop is not a
  `PMF` program. `Randomness/SPMF.lean` addresses this: `SPMF := OptionT PMF`
  carries the divergence probability on `none`, and `retry` is conditioning
  rather than domain theory (`mass_retry_eq_one` is the Las Vegas theorem).
  What remains is the cost reading over `SPMF` and the program-level coupon
  collector.

* Continuous distributions would mean `MeasureTheory.Measure`,
  sigma-algebras and measurability side conditions everywhere: far
  future.

* `tick` calls must be trusted: they state the cost model and nothing checks
  that they match an operational semantics.
