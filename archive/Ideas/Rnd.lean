import ARA.Basic

/-!
# The `Rnd` Monad: Combining Probability and Cost

This module defines the `Rnd` monad, which pairs the probability space (`PMF`)
with a cost accumulator, enabling formal analysis of both the output distribution
and the running time distribution of randomized algorithms.

## Design

A randomized computation with cost tracking is a joint distribution over
(output, cost) pairs:

  Rnd T α ≅ PMF (α × T)

where T is the cost type (typically ℕ for counting operations).

This is equivalent to a WriterT T PMF monad transformer stack, where:
- PMF provides the probability backbone (Giry monad)
- WriterT T accumulates costs additively

## Relationship to TimeM

TimeM T α = (α × T) is cost tracking over the identity monad: one deterministic
(value, cost) pair. Rnd T α = PMF (α × T) is cost tracking over the PMF monad:
a distribution over (value, cost) pairs.

Both are instances of the same pattern: WriterT T M α = M (α × T), where
- M = Id   gives TimeM
- M = PMF  gives Rnd
- M = IO   would give executable cost tracking

A natural future direction: instead of defining Rnd from scratch, recognize that
cost tracking is a general concern (WriterT T M for any monad M) and generalize
TimeM accordingly. Whether we should literally use WriterT or keep a custom
structure (for better simp lemmas, notation, etc.) is an open question.

Rnd.fromTimeM embeds a deterministic TimeM computation (a, c) into Rnd as the
point-mass distribution PMF.pure (a, c).

### Monad Operations

- pure a: returns a with zero cost, probability 1.
  Formally: PMF.pure (a, 0)

- bind m f: the distribution that assigns to (e, c) : β × T the probability
  ∑ (a, c₁), m (a, c₁) * ∑ c₂ with c₁ + c₂ = c, (f a) (e, c₂)
  i.e. probabilities multiply (via PMF bind) and costs add.

### Extraction Functions

Given m : Rnd T α, we can extract:
- m.outputDist : PMF α  — marginalizes over costs
- m.costDist   : PMF T  — marginalizes over outputs
- m.run        : PMF (α × T) — the full joint distribution

### Primitives

- Rnd.coin p          : biased coin flip, zero cost
- Rnd.uniformFin n    : uniform choice over Fin n, zero cost
- Rnd.uniformFintype α: uniform choice over a finite type, zero cost
- Rnd.tick c          : charges cost c, returns PUnit
- Rnd.liftPMF p       : lift a PMF into Rnd with zero cost
-/

namespace ARA

open PMF ENNReal

/-! ## Core Definition -/

/-- `Rnd T α` represents a randomized computation that produces a value of type `α`
    and accumulates a cost of type `T`. It is implemented as `PMF (α × T)`:
    a probability distribution over `(output, cost)` pairs. -/
def Rnd (T : Type*) (α : Type*) := PMF (α × T)

namespace Rnd

variable {T : Type*} {α β γ : Type*}

/-! ## Monad Instance -/

/-- Lift a pure value into `Rnd` with zero cost. -/
noncomputable def pure' [Zero T] (a : α) : Rnd T α :=
  PMF.pure (a, 0)

/-- Sequentially compose two `Rnd` computations.
    Probabilities multiply (via PMF bind), costs add. -/
noncomputable def bind' [Add T] (m : Rnd T α) (f : α → Rnd T β) : Rnd T β :=
  m.bind (fun p => (f p.1).bind (fun q => PMF.pure (q.1, p.2 + q.2)))
/-
A concrete computation: for (e, c) : β × T we have
(bind' m f) (e, c) = (∑' (a, c_1), m (a, c_1) * (bind (f a) (fun q => PMF.pure (q.1, c_1 + q.2)))) (e, c)
= ∑' (a, c_1), m (a, c_1) * (∑' (b, c_2), (f a) (b, c_2) * (PMF.pure (b, c_1 + c_2)) (e, c))
= ∑' (a, c_1), m (a, c_1) * (∑' c_2, (if c_1 + c_2 = c then (f a) (e, c_2) else 0)

Typically if + is injective in the second argument on T, then we can rewrite the last line as
= ∑' (a, c_1), (if ∃ c_2, c_1 + c_2 = c then m (a, c_1) * (f a) (e, c_2) else 0)
-/

/-- Map a function over the output, preserving cost and probability. That is the probability
of getting (e, c) : β × T from `m.map' f` is the sum over all a : α satisfying f a = e
of the probability of getting (a, c) from `m`. -/
noncomputable def map' (f : α → β) (m : Rnd T α) : Rnd T β :=
  m.map (fun p => (f p.1, p.2))
/-
That is m.map' f = m.bind (fun p => PMF.pure (f p.1, p.2))
= ∑' (a, c), m (a, c) * (PMF.pure (f a, c)) which sends (b, d) : β × T to
∑' (a, c), m (a, c) * (if f a = b and c = d then 1 else 0)
= ∑' a, (if f a = b then m (a, d) else 0)
-/

noncomputable instance [Zero T] : Pure (Rnd T) where
  pure := Rnd.pure'

noncomputable instance [Add T] : Bind (Rnd T) where
  bind := Rnd.bind'

noncomputable instance : Functor (Rnd T) where
  map := Rnd.map'

/-! ## Primitive Operations -/

/-- Charge a cost of `c` units, returning `PUnit`. -/
noncomputable def tick [Zero T] (c : T) : Rnd T PUnit :=
  PMF.pure (PUnit.unit, c)
/-
This is used when we want to model a deterministic cost
without affecting the output distribution. For example,
if we have a step in our algorithm that always takes 5
units of time, we can represent it as `tick 5`, which
will contribute 5 to the total cost regardless of the output.
How is it binded to a function f : PUnit → Rnd T α ?
The following way : tick t.bind' f =
(tick.t).bind (fun q => (f PUnit.unit).bind (fun r => PMF.pure (r.1, q.2 + r.2)))
so sends (e, c) : α × T to
∑' (PUnit.unit, c_1), tick t (PUnit.unit, c_1) * (∑' c_2, (if c_1 + c_2 = c then (f PUnit.unit) (e, c_2) else 0))
= ∑' c_2, (if t + c_2 = c then (f PUnit.unit) (e, c_2) else 0))

Typically if + is injective in the second argument on T, then we can rewrite the last line as
= (if ∃ c_2, t + c_2 = c then (f PUnit.unit) (e, c_2) else 0)
-/

/-- A biased coin flip with probability `p` of `true`, zero cost. -/
noncomputable def coin [Zero T] (p : NNReal) (hp : p ≤ 1) : Rnd T Bool :=
  (PMF.bernoulli p hp).map (fun b => (b, (0 : T)))

/-- Uniform random choice over `Fin n`, zero cost. -/
noncomputable def uniformFin [Zero T] (n : ℕ) [NeZero n] : Rnd T (Fin n) :=
  (PMF.uniformOfFintype (Fin n)).map (fun i => (i, (0 : T)))

/-- Uniform random choice over a nonempty finite type, zero cost. -/
noncomputable def uniformFintype [Zero T] (α : Type*) [Fintype α] [Nonempty α] : Rnd T α :=
  (PMF.uniformOfFintype α).map (fun a => (a, (0 : T)))

/-- Uniform random choice over a nonempty finset, zero cost. -/
noncomputable def uniformFinset [Zero T] {α : Type*} (s : Finset α) (hs : s.Nonempty) : Rnd T α :=
  (PMF.uniformOfFinset s hs).map (fun a => (a, (0 : T)))

/-- Lift a PMF into `Rnd` with zero cost. -/
noncomputable def liftPMF [Zero T] (p : PMF α) : Rnd T α :=
  p.map (fun a => (a, (0 : T)))

/-- Embed a deterministic `TimeM`-style computation `(value, cost)` into `Rnd`
    as a point-mass distribution. -/
noncomputable def fromTimeM (ret : α) (time : T) : Rnd T α :=
  PMF.pure (ret, time)

/-! ## Extraction Functions -/

/-- Access the underlying `PMF (α × T)` joint distribution. -/
def run (m : Rnd T α) : PMF (α × T) := m

/-- Extract the **output distribution** by marginalizing over costs.
    `m.outputDist a = ∑' c, m.run (a, c)`
  That is the probability of getting a from m.outputDist is the sum
  over all cost c : T of the probability of getting (a, c) from m.run.
-/
noncomputable def outputDist (m : Rnd T α) : PMF α :=
  (m.run).map Prod.fst
/-
Indeed we compute that m.outputDist a = ((m.run).map Prod.fst) a
= (PMF.bind m.run (fun p => PMF.pure (Prod.fst p))) a
= (∑' (b, c), m.run (b, c) * (PMF.pure Prod.fst (b, c))) a
= ∑' (b, c), m.run (b, c) * (if b = a then 1 else 0)
= ∑' c, m.run (a, c)
-/

/-- Extract the **cost distribution** by marginalizing over outputs.
    `m.costDist c = ∑' a, m.run (a, c)`
  That is the probability of getting c from m.costDist is the sum
  over all output a : α of the probability of getting (a, c) from m.run.
-/
noncomputable def costDist (m : Rnd T α) : PMF T :=
  (m.run).map Prod.snd
/-
Indeed we compute that m.costDist c = ((m.run).map Prod.snd) c
= (PMF.bind m.run (fun p => PMF.pure (Prod.snd p))) c
= (∑' (a, d), m.run (a, d) * (PMF.pure Prod.snd (a, d))) c
= ∑' (a, d), m.run (a, d) * (if d = c then 1 else 0)
= ∑' a, m.run (a, c)
-/

/-- The probability of a specific `(output, cost)` pair. -/
noncomputable def prob (m : Rnd T α) (a : α) (c : T) : ℝ≥0∞ :=
  m.run (a, c)

/-- The probability of a specific output (marginalizing over all costs). -/
noncomputable def probOutput (m : Rnd T α) (a : α) : ℝ≥0∞ :=
  m.outputDist a

/-- The probability of a specific cost (marginalizing over all outputs). -/
noncomputable def probCost (m : Rnd T α) (c : T) : ℝ≥0∞ :=
  m.costDist c

/-! ## Simp Lemmas -/

@[simp]
lemma run_pure [Zero T] (a : α) : (pure a : Rnd T α).run = PMF.pure (a, 0) := rfl

-- run_bind unfolds by definition (rfl)

@[simp]
lemma outputDist_pure [Zero T] (a : α) : (pure a : Rnd T α).outputDist = PMF.pure a := by
  show (PMF.pure (a, (0 : T))).map Prod.fst = PMF.pure a
  simp [PMF.pure_map]

@[simp]
lemma costDist_pure [Zero T] (a : α) : (pure a : Rnd T α).costDist = PMF.pure (0 : T) := by
  show (PMF.pure (a, (0 : T))).map Prod.snd = PMF.pure (0 : T)
  simp [PMF.pure_map]

@[simp]
lemma outputDist_liftPMF [Zero T] (p : PMF α) : (liftPMF p : Rnd T α).outputDist = p := by
  show (p.map (fun a => (a, (0 : T)))).map Prod.fst = p
  rw [PMF.map_comp]
  convert PMF.map_id p

@[simp]
lemma costDist_tick [Zero T] (c : T) : (tick c : Rnd T PUnit).costDist = PMF.pure c := by
  show (PMF.pure (PUnit.unit, c)).map Prod.snd = PMF.pure c
  simp [PMF.pure_map]

/-! ## Example: Coin flip with cost -/

/-- A fair coin flip that costs 1 unit. -/
noncomputable def fairCoinWithCost : Rnd ℕ Bool := do
  tick 1
  coin (1/2 : NNReal) (by norm_num)

end Rnd

end ARA
