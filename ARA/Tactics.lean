import ARA.Basic

/-!
  Tactic infrastructure for PMF proofs.

  Organized in layers:
  - A: grind/simp tags to bridge PMF into arithmetic
  - B: pmf_simp macro and pmf_norm for computing probabilities
  - C: reusable derived lemmas
-/

namespace ARA

open ENNReal PMF


/-! ================================================================
    LAYER A: simp/grind tags
    ================================================================

  - @[simp] for monad laws (safe, always normalize in the right direction)
  - @[grind =] for domain-bridge lemmas (bind_apply, uniformOfFintype_apply, etc.)
    grind's e-matching picks these up when the goal already mentions the terms
  - @[grind →] for forward side conditions (ne_zero, ne_top)
-/

/-! ##### A.1  ENNReal Arithmetic -/

@[grind =]
lemma ennreal_natCast_inv_mul_self {n : ℕ} [NeZero n] :
    (n : ENNReal)⁻¹ * (n : ENNReal) = 1 :=
  ENNReal.inv_mul_cancel (by exact_mod_cast NeZero.ne n) (ENNReal.natCast_ne_top n)

@[grind =]
lemma ennreal_natCast_mul_inv_self {n : ℕ} [NeZero n] :
    (n : ENNReal) * (n : ENNReal)⁻¹ = 1 :=
  ENNReal.mul_inv_cancel (by exact_mod_cast NeZero.ne n) (ENNReal.natCast_ne_top n)

@[grind →]
lemma ennreal_natCast_inv_ne_zero {n : ℕ} [NeZero n] :
    (n : ENNReal)⁻¹ ≠ 0 :=
  ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n)

@[grind →]
lemma ennreal_natCast_inv_ne_top {n : ℕ} [NeZero n] :
    (n : ENNReal)⁻¹ ≠ ⊤ :=
  ENNReal.inv_ne_top.mpr (by exact_mod_cast NeZero.ne n)

attribute [grind =] ENNReal.div_add_div_same

-- summing n copies of n⁻¹ * t over Fin n gives t
lemma ennreal_inv_nsmul_cancel {n : ℕ} [NeZero n] (t : ENNReal) :
    ∑ _i : Fin n, (n : ENNReal)⁻¹ * t = t := by
  rw [Finset.sum_const]; simp [Fintype.card_fin]
  rw [← mul_assoc, ENNReal.mul_inv_cancel]
  · simp
  · exact_mod_cast NeZero.ne n
  · exact ENNReal.natCast_ne_top n


/-! ##### A.2  PMF Monad Laws (@[simp] — safe normalization) -/

attribute [simp] PMF.pure_bind    -- `pure a >>= f = f a`
attribute [simp] PMF.bind_pure    -- `p >>= pure = p`
attribute [simp] PMF.bind_const   -- `p >>= (fun _ => q) = q`
attribute [simp] PMF.bind_bind    -- `(p >>= f) >>= g = p >>= (fun a => f a >>= g)`
attribute [simp] PMF.pure_map     -- `f <$> pure a = pure (f a)`
attribute [simp] PMF.map_id       -- `id <$> p = p`

-- also register for grind (the two engines are independent)
attribute [grind =] PMF.pure_bind
attribute [grind =] PMF.bind_pure
attribute [grind =] PMF.bind_bind


/-! ##### A.3  PMF Pointwise Application & Distribution Weights (@[grind =]) -/

-- not safe as @[simp] (introducing tsum/ite can blow up), but fine for grind's e-matching
attribute [grind =] PMF.pure_apply
attribute [grind =] PMF.bind_apply
attribute [grind =] PMF.map_apply
attribute [grind =] PMF.uniformOfFintype_apply
attribute [grind =] PMF.uniformOfFinset_apply
attribute [grind =] PMF.bernoulli_apply
attribute [grind =] Fintype.card_fin
attribute [grind =] Fintype.card_bool

-- also register for grind
attribute [grind =] PMF.map_comp
attribute [grind =] PMF.bind_map
attribute [grind =] PMF.map_bind
attribute [grind =] PMF.bind_pure_comp


/-! ##### A.4  Support & bindOnSupport -/

attribute [grind =] PMF.support_uniformOfFintype
attribute [grind =] PMF.support_uniformOfFinset
attribute [grind =] PMF.support_pure
attribute [grind =] PMF.mem_support_iff
attribute [grind =] PMF.support_bind
attribute [grind =] PMF.mem_support_uniformOfFinset_iff
attribute [grind =] PMF.pure_bindOnSupport
attribute [grind =] PMF.bindOnSupport_apply


/-! ================================================================
    LAYER B: pmf_simp — concrete probability computation
    ================================================================

  Use pmf_simp to compute things like P(X = 3) = 1/12.
  It collapses tsum to finite sums, applies distribution weights, and cleans up arithmetic.
  For correctness proofs (showing output is a pure) use the lemmas in Layer C instead.
-/
macro "pmf_simp" : tactic =>
  `(tactic| (
    simp only [
      tsum_fintype,
      Fin.sum_univ_one, Fin.sum_univ_two, Fin.sum_univ_three,
      Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six,
      Fin.sum_univ_seven, Fin.sum_univ_eight,
      Fintype.sum_bool,
      tsum_ite_eq,
      PMF.tsum_coe,
      PMF.pure_bind, PMF.bind_pure, PMF.pure_apply,
      PMF.bind_apply, PMF.bind_const,
      PMF.pure_map, PMF.map_apply, PMF.map_id,
      PMF.bind_pure_comp,
      PMF.uniformOfFintype_apply, PMF.uniformOfFinset_apply,
      PMF.bernoulli_apply,
      PMF.bindOnSupport_eq_bind, PMF.pure_bindOnSupport,
      PMF.bindOnSupport_apply,
      Fintype.card_fin, Fintype.card_bool,
      ite_mul, mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq',
      mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add,
      ENNReal.inv_two_add_inv_two,
      if_true, if_false, ite_self, dite_true, dite_false,
      eq_self_iff_true, ne_eq,
      Finset.mem_univ, Finset.mem_singleton, Finset.mem_insert
    ]
    <;> try simp
    <;> try norm_num
    <;> try ring_nf))

/-- pmf_norm extends pmf_simp with omega for index bounds -/
macro "pmf_norm" : tactic =>
  `(tactic| (
    try pmf_simp
    <;> try omega
    <;> try (simp; ring_nf)
    <;> try norm_num))


/-! ================================================================
    LAYER C: Reusable Derived Lemmas
    ================================================================ -/

/-- uniformOfFintype (Fin 1) = pure 0, useful as a base case -/
lemma pmf_uniformOfFintype_fin_one :
    PMF.uniformOfFintype (Fin 1) = PMF.pure (0 : Fin 1) := by
  ext a
  have ha : a = 0 := Fin.ext (by omega)
  subst ha; simp [PMF.uniformOfFintype_apply]

/-- bind over a fintype PMF as a Finset.sum (helper for the next lemma) -/
lemma pmf_bind_apply_fintype {α β : Type*} [Fintype α] (p : PMF α)
    (f : α → PMF β) (b : β) :
    (p.bind f) b = ∑ a : α, p a * (f a) b := by
  rw [PMF.bind_apply, tsum_fintype]

/-- uniform bind over Fin n expressed as n⁻¹ * ∑ i, … -/
lemma pmf_uniform_fin_bind_apply {β : Type*} {n : ℕ} [NeZero n]
    (f : Fin n → PMF β) (b : β) :
    ((PMF.uniformOfFintype (Fin n)).bind f) b =
    (n : ENNReal)⁻¹ * ∑ i : Fin n, (f i) b := by
  rw [pmf_bind_apply_fintype]
  simp [PMF.uniformOfFintype_apply, Fintype.card_fin, Finset.mul_sum]

/-- when all branches of a uniform bind over Fin n give the same probability v,
    the result is v -/
lemma pmf_uniform_fin_bind_const_prob {β : Type*} {n : ℕ} [NeZero n]
    (f : Fin n → PMF β) (b : β) (v : ENNReal)
    (hv : ∀ i, (f i) b = v) :
    ((PMF.uniformOfFintype (Fin n)).bind f) b = v := by
  rw [pmf_uniform_fin_bind_apply]
  simp only [hv, Finset.mul_sum]
  exact ennreal_inv_nsmul_cancel v

end ARA
