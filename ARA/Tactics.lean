import ARA.SimpAttr

/-!
  Tactic infrastructure for PMF proofs.

  Organized in layers:
  - A: grind/simp tags to bridge PMF into arithmetic
  - B: pmf_simp macro and pmf_norm for computing probabilities
  - C: reusable derived lemmas

  ## Custom simp attribute

  We use a registered `@[pmf_simp_attr]` attribute (declared in
  `ARA.SimpAttr`). Downstream files can locally tag domain-specific
  lemmas with `@[pmf_simp_attr]` to extend the automation organically.
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


/-! ##### A.4  Do-notation Desugaring

  do-notation desugars `←` to `Bind.bind`, `return` to `Pure.pure`, and
  sometimes `←` to `Functor.map`.  These typeclass methods are
  definitionally equal to their concrete counterparts (e.g. `PMF.bind`),
  but `grind`/`simp` pattern-match syntactically and won't see through
  the typeclass layer.

  `unfold_do` resolves them via `dsimp` (definitional unfolding).
  Globally tagging them at `@[simp]` would be too aggressive.
-/
macro "unfold_do" : tactic => `(tactic| dsimp only [Bind.bind, Pure.pure, Functor.map])


/-! ##### A.5  Support & bindOnSupport -/

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
  It collapses tsum to finite sums, applies distribution weights,
  and cleans up arithmetic.

  The core simp set is the registered `pmf_simp_attr` attribute
  (declared in `ARA.SimpAttr`). Downstream files can extend it by
  tagging their lemmas with `@[pmf_simp_attr]`.
-/

-- Tag key lemmas with the custom attribute
attribute [pmf_simp_attr] tsum_fintype
attribute [pmf_simp_attr] Fin.sum_univ_one Fin.sum_univ_two Fin.sum_univ_three
attribute [pmf_simp_attr] Fin.sum_univ_four Fin.sum_univ_five Fin.sum_univ_six
attribute [pmf_simp_attr] Fin.sum_univ_seven Fin.sum_univ_eight
attribute [pmf_simp_attr] Fintype.sum_bool
attribute [pmf_simp_attr] tsum_ite_eq
attribute [pmf_simp_attr] PMF.tsum_coe
attribute [pmf_simp_attr] PMF.pure_bind PMF.bind_pure PMF.pure_apply
attribute [pmf_simp_attr] PMF.bind_apply PMF.bind_const
attribute [pmf_simp_attr] PMF.pure_map PMF.map_apply PMF.map_id
attribute [pmf_simp_attr] PMF.bind_pure_comp
attribute [pmf_simp_attr] PMF.uniformOfFintype_apply PMF.uniformOfFinset_apply
attribute [pmf_simp_attr] PMF.bernoulli_apply
attribute [pmf_simp_attr] PMF.bindOnSupport_eq_bind PMF.pure_bindOnSupport
attribute [pmf_simp_attr] PMF.bindOnSupport_apply
attribute [pmf_simp_attr] Fintype.card_fin Fintype.card_bool
attribute [pmf_simp_attr] ite_mul mul_ite
attribute [pmf_simp_attr] Finset.sum_ite_eq Finset.sum_ite_eq'
attribute [pmf_simp_attr] mul_one one_mul mul_zero zero_mul add_zero zero_add
attribute [pmf_simp_attr] ENNReal.inv_two_add_inv_two
attribute [pmf_simp_attr] if_true if_false ite_self dite_true dite_false
attribute [pmf_simp_attr] eq_self_iff_true ne_eq
attribute [pmf_simp_attr] Finset.mem_univ Finset.mem_singleton Finset.mem_insert

/-- `pmf_simp` normalizes PMF expressions by applying the `pmf_simp_attr`
simp set, then cleaning up with `norm_num`. -/
macro "pmf_simp" : tactic =>
  `(tactic| (simp only [pmf_simp_attr]; try norm_num))

/-- `pmf_norm` extends `pmf_simp` with `omega` for index bounds and
`ring_nf` for residual arithmetic. -/
macro "pmf_norm" : tactic =>
  `(tactic| first
    | pmf_simp
    | (simp only [pmf_simp_attr]; omega)
    | (simp only [pmf_simp_attr]; ring_nf; norm_num))


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
