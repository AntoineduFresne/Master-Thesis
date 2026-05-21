import ARA.Basic

/-!
  ### Phase 1: Basic Probability Manipulation and familiarisation with PMF

  Here we go through the three main use cases of the PMF monad:
  1. Chaining (bind): a coin flip decides between different subsequent random processes.
  2. Deterministic Steps (pure): embedding a deterministic value into the PMF monad.
  3. Strict Safety (bindOnSupport): forcing the compiler to prove that unsafe operations
     (like out-of-bounds indexing) are never reachable.
-/

namespace ARA

open PMF

/--
  Use 1

  Example: flip a fair coin, heads -> roll d6, tails -> roll d20.
  bind (>>=) handles the probability mass multiplication automatically:
  - P(Heads) * P(d6=k) = 1/2 * 1/6
  - P(Tails) * P(d20=k) = 1/2 * 1/20

  First we model a simple coin flip as a Bernoulli trial with parameter p=1/2.
-/
noncomputable def coin_flip : PMF Bool := PMF.bernoulli (1/2 : NNReal) (by norm_num)

/--
  lemma: The probability of obtaining Heads (true) in a fair coin flip is exactly 1/2.
-/
lemma coin_flip_prob_heads : coin_flip true = 1/2 := by
  -- Unfold the definition of coin_flip and apply Bernoulli properties
  simp [coin_flip, PMF.bernoulli_apply]

noncomputable def d6 : PMF (Fin 6) := PMF.uniformOfFintype (Fin 6)
noncomputable def d20 : PMF (Fin 20) := PMF.uniformOfFintype (Fin 20)

/-
The probability mass function is obtained by two layers of bind operation:
  -- One for the coin flip: coin_flip >>= (λ outcome => if outcome then d6 else d20)
  -- One for the subsequent die roll based on the coin outcome:
    * d6 >>= (λ result => PMF ℕ.pure (result.val + 1)) for heads
      (we add 1 to the die result because result lives in Fin 6 which is {0,1,2,3,4,5})
    * d20 >>= (λ result => PMF ℕ.pure (result.val + 1)) for tails.
-/

noncomputable def algorithm1: Bool → PMF ℕ
| true => d6.bind (λ result => PMF.pure (result.val + 1))
| false => d20.bind (λ result => PMF.pure (result.val + 1))

noncomputable def mixed_dice_game : PMF ℕ := coin_flip.bind algorithm1

-- e.g. to "compute" the probability of rolling a 3:
theorem prob_rolling_3 : mixed_dice_game 3 = (1/2) * (1/6) + (1/2) * (1/20) := by
  rw [mixed_dice_game, PMF.bind_apply, coin_flip]
  simp [PMF.bernoulli_apply]
  -- We need to prove the values for the two branches

  have : algorithm1 true 3 = 1/6 := by
    unfold algorithm1 d6
    simp [PMF.bind_apply, PMF.uniformOfFintype_apply]
    rw [Finset.sum_eq_single (2 : Fin 6)]
    · simp
    · intro b _ hb
      simp
      intro h
      apply hb
      apply Fin.eq_of_val_eq
      simp_all
    · simp

  rw [this]

  have : algorithm1 false 3 = 1/20 := by
    unfold algorithm1 d20
    simp [PMF.bind_apply, PMF.uniformOfFintype_apply]
    rw [Finset.sum_eq_single (2 : Fin 20)]
    · simp
    · intro b _ hb
      simp
      intro h
      apply hb
      apply Fin.eq_of_val_eq
      simp_all
    · simp

  rw [this]

  simp_all

/--
  Use 2

  pure embeds a deterministic value into the PMF monad.
  Building on the previous example, we define a deterministic bonus that adds 100 to the die result.
-/
noncomputable def deterministic_bonus (score : ℕ) : PMF ℕ := PMF.pure (score + 100)

-- So that:
noncomputable def mixed_dice_game_with_bonus : PMF ℕ := mixed_dice_game.bind deterministic_bonus

-- The probability of rolling a k and then adding the bonus is the same as rolling a k:
theorem prob_rolling_k_with_bonus (k : ℕ) : mixed_dice_game_with_bonus (k + 100) = mixed_dice_game k := by
  rw [mixed_dice_game_with_bonus, PMF.bind_apply]
  simp [deterministic_bonus, PMF.pure_apply]
  simp_rw [@eq_comm _ k, tsum_ite_eq]


/--
  Use 3

  bindOnSupport is like bind but the continuation only needs to be defined on the support
  of the distribution (i.e. where P x ≠ 0). The extra argument h : P x ≠ 0 acts as a
  compile-time proof that x is actually reachable.

  This is useful when we want to do "unsafe" operations (like indexing into a list) and we
  want the compiler to force us to prove those operations are only called on valid inputs,
  instead of relying on default values or Option types.

  Example: a distribution supported on {0, 1} is used to index into a 2-element list.
  With bindOnSupport the compiler forces us to prove n < 2 before we can call the list accessor,
  so we never touch an out-of-bounds index.
-/

-- A distribution that only supports {0, 1}
noncomputable def safe_index_dist : PMF ℕ := PMF.uniformOfFinset {0, 1} (by simp)

-- A strict operation that cannot be called without a proof that n < 2 (our λ).
-- It safely extracts elements from a 2-element list and returns them as a
-- PMF String.
noncomputable def strict_list_access (n : ℕ) (h : n < 2) : PMF String :=
  let safe_idx : Fin (["Result A", "Result B"]).length := ⟨n, h⟩
  PMF.pure (["Result A", "Result B"].get safe_idx)

-- So our λ takes n : ℕ and a proof that n < 2, and returns a PMF String.

-- Using `bindOnSupport` to connect them.
-- The compiler forces us to prove that every element in the support of `safe_index_dist`
-- satisfies `n < 2`.
noncomputable def safe_chaining_example : PMF String :=
  safe_index_dist.bindOnSupport (λ n h_support =>
    have h_safe : n < 2 := by
      unfold safe_index_dist at h_support
      simp_all
      omega

    strict_list_access n h_safe
  )

lemma safe_chaining_example_resultA : safe_chaining_example "Result A" = 1/2 := by
  unfold safe_chaining_example safe_index_dist strict_list_access
  simp_all
  apply tsum_eq_single 0
  intro a ha; rcases a with _ | _ | a <;> simp_all

lemma safe_chaining_example_resultB : safe_chaining_example "Result B" = 1/2 := by
  unfold safe_chaining_example safe_index_dist strict_list_access
  simp_all
  apply tsum_eq_single 1
  · intro a ha
    rcases a with _ | _ | a
    · simp
    · contradiction
    · simp

end ARA
