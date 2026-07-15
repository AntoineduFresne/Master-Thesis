/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.ExpectedCost
import ARA.Correctness
import ARA.Algorithms.Partition
import Mathlib.Data.Nat.Log

/-!
# Treap / randomized binary search tree

A treap assigns each key a random priority and keeps a BST on keys /
heap on priorities; equivalently, the resulting tree is the BST
obtained by inserting the keys in a **uniformly random order**. We
model this directly via a random shuffle, keeping the randomness
explicit and the output distribution exact.

## Architecture

`randomBST` is polymorphic in the random monad `M`; it runs in `IO`
(executable), specifies a distribution in `PMF`, etc. It draws no
`MonadCost` ticks — for a data structure the analogue of runtime is a
*structural* measure (the tree height), read off the output.

## Main results

* `Correctness_Treap` — **every** tree the sampler can output is a
  valid BST over the (distinct) keys: its in-order traversal is sorted
  and a permutation of the keys. This holds for every random order, so
  the in-order traversal is deterministic even though the tree *shape*
  is random — the framework's distributional-support correctness.
* `randomBST_height_le` — a deterministic honest bound: the height
  never exceeds the number of keys.

The sharp result — that the *expected* height is `Θ(log n)` (Devroye
1986) — is a substantially harder analysis (it controls the whole
shape distribution, not just the support) and is left as future work.
-/

namespace ARA

open Cslib.Algorithms.Lean

/-! ## Binary search trees -/

/-- A binary tree with `ℕ` keys. -/
inductive Tree where
  | leaf : Tree
  | node : Tree → ℕ → Tree → Tree
deriving Repr

namespace Tree

/-- Standard (duplicate-dropping) BST insertion. -/
def insert : Tree → ℕ → Tree
  | leaf, k => node leaf k leaf
  | node l x r, k =>
      if k < x then node (insert l k) x r
      else if x < k then node l x (insert r k)
      else node l x r

/-- Height of the tree (a `leaf` has height `0`). -/
def height : Tree → ℕ
  | leaf => 0
  | node l _ r => 1 + max l.height r.height

/-- Number of nodes. -/
def size : Tree → ℕ
  | leaf => 0
  | node l _ r => 1 + l.size + r.size

/-- In-order traversal (the sorted key sequence of a BST). -/
def inorder : Tree → List ℕ
  | leaf => []
  | node l x r => l.inorder ++ x :: r.inorder

/-- Membership in a tree, via its in-order traversal. -/
@[simp] lemma mem_inorder_leaf (a : ℕ) : a ∈ leaf.inorder ↔ False := by
  simp [inorder]

/-- Insertion adds exactly the new key to the element set. -/
lemma mem_inorder_insert (t : Tree) (k a : ℕ) :
    a ∈ (t.insert k).inorder ↔ a = k ∨ a ∈ t.inorder := by
  induction t with
  | leaf => simp [insert, inorder]
  | node l x r ihl ihr =>
    rw [insert]
    split_ifs with h1 h2
    · simp only [inorder, List.mem_append, List.mem_cons, ihl]
      tauto
    · simp only [inorder, List.mem_append, List.mem_cons, ihr]
      tauto
    · -- `k = x`, already present.
      have hkx : k = x := by omega
      simp only [inorder, List.mem_append, List.mem_cons]
      rw [hkx]; tauto

/-- Insertion preserves in-order sortedness (the BST invariant). -/
lemma sorted_inorder_insert (t : Tree) (k : ℕ)
    (hs : t.inorder.Pairwise (· < ·)) :
    (t.insert k).inorder.Pairwise (· < ·) := by
  induction t with
  | leaf => simp [insert, inorder]
  | node l x r ihl ihr =>
    rw [inorder, List.pairwise_append] at hs
    obtain ⟨hsl, hsxr, hlt⟩ := hs
    rw [List.pairwise_cons] at hsxr
    obtain ⟨hxr, hsr⟩ := hsxr
    have hlx : ∀ a ∈ l.inorder, a < x := fun a ha => hlt a ha x (by simp)
    rw [insert]
    split_ifs with h1 h2
    · -- `k < x`: recurse left; new left block still all `< x`.
      rw [inorder, List.pairwise_append]
      refine ⟨ihl hsl, List.pairwise_cons.mpr ⟨hxr, hsr⟩, fun a ha b hb => ?_⟩
      rw [mem_inorder_insert] at ha
      rcases List.mem_cons.mp hb with rfl | hb'
      · rcases ha with rfl | ha'
        · exact h1
        · exact hlx a ha'
      · rcases ha with rfl | ha'
        · exact lt_trans h1 (hxr b hb')
        · exact lt_trans (hlx a ha') (hxr b hb')
    · -- `x < k`: recurse right; new right block still all `> x`.
      rw [inorder, List.pairwise_append]
      refine ⟨hsl, ?_, fun a ha b hb => ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨fun b hb => ?_, ihr hsr⟩
        rw [mem_inorder_insert] at hb
        rcases hb with rfl | hb'
        · exact h2
        · exact hxr b hb'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact hlx a ha
        · rw [mem_inorder_insert] at hb'
          rcases hb' with rfl | hb''
          · exact lt_trans (hlx a ha) h2
          · exact lt_trans (hlx a ha) (hxr b hb'')
    · -- `k = x`: unchanged.
      rw [inorder, List.pairwise_append]
      exact ⟨hsl, List.pairwise_cons.mpr ⟨hxr, hsr⟩, hlt⟩

/-- Folding insertion over a list: element set is exactly the list. -/
lemma mem_inorder_foldl (L : List ℕ) (t : Tree) (a : ℕ) :
    a ∈ (L.foldl Tree.insert t).inorder ↔ a ∈ L ∨ a ∈ t.inorder := by
  induction L generalizing t with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, mem_inorder_insert]
    simp only [List.mem_cons]
    tauto

/-- Folding insertion keeps the in-order traversal sorted. -/
lemma sorted_inorder_foldl (L : List ℕ) (t : Tree)
    (hs : t.inorder.Pairwise (· < ·)) :
    (L.foldl Tree.insert t).inorder.Pairwise (· < ·) := by
  induction L generalizing t with
  | nil => simpa using hs
  | cons x xs ih =>
    rw [List.foldl_cons]
    exact ih _ (sorted_inorder_insert t x hs)

/-- Height is bounded by the number of nodes. -/
lemma height_le_size (t : Tree) : t.height ≤ t.size := by
  induction t with
  | leaf => simp [height, size]
  | node l x r ihl ihr =>
    simp only [height, size]
    omega

/-- Insertion adds at most one node. -/
lemma size_insert_le (t : Tree) (k : ℕ) : (t.insert k).size ≤ t.size + 1 := by
  induction t with
  | leaf => simp [insert, size]
  | node l x r ihl ihr =>
    rw [insert]
    split_ifs <;> simp only [size] <;> omega

/-- Folding insertion over `L` yields at most `|L|` nodes. -/
lemma size_foldl_le (L : List ℕ) (t : Tree) :
    (L.foldl Tree.insert t).size ≤ t.size + L.length := by
  induction L generalizing t with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, List.length_cons]
    exact le_trans (ih (t.insert x)) (by have := size_insert_le t x; omega)

end Tree

/-! ## Algorithm -/

/-- Uniformly random shuffle of a list, by repeatedly removing a
uniformly random remaining element (`fuel` bounds the removals). -/
def shuffle {M} [Monad M] [RandMonad M] : ℕ → List ℕ → M (List ℕ)
  | 0, _ => return []
  | fuel + 1, L =>
      if h : 0 < L.length then do
        let i ← randIdx L h
        let rest ← shuffle fuel (L.eraseIdx i.1)
        return L[i] :: rest
      else
        return []

/-- Build a randomized BST by inserting the keys in a uniformly random
order. -/
def randomBST {M} [Monad M] [RandMonad M] (keys : List ℕ) : M Tree := do
  let perm ← shuffle keys.length keys
  return perm.foldl Tree.insert Tree.leaf

-- ----------------------------------------
-- Different instances of "randomness"
-- ----------------------------------------

def randomBST_IO : List ℕ → IO Tree := randomBST

#eval do IO.println s!"{repr (← randomBST_IO [3, 1, 4, 1, 5, 9, 2, 6])}"

noncomputable def randomBST_PMF : List ℕ → PMF Tree := randomBST

-- ----------------------------------------
-- Generic Correctness proof
-- ----------------------------------------

/-!
## Correctness: every output is a valid BST

The shuffle only ever produces permutations of the input, and folding
BST-insertion over a permutation of distinct keys always yields a tree
whose in-order traversal is the sorted key list — so the traversal is
deterministic even as the shape varies.
-/

/-- A strictly-increasing list has no duplicates. -/
private lemma pairwise_lt_nodup {l : List ℕ} (h : l.Pairwise (· < ·)) :
    l.Nodup :=
  h.imp (fun hab => ne_of_lt hab)

/-- The shuffle outputs only permutations of its input. -/
lemma shuffle_perm {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] :
    ∀ (fuel : ℕ) (L : List ℕ), L.length ≤ fuel →
      ∀ t ∈ (inst.toPMF (shuffle fuel L)).support, t.Perm L := by
  intro fuel
  induction fuel with
  | zero =>
    intro L hL t ht
    rw [show L = [] from List.eq_nil_of_length_eq_zero (by omega)]
    rw [show L = [] from List.eq_nil_of_length_eq_zero (by omega)] at ht
    rw [shuffle, inst.toPMF_pure, pmf_pure_eq, PMF.support_pure,
      Set.mem_singleton_iff] at ht
    rw [ht]
  | succ fuel ih =>
    intro L hL t ht
    rw [shuffle] at ht
    by_cases h : 0 < L.length
    · rw [dif_pos h, inst.toPMF_bind, inst.toPMF_randIdx] at ht
      rw [pmf_bind_eq, PMF.mem_support_bind_iff] at ht
      obtain ⟨i, _, ht'⟩ := ht
      rw [inst.toPMF_bind, pmf_bind_eq, PMF.mem_support_bind_iff] at ht'
      obtain ⟨rest, hrest, ht''⟩ := ht'
      rw [inst.toPMF_pure, pmf_pure_eq, PMF.support_pure,
        Set.mem_singleton_iff] at ht''
      -- `t = L[i] :: rest`, `rest ~ L.eraseIdx i`.
      have hlen : (L.eraseIdx i.1).length ≤ fuel := by
        have hi : (i : ℕ) < L.length := i.isLt
        rw [List.length_eraseIdx]
        split <;> omega
      have hp := ih (L.eraseIdx i.1) hlen rest hrest
      rw [ht'']
      exact (hp.cons L[i]).trans (perm_getElem_cons_eraseIdx L i).symm
    · rw [dif_neg h, inst.toPMF_pure, pmf_pure_eq, PMF.support_pure,
        Set.mem_singleton_iff] at ht
      rw [ht, show L = [] from List.eq_nil_of_length_eq_zero (by omega)]

/-- **Correctness.** For any `LawfulRandMonad`, every tree the sampler
can produce from distinct `keys` is a valid BST over them: its in-order
traversal is sorted and a permutation of `keys`. -/
theorem Correctness_Treap
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (keys : List ℕ) (hnd : keys.Nodup) (t : Tree)
    (ht : t ∈ (inst.toPMF (randomBST keys)).support) :
    t.inorder.Pairwise (· < ·) ∧ t.inorder.Perm keys := by
  rw [randomBST, inst.toPMF_bind, pmf_bind_eq, PMF.mem_support_bind_iff] at ht
  obtain ⟨perm, hperm, ht'⟩ := ht
  rw [inst.toPMF_pure, pmf_pure_eq, PMF.support_pure, Set.mem_singleton_iff] at ht'
  -- `t = perm.foldl insert leaf` and `perm ~ keys`.
  have hp : perm.Perm keys := shuffle_perm keys.length keys le_rfl perm hperm
  subst ht'
  have hsorted : (perm.foldl Tree.insert Tree.leaf).inorder.Pairwise (· < ·) :=
    Tree.sorted_inorder_foldl perm Tree.leaf (by simp [Tree.inorder])
  refine ⟨hsorted, ?_⟩
  -- Same element set as `perm` (nodup on both sides), hence a permutation.
  refine List.Perm.trans ?_ hp
  refine (List.perm_ext_iff_of_nodup (pairwise_lt_nodup hsorted)
    (hp.nodup_iff.mpr hnd)).mpr fun a => ?_
  rw [Tree.mem_inorder_foldl]
  simp [Tree.inorder]

/-- Correctness at `M = PMF` (where `toPMF` is the identity). -/
theorem randomBST_isBST (keys : List ℕ) (hnd : keys.Nodup) (t : Tree)
    (ht : (randomBST keys : PMF Tree) t ≠ 0) :
    t.inorder.Pairwise (· < ·) ∧ t.inorder.Perm keys :=
  Correctness_Treap (M := PMF) keys hnd t ht

-- ----------------------------------------
-- Structural bound: height
-- ----------------------------------------

/-!
## Height

A deterministic, honest bound: the height never exceeds the number of
keys (a treap on `n` keys has at most `n` nodes, and height ≤ nodes).
The sharp `Θ(log n)` *expected* height is future work — see the module
header.
-/

/-- **Deterministic height bound.** Every tree the sampler can output
has height at most `keys.length`. -/
theorem randomBST_height_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (keys : List ℕ) (t : Tree)
    (ht : t ∈ (inst.toPMF (randomBST keys)).support) :
    t.height ≤ keys.length := by
  rw [randomBST, inst.toPMF_bind, pmf_bind_eq, PMF.mem_support_bind_iff] at ht
  obtain ⟨perm, hperm, ht'⟩ := ht
  rw [inst.toPMF_pure, pmf_pure_eq, PMF.support_pure, Set.mem_singleton_iff] at ht'
  have hp : perm.Perm keys := shuffle_perm keys.length keys le_rfl perm hperm
  subst ht'
  calc (perm.foldl Tree.insert Tree.leaf).height
      ≤ (perm.foldl Tree.insert Tree.leaf).size := Tree.height_le_size _
    _ ≤ Tree.leaf.size + perm.length := Tree.size_foldl_le perm Tree.leaf
    _ = perm.length := by simp [Tree.size]
    _ = keys.length := hp.length_eq

end ARA
