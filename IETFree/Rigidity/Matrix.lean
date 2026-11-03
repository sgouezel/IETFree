/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.PairReach
public import IETFree.RauzyVeech.RauzyReach

/-!
# The positive block of the Rauzy matrix

This module proves the two lemmas on nonnegative integer matrices behind Veech's positive block:

* `colsum_le_of_one_le`: a positive right factor makes the column sums of a nonnegative integer
  matrix comparable, with the comparability constant given by the largest entry of the factor
  (Veech's (3.1)–(3.2));
* `exists_pos_cycle`: from every irreducible vertex of the Rauzy diagram there is a positive cycle
  whose entries are bounded by a constant depending on the vertex only — Veech's positive block.

The second proof composes the uniform positive word of `IETDatum₂.exists_uniform_bound'` with a
return word given by the strong connectivity of the Rauzy diagram
(`RauzyReach.exists_path_between`, which supplies both the return word and a uniform bound on its
length), and bounds the entries of the resulting cycle by a maximum over the finitely many words of
bounded length. No length vector enters the constant.
-/

@[expose] public section

open scoped BigOperators

namespace IETFree.Rigidity

/-- A positive right factor makes the column sums of a nonnegative integer matrix comparable. -/
theorem colsum_le_of_one_le {α : Type*} [Fintype α] (A B : Matrix α α ℤ) (M : ℤ)
    (hA : ∀ a c, 0 ≤ A a c) (h1 : ∀ a c, 1 ≤ B a c) (hM : ∀ a c, B a c ≤ M) :
    ∀ j j', ∑ a, (A * B) a j ≤ M * ∑ a, (A * B) a j' := by
  -- column sums of a product: `∑ a, (A * B) a j = ∑ i, (∑ a, A a i) * B i j`
  have key (j : α) : ∑ a, (A * B) a j = ∑ i, (∑ a, A a i) * B i j := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => by rw [Finset.sum_mul])
  by_cases hne : Nonempty α
  · obtain ⟨a₀⟩ := hne
    -- `1 ≤ M`, from `1 ≤ B a c ≤ M` at any entry
    have hM0 : 0 ≤ M := by
      have h : (1 : ℤ) ≤ M := le_trans (h1 a₀ a₀) (hM a₀ a₀)
      linarith
    intro j j'
    rw [key j, key j']
    have hstep (i : α) : (∑ a, A a i) * B i j ≤ M * ((∑ a, A a i) * B i j') := by
      have hS : 0 ≤ ∑ a, A a i := Finset.sum_nonneg (fun a _ => hA a i)
      have hMS : 0 ≤ M * (∑ a, A a i) := mul_nonneg hM0 hS
      calc (∑ a, A a i) * B i j
          ≤ (∑ a, A a i) * M := mul_le_mul_of_nonneg_left (hM i j) hS
        _ = M * (∑ a, A a i) := by ring
        _ = M * (∑ a, A a i) * 1 := by ring
        _ ≤ M * (∑ a, A a i) * B i j' := mul_le_mul_of_nonneg_left (h1 i j') hMS
        _ = M * ((∑ a, A a i) * B i j') := by ring
    calc ∑ i, (∑ a, A a i) * B i j
        ≤ ∑ i, M * ((∑ a, A a i) * B i j') := Finset.sum_le_sum (fun i _ => hstep i)
      _ = M * ∑ i, (∑ a, A a i) * B i j' := by rw [Finset.mul_sum]
  · -- nothing to prove when there are no letters
    have hempty : (Finset.univ : Finset α) = ∅ :=
      Finset.univ_eq_empty_iff.mpr (not_nonempty_iff.mp hne)
    intro j j'
    simp [hempty]

/-- The largest entry of `Path.Q Q (v ++ w)` in coordinates `a c`, over all words `w` of length at
most `L`. This is a maximum over a finite set depending on `Q`, `v` and `L` only. -/
private noncomputable def entryCap {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (Q : IETDatum₂ α n) (v : List Bool) (L : ℕ) (a c : α) : ℕ :=
  (Finset.univ : Finset (Σ k : Fin (L + 1), (Fin (k : ℕ) → Bool))).sup
    (fun p => (IETDatum₂.Path.Q Q (v ++ List.ofFn p.2) a c).toNat)

/-- The maximum of `entryCap Q v L` over the pairs of coordinates. -/
private noncomputable def cycleCap {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (Q : IETDatum₂ α n) (v : List Bool) (L : ℕ) : ℕ :=
  (Finset.univ : Finset (α × α)).sup (fun p => entryCap Q v L p.1 p.2)

/-- From every irreducible vertex there is a positive cycle, with bounded entries. -/
theorem exists_pos_cycle {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (Q : IETDatum₂ α n) (hQ : Q.Irreducible) (hn : 2 ≤ n) :
    ∃ (Bw : List Bool) (M : ℤ), 1 < M ∧ IETDatum₂.vertex Q Bw = Q ∧
      ∀ a c, 1 ≤ IETDatum₂.Path.Q Q Bw a c ∧ IETDatum₂.Path.Q Q Bw a c ≤ M := by
  classical
  -- a word from `Q` with all entries `≥ 1`
  obtain ⟨_, _, hposw⟩ := IETDatum₂.exists_uniform_bound' (α := α) (n := n) hn
  obtain ⟨v, hv⟩ := hposw Q hQ
  -- a bounded return word from the vertex reached by `v`
  obtain ⟨L, hL⟩ := RauzyReach.exists_path_between (α := α) (n := n) Q
  obtain ⟨ρ, hρL, hρ⟩ :=
    hL (IETDatum₂.vertex Q v) Q ⟨v, rfl⟩ (RauzyReach.reach_refl Q)
  refine ⟨v ++ ρ, ((cycleCap Q v L : ℕ) : ℤ) + 2, ?_, ?_, ?_⟩
  · -- the bound is at least `2`
    have h : (0 : ℤ) ≤ ((cycleCap Q v L : ℕ) : ℤ) := Int.natCast_nonneg _
    linarith
  · -- the word is a cycle at `Q`
    rw [IETDatum₂.vertex_append, hρ]
  · intro a c
    have hnn : 0 ≤ IETDatum₂.Path.Q Q (v ++ ρ) a c :=
      IETDatum₂.Path.Q_nonneg Q (v ++ ρ) a c
    refine ⟨?_, ?_⟩
    · -- positivity: `Q(v) * Q(ρ) ≥ 1` entrywise
      have hmul : IETDatum₂.Path.Q Q (v ++ ρ)
          = IETDatum₂.Path.Q Q v * IETDatum₂.Path.Q (IETDatum₂.vertex Q v) ρ :=
        IETDatum₂.Path.Q_append Q v ρ
      rw [hmul, Matrix.mul_apply]
      have hterm : ∀ i ∈ (Finset.univ : Finset α), 0 ≤ IETDatum₂.Path.Q Q v a i *
          IETDatum₂.Path.Q (IETDatum₂.vertex Q v) ρ i c :=
        fun i _ => mul_nonneg (IETDatum₂.Path.Q_nonneg Q v a i)
          (IETDatum₂.Path.Q_nonneg (IETDatum₂.vertex Q v) ρ i c)
      have h1 := Finset.single_le_sum hterm (Finset.mem_univ c)
      have h2 : (1 : ℤ) ≤ IETDatum₂.Path.Q Q v a c *
          IETDatum₂.Path.Q (IETDatum₂.vertex Q v) ρ c c := by
        have h := mul_le_mul (hv a c).1
          (IETDatum₂.Path.one_le_Q_diag (IETDatum₂.vertex Q v) ρ c)
          (by norm_num) (by linarith [(hv a c).1])
        simpa using h
      linarith
    · -- the bound: a maximum over the words of length `≤ L`
      have hstep1 : (IETDatum₂.Path.Q Q (v ++ ρ) a c).toNat ≤ entryCap Q v L a c := by
        have h := Finset.le_sup (s := (Finset.univ : Finset
            (Σ k : Fin (L + 1), (Fin (k : ℕ) → Bool))))
          (f := fun p => (IETDatum₂.Path.Q Q (v ++ List.ofFn p.2) a c).toNat)
          (b := ⟨⟨ρ.length, Nat.lt_succ_of_le hρL⟩, ρ.get⟩) (Finset.mem_univ _)
        rw [List.ofFn_get] at h
        exact h
      have hstep2 : entryCap Q v L a c ≤ cycleCap Q v L :=
        Finset.le_sup (s := (Finset.univ : Finset (α × α)))
          (f := fun p : α × α => entryCap Q v L p.1 p.2) (b := (a, c)) (Finset.mem_univ _)
      calc IETDatum₂.Path.Q Q (v ++ ρ) a c
          = (((IETDatum₂.Path.Q Q (v ++ ρ) a c).toNat : ℕ) : ℤ) :=
            (Int.toNat_of_nonneg hnn).symm
        _ ≤ ((cycleCap Q v L : ℕ) : ℤ) := by exact_mod_cast le_trans hstep1 hstep2
        _ ≤ ((cycleCap Q v L : ℕ) : ℤ) + 2 := by linarith

end IETFree.Rigidity

end
