/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.Nesting
public import IETFree.RauzyVeech.PairReach

/-!
# An extreme vertex, runs of `true` steps, and the big cell

This module proves the two combinatorial facts about vertices of the Rauzy diagram that the positive
block of the rigid step rests on.

* `exists_vertex_last_true_eq_piBottom_zero` — the **extreme vertex**: from every irreducible
  datum some reachable vertex has a letter `b` that is last in the top order and first in the
  bottom order (so `piBottom b = 0`);
* `IETDatum₂.Path.Q_replicate_true` — at an extreme vertex, a run of `K` steps of type `true`
  multiplies the Rauzy matrix by a rank-one perturbation of the identity: `Q(true^K) = 1 + E_{b,v}`
  with `v b = 0`, and every other letter is `last false` at least `K / (card α - 1)` times along
  the run;
* `bigCell_of_mem_cone` — consequently, at the *beginning* of the run the letter `b` occupies at
  least `1 - δ` of the base, for every vector at the end of the run, as soon as
  `(1 - δ)/δ ≤ K / (card α - 1)`.

The key combinatorial input is the rotation of the bottom order along a run of `true` steps: at an
extreme vertex the pivot is `0`, so one `true` step fixes the bottom position `0` and rotates the
remaining `n - 1` positions by one, whence the letters in the last bottom position cycle through
all the letters other than `b`, one per step.
-/

@[expose] public section

open scoped BigOperators
open IntervalExchange.RauzyVeech

namespace IntervalExchange.Rigidity

/-- **An extreme vertex is reachable**: a letter that is last in the top order and first in the
bottom order. -/
theorem exists_vertex_last_true_eq_piBottom_zero {α : Type*} [Fintype α]
    {n : ℕ} [NeZero n] (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∃ (Q : IETDatum₂ α n) (w : List Bool),
      IETDatum₂.vertex P w = Q ∧ Q.last true = Q.piBottom.symm 0 := by
  obtain ⟨w, hw⟩ := IETDatum₂.exists_last_true_first P hP hn
  exact ⟨IETDatum₂.vertex P w, w, rfl,
    by rw [IETDatum₂.piBottom_zero_letter P w]; exact hw⟩

end IntervalExchange.Rigidity

namespace IntervalExchange

namespace IETDatum₂.Path

/-! ## The matrix `1 + E_{b,v}` and its multiplicative structure -/

/-- The matrix whose row `b` is the vector `v` (read in `ℤ`) and whose other rows vanish. -/
def Emat {α : Type*} [DecidableEq α] (b : α) (v : α → ℕ) :
    Matrix α α ℤ :=
  Matrix.of (fun a c => if a = b then (v c : ℤ) else 0)

lemma Emat_add {α : Type*} [DecidableEq α] (b : α) (v w : α → ℕ) :
    Emat b v + Emat b w = Emat b (fun c => v c + w c) := by
  ext a c
  simp only [Emat, Matrix.add_apply, Matrix.of_apply]
  by_cases h : a = b <;> simp [h]

lemma Emat_mul {α : Type*} [Fintype α] [DecidableEq α] (b : α) (v w : α → ℕ) :
    Emat b v * Emat b w = Emat b (fun c => v b * w c) := by
  ext a c
  rw [Matrix.mul_apply]
  simp only [Emat, Matrix.of_apply]
  rw [Finset.sum_eq_single b (fun m _ hm => by simp [hm])
    (fun h => absurd (Finset.mem_univ b) h)]
  by_cases h : a = b <;> simp [h]

/-- The elementary matrix of a `true` step is `1 + E_{last true, last false}`. -/
private lemma rvMat_true_eq {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (hne : P.last true ≠ P.last false) :
    P.rvMat true = 1 + Emat (P.last true) (fun c => if P.last false = c then 1 else 0) := by
  ext a c
  simp only [IETDatum₂.rvMat, Emat, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
  by_cases hac : a = c
  · subst hac
    rw [ite_eq_left rfl, ite_eq_left rfl]
    by_cases hb : a = P.last true
    · rw [ite_eq_left hb, ite_eq_right (fun h => hne (hb.symm.trans h.symm))]
      simp
    · rw [ite_eq_right hb]
      simp
  · rw [ite_eq_right hac, ite_eq_right hac, zero_add]
    by_cases hb : a = P.last true <;> by_cases hc : P.last false = c
    · rw [ite_eq_left ⟨hb, hc.symm⟩, ite_eq_left hb, ite_eq_left hc]
      simp
    · rw [ite_eq_right (fun h => hc h.2.symm), ite_eq_left hb, ite_eq_right hc]
      simp
    · rw [ite_eq_right (fun h => hb h.1), ite_eq_right hb]
    · rw [ite_eq_right (fun h => hb h.1), ite_eq_right hb]

/-- Multiplying `1 + E_{b,v}` on the right by the elementary matrix of a step whose `last false`
letter is `c₀`: the rows add when `v b = 0`. -/
lemma Emat_one_add_mul {α : Type*} [Fintype α] [DecidableEq α] (b c₀ : α)
    (v : α → ℕ) (hv : v b = 0) :
    (1 + Emat b v) * (1 + Emat b (fun c => if c₀ = c then 1 else 0))
      = 1 + Emat b (fun c => v c + (if c₀ = c then 1 else 0)) := by
  have hVW : Emat b v * Emat b (fun c => if c₀ = c then 1 else 0) = 0 := by
    rw [Emat_mul, hv]
    ext a c
    simp [Emat]
  calc (1 + Emat b v) * (1 + Emat b (fun c => if c₀ = c then 1 else 0))
      = 1 + Emat b v + (Emat b (fun c => if c₀ = c then 1 else 0)
          + Emat b v * Emat b (fun c => if c₀ = c then 1 else 0)) := by noncomm_ring
    _ = 1 + Emat b v + Emat b (fun c => if c₀ = c then 1 else 0) := by rw [hVW, add_zero]
    _ = 1 + (Emat b v + Emat b (fun c => if c₀ = c then 1 else 0)) := by abel
    _ = 1 + Emat b (fun c => v c + (if c₀ = c then 1 else 0)) := by rw [Emat_add]

/-! ## Counting the `last false` letters along a run of `true` steps -/

/-- The number of steps `i < K` of the run of `true` steps from `P` at which the letter `c` is
last in the bottom order. -/
private noncomputable def lfCount {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (K : ℕ) (c : α) : ℕ :=
  ((Finset.range K).filter
    (fun i => (IETDatum₂.vertex P (List.replicate i true)).last false = c)).card

private lemma lfCount_zero {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (c : α) : lfCount P 0 c = 0 := by
  simp [lfCount]

private lemma lfCount_succ {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (K : ℕ) (c : α) :
    lfCount P (K + 1) c = lfCount P K c
      + (if (IETDatum₂.vertex P (List.replicate K true)).last false = c then 1 else 0) := by
  rw [lfCount, lfCount, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

/-- Along a run of `true` steps from an irreducible vertex, the letter `last true` is never last in
the bottom order. -/
private lemma lfCount_last_true {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) (K : ℕ) :
    lfCount P K (P.last true) = 0 := by
  have hb (i) : (IETDatum₂.vertex P (List.replicate i true)).last false ≠ P.last true := by
    intro hh
    have h1 : (IETDatum₂.vertex P (List.replicate i true)).last true = P.last true :=
      IETDatum₂.true_block_last_true P i
    exact IETDatum₂.vertex_last_ne P hP hn (List.replicate i true) (by rw [h1, hh])
  rw [lfCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _ hi
  exact hb i hi

/-! ## The product of a run of `true` steps -/

/-- **A run of `true` steps is a rank-one perturbation of the identity, in the form needed for the
induction**: `Q(true^K) = 1 + E_{b, lfCount K}`. -/
private theorem Q_replicate_true_eq_one_add_Emat {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    [NeZero n] (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) (K : ℕ) :
    IETDatum₂.Path.Q P (List.replicate K true)
      = 1 + Emat (P.last true) (lfCount P K) := by
  induction K with
  | zero =>
    rw [List.replicate_zero, IETDatum₂.Path.Q_nil]
    have h : lfCount P 0 = fun _ => 0 := funext (fun c => lfCount_zero P c)
    rw [h]
    ext a c
    simp [Emat]
  | succ K ih =>
    have hcount : lfCount P (K + 1)
        = fun c => lfCount P K c
            + (if (IETDatum₂.vertex P (List.replicate K true)).last false = c then 1 else 0) :=
      funext (fun c => lfCount_succ P K c)
    rw [List.replicate_succ', IETDatum₂.Path.Q_append, IETDatum₂.Path.Q_singleton, ih, hcount]
    rw [rvMat_true_eq _ (IETDatum₂.vertex_last_ne P hP hn (List.replicate K true)),
      IETDatum₂.true_block_last_true,
      ← Emat_one_add_mul (P.last true)
        ((IETDatum₂.vertex P (List.replicate K true)).last false) (lfCount P K)
        (lfCount_last_true P hP hn K)]

/-! ## The rotation of the bottom order -/

/-- **The orbit of a position under one `true` step at an extreme vertex**: the insertion of the
last position just after position `0` fixes `0` and rotates the other `n - 1` positions by one. -/
lemma insertEquiv_zero_pow_val {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n)
    (hi : i ≠ 0) (j : ℕ) :
    (((insertEquiv (0 : Fin n)) ^ j) i).val = 1 + ((i.val - 1 + j) % (n - 1)) := by
  induction j with
  | zero =>
    rw [pow_zero, Equiv.Perm.one_apply, Nat.add_zero]
    have h1 : 1 ≤ i.val := Fin.pos_iff_ne_zero.mpr hi
    rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)]
    omega
  | succ j ih =>
    set s : ℕ := (i.val - 1 + j) % (n - 1) with hs
    set p : Fin n := ((insertEquiv (0 : Fin n)) ^ j) i with hp
    have hn2 : ((0 : Fin n)).val + 1 < n := by simp only [Fin.val_zero]; omega
    rw [pow_succ', Equiv.Perm.mul_apply, ← hp]
    have hmod : (i.val - 1 + (j + 1)) % (n - 1) = (s + 1) % (n - 1) := by
      have h1 : i.val - 1 + (j + 1) = (i.val - 1 + j) + 1 := by omega
      rw [h1, hs]
      exact ((Nat.mod_modEq (i.val - 1 + j) (n - 1)).add_right 1).symm
    rw [hmod]
    have hsm : s < n - 1 := Nat.mod_lt _ (by omega)
    by_cases hcase : s + 1 = n - 1
    · have hpl : p = lastPos n := by
        apply Fin.ext
        rw [lastPos_val]
        omega
      rw [hpl, insertEquiv_lastPos hn2, hcase, Nat.mod_self]
      simp
    · have hlt : s + 1 < n - 1 := by omega
      have hgt : ((0 : Fin n)).val < p.val := by rw [ih]; simp
      have hne : p ≠ lastPos n := by
        intro h
        rw [h, lastPos_val] at ih
        omega
      rw [insertEquiv_apply_gt (p := (0 : Fin n)) (k := p) hn2 hgt hne,
        Nat.mod_eq_of_lt hlt]
      omega

/-- **The bottom order after `j` steps of a run of `true` steps from an extreme vertex**. -/
private lemma piBottom_replicate_true_apply {α : Type*} [Fintype α] {n : ℕ}
    [NeZero n] (P : IETDatum₂ α n) (hx : P.piBottom (P.last true) = 0) (j : ℕ) (a : α) :
    (IETDatum₂.vertex P (List.replicate j true)).piBottom a
      = ((insertEquiv (0 : Fin n)) ^ j) (P.piBottom a) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ', IETDatum₂.vertex_append_singleton, IETDatum₂.rvStep_apply_true]
    have hpiv : (IETDatum₂.vertex P (List.replicate j true)).piBottom
        ((IETDatum₂.vertex P (List.replicate j true)).last true) = (0 : Fin n) := by
      rw [IETDatum₂.true_block_pivot P j]; exact hx
    rw [hpiv, ih, pow_succ', Equiv.Perm.mul_apply]

/-- **When a given letter is last in the bottom order along a run of `true` steps.** -/
private lemma last_false_replicate_of_mod {α : Type*} [Fintype α] {n : ℕ}
    [NeZero n] (P : IETDatum₂ α n) (hx : P.piBottom (P.last true) = 0) (hn : 2 ≤ n)
    {c : α} (hc : c ≠ P.last true) {j : ℕ}
    (hj : j % (n - 1) = n - 1 - (P.piBottom c).val) :
    (IETDatum₂.vertex P (List.replicate j true)).last false = c := by
  have hne : P.piBottom c ≠ 0 := by
    intro h
    exact hc (P.piBottom.injective (by rw [h, hx]))
  have hv1 : 1 ≤ (P.piBottom c).val := Fin.pos_iff_ne_zero.mpr hne
  have hvle : (P.piBottom c).val ≤ n - 1 := by have := (P.piBottom c).isLt; omega
  have key : (IETDatum₂.vertex P (List.replicate j true)).piBottom c = lastPos n := by
    rw [piBottom_replicate_true_apply P hx j c]
    apply Fin.ext
    rw [insertEquiv_zero_pow_val hn _ hne j]
    have hstep : ((P.piBottom c).val - 1 + j) % (n - 1)
        = ((P.piBottom c).val - 1 + (j % (n - 1))) % (n - 1) := by
      rw [Nat.add_mod,
        Nat.mod_eq_of_lt (show (P.piBottom c).val - 1 < n - 1 by omega)]
    rw [hstep, hj, Nat.mod_eq_of_lt (by omega)]
    have : (P.piBottom c).val - 1 + (n - 1 - (P.piBottom c).val) = n - 1 - 1 := by omega
    rw [this, lastPos_val]
    omega
  have h1 : (IETDatum₂.vertex P (List.replicate j true)).last false
      = (IETDatum₂.vertex P (List.replicate j true)).piBottom.symm (lastPos n) := (rfl)
  rw [h1, ← key, Equiv.symm_apply_apply]

/-- **The counting bound**: the number of multiples of `m` in a residue class below `K` is at
least `K / m`. -/
lemma card_filter_mod_ge (m K r : ℕ) (hm : 1 ≤ m) (hr : r < m) :
    K / m ≤ ((Finset.range K).filter (fun j => j % m = r)).card := by
  have hinj : Function.Injective (fun i => i * m + r) := by
    intro i₁ i₂ h
    exact Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel h)
  have hsub : (Finset.range (K / m)).image (fun i => i * m + r)
      ⊆ (Finset.range K).filter (fun j => j % m = r) := by
    intro j hj
    simp only [Finset.mem_image, Finset.mem_range] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · have h1 : i + 1 ≤ K / m := hi
      have h2 : (i + 1) * m ≤ K :=
        le_trans (Nat.mul_le_mul_right m h1) (Nat.div_mul_le_self K m)
      have h3 : i * m + r < (i + 1) * m := by rw [Nat.succ_mul]; omega
      omega
    · rw [Nat.add_comm, Nat.mul_comm i m, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  calc K / m = ((Finset.range (K / m)).image (fun i => i * m + r)).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    _ ≤ _ := Finset.card_le_card hsub

/-- **A `true` block from an extreme vertex is a rank-one perturbation of the identity.** -/
theorem Q_replicate_true {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (Q : IETDatum₂ α n) (hQ : Q.Irreducible) (hn : 2 ≤ n)
    (hx : Q.last true = Q.piBottom.symm 0) (K : ℕ) :
    ∃ v : α → ℕ, v (Q.last true) = 0 ∧
      IETDatum₂.Path.Q Q (List.replicate K true)
        = 1 + Matrix.of (fun a c => if a = Q.last true then (v c : ℤ) else 0) ∧
      ∀ c, c ≠ Q.last true → K / (Fintype.card α - 1) ≤ v c := by
  have h0 : Q.piBottom (Q.last true) = 0 := by rw [hx, Equiv.apply_symm_apply]
  have hcard : Fintype.card α = n := by
    rw [← Fintype.card_fin n]
    exact Fintype.card_congr Q.piBottom
  refine ⟨lfCount Q K, lfCount_last_true Q hQ hn K, ?_, ?_⟩
  · rw [Q_replicate_true_eq_one_add_Emat Q hQ hn K]
    rfl
  · intro c hc
    have hne : Q.piBottom c ≠ 0 := by
      intro h
      exact hc (Q.piBottom.injective (by rw [h, h0]))
    have hv1 : 1 ≤ (Q.piBottom c).val := Fin.pos_iff_ne_zero.mpr hne
    have hvle : (Q.piBottom c).val ≤ n - 1 := by have := (Q.piBottom c).isLt; omega
    have hincl : (Finset.range K).filter
        (fun j => j % (n - 1) = n - 1 - (Q.piBottom c).val)
        ⊆ (Finset.range K).filter
          (fun j => (IETDatum₂.vertex Q (List.replicate j true)).last false = c) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨hj.1, last_false_replicate_of_mod Q h0 hn hc hj.2⟩
    rw [hcard]
    exact le_trans (card_filter_mod_ge (n - 1) K (n - 1 - (Q.piBottom c).val)
      (by omega) (by omega)) (Finset.card_le_card hincl)

end IETDatum₂.Path

end IntervalExchange

namespace IntervalExchange.Rigidity

/-- **Big cell from a run**: at the beginning of the run the extreme letter's cell occupies at least
`1 - δ` of the base. -/
theorem bigCell_of_mem_cone {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (Q : IETDatum₂ α n) (hQ : Q.Irreducible) (hn : 2 ≤ n)
    (hx : Q.last true = Q.piBottom.symm 0) {K : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hK : (1 - δ) / δ ≤ (K / (Fintype.card α - 1) : ℕ))
    {σ σ' : α → ℝ} (hpos : ∀ c, 0 < σ' c)
    (hσ : σ = qApply (IETDatum₂.Path.Q Q (List.replicate K true)) σ') :
    (1 - δ) * ∑ c, σ c ≤ σ (Q.last true) := by
  set b : α := Q.last true with hb
  obtain ⟨v, hv0, hmat, hbound⟩ := IETDatum₂.Path.Q_replicate_true Q hQ hn hx K
  rw [hσ, hmat]
  set M : Matrix α α ℤ := 1 + Matrix.of (fun a c => if a = b then (v c : ℤ) else 0) with hM
  -- the entries of `M`
  have hentry (a) (c : α) : M a c
      = (if a = c then (1 : ℤ) else 0) + (if a = b then (v c : ℤ) else 0) := by
    rw [hM, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
  have hentry' (a) (c : α) : (M a c : ℝ)
      = (if a = c then (1 : ℝ) else 0) + (if a = b then (v c : ℝ) else 0) := by
    rw [hentry a c]
    by_cases h1 : a = c <;> by_cases h2 : a = b <;> simp [h1, h2]
  -- the action of `M` on a vector
  have happly (a) : qApply M σ' a
      = σ' a + (if a = b then ∑ c, (v c : ℝ) * σ' c else 0) := by
    rw [qApply_apply]
    have hterm (c) : (M a c : ℝ) * σ' c = (if a = c then (1 : ℝ) else 0) * σ' c
        + (if a = b then (v c : ℝ) * σ' c else 0) := by
      rw [hentry' a c, add_mul]
      by_cases h : a = b <;> simp [h]
    rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_add_distrib]
    have h1 : ∑ c, (if a = c then (1 : ℝ) else 0) * σ' c = σ' a := by
      have hstep (c) : (if a = c then (1 : ℝ) else 0) * σ' c
          = (if a = c then σ' c else 0) := by
        by_cases h : a = c <;> simp [h]
      rw [Finset.sum_congr rfl (fun c _ => hstep c),
        Finset.sum_ite_eq Finset.univ a (fun c => σ' c)]
      simp
    rw [h1]
    by_cases h : a = b <;> simp [h]
  have hσb : qApply M σ' b = σ' b + ∑ c, (v c : ℝ) * σ' c := by
    rw [happly b, ite_eq_left rfl]
  have hσc (c) (hc : c ≠ b) : qApply M σ' c = σ' c := by
    rw [happly c, ite_eq_right hc, add_zero]
  -- split the total mass at the letter `b`
  set S : ℝ := ∑ c ∈ Finset.univ.erase b, σ' c with hS
  have hsum : ∑ c, qApply M σ' c = qApply M σ' b + S := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b), add_comm]
    congr 1
    rw [hS]
    exact Finset.sum_congr rfl (fun c hc => hσc c (Finset.mem_erase.mp hc).1)
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun c _ => le_of_lt (hpos c))
  have hδ0 : 0 ≤ 1 - δ := by linarith
  have hVd : 1 - δ ≤ δ * ((K / (Fintype.card α - 1) : ℕ) : ℝ) := by
    rw [div_le_iff₀ hδ] at hK
    linarith
  -- the `b`-coordinate dominates `S` with the factor `K / (card α - 1)`
  have hlow : ((K / (Fintype.card α - 1) : ℕ) : ℝ) * S ≤ qApply M σ' b := by
    have hsplit : ∑ c, (v c : ℝ) * σ' c
        = ∑ c ∈ Finset.univ.erase b, (v c : ℝ) * σ' c := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b)]
      have hvb : ((v b : ℝ)) * σ' b = 0 := by rw [hb, hv0]; simp
      rw [hvb, add_zero]
    have hstep : ((K / (Fintype.card α - 1) : ℕ) : ℝ) * S
        ≤ ∑ c ∈ Finset.univ.erase b, (v c : ℝ) * σ' c := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_le_sum (fun c hc => ?_)
      rw [Finset.mem_erase] at hc
      refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (hpos c))
      exact_mod_cast hbound c hc.1
    rw [hσb, hsplit]
    linarith [hpos b]
  calc (1 - δ) * ∑ c, qApply M σ' c
      = (1 - δ) * (qApply M σ' b + S) := by rw [hsum]
    _ ≤ qApply M σ' b := by
        have h1 : (1 - δ) * S ≤ δ * qApply M σ' b := by
          calc (1 - δ) * S ≤ (δ * ((K / (Fintype.card α - 1) : ℕ) : ℝ)) * S :=
                mul_le_mul_of_nonneg_right hVd hS0
            _ = δ * (((K / (Fintype.card α - 1) : ℕ) : ℝ) * S) := by ring
            _ ≤ δ * qApply M σ' b :=
                mul_le_mul_of_nonneg_left hlow (le_of_lt hδ)
        nlinarith [hδ0]

end IntervalExchange.Rigidity

end
