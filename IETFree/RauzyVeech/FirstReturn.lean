/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.Nesting
public import IETFree.RauzyVeech.Step

/-!
# The first return map of an interval exchange into a Rauzy subinterval

Setup (the "Rauzy situation", type `false` of `IETDatum₂.rvStep`): `T = mkIETFun lam π 0` is the
exchange on `[0, Λ)`, `Λ = ∑ lam`, with cells indexed by bottom position.  `topCell π = π⁻¹ (last)`
is the cell whose *image* is the rightmost image cell, `botCell = last` is the rightmost domain
cell.  The hypothesis is `λ (topCell π) < λ botCell` (the image-rightmost cell is the shorter of the
two rightmost cells), and the induced subinterval is `[0, c)` with `c = Λ - λ (topCell
 π)`. Main results:
* `Tower.ret_of_mem`, `Tower.ret_of_not_mem`: the first return time `ret` of `[0, c)` is `1` on the
  subinterval and `2` off it (`ret y = 1` if `T y ∈ [0,c)`, `= 2` otherwise);
* `Tower.exchHat_eq_exch` / `Tower.exchHat_eq_exch_sq`: the first return map is `T` on the cells
  whose image is not the rightmost one, and `T²` on the cell `topCell π`;
* `Tower.firstReturn_eq`: the first return map is again an interval exchange, with lengths `lamHat`
  (`λ` with the top-rightmost length removed from the bottom-rightmost cell) and permutation
  `piHat = insertEquiv (π botCell) ∘ π`, which is exactly the Rauzy–Veech step;
* `Tower.rvMat_toComb_false_apply`: the multiplicity matrix of the return is `rvMat false` — one
  floor over `α`, plus a second one over `topCell π` inside `botCell`;
* `Tower.tower_decomp`, `Tower.tower_decomp_iUnion`: the tower decomposition
  `[0, Λ) = ⨆ β, ⨆ j < h β, T^[j] (cell β)`, with return times `h β ∈ {1, 2}`
  (`Tower.returnB_eq_one`, `Tower.returnB_eq_two`);
* `Tower.tower_formula_one_step`: the tower formula at level one for an invariant measure.
-/

@[expose] public section

open MeasureTheory Finset
open scoped BigOperators ENNReal NNReal

/-!
# The first return map, the tower decomposition and the tower formula

**Status.**  Part 1 (the Rauzy first return, type `false` case) is complete: the first return time
is `1` or `2`, the return map is `mkIETFun` for the data `rvStep _ false` and the lengths
transformed by `rvMat false`, and the exchange decomposes into the base interval and the floor of
the second tower. Part 2 is complete at level one: the floors of one tower have equal mass and the
multiplicity of the floor over `β` inside the cell `α` is `rvMat false`.

**What follows this file**: the inverse Rauzy type (`TrueStep.lean`), the tower-of-towers refinement
(the level-`(k+1)` floors refine the level-`k` ones) and the level-`n` formula `μ (cell α) = ∑ β,
(Path.Q P γ α β : ℝ) * μ (level-n cell β)` for an arbitrary word `γ`, by induction on `γ` from `Q (γ
++ [ε]) = Q γ * rvMat ε` (`LevelN.lean`, `TrueStep.TowerTrue.tower_formula_level_pathQ_any`). -/

namespace Tower

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## 1. Notation and elementary facts -/

theorem le_lastPos (i : Fin n) : i ≤ IETDatum₂.lastPos n := by
  rw [Fin.le_def, IETDatum₂.lastPos_val]
  have := i.isLt
  omega

theorem lt_lastPos_iff {i : Fin n} : i < IETDatum₂.lastPos n ↔ i.val + 1 < n := by
  rw [Fin.lt_def, IETDatum₂.lastPos_val]
  have := i.isLt
  omega

/-- The cell whose image is the rightmost image cell (`π⁻¹ (last)`). -/
def topCell (π : Equiv.Perm (Fin n)) : Fin n := π.symm (IETDatum₂.lastPos n)

/-- The rightmost domain cell. -/
def botCell : Fin n := IETDatum₂.lastPos n

@[simp] theorem topCell_apply (π : Equiv.Perm (Fin n)) :
    π (topCell π) = IETDatum₂.lastPos n := π.apply_symm_apply _

theorem topCell_inj {π : Equiv.Perm (Fin n)} {j : Fin n} (h : π j = IETDatum₂.lastPos n) :
    j = topCell π := by
  apply π.injective
  rw [topCell_apply, h]

theorem topCell_ne_botCell {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam botCell) : topCell π ≠ botCell :=
  fun h => absurd hlt (by rw [h]; exact lt_irrefl _)

/-- The total length `Λ = ∑ lam`. -/
def tot (lam : Fin n → ℝ≥0) : ℝ := ∑ i, (lam i : ℝ)

omit [NeZero n] in
theorem single_le_tot (lam : Fin n → ℝ≥0) (i : Fin n) : (lam i : ℝ) ≤ tot lam :=
  Finset.single_le_sum (f := fun i => (lam i : ℝ)) (fun i _ => (lam i).coe_nonneg)
    (Finset.mem_univ i)

theorem filter_lt_lastPos (π : Equiv.Perm (Fin n)) :
    Finset.univ.filter (fun j => π j < IETDatum₂.lastPos n) = Finset.univ.erase (topCell π) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · intro hj
    refine ⟨?_, trivial⟩
    intro hje
    rw [hje, topCell_apply] at hj
    exact absurd hj (lt_irrefl _)
  · intro hj
    show π j < IETDatum₂.lastPos n
    exact lt_of_le_of_ne (le_lastPos _) (fun hh => hj.1 (topCell_inj hh))

/-- The image of the cell `topCell π` starts at `Λ - λ (topCell π)`. -/
theorem imageLeft_topCell (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    imageLeft π lam (topCell π) = tot lam - (lam (topCell π) : ℝ) := by
  have hset : Finset.univ.filter (fun j => π j < π (topCell π))
      = Finset.univ.erase (topCell π) := by
    rw [topCell_apply]; exact filter_lt_lastPos π
  rw [imageLeft, hset, tot,
    ← Finset.add_sum_erase _ (fun i => (lam i : ℝ)) (Finset.mem_univ _)]
  ring

/-- The right end of the image of the cell `i`. -/
def imageUpper (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => π j ≤ π i), (lam j : ℝ)

omit [NeZero n] in
theorem imageUpper_eq (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (i : Fin n) :
    imageUpper π lam i = imageLeft π lam i + (lam i : ℝ) := by
  have hins : Finset.univ.filter (fun j => π j ≤ π i)
      = insert i (Finset.univ.filter (fun j => π j < π i)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      rcases lt_or_eq_of_le hj with h | h
      · exact Or.inr h
      · exact Or.inl (π.injective h)
    · rintro (rfl | h)
      · exact le_rfl
      · exact le_of_lt h
  rw [imageUpper, hins, Finset.sum_insert (by simp), imageLeft]
  ring

/-- The image of a cell that is not the rightmost one ends before the cut point. -/
theorem imageUpper_le_tot (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) {i : Fin n}
    (hi : i ≠ topCell π) : imageUpper π lam i ≤ tot lam - (lam (topCell π) : ℝ) := by
  have hsub : Finset.univ.filter (fun j => π j ≤ π i)
      ⊆ Finset.univ.erase (topCell π) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro hje
    rw [hje, topCell_apply] at hj
    refine hi (topCell_inj ?_)
    exact le_antisymm (le_lastPos _) hj
  have hle : imageUpper π lam i
      ≤ ∑ j ∈ Finset.univ.erase (topCell π), (lam j : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => (lam j).coe_nonneg)
  have hsplit : (∑ j ∈ Finset.univ.erase (topCell π), (lam j : ℝ)) + (lam (topCell π) : ℝ)
      = tot lam := by
    rw [tot, Finset.sum_erase_add _ (fun i => (lam i : ℝ)) (Finset.mem_univ _)]
  linarith

/-! ## 2. The new length vector and the new permutation -/

/-- The new length vector: the rightmost domain cell loses the length of the rightmost image cell.
It is `lam` in bottom order (for a step of type `false` the bottom order is unchanged). -/
def lamHat (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) : Fin n → ℝ≥0 :=
  fun i => if i = botCell then lam i - lam (topCell π) else lam i

/-- The new permutation of the step: the cell `topCell π` is inserted just after `π botCell`. -/
def piHat (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  π.trans (IETDatum₂.insertEquiv (π botCell))

theorem piHat_apply (π : Equiv.Perm (Fin n)) (j : Fin n) :
    piHat π j = IETDatum₂.insertEquiv (π botCell) (π j) := rfl

theorem botCell_ne_lastPos_iff_pi {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam botCell) : π botCell ≠ IETDatum₂.lastPos n := by
  intro h
  exact topCell_ne_botCell hlt (topCell_inj h).symm

theorem pivot_succ_lt {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam botCell) : (π botCell).val + 1 < n := by
  have h1 : π botCell < IETDatum₂.lastPos n :=
    lt_of_le_of_ne (le_lastPos _) (botCell_ne_lastPos_iff_pi hlt)
  rwa [lt_lastPos_iff] at h1

theorem piHat_topCell_val {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam botCell) :
    (piHat π (topCell π)).val = (π botCell).val + 1 := by
  rw [piHat_apply, topCell_apply, IETDatum₂.insertEquiv_lastPos (pivot_succ_lt hlt)]

/-! ## 3. The new length vector: sums and endpoints -/

theorem lamHat_coe {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam botCell) (j : Fin n) :
    (lamHat π lam j : ℝ) = (lam j : ℝ) - (if j = botCell then (lam (topCell π) : ℝ) else 0) := by
  rw [lamHat]
  by_cases hj : j = botCell
  · subst hj
    rw [ite_eq_left rfl, ite_eq_left rfl, NNReal.coe_sub (le_of_lt hlt)]
  · rw [ite_eq_right hj, ite_eq_right hj, sub_zero]

theorem lamHat_of_ne {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0} {j : Fin n}
    (hj : j ≠ botCell) : lamHat π lam j = lam j := by
  rw [lamHat, ite_eq_right hj]

theorem lamHat_botCell {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam botCell) :
    (lamHat π lam botCell : ℝ) = (lam botCell : ℝ) - (lam (topCell π) : ℝ) := by
  rw [lamHat, ite_eq_left rfl, NNReal.coe_sub (le_of_lt hlt)]

theorem sum_filter_lamHat {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam botCell) (S : Finset (Fin n)) :
    ∑ j ∈ S, (lamHat π lam j : ℝ)
      = ∑ j ∈ S, (lam j : ℝ) - (if botCell ∈ S then (lam (topCell π) : ℝ) else 0) := by
  have hterm (j) (hj : j ∈ S) : (lamHat π lam j : ℝ)
      = (lam j : ℝ) - (if j = botCell then (lam (topCell π) : ℝ) else 0) := lamHat_coe hlt j
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' S botCell (fun _ => (lam (topCell π) : ℝ))]

/-- The left ends are unchanged: the modified coordinate is the last one. -/
theorem leftEnd_lamHat (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (i : Fin n) :
    leftEnd (lamHat π lam) i = leftEnd lam i := by
  rw [leftEnd, leftEnd]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  rw [lamHat_of_ne]
  intro h
  rw [h] at hj
  exact absurd (le_lastPos i) (not_le.mpr hj)

/-- The total length of the new vector. -/
theorem sum_lamHat {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam botCell) :
    ∑ i, (lamHat π lam i : ℝ) = tot lam - (lam (topCell π) : ℝ) := by
  have h := sum_filter_lamHat (π := π) hlt Finset.univ
  simpa only [tot, Finset.mem_univ, ite_true] using h

/-- The cut point `c = Λ - λ (topCell π)`. -/
def cut (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) : ℝ := tot lam - (lam (topCell π) : ℝ)

theorem cut_eq_sum_lamHat {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam botCell) :
    ∑ i, (lamHat π lam i : ℝ) = cut π lam :=
  sum_lamHat hlt

theorem filter_lt_botCell : Finset.univ.filter (fun j : Fin n => j < botCell)
    = Finset.univ.erase botCell := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · intro hj
    exact ⟨ne_of_lt hj, trivial⟩
  · intro hj
    exact lt_of_le_of_ne (le_lastPos j) hj.1

theorem leftEnd_botCell (lam : Fin n → ℝ≥0) :
    leftEnd lam botCell = tot lam - (lam botCell : ℝ) := by
  rw [leftEnd, filter_lt_botCell, tot,
    ← Finset.add_sum_erase _ (fun i => (lam i : ℝ)) (Finset.mem_univ _)]
  ring

/-- The right end of the cell `botCell` is the total length. -/
theorem upperEnd_botCell (lam : Fin n → ℝ≥0) : upperEnd lam botCell = tot lam := by
  rw [upperEnd_eq, leftEnd_botCell]
  ring

/-! ## 4. Order properties of the insertion -/

/-- The insertion of the position `p` preserves the order of the positions that are not last, and
moves the last position to `p + 1`.  This is the combinatorial core of the step: it compares the
images of two cells that both avoid `topCell`. -/
theorem insertEquiv_lt_iff {p : Fin n} (hp : p.val + 1 < n) {k k' : Fin n}
    (hk : k ≠ IETDatum₂.lastPos n) (hk' : k' ≠ IETDatum₂.lastPos n) :
    IETDatum₂.insertEquiv p k' < IETDatum₂.insertEquiv p k ↔ k' < k := by
  by_cases h2 : k'.val ≤ p.val
  · have hik' : IETDatum₂.insertEquiv p k' = k' := IETDatum₂.insertEquiv_apply_le h2
    by_cases h1 : k.val ≤ p.val
    · have hik : IETDatum₂.insertEquiv p k = k := IETDatum₂.insertEquiv_apply_le h1
      rw [hik', hik]
    · have h1' : p.val < k.val := by omega
      have hikv : ((IETDatum₂.insertEquiv p) k).val = k.val + 1 :=
        IETDatum₂.insertEquiv_apply_gt hp h1' hk
      rw [hik', Fin.lt_def, hikv, Fin.lt_def]
      omega
  · have h2' : p.val < k'.val := by omega
    have hik'v : ((IETDatum₂.insertEquiv p) k').val = k'.val + 1 :=
      IETDatum₂.insertEquiv_apply_gt hp h2' hk'
    by_cases h1 : k.val ≤ p.val
    · have hik : IETDatum₂.insertEquiv p k = k := IETDatum₂.insertEquiv_apply_le h1
      rw [hik, Fin.lt_def, hik'v, Fin.lt_def]
      omega
    · have h1' : p.val < k.val := by omega
      have hikv : ((IETDatum₂.insertEquiv p) k).val = k.val + 1 :=
        IETDatum₂.insertEquiv_apply_gt hp h1' hk
      rw [Fin.lt_def, hik'v, hikv, Fin.lt_def]
      omega

/-! ## 5. The images of the cells after the step -/

variable {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}

theorem piHat_apply_gt (hlt : lam (topCell π) < lam botCell) {i : Fin n}
    (h : (π botCell).val < (π i).val) (hit : i ≠ topCell π) :
    (piHat π i).val = (π i).val + 1 :=
  IETDatum₂.insertEquiv_apply_gt (pivot_succ_lt hlt) h (fun hh => hit (topCell_inj hh))

theorem piHat_apply_le {i : Fin n} (h : (π i).val ≤ (π botCell).val) : piHat π i = π i :=
  IETDatum₂.insertEquiv_apply_le h

/-- **The images of all the cells except the rightmost one are unchanged** by the step: the cut only
moves the rightmost image cell, which is `topCell π`'s image, past the image of `botCell`. -/
theorem imageLeft_lamHat_of_ne (hlt : lam (topCell π) < lam botCell) (i : Fin n)
    (hit : i ≠ topCell π) :
    imageLeft (piHat π) (lamHat π lam) i = imageLeft π lam i := by
  have hpv := pivot_succ_lt hlt
  have hit' : π i ≠ IETDatum₂.lastPos n := fun h => hit (topCell_inj h)
  have hkey (j : Fin n) (hj : j ≠ topCell π) : (piHat π j < piHat π i ↔ π j < π i) := by
    have hj' : π j ≠ IETDatum₂.lastPos n := fun h => hj (topCell_inj h)
    rw [piHat_apply, piHat_apply]
    exact insertEquiv_lt_iff hpv hit' hj'
  by_cases hcase : (π i).val ≤ (π botCell).val
  · -- case 1: the image of `i` ends before the image of `botCell`
    have hii : piHat π i = π i := piHat_apply_le hcase
    have hS : Finset.univ.filter (fun j => piHat π j < piHat π i)
        = Finset.univ.filter (fun j => π j < π i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hj : j = topCell π
      · subst hj
        have h1 : ¬ (piHat π (topCell π) < piHat π i) := by
          intro hcon
          rw [Fin.lt_def, piHat_topCell_val (π := π) (lam := lam) hlt, hii] at hcon
          omega
        have h2 : ¬ (π (topCell π) < π i) := by
          rw [topCell_apply]; exact not_lt.mpr (le_lastPos _)
        exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      · exact hkey j hj
    have hnotmem : botCell ∉ Finset.univ.filter (fun j => π j < π i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      exact hcase
    have hmain :
        ∑ j ∈ Finset.univ.filter (fun j => piHat π j < piHat π i), (lamHat π lam j : ℝ)
          = ∑ j ∈ Finset.univ.filter (fun j => π j < π i), (lam j : ℝ) := by
      rw [hS, sum_filter_lamHat hlt, ite_eq_right hnotmem, sub_zero]
    exact hmain
  · -- case 2: the image of `i` lies strictly after the image of `botCell`
    have hcase' : (π botCell).val < (π i).val := by omega
    have hii : (piHat π i).val = (π i).val + 1 := piHat_apply_gt hlt hcase' hit
    have hS : Finset.univ.filter (fun j => piHat π j < piHat π i)
        = insert (topCell π) (Finset.univ.filter (fun j => π j < π i)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hj : j = topCell π
      · subst hj
        have h1 : piHat π (topCell π) < piHat π i := by
          rw [Fin.lt_def, piHat_topCell_val (π := π) (lam := lam) hlt, hii]
          omega
        have h2 : ¬ (π (topCell π) < π i) := by
          rw [topCell_apply]; exact not_lt.mpr (le_lastPos _)
        exact ⟨fun _ => Or.inl rfl, fun _ => h1⟩
      · have hk := hkey j hj
        constructor
        · intro h; exact Or.inr (hk.mp h)
        · rintro (rfl | h)
          · exact absurd rfl hj
          · exact hk.mpr h
    have hmem : botCell ∈ Finset.univ.filter (fun j => π j < π i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show π botCell < π i
      rw [Fin.lt_def]; exact hcase'
    have hnotmem : topCell π ∉ Finset.univ.filter (fun j => π j < π i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      rw [topCell_apply]; exact le_lastPos _
    have hmain :
        ∑ j ∈ Finset.univ.filter (fun j => piHat π j < piHat π i), (lamHat π lam j : ℝ)
          = ∑ j ∈ Finset.univ.filter (fun j => π j < π i), (lam j : ℝ) := by
      rw [hS, Finset.sum_insert hnotmem, sum_filter_lamHat hlt, ite_eq_left hmem,
        lamHat_of_ne (topCell_ne_botCell hlt)]
      ring
    exact hmain

/-- **The image of the rightmost cell** after the step: the old image of `botCell`, plus a new cell
of length `λ botCell - λ (topCell π)` inserted just after it. -/
theorem imageLeft_lamHat_topCell (hlt : lam (topCell π) < lam botCell) :
    imageLeft (piHat π) (lamHat π lam) (topCell π)
      = imageLeft π lam botCell + ((lam botCell : ℝ) - (lam (topCell π) : ℝ)) := by
  have hpv := pivot_succ_lt hlt
  have hSp : Finset.univ.filter (fun j => piHat π j < piHat π (topCell π))
      = insert botCell (Finset.univ.filter (fun j => π j < π botCell)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hj : j = topCell π
    · subst hj
      have h1 : ¬ (piHat π (topCell π) < piHat π (topCell π)) := lt_irrefl _
      have h2 : ¬ (π (topCell π) < π botCell) := by
        rw [topCell_apply]; exact not_lt.mpr (le_lastPos _)
      refine ⟨fun h => absurd h h1, ?_⟩
      rintro (hb | hlt')
      · exact absurd hb (topCell_ne_botCell hlt)
      · exact absurd hlt' h2
    · have hj' : π j ≠ IETDatum₂.lastPos n := fun h => hj (topCell_inj h)
      have hiff : piHat π j < piHat π (topCell π) ↔ (π j).val ≤ (π botCell).val := by
        rw [Fin.lt_def, piHat_topCell_val (π := π) (lam := lam) hlt]
        by_cases hc : (π j).val ≤ (π botCell).val
        · have hv : (piHat π j).val = (π j).val := by rw [piHat_apply_le hc]
          rw [hv]
          constructor <;> intro h <;> omega
        · have hc' : (π botCell).val < (π j).val := by omega
          rw [piHat_apply_gt hlt hc' hj]
          constructor <;> intro h <;> omega
      rw [hiff]
      exact ⟨fun h => (eq_or_lt_of_le h).elim (fun h1 => Or.inl (π.injective (Fin.ext h1)))
          (fun h1 => Or.inr (by rw [Fin.lt_def]; exact h1)),
        fun h => h.elim (fun hb => hb ▸ le_rfl) le_of_lt⟩
  have hnotmem : botCell ∉ Finset.univ.filter (fun j => π j < π botCell) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_irrefl _
  have hnotmem' : topCell π ∉ Finset.univ.filter (fun j => π j < π botCell) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    rw [topCell_apply]; exact le_lastPos _
  have hmain :
      ∑ j ∈ Finset.univ.filter (fun j => piHat π j < piHat π (topCell π)), (lamHat π lam j : ℝ)
        = ∑ j ∈ Finset.univ.filter (fun j => π j < π botCell), (lam j : ℝ)
          + ((lam botCell : ℝ) - (lam (topCell π) : ℝ)) := by
    rw [hSp, Finset.sum_insert hnotmem, sum_filter_lamHat hlt, ite_eq_right hnotmem, sub_zero,
      lamHat_botCell hlt]
    ring
  exact hmain

/-! ## 6. The translation vectors of the step -/

theorem translationVector_lamHat_of_ne (hlt : lam (topCell π) < lam botCell) (i : Fin n)
    (_hib : i ≠ botCell) (hit : i ≠ topCell π) :
    translationVector (piHat π) (lamHat π lam) i = translationVector π lam i := by
  rw [translationVector, translationVector, imageLeft_lamHat_of_ne hlt i hit, leftEnd_lamHat]

theorem translationVector_lamHat_botCell (hlt : lam (topCell π) < lam botCell) :
    translationVector (piHat π) (lamHat π lam) botCell = translationVector π lam botCell := by
  rw [translationVector, translationVector,
    imageLeft_lamHat_of_ne hlt botCell (fun h => topCell_ne_botCell hlt h.symm), leftEnd_lamHat]

/-- The translation on the rightmost cell: the return time is `2` there, and the two
translations add up. -/
theorem translationVector_lamHat_topCell (hlt : lam (topCell π) < lam botCell) :
    translationVector (piHat π) (lamHat π lam) (topCell π)
      = translationVector π lam (topCell π) + translationVector π lam botCell := by
  rw [translationVector, translationVector, translationVector,
    imageLeft_lamHat_topCell hlt, leftEnd_lamHat, imageLeft_topCell, leftEnd_botCell]
  ring

/-! ## 7. The dynamics of the first return to `[0, cut)` -/

/-- The exchange `T = mkIETFun lam π 0`. -/
def exch (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) : ℝ → ℝ := mkIETFun lam π 0

theorem cut_le_tot (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) : cut π lam ≤ tot lam := by
  rw [cut]
  exact sub_le_self _ (by positivity)

theorem mem_Ico_tot_of_mem_cut {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0} {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) : y ∈ Set.Ico 0 (tot lam) :=
  ⟨hy.1, lt_of_lt_of_le hy.2 (cut_le_tot π lam)⟩

/-- On `[0, Λ)` the exchange is the translation by the vector of the cell of `y`. -/
theorem exch_of_mem (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (tot lam)) :
    exch π lam y = y + translationVector π lam (idx lam y hy.1) := by
  have hmem : y ∈ Set.Ico 0 (0 + ∑ i, (lam i : ℝ)) := by
    refine ⟨by linarith [hy.1], ?_⟩
    rw [zero_add]
    exact hy.2
  have h := mkIETFun_of_mem lam π 0 hmem
  simpa [exch, zero_add] using h

/-- A point of the cut interval lies in the cell given by `idx`. -/
theorem idx_cut {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0} {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) :
    leftEnd lam (idx lam y hy.1) ≤ y ∧ y < upperEnd lam (idx lam y hy.1) :=
  ⟨idx_mem lam y hy.1, lt_upperEnd_idx lam (mem_Ico_tot_of_mem_cut hy)⟩

/-- The cut is positive. -/
theorem cut_pos {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam botCell) : 0 < cut π lam := by
  have h1 := NNReal.coe_lt_coe.mpr hlt
  have h2 := single_le_tot lam botCell
  rw [cut]; linarith

/-- The rightmost domain cell starts before the cut. -/
theorem leftEnd_botCell_le_cut {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam botCell) : leftEnd lam botCell < cut π lam := by
  rw [leftEnd_botCell, cut]
  have h := NNReal.coe_lt_coe.mpr hlt
  linarith

/-- The image of a cell other than the rightmost one ends before the cut. -/
theorem imageUpper_le_cut (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) {i : Fin n}
    (hi : i ≠ topCell π) : imageUpper π lam i ≤ cut π lam :=
  imageUpper_le_tot π lam hi

/-- **A point outside the rightmost cell returns to `[0, cut)` in one step.** -/
theorem exch_mem_cut_of_ne (_hlt : lam (topCell π) < lam botCell) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) (hi : idx lam y hy.1 ≠ topCell π) :
    exch π lam y ∈ Set.Ico 0 (cut π lam) := by
  have hyT := mem_Ico_tot_of_mem_cut hy
  rw [exch_of_mem π lam hyT]
  obtain ⟨h1, h2⟩ := idx_cut hy
  have hupper : imageUpper π lam (idx lam y hy.1) ≤ cut π lam := imageUpper_le_cut π lam hi
  have htv : translationVector π lam (idx lam y hy.1)
      = imageLeft π lam (idx lam y hy.1) - leftEnd lam (idx lam y hy.1) := rfl
  have hnn : 0 ≤ imageLeft π lam (idx lam y hy.1) := imageLeft_nonneg _ _ _
  have hueq : imageUpper π lam (idx lam y hy.1)
      = imageLeft π lam (idx lam y hy.1) + (lam (idx lam y hy.1) : ℝ) :=
    imageUpper_eq π lam _
  have hU : upperEnd lam (idx lam y hy.1)
      = leftEnd lam (idx lam y hy.1) + (lam (idx lam y hy.1) : ℝ) := upperEnd_eq _ _
  constructor
  · rw [htv]; linarith
  · rw [htv]; linarith

/-- **A point of the rightmost cell does not return in one step.** -/
theorem exch_mem_Ico_cut_tot (_hlt : lam (topCell π) < lam botCell) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) (hi : idx lam y hy.1 = topCell π) :
    exch π lam y ∈ Set.Ico (cut π lam) (tot lam) := by
  have hyT := mem_Ico_tot_of_mem_cut hy
  rw [exch_of_mem π lam hyT, hi]
  have hleft : cut π lam = tot lam - (lam (topCell π) : ℝ) := rfl
  have hspec := imageLeft_topCell π lam
  have h1 := idx_mem lam y hy.1
  rw [hi] at h1
  have h2 : y < leftEnd lam (topCell π) + (lam (topCell π) : ℝ) := by
    have h := lt_upperEnd_idx lam hyT
    rwa [upperEnd_eq, hi] at h
  have htv : translationVector π lam (topCell π)
      = imageLeft π lam (topCell π) - leftEnd lam (topCell π) := rfl
  constructor
  · rw [htv, hspec, hleft]; linarith
  · rw [htv, hspec]; linarith

/-- On the rightmost cell the image lands in the rightmost *domain* cell. -/
theorem idx_exch_of_idx_topCell (hlt : lam (topCell π) < lam botCell) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) (hi : idx lam y hy.1 = topCell π) :
    idx lam (exch π lam y)
      (le_trans (le_of_lt (cut_pos hlt)) (exch_mem_Ico_cut_tot hlt hy hi).1) = botCell := by
  obtain ⟨h1, h2⟩ := exch_mem_Ico_cut_tot hlt hy hi
  refine idx_eq lam ⟨le_trans (le_of_lt (cut_pos hlt)) h1, h2⟩ ?_ ?_
  · exact le_trans (le_of_lt (leftEnd_botCell_le_cut hlt)) h1
  · rw [upperEnd_botCell]; exact h2

/-- **The second iterate of a point of the rightmost cell.** -/
theorem exch_exch_eq (hlt : lam (topCell π) < lam botCell) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) (hi : idx lam y hy.1 = topCell π) :
    exch π lam (exch π lam y)
      = exch π lam y + translationVector π lam botCell := by
  have hT := exch_mem_Ico_cut_tot hlt hy hi
  have hidx := idx_exch_of_idx_topCell hlt hy hi
  have hT' : exch π lam y ∈ Set.Ico 0 (tot lam) :=
    ⟨le_trans (le_of_lt (cut_pos hlt)) hT.1, hT.2⟩
  rw [exch_of_mem π lam hT', hidx]

theorem iterate_two_eq (f : ℝ → ℝ) (y : ℝ) : f^[2] y = f (f y) := rfl

/-- The exchange with base point `0`, written with `idx` at `y` itself. -/
theorem mkIETFun_zero_of_mem {π' : Equiv.Perm (Fin n)} {lam' : Fin n → ℝ≥0} {y : ℝ}
    (hy : y ∈ Set.Ico 0 (∑ i, (lam' i : ℝ))) :
    mkIETFun lam' π' 0 y = y + translationVector π' lam' (idx lam' y hy.1) := by
  have h := mkIETFun_of_mem lam' π' 0 (x := y) (by simpa using hy)
  simpa using h

/-! ## 8. Endpoints of the new cells -/

theorem upperEnd_lamHat_of_ne {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0} {i : Fin n}
    (hi : i ≠ botCell) : upperEnd (lamHat π lam) i = upperEnd lam i := by
  rw [upperEnd_eq, upperEnd_eq, leftEnd_lamHat, lamHat_of_ne hi]

theorem upperEnd_lamHat_botCell {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam botCell) :
    upperEnd (lamHat π lam) botCell = cut π lam := by
  rw [upperEnd_eq, leftEnd_lamHat, leftEnd_botCell, lamHat_botCell hlt, cut]
  ring

/-- The `idx` of `y` does not change when the length of the rightmost cell is reduced, as long as
`y` lies in the cut interval. -/
theorem idx_lamHat_eq (hlt : lam (topCell π) < lam botCell) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) :
    idx (lamHat π lam) y hy.1 = idx lam y hy.1 := by
  set i := idx lam y hy.1 with hi
  have h1 : leftEnd (lamHat π lam) i ≤ y := by
    rw [leftEnd_lamHat]; exact idx_mem lam y hy.1
  have h2 : y < upperEnd (lamHat π lam) i := by
    by_cases hib : i = botCell
    · rw [hib, upperEnd_lamHat_botCell hlt]; exact hy.2
    · rw [upperEnd_lamHat_of_ne hib]
      exact lt_upperEnd_idx lam (mem_Ico_tot_of_mem_cut hy)
  have hsum : y ∈ Set.Ico 0 (∑ i, (lamHat π lam i : ℝ)) := by
    refine ⟨hy.1, ?_⟩
    rw [cut_eq_sum_lamHat hlt]; exact hy.2
  exact idx_eq (lamHat π lam) hsum h1 h2

/-! ## 9. The first return map is the interval exchange of the step -/

/-- **First formula of the return map**: on a point whose image is not the rightmost one, the
return map is `T` itself, with the translation vector of the step. -/
theorem exchHat_eq_exch (hlt : lam (topCell π) < lam botCell) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) (hi : idx lam y hy.1 ≠ topCell π) :
    mkIETFun (lamHat π lam) (piHat π) 0 y = exch π lam y := by
  have hsum : y ∈ Set.Ico 0 (∑ i, (lamHat π lam i : ℝ)) := by
    refine ⟨by linarith [hy.1], ?_⟩
    rw [cut_eq_sum_lamHat hlt]; exact hy.2
  rw [mkIETFun_zero_of_mem hsum, idx_lamHat_eq hlt hy,
    exch_of_mem π lam (mem_Ico_tot_of_mem_cut hy)]
  by_cases hib : idx lam y hy.1 = botCell
  · rw [hib, translationVector_lamHat_botCell hlt]
  · rw [translationVector_lamHat_of_ne hlt (idx lam y hy.1) hib hi]

/-- **Second formula of the return map**: on the rightmost cell the return map is `T²`. -/
theorem exchHat_eq_exch_sq (hlt : lam (topCell π) < lam botCell) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) (hi : idx lam y hy.1 = topCell π) :
    mkIETFun (lamHat π lam) (piHat π) 0 y = exch π lam (exch π lam y) := by
  have hsum : y ∈ Set.Ico 0 (∑ i, (lamHat π lam i : ℝ)) := by
    refine ⟨by linarith [hy.1], ?_⟩
    rw [cut_eq_sum_lamHat hlt]; exact hy.2
  rw [mkIETFun_zero_of_mem hsum, idx_lamHat_eq hlt hy, hi,
    translationVector_lamHat_topCell hlt, exch_exch_eq hlt hy hi,
    exch_of_mem π lam (mem_Ico_tot_of_mem_cut hy), hi]
  ring

/-! ## 10. The first return time -/

/-- The return time to `[0, cut)`: `1` if the first iterate is back, `2` otherwise (it is `2` only
on the rightmost cell). -/
def ret (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (y : ℝ) : ℕ :=
  if exch π lam y ∈ Set.Ico 0 (cut π lam) then 1 else 2

theorem ret_of_mem {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0} {y : ℝ}
    (h : exch π lam y ∈ Set.Ico 0 (cut π lam)) : ret π lam y = 1 := by
  rw [ret]; exact ite_eq_left h

theorem ret_of_not_mem {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0} {y : ℝ}
    (h : exch π lam y ∉ Set.Ico 0 (cut π lam)) : ret π lam y = 2 := by
  rw [ret]; exact ite_eq_right h

/-- **The first return map (source 4.1, first half)**: the first return map of the exchange to the
Rauzy subinterval `[0, cut)` is the exchange with lengths `lamHat` and permutation `piHat`, i.e. the
Rauzy–Veech step. -/
theorem firstReturn_eq (hlt : lam (topCell π) < lam botCell) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) :
    (exch π lam)^[ret π lam y] y = mkIETFun (lamHat π lam) (piHat π) 0 y := by
  by_cases h : idx lam y hy.1 = topCell π
  · have hnot : exch π lam y ∉ Set.Ico 0 (cut π lam) := by
      intro hc
      have hge := (exch_mem_Ico_cut_tot hlt hy h).1
      linarith [hc.2]
    rw [ret_of_not_mem hnot, iterate_two_eq (exch π lam) y, exchHat_eq_exch_sq hlt hy h]
  · rw [ret_of_mem (exch_mem_cut_of_ne hlt hy h), Function.iterate_one,
      exchHat_eq_exch hlt hy h]

/-! ## 11. The tower decomposition -/

/-- The second floor of the tower: the image of the rightmost cell is exactly `[cut, Λ)`. -/
theorem exch_image_topCell (hlt : lam (topCell π) < lam botCell) :
    exch π lam '' Set.Ico (leftEnd lam (topCell π)) (upperEnd lam (topCell π))
      = Set.Ico (cut π lam) (tot lam) := by
  have htv : translationVector π lam (topCell π) = cut π lam - leftEnd lam (topCell π) := by
    rw [translationVector, imageLeft_topCell, cut]
  have hU : upperEnd lam (topCell π) = leftEnd lam (topCell π) + (lam (topCell π) : ℝ) :=
    upperEnd_eq _ _
  have hcut : cut π lam = tot lam - (lam (topCell π) : ℝ) := rfl
  have hle0 : 0 ≤ leftEnd lam (topCell π) := leftEnd_nonneg _ _
  have hlec : leftEnd lam (topCell π) ≤ cut π lam :=
    le_of_lt (lt_of_le_of_lt (leftEnd_le (lam := lam) (i := topCell π) (j := botCell)
      (le_lastPos _)) (leftEnd_botCell_le_cut hlt))
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyl, hyu⟩ := hy
    have hyT : y ∈ Set.Ico 0 (tot lam) :=
      ⟨le_trans (leftEnd_nonneg lam _) hyl, lt_of_lt_of_le hyu (upperEnd_le_total lam _)⟩
    have hidx : idx lam y hyT.1 = topCell π := idx_eq lam hyT hyl hyu
    rw [exch_of_mem π lam hyT, hidx, htv]
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    refine ⟨z - translationVector π lam (topCell π), ⟨?_, ?_⟩, ?_⟩
    · rw [htv]; linarith
    · rw [htv, hU]; linarith
    · have hyT : z - translationVector π lam (topCell π) ∈ Set.Ico 0 (tot lam) := by
        refine ⟨?_, ?_⟩
        · rw [htv]
          linarith [cut_pos hlt]
        · rw [htv]
          linarith
      rw [exch_of_mem π lam hyT]
      have hidx : idx lam (z - translationVector π lam (topCell π)) hyT.1 = topCell π := by
        refine idx_eq lam hyT ?_ ?_
        · rw [htv]; linarith
        · rw [htv, hU]; linarith
      rw [hidx]; ring

/-- **The tower decomposition (two floors)**: the interval is the disjoint union of the base
`[0, cut)` of the first return map and of its first floor `T(cell topCell) = [cut, Λ)`. -/
theorem tower_decomp (hlt : lam (topCell π) < lam botCell) :
    Set.Ico 0 (tot lam) = Set.Ico 0 (cut π lam) ∪
      exch π lam '' Set.Ico (leftEnd lam (topCell π)) (upperEnd lam (topCell π)) := by
  rw [exch_image_topCell hlt]
  ext z
  constructor
  · intro hz
    by_cases hc : z < cut π lam
    · exact Or.inl ⟨hz.1, hc⟩
    · exact Or.inr ⟨le_of_not_gt hc, hz.2⟩
  · rintro (h | h)
    · exact mem_Ico_tot_of_mem_cut h
    · exact ⟨le_trans (le_of_lt (cut_pos hlt)) h.1, h.2⟩

/-- The return time on the base: `2` on the rightmost cell, `1` on the others. -/
def returnB (π : Equiv.Perm (Fin n)) (β : Fin n) : ℕ := if β = topCell π then 2 else 1

theorem returnB_eq_one {π : Equiv.Perm (Fin n)} {β : Fin n} (h : β ≠ topCell π) :
    returnB π β = 1 := by rw [returnB, ite_eq_right h]

theorem returnB_eq_two {π : Equiv.Perm (Fin n)} : returnB π (topCell π) = 2 := by
  rw [returnB, ite_eq_left rfl]

theorem returnB_pos (π : Equiv.Perm (Fin n)) (β : Fin n) : 0 < returnB π β := by
  rw [returnB]; split <;> omega

/-- The cells of the first return map: half-open intervals. -/
def cellHat (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (β : Fin n) : Set ℝ :=
  Set.Ico (leftEnd (lamHat π lam) β) (upperEnd (lamHat π lam) β)

theorem cellHat_topCell {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam botCell) :
    cellHat π lam (topCell π) = Set.Ico (leftEnd lam (topCell π)) (upperEnd lam (topCell π)) := by
  rw [cellHat, upperEnd_lamHat_of_ne (topCell_ne_botCell hlt), leftEnd_lamHat]

theorem upperEnd_lamHat_le_cut {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam botCell) (β : Fin n) :
    upperEnd (lamHat π lam) β ≤ cut π lam := by
  rw [← cut_eq_sum_lamHat hlt]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun j _ _ => (lamHat π lam j).coe_nonneg)

theorem cellHat_subset_cut {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam botCell) (β : Fin n) :
    cellHat π lam β ⊆ Set.Ico 0 (cut π lam) := by
  intro y hy
  refine ⟨le_trans (leftEnd_nonneg _ _) hy.1, lt_of_lt_of_le hy.2 (upperEnd_lamHat_le_cut hlt β)⟩

theorem iUnion_cellHat {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam botCell) :
    Set.iUnion (fun β : Fin n => cellHat π lam β) = Set.Ico 0 (cut π lam) := by
  ext y
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨β, hβ⟩
    exact cellHat_subset_cut hlt β hβ
  · intro hy
    have hsum : y ∈ Set.Ico 0 (∑ i, (lamHat π lam i : ℝ)) := by
      refine ⟨hy.1, ?_⟩
      rw [cut_eq_sum_lamHat hlt]; exact hy.2
    exact ⟨idx (lamHat π lam) y hy.1, idx_mem _ _ _, lt_upperEnd_idx _ hsum⟩

/-- **The tower decomposition (source form)**: `[0, Λ)` is the disjoint union of the floors
`T^j (cell β)` for `β` a cell of the first return map and `j < h β`. -/
theorem tower_decomp_iUnion (hlt : lam (topCell π) < lam botCell) :
    Set.Ico 0 (tot lam) = Set.iUnion (fun β : Fin n =>
      Set.iUnion (fun j : Fin (returnB π β) => (exch π lam)^[(j : ℕ)] '' cellHat π lam β)) := by
  rw [tower_decomp hlt, ← iUnion_cellHat hlt]
  ext z
  constructor
  · rintro (hz | hz)
    · obtain ⟨β, hβ⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion.mpr ⟨β, Set.mem_iUnion.mpr ⟨⟨0, returnB_pos π β⟩, by simpa using hβ⟩⟩
    · refine Set.mem_iUnion.mpr ⟨topCell π, Set.mem_iUnion.mpr
        ⟨⟨1, by rw [returnB_eq_two]; omega⟩, ?_⟩⟩
      simpa [cellHat_topCell hlt] using hz
  · rw [Set.mem_iUnion]
    rintro ⟨β, hz⟩
    rw [Set.mem_iUnion] at hz
    obtain ⟨j, hzj⟩ := hz
    obtain ⟨w, hw, rfl⟩ := hzj
    rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
    · left
      exact Set.mem_iUnion.mpr ⟨β, by rw [h0]; simpa using hw⟩
    · right
      have hβ : β = topCell π := by
        by_contra hne
        have h1 : returnB π β = 1 := returnB_eq_one hne
        have hjlt : (j : ℕ) < 1 := by
          calc (j : ℕ) < returnB π β := j.isLt
            _ = 1 := h1
        omega
      subst hβ
      have hj1 : (j : ℕ) = 1 := by
        have := j.isLt
        have h2 : returnB π (topCell π) = 2 := returnB_eq_two
        omega
      rw [show (j : ℕ) = 1 from hj1, Function.iterate_one]
      rw [cellHat_topCell hlt] at hw
      exact ⟨w, hw, rfl⟩

theorem ret_eq_returnB (hlt : lam (topCell π) < lam botCell) {β : Fin n} {y : ℝ}
    (hy : y ∈ cellHat π lam β) : ret π lam y = returnB π β := by
  have hyc : y ∈ Set.Ico 0 (cut π lam) := cellHat_subset_cut hlt β hy
  have hidxH : idx (lamHat π lam) y hyc.1 = β := by
    refine idx_eq (lamHat π lam) ⟨hyc.1, ?_⟩ hy.1 hy.2
    rw [cut_eq_sum_lamHat hlt]; exact hyc.2
  have hidx : idx lam y hyc.1 = β := by
    rw [← idx_lamHat_eq hlt hyc]; exact hidxH
  by_cases hβ : β = topCell π
  · have hnot : exch π lam y ∉ Set.Ico 0 (cut π lam) := by
      intro hcin
      have hge := (exch_mem_Ico_cut_tot hlt hyc (by rw [hidx, hβ])).1
      linarith [hcin.2]
    rw [ret_of_not_mem hnot, hβ, returnB_eq_two]
  · rw [ret_of_mem (exch_mem_cut_of_ne hlt hyc (by rw [hidx]; exact hβ)), returnB_eq_one hβ]

/-! ## 12. The bridge with `IETDatum₂.rvStep` and `rvMat` -/

/-- The combinatorial data with identity bottom order attached to a permutation: the source's `(π₀,
π₁) = (id, π)`. -/
def toComb (π : Equiv.Perm (Fin n)) : IETDatum₂ (Fin n) n := ⟨π, 1⟩

theorem toComb_last_false (π : Equiv.Perm (Fin n)) :
    (toComb π).last false = botCell := rfl

theorem toComb_last_true (π : Equiv.Perm (Fin n)) :
    (toComb π).last true = topCell π := rfl

theorem rvMat_toComb_false_apply (π : Equiv.Perm (Fin n)) (i j : Fin n) :
    ((toComb π).rvMat false) i j
      = if i = j then 1 else if i = botCell ∧ j = topCell π then 1 else 0 := by
  rw [IETDatum₂.rvMat]
  simp only [toComb_last_false, toComb_last_true, Bool.not_false]

/-! ## 13. Part 2: the tower formula for an invariant measure (level 1)  `T = exch π lam` is a
measurable bijection of `ℝ` (it is `mkIETEquiv lam π 0`), so an invariant measure gives equal mass
to all floors `T^[j] '' A` (`measure_image_iterate`).  The level-one tower decomposition (Section
11) then gives the tower formula  `μ (cell α) = ∑ β, (rvMat false) α β * μ (cell β of the return
map)`.  The multiplicities are `1` for `β = α` and an extra floor over `topCell π` inside the
rightmost cell `botCell`: exactly the first Rauzy–Veech matrix. -/

/-- The exchange as a bijection of `ℝ`. -/
def exchEquiv (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) : Equiv ℝ ℝ := mkIETEquiv lam π 0

theorem coe_exchEquiv (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    ⇑(exchEquiv π lam) = exch π lam := rfl

theorem measurable_exch (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    Measurable (exch π lam) := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ ∑ i, (lam i : ℝ) from by positivity) with h0 | hpos
  · have hid : exch π lam = fun x => x := by
      funext x
      rw [exch, mkIETFun_of_notMem]
      intro hcon
      linarith [h0, hcon.1, hcon.2]
    rw [hid]; exact measurable_id
  · exact (isCutSet_mkIETCuts lam π 0 (le_refl _) hpos).measurable

theorem measurable_exchEquiv (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    Measurable ⇑(exchEquiv π lam) := measurable_exch π lam

theorem measurable_exchEquiv_symm (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    Measurable ⇑(exchEquiv π lam).symm :=
  measurable_exch π.symm (imageLengths π lam)

theorem measurable_exch_symm_iterate (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (j : ℕ) :
    Measurable (⇑(exchEquiv π lam).symm)^[j] :=
  (measurable_exchEquiv_symm π lam).iterate j

theorem exch_apply_iterate_symm (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (j : ℕ) (x : ℝ) :
    (⇑(exchEquiv π lam))^[j] ((⇑(exchEquiv π lam).symm)^[j] x) = x :=
  (Function.LeftInverse.iterate
    (f := ⇑(exchEquiv π lam).symm) (g := ⇑(exchEquiv π lam))
    (fun y => Equiv.apply_symm_apply (exchEquiv π lam) y) j) x

theorem exch_symm_apply_iterate (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (j : ℕ) (x : ℝ) :
    (⇑(exchEquiv π lam).symm)^[j] ((⇑(exchEquiv π lam))^[j] x) = x :=
  (Function.LeftInverse.iterate
    (f := ⇑(exchEquiv π lam)) (g := ⇑(exchEquiv π lam).symm)
    (fun y => Equiv.symm_apply_apply (exchEquiv π lam) y) j) x

theorem map_exch_symm (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (μ : Measure ℝ)
    (hμ : μ.map (exch π lam) = μ) : μ.map (⇑(exchEquiv π lam).symm) = μ := by
  have hμ' : μ.map (⇑(exchEquiv π lam)) = μ := hμ
  have h := congrArg (fun ν : Measure ℝ => ν.map (⇑(exchEquiv π lam).symm)) hμ'
  rw [Measure.map_map (measurable_exchEquiv_symm π lam) (measurable_exchEquiv π lam)] at h
  rw [show ⇑(exchEquiv π lam).symm ∘ ⇑(exchEquiv π lam) = id from
    funext (Equiv.symm_apply_apply (exchEquiv π lam))] at h
  rw [Measure.map_id] at h
  exact h.symm

theorem map_exch_symm_iterate (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (μ : Measure ℝ)
    (hμ : μ.map (exch π lam) = μ) (j : ℕ) : μ.map (⇑(exchEquiv π lam).symm)^[j] = μ := by
  induction j with
  | zero => simp
  | succ k ih =>
    have hcomp : (⇑(exchEquiv π lam).symm)^[k + 1]
        = ⇑(exchEquiv π lam).symm ∘ (⇑(exchEquiv π lam).symm)^[k] := by
      funext x
      rw [Function.iterate_succ_apply']
      rfl
    rw [hcomp, ← Measure.map_map (measurable_exchEquiv_symm π lam)
      (measurable_exch_symm_iterate π lam k), ih, map_exch_symm π lam μ hμ]

/-- **All floors of a tower have the same mass**, for an invariant measure. -/
theorem measure_image_iterate (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (μ : Measure ℝ)
    (hμ : μ.map (exch π lam) = μ) (A : Set ℝ) (hA : MeasurableSet A) (j : ℕ) :
    μ ((exch π lam)^[j] '' A) = μ A := by
  have hpre : (exch π lam)^[j] '' A = ((⇑(exchEquiv π lam).symm)^[j]) ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [Set.mem_preimage]
      simp only [← coe_exchEquiv]
      rw [exch_symm_apply_iterate π lam j a]
      exact ha
    · intro hx
      exact ⟨_, hx, exch_apply_iterate_symm π lam j x⟩
  rw [hpre, ← Measure.map_apply (measurable_exch_symm_iterate π lam j) hA,
    map_exch_symm_iterate π lam μ hμ j]

/-- **A floor has the same mass as the base**: `μ (T '' A) = μ A`. -/
theorem measure_image_exch (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (μ : Measure ℝ)
    (hμ : μ.map (exch π lam) = μ) (A : Set ℝ) (hA : MeasurableSet A) :
    μ (exch π lam '' A) = μ A := by
  have h := measure_image_iterate π lam μ hμ A hA 1
  rwa [Function.iterate_one] at h

/-! ### The multiplicity of the level-one tower -/

/-- The multiplicity of the floor over `β` inside the cell `α`, in the level-one tower: `1` if
`β = α`, plus `1` if `α` is the rightmost cell and `β` is the cell whose image is the rightmost
image cell.  This is the Rauzy–Veech matrix `rvMat false`. -/
def multOne (π : Equiv.Perm (Fin n)) (α β : Fin n) : ℕ :=
  if β = α then 1 else if β = topCell π ∧ α = botCell then 1 else 0

theorem measurableSet_cellHat (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (β : Fin n) :
    MeasurableSet (cellHat π lam β) := measurableSet_Ico

/-- **The tower formula at level one**, in the form of a two-term identity: the mass of a cell of
`T` is the mass of the cell of the first return map above it, plus — for the rightmost cell — the
mass of the cell over `topCell π` (the second floor). -/
theorem tower_formula_one_step (hlt : lam (topCell π) < lam botCell) (μ : Measure ℝ)
    (hμ : μ.map (exch π lam) = μ) (α : Fin n) :
    μ (Set.Ico (leftEnd lam α) (upperEnd lam α))
      = μ (cellHat π lam α) + (if α = botCell then μ (cellHat π lam (topCell π)) else 0) := by
  have hmeas := measurableSet_cellHat π lam
  by_cases hb : α = botCell
  · subst hb
    rw [ite_eq_left rfl]
    have hsplit : Set.Ico (leftEnd lam botCell) (upperEnd lam botCell)
        = cellHat π lam botCell ∪ exch π lam '' cellHat π lam (topCell π) := by
      rw [upperEnd_botCell, cellHat_topCell hlt, exch_image_topCell hlt, cellHat,
        upperEnd_lamHat_botCell hlt, leftEnd_lamHat]
      exact (Set.Ico_union_Ico_eq_Ico (le_of_lt (leftEnd_botCell_le_cut hlt))
        (cut_le_tot π lam)).symm
    have hd : Disjoint (cellHat π lam botCell) (exch π lam '' cellHat π lam (topCell π)) := by
      rw [cellHat, upperEnd_lamHat_botCell hlt, leftEnd_lamHat, cellHat_topCell hlt,
        exch_image_topCell hlt, Set.Ico_disjoint_Ico]
      exact le_trans (min_le_left _ _) (le_max_right _ _)
    have hm : MeasurableSet (exch π lam '' cellHat π lam (topCell π)) := by
      rw [cellHat_topCell hlt, exch_image_topCell hlt]
      exact measurableSet_Ico
    rw [hsplit, measure_union hd hm, measure_image_exch π lam μ hμ _ (hmeas (topCell π))]
  · rw [ite_eq_right hb, add_zero]
    congr 1
    rw [cellHat, upperEnd_lamHat_of_ne hb, leftEnd_lamHat]

end

end Tower

end
