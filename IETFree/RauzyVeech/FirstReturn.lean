/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.Step
import Mathlib.Tactic.Positivity.Finset

/-!
# The first return map of an interval exchange into a Rauzy subinterval

Setup (the "Rauzy situation", type `false` of `IETDatum₂.rvStep`): `T = mkIETFun lam π 0` is the
exchange on `[0, Λ)`, `Λ = ∑ lam`, with cells indexed by bottom position.  `topCell π = π⁻¹ (last)`
is the cell whose *image* is the rightmost image cell, `lastPos n = last` is the rightmost domain
cell.  The hypothesis is `λ (topCell π) < λ (lastPos n)` (the image-rightmost cell is the shorter of
the two rightmost cells), and the induced subinterval is `[0, c)` with `c = Λ - λ (topCell
 π)`. Main results:
* `ret_of_mem`, `ret_of_not_mem`: the first return time `ret` of `[0, c)` is `1` on the
  subinterval and `2` off it (`ret y = 1` if `T y ∈ [0,c)`, `= 2` otherwise);
* `exchHat_eq_mkIETFun` / `exchHat_eq_mkIETFun_sq`: the first return map is `T` on the
cells
  whose image is not the rightmost one, and `T²` on the cell `topCell π`;
* `firstReturn_eq`: the first return map is again an interval exchange, with lengths `lamHat`
  (`λ` with the top-rightmost length removed from the bottom-rightmost cell) and permutation
  `piHat = insertEquiv (π lastPos n) ∘ π`, which is exactly the Rauzy–Veech step;
* `rvMat_ofPerm_false_apply`: the multiplicity matrix of the return is `rvMat false` — one
  floor over `α`, plus a second one over `topCell π` inside `lastPos n`;
* `tower_decomp`, `tower_decomp_iUnion`: the tower decomposition
  `[0, Λ) = ⨆ β, ⨆ j < h β, T^[j] (cell β)`, with return times `h β ∈ {1, 2}`
  (`returnB_eq_one`, `returnB_eq_two`);
* `tower_formula_one_step`: the tower formula at level one for an invariant measure.
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

namespace IntervalExchange.RauzyVeech

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## 1. Notation and elementary facts -/

theorem le_lastPos (i : Fin n) : i ≤ lastPos n := by
  rw [Fin.le_def, lastPos_val]
  have := i.isLt
  omega

theorem lt_lastPos_iff {i : Fin n} : i < lastPos n ↔ i.val + 1 < n := by
  rw [Fin.lt_def, lastPos_val]
  have := i.isLt
  omega

/-- The cell whose image is the rightmost image cell (`π⁻¹ (last)`). -/
def topCell (π : Equiv.Perm (Fin n)) : Fin n := π.symm (lastPos n)

@[simp] theorem topCell_apply (π : Equiv.Perm (Fin n)) :
    π (topCell π) = lastPos n := π.apply_symm_apply _

theorem topCell_inj {π : Equiv.Perm (Fin n)} {j : Fin n} (h : π j = lastPos n) :
    j = topCell π := by
  apply π.injective
  rw [topCell_apply, h]

theorem topCell_ne_lastPos {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam (lastPos n)) : topCell π ≠ (lastPos n) :=
  fun h => absurd hlt (by rw [h]; exact lt_irrefl _)

omit [NeZero n] in
theorem single_le_totalLength (lam : Fin n → ℝ≥0) (i : Fin n) : (lam i : ℝ) ≤ totalLength lam :=
  Finset.single_le_sum (f := fun i => (lam i : ℝ)) (fun i _ => (lam i).coe_nonneg)
    (Finset.mem_univ i)

theorem filter_lt_lastPos (π : Equiv.Perm (Fin n)) :
    Finset.univ.filter (fun j => π j < lastPos n) = Finset.univ.erase (topCell π) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · intro hj
    refine ⟨?_, trivial⟩
    intro hje
    rw [hje, topCell_apply] at hj
    exact absurd hj (lt_irrefl _)
  · intro hj
    -- `topCell` unfolded: stated so that `lt_of_le_of_ne` closes the strict form
    show π j < lastPos n
    exact lt_of_le_of_ne (le_lastPos _) (fun hh => hj.1 (topCell_inj hh))

/-- The image of the cell `topCell π` starts at `Λ - λ (topCell π)`. -/
theorem imageLeft_topCell (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    imageLeft π lam (topCell π) = totalLength lam - (lam (topCell π) : ℝ) := by
  have hset : Finset.univ.filter (fun j => π j < π (topCell π))
      = Finset.univ.erase (topCell π) := by
    rw [topCell_apply]; exact filter_lt_lastPos π
  rw [imageLeft, hset, totalLength,
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
theorem imageUpper_le_totalLength (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) {i : Fin n}
    (hi : i ≠ topCell π) : imageUpper π lam i ≤ totalLength lam - (lam (topCell π) : ℝ) := by
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
      = totalLength lam := by
    rw [totalLength, Finset.sum_erase_add _ (fun i => (lam i : ℝ)) (Finset.mem_univ _)]
  linarith

/-! ## 2. The new length vector and the new permutation -/

/-- The new length vector: the rightmost domain cell loses the length of the rightmost image cell.
It is `lam` in bottom order (for a step of type `false` the bottom order is unchanged). -/
def lamHat (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) : Fin n → ℝ≥0 :=
  fun i => if i = (lastPos n) then lam i - lam (topCell π) else lam i

/-- The new permutation of the step: the cell `topCell π` is inserted just after `π lastPos n`. -/
def piHat (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  π.trans (insertEquiv (π (lastPos n)))

theorem piHat_apply (π : Equiv.Perm (Fin n)) (j : Fin n) :
    piHat π j = insertEquiv (π (lastPos n)) (π j) := (rfl)

theorem lastPos_ne_lastPos_of_lt {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam (lastPos n)) : π (lastPos n) ≠ lastPos n := by
  intro h
  exact topCell_ne_lastPos hlt (topCell_inj h).symm

theorem pivot_succ_lt {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam (lastPos n)) : (π (lastPos n)).val + 1 < n := by
  have h1 : π (lastPos n) < lastPos n :=
    lt_of_le_of_ne (le_lastPos _) (lastPos_ne_lastPos_of_lt hlt)
  rwa [lt_lastPos_iff] at h1

theorem piHat_topCell_val {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam (lastPos n)) :
    (piHat π (topCell π)).val = (π (lastPos n)).val + 1 := by
  rw [piHat_apply, topCell_apply, insertEquiv_lastPos (pivot_succ_lt hlt)]

/-! ## 3. The new length vector: sums and endpoints -/

theorem lamHat_coe {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam (lastPos n)) (j : Fin n) :
    (lamHat π lam j : ℝ) = (lam j : ℝ) - (if j = lastPos n then (lam (topCell π) : ℝ) else 0) := by
  rw [lamHat]
  by_cases hj : j = (lastPos n)
  · subst hj
    rw [ite_eq_left rfl, ite_eq_left rfl, NNReal.coe_sub (le_of_lt hlt)]
  · rw [ite_eq_right hj, ite_eq_right hj, sub_zero]

theorem lamHat_of_ne {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0} {j : Fin n}
    (hj : j ≠ (lastPos n)) : lamHat π lam j = lam j := by
  rw [lamHat, ite_eq_right hj]

theorem lamHat_lastPos {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam (lastPos n)) :
    (lamHat π lam (lastPos n) : ℝ) = (lam (lastPos n) : ℝ) - (lam (topCell π) : ℝ) := by
  rw [lamHat, ite_eq_left rfl, NNReal.coe_sub (le_of_lt hlt)]

theorem sum_filter_lamHat {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam (lastPos n)) (S : Finset (Fin n)) :
    ∑ j ∈ S, (lamHat π lam j : ℝ)
      = ∑ j ∈ S, (lam j : ℝ) - (if (lastPos n) ∈ S then (lam (topCell π) : ℝ) else 0) := by
  have hterm (j) (hj : j ∈ S) : (lamHat π lam j : ℝ)
      = (lam j : ℝ) - (if j = (lastPos n) then (lam (topCell π) : ℝ) else 0) := lamHat_coe hlt j
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' S (lastPos n) (fun _ => (lam (topCell π) : ℝ))]

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
    (hlt : lam (topCell π) < lam (lastPos n)) :
    ∑ i, (lamHat π lam i : ℝ) = totalLength lam - (lam (topCell π) : ℝ) := by
  have h := sum_filter_lamHat (π := π) hlt Finset.univ
  simpa only [totalLength, Finset.mem_univ, ite_true] using h

/-- The cut point `c = Λ - λ (topCell π)`. -/
def cut (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) : ℝ := totalLength lam - (lam (topCell π) : ℝ)

theorem cut_eq_sum_lamHat {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam (lastPos n)) :
    ∑ i, (lamHat π lam i : ℝ) = cut π lam :=
  sum_lamHat hlt

theorem filter_lt_lastPos_eq_erase :
    Finset.univ.filter (fun j : Fin n => j < lastPos n) = Finset.univ.erase (lastPos n) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · intro hj
    exact ⟨ne_of_lt hj, trivial⟩
  · intro hj
    exact lt_of_le_of_ne (le_lastPos j) hj.1

theorem leftEnd_lastPos (lam : Fin n → ℝ≥0) :
    leftEnd lam (lastPos n) = totalLength lam - (lam (lastPos n) : ℝ) := by
  rw [leftEnd, filter_lt_lastPos_eq_erase, totalLength,
    ← Finset.add_sum_erase _ (fun i => (lam i : ℝ)) (Finset.mem_univ _)]
  ring

/-- The right end of the cell `lastPos n` is the total length. -/
theorem upperEnd_lastPos (lam : Fin n → ℝ≥0) : upperEnd lam (lastPos n) = totalLength lam := by
  rw [upperEnd_eq, leftEnd_lastPos]
  ring

/-! ## 4. Order properties of the insertion -/

/-- The insertion of the position `p` preserves the order of the positions that are not last, and
moves the last position to `p + 1`.  This is the combinatorial core of the step: it compares the
images of two cells that both avoid `topCell`. -/
theorem insertEquiv_lt_iff {p : Fin n} (hp : p.val + 1 < n) {k k' : Fin n}
    (hk : k ≠ lastPos n) (hk' : k' ≠ lastPos n) :
    insertEquiv p k' < insertEquiv p k ↔ k' < k := by
  by_cases h2 : k'.val ≤ p.val
  · have hik' : insertEquiv p k' = k' := insertEquiv_apply_le h2
    by_cases h1 : k.val ≤ p.val
    · have hik : insertEquiv p k = k := insertEquiv_apply_le h1
      rw [hik', hik]
    · have h1' : p.val < k.val := by omega
      have hikv : ((insertEquiv p) k).val = k.val + 1 :=
        insertEquiv_apply_gt hp h1' hk
      rw [hik', Fin.lt_def, hikv, Fin.lt_def]
      omega
  · have h2' : p.val < k'.val := by omega
    have hik'v : ((insertEquiv p) k').val = k'.val + 1 :=
      insertEquiv_apply_gt hp h2' hk'
    by_cases h1 : k.val ≤ p.val
    · have hik : insertEquiv p k = k := insertEquiv_apply_le h1
      rw [hik, Fin.lt_def, hik'v, Fin.lt_def]
      omega
    · have h1' : p.val < k.val := by omega
      have hikv : ((insertEquiv p) k).val = k.val + 1 :=
        insertEquiv_apply_gt hp h1' hk
      rw [Fin.lt_def, hik'v, hikv, Fin.lt_def]
      omega

/-! ## 5. The images of the cells after the step -/

variable {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}

theorem piHat_apply_gt (hlt : lam (topCell π) < lam (lastPos n)) {i : Fin n}
    (h : (π (lastPos n)).val < (π i).val) (hit : i ≠ topCell π) :
    (piHat π i).val = (π i).val + 1 :=
  insertEquiv_apply_gt (pivot_succ_lt hlt) h (fun hh => hit (topCell_inj hh))

theorem piHat_apply_le {i : Fin n} (h : (π i).val ≤ (π (lastPos n)).val) : piHat π i = π i :=
  insertEquiv_apply_le h

/-- **The images of all the cells except the rightmost one are unchanged** by the step: the cut only
moves the rightmost image cell, which is `topCell π`'s image, past the image of `lastPos n`. -/
theorem imageLeft_lamHat_of_ne (hlt : lam (topCell π) < lam (lastPos n)) (i : Fin n)
    (hit : i ≠ topCell π) :
    imageLeft (piHat π) (lamHat π lam) i = imageLeft π lam i := by
  have hpv := pivot_succ_lt hlt
  have hit' : π i ≠ lastPos n := fun h => hit (topCell_inj h)
  have hkey (j : Fin n) (hj : j ≠ topCell π) : (piHat π j < piHat π i ↔ π j < π i) := by
    have hj' : π j ≠ lastPos n := fun h => hj (topCell_inj h)
    rw [piHat_apply, piHat_apply]
    exact insertEquiv_lt_iff hpv hit' hj'
  by_cases hcase : (π i).val ≤ (π (lastPos n)).val
  · -- case 1: the image of `i` ends before the image of `lastPos n`
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
    have hnotmem : (lastPos n) ∉ Finset.univ.filter (fun j => π j < π i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      exact hcase
    have hmain :
        ∑ j ∈ Finset.univ.filter (fun j => piHat π j < piHat π i), (lamHat π lam j : ℝ)
          = ∑ j ∈ Finset.univ.filter (fun j => π j < π i), (lam j : ℝ) := by
      rw [hS, sum_filter_lamHat hlt, ite_eq_right hnotmem, sub_zero]
    exact hmain
  · -- case 2: the image of `i` lies strictly after the image of `lastPos n`
    have hcase' : (π (lastPos n)).val < (π i).val := by omega
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
    have hmem : (lastPos n) ∈ Finset.univ.filter (fun j => π j < π i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      -- what `Finset.mem_filter` leaves; stated so that `Fin.lt_def` applies
      show π (lastPos n) < π i
      rw [Fin.lt_def]; exact hcase'
    have hnotmem : topCell π ∉ Finset.univ.filter (fun j => π j < π i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      rw [topCell_apply]; exact le_lastPos _
    have hmain :
        ∑ j ∈ Finset.univ.filter (fun j => piHat π j < piHat π i), (lamHat π lam j : ℝ)
          = ∑ j ∈ Finset.univ.filter (fun j => π j < π i), (lam j : ℝ) := by
      rw [hS, Finset.sum_insert hnotmem, sum_filter_lamHat hlt, ite_eq_left hmem,
        lamHat_of_ne (topCell_ne_lastPos hlt)]
      ring
    exact hmain

/-- **The image of the rightmost cell** after the step: the old image of `lastPos n`, plus a new
cell of length `λ (lastPos n) - λ (topCell π)` inserted just after it. -/
theorem imageLeft_lamHat_topCell (hlt : lam (topCell π) < lam (lastPos n)) :
    imageLeft (piHat π) (lamHat π lam) (topCell π)
      = imageLeft π lam (lastPos n) + ((lam (lastPos n) : ℝ) - (lam (topCell π) : ℝ)) := by
  have hpv := pivot_succ_lt hlt
  have hSp : Finset.univ.filter (fun j => piHat π j < piHat π (topCell π))
      = insert (lastPos n) (Finset.univ.filter (fun j => π j < π (lastPos n))) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hj : j = topCell π
    · subst hj
      have h1 : ¬ (piHat π (topCell π) < piHat π (topCell π)) := lt_irrefl _
      have h2 : ¬ (π (topCell π) < π (lastPos n)) := by
        rw [topCell_apply]; exact not_lt.mpr (le_lastPos _)
      refine ⟨fun h => absurd h h1, ?_⟩
      rintro (hb | hlt')
      · exact absurd hb (topCell_ne_lastPos hlt)
      · exact absurd hlt' h2
    · have hj' : π j ≠ lastPos n := fun h => hj (topCell_inj h)
      have hiff : piHat π j < piHat π (topCell π) ↔ (π j).val ≤ (π (lastPos n)).val := by
        rw [Fin.lt_def, piHat_topCell_val (π := π) (lam := lam) hlt]
        by_cases hc : (π j).val ≤ (π (lastPos n)).val
        · have hv : (piHat π j).val = (π j).val := by rw [piHat_apply_le hc]
          rw [hv]
          constructor <;> intro h <;> omega
        · have hc' : (π (lastPos n)).val < (π j).val := by omega
          rw [piHat_apply_gt hlt hc' hj]
          constructor <;> intro h <;> omega
      rw [hiff]
      exact ⟨fun h => (eq_or_lt_of_le h).elim (fun h1 => Or.inl (π.injective (Fin.ext h1)))
          (fun h1 => Or.inr (by rw [Fin.lt_def]; exact h1)),
        fun h => h.elim (fun hb => hb ▸ le_rfl) le_of_lt⟩
  have hnotmem : (lastPos n) ∉ Finset.univ.filter (fun j => π j < π (lastPos n)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_irrefl _
  have hnotmem' : topCell π ∉ Finset.univ.filter (fun j => π j < π (lastPos n)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    rw [topCell_apply]; exact le_lastPos _
  have hmain :
      ∑ j ∈ Finset.univ.filter (fun j => piHat π j < piHat π (topCell π)), (lamHat π lam j : ℝ)
        = ∑ j ∈ Finset.univ.filter (fun j => π j < π (lastPos n)), (lam j : ℝ)
          + ((lam (lastPos n) : ℝ) - (lam (topCell π) : ℝ)) := by
    rw [hSp, Finset.sum_insert hnotmem, sum_filter_lamHat hlt, ite_eq_right hnotmem, sub_zero,
      lamHat_lastPos hlt]
    ring
  exact hmain

/-! ## 6. The translation vectors of the step -/

theorem translationVector_lamHat_of_ne (hlt : lam (topCell π) < lam (lastPos n)) (i : Fin n)
    (hit : i ≠ topCell π) :
    translationVector (piHat π) (lamHat π lam) i = translationVector π lam i := by
  unfold translationVector
  rw [imageLeft_lamHat_of_ne hlt i hit, leftEnd_lamHat]

/-- The translation on the rightmost cell: the return time is `2` there, and the two
translations add up. -/
theorem translationVector_lamHat_topCell (hlt : lam (topCell π) < lam (lastPos n)) :
    translationVector (piHat π) (lamHat π lam) (topCell π)
      = translationVector π lam (topCell π) + translationVector π lam (lastPos n) := by
  unfold translationVector
  rw [imageLeft_lamHat_topCell hlt, leftEnd_lamHat, imageLeft_topCell, leftEnd_lastPos]
  ring

/-! ## 7. The dynamics of the first return to `[0, cut)` -/

theorem cut_le_totalLength (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    cut π lam ≤ totalLength lam := by
  rw [cut]
  exact sub_le_self _ (by positivity)

theorem mem_Ico_totalLength_of_mem_cut {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0} {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) : y ∈ Set.Ico 0 (totalLength lam) :=
  ⟨hy.1, lt_of_lt_of_le hy.2 (cut_le_totalLength π lam)⟩

/-- The exchange with base point `0`, written with `idx` at `y` itself. -/
theorem mkIETFun_zero_of_mem {π' : Equiv.Perm (Fin n)} {lam' : Fin n → ℝ≥0} {y : ℝ}
    (hy : y ∈ Set.Ico 0 (∑ i, (lam' i : ℝ))) :
    mkIETFun lam' π' 0 y = y + translationVector π' lam' (idx lam' y hy.1) := by
  have h := mkIETFun_of_mem lam' π' 0 (x := y) (by simpa using hy)
  simpa using h

/-- A point of the cut interval lies in the cell given by `idx`. -/
theorem idx_cut {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0} {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) :
    leftEnd lam (idx lam y hy.1) ≤ y ∧ y < upperEnd lam (idx lam y hy.1) :=
  ⟨idx_mem lam y hy.1, lt_upperEnd_idx lam (mem_Ico_totalLength_of_mem_cut hy)⟩

/-- The cut is positive. -/
theorem cut_pos {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam (lastPos n)) : 0 < cut π lam := by
  have h1 := NNReal.coe_lt_coe.mpr hlt
  have h2 := single_le_totalLength lam (lastPos n)
  rw [cut]; linarith

/-- The rightmost domain cell starts before the cut. -/
theorem leftEnd_lastPos_le_cut {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam (lastPos n)) : leftEnd lam (lastPos n) < cut π lam := by
  rw [leftEnd_lastPos, cut]
  have h := NNReal.coe_lt_coe.mpr hlt
  linarith

/-- The image of a cell other than the rightmost one ends before the cut. -/
theorem imageUpper_le_cut (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) {i : Fin n}
    (hi : i ≠ topCell π) : imageUpper π lam i ≤ cut π lam :=
  imageUpper_le_totalLength π lam hi

/-- **A point outside the rightmost cell returns to `[0, cut)` in one step.** -/
theorem mkIETFun_mem_cut_of_ne {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) (hi : idx lam y hy.1 ≠ topCell π) :
    mkIETFun lam π 0 y ∈ Set.Ico 0 (cut π lam) := by
  have hyT := mem_Ico_totalLength_of_mem_cut hy
  rw [mkIETFun_zero_of_mem hyT]
  obtain ⟨h1, h2⟩ := idx_cut hy
  have hupper : imageUpper π lam (idx lam y hy.1) ≤ cut π lam := imageUpper_le_cut π lam hi
  have htv : translationVector π lam (idx lam y hy.1)
      = imageLeft π lam (idx lam y hy.1) - leftEnd lam (idx lam y hy.1) := (rfl)
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
theorem mkIETFun_mem_Ico_cut_totalLength {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) (hi : idx lam y hy.1 = topCell π) :
    mkIETFun lam π 0 y ∈ Set.Ico (cut π lam) (totalLength lam) := by
  have hyT := mem_Ico_totalLength_of_mem_cut hy
  rw [mkIETFun_zero_of_mem hyT, hi]
  have hleft : cut π lam = totalLength lam - (lam (topCell π) : ℝ) := (rfl)
  have hspec := imageLeft_topCell π lam
  have h1 := idx_mem lam y hy.1
  rw [hi] at h1
  have h2 : y < leftEnd lam (topCell π) + (lam (topCell π) : ℝ) := by
    have h := lt_upperEnd_idx lam hyT
    rwa [upperEnd_eq, hi] at h
  have htv : translationVector π lam (topCell π)
      = imageLeft π lam (topCell π) - leftEnd lam (topCell π) := (rfl)
  constructor
  · rw [htv, hspec, hleft]; linarith
  · rw [htv, hspec]; linarith

/-- On the rightmost cell the image lands in the rightmost *domain* cell. -/
theorem idx_mkIETFun_of_idx_topCell (hlt : lam (topCell π) < lam (lastPos n)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) (hi : idx lam y hy.1 = topCell π) :
    idx lam (mkIETFun lam π 0 y)
      (le_trans (le_of_lt (cut_pos hlt))
        (mkIETFun_mem_Ico_cut_totalLength hy hi).1) = (lastPos n) := by
  obtain ⟨h1, h2⟩ := mkIETFun_mem_Ico_cut_totalLength hy hi
  refine idx_eq lam ⟨le_trans (le_of_lt (cut_pos hlt)) h1, h2⟩ ?_ ?_
  · exact le_trans (le_of_lt (leftEnd_lastPos_le_cut hlt)) h1
  · rw [upperEnd_lastPos]; exact h2

/-- **The second iterate of a point of the rightmost cell.** -/
theorem mkIETFun_mkIETFun_eq (hlt : lam (topCell π) < lam (lastPos n)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) (hi : idx lam y hy.1 = topCell π) :
    mkIETFun lam π 0 (mkIETFun lam π 0 y)
      = mkIETFun lam π 0 y + translationVector π lam (lastPos n) := by
  have hT := mkIETFun_mem_Ico_cut_totalLength hy hi
  have hidx := idx_mkIETFun_of_idx_topCell hlt hy hi
  have hT' : mkIETFun lam π 0 y ∈ Set.Ico 0 (totalLength lam) :=
    ⟨le_trans (le_of_lt (cut_pos hlt)) hT.1, hT.2⟩
  rw [mkIETFun_zero_of_mem hT', hidx]

theorem iterate_two_eq (f : ℝ → ℝ) (y : ℝ) : f^[2] y = f (f y) := (rfl)

/-! ## 8. Endpoints of the new cells -/

theorem upperEnd_lamHat_of_ne {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0} {i : Fin n}
    (hi : i ≠ (lastPos n)) : upperEnd (lamHat π lam) i = upperEnd lam i := by
  rw [upperEnd_eq, upperEnd_eq, leftEnd_lamHat, lamHat_of_ne hi]

theorem upperEnd_lamHat_lastPos {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam (lastPos n)) :
    upperEnd (lamHat π lam) (lastPos n) = cut π lam := by
  rw [upperEnd_eq, leftEnd_lamHat, leftEnd_lastPos, lamHat_lastPos hlt, cut]
  ring

/-- The `idx` of `y` does not change when the length of the rightmost cell is reduced, as long as
`y` lies in the cut interval. -/
theorem idx_lamHat_eq (hlt : lam (topCell π) < lam (lastPos n)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) :
    idx (lamHat π lam) y hy.1 = idx lam y hy.1 := by
  set i := idx lam y hy.1 with hi
  have h1 : leftEnd (lamHat π lam) i ≤ y := by
    rw [leftEnd_lamHat]; exact idx_mem lam y hy.1
  have h2 : y < upperEnd (lamHat π lam) i := by
    by_cases hib : i = (lastPos n)
    · rw [hib, upperEnd_lamHat_lastPos hlt]; exact hy.2
    · rw [upperEnd_lamHat_of_ne hib]
      exact lt_upperEnd_idx lam (mem_Ico_totalLength_of_mem_cut hy)
  have hsum : y ∈ Set.Ico 0 (∑ i, (lamHat π lam i : ℝ)) := by
    refine ⟨hy.1, ?_⟩
    rw [cut_eq_sum_lamHat hlt]; exact hy.2
  exact idx_eq (lamHat π lam) hsum h1 h2

/-! ## 9. The first return map is the interval exchange of the step -/

/-- **First formula of the return map**: on a point whose image is not the rightmost one, the
return map is `T` itself, with the translation vector of the step. -/
theorem exchHat_eq_mkIETFun (hlt : lam (topCell π) < lam (lastPos n)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) (hi : idx lam y hy.1 ≠ topCell π) :
    mkIETFun (lamHat π lam) (piHat π) 0 y = mkIETFun lam π 0 y := by
  have hsum : y ∈ Set.Ico 0 (∑ i, (lamHat π lam i : ℝ)) := by
    refine ⟨by linarith [hy.1], ?_⟩
    rw [cut_eq_sum_lamHat hlt]; exact hy.2
  rw [mkIETFun_zero_of_mem hsum, idx_lamHat_eq hlt hy,
    mkIETFun_zero_of_mem (mem_Ico_totalLength_of_mem_cut hy)]
  rw [translationVector_lamHat_of_ne hlt (idx lam y hy.1) hi]

/-- **Second formula of the return map**: on the rightmost cell the return map is `T²`. -/
theorem exchHat_eq_mkIETFun_sq (hlt : lam (topCell π) < lam (lastPos n)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) (hi : idx lam y hy.1 = topCell π) :
    mkIETFun (lamHat π lam) (piHat π) 0 y = mkIETFun lam π 0 (mkIETFun lam π 0 y) := by
  have hsum : y ∈ Set.Ico 0 (∑ i, (lamHat π lam i : ℝ)) := by
    refine ⟨by linarith [hy.1], ?_⟩
    rw [cut_eq_sum_lamHat hlt]; exact hy.2
  rw [mkIETFun_zero_of_mem hsum, idx_lamHat_eq hlt hy, hi,
    translationVector_lamHat_topCell hlt, mkIETFun_mkIETFun_eq hlt hy hi,
    mkIETFun_zero_of_mem (mem_Ico_totalLength_of_mem_cut hy), hi]
  ring

/-! ## 10. The first return time -/

/-- The return time to `[0, cut)`: `1` if the first iterate is back, `2` otherwise (it is `2` only
on the rightmost cell). -/
def ret (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (y : ℝ) : ℕ :=
  if mkIETFun lam π 0 y ∈ Set.Ico 0 (cut π lam) then 1 else 2

theorem ret_of_mem {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0} {y : ℝ}
    (h : mkIETFun lam π 0 y ∈ Set.Ico 0 (cut π lam)) : ret π lam y = 1 := by
  rw [ret]; exact ite_eq_left h

theorem ret_of_not_mem {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0} {y : ℝ}
    (h : mkIETFun lam π 0 y ∉ Set.Ico 0 (cut π lam)) : ret π lam y = 2 := by
  rw [ret]; exact ite_eq_right h

/-- **The first return map (source 4.1, first half)**: the first return map of the exchange to the
Rauzy subinterval `[0, cut)` is the exchange with lengths `lamHat` and permutation `piHat`, i.e. the
Rauzy–Veech step. -/
theorem firstReturn_eq (hlt : lam (topCell π) < lam (lastPos n)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cut π lam)) :
    (mkIETFun lam π 0)^[ret π lam y] y = mkIETFun (lamHat π lam) (piHat π) 0 y := by
  by_cases h : idx lam y hy.1 = topCell π
  · have hnot : mkIETFun lam π 0 y ∉ Set.Ico 0 (cut π lam) := by
      intro hc
      have hge := (mkIETFun_mem_Ico_cut_totalLength hy h).1
      linarith [hc.2]
    rw [ret_of_not_mem hnot, iterate_two_eq (mkIETFun lam π 0) y, exchHat_eq_mkIETFun_sq hlt hy h]
  · rw [ret_of_mem (mkIETFun_mem_cut_of_ne hy h), Function.iterate_one,
      exchHat_eq_mkIETFun hlt hy h]

/-! ## 11. The tower decomposition -/

/-- The second floor of the tower: the image of the rightmost cell is exactly `[cut, Λ)`. -/
theorem mkIETFun_image_topCell (hlt : lam (topCell π) < lam (lastPos n)) :
    mkIETFun lam π 0 '' Set.Ico (leftEnd lam (topCell π)) (upperEnd lam (topCell π))
      = Set.Ico (cut π lam) (totalLength lam) := by
  have htv : translationVector π lam (topCell π) = cut π lam - leftEnd lam (topCell π) := by
    unfold translationVector
    rw [imageLeft_topCell, cut]
  have hU : upperEnd lam (topCell π) = leftEnd lam (topCell π) + (lam (topCell π) : ℝ) :=
    upperEnd_eq _ _
  have hcut : cut π lam = totalLength lam - (lam (topCell π) : ℝ) := (rfl)
  have hle0 : 0 ≤ leftEnd lam (topCell π) := leftEnd_nonneg _ _
  have hlec : leftEnd lam (topCell π) ≤ cut π lam :=
    le_of_lt (lt_of_le_of_lt (leftEnd_mono (lam := lam) (i := topCell π) (j := (lastPos n))
      (le_lastPos _)) (leftEnd_lastPos_le_cut hlt))
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyl, hyu⟩ := hy
    have hyT : y ∈ Set.Ico 0 (totalLength lam) :=
      ⟨le_trans (leftEnd_nonneg lam _) hyl, lt_of_lt_of_le hyu (upperEnd_le_total lam _)⟩
    have hidx : idx lam y hyT.1 = topCell π := idx_eq lam hyT hyl hyu
    rw [mkIETFun_zero_of_mem hyT, hidx, htv]
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    refine ⟨z - translationVector π lam (topCell π), ⟨?_, ?_⟩, ?_⟩
    · rw [htv]; linarith
    · rw [htv, hU]; linarith
    · have hyT : z - translationVector π lam (topCell π) ∈ Set.Ico 0 (totalLength lam) := by
        refine ⟨?_, ?_⟩
        · rw [htv]
          linarith [cut_pos hlt]
        · rw [htv]
          linarith
      rw [mkIETFun_zero_of_mem hyT]
      have hidx : idx lam (z - translationVector π lam (topCell π)) hyT.1 = topCell π := by
        refine idx_eq lam hyT ?_ ?_
        · rw [htv]; linarith
        · rw [htv, hU]; linarith
      rw [hidx]; ring

/-- **The tower decomposition (two floors)**: the interval is the disjoint union of the base
`[0, cut)` of the first return map and of its first floor `T(cell topCell) = [cut, Λ)`. -/
theorem tower_decomp (hlt : lam (topCell π) < lam (lastPos n)) :
    Set.Ico 0 (totalLength lam) = Set.Ico 0 (cut π lam) ∪
      mkIETFun lam π 0 '' Set.Ico (leftEnd lam (topCell π)) (upperEnd lam (topCell π)) := by
  rw [mkIETFun_image_topCell hlt]
  ext z
  constructor
  · intro hz
    by_cases hc : z < cut π lam
    · exact Or.inl ⟨hz.1, hc⟩
    · exact Or.inr ⟨le_of_not_gt hc, hz.2⟩
  · rintro (h | h)
    · exact mem_Ico_totalLength_of_mem_cut h
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
    (hlt : lam (topCell π) < lam (lastPos n)) :
    cellHat π lam (topCell π) = Set.Ico (leftEnd lam (topCell π)) (upperEnd lam (topCell π)) := by
  rw [cellHat, upperEnd_lamHat_of_ne (topCell_ne_lastPos hlt), leftEnd_lamHat]

theorem upperEnd_lamHat_le_cut {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam (lastPos n)) (β : Fin n) :
    upperEnd (lamHat π lam) β ≤ cut π lam := by
  rw [← cut_eq_sum_lamHat hlt]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun j _ _ => (lamHat π lam j).coe_nonneg)

theorem cellHat_subset_cut {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam (lastPos n)) (β : Fin n) :
    cellHat π lam β ⊆ Set.Ico 0 (cut π lam) := by
  intro y hy
  refine ⟨le_trans (leftEnd_nonneg _ _) hy.1, lt_of_lt_of_le hy.2 (upperEnd_lamHat_le_cut hlt β)⟩

theorem iUnion_cellHat {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (topCell π) < lam (lastPos n)) :
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
theorem tower_decomp_iUnion (hlt : lam (topCell π) < lam (lastPos n)) :
    Set.Ico 0 (totalLength lam) = Set.iUnion (fun β : Fin n =>
      Set.iUnion (fun j : Fin (returnB π β) =>
        (mkIETFun lam π 0)^[(j : ℕ)] '' cellHat π lam β)) := by
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
      rw [hj1, Function.iterate_one]
      rw [cellHat_topCell hlt] at hw
      exact ⟨w, hw, rfl⟩

theorem ret_eq_returnB (hlt : lam (topCell π) < lam (lastPos n)) {β : Fin n} {y : ℝ}
    (hy : y ∈ cellHat π lam β) : ret π lam y = returnB π β := by
  have hyc : y ∈ Set.Ico 0 (cut π lam) := cellHat_subset_cut hlt β hy
  have hidxH : idx (lamHat π lam) y hyc.1 = β := by
    refine idx_eq (lamHat π lam) ⟨hyc.1, ?_⟩ hy.1 hy.2
    rw [cut_eq_sum_lamHat hlt]; exact hyc.2
  have hidx : idx lam y hyc.1 = β := by
    rw [← idx_lamHat_eq hlt hyc]; exact hidxH
  by_cases hβ : β = topCell π
  · have hnot : mkIETFun lam π 0 y ∉ Set.Ico 0 (cut π lam) := by
      intro hcin
      have hge := (mkIETFun_mem_Ico_cut_totalLength hyc (by rw [hidx, hβ])).1
      linarith [hcin.2]
    rw [ret_of_not_mem hnot, hβ, returnB_eq_two]
  · rw [ret_of_mem (mkIETFun_mem_cut_of_ne hyc (by rw [hidx]; exact hβ)), returnB_eq_one hβ]

/-! ## 12. The bridge with `IETDatum₂.rvStep` and `rvMat` -/

theorem ofPerm_last_false (π : Equiv.Perm (Fin n)) :
    (IETDatum₂.ofPerm (π)).last false = (lastPos n) := (rfl)

theorem ofPerm_last_true (π : Equiv.Perm (Fin n)) :
    (IETDatum₂.ofPerm (π)).last true = topCell π := (rfl)

theorem rvMat_ofPerm_false_apply (π : Equiv.Perm (Fin n)) (i j : Fin n) :
    ((IETDatum₂.ofPerm (π)).rvMat false) i j
      = if i = j then 1 else if i = (lastPos n) ∧ j = topCell π then 1 else 0 := by
  rw [IETDatum₂.rvMat]
  simp only [ofPerm_last_false, ofPerm_last_true, Bool.not_false]

/-! ## 13. Part 2: the tower formula for an invariant measure (level 1)  `T = mkIETFun lam π 0` is a
measurable bijection of `ℝ` (it is `mkIETEquiv lam π 0`), so an invariant measure gives equal mass
to all floors `T^[j] '' A` (`measure_image_iterate`).  The level-one tower decomposition (Section
11) then gives the tower formula  `μ (cell α) = ∑ β, (rvMat false) α β * μ (cell β of the return
map)`.  The multiplicities are `1` for `β = α` and an extra floor over `topCell π` inside the
rightmost cell `lastPos n`: exactly the first Rauzy–Veech matrix. -/

theorem measurable_mkIETFun (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    Measurable (mkIETFun lam π 0) := by
  rcases eq_or_lt_of_le (Finset.sum_nonneg fun i _ => (lam i).coe_nonneg) with h0 | hpos
  · have hid : mkIETFun lam π 0 = fun x => x := by
      funext x
      rw [mkIETFun_of_notMem]
      intro hcon
      linarith [h0, hcon.1, hcon.2]
    rw [hid]; exact measurable_id
  · exact (isCutSet_mkIETCuts lam π 0 (le_refl _) hpos).measurable

theorem measurable_mkIETEquiv (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    Measurable ⇑(mkIETEquiv lam π 0) := measurable_mkIETFun π lam

theorem measurable_mkIETEquiv_symm (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    Measurable ⇑(mkIETEquiv lam π 0).symm :=
  measurable_mkIETFun π.symm (imageLengths π lam)

theorem measurable_mkIETFun_symm_iterate (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (j : ℕ) :
    Measurable (⇑(mkIETEquiv lam π 0).symm)^[j] :=
  (measurable_mkIETEquiv_symm π lam).iterate j

theorem mkIETFun_apply_iterate_symm (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (j : ℕ) (x : ℝ) :
    (⇑(mkIETEquiv lam π 0))^[j] ((⇑(mkIETEquiv lam π 0).symm)^[j] x) = x :=
  (Function.LeftInverse.iterate
    (f := ⇑(mkIETEquiv lam π 0).symm) (g := ⇑(mkIETEquiv lam π 0))
    (fun y => Equiv.apply_symm_apply (mkIETEquiv lam π 0) y) j) x

theorem mkIETFun_symm_apply_iterate (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (j : ℕ) (x : ℝ) :
    (⇑(mkIETEquiv lam π 0).symm)^[j] ((⇑(mkIETEquiv lam π 0))^[j] x) = x :=
  (Function.LeftInverse.iterate
    (f := ⇑(mkIETEquiv lam π 0)) (g := ⇑(mkIETEquiv lam π 0).symm)
    (fun y => Equiv.symm_apply_apply (mkIETEquiv lam π 0) y) j) x

theorem map_mkIETFun_symm (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (μ : Measure ℝ)
    (hμ : μ.map (mkIETFun lam π 0) = μ) : μ.map (⇑(mkIETEquiv lam π 0).symm) = μ := by
  have hμ' : μ.map (⇑(mkIETEquiv lam π 0)) = μ := hμ
  have h := congrArg (fun ν : Measure ℝ => ν.map (⇑(mkIETEquiv lam π 0).symm)) hμ'
  rw [Measure.map_map (measurable_mkIETEquiv_symm π lam) (measurable_mkIETEquiv π lam)] at h
  rw [Equiv.symm_comp_self (mkIETEquiv lam π 0)] at h
  rw [Measure.map_id] at h
  exact h.symm

theorem map_mkIETFun_symm_iterate (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (μ : Measure ℝ)
    (hμ : μ.map (mkIETFun lam π 0) = μ) (j : ℕ) : μ.map (⇑(mkIETEquiv lam π 0).symm)^[j] = μ := by
  induction j with
  | zero => simp
  | succ k ih =>
    have hcomp : (⇑(mkIETEquiv lam π 0).symm)^[k + 1]
        = ⇑(mkIETEquiv lam π 0).symm ∘ (⇑(mkIETEquiv lam π 0).symm)^[k] := by
      funext x
      rw [Function.iterate_succ_apply']
      rfl
    rw [hcomp, ← Measure.map_map (measurable_mkIETEquiv_symm π lam)
      (measurable_mkIETFun_symm_iterate π lam k), ih, map_mkIETFun_symm π lam μ hμ]

/-- The `j`-th iterate of the exchange applied to `A`, as the preimage of `A` under the `j`-th
iterate of the inverse exchange. -/
theorem image_iterate_eq_preimage_symm (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (j : ℕ)
    (A : Set ℝ) :
    (mkIETFun lam π 0)^[j] '' A = ((⇑(mkIETEquiv lam π 0).symm)^[j]) ⁻¹' A := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Set.mem_preimage]
    simp only [← coe_mkIETEquiv]
    rw [mkIETFun_symm_apply_iterate π lam j a]
    exact ha
  · intro hx
    exact ⟨_, hx, mkIETFun_apply_iterate_symm π lam j x⟩

/-- **All floors of a tower have the same mass**, for an invariant measure. -/
theorem measure_image_iterate (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (μ : Measure ℝ)
    (hμ : μ.map (mkIETFun lam π 0) = μ) (A : Set ℝ) (hA : MeasurableSet A) (j : ℕ) :
    μ ((mkIETFun lam π 0)^[j] '' A) = μ A := by
  rw [image_iterate_eq_preimage_symm π lam j A,
    ← Measure.map_apply (measurable_mkIETFun_symm_iterate π lam j) hA,
    map_mkIETFun_symm_iterate π lam μ hμ j]

/-- **A floor has the same mass as the base**: `μ (T '' A) = μ A`. -/
theorem measure_image_mkIETFun (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (μ : Measure ℝ)
    (hμ : μ.map (mkIETFun lam π 0) = μ) (A : Set ℝ) (hA : MeasurableSet A) :
    μ (mkIETFun lam π 0 '' A) = μ A := by
  have h := measure_image_iterate π lam μ hμ A hA 1
  rwa [Function.iterate_one] at h

/-! ### The multiplicity of the level-one tower -/

/-- The multiplicity of the floor over `β` inside the cell `α`, in the level-one tower: `1` if
`β = α`, plus `1` if `α` is the rightmost cell and `β` is the cell whose image is the rightmost
image cell.  This is the Rauzy–Veech matrix `rvMat false`. -/
def multOne (π : Equiv.Perm (Fin n)) (α β : Fin n) : ℕ :=
  if β = α then 1 else if β = topCell π ∧ α = (lastPos n) then 1 else 0

theorem measurableSet_cellHat (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (β : Fin n) :
    MeasurableSet (cellHat π lam β) := measurableSet_Ico

/-- **The tower formula at level one**, in the form of a two-term identity: the mass of a cell of
`T` is the mass of the cell of the first return map above it, plus — for the rightmost cell — the
mass of the cell over `topCell π` (the second floor). -/
theorem tower_formula_one_step (hlt : lam (topCell π) < lam (lastPos n)) (μ : Measure ℝ)
    (hμ : μ.map (mkIETFun lam π 0) = μ) (α : Fin n) :
    μ (Set.Ico (leftEnd lam α) (upperEnd lam α))
      = μ (cellHat π lam α) + (if α = (lastPos n) then μ (cellHat π lam (topCell π)) else 0) := by
  have hmeas := measurableSet_cellHat π lam
  by_cases hb : α = (lastPos n)
  · subst hb
    rw [ite_eq_left rfl]
    have hsplit : Set.Ico (leftEnd lam (lastPos n)) (upperEnd lam (lastPos n))
        = cellHat π lam (lastPos n) ∪ mkIETFun lam π 0 '' cellHat π lam (topCell π) := by
      rw [upperEnd_lastPos, cellHat_topCell hlt, mkIETFun_image_topCell hlt, cellHat,
        upperEnd_lamHat_lastPos hlt, leftEnd_lamHat]
      exact (Set.Ico_union_Ico_eq_Ico (le_of_lt (leftEnd_lastPos_le_cut hlt))
        (cut_le_totalLength π lam)).symm
    have hd : Disjoint (cellHat π lam (lastPos n))
        (mkIETFun lam π 0 '' cellHat π lam (topCell π)) := by
      rw [cellHat, upperEnd_lamHat_lastPos hlt, leftEnd_lamHat, cellHat_topCell hlt,
        mkIETFun_image_topCell hlt, Set.Ico_disjoint_Ico]
      exact le_trans (min_le_left _ _) (le_max_right _ _)
    have hm : MeasurableSet (mkIETFun lam π 0 '' cellHat π lam (topCell π)) := by
      rw [cellHat_topCell hlt, mkIETFun_image_topCell hlt]
      exact measurableSet_Ico
    rw [hsplit, measure_union hd hm, measure_image_mkIETFun π lam μ hμ _ (hmeas (topCell π))]
  · rw [ite_eq_right hb, add_zero]
    congr 1
    rw [cellHat, upperEnd_lamHat_of_ne hb, leftEnd_lamHat]

/-- The cell of the first return map sits inside the corresponding domain cell. -/
theorem cellHat_subset_dom (π' : Equiv.Perm (Fin n)) (L' : Fin n → ℝ≥0) (β : Fin n) :
    cellHat π' L' β ⊆ Set.Ico (leftEnd L' β) (upperEnd L' β) := by
  have h1 : leftEnd (lamHat π' L') β = leftEnd L' β := leftEnd_lamHat _ _ β
  have h2 : lamHat π' L' β ≤ L' β := by
    rw [lamHat]
    split
    · exact tsub_le_self
    · exact le_rfl
  have h2' : ((lamHat π' L') β : ℝ) ≤ (L' β : ℝ) := by exact_mod_cast h2
  intro y hy
  simp only [cellHat, Set.mem_Ico] at hy ⊢
  refine ⟨?_, ?_⟩
  · rw [← h1]; exact hy.1
  · have hle : upperEnd (lamHat π' L') β ≤ upperEnd L' β := by
      rw [upperEnd_eq, upperEnd_eq, h1]; linarith
    exact lt_of_lt_of_le hy.2 hle

end

end IntervalExchange.RauzyVeech

end
