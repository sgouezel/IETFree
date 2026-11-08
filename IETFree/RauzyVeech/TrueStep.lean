/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import IETFree.RauzyVeech.InvariantMeasure
public import IETFree.RauzyVeech.RenormData

/-!
# The Rauzy–Veech step of type `true`

Mirror of `IETFree.RauzyVeech.FirstReturn` for the case `λ (lastPos n) < λ (topCell π)`: the induced
subinterval
is the prefix `Ico 0 (Λ - λ (lastPos n))`, the return time is `1` except on the upper part of the
top cell where it is `2`, and the return map is the exchange of the step
`IETDatum₂.rvStep (IETDatum₂.ofPerm π)
true`. -/

open MeasureTheory Finset IntervalExchange.IETDatum₂
open scoped BigOperators ENNReal NNReal

@[expose] public section

namespace IntervalExchange.RauzyVeech

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## 1. The data of the type-`true` step -/

/-- The Rauzy cut of the type-`true` case: `Λ - λ (lastPos n)`. -/
def cutT (lam : Fin n → ℝ≥0) : ℝ := totalLength lam - (lam (lastPos n) : ℝ)

theorem leftEnd_lastPos_eq_cutT (lam : Fin n → ℝ≥0) : leftEnd lam (lastPos n) = cutT lam :=
  leftEnd_lastPos lam

/-- The insertion of the top-last position: the new bottom order of the type-`true` step. -/
def eT (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) := insertEquiv (topCell π)

/-- The permutation of the type-`true` step, in bottom-position coordinates. -/
def piHatT (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) := (eT π).symm.trans π

/-- The new lengths, indexed by letters. -/
def lamH (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) : Fin n → ℝ≥0 :=
  fun a => if a = topCell π then lam a - lam (lastPos n) else lam a

/-- The new lengths, in the new bottom order. -/
def lamT (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) : Fin n → ℝ≥0 :=
  fun j => lamH π lam ((eT π).symm j)

/-! ## 2. Consequences of the type-`true` hypothesis -/

variable {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}

theorem topCell_ne_lastPos_of_lt (hlt : lam (lastPos n) < lam (topCell π)) :
    topCell π ≠ (lastPos n) :=
  fun h => absurd hlt (by rw [h]; exact lt_irrefl _)

theorem topCell_succ_lt (hlt : lam (lastPos n) < lam (topCell π)) :
    (topCell π).val + 1 < n := by
  have hne := topCell_ne_lastPos_of_lt hlt
  have hvl : (topCell π).val ≠ n - 1 := by
    intro hh
    exact hne (Fin.ext (by rw [lastPos_val, hh]))
  have := (topCell π).isLt
  omega

/-! ## 3. The insertion at the top cell -/

theorem eT_apply_le {a : Fin n} (ha : a.val ≤ (topCell π).val) :
    eT π a = a :=
  insertEquiv_apply_le ha

theorem eT_apply_gt (hlt : lam (lastPos n) < lam (topCell π)) {a : Fin n}
    (ha : (topCell π).val < a.val) (hne : a ≠ lastPos n) :
    (eT π a).val = a.val + 1 :=
  insertEquiv_apply_gt (topCell_succ_lt hlt) ha hne

theorem eT_lastPos (hlt : lam (lastPos n) < lam (topCell π)) :
    eT π (lastPos n) = (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n) :=
  insertEquiv_lastPos (topCell_succ_lt hlt)

/-! ## 4. The new length vector: elementary values -/

theorem lamH_of_ne {a : Fin n} (ha : a ≠ topCell π) : lamH π lam a = lam a := by
  rw [lamH]; exact ite_eq_right ha

theorem lamH_topCell : lamH π lam (topCell π)
    = lam (topCell π) - lam (lastPos n) := by
  rw [lamH]; exact ite_eq_left rfl

theorem lamT_apply (j : Fin n) : lamT π lam j = lamH π lam ((eT π).symm j) := (rfl)

theorem eT_symm_of_le {j : Fin n} (hj : j.val ≤ (topCell π).val) :
    (eT π).symm j = j := by
  have h : eT π j = j := eT_apply_le hj
  have h2 : (eT π).symm (eT π j) = j := Equiv.symm_apply_apply _ _
  rwa [h] at h2

theorem eT_symm_succ (hlt : lam (lastPos n) < lam (topCell π)) :
    (eT π).symm (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      = (lastPos n) := by
  rw [← eT_lastPos hlt, Equiv.symm_apply_apply]

theorem eT_symm_of_gt (hlt : lam (lastPos n) < lam (topCell π)) {j : Fin n}
    (hj : (topCell π).val + 1 < j.val) :
    (eT π).symm j = (⟨j.val - 1, by have := j.isLt; omega⟩ : Fin n) := by
  set a : Fin n := ⟨j.val - 1, by have := j.isLt; omega⟩ with ha
  have haval : a.val = j.val - 1 := by rw [ha]
  have hne : a ≠ lastPos n := by
    intro h
    have h' : a.val = n - 1 := by rw [h, lastPos_val]
    omega
  have key : eT π a = j := by
    refine Fin.ext ?_
    rw [eT_apply_gt hlt (by omega) hne, haval]
    have := j.isLt
    omega
  rw [← key, Equiv.symm_apply_apply]

/-! ## 5. The total length of the new vector -/

theorem sum_lamH (hlt : lam (lastPos n) < lam (topCell π)) :
    ∑ a, (lamH π lam a : ℝ) = totalLength lam - (lam (lastPos n) : ℝ) := by
  have hterm (a : Fin n) :
    (lamH π lam a : ℝ)
      = (lam a : ℝ) - (if a = topCell π then (lam (lastPos n) : ℝ) else 0) := by
    by_cases ha : a = topCell π
    · rw [ha, lamH_topCell, NNReal.coe_sub (le_of_lt hlt), ite_eq_left rfl]
    · rw [lamH_of_ne ha, ite_eq_right ha, sub_zero]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ (topCell π) (fun _ => (lam (lastPos n) : ℝ))]
  simp only [Finset.mem_univ, ite_true]
  rw [totalLength]

theorem sum_lamT (hlt : lam (lastPos n) < lam (topCell π)) :
    ∑ j, (lamT π lam j : ℝ) = cutT lam := by
  have h : (∑ j, (lamT π lam j : ℝ)) = ∑ a, (lamH π lam a : ℝ) :=
    Equiv.sum_comp (eT π).symm (fun a => (lamH π lam a : ℝ))
  rw [h, sum_lamH hlt, cutT]

theorem totalLength_lamT (hlt : lam (lastPos n) < lam (topCell π)) :
    totalLength (lamT π lam) = cutT lam := sum_lamT hlt

/-! ## 6. Values of the new vector -/

theorem lamT_of_le {j : Fin n} (hj : j.val ≤ (topCell π).val) :
    lamT π lam j = lamH π lam j := by
  rw [lamT_apply, eT_symm_of_le hj]

theorem lamT_succ (hlt : lam (lastPos n) < lam (topCell π)) :
    lamT π lam (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      = lam (lastPos n) := by
  rw [lamT_apply, eT_symm_succ hlt, lamH_of_ne (Ne.symm (topCell_ne_lastPos_of_lt hlt))]

theorem lamT_of_gt (hlt : lam (lastPos n) < lam (topCell π)) {j : Fin n}
    (hj : (topCell π).val + 1 < j.val) :
    lamT π lam j = lam (⟨j.val - 1, by have := j.isLt; omega⟩ : Fin n) := by
  have hlt' := j.isLt
  set a : Fin n := ⟨j.val - 1, by omega⟩ with ha
  have haval : a.val = j.val - 1 := by rw [ha]
  have hap : a ≠ topCell π := by
    intro h
    have h' : a.val = (topCell π).val := by rw [h]
    omega
  rw [lamT_apply, eT_symm_of_gt hlt hj, lamH_of_ne hap]

/-! ## 7. Reindexing lemmas for the endpoints -/

omit [NeZero n] in
theorem leftEnd_comp_symm (e : Equiv.Perm (Fin n)) (f : Fin n → ℝ≥0) (j : Fin n) :
    leftEnd (fun k => f (e.symm k)) j
      = ∑ a ∈ Finset.univ.filter (fun a => e a < j), (f a : ℝ) := by
  rw [leftEnd, Finset.sum_filter,
    ← Equiv.sum_comp e (fun k => if k < j then (f (e.symm k) : ℝ) else 0), Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp

omit [NeZero n] in
theorem imageLeft_reindex (e : Equiv.Perm (Fin n)) (π : Equiv.Perm (Fin n))
    (f : Fin n → ℝ≥0) (j : Fin n) :
    imageLeft (e.symm.trans π) (fun k => f (e.symm k)) j = imageLeft π f (e.symm j) := by
  rw [imageLeft, imageLeft, Finset.sum_filter, Finset.sum_filter,
    ← Equiv.sum_comp e (fun k => if (e.symm.trans π) k < (e.symm.trans π) j
      then (f (e.symm k) : ℝ) else 0)]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Equiv.trans_apply]

theorem imageLeft_lamH (a : Fin n) : imageLeft π (lamH π lam) a = imageLeft π lam a := by
  rw [imageLeft, imageLeft]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_filter] at hb
  have hbp : b ≠ topCell π := by
    intro h
    rw [h, topCell_apply] at hb
    exact absurd hb.2 (not_lt.mpr (le_lastPos (π a)))
  rw [lamH_of_ne hbp]

/-! ## 8. The filters `{a | eT π a < j}` -/

theorem eT_apply_val (π : Equiv.Perm (Fin n)) (a : Fin n) :
    (eT π a).val = if a.val ≤ (topCell π).val then a.val
      else if a = lastPos n then (topCell π).val + 1 else a.val + 1 := by
  have h := trans_insertEquiv_apply_val (1 : Equiv.Perm (Fin n)) (topCell π)
    (c := lastPos n) (by simp) a
  simpa [eT] using h

theorem filter_eT_lt_of_le {j : Fin n}
    (hj : j.val ≤ (topCell π).val) :
    Finset.univ.filter (fun a : Fin n => eT π a < j) = Finset.univ.filter (fun a => a < j) := by
  have hlv : (lastPos n).val = n - 1 := lastPos_val
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
  rw [eT_apply_val]
  by_cases ha : a.val ≤ (topCell π).val
  · rw [ite_eq_left ha]
  · rw [ite_eq_right ha]
    by_cases hb : a = lastPos n
    · rw [ite_eq_left hb, hb]
      constructor <;> intro h <;> omega
    · rw [ite_eq_right hb]
      constructor <;> intro h <;> omega

theorem filter_eT_lt_succ (hlt : lam (lastPos n) < lam (topCell π)) :
    Finset.univ.filter (fun a : Fin n => eT π a < (⟨(topCell π).val + 1,
        topCell_succ_lt hlt⟩ : Fin n))
      = Finset.univ.filter (fun a : Fin n => a.val ≤ (topCell π).val) := by
  have hlv : (lastPos n).val = n - 1 := lastPos_val
  have hpv : (topCell π).val < n - 1 := by
    have hne := topCell_ne_lastPos_of_lt hlt
    have h1 := (topCell π).isLt
    have h2 : (topCell π).val ≠ n - 1 := by
      intro hh
      exact hne (Fin.ext (by rw [lastPos_val, hh]))
    omega
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
  rw [eT_apply_val]
  by_cases ha : a.val ≤ (topCell π).val
  · rw [ite_eq_left ha]; omega
  · rw [ite_eq_right ha]
    by_cases hb : a = lastPos n
    · rw [ite_eq_left hb, hb]
      have hle : (topCell π).val ≤ (lastPos n).val :=
        Fin.le_def.mp (le_lastPos (topCell π))
      have hpv := topCell_succ_lt hlt
      omega
    · rw [ite_eq_right hb]; omega

theorem filter_eT_lt_of_gt {j : Fin n}
    (hj : (topCell π).val + 1 < j.val) :
    Finset.univ.filter (fun a : Fin n => eT π a < j)
      = insert (lastPos n) (Finset.univ.filter (fun a : Fin n => a.val < j.val - 1)) := by
  have hlv : (lastPos n).val = n - 1 := lastPos_val
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def]
  rw [eT_apply_val]
  by_cases ha : a.val ≤ (topCell π).val
  · rw [ite_eq_left ha]
    exact ⟨fun _ => Or.inr (by omega), fun _ => by omega⟩
  · rw [ite_eq_right ha]
    by_cases hb : a = lastPos n
    · rw [ite_eq_left hb]
      exact ⟨fun _ => Or.inl hb, fun _ => by omega⟩
    · rw [ite_eq_right hb]
      constructor
      · intro h; exact Or.inr (by omega)
      · rintro (h | h)
        · exact absurd h hb
        · omega

/-! ## 9. The left end of the new cells -/

theorem leftEnd_lamT_of_le {j : Fin n} (hj : j.val ≤ (topCell π).val) :
    leftEnd (lamT π lam) j = leftEnd lam j := by
  have hL : leftEnd (lamT π lam) j
      = ∑ a ∈ Finset.univ.filter (fun a : Fin n => eT π a < j), (lamH π lam a : ℝ) :=
    leftEnd_comp_symm (eT π) (lamH π lam) j
  rw [hL, filter_eT_lt_of_le hj, leftEnd]
  refine Finset.sum_congr rfl fun a ha => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  rw [lamH_of_ne (by intro h; rw [h] at ha; omega)]

theorem leftEnd_lamT_succ (hlt : lam (lastPos n) < lam (topCell π)) :
    leftEnd (lamT π lam) (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      = upperEnd lam (topCell π) - (lam (lastPos n) : ℝ) := by
  have hL : leftEnd (lamT π lam) (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      = ∑ a ∈ Finset.univ.filter (fun a : Fin n => eT π a < (⟨(topCell π).val + 1,
          topCell_succ_lt hlt⟩ : Fin n)), (lamH π lam a : ℝ) :=
    leftEnd_comp_symm (eT π) (lamH π lam) _
  rw [hL, filter_eT_lt_succ hlt]
  have hins : Finset.univ.filter (fun a : Fin n => a.val ≤ (topCell π).val)
      = insert (topCell π) (Finset.univ.filter (fun a : Fin n => a < topCell π)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inr h'
      · exact Or.inl (Fin.ext h')
    · rintro (rfl | h)
      · exact le_rfl
      · exact le_of_lt h
  have hterms : (∑ a ∈ Finset.univ.filter (fun a : Fin n => a < topCell π),
        (lamH π lam a : ℝ))
      = ∑ a ∈ Finset.univ.filter (fun a : Fin n => a < topCell π), (lam a : ℝ) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [lamH_of_ne (ne_of_lt ha)]
  rw [hins, Finset.sum_insert (by simp), lamH_topCell, NNReal.coe_sub (le_of_lt hlt), hterms,
    upperEnd_eq, leftEnd]
  ring

theorem leftEnd_lamT_of_gt (hlt : lam (lastPos n) < lam (topCell π)) {j : Fin n}
    (hj : (topCell π).val + 1 < j.val) :
    leftEnd (lamT π lam) j = leftEnd lam (⟨j.val - 1, by have := j.isLt; omega⟩ : Fin n) := by
  have hlt' := j.isLt
  set i : Fin n := ⟨j.val - 1, by omega⟩ with hi
  have hival : i.val = j.val - 1 := by rw [hi]
  have hb : (lastPos n) ∉ Finset.univ.filter (fun a : Fin n => a.val < j.val - 1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    have hbv : (lastPos n).val = n - 1 := (rfl)
    omega
  have hp : topCell π ∈ Finset.univ.filter (fun a : Fin n => a.val < j.val - 1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hL : leftEnd (lamT π lam) j
      = ∑ a ∈ Finset.univ.filter (fun a : Fin n => eT π a < j), (lamH π lam a : ℝ) :=
    leftEnd_comp_symm (eT π) (lamH π lam) j
  rw [hL, filter_eT_lt_of_gt hj, Finset.sum_insert hb,
    lamH_of_ne (Ne.symm (topCell_ne_lastPos_of_lt hlt))]
  have hterm (a : Fin n) :
    (lamH π lam a : ℝ)
      = (lam a : ℝ) - (if a = topCell π then (lam (lastPos n) : ℝ) else 0) := by
    by_cases ha : a = topCell π
    · rw [ha, lamH_topCell, NNReal.coe_sub (le_of_lt hlt), ite_eq_left rfl]
    · rw [lamH_of_ne ha, ite_eq_right ha, sub_zero]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_sub_distrib,
    Finset.sum_ite_eq' (Finset.univ.filter (fun a : Fin n => a.val < j.val - 1))
      (topCell π) (fun _ => (lam (lastPos n) : ℝ)), ite_eq_left hp]
  have hLe : Finset.univ.filter (fun a : Fin n => a.val < j.val - 1)
      = Finset.univ.filter (fun a : Fin n => a < i) := by
    rw [← hival]
    simp only [Fin.lt_def]
  rw [hLe, leftEnd]
  ring

/-! ## 10. The dynamics of the first return to `Ico 0 (cutT lam)` -/

theorem cutT_le_totalLength (lam : Fin n → ℝ≥0) : cutT lam ≤ totalLength lam := by
  rw [cutT]; exact sub_le_self _ (by positivity)

theorem mem_Ico_totalLength_of_mem_cutT {y : ℝ} (hy : y ∈ Set.Ico 0 (cutT lam)) :
    y ∈ Set.Ico 0 (totalLength lam) :=
  ⟨hy.1, lt_of_lt_of_le hy.2 (cutT_le_totalLength lam)⟩

theorem cutT_pos (hlt : lam (lastPos n) < lam (topCell π)) : 0 < cutT lam := by
  have h1 := NNReal.coe_lt_coe.mpr hlt
  have h2 := single_le_totalLength lam (topCell π)
  rw [cutT]; linarith

theorem idx_mem_cutT {y : ℝ} (hy : y ∈ Set.Ico 0 (cutT lam)) :
    leftEnd lam (idx lam y hy.1) ≤ y ∧ y < upperEnd lam (idx lam y hy.1) :=
  ⟨idx_mem lam y hy.1, lt_upperEnd_idx lam (mem_Ico_totalLength_of_mem_cutT hy)⟩

theorem idx_ne_lastPos {y : ℝ} (hy : y ∈ Set.Ico 0 (cutT lam)) :
    idx lam y hy.1 ≠ (lastPos n) := by
  intro h
  have h1 := (idx_mem_cutT hy).1
  rw [h, leftEnd_lastPos_eq_cutT] at h1
  linarith [hy.2]

theorem mkIETFun_apply_cutT {y : ℝ} (hy : y ∈ Set.Ico 0 (cutT lam)) :
    mkIETFun lam π 0 y = y + translationVector π lam (idx lam y hy.1) :=
  mkIETFun_zero_of_mem (mem_Ico_totalLength_of_mem_cutT hy)

theorem translationVector_topCell :
    translationVector π lam (topCell π)
      = totalLength lam - (lam (topCell π) : ℝ) - leftEnd lam (topCell π) := by
  unfold translationVector
  rw [imageLeft_topCell]

/-- The split point of the top cell: the part of the top cell above it returns in two steps. -/
def splitT (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) : ℝ :=
  leftEnd lam (topCell π) + ((lam (topCell π) : ℝ) - (lam (lastPos n) : ℝ))

theorem imageUpper_le_cutT (hlt : lam (lastPos n) < lam (topCell π)) {i : Fin n}
    (hi : i ≠ topCell π) : imageUpper π lam i ≤ cutT lam := by
  refine le_trans (imageUpper_le_totalLength π lam hi) ?_
  have h := NNReal.coe_lt_coe.mpr hlt
  rw [cutT]; linarith

/-- **A point outside the top cell returns in one step.** -/
theorem mkIETFun_mem_cutT_of_ne_top (hlt : lam (lastPos n) < lam (topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 ≠ topCell π) :
    mkIETFun lam π 0 y ∈ Set.Ico 0 (cutT lam) := by
  rw [mkIETFun_apply_cutT hy]
  obtain ⟨h1, h2⟩ := idx_mem_cutT hy
  have hupper : imageUpper π lam (idx lam y hy.1) ≤ cutT lam := imageUpper_le_cutT hlt hi
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

/-- **A point of the lower part of the top cell returns in one step.** -/
theorem mkIETFun_mem_cutT_of_top_low (hlt : lam (lastPos n) < lam (topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 = topCell π)
    (hlo : y < splitT π lam) :
    mkIETFun lam π 0 y ∈ Set.Ico 0 (cutT lam) := by
  rw [mkIETFun_apply_cutT hy, hi, translationVector_topCell]
  have h1 := (idx_mem_cutT hy).1
  rw [hi] at h1
  have hlt' := NNReal.coe_lt_coe.mpr hlt
  have hnn : 0 ≤ imageLeft π lam (topCell π) := imageLeft_nonneg _ _ _
  have himg : imageLeft π lam (topCell π)
      = totalLength lam - (lam (topCell π) : ℝ) := imageLeft_topCell π lam
  have hsp : splitT π lam = leftEnd lam (topCell π)
      + ((lam (topCell π) : ℝ) - (lam (lastPos n) : ℝ)) := (rfl)
  constructor
  · linarith
  · rw [cutT]; linarith

/-- **A point of the upper part of the top cell leaves the base in one step.** -/
theorem mkIETFun_mem_Ico_cutT_totalLength_of_top_high (hlt : lam (lastPos n) < lam (topCell π))
    {y : ℝ} (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 = topCell π)
    (hhi : splitT π lam ≤ y) :
    mkIETFun lam π 0 y ∈ Set.Ico (cutT lam) (totalLength lam) := by
  rw [mkIETFun_apply_cutT hy, hi, translationVector_topCell]
  have h2 : y < leftEnd lam (topCell π) + (lam (topCell π) : ℝ) := by
    have h := lt_upperEnd_idx lam (mem_Ico_totalLength_of_mem_cutT hy)
    rwa [upperEnd_eq, hi] at h
  have hlt' := NNReal.coe_lt_coe.mpr hlt
  have himg : imageLeft π lam (topCell π)
      = totalLength lam - (lam (topCell π) : ℝ) := imageLeft_topCell π lam
  have hsp : splitT π lam = leftEnd lam (topCell π)
      + ((lam (topCell π) : ℝ) - (lam (lastPos n) : ℝ)) := (rfl)
  constructor
  · rw [cutT]; linarith
  · linarith

/-- On the upper part of the top cell the image lands in the rightmost domain cell. -/
theorem idx_mkIETFun_of_idx_topCell_high (hlt : lam (lastPos n) < lam (topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 = topCell π)
    (hhi : splitT π lam ≤ y) :
    idx lam (mkIETFun lam π 0 y)
      (le_trans (le_of_lt (cutT_pos hlt))
        (mkIETFun_mem_Ico_cutT_totalLength_of_top_high hlt hy hi hhi).1)
      = (lastPos n) := by
  obtain ⟨h1, h2⟩ := mkIETFun_mem_Ico_cutT_totalLength_of_top_high hlt hy hi hhi
  refine idx_eq lam ⟨le_trans (le_of_lt (cutT_pos hlt)) h1, h2⟩ ?_ ?_
  · rw [leftEnd_lastPos_eq_cutT]; exact h1
  · rw [upperEnd_lastPos]; exact h2

/-- **The second iterate of a point of the upper part of the top cell.** -/
theorem mkIETFun_mkIETFun_eq_true (hlt : lam (lastPos n) < lam (topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 = topCell π)
    (hhi : splitT π lam ≤ y) :
    mkIETFun lam π 0 (mkIETFun lam π 0 y)
      = mkIETFun lam π 0 y + translationVector π lam (lastPos n) := by
  have hT := mkIETFun_mem_Ico_cutT_totalLength_of_top_high hlt hy hi hhi
  have hidx := idx_mkIETFun_of_idx_topCell_high hlt hy hi hhi
  have hT' : mkIETFun lam π 0 y ∈ Set.Ico 0 (totalLength lam) :=
    ⟨le_trans (le_of_lt (cutT_pos hlt)) hT.1, hT.2⟩
  rw [mkIETFun_zero_of_mem hT', hidx]

/-! ## 11. The return time -/

/-- The return time to `Ico 0 (cutT lam)`: `1` unless the first iterate leaves the base. -/
def retT (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (y : ℝ) : ℕ :=
  if mkIETFun lam π 0 y ∈ Set.Ico 0 (cutT lam) then 1 else 2

theorem retT_of_mem {y : ℝ} (h : mkIETFun lam π 0 y ∈ Set.Ico 0 (cutT lam)) :
    retT π lam y = 1 := by
  rw [retT]; exact ite_eq_left h

theorem retT_of_not_mem {y : ℝ} (h : mkIETFun lam π 0 y ∉ Set.Ico 0 (cutT lam)) :
    retT π lam y = 2 := by
  rw [retT]; exact ite_eq_right h

/-! ## 12. The cells of the new arrangement -/

/-- The cells of the return exchange, in the new bottom order. -/
def cellHatT (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (j : Fin n) : Set ℝ :=
  Set.Ico (leftEnd (lamT π lam) j) (upperEnd (lamT π lam) j)

/-- The successor of a position. -/
def succFin {n : ℕ} (i : Fin n) (h : i.val + 1 < n) : Fin n := ⟨i.val + 1, h⟩

omit [NeZero n] in
@[simp] theorem succFin_val {i : Fin n} (h : i.val + 1 < n) : (succFin i h).val = i.val + 1 := (rfl)

theorem upperEnd_lamT_of_lt {j : Fin n} (hj : j.val < (topCell π).val) :
    upperEnd (lamT π lam) j = upperEnd lam j := by
  have hne : j ≠ topCell π := by
    intro h; rw [h] at hj; exact absurd hj (lt_irrefl _)
  rw [upperEnd_eq, upperEnd_eq, leftEnd_lamT_of_le (le_of_lt hj), lamT_of_le (le_of_lt hj),
    lamH_of_ne hne]

theorem leftEnd_lamT_succ_of_gt (hlt : lam (lastPos n) < lam (topCell π)) {i : Fin n}
    (hi : (topCell π).val < i.val) (h : i.val + 1 < n) :
    leftEnd (lamT π lam) (succFin i h) = leftEnd lam i := by
  have h2 : (topCell π).val + 1 < (succFin i h).val := by
    rw [succFin_val]; omega
  have h3 := leftEnd_lamT_of_gt hlt (j := succFin i h) h2
  rw [h3]
  congr 1

theorem upperEnd_lamT_succ_of_gt (hlt : lam (lastPos n) < lam (topCell π)) {i : Fin n}
    (hi : (topCell π).val < i.val) (h : i.val + 1 < n) :
    upperEnd (lamT π lam) (succFin i h) = upperEnd lam i := by
  have h2 : (topCell π).val + 1 < (succFin i h).val := by
    rw [succFin_val]; omega
  rw [upperEnd_eq, upperEnd_eq, leftEnd_lamT_succ_of_gt hlt hi h,
    lamT_of_gt hlt (j := succFin i h) h2]
  congr 1

theorem upperEnd_lamT_top (hlt : lam (lastPos n) < lam (topCell π)) :
    upperEnd (lamT π lam) (topCell π) = splitT π lam := by
  rw [upperEnd_eq, leftEnd_lamT_of_le (le_refl _), lamT_of_le (le_refl _), lamH_topCell,
    NNReal.coe_sub (le_of_lt hlt), splitT]

theorem leftEnd_lamT_succ_eq_splitT (hlt : lam (lastPos n) < lam (topCell π)) :
    leftEnd (lamT π lam)
      (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n) = splitT π lam := by
  rw [leftEnd_lamT_succ hlt, splitT, upperEnd_eq]
  ring

theorem upperEnd_lamT_succ_eq (hlt : lam (lastPos n) < lam (topCell π)) :
    upperEnd (lamT π lam) (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      = upperEnd lam (topCell π) := by
  rw [upperEnd_eq, leftEnd_lamT_succ hlt, lamT_succ hlt, upperEnd_eq]
  ring

/-! ## 13. The index of a point in the new arrangement -/

theorem mem_Ico_sum_lamT (hlt : lam (lastPos n) < lam (topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) : y ∈ Set.Ico 0 (∑ j, (lamT π lam j : ℝ)) :=
  ⟨hy.1, by rw [sum_lamT hlt]; exact hy.2⟩

theorem idx_lamT_of_lt (hlt : lam (lastPos n) < lam (topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam))
    (hi : (idx lam y hy.1).val < (topCell π).val) :
    idx (lamT π lam) y hy.1 = idx lam y hy.1 := by
  have hmem := idx_mem_cutT hy
  refine idx_eq (lamT π lam) (mem_Ico_sum_lamT hlt hy) ?_ ?_
  · rw [leftEnd_lamT_of_le (le_of_lt hi)]; exact hmem.1
  · rw [upperEnd_lamT_of_lt hi]; exact hmem.2

theorem idx_lamT_of_top_low (hlt : lam (lastPos n) < lam (topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 = topCell π)
    (hlo : y < splitT π lam) :
    idx (lamT π lam) y hy.1 = topCell π := by
  have hmem := idx_mem_cutT hy
  rw [hi] at hmem
  refine idx_eq (lamT π lam) (mem_Ico_sum_lamT hlt hy) ?_ ?_
  · rw [leftEnd_lamT_of_le (le_refl _)]; exact hmem.1
  · rw [upperEnd_lamT_top hlt]; exact hlo

theorem idx_lamT_of_top_high (hlt : lam (lastPos n) < lam (topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 = topCell π)
    (hhi : splitT π lam ≤ y) :
    idx (lamT π lam) y hy.1
      = (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n) := by
  have hmem := idx_mem_cutT hy
  rw [hi] at hmem
  have h2 : y < leftEnd lam (topCell π) + (lam (topCell π) : ℝ) := by
    have h := lt_upperEnd_idx lam (mem_Ico_totalLength_of_mem_cutT hy)
    rwa [upperEnd_eq, hi] at h
  refine idx_eq (lamT π lam) (mem_Ico_sum_lamT hlt hy) ?_ ?_
  · rw [leftEnd_lamT_succ_eq_splitT hlt]; exact hhi
  · rw [upperEnd_lamT_succ_eq hlt, upperEnd_eq]; exact h2

theorem idx_lamT_of_gt (hlt : lam (lastPos n) < lam (topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam))
    (hi : (topCell π).val < (idx lam y hy.1).val) :
    idx (lamT π lam) y hy.1 = succFin (idx lam y hy.1) (by
      have hib := idx_ne_lastPos hy
      have hibv : (idx lam y hy.1).val ≠ n - 1 := by
        intro h
        exact hib (Fin.ext (by rw [h]; rfl))
      have := (idx lam y hy.1).isLt
      omega) := by
  have hmem := idx_mem_cutT hy
  refine idx_eq (lamT π lam) (mem_Ico_sum_lamT hlt hy) ?_ ?_
  · rw [leftEnd_lamT_succ_of_gt hlt hi]; exact hmem.1
  · rw [upperEnd_lamT_succ_of_gt hlt hi]; exact hmem.2

/-! ## 14. The translation vectors of the new arrangement -/

theorem imageLeft_lamT (j : Fin n) :
    imageLeft (piHatT π) (lamT π lam) j = imageLeft π lam ((eT π).symm j) :=
  (imageLeft_reindex (eT π) π (lamH π lam) j).trans (imageLeft_lamH ((eT π).symm j))

theorem translationVector_piHatT_of_lt {i : Fin n} (hi : i.val < (topCell π).val) :
    translationVector (piHatT π) (lamT π lam) i = translationVector π lam i := by
  unfold translationVector
  rw [imageLeft_lamT, eT_symm_of_le (le_of_lt hi),
    leftEnd_lamT_of_le (le_of_lt hi)]

theorem translationVector_piHatT_top :
    translationVector (piHatT π) (lamT π lam) (topCell π)
      = translationVector π lam (topCell π) := by
  unfold translationVector
  rw [imageLeft_lamT, eT_symm_of_le (le_refl _),
    leftEnd_lamT_of_le (le_refl _)]

theorem translationVector_piHatT_succ (hlt : lam (lastPos n) < lam (topCell π)) :
    translationVector (piHatT π) (lamT π lam)
        (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      = translationVector π lam (topCell π) + translationVector π lam (lastPos n) := by
  unfold translationVector
  rw [imageLeft_lamT, eT_symm_succ hlt,
    leftEnd_lamT_succ_eq_splitT hlt, splitT, imageLeft_topCell, leftEnd_lastPos_eq_cutT]
  simp only [cutT]
  ring

theorem translationVector_piHatT_succ_of_gt (hlt : lam (lastPos n) < lam (topCell π))
    {i : Fin n} (hi : (topCell π).val < i.val) (h : i.val + 1 < n) :
    translationVector (piHatT π) (lamT π lam) (succFin i h) = translationVector π lam i := by
  have h2 : (topCell π).val + 1 < (succFin i h).val := by rw [succFin_val]; omega
  have h3 : (eT π).symm (succFin i h)
      = (⟨(succFin i h).val - 1, by have := (succFin i h).isLt; omega⟩ : Fin n) :=
    eT_symm_of_gt hlt h2
  have h4 : (⟨(succFin i h).val - 1, by have := (succFin i h).isLt; omega⟩ : Fin n) = i := by
    refine Fin.ext ?_
    simp only []
    rw [succFin_val]
    omega
  unfold translationVector
  rw [imageLeft_lamT, h3, h4,
    leftEnd_lamT_succ_of_gt hlt hi h]

/-! ## 15. The return map is the exchange of the step -/

theorem mkIETFun_lamT_of_lt (hlt : lam (lastPos n) < lam (topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam))
    (hi : (idx lam y hy.1).val < (topCell π).val) :
    mkIETFun (lamT π lam) (piHatT π) 0 y = mkIETFun lam π 0 y := by
  rw [mkIETFun_zero_of_mem (mem_Ico_sum_lamT hlt hy), mkIETFun_apply_cutT hy,
    idx_lamT_of_lt hlt hy hi, translationVector_piHatT_of_lt hi]

theorem mkIETFun_lamT_of_top_low (hlt : lam (lastPos n) < lam (topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 = topCell π)
    (hlo : y < splitT π lam) :
    mkIETFun (lamT π lam) (piHatT π) 0 y = mkIETFun lam π 0 y := by
  rw [mkIETFun_zero_of_mem (mem_Ico_sum_lamT hlt hy), mkIETFun_apply_cutT hy,
    idx_lamT_of_top_low hlt hy hi hlo, hi, translationVector_piHatT_top]

theorem mkIETFun_lamT_of_top_high (hlt : lam (lastPos n) < lam (topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 = topCell π)
    (hhi : splitT π lam ≤ y) :
    mkIETFun (lamT π lam) (piHatT π) 0 y
      = mkIETFun lam π 0 (mkIETFun lam π 0 y) := by
  rw [mkIETFun_zero_of_mem (mem_Ico_sum_lamT hlt hy),
    idx_lamT_of_top_high hlt hy hi hhi, mkIETFun_mkIETFun_eq_true hlt hy hi hhi,
    mkIETFun_apply_cutT hy, hi,
    translationVector_piHatT_succ hlt]
  ring

theorem mkIETFun_lamT_of_gt (hlt : lam (lastPos n) < lam (topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam))
    (hi : (topCell π).val < (idx lam y hy.1).val) :
    mkIETFun (lamT π lam) (piHatT π) 0 y = mkIETFun lam π 0 y := by
  have hib := idx_ne_lastPos hy
  have hibv : (idx lam y hy.1).val ≠ n - 1 := by
    intro h
    exact hib (Fin.ext (by rw [h]; rfl))
  have h : (idx lam y hy.1).val + 1 < n := by
    have := (idx lam y hy.1).isLt
    omega
  rw [mkIETFun_zero_of_mem (mem_Ico_sum_lamT hlt hy),
    idx_lamT_of_gt hlt hy hi, mkIETFun_apply_cutT hy, translationVector_piHatT_succ_of_gt hlt hi h]

/-- **Type `true`**: the first return map of the exchange to `Ico 0 (Λ - λ (lastPos n))` is the
exchange of the lengths `lamT` and the permutation `piHatT`, i.e. the Rauzy–Veech step of type
`true`. -/
theorem firstReturnT_eq (hlt : lam (lastPos n) < lam (topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) :
    (mkIETFun lam π 0)^[retT π lam y] y = mkIETFun (lamT π lam) (piHatT π) 0 y := by
  by_cases h : idx lam y hy.1 = topCell π
  · by_cases hlo : y < splitT π lam
    · rw [retT_of_mem (mkIETFun_mem_cutT_of_top_low hlt hy h hlo), Function.iterate_one,
        mkIETFun_lamT_of_top_low hlt hy h hlo]
    · have hhi : splitT π lam ≤ y := le_of_not_gt hlo
      have hnot : mkIETFun lam π 0 y ∉ Set.Ico 0 (cutT lam) := by
        intro hc
        have hge := (mkIETFun_mem_Ico_cutT_totalLength_of_top_high hlt hy h hhi).1
        linarith [hc.2]
      rw [retT_of_not_mem hnot, iterate_two_eq, mkIETFun_lamT_of_top_high hlt hy h hhi]
  · by_cases hi : (idx lam y hy.1).val < (topCell π).val
    · rw [retT_of_mem (mkIETFun_mem_cutT_of_ne_top hlt hy h), Function.iterate_one,
        mkIETFun_lamT_of_lt hlt hy hi]
    · have hi' : (topCell π).val < (idx lam y hy.1).val := by
        have hle : (topCell π).val ≤ (idx lam y hy.1).val := by
          by_contra hcon
          exact hi (by omega)
        have hne : (topCell π).val ≠ (idx lam y hy.1).val := by
          intro hc
          exact h (Fin.ext hc).symm
        omega
      rw [retT_of_mem (mkIETFun_mem_cutT_of_ne_top hlt hy h), Function.iterate_one,
        mkIETFun_lamT_of_gt hlt hy hi']

/-! ## 16. The cells of the return exchange and the return time on them -/

theorem measurableSet_cellHatT (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (β : Fin n) :
    MeasurableSet (cellHatT π lam β) := measurableSet_Ico

theorem cellHatT_subset_cutT (hlt : lam (lastPos n) < lam (topCell π)) (β : Fin n) :
    cellHatT π lam β ⊆ Set.Ico 0 (cutT lam) := by
  intro y hy
  refine ⟨le_trans (leftEnd_nonneg _ _) hy.1, ?_⟩
  refine lt_of_lt_of_le hy.2 ?_
  rw [← totalLength_lamT hlt]
  exact upperEnd_le_total _ _

theorem iUnion_cellHatT (hlt : lam (lastPos n) < lam (topCell π)) :
    Set.iUnion (fun β : Fin n => cellHatT π lam β) = Set.Ico 0 (cutT lam) := by
  ext y
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨β, hβ⟩
    exact cellHatT_subset_cutT hlt β hβ
  · intro hy
    exact ⟨idx (lamT π lam) y hy.1, idx_mem _ _ _, lt_upperEnd_idx _ (mem_Ico_sum_lamT hlt hy)⟩

theorem cellHatT_of_lt {j : Fin n} (hj : j.val < (topCell π).val) :
    cellHatT π lam j = Set.Ico (leftEnd lam j) (upperEnd lam j) := by
  rw [cellHatT, leftEnd_lamT_of_le (le_of_lt hj), upperEnd_lamT_of_lt hj]

theorem cellHatT_top (hlt : lam (lastPos n) < lam (topCell π)) :
    cellHatT π lam (topCell π)
      = Set.Ico (leftEnd lam (topCell π)) (splitT π lam) := by
  rw [cellHatT, leftEnd_lamT_of_le (le_refl _), upperEnd_lamT_top hlt]

theorem cellHatT_succ (hlt : lam (lastPos n) < lam (topCell π)) :
    cellHatT π lam (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      = Set.Ico (splitT π lam) (upperEnd lam (topCell π)) := by
  rw [cellHatT, leftEnd_lamT_succ_eq_splitT hlt, upperEnd_lamT_succ_eq hlt]

theorem cellHatT_of_gt (hlt : lam (lastPos n) < lam (topCell π)) {i : Fin n}
    (hi : (topCell π).val < i.val) (h : i.val + 1 < n) :
    cellHatT π lam (succFin i h) = Set.Ico (leftEnd lam i) (upperEnd lam i) := by
  rw [cellHatT, leftEnd_lamT_succ_of_gt hlt hi h, upperEnd_lamT_succ_of_gt hlt hi h]

/-- The multiplicity of the level-one tower in the type-`true` case. -/
def returnBT (π : Equiv.Perm (Fin n)) (β : Fin n) : ℕ :=
  if β = eT π (lastPos n) then 2 else 1

theorem returnBT_eq_two : returnBT π (eT π (lastPos n)) = 2 := by
  rw [returnBT]; exact ite_eq_left rfl

theorem returnBT_pos (π : Equiv.Perm (Fin n)) (β : Fin n) : 0 < returnBT π β := by
  rw [returnBT]; split <;> omega

theorem returnBT_le_two (π : Equiv.Perm (Fin n)) (β : Fin n) : returnBT π β ≤ 2 := by
  rw [returnBT]; split <;> omega

/-- **The return time on each cell of the return exchange.** -/
theorem retT_eq_returnBT (hlt : lam (lastPos n) < lam (topCell π)) {β : Fin n} {y : ℝ}
    (hy : y ∈ cellHatT π lam β) : retT π lam y = returnBT π β := by
  have hlt' := NNReal.coe_lt_coe.mpr hlt
  have hyc : y ∈ Set.Ico 0 (cutT lam) := cellHatT_subset_cutT hlt β hy
  have hsum : y ∈ Set.Ico 0 (totalLength lam) := mem_Ico_totalLength_of_mem_cutT hyc
  have hidxH : idx (lamT π lam) y hyc.1 = β := by
    refine idx_eq (lamT π lam) (mem_Ico_sum_lamT hlt hyc) hy.1 hy.2
  by_cases hβ : β = eT π (lastPos n)
  · rw [returnBT, ite_eq_left hβ]
    have hβv : β = (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n) := by
      rw [hβ, eT_lastPos hlt]
    have hy' : y ∈ Set.Ico (splitT π lam) (upperEnd lam (topCell π)) := by
      rw [← cellHatT_succ hlt, ← hβv]; exact hy
    have hidx : idx lam y hyc.1 = topCell π := by
      refine idx_eq lam hsum ?_ ?_
      · have h1 : leftEnd lam (topCell π) ≤ splitT π lam := by
          rw [splitT]; linarith
        linarith [hy'.1]
      · rw [upperEnd_eq] at hy' ⊢; exact hy'.2
    have hnot : mkIETFun lam π 0 y ∉ Set.Ico 0 (cutT lam) := by
      intro hc
      have hge := (mkIETFun_mem_Ico_cutT_totalLength_of_top_high hlt hyc hidx hy'.1).1
      linarith [hc.2]
    exact retT_of_not_mem hnot
  · rw [returnBT, ite_eq_right hβ]
    have hmem : mkIETFun lam π 0 y ∈ Set.Ico 0 (cutT lam) := by
      rcases lt_or_ge (topCell π).val β.val with hgt | hle
      · -- β above the top cell: it is the successor of a cell `i > p`
        have hβ2 : β.val ≠ (topCell π).val + 1 := by
          intro hc
          exact hβ (by
            rw [eT_lastPos hlt]
            exact Fin.ext (by rw [hc]))
        have hβ3 : (topCell π).val + 1 < β.val := by omega
        set i : Fin n := ⟨β.val - 1, by have := β.isLt; omega⟩ with hidef
        have hival : i.val = β.val - 1 := by rw [hidef]
        have hi : (topCell π).val < i.val := by rw [hival]; omega
        have hβi : β = succFin i (by rw [hival]; have := β.isLt; omega) := by
          refine Fin.ext ?_
          rw [succFin_val, hival]
          have := β.isLt
          omega
        have hy' : y ∈ Set.Ico (leftEnd lam i) (upperEnd lam i) := by
          rw [← cellHatT_of_gt hlt hi (by rw [hival]; have := β.isLt; omega), ← hβi]
          exact hy
        have hidx : idx lam y hyc.1 = i := idx_eq lam hsum hy'.1 hy'.2
        exact mkIETFun_mem_cutT_of_ne_top hlt hyc (by rw [hidx]; exact ne_of_gt hi)
      · rcases lt_or_eq_of_le hle with hlt2 | heq2
        · -- β below the top cell
          have hy' : y ∈ Set.Ico (leftEnd lam β) (upperEnd lam β) := by
            rw [← cellHatT_of_lt hlt2]; exact hy
          have hidx : idx lam y hyc.1 = β := idx_eq lam hsum hy'.1 hy'.2
          exact mkIETFun_mem_cutT_of_ne_top hlt hyc (by rw [hidx]; exact ne_of_lt hlt2)
        · -- β is the top cell
          have hβp : β = topCell π := Fin.ext heq2
          have hy' : y ∈ Set.Ico (leftEnd lam (topCell π)) (splitT π lam) := by
            rw [← cellHatT_top hlt, ← hβp]; exact hy
          have hidx : idx lam y hyc.1 = topCell π := by
            refine idx_eq lam hsum hy'.1 ?_
            rw [upperEnd_eq]
            have h2 := hy'.2
            rw [splitT] at h2
            linarith
          exact mkIETFun_mem_cutT_of_top_low hlt hyc hidx hy'.2
    exact retT_of_mem hmem

/-! ## 17. Induced invariance in the type-`true` case -/

theorem pairwiseDisjoint_cellHatT (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n))) (cellHatT π lam) := by
  intro β _ β' _ hne
  exact disjoint_cell (lamT π lam) hne

theorem image_cutT_self (hlt : lam (lastPos n) < lam (topCell π)) :
    mkIETFun (lamT π lam) (piHatT π) 0 '' Set.Ico 0 (cutT lam) = Set.Ico 0 (cutT lam) := by
  have h := image_Ico_totalLength (piHatT π) (lamT π lam)
  rw [totalLength_lamT hlt] at h
  exact h

/-- **Induced invariance, type `true`.** If `μ` is invariant under `T = mkIETFun lam π 0`
and `λ (lastPos n) <
λ (topCell π)`, then the restriction of `μ` to `Ico 0 (Λ - λ (lastPos n))` is invariant under the
first-return exchange `mkIETFun (lamT π lam) (piHatT π) 0`. -/
theorem restrict_cut_invariant_true (hlt : lam (lastPos n) < lam (topCell π))
    (μ : Measure ℝ) (hμ : μ.map (mkIETFun lam π 0) = μ) :
    (μ.restrict (Set.Ico 0 (cutT lam))).map (mkIETFun (lamT π lam) (piHatT π) 0)
      = μ.restrict (Set.Ico 0 (cutT lam)) := by
  -- the first-return exchange is measurable and maps the base `Ico 0 (cutT lam)` to itself
  have hmeasTH : Measurable (mkIETFun (lamT π lam) (piHatT π) 0) := measurable_mkIETFun _ _
  have hIm : mkIETFun (lamT π lam) (piHatT π) 0 '' Set.Ico 0 (cutT lam)
      = Set.Ico 0 (cutT lam) := image_cutT_self hlt
  have hcell (β : Fin n) : MeasurableSet (cellHatT π lam β) := measurableSet_cellHatT π lam β
  -- it suffices to compare `μ A` with `μ` of its image, for a measurable `A` in the base
  have hmain (A : Set ℝ) (hAI : A ⊆ Set.Ico 0 (cutT lam)) (hA : MeasurableSet A) :
    μ (mkIETFun (lamT π lam) (piHatT π) 0 '' A) = μ A := by
  -- split `A` over the cells: there the exchange is an iterate of `T`, so `μ` is preserved
    have hcover : A = ⋃ β, A ∩ cellHatT π lam β := by
      ext x
      constructor
      · intro hx
        have hxI : x ∈ ⋃ β : Fin n, cellHatT π lam β := by
          rw [iUnion_cellHatT hlt]
          exact hAI hx
        rw [Set.mem_iUnion] at hxI
        obtain ⟨β, hβ⟩ := hxI
        rw [Set.mem_iUnion]
        exact ⟨β, hx, hβ⟩
      · intro hx
        rw [Set.mem_iUnion] at hx
        obtain ⟨β, hβ⟩ := hx
        exact hβ.1
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n)))
        (fun β => A ∩ cellHatT π lam β) := by
      intro β _ β' _ hne
      exact (pairwiseDisjoint_cellHatT π lam (Finset.mem_univ β) (Finset.mem_univ β')
        hne).mono Set.inter_subset_right Set.inter_subset_right
    have hmeasInt (β) (hβ : β ∈ (Finset.univ : Finset (Fin n))) :
        MeasurableSet (A ∩ cellHatT π lam β) := hA.inter (hcell β)
    have hstep (β : Fin n) : μ (mkIETFun (lamT π lam) (piHatT π) 0 '' (A ∩ cellHatT π lam β))
        = μ (A ∩ cellHatT π lam β) := by
      have hfun (y) (hy0 : y ∈ A ∩ cellHatT π lam β) :
          mkIETFun (lamT π lam) (piHatT π) 0 y
            = (mkIETFun lam π 0)^[returnBT π β] y := by
        obtain ⟨-, hy⟩ := hy0
        have hyI : y ∈ Set.Ico 0 (cutT lam) := cellHatT_subset_cutT hlt β hy
        have h1 := firstReturnT_eq hlt hyI
        have h2 := retT_eq_returnBT hlt hy
        rw [h2] at h1
        exact h1.symm
      rw [Set.image_congr hfun]
      exact measure_image_iterate π lam μ hμ _ (hmeasInt β (Finset.mem_univ β)) _
    have hsum : μ A = ∑ β, μ (A ∩ cellHatT π lam β) := by
      conv_lhs => rw [hcover]
      have hbi := measure_biUnion_finset (μ := μ) hdisj hmeasInt
      simpa using hbi
  -- the image splits the same way, so the two masses agree on `A`
    have hcov : mkIETFun (lamT π lam) (piHatT π) 0 '' A
        = ⋃ β, mkIETFun (lamT π lam) (piHatT π) 0 '' (A ∩ cellHatT π lam β) := by
      conv_lhs => rw [hcover]
      rw [Set.image_iUnion]
    have hdisj' := pairwiseDisjoint_image
      (injective_mkIETFun (piHatT π) (lamT π lam)) hdisj
    have hmeas' (β) (hβ : β ∈ (Finset.univ : Finset (Fin n))) :
        MeasurableSet (mkIETFun (lamT π lam) (piHatT π) 0 '' (A ∩ cellHatT π lam β)) :=
            measurableSet_image_mkIETFun _ _ (hmeasInt β (Finset.mem_univ β))
    have hsum' : μ (mkIETFun (lamT π lam) (piHatT π) 0 '' A)
        = ∑ β, μ (A ∩ cellHatT π lam β) := by
      rw [hcov]
      have hbi := measure_biUnion_finset (μ := μ) hdisj' hmeas'
      rw [show μ (⋃ β, mkIETFun (lamT π lam) (piHatT π) 0 '' (A ∩ cellHatT π lam β))
          = ∑ β, μ (mkIETFun (lamT π lam) (piHatT π) 0 '' (A ∩ cellHatT π lam β)) from by
        simpa using hbi]
      exact Finset.sum_congr rfl fun β _ => hstep β
    rw [hsum', hsum]
  -- for a general `B`, apply that to the preimage of `B` in the base
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply hmeasTH hB, Measure.restrict_apply' measurableSet_Ico,
    Measure.restrict_apply' measurableSet_Ico]
  have hA : MeasurableSet (mkIETFun (lamT π lam) (piHatT π) 0 ⁻¹' B
      ∩ Set.Ico 0 (cutT lam)) :=
    (hB.preimage hmeasTH).inter measurableSet_Ico
  have hkey := hmain _ Set.inter_subset_right hA
  have himg1 : mkIETFun (lamT π lam) (piHatT π) 0
        '' (mkIETFun (lamT π lam) (piHatT π) 0 ⁻¹' B ∩ Set.Ico 0 (cutT lam))
      = B ∩ mkIETFun (lamT π lam) (piHatT π) 0 '' Set.Ico 0 (cutT lam) := by
    ext z
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨hy1, y, hy2, rfl⟩
    · rintro ⟨hzB, y, hyI, rfl⟩
      exact ⟨y, ⟨hzB, hyI⟩, rfl⟩
  rw [himg1, hIm] at hkey
  exact hkey.symm

/-! ## 18. The level-one tower formula in the type-`true` case -/

/-- The cell of the letter `a` in the return exchange (letter coordinates). -/
def cellHatL (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (a : Fin n) : Set ℝ :=
  cellHatT π lam (eT π a)

/-- The multiplicity of the level-one tower in the type-`true` case, in letter coordinates. -/
def multOneT (π : Equiv.Perm (Fin n)) (α β : Fin n) : ℕ :=
  if β = α then 1 else if α = topCell π ∧ β = (lastPos n) then 1 else 0

theorem cellHatL_top (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    cellHatL π lam (topCell π) = cellHatT π lam (topCell π) := by
  rw [cellHatL, eT_apply_le (le_refl _)]

theorem cellHatL_bot (hlt : lam (lastPos n) < lam (topCell π)) :
    cellHatL π lam (lastPos n)
      = cellHatT π lam (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n) := by
  rw [cellHatL, eT_lastPos hlt]

theorem cellHatL_of_lt {a : Fin n} (ha : a.val < (topCell π).val) :
    cellHatL π lam a = Set.Ico (leftEnd lam a) (upperEnd lam a) := by
  rw [cellHatL, eT_apply_le (le_of_lt ha), cellHatT_of_lt ha]

theorem cellHatL_of_gt (hlt : lam (lastPos n) < lam (topCell π)) {a : Fin n}
    (ha : (topCell π).val < a.val) (hb : a ≠ (lastPos n)) :
    cellHatL π lam a = Set.Ico (leftEnd lam a) (upperEnd lam a) := by
  have hav : a.val + 1 < n := by
    have hav1 : a.val ≠ n - 1 := by
      intro h
      exact hb (Fin.ext (by rw [h]; rfl))
    have := a.isLt
    omega
  have he : eT π a = succFin a hav := by
    refine Fin.ext ?_
    rw [succFin_val, eT_apply_gt hlt ha hb]
  rw [cellHatL, he, cellHatT_of_gt hlt ha hav]

/-- **The second floor is the image of the upper part of the top cell.** -/
theorem mkIETFun_image_cellHatT_succ (hlt : lam (lastPos n) < lam (topCell π)) :
    mkIETFun lam π 0 ''
        cellHatT π lam (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      = Set.Ico (leftEnd lam (lastPos n)) (upperEnd lam (lastPos n)) := by
  have htv : translationVector π lam (topCell π)
      = totalLength lam - (lam (topCell π) : ℝ) - leftEnd lam (topCell π) :=
    translationVector_topCell
  have hlv : leftEnd lam (lastPos n) = totalLength lam - (lam (lastPos n) : ℝ) :=
    leftEnd_lastPos lam
  have huv : upperEnd lam (lastPos n) = totalLength lam := upperEnd_lastPos lam
  have hsp : splitT π lam = leftEnd lam (topCell π)
      + ((lam (topCell π) : ℝ) - (lam (lastPos n) : ℝ)) := (rfl)
  have hpt (y) (hy : y ∈ cellHatT π lam
        (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)) : mkIETFun lam π 0
            y = y + translationVector π lam (topCell π) := by
    have hyI : y ∈ Set.Ico 0 (cutT lam) := by
      rw [← iUnion_cellHatT hlt]
      exact Set.mem_iUnion.mpr ⟨_, hy⟩
    rw [cellHatT_succ hlt] at hy
    rw [mkIETFun_apply_cutT hyI]
    have hidx : idx lam y hyI.1 = topCell π := by
      refine idx_eq lam (mem_Ico_totalLength_of_mem_cutT hyI) ?_ ?_
      · linarith [hy.1]
      · exact hy.2
    rw [hidx]
  rw [Set.image_congr hpt]
  have hgoal (z : ℝ) :
    z ∈ (fun a => a + translationVector π lam (topCell π)) ''
        cellHatT π lam (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      ↔ z ∈ Set.Ico (leftEnd lam (lastPos n)) (upperEnd lam (lastPos n)) := by
    rw [Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      -- the image point is this translate by definition, which `cellHatT_succ` rewrites
      show y + translationVector π lam (topCell π)
        ∈ Set.Ico (leftEnd lam (lastPos n)) (upperEnd lam (lastPos n))
      rw [cellHatT_succ hlt] at hy
      rw [hsp] at hy
      rw [htv, hlv, huv]
      have hup : upperEnd lam (topCell π)
          = leftEnd lam (topCell π) + (lam (topCell π) : ℝ) := upperEnd_eq lam _
      constructor <;> linarith [hy.1, hy.2]
    · intro hz
      rw [hlv, huv] at hz
      refine ⟨z - translationVector π lam (topCell π), ?_, ?_⟩
      · rw [cellHatT_succ hlt, hsp, htv, upperEnd_eq]
        constructor <;> linarith [hz.1, hz.2]
      · show z - translationVector π lam (topCell π)
            + translationVector π lam (topCell π) = z
        ring
  ext z
  exact hgoal z

/-- **The tower formula at level one, type `true`**, in two-term form. -/
theorem tower_formula_one_step_true (hlt : lam (lastPos n) < lam (topCell π))
    (μ : Measure ℝ) (hμ : μ.map (mkIETFun lam π 0) = μ) (α : Fin n) :
    μ (Set.Ico (leftEnd lam α) (upperEnd lam α))
      = μ (cellHatL π lam α)
        + (if α = topCell π then μ (cellHatL π lam (lastPos n)) else 0) := by
  have hlt' := NNReal.coe_lt_coe.mpr hlt
  have hmeas := measurableSet_cellHatT π lam
  have himg := mkIETFun_image_cellHatT_succ hlt
  have hmeasB : MeasurableSet (cellHatL π lam (lastPos n)) := by
    rw [cellHatL_bot hlt]; exact hmeas _
  by_cases hα : α = topCell π
  · subst hα
    rw [ite_eq_left rfl, cellHatL_top, cellHatL_bot hlt]
    have hsplit : Set.Ico (leftEnd lam (topCell π)) (upperEnd lam (topCell π))
        = cellHatT π lam (topCell π)
          ∪ cellHatT π lam (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n) := by
      have hb0 : (0 : ℝ) ≤ (lam (lastPos n) : ℝ) := NNReal.coe_nonneg _
      rw [cellHatT_top hlt, cellHatT_succ hlt, splitT, upperEnd_eq,
        Set.Ico_union_Ico_eq_Ico (by linarith) (by linarith)]
    have hd : Disjoint (cellHatT π lam (topCell π))
        (cellHatT π lam (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)) :=
      disjoint_cell (lamT π lam) (by
        intro h
        have hv := congrArg Fin.val h
        simp only at hv
        omega)
    rw [hsplit, measure_union hd (hmeas _)]
  · rw [ite_eq_right hα, add_zero]
    by_cases hαb : α = (lastPos n)
    · subst hαb
      rw [cellHatL_bot hlt, ← himg,
        measure_image_mkIETFun π lam μ hμ _ (hmeas _)]
    · rcases lt_or_gt_of_ne hα with hlt2 | hgt2
      · exact congrArg μ (cellHatL_of_lt hlt2).symm
      · exact congrArg μ (cellHatL_of_gt hlt hgt2 hαb).symm

theorem multOneT_cast_mul {f : Fin n → ℝ≥0∞} (hne : topCell π ≠ (lastPos n))
    (i j : Fin n) :
    (multOneT π i j : ℝ≥0∞) * f j
      = (if i = j then f j else 0)
        + (if i = topCell π then (if j = (lastPos n) then f j else 0) else 0) := by
  unfold multOneT
  by_cases h1 : j = i
  · rw [h1]
    rw [ite_eq_left rfl, ite_eq_left rfl]
    by_cases h2 : i = topCell π
    · rw [ite_eq_left h2, ite_eq_right (fun h => hne (h2.symm.trans h))]
      simp
    · rw [ite_eq_right h2]
      simp
  · rw [ite_eq_right h1, ite_eq_right (Ne.symm h1), zero_add]
    by_cases h2 : i = topCell π
    · rw [ite_eq_left h2]
      by_cases h3 : j = (lastPos n)
      · rw [ite_eq_left ⟨h2, h3⟩, ite_eq_left h3]
        simp
      · rw [ite_eq_right (fun h => h3 h.2), ite_eq_right h3]
        simp
    · rw [ite_eq_right (fun h => h2 h.1), ite_eq_right h2]
      simp

/-- **The level-one tower formula, matrix form, type `true`**: for a `T`-invariant measure `μ`, `μ
(cell i) = ∑ j, multOneT i j * μ (cell j of the first return map)`, the multiplicity matrix being
`rvMat true`. -/
theorem tower_formula_one_step_mult_true (hlt : lam (lastPos n) < lam (topCell π))
    (μ : Measure ℝ) (hμ : μ.map (mkIETFun lam π 0) = μ) (i : Fin n) :
    μ (Set.Ico (leftEnd lam i) (upperEnd lam i))
      = ∑ j, (multOneT π i j : ℝ≥0∞) * μ (cellHatL π lam j) := by
  rw [tower_formula_one_step_true hlt μ hμ i]
  have hne : topCell π ≠ (lastPos n) := topCell_ne_lastPos_of_lt hlt
  have hsum : (∑ j, (multOneT π i j : ℝ≥0∞) * μ (cellHatL π lam j))
      = ∑ j, ((if i = j then μ (cellHatL π lam j) else 0)
          + (if i = topCell π then
              (if j = (lastPos n) then μ (cellHatL π lam j) else 0) else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    exact multOneT_cast_mul (f := fun j => μ (cellHatL π lam j)) hne i j
  rw [hsum, Finset.sum_add_distrib,
    Finset.sum_ite_eq Finset.univ i (fun j => μ (cellHatL π lam j))]
  simp only [Finset.mem_univ, ite_true]
  have hinner : (∑ j, (if i = topCell π then
        (if j = (lastPos n) then μ (cellHatL π lam j) else 0) else 0))
      = if i = topCell π then μ (cellHatL π lam (lastPos n)) else 0 := by
    by_cases hi : i = topCell π
    · rw [ite_eq_left hi,
        Finset.sum_congr rfl (fun j _ => ite_eq_left hi),
        Finset.sum_ite_eq' Finset.univ ((lastPos n)) (fun j => μ (cellHatL π lam j))]
      simp
    · rw [ite_eq_right hi, Finset.sum_eq_zero (fun j _ => ite_eq_right hi)]
  rw [hinner]

/-! ## 19. The level-`n` formula along an arbitrary word  The per-step condition is
`IsRauzyStep P lam ε`: at the vertex `P` with lengths `lam`, the step of type `ε` is the Rauzy
step, i.e. the strict inequality of the two last lengths holds in the direction `ε`.  Its iteration
along a word is `IsRauzyPath`. -/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The type-`ε` Rauzy condition at the vertex `P` with lengths `lam`. -/
def IsRauzyStep (P : IETDatum₂ α n) (lam : α → ℝ≥0) (ε : Bool) : Prop :=
  if ε then lam (P.last false) < lam (P.last true) else lam (P.last true) < lam (P.last false)

omit [DecidableEq α] in
theorem isRauzyStep_true_iff (P : IETDatum₂ α n) (lam : α → ℝ≥0) :
    IsRauzyStep P lam true ↔ lam (P.last false) < lam (P.last true) := Iff.rfl

omit [DecidableEq α] in
theorem isRauzyStep_false_iff (P : IETDatum₂ α n) (lam : α → ℝ≥0) :
    IsRauzyStep P lam false ↔ lam (P.last true) < lam (P.last false) := Iff.rfl

/-- The iteration of `IsRauzyStep` along a word. -/
def IsRauzyPath (P : IETDatum₂ α n) (lam : α → ℝ≥0) : List Bool → Prop
  | [] => True
  | e :: es => IsRauzyStep P lam e ∧ IsRauzyPath (P.rvStep e) (hatLam P e lam) es

omit [DecidableEq α] in
theorem perm_rvStep_true (P : IETDatum₂ α n) : (P.rvStep true).perm = piHatT P.perm := by
  have hp : IETDatum₂.pivot P true = topCell P.perm := IETDatum₂.piBottom_last_true P
  rw [IETDatum₂.rvStep_perm_true, hp, piHatT, eT, Equiv.symm_trans, Equiv.trans_assoc]
  rfl

omit [DecidableEq α] in
theorem piBottom_rvStep_true (P : IETDatum₂ α n) (a : α) :
    (P.rvStep true).piBottom a = eT P.perm (P.piBottom a) := by
  have hp : IETDatum₂.pivot P true = topCell P.perm := IETDatum₂.piBottom_last_true P
  rw [IETDatum₂.rvStep_apply_true, ← IETDatum₂.pivot_true, hp]
  rfl

omit [DecidableEq α] in
theorem piBottom_rvStep_true_symm (P : IETDatum₂ α n) (j : Fin n) :
    (P.rvStep true).piBottom.symm j = P.piBottom.symm ((eT P.perm).symm j) := by
  rw [Equiv.symm_apply_eq, piBottom_rvStep_true, Equiv.apply_symm_apply]
  exact (Equiv.apply_symm_apply (eT P.perm) j).symm

/-- The renormalised lengths after a `true` step, in `α` coordinates. -/
theorem lengthsInBottom_hatLam_true (P : IETDatum₂ α n) (lam : α → ℝ≥0) :
    (P.rvStep true).lengthsInBottom (hatLam P true lam)
      = lamT P.perm (P.lengthsInBottom lam) := by
  have hlastt : P.last true = P.piBottom.symm (topCell P.perm) := by
    rw [← IETDatum₂.piBottom_last_true P, Equiv.symm_apply_apply]
  have hlastf : P.last false = P.piBottom.symm (lastPos n) := by
    rw [← IETDatum₂.piBottom_last_false P, Equiv.symm_apply_apply]
  funext j
  rw [IETDatum₂.lengthsInBottom, piBottom_rvStep_true_symm, lamT, lamH,
    hatLam, IETDatum₂.lengthsInBottom]
  simp only [Bool.not_true, hlastt, hlastf]
  by_cases hj : (eT P.perm).symm j = topCell P.perm
  · have hj' : P.piBottom.symm ((eT P.perm).symm j)
        = P.piBottom.symm (topCell P.perm) := by rw [hj]
    rw [ite_eq_left hj, ite_eq_left hj']
    rfl
  · have hj' : ¬ (P.piBottom.symm ((eT P.perm).symm j)
        = P.piBottom.symm (topCell P.perm)) := fun h => hj (P.piBottom.symm.injective h)
    rw [ite_eq_right hj, ite_eq_right hj']

/-- `rvMat true` of `IETDatum₂` data is `rvMat true` of the permutation, in bottom coordinates. -/
theorem rvMat_ofPerm_true (P : IETDatum₂ α n) (a b : α) :
    P.rvMat true a b = (IETDatum₂.ofPerm (P.perm)).rvMat true (P.piBottom a) (P.piBottom b) := by
  have e1 : (P.piBottom a = P.piBottom b) ↔ (a = b) := P.piBottom.injective.eq_iff
  have e2 : (P.piBottom a = (IETDatum₂.ofPerm (P.perm)).last true) ↔ (a = P.last true) := by
    rw [ofPerm_last_true (P.perm),
      ← IETDatum₂.piBottom_last_true P]
    exact P.piBottom.injective.eq_iff
  have e3 : (P.piBottom b = (IETDatum₂.ofPerm (P.perm)).last false) ↔ (b = P.last false) := by
    rw [ofPerm_last_false (P.perm),
      ← IETDatum₂.piBottom_last_false P]
    exact P.piBottom.injective.eq_iff
  simp only [IETDatum₂.rvMat, Bool.not_true, e1, e2, e3]

theorem rvMatNat_ofPerm_true (P : IETDatum₂ α n) (a b : α) :
    P.rvMatNat true a b = multOneT P.perm (P.piBottom a) (P.piBottom b) := by
  have key : P.rvMat true a b
      = if P.piBottom b = P.piBottom a then (1 : ℤ)
        else if P.piBottom a = topCell P.perm ∧ P.piBottom b = (lastPos n) then 1
        else 0 := by
    rw [rvMat_ofPerm_true P a b, IETDatum₂.rvMat]
    simp only [ofPerm_last_true, ofPerm_last_false, Bool.not_true]
    by_cases h2 : P.piBottom b = P.piBottom a
    · rw [ite_eq_left h2, ite_eq_left h2.symm]
    · rw [ite_eq_right h2, ite_eq_right (Ne.symm h2)]
  rw [IETDatum₂.rvMatNat, key]
  unfold multOneT
  by_cases h2 : P.piBottom b = P.piBottom a
  · rw [ite_eq_left h2, ite_eq_left h2]
    exact Int.toNat_natCast 1
  · rw [ite_eq_right h2, ite_eq_right h2]
    by_cases h3 : P.piBottom a = topCell P.perm ∧ P.piBottom b = (lastPos n)
    · rw [ite_eq_left h3, ite_eq_left h3]
      exact Int.toNat_natCast 1
    · rw [ite_eq_right h3, ite_eq_right h3]
      exact Int.toNat_natCast 0

/-- The cell of the letter `b` after one step of type `ε`. -/
theorem cellAt_singleton_false (P : IETDatum₂ α n) (lam : α → ℝ≥0) (b : α) :
    cellAt P [false] lam b
      = cellHat P.perm (P.lengthsInBottom lam) (P.piBottom b) := by
  rw [cellAt, vertex_singleton, lamAfter_singleton, lengthsInBottom_hatLam]
  rfl

theorem cellAt_singleton_true (P : IETDatum₂ α n) (lam : α → ℝ≥0) (b : α) :
    cellAt P [true] lam b
      = cellHatL P.perm (P.lengthsInBottom lam) (P.piBottom b) := by
  rw [cellAt, vertex_singleton, lamAfter_singleton, lengthsInBottom_hatLam_true, cellHatL, cellHatT,
    piBottom_rvStep_true]

omit [NeZero n] [DecidableEq α] in
theorem totalLength_lengthsInBottom_eq (P : IETDatum₂ α n) (lam : α → ℝ≥0) :
    totalLength (P.lengthsInBottom lam) = totalLength lam :=
  Equiv.sum_comp P.piBottom.symm (fun a => (lam a : ℝ))

theorem totalLength_hatLam_le (P : IETDatum₂ α n) (ε : Bool) (lam : α → ℝ≥0) :
    totalLength (hatLam P ε lam) ≤ totalLength lam := by
  refine Finset.sum_le_sum fun a _ => ?_
  rw [hatLam]
  split
  · exact_mod_cast tsub_le_self
  · exact le_rfl

theorem totalLength_lamAfter_le (P : IETDatum₂ α n) (lam : α → ℝ≥0) (γ : List Bool) :
    totalLength (lamAfter P γ lam) ≤ totalLength lam := by
  induction γ generalizing P lam with
  | nil => exact le_rfl
  | cons e es ih => rw [lamAfter_cons]; exact le_trans (ih _ _) (totalLength_hatLam_le P e lam)

theorem cellAt_subset_totalLength_le (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) (b : α)
    {A : ℝ} (hA : totalLength (lamAfter P γ lam) ≤ A) :
    cellAt P γ lam b ⊆ Set.Ico 0 A := by
  intro y hy
  refine ⟨le_trans (leftEnd_nonneg _ _) hy.1, ?_⟩
  rw [← totalLength_lengthsInBottom_eq (P.vertex γ) (lamAfter P γ lam)] at hA
  exact lt_of_lt_of_le hy.2 (le_trans (upperEnd_le_total _ _) hA)

theorem pathQ_toNat_eq_Qnat (P : IETDatum₂ α n) (γ : List Bool) (a b : α) :
    (IETDatum₂.Path.Q P γ a b).toNat = P.Qnat γ a b := by
  rw [← P.Qnat_cast γ a b]
  exact Int.toNat_natCast (P.Qnat γ a b)

/-- **The level-one tower formula in `α` coordinates**, for either type `ε`. -/
theorem tower_formula_one_step_comb (P : IETDatum₂ α n) (lam : α → ℝ≥0) (ν : Measure ℝ)
    (hν : ν.map (mkIETFun (P.lengthsInBottom lam) P.perm 0) = ν) (ε : Bool)
    (hε : IsRauzyStep P lam ε) (a : α) :
    ν (cellOf P lam a)
      = ∑ b, ((P.rvMat ε a b).toNat : ℝ≥0∞) * ν (cellAt P [ε] lam b) := by
  have e1 : P.lengthsInBottom lam (topCell P.perm) = lam (P.last true) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_true P, Equiv.symm_apply_apply]
  have e2 : P.lengthsInBottom lam (lastPos n) = lam (P.last false) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_false P, Equiv.symm_apply_apply]
  cases ε with
  | false =>
    have hlt : P.lengthsInBottom lam (topCell P.perm)
        < P.lengthsInBottom lam (lastPos n) := by
      rw [e1, e2]; exact hε
    have h1 := tower_formula_one_step_mult (π := P.perm) (lam := P.lengthsInBottom lam)
      hlt ν hν (P.piBottom a)
    rw [← Equiv.sum_comp P.piBottom (fun y : Fin n =>
      (multOne P.perm (P.piBottom a) y : ℝ≥0∞)
        * ν (cellHat P.perm (P.lengthsInBottom lam) y))] at h1
    refine h1.trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [← cellAt_singleton_false P lam b, ← P.rvMatNat_ofPerm_false a b]
    rfl
  | true =>
    have hlt : P.lengthsInBottom lam (lastPos n)
        < P.lengthsInBottom lam (topCell P.perm) := by
      rw [e1, e2]; exact hε
    have h1 := tower_formula_one_step_mult_true (π := P.perm) (lam := P.lengthsInBottom lam)
      hlt ν hν (P.piBottom a)
    rw [← Equiv.sum_comp P.piBottom (fun y : Fin n =>
      (multOneT P.perm (P.piBottom a) y : ℝ≥0∞)
        * ν (cellHatL P.perm (P.lengthsInBottom lam) y))] at h1
    refine h1.trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [← cellAt_singleton_true P lam b, ← rvMatNat_ofPerm_true P a b]
    rfl

theorem totalLength_hatLam_false (P : IETDatum₂ α n) (lam : α → ℝ≥0)
    (hlt : P.lengthsInBottom lam (topCell P.perm) < P.lengthsInBottom lam (lastPos n)) :
    totalLength (hatLam P false lam) = cut P.perm (P.lengthsInBottom lam) := by
  rw [← totalLength_lengthsInBottom_eq (P.rvStep false) (hatLam P false lam),
    ← cut_eq_sum_lamHat hlt, ← lengthsInBottom_hatLam P lam]
  rfl

theorem totalLength_hatLam_true (P : IETDatum₂ α n) (lam : α → ℝ≥0)
    (hlt : P.lengthsInBottom lam (lastPos n) < P.lengthsInBottom lam (topCell P.perm)) :
    totalLength (hatLam P true lam) = cutT (P.lengthsInBottom lam) := by
  rw [← totalLength_lengthsInBottom_eq (P.rvStep true) (hatLam P true lam),
    ← totalLength_lamT hlt, ← lengthsInBottom_hatLam_true P lam]

theorem mkIETFun_rvStep_false_hatLam (P : IETDatum₂ α n) (lam : α → ℝ≥0) :
    mkIETFun (lamHat P.perm (P.lengthsInBottom lam)) (piHat P.perm) 0
      = mkIETFun ((P.rvStep false).lengthsInBottom (hatLam P false lam))
          ((P.rvStep false).perm) 0 := by
  rw [IETDatum₂.perm_rvStep_false, lengthsInBottom_hatLam]

theorem mkIETFun_rvStep_true_hatLam (P : IETDatum₂ α n) (lam : α → ℝ≥0) :
    mkIETFun (lamT P.perm (P.lengthsInBottom lam)) (piHatT P.perm) 0
      = mkIETFun ((P.rvStep true).lengthsInBottom (hatLam P true lam))
          ((P.rvStep true).perm) 0 := by
  rw [perm_rvStep_true, lengthsInBottom_hatLam_true]

/-- Regrouping of a double sum with weights. -/
theorem sum_mul_sum {ι : Type*} [Fintype ι] (A : ι → ℝ≥0∞)
    (B : ι → ι → ℝ≥0∞) (w : ι → ℝ≥0∞) :
    (∑ c, A c * ∑ b, B c b * w b) = ∑ b, (∑ c, A c * B c b) * w b := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [mul_assoc]

/-- **The level-`n` tower formula along an arbitrary word** (both Rauzy types). -/
theorem tower_formula_level_pathQ_mkIETFun (P : IETDatum₂ α n) (lam : α → ℝ≥0)
    (ν : Measure ℝ) (hν : ν.map (mkIETFun (P.lengthsInBottom lam) P.perm 0) = ν)
    (γ : List Bool) (hγ : IsRauzyPath P lam γ) (a : α) :
    ν (cellOf P lam a)
      = ∑ b, ((IETDatum₂.Path.Q P γ a b).toNat : ℝ≥0∞) * ν (cellAt P γ lam b) := by
  induction γ generalizing P lam ν a with
  | nil =>
    rw [IETDatum₂.Path.Q_nil, Finset.sum_eq_single a]
    · rw [Matrix.one_apply, ite_eq_left rfl]
      rw [Int.toNat_one, Nat.cast_one, one_mul]
      rfl
    · intro b _ hba
      rw [Matrix.one_apply, ite_eq_right (fun h : a = b => hba h.symm)]
      simp
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  | cons e es ih =>
    obtain ⟨he, hes⟩ := hγ
    have e1 : P.lengthsInBottom lam (topCell P.perm) = lam (P.last true) := by
      simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_true P,
        Equiv.symm_apply_apply]
    have e2 : P.lengthsInBottom lam (lastPos n) = lam (P.last false) := by
      simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_false P,
        Equiv.symm_apply_apply]
    -- the restricted measure is invariant under the renormalised exchange
    have hν' : (ν.restrict (Set.Ico 0 (totalLength (hatLam P e lam)))).map
        (mkIETFun ((P.rvStep e).lengthsInBottom (hatLam P e lam)) ((P.rvStep e).perm) 0)
        = ν.restrict (Set.Ico 0 (totalLength (hatLam P e lam))) := by
      cases e with
      | false =>
        have hlt : P.lengthsInBottom lam (topCell P.perm)
            < P.lengthsInBottom lam (lastPos n) := by
          rw [e1, e2]; exact he
        rw [totalLength_hatLam_false P lam hlt, ← mkIETFun_rvStep_false_hatLam]
        exact restrict_cut_invariant hlt ν hν
      | true =>
        have hlt : P.lengthsInBottom lam (lastPos n)
            < P.lengthsInBottom lam (topCell P.perm) := by
          rw [e1, e2]; exact he
        rw [totalLength_hatLam_true P lam hlt, ← mkIETFun_rvStep_true_hatLam]
        exact restrict_cut_invariant_true hlt ν hν
    -- the restricted measure agrees with `ν` on the cells
    have hagree (X : Set ℝ) (hX : X ⊆ Set.Ico 0 (totalLength (hatLam P e lam))) :
      ν.restrict (Set.Ico 0 (totalLength (hatLam P e lam))) X = ν X := by
      rw [Measure.restrict_apply' measurableSet_Ico, Set.inter_eq_self_of_subset_left hX]
    have hcell1 (c : α) : cellAt P [e] lam c
        ⊆ Set.Ico 0 (totalLength (hatLam P e lam)) := by
      cases e with
      | false =>
        have hlt : P.lengthsInBottom lam (topCell P.perm)
            < P.lengthsInBottom lam (lastPos n) := by
          rw [e1, e2]; exact he
        rw [cellAt_singleton_false, totalLength_hatLam_false P lam hlt]
        exact cellHat_subset_cut hlt (P.piBottom c)
      | true =>
        have hlt : P.lengthsInBottom lam (lastPos n)
            < P.lengthsInBottom lam (topCell P.perm) := by
          rw [e1, e2]; exact he
        rw [cellAt_singleton_true, totalLength_hatLam_true P lam hlt]
        exact cellHatT_subset_cutT hlt _
    have hcell2 (b : α) : cellAt (P.rvStep e) es (hatLam P e lam) b
        ⊆ Set.Ico 0 (totalLength (hatLam P e lam)) := cellAt_subset_totalLength_le (P.rvStep e) es
            (hatLam P e lam) b
        (totalLength_lamAfter_le (P.rvStep e) (hatLam P e lam) es)
    -- the matrix identity
    have hQ (b : α) :
      (IETDatum₂.Path.Q P (e :: es) a b).toNat
        = ∑ c, (P.rvMat e a c).toNat
            * (IETDatum₂.Path.Q (P.rvStep e) es c b).toNat := by
      rw [pathQ_toNat_eq_Qnat, IETDatum₂.Qnat_cons, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← pathQ_toNat_eq_Qnat]
      rfl
    calc ν (cellOf P lam a)
        = ∑ c, ((P.rvMat e a c).toNat : ℝ≥0∞) * ν (cellAt P [e] lam c) :=
          tower_formula_one_step_comb P lam ν hν e he a
      _ = ∑ c, ((P.rvMat e a c).toNat : ℝ≥0∞)
            * ν.restrict (Set.Ico 0 (totalLength (hatLam P e lam))) (cellAt P [e] lam c) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [hagree _ (hcell1 c)]
      _ = ∑ c, ((P.rvMat e a c).toNat : ℝ≥0∞)
            * (∑ b, ((IETDatum₂.Path.Q (P.rvStep e) es c b).toNat : ℝ≥0∞)
              * ν.restrict (Set.Ico 0 (totalLength (hatLam P e lam)))
                (cellAt (P.rvStep e) es (hatLam P e lam) b)) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [show cellAt P [e] lam c
            = cellOf (P.rvStep e) (hatLam P e lam) c from rfl,
            ih (P.rvStep e) (hatLam P e lam) _ hν' hes c]
      _ = ∑ b, (∑ c, ((P.rvMat e a c).toNat : ℝ≥0∞)
              * (IETDatum₂.Path.Q (P.rvStep e) es c b).toNat)
            * ν.restrict (Set.Ico 0 (totalLength (hatLam P e lam)))
              (cellAt (P.rvStep e) es (hatLam P e lam) b) :=
          sum_mul_sum (fun c => ((P.rvMat e a c).toNat : ℝ≥0∞))
            (fun c b => ((IETDatum₂.Path.Q (P.rvStep e) es c b).toNat : ℝ≥0∞)) _
      _ = ∑ b, (∑ c, ((P.rvMat e a c).toNat : ℝ≥0∞)
              * (IETDatum₂.Path.Q (P.rvStep e) es c b).toNat)
            * ν (cellAt (P.rvStep e) es (hatLam P e lam) b) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hagree _ (hcell2 b)]
      _ = ∑ b, ((IETDatum₂.Path.Q P (e :: es) a b).toNat : ℝ≥0∞)
            * ν (cellAt P (e :: es) lam b) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hQ b]
          push_cast
          rfl

/-- **The level-`n` tower formula** along an *arbitrary* word `γ` for an invariant
measure of the exchange `P.toIET lam`, the per-step hypothesis being the single predicate
`IsRauzyPath P lam γ` (each step is the Rauzy step of the renormalised lengths at that vertex). -/
theorem tower_formula_level_pathQ_any (P : IETDatum₂ α n)
    (lam : α → ℝ≥0) (hlam : lam ∈ simplex α) (μ : Measure ℝ)
    (hμ : μ.map ⇑(P.toIET lam) = μ) (γ : List Bool) (hγ : IsRauzyPath P lam γ) (a : α) :
    μ (cellOf P lam a)
      = ∑ b, ((IETDatum₂.Path.Q P γ a b).toNat : ℝ≥0∞) * μ (cellAt P γ lam b) := by
  have hcoe : ⇑(P.toIET lam) = mkIETFun (P.lengthsInBottom lam) P.perm 0 := by
    rw [IETDatum₂.toIET_eq_mkIET1 P hlam, coe_mkIET1']
  rw [hcoe] at hμ
  exact tower_formula_level_pathQ_mkIETFun P lam μ hμ γ hγ a

end

end IntervalExchange.RauzyVeech

end
