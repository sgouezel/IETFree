/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.InvariantMeasure
public import IETFree.RauzyVeech.LevelN

/-!
# The Rauzy–Veech step of type `true`

Mirror of `IETFree.FirstReturn` for the case `λ botCell < λ (topCell π)`: the induced subinterval
is the prefix `Ico 0 (Λ - λ botCell)`, the return time is `1` except on the upper part of the top
cell where it is `2`, and the return map is the exchange of the step `IETDatum₂.rvStep (toComb π)
true`. -/

@[expose] public section

open MeasureTheory Finset
open scoped BigOperators ENNReal NNReal

namespace TowerTrue

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## 1. The data of the type-`true` step -/

/-- The Rauzy cut of the type-`true` case: `Λ - λ botCell`. -/
def cutT (lam : Fin n → ℝ≥0) : ℝ := Tower.tot lam - (lam Tower.botCell : ℝ)

theorem leftEnd_botCell_eq_cutT (lam : Fin n → ℝ≥0) : leftEnd lam Tower.botCell = cutT lam :=
  Tower.leftEnd_botCell lam

/-- The insertion of the top-last position: the new bottom order of the type-`true` step. -/
def eT (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) := IETDatum₂.insertEquiv (Tower.topCell π)

/-- The permutation of the type-`true` step, in bottom-position coordinates. -/
def piHatT (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) := (eT π).symm.trans π

/-- The new lengths, indexed by letters. -/
def lamH (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) : Fin n → ℝ≥0 :=
  fun a => if a = Tower.topCell π then lam a - lam Tower.botCell else lam a

/-- The new lengths, in the new bottom order. -/
def lamT (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) : Fin n → ℝ≥0 :=
  fun j => lamH π lam ((eT π).symm j)

/-! ## 2. Consequences of the type-`true` hypothesis -/

variable {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}

theorem topCell_ne_botCell_of_lt (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    Tower.topCell π ≠ Tower.botCell :=
  fun h => absurd hlt (by rw [h]; exact lt_irrefl _)

theorem topCell_ne_lastPos (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    Tower.topCell π ≠ IETDatum₂.lastPos n := by
  intro h
  refine topCell_ne_botCell_of_lt hlt ?_
  rw [h]
  rfl

theorem topCell_succ_lt (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    (Tower.topCell π).val + 1 < n := by
  have hne := topCell_ne_lastPos hlt
  have hvl : (Tower.topCell π).val ≠ n - 1 := by
    intro hh
    exact hne (Fin.ext (by rw [IETDatum₂.lastPos_val, hh]))
  have := (Tower.topCell π).isLt
  omega

/-! ## 3. The insertion at the top cell -/

theorem eT_apply_le {a : Fin n} (ha : a.val ≤ (Tower.topCell π).val) :
    eT π a = a :=
  IETDatum₂.insertEquiv_apply_le ha

theorem eT_apply_gt (hlt : lam Tower.botCell < lam (Tower.topCell π)) {a : Fin n}
    (ha : (Tower.topCell π).val < a.val) (hne : a ≠ IETDatum₂.lastPos n) :
    (eT π a).val = a.val + 1 :=
  IETDatum₂.insertEquiv_apply_gt (topCell_succ_lt hlt) ha hne

theorem eT_botCell (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    eT π Tower.botCell = (⟨(Tower.topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n) :=
  IETDatum₂.insertEquiv_lastPos (topCell_succ_lt hlt)

/-! ## 4. The new length vector: elementary values -/

theorem lamH_of_ne {a : Fin n} (ha : a ≠ Tower.topCell π) : lamH π lam a = lam a := by
  rw [lamH]; exact if_neg ha

theorem lamH_topCell : lamH π lam (Tower.topCell π)
    = lam (Tower.topCell π) - lam Tower.botCell := by
  rw [lamH]; exact if_pos rfl

theorem lamT_apply (j : Fin n) : lamT π lam j = lamH π lam ((eT π).symm j) := rfl

theorem eT_symm_of_le {j : Fin n} (hj : j.val ≤ (Tower.topCell π).val) :
    (eT π).symm j = j := by
  have h : eT π j = j := eT_apply_le hj
  have h2 : (eT π).symm (eT π j) = j := Equiv.symm_apply_apply _ _
  rwa [h] at h2

theorem eT_symm_succ (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    (eT π).symm (⟨(Tower.topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      = Tower.botCell := by
  rw [← eT_botCell hlt, Equiv.symm_apply_apply]

theorem eT_symm_of_gt (hlt : lam Tower.botCell < lam (Tower.topCell π)) {j : Fin n}
    (hj : (Tower.topCell π).val + 1 < j.val) :
    (eT π).symm j = (⟨j.val - 1, by have := j.isLt; omega⟩ : Fin n) := by
  set a : Fin n := ⟨j.val - 1, by have := j.isLt; omega⟩ with ha
  have haval : a.val = j.val - 1 := by rw [ha]
  have hne : a ≠ IETDatum₂.lastPos n := by
    intro h
    have h' : a.val = n - 1 := by rw [h, IETDatum₂.lastPos_val]
    omega
  have key : eT π a = j := by
    refine Fin.ext ?_
    rw [eT_apply_gt hlt (by omega) hne, haval]
    have := j.isLt
    omega
  rw [← key, Equiv.symm_apply_apply]

/-! ## 5. The total length of the new vector -/

theorem sum_lamH (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    ∑ a, (lamH π lam a : ℝ) = Tower.tot lam - (lam Tower.botCell : ℝ) := by
  have hterm (a : Fin n) :
    (lamH π lam a : ℝ)
      = (lam a : ℝ) - (if a = Tower.topCell π then (lam Tower.botCell : ℝ) else 0) := by
    by_cases ha : a = Tower.topCell π
    · rw [ha, lamH_topCell, NNReal.coe_sub (le_of_lt hlt), if_pos rfl]
    · rw [lamH_of_ne ha, if_neg ha, sub_zero]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ (Tower.topCell π) (fun _ => (lam Tower.botCell : ℝ))]
  simp only [Finset.mem_univ, if_true]
  rw [Tower.tot]

theorem sum_lamT (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    ∑ j, (lamT π lam j : ℝ) = cutT lam := by
  have h : (∑ j, (lamT π lam j : ℝ)) = ∑ a, (lamH π lam a : ℝ) :=
    Equiv.sum_comp (eT π).symm (fun a => (lamH π lam a : ℝ))
  rw [h, sum_lamH hlt, cutT]

theorem tot_lamT (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    Tower.tot (lamT π lam) = cutT lam := sum_lamT hlt

/-! ## 6. Values of the new vector -/

theorem lamT_of_le {j : Fin n} (hj : j.val ≤ (Tower.topCell π).val) :
    lamT π lam j = lamH π lam j := by
  rw [lamT_apply, eT_symm_of_le hj]

theorem lamT_succ (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    lamT π lam (⟨(Tower.topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      = lam Tower.botCell := by
  rw [lamT_apply, eT_symm_succ hlt, lamH_of_ne (Ne.symm (topCell_ne_botCell_of_lt hlt))]

theorem lamT_of_gt (hlt : lam Tower.botCell < lam (Tower.topCell π)) {j : Fin n}
    (hj : (Tower.topCell π).val + 1 < j.val) :
    lamT π lam j = lam (⟨j.val - 1, by have := j.isLt; omega⟩ : Fin n) := by
  have hlt' := j.isLt
  set a : Fin n := ⟨j.val - 1, by omega⟩ with ha
  have haval : a.val = j.val - 1 := by rw [ha]
  have hap : a ≠ Tower.topCell π := by
    intro h
    have h' : a.val = (Tower.topCell π).val := by rw [h]
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
  have hbp : b ≠ Tower.topCell π := by
    intro h
    rw [h, Tower.topCell_apply] at hb
    exact absurd hb.2 (not_lt.mpr (Tower.le_lastPos (π a)))
  rw [lamH_of_ne hbp]

/-! ## 8. The filters `{a | eT π a < j}` -/

theorem eT_apply_val (π : Equiv.Perm (Fin n)) (a : Fin n) :
    (eT π a).val = if a.val ≤ (Tower.topCell π).val then a.val
      else if a = IETDatum₂.lastPos n then (Tower.topCell π).val + 1 else a.val + 1 := by
  have h := IETDatum₂.trans_insertEquiv_apply_val (1 : Equiv.Perm (Fin n)) (Tower.topCell π)
    (c := IETDatum₂.lastPos n) (by simp) a
  simpa [eT] using h

theorem filter_eT_lt_of_le (_hlt : lam Tower.botCell < lam (Tower.topCell π)) {j : Fin n}
    (hj : j.val ≤ (Tower.topCell π).val) :
    Finset.univ.filter (fun a : Fin n => eT π a < j) = Finset.univ.filter (fun a => a < j) := by
  have hlv : (IETDatum₂.lastPos n).val = n - 1 := IETDatum₂.lastPos_val
  have hjt := j.isLt
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
  rw [eT_apply_val]
  by_cases ha : a.val ≤ (Tower.topCell π).val
  · rw [if_pos ha]
  · rw [if_neg ha]
    by_cases hb : a = IETDatum₂.lastPos n
    · rw [if_pos hb, hb]
      constructor <;> intro h <;> omega
    · rw [if_neg hb]
      constructor <;> intro h <;> omega

theorem filter_eT_lt_succ (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    Finset.univ.filter (fun a : Fin n => eT π a < (⟨(Tower.topCell π).val + 1,
        topCell_succ_lt hlt⟩ : Fin n))
      = Finset.univ.filter (fun a : Fin n => a.val ≤ (Tower.topCell π).val) := by
  have hlv : (IETDatum₂.lastPos n).val = n - 1 := IETDatum₂.lastPos_val
  have hpv : (Tower.topCell π).val < n - 1 := by
    have hne := topCell_ne_lastPos hlt
    have h1 := (Tower.topCell π).isLt
    have h2 : (Tower.topCell π).val ≠ n - 1 := by
      intro hh
      exact hne (Fin.ext (by rw [IETDatum₂.lastPos_val, hh]))
    omega
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
  rw [eT_apply_val]
  by_cases ha : a.val ≤ (Tower.topCell π).val
  · rw [if_pos ha]; omega
  · rw [if_neg ha]
    by_cases hb : a = IETDatum₂.lastPos n
    · rw [if_pos hb, hb]
      have hle : (Tower.topCell π).val ≤ (IETDatum₂.lastPos n).val :=
        Fin.le_def.mp (Tower.le_lastPos (Tower.topCell π))
      have hpv := topCell_succ_lt hlt
      omega
    · rw [if_neg hb]; omega

theorem filter_eT_lt_of_gt (_hlt : lam Tower.botCell < lam (Tower.topCell π)) {j : Fin n}
    (hj : (Tower.topCell π).val + 1 < j.val) :
    Finset.univ.filter (fun a : Fin n => eT π a < j)
      = insert Tower.botCell (Finset.univ.filter (fun a : Fin n => a.val < j.val - 1)) := by
  have hlv : (IETDatum₂.lastPos n).val = n - 1 := IETDatum₂.lastPos_val
  have hjt := j.isLt
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def]
  rw [eT_apply_val]
  by_cases ha : a.val ≤ (Tower.topCell π).val
  · rw [if_pos ha]
    exact ⟨fun _ => Or.inr (by omega), fun _ => by omega⟩
  · rw [if_neg ha]
    by_cases hb : a = IETDatum₂.lastPos n
    · rw [if_pos hb]
      exact ⟨fun _ => Or.inl hb, fun _ => by omega⟩
    · rw [if_neg hb]
      constructor
      · intro h; exact Or.inr (by omega)
      · rintro (h | h)
        · exact absurd h hb
        · omega

/-! ## 9. The left end of the new cells -/

theorem leftEnd_lamT_of_le (hlt : lam Tower.botCell < lam (Tower.topCell π)) {j : Fin n}
    (hj : j.val ≤ (Tower.topCell π).val) : leftEnd (lamT π lam) j = leftEnd lam j := by
  have hL : leftEnd (lamT π lam) j
      = ∑ a ∈ Finset.univ.filter (fun a : Fin n => eT π a < j), (lamH π lam a : ℝ) :=
    leftEnd_comp_symm (eT π) (lamH π lam) j
  rw [hL, filter_eT_lt_of_le hlt hj, leftEnd]
  refine Finset.sum_congr rfl fun a ha => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  rw [lamH_of_ne (by intro h; rw [h] at ha; omega)]

theorem leftEnd_lamT_succ (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    leftEnd (lamT π lam) (⟨(Tower.topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      = upperEnd lam (Tower.topCell π) - (lam Tower.botCell : ℝ) := by
  have hL : leftEnd (lamT π lam) (⟨(Tower.topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      = ∑ a ∈ Finset.univ.filter (fun a : Fin n => eT π a < (⟨(Tower.topCell π).val + 1,
          topCell_succ_lt hlt⟩ : Fin n)), (lamH π lam a : ℝ) :=
    leftEnd_comp_symm (eT π) (lamH π lam) _
  rw [hL, filter_eT_lt_succ hlt]
  have hins : Finset.univ.filter (fun a : Fin n => a.val ≤ (Tower.topCell π).val)
      = insert (Tower.topCell π) (Finset.univ.filter (fun a : Fin n => a < Tower.topCell π)) := by
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
  have hterms : (∑ a ∈ Finset.univ.filter (fun a : Fin n => a < Tower.topCell π),
        (lamH π lam a : ℝ))
      = ∑ a ∈ Finset.univ.filter (fun a : Fin n => a < Tower.topCell π), (lam a : ℝ) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [lamH_of_ne (ne_of_lt ha)]
  rw [hins, Finset.sum_insert (by simp), lamH_topCell, NNReal.coe_sub (le_of_lt hlt), hterms,
    upperEnd_eq, leftEnd]
  ring

theorem leftEnd_lamT_of_gt (hlt : lam Tower.botCell < lam (Tower.topCell π)) {j : Fin n}
    (hj : (Tower.topCell π).val + 1 < j.val) :
    leftEnd (lamT π lam) j = leftEnd lam (⟨j.val - 1, by have := j.isLt; omega⟩ : Fin n) := by
  have hlt' := j.isLt
  set i : Fin n := ⟨j.val - 1, by omega⟩ with hi
  have hival : i.val = j.val - 1 := by rw [hi]
  have hb : Tower.botCell ∉ Finset.univ.filter (fun a : Fin n => a.val < j.val - 1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    have hbv : Tower.botCell.val = n - 1 := rfl
    omega
  have hp : Tower.topCell π ∈ Finset.univ.filter (fun a : Fin n => a.val < j.val - 1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hL : leftEnd (lamT π lam) j
      = ∑ a ∈ Finset.univ.filter (fun a : Fin n => eT π a < j), (lamH π lam a : ℝ) :=
    leftEnd_comp_symm (eT π) (lamH π lam) j
  rw [hL, filter_eT_lt_of_gt hlt hj, Finset.sum_insert hb,
    lamH_of_ne (Ne.symm (topCell_ne_botCell_of_lt hlt))]
  have hterm (a : Fin n) :
    (lamH π lam a : ℝ)
      = (lam a : ℝ) - (if a = Tower.topCell π then (lam Tower.botCell : ℝ) else 0) := by
    by_cases ha : a = Tower.topCell π
    · rw [ha, lamH_topCell, NNReal.coe_sub (le_of_lt hlt), if_pos rfl]
    · rw [lamH_of_ne ha, if_neg ha, sub_zero]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_sub_distrib,
    Finset.sum_ite_eq' (Finset.univ.filter (fun a : Fin n => a.val < j.val - 1))
      (Tower.topCell π) (fun _ => (lam Tower.botCell : ℝ)), if_pos hp]
  have hLe : Finset.univ.filter (fun a : Fin n => a.val < j.val - 1)
      = Finset.univ.filter (fun a : Fin n => a < i) := by
    rw [← hival]
    simp only [Fin.lt_def]
  rw [hLe, leftEnd]
  ring

/-! ## 10. The dynamics of the first return to `Ico 0 (cutT lam)` -/

theorem cutT_le_tot (lam : Fin n → ℝ≥0) : cutT lam ≤ Tower.tot lam := by
  rw [cutT]; exact sub_le_self _ (by positivity)

theorem mem_Ico_tot_of_mem_cutT {y : ℝ} (hy : y ∈ Set.Ico 0 (cutT lam)) :
    y ∈ Set.Ico 0 (Tower.tot lam) :=
  ⟨hy.1, lt_of_lt_of_le hy.2 (cutT_le_tot lam)⟩

theorem cutT_pos (hlt : lam Tower.botCell < lam (Tower.topCell π)) : 0 < cutT lam := by
  have h1 := NNReal.coe_lt_coe.mpr hlt
  have h2 := Tower.single_le_tot lam (Tower.topCell π)
  rw [cutT]; linarith

theorem idx_mem_cutT {y : ℝ} (hy : y ∈ Set.Ico 0 (cutT lam)) :
    leftEnd lam (idx lam y hy.1) ≤ y ∧ y < upperEnd lam (idx lam y hy.1) :=
  ⟨idx_mem lam y hy.1, lt_upperEnd_idx lam (mem_Ico_tot_of_mem_cutT hy)⟩

theorem idx_ne_botCell {y : ℝ} (hy : y ∈ Set.Ico 0 (cutT lam)) :
    idx lam y hy.1 ≠ Tower.botCell := by
  intro h
  have h1 := (idx_mem_cutT hy).1
  rw [h, leftEnd_botCell_eq_cutT] at h1
  linarith [hy.2]

theorem exch_apply_cutT {y : ℝ} (hy : y ∈ Set.Ico 0 (cutT lam)) :
    Tower.exch π lam y = y + translationVector π lam (idx lam y hy.1) :=
  Tower.exch_of_mem π lam (mem_Ico_tot_of_mem_cutT hy)

theorem translationVector_topCell :
    translationVector π lam (Tower.topCell π)
      = Tower.tot lam - (lam (Tower.topCell π) : ℝ) - leftEnd lam (Tower.topCell π) := by
  rw [translationVector, Tower.imageLeft_topCell]

/-- The split point of the top cell: the part of the top cell above it returns in two steps. -/
def splitT (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) : ℝ :=
  leftEnd lam (Tower.topCell π) + ((lam (Tower.topCell π) : ℝ) - (lam Tower.botCell : ℝ))

theorem imageUpper_le_cutT (hlt : lam Tower.botCell < lam (Tower.topCell π)) {i : Fin n}
    (hi : i ≠ Tower.topCell π) : Tower.imageUpper π lam i ≤ cutT lam := by
  refine le_trans (Tower.imageUpper_le_tot π lam hi) ?_
  have h := NNReal.coe_lt_coe.mpr hlt
  rw [cutT]; linarith

/-- **A point outside the top cell returns in one step.** -/
theorem exch_mem_cutT_of_ne_top (hlt : lam Tower.botCell < lam (Tower.topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 ≠ Tower.topCell π) :
    Tower.exch π lam y ∈ Set.Ico 0 (cutT lam) := by
  rw [exch_apply_cutT hy]
  obtain ⟨h1, h2⟩ := idx_mem_cutT hy
  have hupper : Tower.imageUpper π lam (idx lam y hy.1) ≤ cutT lam := imageUpper_le_cutT hlt hi
  have htv : translationVector π lam (idx lam y hy.1)
      = imageLeft π lam (idx lam y hy.1) - leftEnd lam (idx lam y hy.1) := rfl
  have hnn : 0 ≤ imageLeft π lam (idx lam y hy.1) := imageLeft_nonneg _ _ _
  have hueq : Tower.imageUpper π lam (idx lam y hy.1)
      = imageLeft π lam (idx lam y hy.1) + (lam (idx lam y hy.1) : ℝ) :=
    Tower.imageUpper_eq π lam _
  have hU : upperEnd lam (idx lam y hy.1)
      = leftEnd lam (idx lam y hy.1) + (lam (idx lam y hy.1) : ℝ) := upperEnd_eq _ _
  constructor
  · rw [htv]; linarith
  · rw [htv]; linarith

/-- **A point of the lower part of the top cell returns in one step.** -/
theorem exch_mem_cutT_of_top_low (hlt : lam Tower.botCell < lam (Tower.topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 = Tower.topCell π)
    (hlo : y < splitT π lam) :
    Tower.exch π lam y ∈ Set.Ico 0 (cutT lam) := by
  rw [exch_apply_cutT hy, hi, translationVector_topCell]
  have h1 := (idx_mem_cutT hy).1
  rw [hi] at h1
  have hlt' := NNReal.coe_lt_coe.mpr hlt
  have hnn : 0 ≤ imageLeft π lam (Tower.topCell π) := imageLeft_nonneg _ _ _
  have himg : imageLeft π lam (Tower.topCell π)
      = Tower.tot lam - (lam (Tower.topCell π) : ℝ) := Tower.imageLeft_topCell π lam
  have hsp : splitT π lam = leftEnd lam (Tower.topCell π)
      + ((lam (Tower.topCell π) : ℝ) - (lam Tower.botCell : ℝ)) := rfl
  constructor
  · linarith
  · rw [cutT]; linarith

/-- **A point of the upper part of the top cell leaves the base in one step.** -/
theorem exch_mem_Ico_cutT_tot_of_top_high (hlt : lam Tower.botCell < lam (Tower.topCell π))
    {y : ℝ} (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 = Tower.topCell π)
    (hhi : splitT π lam ≤ y) :
    Tower.exch π lam y ∈ Set.Ico (cutT lam) (Tower.tot lam) := by
  rw [exch_apply_cutT hy, hi, translationVector_topCell]
  have h2 : y < leftEnd lam (Tower.topCell π) + (lam (Tower.topCell π) : ℝ) := by
    have h := lt_upperEnd_idx lam (mem_Ico_tot_of_mem_cutT hy)
    rwa [upperEnd_eq, hi] at h
  have hlt' := NNReal.coe_lt_coe.mpr hlt
  have himg : imageLeft π lam (Tower.topCell π)
      = Tower.tot lam - (lam (Tower.topCell π) : ℝ) := Tower.imageLeft_topCell π lam
  have hsp : splitT π lam = leftEnd lam (Tower.topCell π)
      + ((lam (Tower.topCell π) : ℝ) - (lam Tower.botCell : ℝ)) := rfl
  constructor
  · rw [cutT]; linarith
  · linarith

/-- On the upper part of the top cell the image lands in the rightmost domain cell. -/
theorem idx_exch_of_idx_topCell (hlt : lam Tower.botCell < lam (Tower.topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 = Tower.topCell π)
    (hhi : splitT π lam ≤ y) :
    idx lam (Tower.exch π lam y)
      (le_trans (le_of_lt (cutT_pos hlt)) (exch_mem_Ico_cutT_tot_of_top_high hlt hy hi hhi).1)
      = Tower.botCell := by
  obtain ⟨h1, h2⟩ := exch_mem_Ico_cutT_tot_of_top_high hlt hy hi hhi
  refine idx_eq lam ⟨le_trans (le_of_lt (cutT_pos hlt)) h1, h2⟩ ?_ ?_
  · rw [leftEnd_botCell_eq_cutT]; exact h1
  · rw [Tower.upperEnd_botCell]; exact h2

/-- **The second iterate of a point of the upper part of the top cell.** -/
theorem exch_exch_eq_true (hlt : lam Tower.botCell < lam (Tower.topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 = Tower.topCell π)
    (hhi : splitT π lam ≤ y) :
    Tower.exch π lam (Tower.exch π lam y)
      = Tower.exch π lam y + translationVector π lam Tower.botCell := by
  have hT := exch_mem_Ico_cutT_tot_of_top_high hlt hy hi hhi
  have hidx := idx_exch_of_idx_topCell hlt hy hi hhi
  have hT' : Tower.exch π lam y ∈ Set.Ico 0 (Tower.tot lam) :=
    ⟨le_trans (le_of_lt (cutT_pos hlt)) hT.1, hT.2⟩
  rw [Tower.exch_of_mem π lam hT', hidx]

/-! ## 11. The return time -/

/-- The return time to `Ico 0 (cutT lam)`: `1` unless the first iterate leaves the base. -/
def retT (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (y : ℝ) : ℕ :=
  if Tower.exch π lam y ∈ Set.Ico 0 (cutT lam) then 1 else 2

theorem retT_of_mem {y : ℝ} (h : Tower.exch π lam y ∈ Set.Ico 0 (cutT lam)) :
    retT π lam y = 1 := by
  rw [retT]; exact if_pos h

theorem retT_of_not_mem {y : ℝ} (h : Tower.exch π lam y ∉ Set.Ico 0 (cutT lam)) :
    retT π lam y = 2 := by
  rw [retT]; exact if_neg h

/-! ## 12. The cells of the new arrangement -/

/-- The cells of the return exchange, in the new bottom order. -/
def cellHatT (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (j : Fin n) : Set ℝ :=
  Set.Ico (leftEnd (lamT π lam) j) (upperEnd (lamT π lam) j)

/-- The successor of a position. -/
def succFin {n : ℕ} (i : Fin n) (h : i.val + 1 < n) : Fin n := ⟨i.val + 1, h⟩

omit [NeZero n] in
@[simp] theorem succFin_val {i : Fin n} (h : i.val + 1 < n) : (succFin i h).val = i.val + 1 := rfl

theorem upperEnd_lamT_of_lt (hlt : lam Tower.botCell < lam (Tower.topCell π)) {j : Fin n}
    (hj : j.val < (Tower.topCell π).val) : upperEnd (lamT π lam) j = upperEnd lam j := by
  have hne : j ≠ Tower.topCell π := by
    intro h; rw [h] at hj; exact absurd hj (lt_irrefl _)
  rw [upperEnd_eq, upperEnd_eq, leftEnd_lamT_of_le hlt (le_of_lt hj), lamT_of_le (le_of_lt hj),
    lamH_of_ne hne]

theorem leftEnd_lamT_succ_of_gt (hlt : lam Tower.botCell < lam (Tower.topCell π)) {i : Fin n}
    (hi : (Tower.topCell π).val < i.val) (h : i.val + 1 < n) :
    leftEnd (lamT π lam) (succFin i h) = leftEnd lam i := by
  have h2 : (Tower.topCell π).val + 1 < (succFin i h).val := by
    rw [succFin_val]; omega
  have h3 := leftEnd_lamT_of_gt hlt (j := succFin i h) h2
  rw [h3]
  congr 1

theorem upperEnd_lamT_succ_of_gt (hlt : lam Tower.botCell < lam (Tower.topCell π)) {i : Fin n}
    (hi : (Tower.topCell π).val < i.val) (h : i.val + 1 < n) :
    upperEnd (lamT π lam) (succFin i h) = upperEnd lam i := by
  have h2 : (Tower.topCell π).val + 1 < (succFin i h).val := by
    rw [succFin_val]; omega
  rw [upperEnd_eq, upperEnd_eq, leftEnd_lamT_succ_of_gt hlt hi h,
    lamT_of_gt hlt (j := succFin i h) h2]
  congr 1

theorem upperEnd_lamT_top (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    upperEnd (lamT π lam) (Tower.topCell π) = splitT π lam := by
  rw [upperEnd_eq, leftEnd_lamT_of_le hlt (le_refl _), lamT_of_le (le_refl _), lamH_topCell,
    NNReal.coe_sub (le_of_lt hlt), splitT]

theorem leftEnd_lamT_succ_eq_splitT (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    leftEnd (lamT π lam)
      (⟨(Tower.topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n) = splitT π lam := by
  rw [leftEnd_lamT_succ hlt, splitT, upperEnd_eq]
  ring

theorem upperEnd_lamT_succ_eq (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    upperEnd (lamT π lam) (⟨(Tower.topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      = upperEnd lam (Tower.topCell π) := by
  rw [upperEnd_eq, leftEnd_lamT_succ hlt, lamT_succ hlt, upperEnd_eq]
  ring

/-! ## 13. The index of a point in the new arrangement -/

theorem mem_Ico_sum_lamT (hlt : lam Tower.botCell < lam (Tower.topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) : y ∈ Set.Ico 0 (∑ j, (lamT π lam j : ℝ)) :=
  ⟨hy.1, by rw [sum_lamT hlt]; exact hy.2⟩

theorem idx_lamT_of_lt (hlt : lam Tower.botCell < lam (Tower.topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam))
    (hi : (idx lam y hy.1).val < (Tower.topCell π).val) :
    idx (lamT π lam) y hy.1 = idx lam y hy.1 := by
  have hmem := idx_mem_cutT hy
  refine idx_eq (lamT π lam) (mem_Ico_sum_lamT hlt hy) ?_ ?_
  · rw [leftEnd_lamT_of_le hlt (le_of_lt hi)]; exact hmem.1
  · rw [upperEnd_lamT_of_lt hlt hi]; exact hmem.2

theorem idx_lamT_of_top_low (hlt : lam Tower.botCell < lam (Tower.topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 = Tower.topCell π)
    (hlo : y < splitT π lam) :
    idx (lamT π lam) y hy.1 = Tower.topCell π := by
  have hmem := idx_mem_cutT hy
  rw [hi] at hmem
  refine idx_eq (lamT π lam) (mem_Ico_sum_lamT hlt hy) ?_ ?_
  · rw [leftEnd_lamT_of_le hlt (le_refl _)]; exact hmem.1
  · rw [upperEnd_lamT_top hlt]; exact hlo

theorem idx_lamT_of_top_high (hlt : lam Tower.botCell < lam (Tower.topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 = Tower.topCell π)
    (hhi : splitT π lam ≤ y) :
    idx (lamT π lam) y hy.1
      = (⟨(Tower.topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n) := by
  have hmem := idx_mem_cutT hy
  rw [hi] at hmem
  have h2 : y < leftEnd lam (Tower.topCell π) + (lam (Tower.topCell π) : ℝ) := by
    have h := lt_upperEnd_idx lam (mem_Ico_tot_of_mem_cutT hy)
    rwa [upperEnd_eq, hi] at h
  refine idx_eq (lamT π lam) (mem_Ico_sum_lamT hlt hy) ?_ ?_
  · rw [leftEnd_lamT_succ_eq_splitT hlt]; exact hhi
  · rw [upperEnd_lamT_succ_eq hlt, upperEnd_eq]; exact h2

theorem idx_lamT_of_gt (hlt : lam Tower.botCell < lam (Tower.topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam))
    (hi : (Tower.topCell π).val < (idx lam y hy.1).val) :
    idx (lamT π lam) y hy.1 = succFin (idx lam y hy.1) (by
      have hib := idx_ne_botCell hy
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

theorem translationVector_piHatT_of_lt (hlt : lam Tower.botCell < lam (Tower.topCell π))
    {i : Fin n} (hi : i.val < (Tower.topCell π).val) :
    translationVector (piHatT π) (lamT π lam) i = translationVector π lam i := by
  rw [translationVector, translationVector, imageLeft_lamT, eT_symm_of_le (le_of_lt hi),
    leftEnd_lamT_of_le hlt (le_of_lt hi)]

theorem translationVector_piHatT_top (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    translationVector (piHatT π) (lamT π lam) (Tower.topCell π)
      = translationVector π lam (Tower.topCell π) := by
  rw [translationVector, translationVector, imageLeft_lamT, eT_symm_of_le (le_refl _),
    leftEnd_lamT_of_le hlt (le_refl _)]

theorem translationVector_piHatT_succ (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    translationVector (piHatT π) (lamT π lam)
        (⟨(Tower.topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      = translationVector π lam (Tower.topCell π) + translationVector π lam Tower.botCell := by
  rw [translationVector, translationVector, translationVector, imageLeft_lamT, eT_symm_succ hlt,
    leftEnd_lamT_succ_eq_splitT hlt, splitT, Tower.imageLeft_topCell, leftEnd_botCell_eq_cutT]
  simp only [cutT]
  ring

theorem translationVector_piHatT_succ_of_gt (hlt : lam Tower.botCell < lam (Tower.topCell π))
    {i : Fin n} (hi : (Tower.topCell π).val < i.val) (h : i.val + 1 < n) :
    translationVector (piHatT π) (lamT π lam) (succFin i h) = translationVector π lam i := by
  have h2 : (Tower.topCell π).val + 1 < (succFin i h).val := by rw [succFin_val]; omega
  have h3 : (eT π).symm (succFin i h)
      = (⟨(succFin i h).val - 1, by have := (succFin i h).isLt; omega⟩ : Fin n) :=
    eT_symm_of_gt hlt h2
  have h4 : (⟨(succFin i h).val - 1, by have := (succFin i h).isLt; omega⟩ : Fin n) = i := by
    refine Fin.ext ?_
    change (succFin i h).val - 1 = i.val
    rw [succFin_val]
    omega
  rw [translationVector, translationVector, imageLeft_lamT, h3, h4,
    leftEnd_lamT_succ_of_gt hlt hi h]

/-! ## 15. The return map is the exchange of the step -/

theorem mkIETFun_lamT_of_lt (hlt : lam Tower.botCell < lam (Tower.topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam))
    (hi : (idx lam y hy.1).val < (Tower.topCell π).val) :
    mkIETFun (lamT π lam) (piHatT π) 0 y = Tower.exch π lam y := by
  rw [Tower.mkIETFun_zero_of_mem (mem_Ico_sum_lamT hlt hy), exch_apply_cutT hy,
    idx_lamT_of_lt hlt hy hi, translationVector_piHatT_of_lt hlt hi]

theorem mkIETFun_lamT_of_top_low (hlt : lam Tower.botCell < lam (Tower.topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 = Tower.topCell π)
    (hlo : y < splitT π lam) :
    mkIETFun (lamT π lam) (piHatT π) 0 y = Tower.exch π lam y := by
  rw [Tower.mkIETFun_zero_of_mem (mem_Ico_sum_lamT hlt hy), exch_apply_cutT hy,
    idx_lamT_of_top_low hlt hy hi hlo, hi, translationVector_piHatT_top hlt]

theorem mkIETFun_lamT_of_top_high (hlt : lam Tower.botCell < lam (Tower.topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) (hi : idx lam y hy.1 = Tower.topCell π)
    (hhi : splitT π lam ≤ y) :
    mkIETFun (lamT π lam) (piHatT π) 0 y
      = Tower.exch π lam (Tower.exch π lam y) := by
  rw [Tower.mkIETFun_zero_of_mem (mem_Ico_sum_lamT hlt hy),
    idx_lamT_of_top_high hlt hy hi hhi, exch_exch_eq_true hlt hy hi hhi, exch_apply_cutT hy, hi,
    translationVector_piHatT_succ hlt]
  ring

theorem mkIETFun_lamT_of_gt (hlt : lam Tower.botCell < lam (Tower.topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam))
    (hi : (Tower.topCell π).val < (idx lam y hy.1).val) :
    mkIETFun (lamT π lam) (piHatT π) 0 y = Tower.exch π lam y := by
  have hib := idx_ne_botCell hy
  have hibv : (idx lam y hy.1).val ≠ n - 1 := by
    intro h
    exact hib (Fin.ext (by rw [h]; rfl))
  have h : (idx lam y hy.1).val + 1 < n := by
    have := (idx lam y hy.1).isLt
    omega
  rw [Tower.mkIETFun_zero_of_mem (mem_Ico_sum_lamT hlt hy),
    idx_lamT_of_gt hlt hy hi, exch_apply_cutT hy, translationVector_piHatT_succ_of_gt hlt hi h]

/-- **Type `true`**: the first return map of the exchange to `Ico 0 (Λ - λ botCell)` is the exchange
of the lengths `lamT` and the permutation `piHatT`, i.e. the Rauzy–Veech step of type `true`. -/
theorem firstReturnT_eq (hlt : lam Tower.botCell < lam (Tower.topCell π)) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (cutT lam)) :
    (Tower.exch π lam)^[retT π lam y] y = mkIETFun (lamT π lam) (piHatT π) 0 y := by
  by_cases h : idx lam y hy.1 = Tower.topCell π
  · by_cases hlo : y < splitT π lam
    · rw [retT_of_mem (exch_mem_cutT_of_top_low hlt hy h hlo), Function.iterate_one,
        mkIETFun_lamT_of_top_low hlt hy h hlo]
    · have hhi : splitT π lam ≤ y := le_of_not_gt hlo
      have hnot : Tower.exch π lam y ∉ Set.Ico 0 (cutT lam) := by
        intro hc
        have hge := (exch_mem_Ico_cutT_tot_of_top_high hlt hy h hhi).1
        linarith [hc.2]
      rw [retT_of_not_mem hnot, Tower.iterate_two_eq, mkIETFun_lamT_of_top_high hlt hy h hhi]
  · by_cases hi : (idx lam y hy.1).val < (Tower.topCell π).val
    · rw [retT_of_mem (exch_mem_cutT_of_ne_top hlt hy h), Function.iterate_one,
        mkIETFun_lamT_of_lt hlt hy hi]
    · have hi' : (Tower.topCell π).val < (idx lam y hy.1).val := by
        have hle : (Tower.topCell π).val ≤ (idx lam y hy.1).val := by
          by_contra hcon
          exact hi (by omega)
        have hne : (Tower.topCell π).val ≠ (idx lam y hy.1).val := by
          intro hc
          exact h (Fin.ext hc).symm
        omega
      rw [retT_of_mem (exch_mem_cutT_of_ne_top hlt hy h), Function.iterate_one,
        mkIETFun_lamT_of_gt hlt hy hi']

/-! ## 17. The cells of the return exchange and the return time on them -/

theorem measurableSet_cellHatT (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (β : Fin n) :
    MeasurableSet (cellHatT π lam β) := measurableSet_Ico

theorem cellHatT_subset_cutT (hlt : lam Tower.botCell < lam (Tower.topCell π)) (β : Fin n) :
    cellHatT π lam β ⊆ Set.Ico 0 (cutT lam) := by
  intro y hy
  refine ⟨le_trans (leftEnd_nonneg _ _) hy.1, ?_⟩
  refine lt_of_lt_of_le hy.2 ?_
  rw [← tot_lamT hlt]
  exact upperEnd_le_total _ _

theorem iUnion_cellHatT (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    Set.iUnion (fun β : Fin n => cellHatT π lam β) = Set.Ico 0 (cutT lam) := by
  ext y
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨β, hβ⟩
    exact cellHatT_subset_cutT hlt β hβ
  · intro hy
    exact ⟨idx (lamT π lam) y hy.1, idx_mem _ _ _, lt_upperEnd_idx _ (mem_Ico_sum_lamT hlt hy)⟩

theorem cellHatT_of_lt (hlt : lam Tower.botCell < lam (Tower.topCell π)) {j : Fin n}
    (hj : j.val < (Tower.topCell π).val) :
    cellHatT π lam j = Set.Ico (leftEnd lam j) (upperEnd lam j) := by
  rw [cellHatT, leftEnd_lamT_of_le hlt (le_of_lt hj), upperEnd_lamT_of_lt hlt hj]

theorem cellHatT_top (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    cellHatT π lam (Tower.topCell π)
      = Set.Ico (leftEnd lam (Tower.topCell π)) (splitT π lam) := by
  rw [cellHatT, leftEnd_lamT_of_le hlt (le_refl _), upperEnd_lamT_top hlt]

theorem cellHatT_succ (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    cellHatT π lam (⟨(Tower.topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      = Set.Ico (splitT π lam) (upperEnd lam (Tower.topCell π)) := by
  rw [cellHatT, leftEnd_lamT_succ_eq_splitT hlt, upperEnd_lamT_succ_eq hlt]

theorem cellHatT_of_gt (hlt : lam Tower.botCell < lam (Tower.topCell π)) {i : Fin n}
    (hi : (Tower.topCell π).val < i.val) (h : i.val + 1 < n) :
    cellHatT π lam (succFin i h) = Set.Ico (leftEnd lam i) (upperEnd lam i) := by
  rw [cellHatT, leftEnd_lamT_succ_of_gt hlt hi h, upperEnd_lamT_succ_of_gt hlt hi h]

/-- The multiplicity of the level-one tower in the type-`true` case. -/
def returnBT (π : Equiv.Perm (Fin n)) (β : Fin n) : ℕ :=
  if β = eT π Tower.botCell then 2 else 1

theorem returnBT_eq_two : returnBT π (eT π Tower.botCell) = 2 := by
  rw [returnBT]; exact if_pos rfl

theorem returnBT_pos (π : Equiv.Perm (Fin n)) (β : Fin n) : 0 < returnBT π β := by
  rw [returnBT]; split <;> omega

theorem returnBT_le_two (π : Equiv.Perm (Fin n)) (β : Fin n) : returnBT π β ≤ 2 := by
  rw [returnBT]; split <;> omega

/-- **The return time on each cell of the return exchange.** -/
theorem retT_eq_returnBT (hlt : lam Tower.botCell < lam (Tower.topCell π)) {β : Fin n} {y : ℝ}
    (hy : y ∈ cellHatT π lam β) : retT π lam y = returnBT π β := by
  have hlt' := NNReal.coe_lt_coe.mpr hlt
  have hyc : y ∈ Set.Ico 0 (cutT lam) := cellHatT_subset_cutT hlt β hy
  have hsum : y ∈ Set.Ico 0 (Tower.tot lam) := mem_Ico_tot_of_mem_cutT hyc
  have hidxH : idx (lamT π lam) y hyc.1 = β := by
    refine idx_eq (lamT π lam) (mem_Ico_sum_lamT hlt hyc) hy.1 hy.2
  by_cases hβ : β = eT π Tower.botCell
  · rw [returnBT, if_pos hβ]
    have hβv : β = (⟨(Tower.topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n) := by
      rw [hβ, eT_botCell hlt]
    have hy' : y ∈ Set.Ico (splitT π lam) (upperEnd lam (Tower.topCell π)) := by
      rw [← cellHatT_succ hlt, ← hβv]; exact hy
    have hidx : idx lam y hyc.1 = Tower.topCell π := by
      refine idx_eq lam hsum ?_ ?_
      · have h1 : leftEnd lam (Tower.topCell π) ≤ splitT π lam := by
          rw [splitT]; linarith
        linarith [hy'.1]
      · rw [upperEnd_eq] at hy' ⊢; exact hy'.2
    have hnot : Tower.exch π lam y ∉ Set.Ico 0 (cutT lam) := by
      intro hc
      have hge := (exch_mem_Ico_cutT_tot_of_top_high hlt hyc hidx hy'.1).1
      linarith [hc.2]
    exact retT_of_not_mem hnot
  · rw [returnBT, if_neg hβ]
    have hmem : Tower.exch π lam y ∈ Set.Ico 0 (cutT lam) := by
      rcases lt_or_ge (Tower.topCell π).val β.val with hgt | hle
      · -- β above the top cell: it is the successor of a cell `i > p`
        have hβ2 : β.val ≠ (Tower.topCell π).val + 1 := by
          intro hc
          exact hβ (by
            rw [eT_botCell hlt]
            exact Fin.ext (by rw [hc]))
        have hβ3 : (Tower.topCell π).val + 1 < β.val := by omega
        set i : Fin n := ⟨β.val - 1, by have := β.isLt; omega⟩ with hidef
        have hival : i.val = β.val - 1 := by rw [hidef]
        have hi : (Tower.topCell π).val < i.val := by rw [hival]; omega
        have hβi : β = succFin i (by rw [hival]; have := β.isLt; omega) := by
          refine Fin.ext ?_
          rw [succFin_val, hival]
          have := β.isLt
          omega
        have hy' : y ∈ Set.Ico (leftEnd lam i) (upperEnd lam i) := by
          rw [← cellHatT_of_gt hlt hi (by rw [hival]; have := β.isLt; omega), ← hβi]
          exact hy
        have hidx : idx lam y hyc.1 = i := idx_eq lam hsum hy'.1 hy'.2
        exact exch_mem_cutT_of_ne_top hlt hyc (by rw [hidx]; exact ne_of_gt hi)
      · rcases lt_or_eq_of_le hle with hlt2 | heq2
        · -- β below the top cell
          have hy' : y ∈ Set.Ico (leftEnd lam β) (upperEnd lam β) := by
            rw [← cellHatT_of_lt hlt hlt2]; exact hy
          have hidx : idx lam y hyc.1 = β := idx_eq lam hsum hy'.1 hy'.2
          exact exch_mem_cutT_of_ne_top hlt hyc (by rw [hidx]; exact ne_of_lt hlt2)
        · -- β is the top cell
          have hβp : β = Tower.topCell π := Fin.ext heq2
          have hy' : y ∈ Set.Ico (leftEnd lam (Tower.topCell π)) (splitT π lam) := by
            rw [← cellHatT_top hlt, ← hβp]; exact hy
          have hidx : idx lam y hyc.1 = Tower.topCell π := by
            refine idx_eq lam hsum hy'.1 ?_
            rw [upperEnd_eq]
            have h2 := hy'.2
            rw [splitT] at h2
            linarith
          exact exch_mem_cutT_of_top_low hlt hyc hidx hy'.2
    exact retT_of_mem hmem

/-! ## 18. Induced invariance in the type-`true` case -/

theorem pairwiseDisjoint_cellHatT (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n))) (cellHatT π lam) := by
  intro β _ β' _ hne
  exact Tower.disjoint_cell (lamT π lam) hne

theorem image_cutT_self (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    Tower.exch (piHatT π) (lamT π lam) '' Set.Ico 0 (cutT lam) = Set.Ico 0 (cutT lam) := by
  have h := Tower.image_Ico_tot (piHatT π) (lamT π lam)
  rw [show Tower.tot (lamT π lam) = cutT lam from tot_lamT hlt] at h
  exact h

/-- **Induced invariance, type `true`.** If `μ` is invariant under `T = exch π lam` and `λ botCell <
λ (topCell π)`, then the restriction of `μ` to `Ico 0 (Λ - λ botCell)` is invariant under the
first-return exchange `exch (piHatT π) (lamT π lam)`. -/
theorem restrict_cut_invariant_true (hlt : lam Tower.botCell < lam (Tower.topCell π))
    (μ : Measure ℝ) (hμ : μ.map (Tower.exch π lam) = μ) :
    (μ.restrict (Set.Ico 0 (cutT lam))).map (Tower.exch (piHatT π) (lamT π lam))
      = μ.restrict (Set.Ico 0 (cutT lam)) := by
  have hmeasTH : Measurable (Tower.exch (piHatT π) (lamT π lam)) := Tower.measurable_exch _ _
  have hIm : Tower.exch (piHatT π) (lamT π lam) '' Set.Ico 0 (cutT lam)
      = Set.Ico 0 (cutT lam) := image_cutT_self hlt
  have hcell : ∀ β : Fin n, MeasurableSet (cellHatT π lam β) := measurableSet_cellHatT π lam
  have hmain (A : Set ℝ) (hAI : A ⊆ Set.Ico 0 (cutT lam)) (hA : MeasurableSet A) :
    μ (Tower.exch (piHatT π) (lamT π lam) '' A) = μ A := by
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
    have hmeasInt : ∀ β ∈ (Finset.univ : Finset (Fin n)),
        MeasurableSet (A ∩ cellHatT π lam β) := fun β _ => hA.inter (hcell β)
    have hstep : ∀ β : Fin n,
        μ (Tower.exch (piHatT π) (lamT π lam) '' (A ∩ cellHatT π lam β))
        = μ (A ∩ cellHatT π lam β) := by
      intro β
      have hfun : ∀ y ∈ A ∩ cellHatT π lam β,
          Tower.exch (piHatT π) (lamT π lam) y
            = (Tower.exch π lam)^[returnBT π β] y := by
        rintro y ⟨-, hy⟩
        have hyI : y ∈ Set.Ico 0 (cutT lam) := cellHatT_subset_cutT hlt β hy
        have h1 := firstReturnT_eq hlt hyI
        have h2 := retT_eq_returnBT hlt hy
        rw [h2] at h1
        exact h1.symm
      rw [Set.image_congr hfun]
      exact Tower.measure_image_iterate π lam μ hμ _ (hmeasInt β (Finset.mem_univ β)) _
    have hsum : μ A = ∑ β, μ (A ∩ cellHatT π lam β) := by
      conv_lhs => rw [hcover]
      have hbi := measure_biUnion_finset (μ := μ) hdisj hmeasInt
      simpa using hbi
    have hcov : Tower.exch (piHatT π) (lamT π lam) '' A
        = ⋃ β, Tower.exch (piHatT π) (lamT π lam) '' (A ∩ cellHatT π lam β) := by
      conv_lhs => rw [hcover]
      rw [Set.image_iUnion]
    have hdisj' := Tower.pairwiseDisjoint_image
      (Tower.injective_exch (piHatT π) (lamT π lam)) hdisj
    have hmeas' : ∀ β ∈ (Finset.univ : Finset (Fin n)),
        MeasurableSet (Tower.exch (piHatT π) (lamT π lam) '' (A ∩ cellHatT π lam β)) :=
      fun β _ => Tower.measurableSet_image_exch _ _ (hmeasInt β (Finset.mem_univ β))
    have hsum' : μ (Tower.exch (piHatT π) (lamT π lam) '' A)
        = ∑ β, μ (A ∩ cellHatT π lam β) := by
      rw [hcov]
      have hbi := measure_biUnion_finset (μ := μ) hdisj' hmeas'
      rw [show μ (⋃ β, Tower.exch (piHatT π) (lamT π lam) '' (A ∩ cellHatT π lam β))
          = ∑ β, μ (Tower.exch (piHatT π) (lamT π lam) '' (A ∩ cellHatT π lam β)) from by
        simpa using hbi]
      exact Finset.sum_congr rfl fun β _ => hstep β
    rw [hsum', hsum]
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply hmeasTH hB, Measure.restrict_apply' measurableSet_Ico,
    Measure.restrict_apply' measurableSet_Ico]
  have hA : MeasurableSet (Tower.exch (piHatT π) (lamT π lam) ⁻¹' B
      ∩ Set.Ico 0 (cutT lam)) :=
    (hB.preimage hmeasTH).inter measurableSet_Ico
  have hkey := hmain _ Set.inter_subset_right hA
  have himg1 : Tower.exch (piHatT π) (lamT π lam)
        '' (Tower.exch (piHatT π) (lamT π lam) ⁻¹' B ∩ Set.Ico 0 (cutT lam))
      = B ∩ Tower.exch (piHatT π) (lamT π lam) '' Set.Ico 0 (cutT lam) := by
    ext z
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨hy1, y, hy2, rfl⟩
    · rintro ⟨hzB, y, hyI, rfl⟩
      exact ⟨y, ⟨hzB, hyI⟩, rfl⟩
  rw [himg1, hIm] at hkey
  exact hkey.symm

/-! ## 19. The level-one tower formula in the type-`true` case -/

/-- The cell of the letter `a` in the return exchange (letter coordinates). -/
def cellHatL (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (a : Fin n) : Set ℝ :=
  cellHatT π lam (eT π a)

/-- The multiplicity of the level-one tower in the type-`true` case, in letter coordinates. -/
def multOneT (π : Equiv.Perm (Fin n)) (α β : Fin n) : ℕ :=
  if β = α then 1 else if α = Tower.topCell π ∧ β = Tower.botCell then 1 else 0

theorem cellHatL_top (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    cellHatL π lam (Tower.topCell π) = cellHatT π lam (Tower.topCell π) := by
  rw [cellHatL, eT_apply_le (le_refl _)]

theorem cellHatL_bot (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    cellHatL π lam Tower.botCell
      = cellHatT π lam (⟨(Tower.topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n) := by
  rw [cellHatL, eT_botCell hlt]

theorem cellHatL_of_lt (hlt : lam Tower.botCell < lam (Tower.topCell π)) {a : Fin n}
    (ha : a.val < (Tower.topCell π).val) :
    cellHatL π lam a = Set.Ico (leftEnd lam a) (upperEnd lam a) := by
  rw [cellHatL, eT_apply_le (le_of_lt ha), cellHatT_of_lt hlt ha]

theorem cellHatL_of_gt (hlt : lam Tower.botCell < lam (Tower.topCell π)) {a : Fin n}
    (ha : (Tower.topCell π).val < a.val) (hb : a ≠ Tower.botCell) :
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
theorem exch_image_cellHatT_succ (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    Tower.exch π lam ''
        cellHatT π lam (⟨(Tower.topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      = Set.Ico (leftEnd lam Tower.botCell) (upperEnd lam Tower.botCell) := by
  have htv : translationVector π lam (Tower.topCell π)
      = Tower.tot lam - (lam (Tower.topCell π) : ℝ) - leftEnd lam (Tower.topCell π) :=
    translationVector_topCell
  have hlv : leftEnd lam Tower.botCell = Tower.tot lam - (lam Tower.botCell : ℝ) :=
    Tower.leftEnd_botCell lam
  have huv : upperEnd lam Tower.botCell = Tower.tot lam := Tower.upperEnd_botCell lam
  have hsp : splitT π lam = leftEnd lam (Tower.topCell π)
      + ((lam (Tower.topCell π) : ℝ) - (lam Tower.botCell : ℝ)) := rfl
  have hpt : ∀ y, y ∈ cellHatT π lam
        (⟨(Tower.topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      → Tower.exch π lam y = y + translationVector π lam (Tower.topCell π) := by
    intro y hy
    have hyI : y ∈ Set.Ico 0 (cutT lam) := by
      rw [← iUnion_cellHatT hlt]
      exact Set.mem_iUnion.mpr ⟨_, hy⟩
    have hy2 := hy
    rw [cellHatT_succ hlt] at hy2
    rw [exch_apply_cutT hyI]
    have hidx : idx lam y hyI.1 = Tower.topCell π := by
      refine idx_eq lam (mem_Ico_tot_of_mem_cutT hyI) ?_ ?_
      · linarith [hy2.1]
      · exact hy2.2
    rw [hidx]
  rw [Set.image_congr hpt]
  have hgoal (z : ℝ) :
    z ∈ (fun a => a + translationVector π lam (Tower.topCell π)) ''
        cellHatT π lam (⟨(Tower.topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)
      ↔ z ∈ Set.Ico (leftEnd lam Tower.botCell) (upperEnd lam Tower.botCell) := by
    rw [Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      show y + translationVector π lam (Tower.topCell π)
        ∈ Set.Ico (leftEnd lam Tower.botCell) (upperEnd lam Tower.botCell)
      rw [cellHatT_succ hlt] at hy
      rw [hsp] at hy
      rw [htv, hlv, huv]
      have hup : upperEnd lam (Tower.topCell π)
          = leftEnd lam (Tower.topCell π) + (lam (Tower.topCell π) : ℝ) := upperEnd_eq lam _
      constructor <;> linarith [hy.1, hy.2]
    · intro hz
      have hz' := hz
      rw [hlv, huv] at hz'
      refine ⟨z - translationVector π lam (Tower.topCell π), ?_, ?_⟩
      · rw [cellHatT_succ hlt, hsp, htv, upperEnd_eq]
        constructor <;> linarith [hz'.1, hz'.2]
      · show z - translationVector π lam (Tower.topCell π)
            + translationVector π lam (Tower.topCell π) = z
        ring
  ext z
  exact hgoal z

/-- **The tower formula at level one, type `true`**, in two-term form. -/
theorem tower_formula_one_step_true (hlt : lam Tower.botCell < lam (Tower.topCell π))
    (μ : Measure ℝ) (hμ : μ.map (Tower.exch π lam) = μ) (α : Fin n) :
    μ (Set.Ico (leftEnd lam α) (upperEnd lam α))
      = μ (cellHatL π lam α)
        + (if α = Tower.topCell π then μ (cellHatL π lam Tower.botCell) else 0) := by
  have hlt' := NNReal.coe_lt_coe.mpr hlt
  have hmeas := measurableSet_cellHatT π lam
  have himg := exch_image_cellHatT_succ hlt
  have hmeasB : MeasurableSet (cellHatL π lam Tower.botCell) := by
    rw [cellHatL_bot hlt]; exact hmeas _
  by_cases hα : α = Tower.topCell π
  · subst hα
    rw [if_pos rfl, cellHatL_top, cellHatL_bot hlt]
    have hsplit : Set.Ico (leftEnd lam (Tower.topCell π)) (upperEnd lam (Tower.topCell π))
        = cellHatT π lam (Tower.topCell π)
          ∪ cellHatT π lam (⟨(Tower.topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n) := by
      have hb0 : (0 : ℝ) ≤ (lam Tower.botCell : ℝ) := NNReal.coe_nonneg _
      rw [cellHatT_top hlt, cellHatT_succ hlt, splitT, upperEnd_eq,
        Set.Ico_union_Ico_eq_Ico (by linarith) (by linarith)]
    have hd : Disjoint (cellHatT π lam (Tower.topCell π))
        (cellHatT π lam (⟨(Tower.topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n)) :=
      Tower.disjoint_cell (lamT π lam) (by
        intro h
        have hv := congrArg Fin.val h
        simp only at hv
        omega)
    rw [hsplit, measure_union hd (hmeas _)]
  · rw [if_neg hα, add_zero]
    by_cases hαb : α = Tower.botCell
    · subst hαb
      rw [cellHatL_bot hlt, ← himg,
        Tower.measure_image_exch π lam μ hμ _ (hmeas _)]
    · rcases lt_or_gt_of_ne hα with hlt2 | hgt2
      · exact congrArg μ (cellHatL_of_lt hlt hlt2).symm
      · exact congrArg μ (cellHatL_of_gt hlt hgt2 hαb).symm

theorem multOneT_cast_mul {f : Fin n → ℝ≥0∞} (hne : Tower.topCell π ≠ Tower.botCell)
    (i j : Fin n) :
    (multOneT π i j : ℝ≥0∞) * f j
      = (if i = j then f j else 0)
        + (if i = Tower.topCell π then (if j = Tower.botCell then f j else 0) else 0) := by
  unfold multOneT
  by_cases h1 : j = i
  · rw [h1]
    rw [if_pos rfl, if_pos rfl]
    by_cases h2 : i = Tower.topCell π
    · rw [if_pos h2, if_neg (fun h => hne (h2.symm.trans h))]
      simp
    · rw [if_neg h2]
      simp
  · rw [if_neg h1, if_neg (Ne.symm h1), zero_add]
    by_cases h2 : i = Tower.topCell π
    · rw [if_pos h2]
      by_cases h3 : j = Tower.botCell
      · rw [if_pos ⟨h2, h3⟩, if_pos h3]
        simp
      · rw [if_neg (fun h => h3 h.2), if_neg h3]
        simp
    · rw [if_neg (fun h => h2 h.1), if_neg h2]
      simp

/-- **The level-one tower formula, matrix form, type `true`**: for a `T`-invariant measure `μ`, `μ
(cell i) = ∑ j, multOneT i j * μ (cell j of the first return map)`, the multiplicity matrix being
`rvMat true`. -/
theorem tower_formula_one_step_mult_true (hlt : lam Tower.botCell < lam (Tower.topCell π))
    (μ : Measure ℝ) (hμ : μ.map (Tower.exch π lam) = μ) (i : Fin n) :
    μ (Set.Ico (leftEnd lam i) (upperEnd lam i))
      = ∑ j, (multOneT π i j : ℝ≥0∞) * μ (cellHatL π lam j) := by
  rw [tower_formula_one_step_true hlt μ hμ i]
  have hne : Tower.topCell π ≠ Tower.botCell := topCell_ne_botCell_of_lt hlt
  have hsum : (∑ j, (multOneT π i j : ℝ≥0∞) * μ (cellHatL π lam j))
      = ∑ j, ((if i = j then μ (cellHatL π lam j) else 0)
          + (if i = Tower.topCell π then
              (if j = Tower.botCell then μ (cellHatL π lam j) else 0) else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    exact multOneT_cast_mul (f := fun j => μ (cellHatL π lam j)) hne i j
  rw [hsum, Finset.sum_add_distrib,
    Finset.sum_ite_eq Finset.univ i (fun j => μ (cellHatL π lam j))]
  simp only [Finset.mem_univ, if_true]
  have hinner : (∑ j, (if i = Tower.topCell π then
        (if j = Tower.botCell then μ (cellHatL π lam j) else 0) else 0))
      = if i = Tower.topCell π then μ (cellHatL π lam Tower.botCell) else 0 := by
    by_cases hi : i = Tower.topCell π
    · rw [if_pos hi,
        Finset.sum_congr rfl (fun j _ => if_pos hi),
        Finset.sum_ite_eq' Finset.univ (Tower.botCell) (fun j => μ (cellHatL π lam j))]
      simp
    · rw [if_neg hi, Finset.sum_eq_zero (fun j _ => if_neg hi)]
  rw [hinner]

/-! ## 20. The level-`n` formula along an arbitrary word  The per-step condition is `StepOK P lam
ε`: at the vertex `P` with lengths `lam`, the step of type `ε` is the Rauzy step, i.e. the strict
inequality of the two last lengths holds in the direction `ε`.  Its iteration along a word
is `IterOK`. -/

open IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The type-`ε` Rauzy condition at the vertex `P` with lengths `lam`. -/
def StepOK (P : IETDatum₂ α n) (lam : α → ℝ≥0) (ε : Bool) : Prop :=
  if ε then lam (P.last false) < lam (P.last true) else lam (P.last true) < lam (P.last false)

omit [DecidableEq α] in
theorem stepOK_true_iff (P : IETDatum₂ α n) (lam : α → ℝ≥0) :
    StepOK P lam true ↔ lam (P.last false) < lam (P.last true) := Iff.rfl

omit [DecidableEq α] in
theorem stepOK_false_iff (P : IETDatum₂ α n) (lam : α → ℝ≥0) :
    StepOK P lam false ↔ lam (P.last true) < lam (P.last false) := Iff.rfl

/-- The iteration of `StepOK` along a word. -/
def IterOK (P : IETDatum₂ α n) (lam : α → ℝ≥0) : List Bool → Prop
  | [] => True
  | e :: es => StepOK P lam e ∧ IterOK (P.rvStep e) (Tower.hatLam P e lam) es

omit [DecidableEq α] in
theorem perm_rvStep_true (P : IETDatum₂ α n) : (P.rvStep true).perm = TowerTrue.piHatT P.perm := by
  have hp : IETDatum₂.pivot P true = Tower.topCell P.perm := IETDatum₂.piBottom_last_true P
  change (P.piBottom.trans (IETDatum₂.insertEquiv (IETDatum₂.pivot P true))).symm.trans P.piTop
      = TowerTrue.piHatT P.perm
  rw [hp, TowerTrue.piHatT, TowerTrue.eT, Equiv.symm_trans, Equiv.trans_assoc]
  rfl

omit [DecidableEq α] in
theorem piBottom_rvStep_true (P : IETDatum₂ α n) (a : α) :
    (P.rvStep true).piBottom a = TowerTrue.eT P.perm (P.piBottom a) := by
  have hp : IETDatum₂.pivot P true = Tower.topCell P.perm := IETDatum₂.piBottom_last_true P
  change (P.piBottom.trans (IETDatum₂.insertEquiv (IETDatum₂.pivot P true))) a
      = TowerTrue.eT P.perm (P.piBottom a)
  rw [Equiv.trans_apply, hp]
  rfl

omit [DecidableEq α] in
theorem piBottom_rvStep_true_symm (P : IETDatum₂ α n) (j : Fin n) :
    (P.rvStep true).piBottom.symm j = P.piBottom.symm ((TowerTrue.eT P.perm).symm j) := by
  rw [Equiv.symm_apply_eq, piBottom_rvStep_true, Equiv.apply_symm_apply]
  exact (Equiv.apply_symm_apply (TowerTrue.eT P.perm) j).symm

/-- The renormalised lengths after a `true` step, in `α` coordinates. -/
theorem lengthsInBottom_hatLam_true (P : IETDatum₂ α n) (lam : α → ℝ≥0) :
    (P.rvStep true).lengthsInBottom (Tower.hatLam P true lam)
      = TowerTrue.lamT P.perm (P.lengthsInBottom lam) := by
  have hlastt : P.last true = P.piBottom.symm (Tower.topCell P.perm) := by
    rw [show Tower.topCell P.perm = P.piBottom (P.last true) from
      (IETDatum₂.piBottom_last_true P).symm, Equiv.symm_apply_apply]
  have hlastf : P.last false = P.piBottom.symm Tower.botCell := by
    rw [show Tower.botCell = P.piBottom (P.last false) from
      (IETDatum₂.piBottom_last_false P).symm, Equiv.symm_apply_apply]
  funext j
  rw [IETDatum₂.lengthsInBottom, piBottom_rvStep_true_symm, TowerTrue.lamT, TowerTrue.lamH,
    Tower.hatLam, IETDatum₂.lengthsInBottom]
  simp only [Bool.not_true, hlastt, hlastf]
  by_cases hj : (TowerTrue.eT P.perm).symm j = Tower.topCell P.perm
  · have hj' : P.piBottom.symm ((TowerTrue.eT P.perm).symm j)
        = P.piBottom.symm (Tower.topCell P.perm) := by rw [hj]
    rw [if_pos hj, if_pos hj']
    rfl
  · have hj' : ¬ (P.piBottom.symm ((TowerTrue.eT P.perm).symm j)
        = P.piBottom.symm (Tower.topCell P.perm)) := fun h => hj (P.piBottom.symm.injective h)
    rw [if_neg hj, if_neg hj']

/-- `rvMat true` of `IETDatum₂` data is `rvMat true` of the permutation, in bottom coordinates. -/
theorem rvMat_toComb_true (P : IETDatum₂ α n) (a b : α) :
    P.rvMat true a b = (Tower.toComb P.perm).rvMat true (P.piBottom a) (P.piBottom b) := by
  have e1 : (P.piBottom a = P.piBottom b) ↔ (a = b) := P.piBottom.injective.eq_iff
  have e2 : (P.piBottom a = (Tower.toComb P.perm).last true) ↔ (a = P.last true) := by
    rw [show (Tower.toComb P.perm).last true = Tower.topCell P.perm from rfl,
      ← IETDatum₂.piBottom_last_true P]
    exact P.piBottom.injective.eq_iff
  have e3 : (P.piBottom b = (Tower.toComb P.perm).last false) ↔ (b = P.last false) := by
    rw [show (Tower.toComb P.perm).last false = Tower.botCell from rfl,
      ← IETDatum₂.piBottom_last_false P]
    exact P.piBottom.injective.eq_iff
  simp only [IETDatum₂.rvMat, Bool.not_true, e1, e2, e3]

theorem rvMatNat_toComb_true (P : IETDatum₂ α n) (a b : α) :
    P.rvMatNat true a b = TowerTrue.multOneT P.perm (P.piBottom a) (P.piBottom b) := by
  have key : P.rvMat true a b
      = if P.piBottom b = P.piBottom a then (1 : ℤ)
        else if P.piBottom a = Tower.topCell P.perm ∧ P.piBottom b = Tower.botCell then 1
        else 0 := by
    rw [rvMat_toComb_true P a b, IETDatum₂.rvMat]
    simp only [Tower.toComb_last_true, Tower.toComb_last_false, Bool.not_true]
    by_cases h2 : P.piBottom b = P.piBottom a
    · rw [if_pos h2, if_pos h2.symm]
    · rw [if_neg h2, if_neg (Ne.symm h2)]
  rw [IETDatum₂.rvMatNat, key]
  unfold TowerTrue.multOneT
  by_cases h2 : P.piBottom b = P.piBottom a
  · rw [if_pos h2, if_pos h2]
    exact Int.toNat_natCast 1
  · rw [if_neg h2, if_neg h2]
    by_cases h3 : P.piBottom a = Tower.topCell P.perm ∧ P.piBottom b = Tower.botCell
    · rw [if_pos h3, if_pos h3]
      exact Int.toNat_natCast 1
    · rw [if_neg h3, if_neg h3]
      exact Int.toNat_natCast 0

/-- The cell of the letter `b` after one step of type `ε`. -/
theorem cellAt_singleton_false (P : IETDatum₂ α n) (lam : α → ℝ≥0) (b : α) :
    Tower.cellAt P [false] lam b
      = Tower.cellHat P.perm (P.lengthsInBottom lam) (P.piBottom b) := by
  have hv : P.vertex [false] = P.rvStep false := rfl
  have hl : Tower.lamAfter P [false] lam = Tower.hatLam P false lam := rfl
  rw [Tower.cellAt, hv, hl, Tower.lengthsInBottom_hatLam]
  rfl

theorem cellAt_singleton_true (P : IETDatum₂ α n) (lam : α → ℝ≥0) (b : α) :
    Tower.cellAt P [true] lam b
      = TowerTrue.cellHatL P.perm (P.lengthsInBottom lam) (P.piBottom b) := by
  have hv : P.vertex [true] = P.rvStep true := rfl
  have hl : Tower.lamAfter P [true] lam = Tower.hatLam P true lam := rfl
  rw [Tower.cellAt, hv, hl, lengthsInBottom_hatLam_true, TowerTrue.cellHatL, TowerTrue.cellHatT,
    piBottom_rvStep_true]

/-- The total mass of an `α`-indexed length vector. -/
def sumA (lam : α → ℝ≥0) : ℝ := ∑ a, (lam a : ℝ)

omit [NeZero n] [DecidableEq α] in
theorem tot_lengthsInBottom_eq (P : IETDatum₂ α n) (lam : α → ℝ≥0) :
    Tower.tot (P.lengthsInBottom lam) = sumA lam :=
  Equiv.sum_comp P.piBottom.symm (fun a => (lam a : ℝ))

theorem sumA_hatLam_le (P : IETDatum₂ α n) (ε : Bool) (lam : α → ℝ≥0) :
    sumA (Tower.hatLam P ε lam) ≤ sumA lam := by
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Tower.hatLam]
  split
  · exact_mod_cast tsub_le_self
  · exact le_rfl

theorem sumA_lamAfter_le (P : IETDatum₂ α n) (lam : α → ℝ≥0) (γ : List Bool) :
    sumA (Tower.lamAfter P γ lam) ≤ sumA lam := by
  induction γ generalizing P lam with
  | nil => exact le_rfl
  | cons e es ih => rw [Tower.lamAfter_cons]; exact le_trans (ih _ _) (sumA_hatLam_le P e lam)

theorem cellAt_subset_sumA_le (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) (b : α)
    {A : ℝ} (hA : sumA (Tower.lamAfter P γ lam) ≤ A) :
    Tower.cellAt P γ lam b ⊆ Set.Ico 0 A := by
  intro y hy
  refine ⟨le_trans (leftEnd_nonneg _ _) hy.1, ?_⟩
  rw [← tot_lengthsInBottom_eq (P.vertex γ) (Tower.lamAfter P γ lam)] at hA
  exact lt_of_lt_of_le hy.2 (le_trans (upperEnd_le_total _ _) hA)

theorem pathQ_toNat_eq_Qnat (P : IETDatum₂ α n) (γ : List Bool) (a b : α) :
    (IETDatum₂.Path.Q P γ a b).toNat = P.Qnat γ a b := by
  rw [← P.Qnat_cast γ a b]
  exact Int.toNat_natCast (P.Qnat γ a b)

/-- **The level-one tower formula in `α` coordinates**, for either type `ε`. -/
theorem tower_formula_one_step_comb (P : IETDatum₂ α n) (lam : α → ℝ≥0) (ν : Measure ℝ)
    (hν : ν.map (Tower.exch P.perm (P.lengthsInBottom lam)) = ν) (ε : Bool)
    (hε : StepOK P lam ε) (a : α) :
    ν (InvariantMeasure.cellOf P lam a)
      = ∑ b, ((P.rvMat ε a b).toNat : ℝ≥0∞) * ν (Tower.cellAt P [ε] lam b) := by
  have e1 : P.lengthsInBottom lam (Tower.topCell P.perm) = lam (P.last true) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_true P, Equiv.symm_apply_apply]
  have e2 : P.lengthsInBottom lam Tower.botCell = lam (P.last false) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_false P, Equiv.symm_apply_apply]
  cases ε with
  | false =>
    have hlt : P.lengthsInBottom lam (Tower.topCell P.perm)
        < P.lengthsInBottom lam Tower.botCell := by
      rw [e1, e2]; exact hε
    have h1 := Tower.tower_formula_one_step_mult (π := P.perm) (lam := P.lengthsInBottom lam)
      hlt ν hν (P.piBottom a)
    rw [← Equiv.sum_comp P.piBottom (fun y : Fin n =>
      (Tower.multOne P.perm (P.piBottom a) y : ℝ≥0∞)
        * ν (Tower.cellHat P.perm (P.lengthsInBottom lam) y))] at h1
    refine h1.trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [← cellAt_singleton_false P lam b, ← P.rvMatNat_toComb_false a b]
    rfl
  | true =>
    have hlt : P.lengthsInBottom lam Tower.botCell
        < P.lengthsInBottom lam (Tower.topCell P.perm) := by
      rw [e1, e2]; exact hε
    have h1 := tower_formula_one_step_mult_true (π := P.perm) (lam := P.lengthsInBottom lam)
      hlt ν hν (P.piBottom a)
    rw [← Equiv.sum_comp P.piBottom (fun y : Fin n =>
      (multOneT P.perm (P.piBottom a) y : ℝ≥0∞)
        * ν (cellHatL P.perm (P.lengthsInBottom lam) y))] at h1
    refine h1.trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [← cellAt_singleton_true P lam b, ← rvMatNat_toComb_true P a b]
    rfl

theorem sumA_hatLam_false (P : IETDatum₂ α n) (lam : α → ℝ≥0)
    (hlt : P.lengthsInBottom lam (Tower.topCell P.perm) < P.lengthsInBottom lam Tower.botCell) :
    sumA (Tower.hatLam P false lam) = Tower.cut P.perm (P.lengthsInBottom lam) := by
  rw [← tot_lengthsInBottom_eq (P.rvStep false) (Tower.hatLam P false lam),
    ← Tower.cut_eq_sum_lamHat hlt, ← Tower.lengthsInBottom_hatLam P lam]
  rfl

theorem sumA_hatLam_true (P : IETDatum₂ α n) (lam : α → ℝ≥0)
    (hlt : P.lengthsInBottom lam Tower.botCell < P.lengthsInBottom lam (Tower.topCell P.perm)) :
    sumA (Tower.hatLam P true lam) = cutT (P.lengthsInBottom lam) := by
  rw [← tot_lengthsInBottom_eq (P.rvStep true) (Tower.hatLam P true lam),
    ← tot_lamT hlt, ← lengthsInBottom_hatLam_true P lam]

theorem exch_rvStep_false_hatLam (P : IETDatum₂ α n) (lam : α → ℝ≥0) :
    Tower.exch (Tower.piHat P.perm) (Tower.lamHat P.perm (P.lengthsInBottom lam))
      = Tower.exch (P.rvStep false).perm ((P.rvStep false).lengthsInBottom
          (Tower.hatLam P false lam)) := by
  rw [IETDatum₂.perm_rvStep_false, Tower.lengthsInBottom_hatLam]

theorem exch_rvStep_true_hatLam (P : IETDatum₂ α n) (lam : α → ℝ≥0) :
    Tower.exch (piHatT P.perm) (lamT P.perm (P.lengthsInBottom lam))
      = Tower.exch (P.rvStep true).perm ((P.rvStep true).lengthsInBottom
          (Tower.hatLam P true lam)) := by
  rw [perm_rvStep_true, lengthsInBottom_hatLam_true]

/-- Regrouping of a double sum with weights. -/
theorem sumA_mul_sumB {ι : Type*} [Fintype ι] (A : ι → ℝ≥0∞)
    (B : ι → ι → ℝ≥0∞) (w : ι → ℝ≥0∞) :
    (∑ c, A c * ∑ b, B c b * w b) = ∑ b, (∑ c, A c * B c b) * w b := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [mul_assoc]

/-- **The level-`n` tower formula along an arbitrary word** (both Rauzy types). -/
theorem tower_formula_level_pathQ_exch :
    ∀ (P : IETDatum₂ α n) (lam : α → ℝ≥0) (ν : Measure ℝ),
      ν.map (Tower.exch P.perm (P.lengthsInBottom lam)) = ν →
      ∀ (γ : List Bool), IterOK P lam γ → ∀ a : α,
        ν (InvariantMeasure.cellOf P lam a)
          = ∑ b, ((IETDatum₂.Path.Q P γ a b).toNat : ℝ≥0∞) * ν (Tower.cellAt P γ lam b)
  | P, lam, ν, _, [], _, a => by
    rw [IETDatum₂.Path.Q_nil, Finset.sum_eq_single a]
    · rw [Matrix.one_apply, if_pos rfl]
      rw [show ((1 : ℤ).toNat : ℝ≥0∞) = 1 from by norm_num, one_mul]
      rfl
    · intro b _ hba
      rw [Matrix.one_apply, if_neg (fun h : a = b => hba h.symm)]
      simp
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  | P, lam, ν, hν, e :: es, hγ, a => by
    obtain ⟨he, hes⟩ := hγ
    have e1 : P.lengthsInBottom lam (Tower.topCell P.perm) = lam (P.last true) := by
      simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_true P,
        Equiv.symm_apply_apply]
    have e2 : P.lengthsInBottom lam Tower.botCell = lam (P.last false) := by
      simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_false P,
        Equiv.symm_apply_apply]
    -- the restricted measure is invariant under the renormalised exchange
    have hν' : (ν.restrict (Set.Ico 0 (sumA (Tower.hatLam P e lam)))).map
        (Tower.exch (P.rvStep e).perm ((P.rvStep e).lengthsInBottom (Tower.hatLam P e lam)))
        = ν.restrict (Set.Ico 0 (sumA (Tower.hatLam P e lam))) := by
      cases e with
      | false =>
        have hlt : P.lengthsInBottom lam (Tower.topCell P.perm)
            < P.lengthsInBottom lam Tower.botCell := by
          rw [e1, e2]; exact he
        rw [sumA_hatLam_false P lam hlt, ← exch_rvStep_false_hatLam]
        exact Tower.restrict_cut_invariant hlt ν hν
      | true =>
        have hlt : P.lengthsInBottom lam Tower.botCell
            < P.lengthsInBottom lam (Tower.topCell P.perm) := by
          rw [e1, e2]; exact he
        rw [sumA_hatLam_true P lam hlt, ← exch_rvStep_true_hatLam]
        exact restrict_cut_invariant_true hlt ν hν
    -- the restricted measure agrees with `ν` on the cells
    have hagree (X : Set ℝ) (hX : X ⊆ Set.Ico 0 (sumA (Tower.hatLam P e lam))) :
      ν.restrict (Set.Ico 0 (sumA (Tower.hatLam P e lam))) X = ν X := by
      rw [Measure.restrict_apply' measurableSet_Ico, Set.inter_eq_self_of_subset_left hX]
    have hcell1 (c : α) : Tower.cellAt P [e] lam c
        ⊆ Set.Ico 0 (sumA (Tower.hatLam P e lam)) := by
      cases e with
      | false =>
        have hlt : P.lengthsInBottom lam (Tower.topCell P.perm)
            < P.lengthsInBottom lam Tower.botCell := by
          rw [e1, e2]; exact he
        rw [cellAt_singleton_false, sumA_hatLam_false P lam hlt]
        exact Tower.cellHat_subset_cut hlt (P.piBottom c)
      | true =>
        have hlt : P.lengthsInBottom lam Tower.botCell
            < P.lengthsInBottom lam (Tower.topCell P.perm) := by
          rw [e1, e2]; exact he
        rw [cellAt_singleton_true, sumA_hatLam_true P lam hlt]
        exact cellHatT_subset_cutT hlt _
    have hcell2 : ∀ b : α, Tower.cellAt (P.rvStep e) es (Tower.hatLam P e lam) b
        ⊆ Set.Ico 0 (sumA (Tower.hatLam P e lam)) :=
      fun b => cellAt_subset_sumA_le (P.rvStep e) es (Tower.hatLam P e lam) b
        (sumA_lamAfter_le (P.rvStep e) (Tower.hatLam P e lam) es)
    -- the matrix identity
    have hQ (b : α) :
      (IETDatum₂.Path.Q P (e :: es) a b).toNat
        = ∑ c, (P.rvMat e a c).toNat
            * (IETDatum₂.Path.Q (P.rvStep e) es c b).toNat := by
      rw [pathQ_toNat_eq_Qnat, IETDatum₂.Qnat_cons, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← pathQ_toNat_eq_Qnat]
      rfl
    calc ν (InvariantMeasure.cellOf P lam a)
        = ∑ c, ((P.rvMat e a c).toNat : ℝ≥0∞) * ν (Tower.cellAt P [e] lam c) :=
          tower_formula_one_step_comb P lam ν hν e he a
      _ = ∑ c, ((P.rvMat e a c).toNat : ℝ≥0∞)
            * ν.restrict (Set.Ico 0 (sumA (Tower.hatLam P e lam))) (Tower.cellAt P [e] lam c) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [hagree _ (hcell1 c)]
      _ = ∑ c, ((P.rvMat e a c).toNat : ℝ≥0∞)
            * (∑ b, ((IETDatum₂.Path.Q (P.rvStep e) es c b).toNat : ℝ≥0∞)
              * ν.restrict (Set.Ico 0 (sumA (Tower.hatLam P e lam)))
                (Tower.cellAt (P.rvStep e) es (Tower.hatLam P e lam) b)) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [show Tower.cellAt P [e] lam c
            = InvariantMeasure.cellOf (P.rvStep e) (Tower.hatLam P e lam) c from rfl,
            tower_formula_level_pathQ_exch (P.rvStep e) (Tower.hatLam P e lam) _ hν' es hes c]
      _ = ∑ b, (∑ c, ((P.rvMat e a c).toNat : ℝ≥0∞)
              * (IETDatum₂.Path.Q (P.rvStep e) es c b).toNat)
            * ν.restrict (Set.Ico 0 (sumA (Tower.hatLam P e lam)))
              (Tower.cellAt (P.rvStep e) es (Tower.hatLam P e lam) b) :=
          sumA_mul_sumB (fun c => ((P.rvMat e a c).toNat : ℝ≥0∞))
            (fun c b => ((IETDatum₂.Path.Q (P.rvStep e) es c b).toNat : ℝ≥0∞)) _
      _ = ∑ b, (∑ c, ((P.rvMat e a c).toNat : ℝ≥0∞)
              * (IETDatum₂.Path.Q (P.rvStep e) es c b).toNat)
            * ν (Tower.cellAt (P.rvStep e) es (Tower.hatLam P e lam) b) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hagree _ (hcell2 b)]
      _ = ∑ b, ((IETDatum₂.Path.Q P (e :: es) a b).toNat : ℝ≥0∞)
            * ν (Tower.cellAt P (e :: es) lam b) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hQ b]
          push_cast
          rfl

/-- **The level-`n` tower formula** along an *arbitrary* word `γ` for an invariant
measure of the exchange `P.toIET lam`, the per-step hypothesis being the single predicate
`IterOK P lam γ` (each step is the Rauzy step of the renormalised lengths at that vertex). -/
theorem tower_formula_level_pathQ_any (P : IETDatum₂ α n) (_hP : P.Irreducible) (_hn : 2 ≤ n)
    (lam : α → ℝ≥0) (hlam : lam ∈ simplexOn α) (μ : Measure ℝ)
    (hμ : μ.map ⇑(P.toIET lam) = μ) (γ : List Bool) (hγ : IterOK P lam γ) (a : α) :
    μ (InvariantMeasure.cellOf P lam a)
      = ∑ b, ((IETDatum₂.Path.Q P γ a b).toNat : ℝ≥0∞) * μ (Tower.cellAt P γ lam b) := by
  have hcoe : ⇑(P.toIET lam) = Tower.exch P.perm (P.lengthsInBottom lam) := by
    rw [IETDatum₂.toIET_eq_mkIET1 P hlam, IETDatum₂.coe_mkIET1']
    rfl
  rw [hcoe] at hμ
  exact tower_formula_level_pathQ_exch P lam μ hμ γ hγ a

end
end TowerTrue

end
