/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import IETFree.RauzyVeech.FirstReturn
public import IETFree.RauzyVeech.IterOKPath

/-!
# The level-one Rauzy-Veech tower in `IETDatum₂` letters (both step types)

Base case of the induction proving `TowerTiling`: for one Rauzy step `e` at the
vertex `P` with lengths `L`, the floors `T^j '' cellAt P [e] L b`, `j < Path.height P [e] b`, are a
partition of `Ico 0 (∑ L)`; the heights are the column sums of the elementary matrix `rvMat e`. -/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators Topology

namespace IntervalExchange.RauzyVeech

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Basic rewrites for the level cell and the exchange at a node -/

theorem cellAt_succ (P : IETDatum₂ α n) (γ : List Bool) (e : Bool) (lam : α → ℝ≥0)
    (b : α) :
    cellAt P (γ ++ [e]) lam b
      = cellAt (IETDatum₂.vertex P γ) [e] (lamAfter P γ lam) b := by
  simp only [cellAt, lamAfter_append_singleton, IETDatum₂.vertex_append_singleton,
    lamAfter_cons, lamAfter_nil, IETDatum₂.vertex_singleton]

omit [DecidableEq α] [NeZero n] in
/-- The total length of a renormalised vector read in bottom order. -/
theorem totalLength_lengthsInBottom (P : IETDatum₂ α n) (lam : α → ℝ≥0) :
    totalLength (P.lengthsInBottom lam) = ∑ a, (lam a : ℝ) :=
  Equiv.sum_comp P.piBottom.symm (fun a => (lam a : ℝ))

omit [DecidableEq α] in
/-- On the simplex the exchange of `P` is `mkIETFun`. -/
theorem coe_toIET {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hlam : lam ∈ simplex α) :
    ⇑(P.toIET lam) = mkIETFun (P.lengthsInBottom lam) P.perm 0 := by
  rw [IETDatum₂.toIET_eq_mkIET1 P hlam, coe_mkIET1']

/-! ## 2. The heights are the column sums of `rvMat e` -/

/-- The `ℕ`-valued entries of `rvMat`, as a case split. -/
theorem rvMatNat_eq (P : IETDatum₂ α n) (e : Bool) (a b : α) :
    P.rvMatNat e a b = if a = b then 1 else if a = P.last e ∧ b = P.last (!e) then 1 else 0 := by
  rw [IETDatum₂.rvMatNat, IETDatum₂.rvMat]
  split_ifs <;> simp

theorem sum_ite_single {c : α} (t : ℕ) :
    (∑ a, (if a = c then t else 0)) = t := by
  refine (Finset.sum_eq_single c ?_ ?_).trans (ite_eq_left rfl)
  · intro a _ ha; exact ite_eq_right ha
  · intro h; exact absurd (Finset.mem_univ c) h

/-- The column sums of `rvMat e`: `1` plus one on the secondary name. -/
theorem height_singleton_eq (P : IETDatum₂ α n) (hne : ∀ e : Bool, P.last e ≠ P.last (!e))
    (e : Bool) (b : α) :
    IETDatum₂.Path.height P [e] b = 1 + if b = P.last (!e) then 1 else 0 := by
  have hsplit (a : α) :
    P.rvMatNat e a b
      = (if a = b then 1 else 0)
        + (if a = P.last e then (if b = P.last (!e) then 1 else 0) else 0) := by
    rw [rvMatNat_eq]
    by_cases hab : a = b
    · rw [hab, ite_eq_left rfl, ite_eq_left rfl]
      by_cases h1 : b = P.last e
      · rw [ite_eq_left h1]
        by_cases h2 : b = P.last (!e)
        · exact absurd (h1.symm.trans h2) (hne e)
        · rw [ite_eq_right h2]
      · rw [ite_eq_right h1]
    · rw [ite_eq_right hab, ite_eq_right hab]
      by_cases h1 : a = P.last e
      · rw [ite_eq_left h1]
        by_cases h2 : b = P.last (!e)
        · rw [ite_eq_left h2, ite_eq_left ⟨h1, h2⟩]
        · rw [ite_eq_right h2, ite_eq_right (fun h => h2 h.2)]
      · rw [ite_eq_right h1, ite_eq_right (fun h : a = P.last e ∧ b = P.last (!e) => h1 h.1)]
  calc IETDatum₂.Path.height P [e] b = ∑ a, P.rvMatNat e a b := by
        simp [IETDatum₂.Path.height, IETDatum₂.rvMatNat]
    _ = ∑ a, ((if a = b then 1 else 0)
          + (if a = P.last e then (if b = P.last (!e) then 1 else 0) else 0)) :=
        Finset.sum_congr rfl (fun a _ => hsplit a)
    _ = (∑ a, (if a = b then (1:ℕ) else 0))
          + ∑ a, (if a = P.last e then (if b = P.last (!e) then 1 else 0) else 0) :=
        Finset.sum_add_distrib
    _ = 1 + (if b = P.last (!e) then 1 else 0) := by
        rw [sum_ite_single (c := b) 1, sum_ite_single (c := P.last e)]

/-- The one-letter height is at most two. -/
theorem height_singleton_le_two (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (e : Bool) (c : α) : IETDatum₂.Path.height P [e] c ≤ 2 := by
  rw [height_singleton_eq P (fun e' => IETDatum₂.last_ne_last_not P hP hn e')]
  split <;> omega

/-- The one-letter height of a letter other than the secondary name is one. -/
theorem height_singleton_eq_one_of_ne (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (e : Bool) {c : α} (hc : c ≠ P.last (!e)) : IETDatum₂.Path.height P [e] c = 1 := by
  rw [height_singleton_eq P (fun e' => IETDatum₂.last_ne_last_not P hP hn e')]
  simp only [ite_eq_right hc, add_zero]

/-- `returnB` of the level-one vertex, in letters, is the one-letter height of the false step. -/
theorem returnB_eq_height (P : IETDatum₂ α n) (hne : ∀ e : Bool, P.last e ≠ P.last (!e))
    (b : α) :
    returnB P.perm (P.piBottom b) = IETDatum₂.Path.height P [false] b := by
  have hiff : (P.piBottom b = topCell P.perm) ↔ (b = P.last true) := by
    rw [← IETDatum₂.piBottom_last_true P, P.piBottom.injective.eq_iff]
  rw [height_singleton_eq P hne, returnB]
  simp only [Bool.not_false]
  by_cases h : b = P.last true
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h (hiff.mp hc)), ite_eq_right h]

/-- `returnBT` of the level-one vertex, in letters, is the one-letter height of the true step. -/
theorem returnBT_eq_height (P : IETDatum₂ α n) (hne : ∀ e : Bool, P.last e ≠ P.last (!e))
    (b : α) :
    returnBT P.perm (eT P.perm (P.piBottom b))
      = IETDatum₂.Path.height P [true] b := by
  have hiff : (P.piBottom b = (lastPos n)) ↔ (b = P.last false) := by
    rw [← IETDatum₂.piBottom_last_false P, P.piBottom.injective.eq_iff]
  have hc : (eT P.perm (P.piBottom b) = eT P.perm (lastPos n))
      ↔ (b = P.last false) := by
    rw [(eT P.perm).injective.eq_iff, hiff]
  rw [height_singleton_eq P hne, returnBT]
  simp only [Bool.not_true, hc]
  by_cases h : b = P.last false
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

/-! ## 3. The tower union for one step of type `true` -/

/-- **Tower decomposition for a step of type `true`**: the whole interval is the base `Ico 0 (cutT)`
together with the image of the upper part of the top cell. -/
theorem tower_decomp_true {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (lastPos n) < lam (topCell π)) :
    Set.Ico 0 (totalLength lam)
      = Set.Ico 0 (cutT lam)
        ∪ mkIETFun lam π 0 ''
            cellHatT π lam
              (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n) := by
  have h0 : (0:ℝ) ≤ cutT lam := by
    rw [cutT]
    linarith [single_le_totalLength lam (lastPos n)]
  rw [mkIETFun_image_cellHatT_succ hlt, leftEnd_lastPos_eq_cutT,
    upperEnd_lastPos]
  ext z
  simp only [Set.mem_union, Set.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hc : z < cutT lam
    · exact Or.inl ⟨h1, hc⟩
    · exact Or.inr ⟨le_of_not_gt hc, h2⟩
  · rintro (h | h)
    · exact ⟨h.1, lt_of_lt_of_le h.2 (cutT_le_totalLength lam)⟩
    · exact ⟨le_trans h0 h.1, h.2⟩

/-- **The level-one tower union, type `true`** (in `Fin n` coordinates). -/
theorem iUnion_floor_true {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam (lastPos n) < lam (topCell π)) :
    Set.Ico 0 (totalLength lam)
      = ⋃ β, ⋃ j : Fin (returnBT π β),
          (mkIETFun lam π 0)^[(j : ℕ)] '' cellHatT π lam β := by
  have hβ : eT π (lastPos n)
      = (⟨(topCell π).val + 1, topCell_succ_lt hlt⟩ : Fin n) :=
    eT_lastPos hlt
  have hmain : (⋃ β, ⋃ j : Fin (returnBT π β),
        (mkIETFun lam π 0)^[(j : ℕ)] '' cellHatT π lam β)
      = (⋃ β, cellHatT π lam β)
        ∪ mkIETFun lam π 0 '' cellHatT π lam (eT π (lastPos n)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨β, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
      rcases Nat.eq_zero_or_pos ((j : ℕ)) with h0 | hpos
      · left
        exact Set.mem_iUnion.mpr ⟨β, by rw [h0] at hx; simpa using hx⟩
      · right
        have hle : returnBT π β ≤ 2 := returnBT_le_two π β
        have hj2 : returnBT π β = 2 := by omega
        have hbβ : β = eT π (lastPos n) := by
          rw [returnBT] at hj2
          by_cases h : β = eT π (lastPos n)
          · exact h
          · rw [ite_eq_right h] at hj2; omega
        have hj1 : (j : ℕ) = 1 := by omega
        subst hbβ
        rw [hj1] at hx
        simpa using hx
    · rintro (hx | hx)
      · obtain ⟨β, hx⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨β,
          Set.mem_iUnion.mpr ⟨⟨0, returnBT_pos π β⟩, by simpa using hx⟩⟩
      · refine Set.mem_iUnion.mpr ⟨eT π (lastPos n), Set.mem_iUnion.mpr
          ⟨⟨1, by rw [returnBT_eq_two]; omega⟩, ?_⟩⟩
        simpa using hx
  rw [hmain, tower_decomp_true hlt, iUnion_cellHatT hlt, ← hβ]

omit [DecidableEq α] in
/-- **The bottom-order length of the top cell is the top length of the datum.** -/
theorem lengthsInBottom_topCell (P : IETDatum₂ α n) (L : α → ℝ≥0) :
    P.lengthsInBottom L (topCell P.perm) = L (P.last true) := by
  simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_true P, Equiv.symm_apply_apply]

omit [DecidableEq α] in
/-- **The bottom-order length of the bottom cell is the bottom length of the datum.** -/
theorem lengthsInBottom_lastPos (P : IETDatum₂ α n) (L : α → ℝ≥0) :
    P.lengthsInBottom L (lastPos n) = L (P.last false) := by
  simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_false P, Equiv.symm_apply_apply]

/-! ## 4. The level-one tower in letters, both types -/

/-- **The level-one tower, type `false`**, in letters. -/
theorem level_tower_false (P : IETDatum₂ α n) (hne : ∀ e : Bool, P.last e ≠ P.last (!e))
    (L : α → ℝ≥0) (hL : IsRauzyStep P L false) :
    Set.Ico 0 (∑ b, (L b : ℝ))
      = ⋃ b, ⋃ j : Fin (IETDatum₂.Path.height P [false] b),
          (mkIETFun (P.lengthsInBottom L) P.perm 0)^[(j : ℕ)] '' cellAt P [false] L b := by
  have hlt : P.lengthsInBottom L (topCell P.perm) < P.lengthsInBottom L (lastPos n) := by
    rw [lengthsInBottom_topCell, lengthsInBottom_lastPos]; exact hL
  have h := tower_decomp_iUnion (π := P.perm) (lam := P.lengthsInBottom L) hlt
  rw [totalLength_lengthsInBottom_eq] at h
  simp only [totalLength] at h
  rw [h, ← Function.Surjective.iUnion_comp P.piBottom.surjective
    (fun β => ⋃ j : Fin (returnB P.perm β),
      (mkIETFun (P.lengthsInBottom L) P.perm 0)^[(j : ℕ)] ''
        cellHat P.perm (P.lengthsInBottom L) β)]
  refine Set.iUnion_congr (fun b => ?_)
  rw [returnB_eq_height P hne b, ← cellAt_singleton_false]

/-- **The level-one tower, type `true`**, in letters. -/
theorem level_tower_true (P : IETDatum₂ α n) (hne : ∀ e : Bool, P.last e ≠ P.last (!e))
    (L : α → ℝ≥0) (hL : IsRauzyStep P L true) :
    Set.Ico 0 (∑ b, (L b : ℝ))
      = ⋃ b, ⋃ j : Fin (IETDatum₂.Path.height P [true] b),
          (mkIETFun (P.lengthsInBottom L) P.perm 0)^[(j : ℕ)] '' cellAt P [true] L b := by
  have hlt : P.lengthsInBottom L (lastPos n) < P.lengthsInBottom L (topCell P.perm) := by
    rw [lengthsInBottom_topCell, lengthsInBottom_lastPos]; exact hL
  have h := iUnion_floor_true (π := P.perm) (lam := P.lengthsInBottom L) hlt
  rw [totalLength_lengthsInBottom_eq] at h
  simp only [totalLength] at h
  rw [h, ← Function.Surjective.iUnion_comp (P.piBottom.trans (eT P.perm)).surjective
    (fun β => ⋃ j : Fin (returnBT P.perm β),
      (mkIETFun (P.lengthsInBottom L) P.perm 0)^[(j : ℕ)] '' cellHatT P.perm
        (P.lengthsInBottom L) β)]
  refine Set.iUnion_congr (fun b => ?_)
  rw [show (P.piBottom.trans (eT P.perm)) b
      = eT P.perm (P.piBottom b) from rfl,
    returnBT_eq_height P hne b, ← cellHatL, ← cellAt_singleton_true]

/-! ## 5. The first-return map of the level-one tower is the renormalised exchange  This is piece
(1) of the induction step towards `TowerTiling`: on each level-one cell the first return of `T` to
the cut interval is the new exchange, with return time `IETDatum₂.Path.height P [e] b`. -/

theorem firstReturn_false (P : IETDatum₂ α n) (hne : ∀ e : Bool, P.last e ≠ P.last (!e))
    (L : α → ℝ≥0) (hL : IsRauzyStep P L false) (b : α) {y : ℝ}
    (hy : y ∈ cellAt P [false] L b) :
    (mkIETFun (P.lengthsInBottom L) P.perm 0)^[IETDatum₂.Path.height P [false] b] y
      = (mkIETFun ((P.rvStep false).lengthsInBottom (hatLam P false L))
          (P.rvStep false).perm 0) y := by
  have hlt : P.lengthsInBottom L (topCell P.perm) < P.lengthsInBottom L (lastPos n) := by
    rw [lengthsInBottom_topCell, lengthsInBottom_lastPos]; exact hL
  have hy' : y ∈ cellHat P.perm (P.lengthsInBottom L) (P.piBottom b) := by
    rw [← cellAt_singleton_false]; exact hy
  have hyc : y ∈ Set.Ico 0 (cut P.perm (P.lengthsInBottom L)) :=
    cellHat_subset_cut hlt (P.piBottom b) hy'
  have hret : ret P.perm (P.lengthsInBottom L) y = IETDatum₂.Path.height P [false] b := by
    rw [ret_eq_returnB hlt hy', returnB_eq_height P hne b]
  rw [← hret, firstReturn_eq hlt hyc]
  rw [← mkIETFun_rvStep_false_hatLam P L]

theorem firstReturn_true (P : IETDatum₂ α n) (hne : ∀ e : Bool, P.last e ≠ P.last (!e))
    (L : α → ℝ≥0) (hL : IsRauzyStep P L true) (b : α) {y : ℝ}
    (hy : y ∈ cellAt P [true] L b) :
    (mkIETFun (P.lengthsInBottom L) P.perm 0)^[IETDatum₂.Path.height P [true] b] y
      = (mkIETFun ((P.rvStep true).lengthsInBottom (hatLam P true L))
          (P.rvStep true).perm 0) y := by
  have hlt : P.lengthsInBottom L (lastPos n) < P.lengthsInBottom L (topCell P.perm) := by
    rw [lengthsInBottom_topCell, lengthsInBottom_lastPos]; exact hL
  have hy' : y ∈ cellHatT P.perm (P.lengthsInBottom L)
      (eT P.perm (P.piBottom b)) := by
    rw [← cellHatL, ← cellAt_singleton_true]; exact hy
  have hyc : y ∈ Set.Ico 0 (cutT (P.lengthsInBottom L)) :=
    cellHatT_subset_cutT hlt _ hy'
  have hret : retT P.perm (P.lengthsInBottom L) y = IETDatum₂.Path.height P [true] b := by
    rw [retT_eq_returnBT hlt hy', returnBT_eq_height P hne b]
  rw [← hret, firstReturnT_eq hlt hyc]
  rw [← mkIETFun_rvStep_true_hatLam P L]

/-! ## 6. The two names: where the level-one cells sit and where the top floor goes -/

theorem cellAt_nil (P : IETDatum₂ α n) (L : α → ℝ≥0) (b : α) :
    cellAt P [] L b
      = Set.Ico (leftEnd (P.lengthsInBottom L) (P.piBottom b))
          (upperEnd (P.lengthsInBottom L) (P.piBottom b)) := (rfl)

/-- **False step, nesting**: every level-one cell sits in its level-zero cell. -/
theorem names_false_sub (P : IETDatum₂ α n) (L : α → ℝ≥0) (b : α) :
    cellAt P [false] L b ⊆ cellAt P [] L b := by
  rw [cellAt_singleton_false, cellAt_nil]
  exact cellHat_subset_dom _ _ _

/-- **False step, the second floor lands in the cell of the main name.** -/
theorem names_false_image (P : IETDatum₂ α n) (L : α → ℝ≥0)
    (hL : IsRauzyStep P L false) :
    (mkIETFun (P.lengthsInBottom L) P.perm 0) '' cellAt P [false] L (P.last true)
      ⊆ cellAt P [] L (P.last false) := by
  have hlt : P.lengthsInBottom L (topCell P.perm) < P.lengthsInBottom L (lastPos n) := by
    rw [lengthsInBottom_topCell, lengthsInBottom_lastPos]; exact hL
  have hcell : cellAt P [false] L (P.last true)
      = Set.Ico (leftEnd (P.lengthsInBottom L) (topCell P.perm))
          (upperEnd (P.lengthsInBottom L) (topCell P.perm)) := by
    rw [cellAt_singleton_false, IETDatum₂.piBottom_last_true P,
      cellHat_topCell hlt]
  have himg := mkIETFun_image_topCell (π := P.perm) (lam := P.lengthsInBottom L) hlt
  rw [hcell, himg, cellAt_nil, IETDatum₂.piBottom_last_false P]
  -- `Ico (cut) (totalLength) ⊆ Ico (leftEnd lastPos n) (upperEnd lastPos n)`
  have hbot : leftEnd (P.lengthsInBottom L) (lastPos n)
      = totalLength (P.lengthsInBottom L) - (P.lengthsInBottom L (lastPos n) : ℝ) :=
    leftEnd_lastPos _
  have hup : upperEnd (P.lengthsInBottom L) (lastPos n) = totalLength (P.lengthsInBottom L) :=
    upperEnd_lastPos _
  have hcut : cut P.perm (P.lengthsInBottom L)
      = totalLength (P.lengthsInBottom L) - (P.lengthsInBottom L (topCell P.perm) : ℝ) := (rfl)
  have hle : (P.lengthsInBottom L (topCell P.perm) : ℝ)
      ≤ (P.lengthsInBottom L (lastPos n) : ℝ) := le_of_lt (by exact_mod_cast hlt)
  rw [hbot, hup]
  refine Set.Ico_subset_Ico ?_ le_rfl
  rw [hcut]
  linarith

/-- **True step, nesting**: every level-one cell but the one over the bottom name sits in its
level-zero cell. -/
theorem names_true_sub (P : IETDatum₂ α n) (L : α → ℝ≥0)
    (hL : IsRauzyStep P L true) (a : α) (ha : a ≠ P.last false) :
    cellAt P [true] L a ⊆ cellAt P [] L a := by
  have hlt : P.lengthsInBottom L (lastPos n) < P.lengthsInBottom L (topCell P.perm) := by
    rw [lengthsInBottom_topCell, lengthsInBottom_lastPos]; exact hL
  rw [cellAt_singleton_true, cellHatL, cellAt_nil]
  set β := P.piBottom a with hβ
  rcases lt_trichotomy β.val (topCell P.perm).val with hlt2 | heq | hgt2
  · rw [eT_apply_le (le_of_lt hlt2), cellHatT_of_lt hlt2]
  · have hβtop : β = topCell P.perm := Fin.ext heq
    rw [hβtop, eT_apply_le le_rfl, cellHatT_top hlt]
    refine Set.Ico_subset_Ico le_rfl ?_
    rw [splitT, upperEnd_eq]
    linarith
  · have hβbot : β ≠ (lastPos n) := by
      intro h
      have h1 : P.piBottom a = P.piBottom (P.last false) := by
        rw [← hβ, h, IETDatum₂.piBottom_last_false P]
      exact ha (P.piBottom.injective h1)
    have hβlt : β.val + 1 < n := by
      have h1 : β.val < n := β.isLt
      have h2 : β.val ≠ n - 1 := by
        intro hh
        exact hβbot (Fin.ext (by rw [hh]; rfl))
      omega
    have hval : (eT P.perm β).val = β.val + 1 := eT_apply_gt hlt hgt2 hβbot
    have hE : eT P.perm β = succFin β hβlt :=
      Fin.ext (by rw [hval, succFin_val])
    rw [hE, cellHatT_of_gt hlt hgt2 hβlt]

/-- **True step**: the cell over the bottom name sits in the cell of the top name. -/
theorem names_true_sub_scd (P : IETDatum₂ α n) (L : α → ℝ≥0)
    (hL : IsRauzyStep P L true) :
    cellAt P [true] L (P.last false) ⊆ cellAt P [] L (P.last true) := by
  have hlt : P.lengthsInBottom L (lastPos n) < P.lengthsInBottom L (topCell P.perm) := by
    rw [lengthsInBottom_topCell, lengthsInBottom_lastPos]; exact hL
  have hsucc : (topCell P.perm).val + 1 < n := topCell_succ_lt hlt
  have hcell : cellAt P [true] L (P.last false)
      = Set.Ico (splitT P.perm (P.lengthsInBottom L))
          (upperEnd (P.lengthsInBottom L) (topCell P.perm)) := by
    rw [cellAt_singleton_true, cellHatL, IETDatum₂.piBottom_last_false P,
      eT_lastPos hlt, cellHatT_succ hlt]
  have hnm : cellAt P [] L (P.last true)
      = Set.Ico (leftEnd (P.lengthsInBottom L) (topCell P.perm))
          (upperEnd (P.lengthsInBottom L) (topCell P.perm)) := by
    rw [cellAt_nil, IETDatum₂.piBottom_last_true P]
  rw [hcell, hnm, splitT]
  refine Set.Ico_subset_Ico ?_ le_rfl
  linarith

/-- **True step, the second floor lands in the cell of the bottom name.** -/
theorem names_true_image (P : IETDatum₂ α n) (L : α → ℝ≥0)
    (hL : IsRauzyStep P L true) :
    (mkIETFun (P.lengthsInBottom L) P.perm 0) '' cellAt P [true] L (P.last false)
      ⊆ cellAt P [] L (P.last false) := by
  have hlt : P.lengthsInBottom L (lastPos n) < P.lengthsInBottom L (topCell P.perm) := by
    rw [lengthsInBottom_topCell, lengthsInBottom_lastPos]; exact hL
  have hsucc : (topCell P.perm).val + 1 < n := topCell_succ_lt hlt
  have hcell : cellAt P [true] L (P.last false)
      = cellHatT P.perm (P.lengthsInBottom L)
          ⟨(topCell P.perm).val + 1, hsucc⟩ := by
    rw [cellAt_singleton_true, cellHatL, IETDatum₂.piBottom_last_false P,
      eT_lastPos hlt]
  rw [hcell, mkIETFun_image_cellHatT_succ hlt, cellAt_nil,
    IETDatum₂.piBottom_last_false P]

/-! ## 7. The algebraic recursion of the heights -/

theorem sum_ite_single_int {c : α} (t : α → ℤ) :
    (∑ x, (if x = c then t x else 0)) = t c := by
  refine (Finset.sum_eq_single c ?_ ?_).trans (ite_eq_left rfl)
  · intro x _ hx; exact ite_eq_right hx
  · intro h; exact absurd (Finset.mem_univ c) h

/-- Multiplying a column of `Q` by `rvMat e` adds the main-name column to the secondary one. -/
theorem mulVec_rvMat (Q : Matrix α α ℤ) (V : IETDatum₂ α n) (e : Bool)
    (hne : V.last e ≠ V.last (!e)) (a b : α) :
    (∑ c, Q a c * V.rvMat e c b)
      = Q a b + if b = V.last (!e) then Q a (V.last e) else 0 := by
  have hterm (c : α) :
    Q a c * V.rvMat e c b
      = (if c = b then Q a c else 0)
        + (if c = V.last e then (if b = V.last (!e) then Q a c else 0) else 0) := by
    by_cases h1 : c = b
    · rw [h1, IETDatum₂.rvMat, ite_eq_left rfl, mul_one, ite_eq_left rfl]
      by_cases h3 : b = V.last e
      · rw [ite_eq_left h3]
        by_cases h2 : b = V.last (!e)
        · exact absurd (h3.symm.trans h2) hne
        · rw [ite_eq_right h2]; ring
      · rw [ite_eq_right h3]; ring
    · rw [ite_eq_right h1, IETDatum₂.rvMat, ite_eq_right h1, zero_add]
      by_cases h3 : c = V.last e
      · rw [ite_eq_left h3]
        by_cases h2 : b = V.last (!e)
        · rw [ite_eq_left h2, ite_eq_left ⟨h3, h2⟩, mul_one]
        · rw [ite_eq_right h2, ite_eq_right (fun h => h2 h.2), mul_zero]
      · rw [ite_eq_right h3, ite_eq_right (fun h => h3 h.1), mul_zero]
  calc (∑ c, Q a c * V.rvMat e c b)
      = ∑ c, ((if c = b then Q a c else 0)
          + (if c = V.last e then (if b = V.last (!e) then Q a c else 0) else 0)) :=
        Finset.sum_congr rfl (fun c _ => hterm c)
    _ = (∑ c, (if c = b then Q a c else 0))
          + ∑ c, (if c = V.last e then (if b = V.last (!e) then Q a c else 0) else 0) :=
        Finset.sum_add_distrib
    _ = Q a b + if b = V.last (!e) then Q a (V.last e) else 0 := by
        rw [sum_ite_single_int (c := b) (fun x => Q a x),
          sum_ite_single_int (c := V.last e) (fun x => if b = V.last (!e) then Q a x else 0)]

end IntervalExchange.RauzyVeech

end
