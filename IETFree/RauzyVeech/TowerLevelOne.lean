/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.TowerCells
public import IETFree.RauzyVeech.TowerInjectivity

/-!
# The level-one Rauzy-Veech tower in `IETDatum₂` letters (both step types)

Base case of the induction proving `TowerInjectivity.TowerTiling`: for one Rauzy step `e` at the
vertex `P` with lengths `L`, the floors `T^j '' cellAt P [e] L b`, `j < hgt1 P e b`, are a partition
of `Ico 0 (∑ L)`; the heights are the column sums of the elementary matrix `rvMat e`. -/

@[expose] public section


open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators Topology

namespace TowerInjectivity

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. The heights are the column sums of `rvMat e` -/

/-- The height of the level-one tower over `b`: the column sum of `rvMat e`. -/
def hgt1 (P : IETDatum₂ α n) (e : Bool) (b : α) : ℕ := ∑ a, (P.rvMat e a b).toNat

/-- The `ℕ`-valued entries of `rvMat`, as a case split. -/
theorem rvMatNat_eq (P : IETDatum₂ α n) (e : Bool) (a b : α) :
    P.rvMatNat e a b = if a = b then 1 else if a = P.last e ∧ b = P.last (!e) then 1 else 0 := by
  rw [IETDatum₂.rvMatNat, IETDatum₂.rvMat]
  split_ifs <;> simp

theorem sum_ite_single {c : α} (t : ℕ) :
    (∑ a, (if a = c then t else 0)) = t := by
  refine (Finset.sum_eq_single c ?_ ?_).trans (if_pos rfl)
  · intro a _ ha; exact if_neg ha
  · intro h; exact absurd (Finset.mem_univ c) h

/-- The column sums of `rvMat e`: `1` plus one on the secondary name. -/
theorem hgt1_eq (P : IETDatum₂ α n) (hne : ∀ e : Bool, P.last e ≠ P.last (!e))
    (e : Bool) (b : α) : hgt1 P e b = 1 + if b = P.last (!e) then 1 else 0 := by
  have hsplit (a : α) :
    P.rvMatNat e a b
      = (if a = b then 1 else 0)
        + (if a = P.last e then (if b = P.last (!e) then 1 else 0) else 0) := by
    rw [rvMatNat_eq]
    by_cases hab : a = b
    · rw [hab, if_pos rfl, if_pos rfl]
      by_cases h1 : b = P.last e
      · rw [if_pos h1]
        by_cases h2 : b = P.last (!e)
        · exact absurd (h1.symm.trans h2) (hne e)
        · rw [if_neg h2]
      · rw [if_neg h1]
    · rw [if_neg hab, if_neg hab]
      by_cases h1 : a = P.last e
      · rw [if_pos h1]
        by_cases h2 : b = P.last (!e)
        · rw [if_pos h2, if_pos ⟨h1, h2⟩]
        · rw [if_neg h2, if_neg (fun h => h2 h.2)]
      · rw [if_neg h1, if_neg (fun h : a = P.last e ∧ b = P.last (!e) => h1 h.1)]
  calc hgt1 P e b = ∑ a, P.rvMatNat e a b := rfl
    _ = ∑ a, ((if a = b then 1 else 0)
          + (if a = P.last e then (if b = P.last (!e) then 1 else 0) else 0)) :=
        Finset.sum_congr rfl (fun a _ => hsplit a)
    _ = (∑ a, (if a = b then (1:ℕ) else 0))
          + ∑ a, (if a = P.last e then (if b = P.last (!e) then 1 else 0) else 0) :=
        Finset.sum_add_distrib
    _ = 1 + (if b = P.last (!e) then 1 else 0) := by
        rw [sum_ite_single (c := b) 1, sum_ite_single (c := P.last e)]

/-- `returnB` of the level-one vertex, in letters, is `hgt1` of the false step. -/
theorem returnB_eq_hgt1 (P : IETDatum₂ α n) (hne : ∀ e : Bool, P.last e ≠ P.last (!e))
    (b : α) :
    Tower.returnB P.perm (P.piBottom b) = hgt1 P false b := by
  have hiff : (P.piBottom b = Tower.topCell P.perm) ↔ (b = P.last true) := by
    rw [← IETDatum₂.piBottom_last_true P, P.piBottom.injective.eq_iff]
  rw [hgt1_eq P hne, Tower.returnB]
  simp only [Bool.not_false]
  by_cases h : b = P.last true
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]

/-- `returnBT` of the level-one vertex, in letters, is `hgt1` of the true step. -/
theorem returnBT_eq_hgt1 (P : IETDatum₂ α n) (hne : ∀ e : Bool, P.last e ≠ P.last (!e))
    (b : α) :
    TowerTrue.returnBT P.perm (TowerTrue.eT P.perm (P.piBottom b)) = hgt1 P true b := by
  have hiff : (P.piBottom b = Tower.botCell) ↔ (b = P.last false) := by
    rw [← IETDatum₂.piBottom_last_false P, P.piBottom.injective.eq_iff]
  have hc : (TowerTrue.eT P.perm (P.piBottom b) = TowerTrue.eT P.perm Tower.botCell)
      ↔ (b = P.last false) := by
    rw [(TowerTrue.eT P.perm).injective.eq_iff, hiff]
  rw [hgt1_eq P hne, TowerTrue.returnBT]
  simp only [Bool.not_true, hc]
  by_cases h : b = P.last false
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

omit [Fintype α] [DecidableEq α] in
/-- Reindexing a union along an equivalence of the index types. -/
theorem iUnion_comp_equiv {β : Type*} {ι : Type*} (e : α ≃ β)
    (f : β → Set ι) :
    (⋃ a : α, f (e a)) = ⋃ b : β, f b := by
  ext x
  simp only [Set.mem_iUnion]
  exact ⟨fun ⟨a, ha⟩ => ⟨e a, ha⟩, fun ⟨b, hb⟩ => ⟨e.symm b, by simpa using hb⟩⟩

/-! ## 2. The tower union for one step of type `true` -/

/-- **Tower decomposition for a step of type `true`**: the whole interval is the base `Ico 0 (cutT)`
together with the image of the upper part of the top cell. -/
theorem tower_decomp_true {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    Set.Ico 0 (Tower.tot lam)
      = Set.Ico 0 (TowerTrue.cutT lam)
        ∪ Tower.exch π lam ''
            TowerTrue.cellHatT π lam
              (⟨(Tower.topCell π).val + 1, TowerTrue.topCell_succ_lt hlt⟩ : Fin n) := by
  have h0 : (0:ℝ) ≤ TowerTrue.cutT lam := by
    rw [TowerTrue.cutT]
    linarith [Tower.single_le_tot lam Tower.botCell]
  rw [TowerTrue.exch_image_cellHatT_succ hlt, TowerTrue.leftEnd_botCell_eq_cutT,
    Tower.upperEnd_botCell]
  ext z
  simp only [Set.mem_union, Set.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hc : z < TowerTrue.cutT lam
    · exact Or.inl ⟨h1, hc⟩
    · exact Or.inr ⟨le_of_not_gt hc, h2⟩
  · rintro (h | h)
    · exact ⟨h.1, lt_of_lt_of_le h.2 (TowerTrue.cutT_le_tot lam)⟩
    · exact ⟨le_trans h0 h.1, h.2⟩

/-- **The level-one tower union, type `true`** (in `Fin n` coordinates). -/
theorem iUnion_floor_true {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}
    (hlt : lam Tower.botCell < lam (Tower.topCell π)) :
    Set.Ico 0 (Tower.tot lam)
      = ⋃ β, ⋃ j : Fin (TowerTrue.returnBT π β),
          (Tower.exch π lam)^[(j : ℕ)] '' TowerTrue.cellHatT π lam β := by
  have hβ : TowerTrue.eT π Tower.botCell
      = (⟨(Tower.topCell π).val + 1, TowerTrue.topCell_succ_lt hlt⟩ : Fin n) :=
    TowerTrue.eT_botCell hlt
  have hmain : (⋃ β, ⋃ j : Fin (TowerTrue.returnBT π β),
        (Tower.exch π lam)^[(j : ℕ)] '' TowerTrue.cellHatT π lam β)
      = (⋃ β, TowerTrue.cellHatT π lam β)
        ∪ Tower.exch π lam '' TowerTrue.cellHatT π lam (TowerTrue.eT π Tower.botCell) := by
    ext x
    constructor
    · intro hx
      obtain ⟨β, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
      rcases Nat.eq_zero_or_pos ((j : ℕ)) with h0 | hpos
      · left
        exact Set.mem_iUnion.mpr ⟨β, by rw [h0] at hx; simpa using hx⟩
      · right
        have hle : TowerTrue.returnBT π β ≤ 2 := TowerTrue.returnBT_le_two π β
        have hj2 : TowerTrue.returnBT π β = 2 := by omega
        have hbβ : β = TowerTrue.eT π Tower.botCell := by
          rw [TowerTrue.returnBT] at hj2
          by_cases h : β = TowerTrue.eT π Tower.botCell
          · exact h
          · rw [if_neg h] at hj2; omega
        have hj1 : (j : ℕ) = 1 := by omega
        subst hbβ
        rw [hj1] at hx
        simpa using hx
    · rintro (hx | hx)
      · obtain ⟨β, hx⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨β,
          Set.mem_iUnion.mpr ⟨⟨0, TowerTrue.returnBT_pos π β⟩, by simpa using hx⟩⟩
      · refine Set.mem_iUnion.mpr ⟨TowerTrue.eT π Tower.botCell, Set.mem_iUnion.mpr
          ⟨⟨1, by rw [TowerTrue.returnBT_eq_two]; omega⟩, ?_⟩⟩
        simpa using hx
  rw [hmain, tower_decomp_true hlt, TowerTrue.iUnion_cellHatT hlt, ← hβ]

/-! ## 3. The level-one tower in letters, both types -/

/-- **The level-one tower, type `false`**, in letters. -/
theorem level_tower_false (P : IETDatum₂ α n) (hne : ∀ e : Bool, P.last e ≠ P.last (!e))
    (L : α → ℝ≥0) (hL : TowerTrue.StepOK P L false) :
    Set.Ico 0 (∑ b, (L b : ℝ))
      = ⋃ b, ⋃ j : Fin (hgt1 P false b),
          (Tower.exch P.perm (P.lengthsInBottom L))^[(j : ℕ)] '' Tower.cellAt P [false] L b := by
  have e1 : P.lengthsInBottom L (Tower.topCell P.perm) = L (P.last true) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_true P, Equiv.symm_apply_apply]
  have e2 : P.lengthsInBottom L Tower.botCell = L (P.last false) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_false P, Equiv.symm_apply_apply]
  have hlt : P.lengthsInBottom L (Tower.topCell P.perm) < P.lengthsInBottom L Tower.botCell := by
    rw [e1, e2]; exact hL
  have h := Tower.tower_decomp_iUnion (π := P.perm) (lam := P.lengthsInBottom L) hlt
  rw [TowerTrue.tot_lengthsInBottom_eq] at h
  simp only [TowerTrue.sumA] at h
  rw [h, ← iUnion_comp_equiv P.piBottom
    (fun β => ⋃ j : Fin (Tower.returnB P.perm β),
      (Tower.exch P.perm (P.lengthsInBottom L))^[(j : ℕ)] ''
        Tower.cellHat P.perm (P.lengthsInBottom L) β)]
  refine Set.iUnion_congr (fun b => ?_)
  rw [returnB_eq_hgt1 P hne b, ← TowerTrue.cellAt_singleton_false]

/-- **The level-one tower, type `true`**, in letters. -/
theorem level_tower_true (P : IETDatum₂ α n) (hne : ∀ e : Bool, P.last e ≠ P.last (!e))
    (L : α → ℝ≥0) (hL : TowerTrue.StepOK P L true) :
    Set.Ico 0 (∑ b, (L b : ℝ))
      = ⋃ b, ⋃ j : Fin (hgt1 P true b),
          (Tower.exch P.perm (P.lengthsInBottom L))^[(j : ℕ)] '' Tower.cellAt P [true] L b := by
  have e1 : P.lengthsInBottom L (Tower.topCell P.perm) = L (P.last true) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_true P, Equiv.symm_apply_apply]
  have e2 : P.lengthsInBottom L Tower.botCell = L (P.last false) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_false P, Equiv.symm_apply_apply]
  have hlt : P.lengthsInBottom L Tower.botCell < P.lengthsInBottom L (Tower.topCell P.perm) := by
    rw [e1, e2]; exact hL
  have h := iUnion_floor_true (π := P.perm) (lam := P.lengthsInBottom L) hlt
  rw [TowerTrue.tot_lengthsInBottom_eq] at h
  simp only [TowerTrue.sumA] at h
  rw [h, ← iUnion_comp_equiv (P.piBottom.trans (TowerTrue.eT P.perm))
    (fun β => ⋃ j : Fin (TowerTrue.returnBT P.perm β),
      (Tower.exch P.perm (P.lengthsInBottom L))^[(j : ℕ)] '' TowerTrue.cellHatT P.perm
        (P.lengthsInBottom L) β)]
  refine Set.iUnion_congr (fun b => ?_)
  rw [show (P.piBottom.trans (TowerTrue.eT P.perm)) b
      = TowerTrue.eT P.perm (P.piBottom b) from rfl,
    returnBT_eq_hgt1 P hne b, ← TowerTrue.cellHatL, ← TowerTrue.cellAt_singleton_true]

/-! ## 5. The first-return map of the level-one tower is the renormalised exchange  This is piece
(1) of the induction step towards `TowerTiling`: on each level-one cell the first return of `T` to
the cut interval is the new exchange, with return time `hgt1 P e b`. -/

theorem firstReturn_false (P : IETDatum₂ α n) (hne : ∀ e : Bool, P.last e ≠ P.last (!e))
    (L : α → ℝ≥0) (hL : TowerTrue.StepOK P L false) (b : α) {y : ℝ}
    (hy : y ∈ Tower.cellAt P [false] L b) :
    (Tower.exch P.perm (P.lengthsInBottom L))^[hgt1 P false b] y
      = (Tower.exch (P.rvStep false).perm
          ((P.rvStep false).lengthsInBottom (Tower.hatLam P false L))) y := by
  have e1 : P.lengthsInBottom L (Tower.topCell P.perm) = L (P.last true) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_true P, Equiv.symm_apply_apply]
  have e2 : P.lengthsInBottom L Tower.botCell = L (P.last false) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_false P, Equiv.symm_apply_apply]
  have hlt : P.lengthsInBottom L (Tower.topCell P.perm) < P.lengthsInBottom L Tower.botCell := by
    rw [e1, e2]; exact hL
  have hy' : y ∈ Tower.cellHat P.perm (P.lengthsInBottom L) (P.piBottom b) := by
    rw [← TowerTrue.cellAt_singleton_false]; exact hy
  have hyc : y ∈ Set.Ico 0 (Tower.cut P.perm (P.lengthsInBottom L)) :=
    Tower.cellHat_subset_cut hlt (P.piBottom b) hy'
  have hret : Tower.ret P.perm (P.lengthsInBottom L) y = hgt1 P false b := by
    rw [Tower.ret_eq_returnB hlt hy', returnB_eq_hgt1 P hne b]
  rw [← hret, Tower.firstReturn_eq hlt hyc]
  rw [← TowerTrue.exch_rvStep_false_hatLam P L]
  rfl

theorem firstReturn_true (P : IETDatum₂ α n) (hne : ∀ e : Bool, P.last e ≠ P.last (!e))
    (L : α → ℝ≥0) (hL : TowerTrue.StepOK P L true) (b : α) {y : ℝ}
    (hy : y ∈ Tower.cellAt P [true] L b) :
    (Tower.exch P.perm (P.lengthsInBottom L))^[hgt1 P true b] y
      = (Tower.exch (P.rvStep true).perm
          ((P.rvStep true).lengthsInBottom (Tower.hatLam P true L))) y := by
  have e1 : P.lengthsInBottom L (Tower.topCell P.perm) = L (P.last true) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_true P, Equiv.symm_apply_apply]
  have e2 : P.lengthsInBottom L Tower.botCell = L (P.last false) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_false P, Equiv.symm_apply_apply]
  have hlt : P.lengthsInBottom L Tower.botCell < P.lengthsInBottom L (Tower.topCell P.perm) := by
    rw [e1, e2]; exact hL
  have hy' : y ∈ TowerTrue.cellHatT P.perm (P.lengthsInBottom L)
      (TowerTrue.eT P.perm (P.piBottom b)) := by
    rw [← TowerTrue.cellHatL, ← TowerTrue.cellAt_singleton_true]; exact hy
  have hyc : y ∈ Set.Ico 0 (TowerTrue.cutT (P.lengthsInBottom L)) :=
    TowerTrue.cellHatT_subset_cutT hlt _ hy'
  have hret : TowerTrue.retT P.perm (P.lengthsInBottom L) y = hgt1 P true b := by
    rw [TowerTrue.retT_eq_returnBT hlt hy', returnBT_eq_hgt1 P hne b]
  rw [← hret, TowerTrue.firstReturnT_eq hlt hyc]
  rw [← TowerTrue.exch_rvStep_true_hatLam P L]
  rfl

/-! ## 6. The two names: where the level-one cells sit and where the top floor goes -/

theorem cellAt_nil (P : IETDatum₂ α n) (L : α → ℝ≥0) (b : α) :
    Tower.cellAt P [] L b
      = Set.Ico (leftEnd (P.lengthsInBottom L) (P.piBottom b))
          (upperEnd (P.lengthsInBottom L) (P.piBottom b)) := rfl

/-- **False step, nesting**: every level-one cell sits in its level-zero cell. -/
theorem names_false_sub (P : IETDatum₂ α n) (L : α → ℝ≥0) (b : α) :
    Tower.cellAt P [false] L b ⊆ Tower.cellAt P [] L b := by
  rw [TowerTrue.cellAt_singleton_false, cellAt_nil]
  exact TowerCells.cellHat_subset_dom _ _ _

/-- **False step, the second floor lands in the cell of the main name.** -/
theorem names_false_image (P : IETDatum₂ α n) (L : α → ℝ≥0)
    (hL : TowerTrue.StepOK P L false) :
    (Tower.exch P.perm (P.lengthsInBottom L)) '' Tower.cellAt P [false] L (P.last true)
      ⊆ Tower.cellAt P [] L (P.last false) := by
  have e1 : P.lengthsInBottom L (Tower.topCell P.perm) = L (P.last true) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_true P, Equiv.symm_apply_apply]
  have e2 : P.lengthsInBottom L Tower.botCell = L (P.last false) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_false P, Equiv.symm_apply_apply]
  have hlt : P.lengthsInBottom L (Tower.topCell P.perm) < P.lengthsInBottom L Tower.botCell := by
    rw [e1, e2]; exact hL
  have hcell : Tower.cellAt P [false] L (P.last true)
      = Set.Ico (leftEnd (P.lengthsInBottom L) (Tower.topCell P.perm))
          (upperEnd (P.lengthsInBottom L) (Tower.topCell P.perm)) := by
    rw [TowerTrue.cellAt_singleton_false, IETDatum₂.piBottom_last_true P,
      Tower.cellHat_topCell hlt]
  have himg := Tower.exch_image_topCell (π := P.perm) (lam := P.lengthsInBottom L) hlt
  rw [hcell, himg, cellAt_nil, IETDatum₂.piBottom_last_false P]
  -- `Ico (cut) (tot) ⊆ Ico (leftEnd botCell) (upperEnd botCell)`
  have hbot : leftEnd (P.lengthsInBottom L) Tower.botCell
      = Tower.tot (P.lengthsInBottom L) - (P.lengthsInBottom L Tower.botCell : ℝ) :=
    Tower.leftEnd_botCell _
  have hup : upperEnd (P.lengthsInBottom L) Tower.botCell = Tower.tot (P.lengthsInBottom L) :=
    Tower.upperEnd_botCell _
  have hcut : Tower.cut P.perm (P.lengthsInBottom L)
      = Tower.tot (P.lengthsInBottom L) - (P.lengthsInBottom L (Tower.topCell P.perm) : ℝ) := rfl
  have hle : (P.lengthsInBottom L (Tower.topCell P.perm) : ℝ)
      ≤ (P.lengthsInBottom L Tower.botCell : ℝ) := le_of_lt (by exact_mod_cast hlt)
  rw [hbot, hup]
  refine Set.Ico_subset_Ico ?_ le_rfl
  rw [hcut]
  linarith

/-- **True step, nesting**: every level-one cell but the one over the bottom name sits in its
level-zero cell. -/
theorem names_true_sub (P : IETDatum₂ α n) (L : α → ℝ≥0)
    (hL : TowerTrue.StepOK P L true) (a : α) (ha : a ≠ P.last false) :
    Tower.cellAt P [true] L a ⊆ Tower.cellAt P [] L a := by
  have e1 : P.lengthsInBottom L (Tower.topCell P.perm) = L (P.last true) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_true P, Equiv.symm_apply_apply]
  have e2 : P.lengthsInBottom L Tower.botCell = L (P.last false) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_false P, Equiv.symm_apply_apply]
  have hlt : P.lengthsInBottom L Tower.botCell < P.lengthsInBottom L (Tower.topCell P.perm) := by
    rw [e1, e2]; exact hL
  rw [TowerTrue.cellAt_singleton_true, TowerTrue.cellHatL, cellAt_nil]
  set β := P.piBottom a with hβ
  rcases lt_trichotomy β.val (Tower.topCell P.perm).val with hlt2 | heq | hgt2
  · rw [TowerTrue.eT_apply_le (le_of_lt hlt2), TowerTrue.cellHatT_of_lt hlt hlt2]
  · have hβtop : β = Tower.topCell P.perm := Fin.ext heq
    rw [hβtop, TowerTrue.eT_apply_le le_rfl, TowerTrue.cellHatT_top hlt]
    refine Set.Ico_subset_Ico le_rfl ?_
    rw [TowerTrue.splitT, upperEnd_eq]
    linarith
  · have hβbot : β ≠ Tower.botCell := by
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
    have hval : (TowerTrue.eT P.perm β).val = β.val + 1 := TowerTrue.eT_apply_gt hlt hgt2 hβbot
    have hE : TowerTrue.eT P.perm β = TowerTrue.succFin β hβlt :=
      Fin.ext (by rw [hval, TowerTrue.succFin_val])
    rw [hE, TowerTrue.cellHatT_of_gt hlt hgt2 hβlt]

/-- **True step**: the cell over the bottom name sits in the cell of the top name. -/
theorem names_true_sub_scd (P : IETDatum₂ α n) (L : α → ℝ≥0)
    (hL : TowerTrue.StepOK P L true) :
    Tower.cellAt P [true] L (P.last false) ⊆ Tower.cellAt P [] L (P.last true) := by
  have e1 : P.lengthsInBottom L (Tower.topCell P.perm) = L (P.last true) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_true P, Equiv.symm_apply_apply]
  have e2 : P.lengthsInBottom L Tower.botCell = L (P.last false) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_false P, Equiv.symm_apply_apply]
  have hlt : P.lengthsInBottom L Tower.botCell < P.lengthsInBottom L (Tower.topCell P.perm) := by
    rw [e1, e2]; exact hL
  have hsucc : (Tower.topCell P.perm).val + 1 < n := TowerTrue.topCell_succ_lt hlt
  have hcell : Tower.cellAt P [true] L (P.last false)
      = Set.Ico (TowerTrue.splitT P.perm (P.lengthsInBottom L))
          (upperEnd (P.lengthsInBottom L) (Tower.topCell P.perm)) := by
    rw [TowerTrue.cellAt_singleton_true, TowerTrue.cellHatL, IETDatum₂.piBottom_last_false P,
      TowerTrue.eT_botCell hlt, TowerTrue.cellHatT_succ hlt]
  have hnm : Tower.cellAt P [] L (P.last true)
      = Set.Ico (leftEnd (P.lengthsInBottom L) (Tower.topCell P.perm))
          (upperEnd (P.lengthsInBottom L) (Tower.topCell P.perm)) := by
    rw [cellAt_nil, IETDatum₂.piBottom_last_true P]
  rw [hcell, hnm, TowerTrue.splitT]
  refine Set.Ico_subset_Ico ?_ le_rfl
  linarith

/-- **True step, the second floor lands in the cell of the bottom name.** -/
theorem names_true_image (P : IETDatum₂ α n) (L : α → ℝ≥0)
    (hL : TowerTrue.StepOK P L true) :
    (Tower.exch P.perm (P.lengthsInBottom L)) '' Tower.cellAt P [true] L (P.last false)
      ⊆ Tower.cellAt P [] L (P.last false) := by
  have e1 : P.lengthsInBottom L (Tower.topCell P.perm) = L (P.last true) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_true P, Equiv.symm_apply_apply]
  have e2 : P.lengthsInBottom L Tower.botCell = L (P.last false) := by
    simp only [IETDatum₂.lengthsInBottom, ← IETDatum₂.piBottom_last_false P, Equiv.symm_apply_apply]
  have hlt : P.lengthsInBottom L Tower.botCell < P.lengthsInBottom L (Tower.topCell P.perm) := by
    rw [e1, e2]; exact hL
  have hsucc : (Tower.topCell P.perm).val + 1 < n := TowerTrue.topCell_succ_lt hlt
  have hcell : Tower.cellAt P [true] L (P.last false)
      = TowerTrue.cellHatT P.perm (P.lengthsInBottom L)
          ⟨(Tower.topCell P.perm).val + 1, hsucc⟩ := by
    rw [TowerTrue.cellAt_singleton_true, TowerTrue.cellHatL, IETDatum₂.piBottom_last_false P,
      TowerTrue.eT_botCell hlt]
  rw [hcell, TowerTrue.exch_image_cellHatT_succ hlt, cellAt_nil, IETDatum₂.piBottom_last_false P]

/-! ## 7. The algebraic recursion of the heights -/

theorem sum_ite_single_int {c : α} (t : α → ℤ) :
    (∑ x, (if x = c then t x else 0)) = t c := by
  refine (Finset.sum_eq_single c ?_ ?_).trans (if_pos rfl)
  · intro x _ hx; exact if_neg hx
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
    · rw [h1, IETDatum₂.rvMat, if_pos rfl, mul_one, if_pos rfl]
      by_cases h3 : b = V.last e
      · rw [if_pos h3]
        by_cases h2 : b = V.last (!e)
        · exact absurd (h3.symm.trans h2) hne
        · rw [if_neg h2]; ring
      · rw [if_neg h3]; ring
    · rw [if_neg h1, IETDatum₂.rvMat, if_neg h1, zero_add]
      by_cases h3 : c = V.last e
      · rw [if_pos h3]
        by_cases h2 : b = V.last (!e)
        · rw [if_pos h2, if_pos ⟨h3, h2⟩, mul_one]
        · rw [if_neg h2, if_neg (fun h => h2 h.2), mul_zero]
      · rw [if_neg h3, if_neg (fun h => h3 h.1), mul_zero]
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

end TowerInjectivity

end
