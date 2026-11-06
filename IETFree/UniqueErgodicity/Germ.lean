/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.UniqueErgodicity.Limits
public import IETFree.UniqueErgodicity.Split

/-!
# The germ map of an interval exchange

Blueprint 2, §3: for the interval exchange `T = mkIETEquiv lam π 0` of `[0,1)` with cut set
`s = mkIETCuts lam 0 1` and split set `D = splitSet T s`, we build the germ map `T̃` of the split
interval `SplitI D`:

* the right germ of `x` is sent to the right germ of `T x`;
* the left germ of `x` is sent to the left germ of `L x`, where `L` is the left limit of `T`
  (`Limits.lean`).

We prove that `D` is invariant under `T`, that the left germ of `0` does not belong to the right
part, that `T̃` maps the split interval to itself, is injective, preserves the right part, and is
continuous (Lemmas 3.1–3.5 of the blueprint).
-/

@[expose] public section

open Set Function Filter Topology
open scoped BigOperators NNReal

namespace IETFree.UniqueErgodicity

/-! ## Invariance of the split set -/

/-- **Lemma 1.7 (ii)**: the split set of an exchange is invariant under the exchange, as the union
of the orbits of `s ∪ {1}`. -/
theorem image_splitSet_eq (T : ℝ ≃ ℝ) (s : Finset ℝ) :
    ⇑T '' splitSet T s = splitSet T s := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    obtain ⟨v, hv, hveq⟩ := hk
    refine Set.mem_iUnion.mpr ⟨k + 1, v, hv, ?_⟩
    show ⇑(T ^ (k + 1)) v = ⇑T x
    rw [← hveq, show k + 1 = 1 + k by ring, zpow_one_add]
    rfl
  · intro y hy
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
    obtain ⟨w, hw, hwk⟩ := hk
    have hD : ⇑(T ^ (k - 1)) w ∈ splitSet T s := Set.mem_iUnion.mpr ⟨k - 1, w, hw, rfl⟩
    have hTy : ⇑T (⇑(T ^ (k - 1)) w) = y := by
      rw [← hwk]
      have hstep : (T : ℝ ≃ ℝ) ^ k = T * T ^ (k - 1) := by
        conv_lhs => rw [show k = 1 + (k - 1) by ring]
        rw [zpow_one_add]
      rw [hstep]
      rfl
    exact ⟨_, hD, hTy⟩

/-! ## The side of a point of the split interval -/

section Side

variable {D : Set ℝ}

/-- A point of the split interval whose side is `true` is the right germ of its projection. -/
theorem eq_rightGerm_of_side_true {z : SplitI D} (h : SplitI.side z = true) :
    z = SplitI.rightGerm (D := D) (SplitI.proj z) (SplitI.proj_mem_Icc z) := by
  by_cases hxD : SplitI.proj z ∈ D
  · have hcoord : z.1.2 ⟨SplitI.proj z, hxD⟩ = true := by
      rw [SplitI.side, dif_pos hxD] at h
      exact h
    exact SplitI.eq_rightGerm_of_coord_true (SplitI.proj_mem_Icc z) hxD rfl hcoord
  · have h2 : SplitI.rightGerm (D := D) (SplitI.proj z) (SplitI.proj_mem_Icc z)
        = SplitI.leftGerm (D := D) (SplitI.proj z) (SplitI.proj_mem_Icc z) :=
      SplitI.rightGerm_eq_leftGerm hxD (SplitI.proj_mem_Icc z)
    rcases SplitI.eq_rightGerm_or_leftGerm z with hz | hz
    · exact hz
    · exact hz.trans h2.symm

/-- A point of the split interval whose side is `false` is the left germ of its projection. -/
theorem eq_leftGerm_of_side_false {z : SplitI D} (h : SplitI.side z = false) :
    z = SplitI.leftGerm (D := D) (SplitI.proj z) (SplitI.proj_mem_Icc z) := by
  by_cases hxD : SplitI.proj z ∈ D
  · have hcoord : z.1.2 ⟨SplitI.proj z, hxD⟩ = false := by
      rw [SplitI.side, dif_pos hxD] at h
      exact h
    exact SplitI.eq_leftGerm_of_coord_false (SplitI.proj_mem_Icc z) hxD rfl hcoord
  · have h2 : SplitI.rightGerm (D := D) (SplitI.proj z) (SplitI.proj_mem_Icc z)
        = SplitI.leftGerm (D := D) (SplitI.proj z) (SplitI.proj_mem_Icc z) :=
      SplitI.rightGerm_eq_leftGerm hxD (SplitI.proj_mem_Icc z)
    rcases SplitI.eq_rightGerm_or_leftGerm z with hz | hz
    · exact hz.trans h2
    · exact hz

/-- The side is `false` only at split points. -/
theorem mem_of_side_eq_false {z : SplitI D} (h : SplitI.side z = false) :
    SplitI.proj z ∈ D := by
  by_contra hxD
  rw [SplitI.side, dif_neg hxD] at h
  simp at h

/-- The point of `upSet x` projecting to `x` is the right germ of `x`. -/
theorem eq_rightGerm_of_mem_upSet {x : ℝ} {hx : x ∈ Set.Icc (0 : ℝ) 1} {z : SplitI D}
    (hz : z ∈ SplitI.upSet x hx) (hp : SplitI.proj z = x) :
    z = SplitI.rightGerm x hx := by
  rcases hz with hz | hz
  · have hz' : x < SplitI.proj z := hz
    exact absurd (hp ▸ hz') (lt_irrefl x)
  · exact hz

/-- The point of `downSet x` projecting to `x` is the left germ of `x`. -/
theorem eq_leftGerm_of_mem_downSet {x : ℝ} {hx : x ∈ Set.Icc (0 : ℝ) 1} {z : SplitI D}
    (hz : z ∈ SplitI.downSet x hx) (hp : SplitI.proj z = x) :
    z = SplitI.leftGerm x hx := by
  rcases hz with hz | hz
  · have hz' : SplitI.proj z < x := hz
    exact absurd (hp ▸ hz') (lt_irrefl x)
  · exact hz

end Side

/-- **The left germ of `0` is not in the right part** (used in §4.4 of the blueprint to show that
the left germ of the left end carries no mass). -/
theorem leftGerm_zero_notMem_rightPart_of_mem {D : Set ℝ} (h0 : (0 : ℝ) ∈ D) :
    SplitI.leftGerm (D := D) 0 ⟨le_rfl, zero_le_one⟩ ∉ SplitI.rightPart D := by
  intro hmem
  have hclosed : IsClosed {z : SplitI D | z.1.2 ⟨0, h0⟩ = true} :=
    isClosed_eq (SplitI.continuous_coord ⟨0, h0⟩) continuous_const
  have hsub : Set.range (fun x : Set.Ico (0 : ℝ) 1 =>
      SplitI.rightGerm (D := D) x.1 ⟨x.2.1, le_of_lt x.2.2⟩)
      ⊆ {z : SplitI D | z.1.2 ⟨0, h0⟩ = true} := by
    rintro z ⟨x, rfl⟩
    exact decide_eq_true_iff.mpr x.2.1
  have h1 := (IsClosed.closure_subset_iff hclosed).mpr hsub hmem
  have h2 : decide ((0 : ℝ) < 0) = true := h1
  simp at h2

/-! ## The right end of the image of a cell

Lemma 1.7 (iii) of the blueprint: the left limit maps the split set into itself.  On a cut `c` it is
the right end of the image of the cell of `c`, and the right end of the image of a cell is either
`1` or the left end of the image of another cell, hence again in the split set.
-/

section CellEnd

variable {f : ℝ → ℝ} {e : ℝ ≃ ℝ} {s : Finset ℝ}

/-- The exchange maps `[0,1]` into itself. -/
theorem mapsTo_Icc (hT : IsCutSet (⇑e) 0 1 s) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ⇑e x ∈ Set.Icc (0 : ℝ) 1 := by
  rcases eq_or_lt_of_le hx.2 with h1 | h1
  · subst h1
    rw [hT.apply_eq_self_of_le 1 le_rfl]
    exact ⟨zero_le_one, le_rfl⟩
  · exact ⟨(hT.mapsTo x ⟨hx.1, h1⟩).1, le_of_lt (hT.mapsTo x ⟨hx.1, h1⟩).2⟩

/-- If `c` is a cut, `x` is `1` or a cut, `c < x`, and no cut lies strictly between `c` and `x`,
then the cell starting at `c` ends at `x`. -/
theorem cellPos_of_next (h : IsCutSet f 0 1 s) {c x : ℝ} (hc : c ∈ s)
    (hx : x = 1 ∨ x ∈ s) (hcx : c < x) (hno : ∀ d ∈ s, c < d → x ≤ d) :
    ∃ i : Fin s.card, h.cellStarts i = c ∧ h.cellPos (i.val + 1) = x := by
  obtain ⟨i, hi⟩ := h.cellStarts_surj hc
  rcases hx with rfl | hxs
  · have hlast : i.val + 1 = s.card := by
      by_contra hcon
      have hlt : i.val + 1 < s.card := by omega
      have hmem : h.cellStarts ⟨i.val + 1, hlt⟩ ∈ s := h.cellStarts_mem _
      have hgt : c < h.cellStarts ⟨i.val + 1, hlt⟩ := by
        rw [← hi]
        exact h.cellStarts_strictMono (Fin.lt_def.mpr (by simp))
      have h1 := hno _ hmem hgt
      have h2 := (h.cellStarts_mem_Ico ⟨i.val + 1, hlt⟩).2
      linarith
    refine ⟨i, hi, ?_⟩
    rcases h.cellPos_succ i with ⟨hlt, _⟩ | ⟨_, hh⟩
    · omega
    · exact hh
  · obtain ⟨k, hk⟩ := h.cellStarts_surj hxs
    have hik : i < k := by
      rw [← h.cellStarts_lt_iff, hi, hk]
      exact hcx
    have hsucc : i.val + 1 = k.val := by
      by_contra hcon
      have hlt : i.val + 1 < k.val := by
        omega
      have hmem : h.cellStarts ⟨i.val + 1, by omega⟩ ∈ s := h.cellStarts_mem _
      have hgt : c < h.cellStarts ⟨i.val + 1, by omega⟩ := by
        rw [← hi]
        exact h.cellStarts_strictMono (Fin.lt_def.mpr (by simp))
      have h1 := hno _ hmem hgt
      have h2 : h.cellStarts ⟨i.val + 1, by omega⟩ < x := by
        rw [← hk]
        exact h.cellStarts_strictMono (Fin.lt_def.mpr hlt)
      linarith
    have hpos : h.cellPos (i.val + 1) = x := by
      rw [h.cellPos_of_lt (by omega : i.val + 1 < s.card)]
      have : (⟨i.val + 1, by omega⟩ : Fin s.card) = k := Fin.ext hsucc
      rw [this, hk]
    exact ⟨i, hi, hpos⟩

/-- **The right end of the image of a cell is `1` or the left end of the image of a cell.** -/
theorem image_cell_right_end (h : IsCutSet (⇑e) 0 1 s) (i : Fin s.card) :
    ⇑e (h.cellStarts i) + h.cellLen i = 1 ∨
      ∃ j : Fin s.card, ⇑e (h.cellStarts j) = ⇑e (h.cellStarts i) + h.cellLen i := by
  set z := ⇑e (h.cellStarts i) + h.cellLen i with hz
  have hβ := h.cellStarts_mem_Ico i
  have hβ1 : h.cellPos i.val = h.cellStarts i := h.cellPos_of_lt i.isLt
  have hlt2 : h.cellStarts i < h.cellPos (i.val + 1) := by
    rcases h.cellPos_succ i with ⟨hlt, hh⟩ | ⟨heq, hh⟩
    · rw [hh]
      exact h.cellStarts_strictMono (Fin.lt_def.mpr (by simp))
    · rw [hh]
      exact hβ.2
  have hlen_pos : 0 < h.cellLen i := by
    rw [IsCutSet.cellLen, hβ1]
    linarith
  have hfβ := h.mapsTo _ hβ
  have hfβz : ⇑e (h.cellStarts i) < z := by rw [hz]; linarith
  have hle : z ≤ 1 := by
    by_contra hcon
    rw [not_le] at hcon
    set y := (1 + z) / 2 with hy
    have hy1 : ⇑e (h.cellStarts i) < y := by rw [hy, hz]; linarith [hfβ.2]
    have hy2 : y < z := by rw [hy]; linarith
    have hmem : y ∈ ⇑e '' Set.Ico (h.cellStarts i) (h.cellPos (i.val + 1)) := by
      rw [h.image_cell i, ← hz]
      exact ⟨hy1.le, hy2⟩
    have hsub : ⇑e '' Set.Ico (h.cellStarts i) (h.cellPos (i.val + 1)) ⊆
        Set.Ico (0 : ℝ) 1 := by
      rw [← Equiv.IsIET.image_cells_union h]
      exact Set.subset_iUnion (fun j : Fin s.card =>
        ⇑e '' Set.Ico (h.cellStarts j) (h.cellPos (j.val + 1))) i
    have := hsub hmem
    linarith [this.2]
  rcases eq_or_lt_of_le hle with h1 | h1
  · exact Or.inl h1
  · right
    have hzmem : z ∈ Set.Ico (0 : ℝ) 1 := ⟨by rw [hz]; linarith [hfβ.1], h1⟩
    have hcover : z ∈ ⋃ j : Fin s.card,
        ⇑e '' Set.Ico (h.cellStarts j) (h.cellPos (j.val + 1)) := by
      rw [Equiv.IsIET.image_cells_union h]
      exact hzmem
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hcover
    rw [h.image_cell j] at hj
    have hji : j ≠ i := by
      rintro rfl
      rw [hz] at hj
      exact absurd hj.2 (lt_irrefl z)
    have hjeq : ⇑e (h.cellStarts j) = z := by
      by_contra hne
      have hlt : ⇑e (h.cellStarts j) < z := lt_of_le_of_ne hj.1 hne
      set y := (max (⇑e (h.cellStarts j)) (⇑e (h.cellStarts i)) + z) / 2 with hy
      have hy1 : ⇑e (h.cellStarts j) < y := by
        rw [hy]; linarith [le_max_left (⇑e (h.cellStarts j)) (⇑e (h.cellStarts i))]
      have hy2 : y < z := by
        rw [hy]; linarith [max_lt hlt hfβz]
      have hy3 : ⇑e (h.cellStarts i) < y := by
        rw [hy]; linarith [le_max_right (⇑e (h.cellStarts j)) (⇑e (h.cellStarts i))]
      have hmi : y ∈ ⇑e '' Set.Ico (h.cellStarts i) (h.cellPos (i.val + 1)) := by
        rw [h.image_cell i, ← hz]
        exact ⟨hy3.le, hy2⟩
      have hmj : y ∈ ⇑e '' Set.Ico (h.cellStarts j) (h.cellPos (j.val + 1)) := by
        rw [h.image_cell j]
        exact ⟨hy1.le, lt_trans hy2 hj.2⟩
      exact (Set.disjoint_left.mp (h.image_cell_disjoint e.injective hji) hmj) hmi
    exact ⟨j, hjeq⟩

/-- The right end of the image of the cell of a cut, expressed through `cutBelow`: if `x` is a cut
(or `1`) and `c = cutBelow h x`, then `x + (e c - c)` lies in the split set. -/
theorem rightEnd_mem (hT : IsCutSet (⇑e) 0 1 s) {c x : ℝ} (hc : c ∈ s)
    (hx : x = 1 ∨ x ∈ s) (hcx : c < x) (hno : ∀ d ∈ s, c < d → x ≤ d) :
    x + (⇑e c - c) ∈ splitSet e s := by
  obtain ⟨i, hi, hpos⟩ := cellPos_of_next hT hc hx hcx hno
  have hlen : hT.cellLen i = x - c := by
    rw [IsCutSet.cellLen, hpos, hT.cellPos_of_lt i.isLt, hi]
  have hkey : x + (⇑e c - c) = ⇑e (hT.cellStarts i) + hT.cellLen i := by
    rw [hlen, hi]; ring
  rcases image_cell_right_end hT i with hb | ⟨j, hj⟩
  · rw [hkey, hb]
    exact one_mem_splitSet e s
  · rw [hkey, ← hj, ← image_splitSet_eq e s]
    exact ⟨_, mem_splitSet_of_mem e s (hT.cellStarts_mem j), rfl⟩

/-- **Lemma 1.7 (iii)**: the left limit of an exchange maps the split set into itself. -/
theorem leftLimit_mem_splitSet (hT : IsCutSet (⇑e) 0 1 s) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hxD : x ∈ splitSet e s) :
    leftLimit hT x ∈ splitSet e s := by
  rcases eq_or_lt_of_le hx.2 with hx1 | hx1
  · subst hx1
    rw [leftLimit_eq_add hT ⟨zero_lt_one, le_rfl⟩]
    refine rightEnd_mem hT (cutBelow_mem hT zero_lt_one) (Or.inl rfl)
      (cutBelow_lt hT zero_lt_one) ?_
    intro d hd hcd
    exact absurd (lt_cutBelow hT zero_lt_one hd (hT.cuts_mem d hd).2) (not_le.mpr hcd)
  · have hxIco : x ∈ Set.Ico (0 : ℝ) 1 := ⟨hx.1, hx1⟩
    by_cases hxs : x ∈ s
    · rcases eq_or_lt_of_le hx.1 with hx0 | hx0
      · subst hx0
        rw [leftLimit_of_le hT le_rfl]
        exact mem_splitSet_of_mem e s hxs
      · rw [leftLimit_eq_add hT ⟨hx0, hx1.le⟩]
        refine rightEnd_mem hT (cutBelow_mem hT hx0) (Or.inr hxs) (cutBelow_lt hT hx0) ?_
        intro d hd hcd
        by_contra hcon
        rw [not_le] at hcon
        exact absurd (lt_cutBelow hT hx0 hd hcon) (not_le.mpr hcd)
    · rw [leftLimit_eq_apply hT hxIco hxs, ← image_splitSet_eq e s]
      exact ⟨x, hxD, rfl⟩

end CellEnd

/-! ## The germ map of an exchange -/

section GermMap

variable {T : ℝ ≃ ℝ} {s : Finset ℝ}

/-- The projection coordinate `x'` of the germ map (Definition 3.1 of the blueprint): the left
limit at the left germs of split points, the exchange itself everywhere else. -/
noncomputable def germProjOf (hT : IsCutSet (⇑T) 0 1 s) (z : SplitI (splitSet T s)) : ℝ := by
  classical
  exact if h : SplitI.proj z ∈ splitSet T s then
    (if SplitI.side z = false then leftLimit hT (SplitI.proj z) else ⇑T (SplitI.proj z))
  else ⇑T (SplitI.proj z)

/-- At a left germ, the projection coordinate of the germ map is the left limit. -/
theorem germProjOf_of_side_false (hT : IsCutSet (⇑T) 0 1 s) {z : SplitI (splitSet T s)}
    (h : SplitI.side z = false) : germProjOf hT z = leftLimit hT (SplitI.proj z) := by
  have hD := mem_of_side_eq_false h
  unfold germProjOf
  split_ifs
  rfl

/-- At a right germ, the projection coordinate of the germ map is the exchange. -/
theorem germProjOf_of_side_true (hT : IsCutSet (⇑T) 0 1 s) {z : SplitI (splitSet T s)}
    (h : SplitI.side z = true) : germProjOf hT z = ⇑T (SplitI.proj z) := by
  unfold germProjOf
  split_ifs with hD hs
  · rw [h] at hs
    exact absurd hs (by simp)
  · rfl
  · rfl

/-- Off the split set, both germs coincide and the projection coordinate is the exchange. -/
theorem germProjOf_of_notMem (hT : IsCutSet (⇑T) 0 1 s) {z : SplitI (splitSet T s)}
    (h : SplitI.proj z ∉ splitSet T s) : germProjOf hT z = ⇑T (SplitI.proj z) := by
  unfold germProjOf
  split_ifs
  rfl

/-- **Lemma 3.1**: the projection coordinate of the germ map lies in `[0,1]`. -/
theorem germProjOf_mem (hT : IsCutSet (⇑T) 0 1 s) (z : SplitI (splitSet T s)) :
    germProjOf hT z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold germProjOf
  split_ifs with hD hs
  · exact leftLimit_mem hT (SplitI.proj_mem_Icc z)
  · exact mapsTo_Icc hT (SplitI.proj_mem_Icc z)
  · exact mapsTo_Icc hT (SplitI.proj_mem_Icc z)

/-- The `d`-th coordinate `χ'` of the germ map (Definition 3.1 of the blueprint). -/
noncomputable def germCoordOf (hT : IsCutSet (⇑T) 0 1 s) (z : SplitI (splitSet T s))
    (d : splitSet T s) : Bool :=
  decide (germProjOf hT z > (d : ℝ) ∨ (germProjOf hT z = (d : ℝ) ∧ SplitI.side z = true))

/-- The `d`-th coordinate of the germ map above its own projection is the side. -/
theorem germCoordOf_self (hT : IsCutSet (⇑T) 0 1 s) (z : SplitI (splitSet T s))
    (h : germProjOf hT z ∈ splitSet T s) :
    germCoordOf hT z ⟨germProjOf hT z, h⟩ = SplitI.side z := by
  unfold germCoordOf
  have h1 : ¬ ((⟨germProjOf hT z, h⟩ : splitSet T s) : ℝ) < germProjOf hT z := lt_irrefl _
  simp only [h1, false_or, true_and]
  cases SplitI.side z <;> rfl

/-- **The germ map** `T̃` (Definition 3.1 of the blueprint). -/
noncomputable def germMapOf (hT : IsCutSet (⇑T) 0 1 s) (z : SplitI (splitSet T s)) :
    SplitI (splitSet T s) :=
  ⟨(germProjOf hT z, fun d => germCoordOf hT z d), germProjOf_mem hT z, fun d => by
    constructor
    · intro hlt
      unfold germCoordOf
      refine decide_eq_false_iff_not.mpr ?_
      rintro (h | ⟨h, _⟩)
      · exact absurd h (not_lt.mpr hlt.le)
      · exact hlt.ne h
    · intro hgt
      unfold germCoordOf
      exact decide_eq_true_iff.mpr (Or.inl hgt)⟩

theorem proj_germMapOf (hT : IsCutSet (⇑T) 0 1 s) (z : SplitI (splitSet T s)) :
    SplitI.proj (germMapOf hT z) = germProjOf hT z := rfl

theorem coord_germMapOf (hT : IsCutSet (⇑T) 0 1 s) (z : SplitI (splitSet T s))
    (d : splitSet T s) : (germMapOf hT z).1.2 d = germCoordOf hT z d := rfl

/-- The germs of two equal points of `[0,1]` coincide. -/
theorem leftGerm_congr {D : Set ℝ} {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (h : x = y) :
    SplitI.leftGerm (D := D) x hx = SplitI.leftGerm (D := D) y hy := by
  subst h
  rfl

/-- The right germs of two equal points of `[0,1]` coincide. -/
theorem rightGerm_congr {D : Set ℝ} {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (h : x = y) :
    SplitI.rightGerm (D := D) x hx = SplitI.rightGerm (D := D) y hy := by
  subst h
  rfl

/-- **Lemma 3.5**: the germ map preserves the side. -/
theorem side_germMapOf (hT : IsCutSet (⇑T) 0 1 s) (z : SplitI (splitSet T s)) :
    SplitI.side (germMapOf hT z) = SplitI.side z := by
  by_cases hD : germProjOf hT z ∈ splitSet T s
  · have h1 : SplitI.proj (germMapOf hT z) ∈ splitSet T s := by
      rw [proj_germMapOf]; exact hD
    have h2 : SplitI.side (germMapOf hT z)
        = (germMapOf hT z).1.2 ⟨SplitI.proj (germMapOf hT z), h1⟩ := by
      rw [SplitI.side, dif_pos h1]
    rw [h2]
    exact germCoordOf_self hT z hD
  · have h1 : SplitI.proj (germMapOf hT z) ∉ splitSet T s := by
      rwa [proj_germMapOf]
    unfold SplitI.side
    rw [dif_neg h1]
    by_cases hDz : SplitI.proj z ∈ splitSet T s
    · rw [dif_pos hDz]
      have hz : SplitI.side z ≠ false := by
        intro hz
        rw [germProjOf_of_side_false hT hz] at hD
        exact hD (leftLimit_mem_splitSet hT (SplitI.proj_mem_Icc z) hDz)
      have hz' : SplitI.side z = z.1.2 ⟨SplitI.proj z, hDz⟩ := by
        rw [SplitI.side, dif_pos hDz]
      cases hv : z.1.2 ⟨SplitI.proj z, hDz⟩ with
      | false => exact absurd (by rw [hz', hv]) hz
      | true => rfl
    · rw [dif_neg hDz]

/-- **Lemma 3.2**: the germ map sends the right germ of `x` to the right germ of `T x`. -/
theorem germMapOf_rightGerm (hT : IsCutSet (⇑T) 0 1 s) {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    germMapOf hT (SplitI.rightGerm x ⟨hx.1, le_of_lt hx.2⟩) =
      SplitI.rightGerm (⇑T x) ⟨(hT.mapsTo x hx).1, le_of_lt (hT.mapsTo x hx).2⟩ := by
  set w := SplitI.rightGerm (D := splitSet T s) x ⟨hx.1, le_of_lt hx.2⟩ with hw
  have hwside : SplitI.side w = true := by
    rw [hw]
    exact SplitI.side_rightGerm x ⟨hx.1, le_of_lt hx.2⟩
  have hproj : SplitI.proj (germMapOf hT w) = ⇑T x := by
    rw [proj_germMapOf, germProjOf_of_side_true hT hwside, hw]
    exact congrArg ⇑T (SplitI.proj_rightGerm x ⟨hx.1, le_of_lt hx.2⟩)
  have hmside : SplitI.side (germMapOf hT w) = true := by
    rw [side_germMapOf hT]
    exact hwside
  rw [eq_rightGerm_of_side_true hmside]
  exact rightGerm_congr _ _ hproj

/-- **Lemma 3.4**: the germ map is injective. -/
theorem germMapOf_injective (hT : IsCutSet (⇑T) 0 1 s) : Function.Injective (germMapOf hT) := by
  intro z z' h
  have hside : SplitI.side z = SplitI.side z' := by
    rw [← side_germMapOf hT z, ← side_germMapOf hT z', h]
  have hproj : germProjOf hT z = germProjOf hT z' := by
    rw [← proj_germMapOf hT z, ← proj_germMapOf hT z', h]
  cases hs : SplitI.side z
  · have hs' : SplitI.side z' = false := by rw [← hside]; exact hs
    have h1 : leftLimit hT (SplitI.proj z) = leftLimit hT (SplitI.proj z') := by
      rw [← germProjOf_of_side_false hT hs, ← germProjOf_of_side_false hT hs', hproj]
    have h2 : SplitI.proj z = SplitI.proj z' :=
      leftLimit_injOn hT T.injective (SplitI.proj_mem_Icc z) (SplitI.proj_mem_Icc z') h1
    rw [eq_leftGerm_of_side_false hs, eq_leftGerm_of_side_false hs']
    exact leftGerm_congr _ _ h2
  · have hs' : SplitI.side z' = true := by rw [← hside]; exact hs
    have h1 : ⇑T (SplitI.proj z) = ⇑T (SplitI.proj z') := by
      rw [← germProjOf_of_side_true hT hs, ← germProjOf_of_side_true hT hs', hproj]
    have h2 : SplitI.proj z = SplitI.proj z' := T.injective h1
    rw [eq_rightGerm_of_side_true hs, eq_rightGerm_of_side_true hs']
    exact rightGerm_congr _ _ h2

end GermMap

/-! ## The two cell formulas

Lemma 1.8 of the blueprint: on a cell, both `T` and `L` are the same increasing translation.
-/

section CellFormulas

variable {e : ℝ ≃ ℝ} {s : Finset ℝ}

/-- On the right cell of `x`, both `T` and `L` are the translation `T x + (y - x)`. -/
theorem apply_eq_and_leftLimit_eq (hT : IsCutSet (⇑e) 0 1 s) {x y : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hy : y ∈ Set.Ico (0 : ℝ) 1) (hxy : x < y)
    (hns : ¬ Separated s x y) :
    ⇑e y = ⇑e x + (y - x) ∧ leftLimit hT y = ⇑e x + (y - x) := by
  have hypos : 0 < y := lt_of_le_of_lt hx.1 hxy
  have happly : ⇑e y = ⇑e x + (y - x) := by
    have := hT.transl_of_not_separated x y hx hy hns
    linarith
  refine ⟨happly, ?_⟩
  have hc := cutBelow_mem_Ico hT hypos
  have hcx : cutBelow hT y hypos ≤ x := by
    by_contra hcon
    rw [not_le] at hcon
    refine hns ⟨cutBelow hT y hypos, cutBelow_mem hT hypos, ?_⟩
    rw [Set.mem_Ioc, min_eq_left hxy.le, max_eq_right hxy.le]
    exact ⟨hcon, (cutBelow_lt hT hypos).le⟩
  have hns' : ¬ Separated s (cutBelow hT y hypos) x := by
    intro hsep
    obtain ⟨d, hd, hdmem⟩ := hsep
    rw [Set.mem_Ioc, min_eq_left hcx] at hdmem
    have h3 : max (cutBelow hT y hypos) x < y := max_lt (cutBelow_lt hT hypos) hxy
    exact absurd (lt_cutBelow hT hypos hd (lt_of_le_of_lt hdmem.2 h3)) (not_le.mpr hdmem.1)
  rw [leftLimit_eq_add hT ⟨hypos, hy.2.le⟩]
  have := hT.transl_of_not_separated (cutBelow hT y hypos) x hc hx hns'
  linarith

/-- On the left cell of `x`, both `T` and `L` are the translation `L x + (y - x)`. -/
theorem apply_eq_and_leftLimit_eq_left (hT : IsCutSet (⇑e) 0 1 s) {x y : ℝ}
    (hx : x ∈ Set.Ioc (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) x)
    (hc : cutBelow hT x hx.1 < y) :
    ⇑e y = leftLimit hT x + (y - x) ∧ leftLimit hT y = leftLimit hT x + (y - x) := by
  have hyIco : y ∈ Set.Ico (0 : ℝ) 1 := ⟨hy.1.le, lt_of_lt_of_le hy.2 hx.2⟩
  have hcy := cutBelow_mem_Ico hT hx.1
  have hns : ¬ Separated s (cutBelow hT x hx.1) y := by
    intro hsep
    obtain ⟨d, hd, hdmem⟩ := hsep
    rw [Set.mem_Ioc, min_eq_left hc.le] at hdmem
    obtain ⟨hd1, hd2⟩ := hdmem
    rw [max_eq_right hc.le] at hd2
    exact absurd (lt_cutBelow hT hx.1 hd (lt_of_le_of_lt hd2 hy.2)) (not_le.mpr hd1)
  have happly : ⇑e y = leftLimit hT x + (y - x) := by
    have htrans := hT.transl_of_not_separated (cutBelow hT x hx.1) y hcy hyIco hns
    have hL := leftLimit_eq_add hT hx
    linarith
  refine ⟨happly, ?_⟩
  rw [leftLimit_eq_add hT ⟨hy.1, hyIco.2.le⟩, cutBelow_eq_of_mem hT hx.1 hy.2 hc,
    leftLimit_eq_add hT hx]
  ring

/-- There is no cut strictly between `x` and the next cut above `x`. -/
theorem exists_next_cut (hT : IsCutSet (⇑e) 0 1 s) {x : ℝ} (hx : x < 1) :
    ∃ m : ℝ, x < m ∧ m ≤ 1 ∧ ∀ c ∈ s, x < c → m ≤ c := by
  rcases (s.filter (fun c => x < c)).eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, hx, le_rfl, fun c hc hxc => ?_⟩
    by_contra hcon
    rw [not_le] at hcon
    have hmem : c ∈ s.filter (fun c => x < c) := Finset.mem_filter.mpr ⟨hc, hxc⟩
    rw [hemp] at hmem
    exact Finset.notMem_empty c hmem
  · refine ⟨(s.filter (fun c => x < c)).min' hne, ?_, ?_, fun c hc hxc => ?_⟩
    · exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
    · exact (hT.cuts_mem _ (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1).2.le
    · exact Finset.min'_le _ c (Finset.mem_filter.mpr ⟨hc, hxc⟩)

end CellFormulas

/-! ## The projection coordinate of the germ map is locally a translation

This is the key point of Lemma 3.3: near every point, `x'` agrees with `x' z + (proj · - proj z)`.
-/

section Affine

variable {T : ℝ ≃ ℝ} {s : Finset ℝ}

/-- The point with a given projection and a projection off the split set is unique. -/
theorem eq_of_proj_eq_of_notMem {D : Set ℝ} {z z' : SplitI D}
    (h : SplitI.proj z = SplitI.proj z') (hx : SplitI.proj z ∉ D) : z = z' := by
  have hsz : SplitI.side z = true := by rw [SplitI.side, dif_neg hx]
  have hsz' : SplitI.side z' = true := by rw [SplitI.side, dif_neg (h ▸ hx)]
  refine (eq_rightGerm_of_side_true hsz).trans ?_
  rw [rightGerm_congr _ _ h]
  exact (eq_rightGerm_of_side_true hsz').symm

/-- The projection coordinate of the germ map is either the exchange or the left limit. -/
theorem germProjOf_eq_apply_or (hT : IsCutSet (⇑T) 0 1 s) (z : SplitI (splitSet T s)) :
    germProjOf hT z = ⇑T (SplitI.proj z) ∨
      germProjOf hT z = leftLimit hT (SplitI.proj z) := by
  unfold germProjOf
  split_ifs with hD hs
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

/-- **Lemma 3.3 (a), right germs**: near the right germ of a split point, `x'` is the translation
`T x + (y - x)`. -/
theorem germProjOf_affine_rightGerm (hT : IsCutSet (⇑T) 0 1 s) {x : ℝ}
    (hxIcc : x ∈ Set.Icc (0 : ℝ) 1) (hxD : x ∈ splitSet T s) :
    ∃ N ∈ 𝓝 (SplitI.rightGerm (D := splitSet T s) x hxIcc), ∀ z' ∈ N,
      germProjOf hT z' = germProjOf hT (SplitI.rightGerm x hxIcc) + (SplitI.proj z' - x) := by
  have hxval : germProjOf hT (SplitI.rightGerm (D := splitSet T s) x hxIcc) = ⇑T x :=
    germProjOf_of_side_true hT (SplitI.side_rightGerm x hxIcc)
  rcases eq_or_lt_of_le hxIcc.2 with hx1 | hx1
  · subst hx1
    refine ⟨SplitI.upSet 1 hxIcc,
      (SplitI.isOpen_upSet hxIcc hxD).mem_nhds (Or.inr rfl), fun z' hz' => ?_⟩
    have hy : SplitI.proj z' = 1 :=
      le_antisymm (SplitI.proj_mem_Icc z').2 (SplitI.upSet_subset hz')
    rw [eq_rightGerm_of_mem_upSet hz' hy, SplitI.proj_rightGerm]
    ring
  · obtain ⟨m, hxm, hm1, hmnc⟩ := exists_next_cut hT hx1
    have hxIco : x ∈ Set.Ico (0 : ℝ) 1 := ⟨hxIcc.1, hx1⟩
    refine ⟨SplitI.upSet x hxIcc ∩ {z' | SplitI.proj z' < m}, ?_, fun z' hz' => ?_⟩
    · refine IsOpen.mem_nhds ?_ ⟨Or.inr rfl, ?_⟩
      · exact (SplitI.isOpen_upSet hxIcc hxD).inter
          (isOpen_lt SplitI.continuous_proj continuous_const)
      · simp only [Set.mem_ofPred_eq, SplitI.proj_rightGerm]
        exact hxm
    · obtain ⟨hz1, hz2⟩ := hz'
      have hyx : x ≤ SplitI.proj z' := SplitI.upSet_subset hz1
      rcases lt_or_eq_of_le hyx with hlt | heq
      · have hyIco : SplitI.proj z' ∈ Set.Ico (0 : ℝ) 1 :=
          ⟨hxIcc.1.trans hlt.le, lt_of_lt_of_le hz2 hm1⟩
        have hns : ¬ Separated s x (SplitI.proj z') := by
          intro hsep
          obtain ⟨d, hd, hd1, hd2⟩ := hsep.exists_of_le hlt.le
          exact absurd (le_trans (hmnc d hd hd1) hd2) (not_le.mpr hz2)
        obtain ⟨hA1, hA2⟩ := apply_eq_and_leftLimit_eq hT hxIco hyIco hlt hns
        rw [hxval]
        rcases germProjOf_eq_apply_or hT z' with h | h
        · rw [h]; exact hA1
        · rw [h]; exact hA2
      · rw [eq_rightGerm_of_mem_upSet hz1 heq.symm, SplitI.proj_rightGerm]
        ring

/-- **Lemma 3.3 (a), left germs**: near the left germ of a split point, `x'` is the translation
`L x + (y - x)`. -/
theorem germProjOf_affine_leftGerm (hT : IsCutSet (⇑T) 0 1 s) {x : ℝ}
    (hxIcc : x ∈ Set.Icc (0 : ℝ) 1) (hxD : x ∈ splitSet T s) :
    ∃ N ∈ 𝓝 (SplitI.leftGerm (D := splitSet T s) x hxIcc), ∀ z' ∈ N,
      germProjOf hT z' = germProjOf hT (SplitI.leftGerm x hxIcc) + (SplitI.proj z' - x) := by
  have hxval : germProjOf hT (SplitI.leftGerm (D := splitSet T s) x hxIcc) = leftLimit hT x :=
    germProjOf_of_side_false hT (SplitI.side_leftGerm hxIcc hxD)
  rcases eq_or_lt_of_le hxIcc.1 with hx0 | hx0
  · subst hx0
    refine ⟨SplitI.downSet 0 hxIcc,
      (SplitI.isOpen_downSet hxIcc hxD).mem_nhds (Or.inr rfl), fun z' hz' => ?_⟩
    have hy : SplitI.proj z' = 0 :=
      le_antisymm (SplitI.downSet_subset hz') (SplitI.proj_mem_Icc z').1
    rw [eq_leftGerm_of_mem_downSet hz' hy, SplitI.proj_leftGerm]
    ring
  · have hxIoc : x ∈ Set.Ioc (0 : ℝ) 1 := ⟨hx0, hxIcc.2⟩
    have hcx : cutBelow hT x hx0 < x := cutBelow_lt hT hx0
    refine ⟨SplitI.downSet x hxIcc ∩ {z' | cutBelow hT x hx0 < SplitI.proj z'}, ?_,
      fun z' hz' => ?_⟩
    · refine IsOpen.mem_nhds ?_ ⟨Or.inr rfl, ?_⟩
      · exact (SplitI.isOpen_downSet hxIcc hxD).inter
          (isOpen_lt continuous_const SplitI.continuous_proj)
      · simp only [Set.mem_ofPred_eq, SplitI.proj_leftGerm]
        exact hcx
    · obtain ⟨hz1, hz2⟩ := hz'
      have hle : SplitI.proj z' ≤ x := SplitI.downSet_subset hz1
      rcases lt_or_eq_of_le hle with hlt | heq
      · have hy : SplitI.proj z' ∈ Set.Ioo (0 : ℝ) x :=
          ⟨lt_of_le_of_lt (cutBelow_mem_Ico hT hx0).1 hz2, hlt⟩
        obtain ⟨hB1, hB2⟩ := apply_eq_and_leftLimit_eq_left hT hxIoc hy hz2
        rw [hxval]
        rcases germProjOf_eq_apply_or hT z' with h | h
        · rw [h]; exact hB1
        · rw [h]; exact hB2
      · rw [eq_leftGerm_of_mem_downSet hz1 heq, SplitI.proj_leftGerm]
        ring

/-- **Lemma 3.3 (a)**: the projection coordinate of the germ map is locally a translation. -/
theorem germProjOf_eventually_affine (hT : IsCutSet (⇑T) 0 1 s) (z : SplitI (splitSet T s)) :
    ∃ N ∈ 𝓝 z, ∀ z' ∈ N,
      germProjOf hT z' = germProjOf hT z + (SplitI.proj z' - SplitI.proj z) := by
  set x := SplitI.proj z with hxdef
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := SplitI.proj_mem_Icc z
  by_cases hxD : x ∈ splitSet T s
  · by_cases hs : SplitI.side z = true
    · have hz : z = SplitI.rightGerm (D := splitSet T s) x hxIcc :=
        (eq_rightGerm_of_side_true hs).trans
          (rightGerm_congr (SplitI.proj_mem_Icc z) hxIcc hxdef.symm)
      obtain ⟨N, hN, hNsub⟩ := germProjOf_affine_rightGerm hT hxIcc hxD
      refine ⟨N, hz ▸ hN, fun z' hz' => ?_⟩
      rw [hz]
      exact hNsub z' hz'
    · have hs' : SplitI.side z = false := by
        cases hv : SplitI.side z
        · rfl
        · exact absurd hv hs
      have hz : z = SplitI.leftGerm (D := splitSet T s) x hxIcc :=
        (eq_leftGerm_of_side_false hs').trans
          (leftGerm_congr (SplitI.proj_mem_Icc z) hxIcc hxdef.symm)
      obtain ⟨N, hN, hNsub⟩ := germProjOf_affine_leftGerm hT hxIcc hxD
      refine ⟨N, hz ▸ hN, fun z' hz' => ?_⟩
      rw [hz]
      exact hNsub z' hz'
  · have hxne : x ≠ 1 := fun h => hxD (h ▸ one_mem_splitSet T s)
    have hx1 : x < 1 := lt_of_le_of_ne hxIcc.2 hxne
    have h0mem : (0 : ℝ) ∈ splitSet T s := mem_splitSet_of_mem T s hT.a_mem
    have hx0 : 0 < x := lt_of_le_of_ne hxIcc.1 (fun h => hxD (h ▸ h0mem))
    have hxs : x ∉ s := fun h => hxD (mem_splitSet_of_mem T s h)
    have hxIco : x ∈ Set.Ico (0 : ℝ) 1 := ⟨hxIcc.1, hx1⟩
    have hcx : cutBelow hT x hx0 < x := cutBelow_lt hT hx0
    obtain ⟨m, hxm, hm1, hmnc⟩ := exists_next_cut hT hx1
    have hxval : germProjOf hT z = ⇑T x := by
      have h1 : SplitI.proj z ∉ splitSet T s := by rw [← hxdef]; exact hxD
      rw [germProjOf_of_notMem hT h1, ← hxdef]
    refine ⟨{z' | SplitI.proj z' ∈ Set.Ioo (cutBelow hT x hx0) m}, ?_, fun z' hz' => ?_⟩
    · refine IsOpen.mem_nhds ?_ ⟨hcx, hxm⟩
      exact (isOpen_lt continuous_const SplitI.continuous_proj).inter
        (isOpen_lt SplitI.continuous_proj continuous_const)
    · have hz'1 : cutBelow hT x hx0 < SplitI.proj z' := hz'.1
      rw [hxval]
      rcases lt_trichotomy (SplitI.proj z') x with hlt | heq | hgt
      · have hy : SplitI.proj z' ∈ Set.Ioo (0 : ℝ) x :=
          ⟨lt_of_le_of_lt (cutBelow_mem_Ico hT hx0).1 hz'1, hlt⟩
        obtain ⟨hB1, hB2⟩ := apply_eq_and_leftLimit_eq_left hT ⟨hx0, hxIcc.2⟩ hy hz'1
        rw [leftLimit_eq_apply hT hxIco hxs] at hB1 hB2
        rcases germProjOf_eq_apply_or hT z' with h | h
        · rw [h]; exact hB1
        · rw [h]; exact hB2
      · have hval : germProjOf hT z' = ⇑T (SplitI.proj z') := by
          rcases germProjOf_eq_apply_or hT z' with h | h
          · exact h
          · rw [h, leftLimit_eq_apply hT ⟨(SplitI.proj_mem_Icc z').1, by rw [heq]; exact hx1⟩
              (by rw [heq]; exact hxs)]
        rw [hval, heq]
        ring
      · have hyIco : SplitI.proj z' ∈ Set.Ico (0 : ℝ) 1 :=
          ⟨hxIcc.1.trans hgt.le, lt_of_lt_of_le hz'.2 hm1⟩
        have hns : ¬ Separated s x (SplitI.proj z') := by
          intro hsep
          obtain ⟨d, hd, hd1, hd2⟩ := hsep.exists_of_le hgt.le
          exact absurd (le_trans (hmnc d hd hd1) hd2) (not_le.mpr hz'.2)
        obtain ⟨hA1, hA2⟩ := apply_eq_and_leftLimit_eq hT hxIco hyIco hgt hns
        rcases germProjOf_eq_apply_or hT z' with h | h
        · rw [h]; exact hA1
        · rw [h]; exact hA2

end Affine

/-! ## Continuity of the germ map (Lemma 3.3) -/

section Continuity

variable {T : ℝ ≃ ℝ} {s : Finset ℝ}

/-- **Lemma 3.3 (a)**: the projection coordinate of the germ map is continuous. -/
theorem continuous_germProjOf (hT : IsCutSet (⇑T) 0 1 s) : Continuous (germProjOf hT) := by
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨N, hN, hNsub⟩ := germProjOf_eventually_affine hT z
  have hcont : ContinuousAt (fun z' => germProjOf hT z + (SplitI.proj z' - SplitI.proj z)) z :=
    continuousAt_const.add
      ((SplitI.continuous_proj.sub continuous_const).continuousAt)
  refine hcont.congr ?_
  filter_upwards [hN] with z' hz'
  exact (hNsub z' hz').symm

/-- A point whose image is in the split set is itself in the split set, by invariance of the split
set. -/
theorem mem_splitSet_of_apply_mem {e : ℝ ≃ ℝ} {s : Finset ℝ} {y : ℝ}
    (h : ⇑e y ∈ splitSet e s) : y ∈ splitSet e s := by
  have h2 : ⇑e y ∈ ⇑e '' splitSet e s := by
    rw [image_splitSet_eq e s]
    exact h
  obtain ⟨w, hw, hwe⟩ := h2
  rwa [e.injective hwe] at hw

/-- **Lemma 3.3 (b)**: the coordinates of the germ map are continuous. -/
theorem continuous_germCoordOf (hT : IsCutSet (⇑T) 0 1 s) (d : splitSet T s) :
    Continuous (fun z => germCoordOf hT z d) := by
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨N, hN, hNsub⟩ := germProjOf_eventually_affine hT z
  set x' := germProjOf hT z with hx'def
  rcases lt_trichotomy x' (d : ℝ) with hlt | heq | hgt
  · have hmem : {z' : SplitI (splitSet T s) |
        SplitI.proj z' < SplitI.proj z + ((d : ℝ) - x')} ∈ 𝓝 z :=
      (isOpen_lt SplitI.continuous_proj continuous_const).mem_nhds
        (lt_add_of_pos_right _ (sub_pos.mpr hlt))
    have hconst : ContinuousAt (fun _ : SplitI (splitSet T s) => false) z := continuousAt_const
    refine hconst.congr ?_
    filter_upwards [hN, hmem] with z' hz'N hz'proj
    unfold germCoordOf
    exact (decide_eq_false_iff_not.mpr (fun hcon => by
      rcases hcon with h | ⟨h, _⟩
      · rw [hNsub z' hz'N] at h
        linarith
      · rw [hNsub z' hz'N] at h
        linarith)).symm
  · have hxD : SplitI.proj z ∈ splitSet T s := by
      by_contra hcon
      have h1 : ⇑T (SplitI.proj z) ∈ splitSet T s := by
        rw [← germProjOf_of_notMem hT hcon, ← hx'def]
        exact heq ▸ d.2
      exact hcon (mem_splitSet_of_apply_mem h1)
    have hx'D : germProjOf hT z ∈ splitSet T s := by
      rw [← hx'def]
      exact heq ▸ d.2
    have hval : germCoordOf hT z d = SplitI.side z := by
      have hd_eq : (⟨germProjOf hT z, hx'D⟩ : splitSet T s) = d := Subtype.ext heq
      rw [← hd_eq]
      exact germCoordOf_self hT z hx'D
    cases hs : SplitI.side z
    · have hz : z = SplitI.leftGerm (D := splitSet T s) (SplitI.proj z) (SplitI.proj_mem_Icc z) :=
        eq_leftGerm_of_side_false hs
      have hmem : SplitI.downSet (SplitI.proj z) (SplitI.proj_mem_Icc z) ∈ 𝓝 z := by
        have h0 : SplitI.downSet (SplitI.proj z) (SplitI.proj_mem_Icc z) ∈
            𝓝 (SplitI.leftGerm (SplitI.proj z) (SplitI.proj_mem_Icc z)) :=
          (SplitI.isOpen_downSet (SplitI.proj_mem_Icc z) hxD).mem_nhds (Or.inr rfl)
        rwa [← hz] at h0
      have hconst : ContinuousAt (fun _ : SplitI (splitSet T s) => false) z := continuousAt_const
      refine hconst.congr ?_
      filter_upwards [hN, hmem] with z' hz'N hz'down
      have hproj : SplitI.proj z' ≤ SplitI.proj z := SplitI.downSet_subset hz'down
      have hple : germProjOf hT z' ≤ (d : ℝ) := by
        rw [hNsub z' hz'N, heq]
        linarith
      unfold germCoordOf
      exact (decide_eq_false_iff_not.mpr (fun hcon => by
        rcases hcon with h | ⟨h, hs'⟩
        · linarith
        · have h1 : SplitI.proj z' = SplitI.proj z := by
            rw [hNsub z' hz'N, heq] at h
            linarith
          have h2 : z' = z := (eq_leftGerm_of_mem_downSet hz'down h1).trans hz.symm
          rw [h2, hs] at hs'
          exact absurd hs' (by simp))).symm
    · have hz : z = SplitI.rightGerm (D := splitSet T s) (SplitI.proj z) (SplitI.proj_mem_Icc z) :=
        eq_rightGerm_of_side_true hs
      have hmem : SplitI.upSet (SplitI.proj z) (SplitI.proj_mem_Icc z) ∈ 𝓝 z := by
        have h0 : SplitI.upSet (SplitI.proj z) (SplitI.proj_mem_Icc z) ∈
            𝓝 (SplitI.rightGerm (SplitI.proj z) (SplitI.proj_mem_Icc z)) :=
          (SplitI.isOpen_upSet (SplitI.proj_mem_Icc z) hxD).mem_nhds (Or.inr rfl)
        rwa [← hz] at h0
      have hconst : ContinuousAt (fun _ : SplitI (splitSet T s) => true) z := continuousAt_const
      refine hconst.congr ?_
      filter_upwards [hN, hmem] with z' hz'N hz'up
      have hproj : SplitI.proj z ≤ SplitI.proj z' := SplitI.upSet_subset hz'up
      have hge : (d : ℝ) ≤ germProjOf hT z' := by
        rw [hNsub z' hz'N, heq]
        linarith
      unfold germCoordOf
      exact (decide_eq_true_iff.mpr (by
        by_cases hlt' : (d : ℝ) < germProjOf hT z'
        · exact Or.inl hlt'
        · refine Or.inr ⟨le_antisymm (not_lt.mp hlt') hge, ?_⟩
          have h1 : SplitI.proj z' = SplitI.proj z := by
            rw [hNsub z' hz'N, heq] at hge hlt'
            linarith
          have h2 : z' = z := (eq_rightGerm_of_mem_upSet hz'up h1).trans hz.symm
          rw [h2, hs])).symm
  · have hmem : {z' : SplitI (splitSet T s) |
        SplitI.proj z - (x' - (d : ℝ)) < SplitI.proj z'} ∈ 𝓝 z :=
      (isOpen_lt continuous_const SplitI.continuous_proj).mem_nhds
        (sub_lt_self _ (sub_pos.mpr hgt))
    have hconst : ContinuousAt (fun _ : SplitI (splitSet T s) => true) z := continuousAt_const
    refine hconst.congr ?_
    filter_upwards [hN, hmem] with z' hz'N hz'proj
    unfold germCoordOf
    exact (decide_eq_true_iff.mpr (Or.inl (by
      rw [hNsub z' hz'N]
      linarith))).symm

/-- **Lemma 3.3**: the germ map is continuous. -/
theorem continuous_germMapOf (hT : IsCutSet (⇑T) 0 1 s) : Continuous (germMapOf hT) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_prodMk.mpr ⟨continuous_germProjOf hT, ?_⟩
  exact continuous_pi_iff.mpr (fun d => continuous_germCoordOf hT d)

/-- **Lemma 3.2, iterated form**: the germ map sends the right germs of `[0,1)` into the right
part. -/
theorem mapsTo_range_germMapOf (hT : IsCutSet (⇑T) 0 1 s) :
    Set.MapsTo (germMapOf hT)
      (Set.range (fun x : Set.Ico (0 : ℝ) 1 =>
        SplitI.rightGerm (D := splitSet T s) x.1 ⟨x.2.1, le_of_lt x.2.2⟩))
      (SplitI.rightPart (splitSet T s)) := by
  rintro _ ⟨x, rfl⟩
  rw [germMapOf_rightGerm hT x.2]
  exact SplitI.rightGerm_mem_rightPart (hT.mapsTo x.1 x.2)

/-- **Lemma 3.2 + 3.4**: the germ map preserves the right part `[0+, 1-]`. -/
theorem mapsTo_rightPart_germMapOf (hT : IsCutSet (⇑T) 0 1 s) :
    Set.MapsTo (germMapOf hT) (SplitI.rightPart (splitSet T s))
      (SplitI.rightPart (splitSet T s)) :=
  MapsTo.closure_left (mapsTo_range_germMapOf hT) (continuous_germMapOf hT)
    (SplitI.isClosed_rightPart _)

end Continuity

/-! ## The germ map of the interval exchange `mkIETEquiv lam π 0`

Everything above is proved for an arbitrary exchange `T` with cut set `s` on `[0,1)`; here we
specialise to `T = mkIETEquiv lam π 0` and `s = mkIETCuts lam 0 1`.  The cut-set structure needs
the total length `∑ lam` to be at most `1` (downstream it is `∑ lam = 1`, the simplex), so every
statement below carries this hypothesis `hsum`.
-/

section Concrete

variable {n : ℕ} [NeZero n]

/-- The cut-set structure of the exchange `mkIETEquiv lam π 0` on `[0,1)`. -/
theorem isCutSet_mkIET (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (hsum : (∑ i, (lam i : ℝ)) ≤ 1) :
    IsCutSet (⇑(mkIETEquiv lam π 0)) 0 1 (mkIETCuts lam 0 1) := by
  have h' : IsCutSet (⇑(mkIETEquiv lam π 0)) 0 (0 + 1) (mkIETCuts lam 0 1) :=
    isCutSet_mkIETCuts lam π 0 hsum one_pos
  simpa using h'

/-- **Lemma 1.7 (ii)** for the exchange `mkIETEquiv lam π 0`: its split set is invariant. -/
theorem image_splitSet (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n)) :
    ⇑(mkIETEquiv lam π 0) '' splitSet (mkIETEquiv lam π 0) (mkIETCuts lam 0 1) =
      splitSet (mkIETEquiv lam π 0) (mkIETCuts lam 0 1) :=
  image_splitSet_eq _ _

/-- **`leftGerm 0` is not in the right part** (§4.4 of the blueprint). -/
theorem leftGerm_zero_notMem_rightPart (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (hsum : (∑ i, (lam i : ℝ)) ≤ 1) :
    SplitI.leftGerm (D := splitSet (mkIETEquiv lam π 0) (mkIETCuts lam 0 1))
        0 ⟨le_rfl, zero_le_one⟩ ∉
      SplitI.rightPart (splitSet (mkIETEquiv lam π 0) (mkIETCuts lam 0 1)) :=
  leftGerm_zero_notMem_rightPart_of_mem
    (mem_splitSet_of_mem _ _ (isCutSet_mkIET lam π hsum).a_mem)

/-- **The germ map** `T̃` of the interval exchange `mkIETEquiv lam π 0` (Definition 3.1). -/
noncomputable def germMap (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (hsum : (∑ i, (lam i : ℝ)) ≤ 1) :
    SplitI (splitSet (mkIETEquiv lam π 0) (mkIETCuts lam 0 1)) →
      SplitI (splitSet (mkIETEquiv lam π 0) (mkIETCuts lam 0 1)) :=
  germMapOf (isCutSet_mkIET lam π hsum)

/-- The germ map is the germ map of the cut set `mkIETCuts lam 0 1`. -/
theorem germMap_eq_germMapOf (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (hsum : (∑ i, (lam i : ℝ)) ≤ 1)
    (z : SplitI (splitSet (mkIETEquiv lam π 0) (mkIETCuts lam 0 1))) :
    germMap lam π hsum z = germMapOf (isCutSet_mkIET lam π hsum) z := rfl

/-- **Lemma 3.2**: the germ map sends the right germ of `x` to the right germ of `T x`. -/
theorem germMap_rightGerm (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (hsum : (∑ i, (lam i : ℝ)) ≤ 1) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    germMap lam π hsum (SplitI.rightGerm x ⟨hx.1, le_of_lt hx.2⟩) =
      SplitI.rightGerm (⇑(mkIETEquiv lam π 0) x)
        ⟨((isCutSet_mkIET lam π hsum).mapsTo x hx).1,
          le_of_lt ((isCutSet_mkIET lam π hsum).mapsTo x hx).2⟩ :=
  germMapOf_rightGerm _ hx

/-- **Lemma 3.4**: the germ map is injective. -/
theorem germMap_inj (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (hsum : (∑ i, (lam i : ℝ)) ≤ 1) : Function.Injective (germMap lam π hsum) :=
  germMapOf_injective _

/-- **Lemma 3.3**: the germ map is continuous. -/
theorem continuous_germMap (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (hsum : (∑ i, (lam i : ℝ)) ≤ 1) : Continuous (germMap lam π hsum) :=
  continuous_germMapOf _

/-- **Lemma 3.5**: the germ map preserves the right part `[0+, 1-]`. -/
theorem mapsTo_rightPart (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (hsum : (∑ i, (lam i : ℝ)) ≤ 1) :
    Set.MapsTo (germMap lam π hsum)
      (SplitI.rightPart (splitSet (mkIETEquiv lam π 0) (mkIETCuts lam 0 1)))
      (SplitI.rightPart (splitSet (mkIETEquiv lam π 0) (mkIETCuts lam 0 1))) :=
  mapsTo_rightPart_germMapOf _

end Concrete

end IETFree.UniqueErgodicity

end
