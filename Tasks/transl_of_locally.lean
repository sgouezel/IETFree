/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib

/-! Statement file for the discovery run: the library's `IsCutSet.transl_of_locally`, with the definitions inlined so that
the file only imports `Mathlib`.  The statement is checked against the library in `Tasks/Match.lean`.
-/ 

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

/-- `C` separates `x` from `y`: some cut lies in `(min x y, max x y]`.  With the `Ico` convention
the pieces are `[α, β)`, so a cut `β` that equals `max x y` is a boundary point: it belongs to the
*next* piece and hence separates. -/
def Separated (C : Finset ℝ) (x y : ℝ) : Prop := ∃ c ∈ C, c ∈ Set.Ioc (min x y) (max x y)

/-- Separation survives passing to a larger set of cuts. -/
lemma Separated.mono {C C' : Finset ℝ} {x y : ℝ} (h : Separated C x y) (hsub : C ⊆ C') :
    Separated C' x y :=
  let ⟨c, hc, hci⟩ := h
  ⟨c, hsub hc, hci⟩

/-- `s` is a **cut set** for `f` on `[a, b)`: `f` is the identity below `a` and above `b`, maps
`[a, b)` into itself, `s` is contained in `[a, b)`, and `f` is a translation on each piece cut
by `s`. -/
structure IsCutSet (f : ℝ → ℝ) (a b : ℝ) (s : Finset ℝ) : Prop where
  /-- `f` is the identity below `a`. -/
  apply_eq_self_of_lt : ∀ x, x < a → f x = x
  /-- `f` is the identity from `b` on. -/
  apply_eq_self_of_le : ∀ x, b ≤ x → f x = x
  /-- `f` maps `[a, b)` into itself. -/
  mapsTo : ∀ x, x ∈ Set.Ico a b → f x ∈ Set.Ico a b
  /-- every cut lies in `[a, b)`. -/
  cuts_mem : ∀ c ∈ s, c ∈ Set.Ico a b
  /-- `f` is a translation on each piece cut by `s`. -/
  transl_of_not_separated : ∀ x y : ℝ, x ∈ Set.Ico a b → y ∈ Set.Ico a b → ¬ Separated s x y →
    f y - y = f x - x

/-- The largest cut not exceeding `x`. -/
noncomputable def cellLeft (C : Finset ℝ) (x : ℝ) (h : (C.filter (fun c => c ≤ x)).Nonempty) : ℝ :=
  (C.filter (fun c => c ≤ x)).max' h

/-- The left end of the cell of `x` is a cut. -/
lemma cellLeft_mem {C : Finset ℝ} {x : ℝ} (h : (C.filter (fun c => c ≤ x)).Nonempty) :
    cellLeft C x h ∈ C :=
  (Finset.mem_filter.mp (Finset.max'_mem _ h)).1

/-- The left end of the cell of `x` is at most `x`. -/
lemma cellLeft_le {C : Finset ℝ} {x : ℝ} (h : (C.filter (fun c => c ≤ x)).Nonempty) :
    cellLeft C x h ≤ x :=
  (Finset.mem_filter.mp (Finset.max'_mem _ h)).2

/-- Every cut below `x` is below the left end of the cell of `x`. -/
lemma le_cellLeft {C : Finset ℝ} {x c : ℝ} (h : (C.filter (fun c => c ≤ x)).Nonempty)
    (hc : c ∈ C) (hcx : c ≤ x) : c ≤ cellLeft C x h :=
  Finset.le_max' _ c (Finset.mem_filter.mpr ⟨hc, hcx⟩)

/-- No cut lies strictly between a point and the left end of its cell. -/
lemma not_separated_cellLeft {C : Finset ℝ} {x : ℝ} (h : (C.filter (fun c => c ≤ x)).Nonempty) :
    ¬ Separated C (cellLeft C x h) x := by
  rintro ⟨c, hc, hci⟩
  have hcl : cellLeft C x h ≤ x := cellLeft_le h
  rw [min_eq_left hcl, max_eq_right hcl] at hci
  exact absurd (le_cellLeft h hc hci.2) (not_le.mpr hci.1)

/-- **`f` is a translation on each cell**: on the cell `[cellLeft x, next cut)` the displacement of
`f` is constant, equal to `f (cellLeft x) - cellLeft x`. -/
lemma IsCutSet.map_eq_cell {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ} (hs : IsCutSet f a b s)
    {x : ℝ} (hx : x ∈ Set.Ico a b) :
    f x = x + (f (cellLeft (insert a s) x ⟨a, by simp [hx.1]⟩)
      - cellLeft (insert a s) x ⟨a, by simp [hx.1]⟩) := by
  have hne : ((insert a s).filter (fun c => c ≤ x)).Nonempty := ⟨a, by simp [hx.1]⟩
  have hmem : cellLeft (insert a s) x hne ∈ insert a s := cellLeft_mem hne
  have hle : cellLeft (insert a s) x hne ≤ x := cellLeft_le hne
  have ha : a ≤ cellLeft (insert a s) x hne := by
    rcases Finset.mem_insert.mp hmem with h | h'
    · exact le_of_eq h.symm
    · exact (hs.cuts_mem _ h').1
  have hb : cellLeft (insert a s) x hne < b := lt_of_le_of_lt hle hx.2
  have hdisp := hs.transl_of_not_separated (cellLeft (insert a s) x hne) x ⟨ha, hb⟩ hx
    (fun hh => not_separated_cellLeft hne (Separated.mono hh (Finset.subset_insert a s)))
  linarith

/-- **The inverse of an exchange stays in the interval**: `e.symm` maps `[a, b)` into itself.  This
is what lets the images of the cells cover `[a, b)`. -/
lemma Equiv.IsIET.symm_mapsTo {a b : ℝ} {e : Equiv ℝ ℝ} {s : Finset ℝ}
    (hs : IsCutSet (⇑e) a b s) {y : ℝ} (hy : y ∈ Set.Ico a b) :
    e.symm y ∈ Set.Ico a b := by
  by_contra hcon
  have h1 : ⇑e (e.symm y) = e.symm y := by
    rcases not_and_or.mp hcon with hlt | hle
    · exact hs.apply_eq_self_of_lt _ (not_le.mp hlt)
    · exact hs.apply_eq_self_of_le _ (not_lt.mp hle)
  rw [Equiv.apply_symm_apply] at h1
  exact hcon (h1 ▸ hy)

/-- The increasing enumeration of the cell starts `{a} ∪ s`. -/
noncomputable def IsCutSet.cellStarts {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (_hs : IsCutSet f a b s) : Fin (insert a s).card → ℝ :=
  fun i => ((Finset.orderIsoOfFin (insert a s) rfl) i : ℝ)

/-- The enumeration takes values among the cell starts. -/
lemma IsCutSet.cellStarts_mem {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (i : Fin (insert a s).card) : hs.cellStarts i ∈ insert a s :=
  (Finset.orderIsoOfFin (insert a s) rfl i).2

/-- The enumeration is strictly increasing. -/
lemma IsCutSet.cellStarts_strictMono {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) : StrictMono hs.cellStarts :=
  fun _ _ h => (Finset.orderIsoOfFin (insert a s) rfl).strictMono h

/-- Every cell start lies in `[a, b)`. -/
lemma IsCutSet.cellStarts_mem_Ico {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (hlt : a < b) (i : Fin (insert a s).card) :
    hs.cellStarts i ∈ Set.Ico a b := by
  have hmem := hs.cellStarts_mem i
  refine ⟨?_, ?_⟩
  · rcases Finset.mem_insert.mp hmem with h | h'
    · exact le_of_eq h.symm
    · exact (hs.cuts_mem _ h').1
  · rcases Finset.mem_insert.mp hmem with h | h'
    · rw [h]; exact hlt
    · exact (hs.cuts_mem _ h').2

/-- The first cell starts at `a`. -/
lemma IsCutSet.cellStarts_zero {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (hne : 0 < (insert a s).card) : hs.cellStarts ⟨0, hne⟩ = a := by
  classical
  haveI : NeZero (insert a s).card := ⟨Nat.pos_iff_ne_zero.mp hne⟩
  have hall : ∀ x ∈ insert a s, a ≤ x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h'
    · exact le_of_eq h.symm
    · exact (hs.cuts_mem x h').1
  -- the index at which `a` is enumerated
  set iso := Finset.orderIsoOfFin (insert a s) rfl with hiso
  set j : Fin (insert a s).card := iso.symm ⟨a, by simp⟩ with hj
  have hjval : hs.cellStarts j = a := by
    have h1 : iso j = ⟨a, by simp⟩ := iso.apply_symm_apply _
    show ((iso j : {x // x ∈ insert a s}) : ℝ) = a
    rw [h1]
  have hj0 : j = ⟨0, hne⟩ := by
    refine le_antisymm ?_ (Fin.zero_le _)
    by_contra hcon
    rw [not_le] at hcon
    have hlt : (⟨0, hne⟩ : Fin (insert a s).card) < j := hcon
    have h1 : hs.cellStarts ⟨0, hne⟩ < hs.cellStarts j := hs.cellStarts_strictMono hlt
    have h2 : a ≤ hs.cellStarts ⟨0, hne⟩ := hall _ (hs.cellStarts_mem _)
    rw [hjval] at h1
    linarith
  rw [← hj0]
  exact hjval

/-- The position function: `cellStarts` continued by `b` past the last index. -/
noncomputable def IsCutSet.cellPos {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (k : ℕ) : ℝ :=
  if h : k < (insert a s).card then hs.cellStarts ⟨k, h⟩ else b

/-- The length of the `i`-th cell. -/
noncomputable def IsCutSet.cellLen {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (i : Fin (insert a s).card) : ℝ :=
  hs.cellPos (i.val + 1) - hs.cellPos i.val

/-- Below the last index the position function is the enumeration. -/
lemma IsCutSet.cellPos_of_lt {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) {k : ℕ} (hk : k < (insert a s).card) :
    hs.cellPos k = hs.cellStarts ⟨k, hk⟩ := by
  unfold IsCutSet.cellPos
  exact dif_pos hk

/-- Past the last index the position function is `b`. -/
lemma IsCutSet.cellPos_top {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ} (hs : IsCutSet f a b s) :
    hs.cellPos (insert a s).card = b := by
  unfold IsCutSet.cellPos
  exact dif_neg (by omega)

/-- **The lengths of the cells sum to `b - a`**: the cells tile `[a, b)`. -/
lemma IsCutSet.sum_cellLen {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) :
    ∑ i, hs.cellLen i = b - a := by
  have hne : 0 < (insert a s).card := by
    have : a ∈ insert a s := Finset.mem_insert_self a s
    exact Finset.card_pos.mpr ⟨a, this⟩
  have hfun : ∀ i : Fin (insert a s).card,
      hs.cellLen i = (fun k => hs.cellPos k) (i.val + 1) - (fun k => hs.cellPos k) i.val :=
    fun i => rfl
  simp only [hfun]
  rw [Fin.sum_univ_eq_sum_range (fun k => hs.cellPos (k + 1) - hs.cellPos k) (insert a s).card]
  rw [Finset.sum_range_sub]
  rw [hs.cellPos_top, hs.cellPos_of_lt (k := 0) hne, hs.cellStarts_zero hne]

/-- Every cell start is the value of the enumeration at some index. -/
lemma IsCutSet.cellStarts_surj {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) {c : ℝ} (hc : c ∈ insert a s) :
    ∃ j : Fin (insert a s).card, hs.cellStarts j = c :=
  ⟨(Finset.orderIsoOfFin (insert a s) rfl).symm ⟨c, hc⟩, by simp [IsCutSet.cellStarts]⟩

/-- The enumeration is strictly increasing, in index form. -/
lemma IsCutSet.cellStarts_lt_iff {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) {i j : Fin (insert a s).card} :
    hs.cellStarts i < hs.cellStarts j ↔ i < j :=
  (Finset.orderIsoOfFin (insert a s) rfl).lt_iff_lt

/-- The right end of a cell is the next cell start, or `b` at the last index. -/
lemma IsCutSet.cellPos_succ {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (i : Fin (insert a s).card) :
    (∃ h : i.val + 1 < (insert a s).card,
      hs.cellPos (i.val + 1) = hs.cellStarts ⟨i.val + 1, h⟩)
    ∨ (i.val + 1 = (insert a s).card ∧ hs.cellPos (i.val + 1) = b) := by
  by_cases h : i.val + 1 < (insert a s).card
  · exact Or.inl ⟨h, hs.cellPos_of_lt h⟩
  · refine Or.inr ⟨by omega, ?_⟩
    unfold IsCutSet.cellPos
    rw [dif_neg h]

/-- A cell is nondegenerate. -/
lemma IsCutSet.cellStarts_lt_cellPos {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (hlt : a < b) (i : Fin (insert a s).card) :
    hs.cellStarts i < hs.cellPos (i.val + 1) := by
  rcases hs.cellPos_succ i with ⟨h, hh⟩ | ⟨h, hh⟩
  · rw [hh]
    exact hs.cellStarts_lt_iff.mpr (Fin.lt_def.mpr (by simp))
  · rw [hh]
    exact (hs.cellStarts_mem_Ico hlt i).2

/-- The right end of a cell lies in `(a, b]`. -/
lemma IsCutSet.cellPos_le {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (hlt : a < b) (k : ℕ) : hs.cellPos k ≤ b := by
  by_cases h : k < (insert a s).card
  · rw [hs.cellPos_of_lt h]
    exact le_of_lt (hs.cellStarts_mem_Ico hlt ⟨k, h⟩).2
  · unfold IsCutSet.cellPos
    rw [dif_neg h]

/-- A point of the `i`-th cell has `cellStarts i` as the left end of its cell. -/
lemma IsCutSet.cellLeft_eq {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (hlt : a < b) {i : Fin (insert a s).card} {x : ℝ}
    (hx : x ∈ Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1))) :
    cellLeft (insert a s) x ⟨a, by
      have hβ := hs.cellStarts_mem_Ico hlt i
      simp only [Finset.mem_filter, Finset.mem_insert, true_or, le_trans hβ.1 hx.1, and_self]⟩
      = hs.cellStarts i := by
  have hβ := hs.cellStarts_mem_Ico hlt i
  have hxmem : x ∈ Set.Ico a b :=
    ⟨le_trans hβ.1 hx.1, lt_of_lt_of_le hx.2 (hs.cellPos_le hlt _)⟩
  have hne : ((insert a s).filter (fun c => c ≤ x)).Nonempty := ⟨a, by simp [hxmem.1]⟩
  refine le_antisymm ?_ (le_cellLeft hne (hs.cellStarts_mem i) hx.1)
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨j, hj⟩ := hs.cellStarts_surj (cellLeft_mem hne)
  have h1 : i < j := hs.cellStarts_lt_iff.mp (by rw [hj]; exact hcon)
  have h2 : j.val < i.val + 1 := by
    rcases hs.cellPos_succ i with ⟨h, hh⟩ | ⟨h, hh⟩
    · rw [hh] at hx
      have : hs.cellStarts j < hs.cellStarts ⟨i.val + 1, h⟩ := by
        rw [hj]; exact lt_of_le_of_lt (cellLeft_le hne) hx.2
      exact Fin.lt_def.mp (hs.cellStarts_lt_iff.mp this)
    · rw [h]; exact j.isLt
  simp only [Fin.lt_def] at h1
  omega

/-- Two distinct cells have disjoint images. -/
lemma IsCutSet.image_cell_disjoint {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (hlt : a < b) (hinj : Function.Injective f)
    {i j : Fin (insert a s).card} (hij : i ≠ j) :
    Disjoint (f '' Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1)))
      (f '' Set.Ico (hs.cellStarts j) (hs.cellPos (j.val + 1))) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨x, hx, hxz⟩ := hz
  obtain ⟨x', hx', hx'z⟩ := hz'
  have hxx : x = x' := hinj (by rw [hxz, hx'z])
  subst hxx
  have h1 := hs.cellLeft_eq hlt hx
  have h2 := hs.cellLeft_eq hlt hx'
  have hval : hs.cellStarts i = hs.cellStarts j := by rw [← h1, ← h2]
  exact hij ((Finset.orderIsoOfFin (insert a s) rfl).injective (Subtype.ext hval))

/-- **`f` translates the whole cell of `β i`.** -/
lemma IsCutSet.map_of_mem_cell {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (hlt : a < b) {i : Fin (insert a s).card} {x : ℝ}
    (hx : x ∈ Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1))) :
    f x = x + (f (hs.cellStarts i) - hs.cellStarts i) := by
  have hβ := hs.cellStarts_mem_Ico hlt i
  have hxmem : x ∈ Set.Ico a b :=
    ⟨le_trans hβ.1 hx.1, lt_of_lt_of_le hx.2 (hs.cellPos_le hlt _)⟩
  have hmap := hs.map_eq_cell (f := f) hxmem
  have hcell : cellLeft (insert a s) x ⟨a, by simp [hxmem.1]⟩ = hs.cellStarts i := by
    have hne : ((insert a s).filter (fun c => c ≤ x)).Nonempty := ⟨a, by simp [hxmem.1]⟩
    refine le_antisymm ?_ (le_cellLeft hne (hs.cellStarts_mem i) hx.1)
    by_contra hcon
    rw [not_le] at hcon
    -- `cellLeft x` would be a cell start strictly between `β i` and the end of the cell
    obtain ⟨j, hj⟩ := hs.cellStarts_surj (cellLeft_mem hne)
    have h1 : i < j := hs.cellStarts_lt_iff.mp (by rw [hj]; exact hcon)
    have h2 : j.val < i.val + 1 := by
      rcases hs.cellPos_succ i with ⟨h, hh⟩ | ⟨h, hh⟩
      · rw [hh] at hx
        have : hs.cellStarts j < hs.cellStarts ⟨i.val + 1, h⟩ := by
          rw [hj]; exact lt_of_le_of_lt (cellLeft_le hne) hx.2
        exact Fin.lt_def.mp (hs.cellStarts_lt_iff.mp this)
      · rw [h]; exact j.isLt
    simp only [Fin.lt_def] at h1
    omega
  rw [hcell] at hmap
  exact hmap

/-- **The image of a cell is the interval** `[f β, f β + λ)`. -/
lemma IsCutSet.image_cell {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (hlt : a < b) (i : Fin (insert a s).card) :
    f '' (Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1)))
      = Set.Ico (f (hs.cellStarts i)) (f (hs.cellStarts i) + hs.cellLen i) := by
  have hβpos : hs.cellPos i.val = hs.cellStarts i := hs.cellPos_of_lt i.isLt
  have hstep : hs.cellLen i = hs.cellPos (i.val + 1) - hs.cellStarts i := by
    unfold IsCutSet.cellLen
    rw [hβpos]
  rw [hstep]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hs.map_of_mem_cell hlt hx]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · intro hy
    refine ⟨y - (f (hs.cellStarts i) - hs.cellStarts i), ⟨?_, ?_⟩, ?_⟩
    · linarith [hy.1]
    · linarith [hy.2]
    · rw [hs.map_of_mem_cell hlt ⟨by linarith [hy.1], by linarith [hy.2]⟩]
      ring

/-- **No image interval crosses another**: if the image of the `j`-th cell starts left of the image of
the `i`-th, it ends at or before it. -/
lemma IsCutSet.image_cell_le {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (hlt : a < b) (hinj : Function.Injective f)
    {i j : Fin (insert a s).card} (hij : i ≠ j)
    (hlt' : f (hs.cellStarts j) < f (hs.cellStarts i)) :
    f (hs.cellStarts j) + hs.cellLen j ≤ f (hs.cellStarts i) := by
  by_contra hcon
  rw [not_le] at hcon
  have hmem : f (hs.cellStarts i) ∈ f '' Set.Ico (hs.cellStarts j) (hs.cellPos (j.val + 1)) := by
    rw [hs.image_cell hlt j]
    exact ⟨le_of_lt hlt', hcon⟩
  obtain ⟨x, hx, hfx⟩ := hmem
  have hxi : x = hs.cellStarts i := hinj hfx
  subst hxi
  have h1 := hs.cellLeft_eq hlt hx
  have h2 : cellLeft (insert a s) (hs.cellStarts i)
      ⟨a, by simp [(hs.cellStarts_mem_Ico hlt i).1]⟩
      = hs.cellStarts i := by
    have hne : ((insert a s).filter (fun c => c ≤ hs.cellStarts i)).Nonempty :=
      ⟨hs.cellStarts i, by simp [hs.cellStarts_mem i]⟩
    exact le_antisymm (cellLeft_le hne) (le_cellLeft hne (hs.cellStarts_mem i) le_rfl)
  have hval : hs.cellStarts j = hs.cellStarts i := by rw [← h1, h2]
  exact hij ((Finset.orderIsoOfFin (insert a s) rfl).injective (Subtype.ext hval.symm))

/-- The lengths of the cells before the `i`-th sum to `β i - a`. -/
lemma IsCutSet.sum_cellLen_lt {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (hne : 0 < (insert a s).card)
    (i : Fin (insert a s).card) :
    ∑ j ∈ Finset.univ.filter (fun j => j < i), hs.cellLen j = hs.cellStarts i - a := by
  classical
  have hpos : ∀ j : Fin (insert a s).card, hs.cellLen j = hs.cellPos (j.val + 1) - hs.cellPos j.val := by
    intro j
    have h1 := hs.cellPos_of_lt j.isLt
    unfold IsCutSet.cellLen
    rw [h1]
  have hbij : ∑ j ∈ Finset.univ.filter (fun j : Fin (insert a s).card => j < i), hs.cellLen j
      = ∑ k ∈ Finset.range i.val, (hs.cellPos (k + 1) - hs.cellPos k) := by
    refine Finset.sum_bij (fun (j : Fin (insert a s).card) _ => j.val) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_range]
      exact Fin.lt_def.mp hj
    · intro j1 _ j2 _ h
      exact Fin.ext h
    · intro k hk
      simp only [Finset.mem_range] at hk
      refine ⟨⟨k, lt_trans hk i.isLt⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Fin.lt_def.mpr hk
    · intro j _
      exact hpos j
  rw [hbij, Finset.sum_range_sub]
  rw [hs.cellPos_of_lt i.isLt, hs.cellPos_of_lt (k := 0) hne, hs.cellStarts_zero hne]

/-- The left endpoints of the images of the cells: the images of the cell starts. -/
noncomputable def IsCutSet.imageStarts {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (_hs : IsCutSet f a b s) : Finset ℝ :=
  (insert a s).image f

/-- Membership in the set of image starts. -/
lemma IsCutSet.mem_imageStarts {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) {y : ℝ} :
    y ∈ hs.imageStarts ↔ ∃ β ∈ insert a s, f β = y :=
  Finset.mem_image

/-- There are as many image starts as cell starts, provided `f` is injective. -/
lemma IsCutSet.imageStarts_card {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (hinj : Function.Injective f) :
    hs.imageStarts.card = (insert a s).card :=
  Finset.card_image_of_injective _ hinj

/-- The image starts lie in `[a, b)`. -/
lemma IsCutSet.imageStarts_subset {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) {hlt : a < b} :
    ∀ y ∈ hs.imageStarts, y ∈ Set.Ico a b := by
  intro y hy
  obtain ⟨β, hβ, rfl⟩ := hs.mem_imageStarts.mp hy
  rcases Finset.mem_insert.mp hβ with h | h'
  · rw [h]
    exact hs.mapsTo a ⟨le_rfl, hlt⟩
  · exact hs.mapsTo β (hs.cuts_mem β h')

/-- **The permutation of the cells**: the `i`-th cell goes to the position of its image among the
image starts. -/
noncomputable def IsCutSet.cellPerm {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (hinj : Function.Injective f) :
    Equiv.Perm (Fin (insert a s).card) :=
  let iso₁ := Finset.orderIsoOfFin (insert a s) rfl
  let iso₂ := Finset.orderIsoOfFin hs.imageStarts (hs.imageStarts_card hinj)
  Equiv.ofBijective
    (fun i => iso₂.symm ⟨f (iso₁ i), hs.mem_imageStarts.mpr ⟨(iso₁ i).1, (iso₁ i).2, rfl⟩⟩)
    ⟨fun i j h => by
      have h' : (⟨f (iso₁ i), _⟩ : ↥hs.imageStarts) = ⟨f (iso₁ j), _⟩ := iso₂.symm.injective h
      have hval : f (iso₁ i) = f (iso₁ j) := congrArg Subtype.val h'
      exact iso₁.injective (Subtype.ext (hinj hval)),
     fun j => by
      have hy : (iso₂ j : ℝ) ∈ hs.imageStarts := (iso₂ j).2
      obtain ⟨β, hβ, hfβ⟩ := hs.mem_imageStarts.mp hy
      refine ⟨iso₁.symm ⟨β, hβ⟩, ?_⟩
      show iso₂.symm ⟨f (iso₁ (iso₁.symm ⟨β, hβ⟩)), _⟩ = j
      rw [iso₁.apply_symm_apply]
      have himg : (⟨f β, hs.mem_imageStarts.mpr ⟨β, hβ, rfl⟩⟩ : ↥hs.imageStarts) = iso₂ j :=
        Subtype.ext hfβ
      rw [himg, iso₂.symm_apply_apply]⟩

/-- `cellPerm` lands on the position of the image of the cell start. -/
lemma IsCutSet.cellPerm_val {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (hinj : Function.Injective f) (i : Fin (insert a s).card) :
    (Finset.orderIsoOfFin hs.imageStarts (hs.imageStarts_card hinj)) (hs.cellPerm hinj i)
      = ⟨f (hs.cellStarts i),
          hs.mem_imageStarts.mpr ⟨hs.cellStarts i, hs.cellStarts_mem i, rfl⟩⟩ := by
  unfold IsCutSet.cellPerm
  exact (Finset.orderIsoOfFin hs.imageStarts (hs.imageStarts_card hinj)).apply_symm_apply _

/-- `π j < π i` exactly when the image of the `j`-th cell starts left of the image of the `i`-th. -/
lemma IsCutSet.cellPerm_lt_iff {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (hinj : Function.Injective f) {i j : Fin (insert a s).card} :
    hs.cellPerm hinj j < hs.cellPerm hinj i ↔ f (hs.cellStarts j) < f (hs.cellStarts i) := by
  have key : ∀ k : Fin (insert a s).card,
      (Finset.orderIsoOfFin hs.imageStarts (hs.imageStarts_card hinj)) (hs.cellPerm hinj k)
        = ⟨f (hs.cellStarts k),
            hs.mem_imageStarts.mpr ⟨hs.cellStarts k, hs.cellStarts_mem k, rfl⟩⟩ :=
    fun k => hs.cellPerm_val hinj k
  constructor
  · intro h
    have h2 := (Finset.orderIsoOfFin hs.imageStarts (hs.imageStarts_card hinj)).strictMono h
    rw [key j, key i] at h2
    exact h2
  · intro h
    have h2 : (Finset.orderIsoOfFin hs.imageStarts (hs.imageStarts_card hinj)) (hs.cellPerm hinj j)
        < (Finset.orderIsoOfFin hs.imageStarts (hs.imageStarts_card hinj)) (hs.cellPerm hinj i) := by
      rw [key j, key i]
      exact h
    exact (Finset.orderIsoOfFin hs.imageStarts (hs.imageStarts_card hinj)).lt_iff_lt.mp h2

/-- **The image intervals of the cells whose image starts left of `f (β i)` cover `[a, f (β i))`.** -/
lemma IsCutSet.image_union {e : Equiv ℝ ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet (⇑e) a b s) (hlt : a < b) (i : Fin (insert a s).card) :
    (⋃ j : {j : Fin (insert a s).card // hs.cellPerm e.injective j < hs.cellPerm e.injective i},
        ⇑e '' Set.Ico (hs.cellStarts j.1) (hs.cellPos (j.1.val + 1)))
      = Set.Ico a (⇑e (hs.cellStarts i)) := by
  have hβi := hs.cellStarts_mem_Ico hlt i
  ext y
  constructor
  · intro hy
    obtain ⟨j, yimg⟩ := Set.mem_iUnion.mp hy
    obtain ⟨x, hx, rfl⟩ := yimg
    have hpos : ⇑e (hs.cellStarts j.1) < ⇑e (hs.cellStarts i) :=
      (hs.cellPerm_lt_iff e.injective).mp j.2
    have hne' : j.1 ≠ i := fun h => absurd (h ▸ j.2) (lt_irrefl _)
    have hle := hs.image_cell_le hlt e.injective (i := i) (j := j.1) hne'.symm hpos
    have hmap := hs.map_of_mem_cell hlt hx
    have hxj := hs.cellStarts_mem_Ico hlt j.1
    refine ⟨?_, ?_⟩
    · have : a ≤ ⇑e (hs.cellStarts j.1) := (hs.mapsTo _ hxj).1
      rw [hmap]; linarith [hx.1]
    · rw [hmap]
      have hlen : hs.cellLen j.1 = hs.cellPos (j.1.val + 1) - hs.cellStarts j.1 := by
        unfold IsCutSet.cellLen
        rw [hs.cellPos_of_lt j.1.isLt]
      linarith [hx.2, hle, hlen]
  · intro hy
    have hy' : y ∈ Set.Ico a b := ⟨hy.1, lt_trans hy.2 (hs.mapsTo _ hβi).2⟩
    have hx : e.symm y ∈ Set.Ico a b := Equiv.IsIET.symm_mapsTo (e := e) hs hy'
    have hxeq : ⇑e (e.symm y) = y := Equiv.apply_symm_apply e y
    have hne : ((insert a s).filter (fun c => c ≤ e.symm y)).Nonempty := ⟨a, by simp [hx.1]⟩
    obtain ⟨j, hj⟩ := hs.cellStarts_surj (cellLeft_mem hne)
    have hmemx : e.symm y ∈ Set.Ico (hs.cellStarts j) (hs.cellPos (j.val + 1)) := by
      refine ⟨?_, ?_⟩
      · rw [hj]; exact cellLeft_le hne
      · rcases hs.cellPos_succ j with ⟨h, hh⟩ | ⟨h, hh⟩
        · rw [hh]
          by_contra hcon
          rw [not_lt] at hcon
          have hcut : hs.cellStarts ⟨j.val + 1, h⟩ ∈ insert a s := hs.cellStarts_mem _
          have hle2 : hs.cellStarts ⟨j.val + 1, h⟩ ≤ hs.cellStarts j := by
            rw [hj]
            exact le_cellLeft hne hcut hcon
          have hlt2 : hs.cellStarts j < hs.cellStarts ⟨j.val + 1, h⟩ :=
            hs.cellStarts_lt_iff.mpr (Fin.lt_def.mpr (by simp))
          linarith
        · rw [hh]; exact hx.2
    have hpos : ⇑e (hs.cellStarts j) < ⇑e (hs.cellStarts i) := by
      have hmap := hs.map_of_mem_cell hlt hmemx
      have h1 : ⇑e (hs.cellStarts j) ≤ y := by
        rw [hxeq] at hmap
        linarith [hmemx.1]
      linarith [h1, hy.1, hy.2]
    exact Set.mem_iUnion.mpr ⟨⟨j, (hs.cellPerm_lt_iff e.injective).mpr hpos⟩,
      ⟨e.symm y, hmemx, hxeq⟩⟩

/-- **The sum of the lengths of the cells whose images start left of `f (β i)` is `f (β i) - a`.** -/
lemma IsCutSet.sum_cellLen_image {e : Equiv ℝ ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet (⇑e) a b s) (hlt : a < b) (i : Fin (insert a s).card) :
    ∑ j ∈ Finset.univ.filter (fun j => hs.cellPerm e.injective j < hs.cellPerm e.injective i),
        hs.cellLen j = ⇑e (hs.cellStarts i) - a := by
  classical
  set F := Finset.univ.filter (fun j => hs.cellPerm e.injective j < hs.cellPerm e.injective i) with hF
  have hnn : ∀ j ∈ F, 0 ≤ hs.cellLen j := by
    intro j _
    have h1 := hs.cellPos_of_lt j.isLt
    have h2 := hs.cellStarts_lt_cellPos hlt j
    unfold IsCutSet.cellLen
    rw [h1]
    linarith
  -- the intervals are pairwise disjoint
  have hdisj : (↑F : Set (Fin (insert a s).card)).PairwiseDisjoint
      (fun j => Set.Ico (⇑e (hs.cellStarts j)) (⇑e (hs.cellStarts j) + hs.cellLen j)) := by
    intro j _ k _ hjk
    have hd := hs.image_cell_disjoint hlt e.injective hjk
    rwa [hs.image_cell hlt j, hs.image_cell hlt k] at hd
  -- their union is `[a, f (β i))`
  have hunion : (⋃ j ∈ F, Set.Ico (⇑e (hs.cellStarts j)) (⇑e (hs.cellStarts j) + hs.cellLen j))
      = Set.Ico a (⇑e (hs.cellStarts i)) := by
    have h := hs.image_union hlt i
    rw [Set.iUnion_subtype] at h
    simp only [hs.image_cell hlt, hF, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    exact h
  -- the measure computation
  have hmeas : volume (Set.Ico a (⇑e (hs.cellStarts i)))
      = ∑ j ∈ F, volume (Set.Ico (⇑e (hs.cellStarts j)) (⇑e (hs.cellStarts j) + hs.cellLen j)) := by
    rw [← hunion]
    exact measure_biUnion_finset hdisj (fun j _ => measurableSet_Ico)
  have hof : ENNReal.ofReal (∑ j ∈ F, hs.cellLen j)
      = ∑ j ∈ F, volume (Set.Ico (⇑e (hs.cellStarts j)) (⇑e (hs.cellStarts j) + hs.cellLen j)) := by
    rw [ENNReal.ofReal_sum_of_nonneg hnn]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Real.volume_Ico]
    congr 1
    ring
  rw [← hmeas] at hof
  rw [Real.volume_Ico] at hof
  have hsum : 0 ≤ ∑ j ∈ F, hs.cellLen j := Finset.sum_nonneg hnn
  have hfin : 0 ≤ ⇑e (hs.cellStarts i) - a := by
    have := (hs.mapsTo _ (hs.cellStarts_mem_Ico hlt i)).1
    linarith
  exact (ENNReal.ofReal_eq_ofReal_iff hsum hfin).mp hof



/-- **Tiling, cover half**: every `y ∈ [a, b)` lies in the image of the cell of `e.symm y`, and that
cell starts at or below `y` — the left end of its image is `e β ≤ y`. -/
lemma Equiv.IsIET.tiling {a b : ℝ} {e : Equiv ℝ ℝ} {s : Finset ℝ}
    (hs : IsCutSet (⇑e) a b s) {y : ℝ} (hy : y ∈ Set.Ico a b) :
    ∃ β ∈ insert a s, β ≤ e.symm y ∧ ⇑e β ≤ y := by
  have hx : e.symm y ∈ Set.Ico a b := Equiv.IsIET.symm_mapsTo (e := e) hs hy
  have hne : ((insert a s).filter (fun c => c ≤ e.symm y)).Nonempty := ⟨a, by simp [hx.1]⟩
  refine ⟨cellLeft (insert a s) (e.symm y) hne, cellLeft_mem hne, cellLeft_le hne, ?_⟩
  have hm := hs.map_eq_cell (f := ⇑e) hx
  rw [Equiv.apply_symm_apply] at hm
  have hβ : cellLeft (insert a s) (e.symm y) hne ≤ e.symm y := cellLeft_le hne
  linarith

/-- **Tiling, disjointness half**: two cells with different left endpoints have disjoint images —
`e` is injective and translates each cell. -/
lemma Equiv.IsIET.tiling_disjoint {a b : ℝ} {e : Equiv ℝ ℝ} {s : Finset ℝ}
    (_hs : IsCutSet (⇑e) a b s) {x x' : ℝ} (hx : x ∈ Set.Ico a b) (hx' : x' ∈ Set.Ico a b)
    (hne : cellLeft (insert a s) x ⟨a, by simp [hx.1]⟩
      ≠ cellLeft (insert a s) x' ⟨a, by simp [hx'.1]⟩) : ⇑e x ≠ ⇑e x' := by
  intro hcon
  have hxx' : x = x' := e.injective hcon
  subst hxx'
  exact hne rfl

/-- **The preimage of a finite set under an exchange is finite**: on each of the finitely many
cells `f` is a translation, so each cut of `t` has at most one preimage per cell. -/
lemma IsCutSet.finite_preimage {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ} (hs : IsCutSet f a b s)
    (t : Finset ℝ) : (f ⁻¹' (t : Set ℝ)).Finite := by
  classical
  refine Set.Finite.subset (t.finite_toSet.union
    ((t ×ˢ insert a s).image (fun p : ℝ × ℝ => p.1 - (f p.2 - p.2))).finite_toSet) ?_
  intro x hx
  simp only [Set.mem_preimage, Set.mem_union, Finset.mem_coe] at hx ⊢
  by_cases hxa : x < a
  · exact Or.inl (by rw [hs.apply_eq_self_of_lt x hxa] at hx; exact hx)
  rcases lt_or_ge x b with hxb | hxb
  · right
    have hne : ((insert a s).filter (fun c => c ≤ x)).Nonempty := ⟨a, by simp [not_lt.mp hxa]⟩
    set β := cellLeft (insert a s) x hne with hβ
    have hβmem : β ∈ insert a s := cellLeft_mem hne
    have hβle : β ≤ x := cellLeft_le hne
    have hβa : a ≤ β := by
      rcases Finset.mem_insert.mp hβmem with h | hβs
      · exact le_of_eq h.symm
      · exact (hs.cuts_mem β hβs).1
    have hβb : β < b := lt_of_le_of_lt hβle hxb
    have hdisp : f x - x = f β - β :=
      hs.transl_of_not_separated β x ⟨hβa, hβb⟩ ⟨not_lt.mp hxa, hxb⟩
        (fun hh => not_separated_cellLeft hne (Separated.mono hh (Finset.subset_insert a s)))
    refine Finset.mem_image.mpr ⟨(f x, β), Finset.mem_product.mpr ⟨hx, hβmem⟩, ?_⟩
    show f x - (f β - β) = x
    linarith
  · exact Or.inl (by rw [hs.apply_eq_self_of_le x hxb] at hx; exact hx)

/-- The preimage of a finite set, as a finset, for an exchange. -/
noncomputable def IsCutSet.preimage {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) (t : Finset ℝ) : Finset ℝ :=
  (hs.finite_preimage t).toFinset

/-- Membership in the set of preimages. -/
lemma IsCutSet.mem_preimage {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ} (hs : IsCutSet f a b s)
    {t : Finset ℝ} {p : ℝ} : p ∈ hs.preimage t ↔ f p ∈ t := by
  unfold IsCutSet.preimage
  rw [Set.Finite.mem_toFinset]
  exact Iff.rfl

/-- The cuts of the preimage set lie in `[a, b)`. -/
lemma IsCutSet.preimage_subset {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ} (hs : IsCutSet f a b s)
    {t : Finset ℝ} (ht : ∀ c ∈ t, c ∈ Set.Ico a b) : ∀ p ∈ hs.preimage t, p ∈ Set.Ico a b := by
  intro p hp
  have hfp : f p ∈ t := hs.mem_preimage.mp hp
  by_cases hpa : a ≤ p
  · by_cases hpb : p < b
    · exact ⟨hpa, hpb⟩
    · rw [hs.apply_eq_self_of_le p (not_lt.mp hpb)] at hfp
      exact absurd (ht p hfp).2 (not_lt.mpr (not_lt.mp hpb))
  · rw [hs.apply_eq_self_of_lt p (not_le.mp hpa)] at hfp
    exact absurd (ht p hfp).1 hpa

/-- `f` is a translation in a neighbourhood of `c` (inside `[a, b)`). -/
def IsLocallyTranslationAt (f : ℝ → ℝ) (a b c : ℝ) : Prop :=
  ∃ σ : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℝ, z ∈ Set.Ico a b → |z - c| < ε → f z = z + σ

/-- **A true discontinuity belongs to every cut set.**  If `f` is not locally a translation at `c`,
then `c` lies in every cut set: otherwise `c` would be in the interior of a piece of that cut set,
on which `f` is a translation.  Here `c ∉ s` only says that `c` is not a cut of `s`, and the
distance from `c` to the other cuts of `s` is positive because they are distinct from `c`. -/
lemma IsCutSet.locallyTranslationAt_of_not_mem {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) {c : ℝ} (hc : c ∈ Set.Ico a b) (hcs : c ∉ s) :
    IsLocallyTranslationAt f a b c := by
  classical
  -- the distance from `c` to the other cuts is positive, since they are distinct from `c`
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ s, u ≠ c → δ ≤ |u - c| := by
    rcases (s.filter (fun u => u ≠ c)).eq_empty_or_nonempty with hemp | hne
    · refine ⟨1, one_pos, ?_⟩
      intro u hu huc
      exact absurd (Finset.mem_filter.mpr ⟨hu, huc⟩) (by rw [hemp]; simp)
    · set D := (s.filter (fun u => u ≠ c)).image (fun u => |u - c|) with hD
      have hDne : D.Nonempty := hne.image _
      have hDmem : D.min' hDne ∈ D := Finset.min'_mem _ _
      have hDpos : 0 < D.min' hDne := by
        obtain ⟨u, hu, hue⟩ := Finset.mem_image.mp hDmem
        have huc : u ≠ c := (Finset.mem_filter.mp hu).2
        rw [← hue]
        exact abs_pos.mpr (sub_ne_zero.mpr huc)
      refine ⟨D.min' hDne, hDpos, ?_⟩
      intro u hu huc
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, huc⟩, rfl⟩)
  refine ⟨f c - c, δ, hδpos, ?_⟩
  intro z hz hzc
  have hns : ¬ Separated s z c := by
    rintro ⟨u, hu, hui⟩
    have huc : u ≠ c := by rintro rfl; exact absurd hu hcs
    have hle : |u - c| ≤ |z - c| := by
      rcases le_total z c with h | h
      · rw [min_eq_left h, max_eq_right h] at hui
        have h1 : |u - c| = c - u := by
          rw [abs_of_nonpos (by linarith [hui.2]), neg_sub]
        have h2 : |z - c| = c - z := by
          rw [abs_of_nonpos (by linarith), neg_sub]
        rw [h1, h2]; linarith [hui.1]
      · rw [min_eq_right h, max_eq_left h] at hui
        have h1 : |u - c| = u - c := by
          rw [abs_of_nonneg (by linarith [hui.1])]
        have h2 : |z - c| = z - c := by
          rw [abs_of_nonneg (by linarith)]
        rw [h1, h2]; linarith [hui.2]
    linarith [hδ u hu huc]
  have hdisp := hs.transl_of_not_separated z c hz hc hns
  linarith

/-- **Composition of cut sets**: the cuts of `g ∘ f` are those of `f` together with the preimages
under `f` of the cuts of `g` — finite because `f` is finite-to-one. -/
lemma IsCutSet.comp {s t : Finset ℝ} {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IsCutSet f a b s) (hg : IsCutSet g a b t) :
    IsCutSet (g ∘ f) a b (s ∪ hf.preimage t) := by
  classical
  have ht_sub : ∀ c ∈ t, c ∈ Set.Ico a b := hg.cuts_mem
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Function.comp_apply, hf.apply_eq_self_of_lt x hx, hg.apply_eq_self_of_lt x hx]
  · intro x hx
    simp only [Function.comp_apply, hf.apply_eq_self_of_le x hx, hg.apply_eq_self_of_le x hx]
  · intro x hx
    exact hg.mapsTo (f x) (hf.mapsTo x hx)
  · intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact hf.cuts_mem c hc
    · exact hf.preimage_subset ht_sub c hc
  · intro x y hx hy hns
    have hns_s : ¬ Separated s x y := fun h => hns (Separated.mono h Finset.subset_union_left)
    have hfdisp : f y - y = f x - x := hf.transl_of_not_separated x y hx hy hns_s
    have hns_t : ¬ Separated t (f x) (f y) := by
      rintro ⟨c, hc, hcin⟩
      rcases le_total x y with hxy | hyx
      · have hfxle : f x ≤ f y := by linarith
        rw [min_eq_left hfxle, max_eq_right hfxle] at hcin
        obtain ⟨hc1, hc2⟩ := hcin
        set p : ℝ := c - (f y - y) with hp
        have hpx : x < p := by rw [hp]; linarith
        have hpy : p ≤ y := by rw [hp]; linarith
        have hpdom : p ∈ Set.Ico a b :=
          ⟨le_of_lt (lt_of_le_of_lt hx.1 hpx), lt_of_le_of_lt hpy hy.2⟩
        have hns_sp : ¬ Separated s x p := by
          rintro ⟨d, hd, hdin⟩
          rw [min_eq_left hpx.le, max_eq_right hpx.le] at hdin
          exact hns_s ⟨d, hd, by
            rw [min_eq_left hxy, max_eq_right hxy]
            exact ⟨hdin.1, le_trans hdin.2 hpy⟩⟩
        have hfp : f p - p = f x - x := hf.transl_of_not_separated x p hx hpdom hns_sp
        have hfpc : f p = c := by rw [hp]; linarith
        have hpmem : p ∈ s ∪ hf.preimage t :=
          Finset.mem_union_right _ (hf.mem_preimage.mpr (by rw [hfpc]; exact hc))
        exact hns ⟨p, hpmem, by
          rw [min_eq_left hxy, max_eq_right hxy]
          exact ⟨hpx, hpy⟩⟩
      · have hfyle : f y ≤ f x := by linarith
        rw [min_eq_right hfyle, max_eq_left hfyle] at hcin
        obtain ⟨hc1, hc2⟩ := hcin
        set p : ℝ := c - (f x - x) with hp
        have hpy : y < p := by rw [hp]; linarith
        have hpx : p ≤ x := by rw [hp]; linarith
        have hpdom : p ∈ Set.Ico a b :=
          ⟨le_of_lt (lt_of_le_of_lt hy.1 hpy), lt_of_le_of_lt hpx hx.2⟩
        have hns_sp : ¬ Separated s y p := by
          rintro ⟨d, hd, hdin⟩
          rw [min_eq_left hpy.le, max_eq_right hpy.le] at hdin
          exact hns_s ⟨d, hd, by
            rw [min_eq_right hyx, max_eq_left hyx]
            exact ⟨hdin.1, le_trans hdin.2 hpx⟩⟩
        have hfp : f p - p = f y - y := hf.transl_of_not_separated y p hy hpdom hns_sp
        have hfpc : f p = c := by rw [hp]; linarith
        have hpmem : p ∈ s ∪ hf.preimage t :=
          Finset.mem_union_right _ (hf.mem_preimage.mpr (by rw [hfpc]; exact hc))
        exact hns ⟨p, hpmem, by
          rw [min_eq_right hyx, max_eq_left hyx]
          exact ⟨hpy, hpx⟩⟩
    have hgd : g (f y) - f y = g (f x) - f x :=
      hg.transl_of_not_separated (f x) (f y) (hf.mapsTo x hx) (hf.mapsTo y hy) hns_t
    show g (f y) - y = g (f x) - x
    linarith

/-- **The displacement is constant across non-jumps.**  If every cut of `s` strictly between `x`
and `y` is a point where `f` is locally a translation, then the displacement of `f` at `x` and at
`y` agree. -/
private lemma transl_of_locally_le {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet f a b s) {x y : ℝ} (hxy : x ≤ y)
    (hx : x ∈ Set.Ico a b) (hy : y ∈ Set.Ico a b)
    (h : ∀ c ∈ s, x < c → c ≤ y → IsLocallyTranslationAt f a b c) :
    f y - y = f x - x := by
  classical
  let P : ℕ → Prop := fun n => ∀ x y : ℝ, x ≤ y →
    x ∈ Set.Ico a b → y ∈ Set.Ico a b →
    (∀ c ∈ s, x < c → c ≤ y → IsLocallyTranslationAt f a b c) →
    (s.filter (fun c => x < c ∧ c ≤ y)).card = n → f y - y = f x - x
  have main : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x y hxy hx hy h hcard
      by_cases hne : (s.filter (fun c => x < c ∧ c ≤ y)).Nonempty
      · obtain ⟨c, hc⟩ := hne
        simp only [Finset.mem_filter] at hc
        obtain ⟨hcs, hxc, hcy⟩ := hc
        have hcdom : c ∈ Set.Ico a b := hs.cuts_mem c hcs
        have hloc := h c hcs hxc hcy
        obtain ⟨σ, ε, hεpos, hloc_eq⟩ := hloc
        let p : ℝ := max x (c - ε / 2)
        let q : ℝ := min y (c + ε / 2)
        have hxp : x ≤ p := le_max_left x (c - ε / 2)
        have hpge : c - ε / 2 ≤ p := le_max_right x (c - ε / 2)
        have hp_lt_c : p < c := max_lt hxc (by linarith)
        have hpc : p ≤ c := le_of_lt hp_lt_c
        have hpdom : p ∈ Set.Ico a b := by
          constructor
          · exact le_trans hx.1 hxp
          · exact lt_of_le_of_lt hpc hcdom.2
        have hpclose : |p - c| < ε := by
          rw [abs_of_nonpos (by linarith)]
          linarith
        have hcq : c ≤ q := le_min hcy (by linarith)
        have hqle : q ≤ c + ε / 2 := min_le_right y (c + ε / 2)
        have hqy : q ≤ y := min_le_left y (c + ε / 2)
        have hqdom : q ∈ Set.Ico a b := by
          constructor
          · exact le_trans hcdom.1 hcq
          · exact lt_of_le_of_lt hqy hy.2
        have hqclose : |q - c| < ε := by
          rw [abs_of_nonneg (by linarith)]
          linarith
        have hfc : f c = c + σ := hloc_eq c hcdom (by simpa using hεpos)
        have hfp : f p = p + σ := hloc_eq p hpdom hpclose
        have hfq : f q = q + σ := hloc_eq q hqdom hqclose
        have hpc_eq : f p - p = f c - c := by
          rw [hfp, hfc]
          ring
        have hcq_eq : f q - q = f c - c := by
          rw [hfq, hfc]
          ring
        let P1 : Finset ℝ := s.filter (fun d => x < d ∧ d ≤ p)
        let P0 : Finset ℝ := s.filter (fun d => x < d ∧ d ≤ y)
        have hP0card : P0.card = n := by
          simpa [P0] using hcard
        have hcP0 : c ∈ P0 := by
          simp only [P0, Finset.mem_filter]
          exact ⟨hcs, hxc, hcy⟩
        have hsub1 : P1 ⊆ P0 := by
          intro d hd
          simp only [P1, P0, Finset.mem_filter] at hd ⊢
          exact ⟨hd.1, hd.2.1, le_trans hd.2.2 (le_trans hpc hcy)⟩
        have hproper1 : P1 ⊂ P0 := by
          rw [Finset.ssubset_iff_of_subset hsub1]
          refine ⟨c, hcP0, ?_⟩
          simp only [P1, Finset.mem_filter]
          rintro ⟨-, -, hcp⟩
          exact (not_le_of_gt hp_lt_c) hcp
        have hlt1 : P1.card < n := by
          have := Finset.card_lt_card hproper1
          simpa [hP0card] using this
        have hrestricted1 : ∀ d ∈ s, x < d → d ≤ p →
            IsLocallyTranslationAt f a b d := by
          intro d hds hxd hdp
          exact h d hds hxd (le_trans hdp (le_trans hpc hcy))
        have hrec1 : f p - p = f x - x :=
          ih P1.card hlt1 x p hxp hx hpdom hrestricted1 (by simp [P1])
        let P2 : Finset ℝ := s.filter (fun d => q < d ∧ d ≤ y)
        have hsub2 : P2 ⊆ P0 := by
          intro d hd
          simp only [P2, P0, Finset.mem_filter] at hd ⊢
          exact ⟨hd.1, lt_trans hxc (lt_of_le_of_lt hcq hd.2.1), hd.2.2⟩
        have hproper2 : P2 ⊂ P0 := by
          rw [Finset.ssubset_iff_of_subset hsub2]
          refine ⟨c, hcP0, ?_⟩
          simp only [P2, Finset.mem_filter]
          rintro ⟨-, hqc, -⟩
          exact (not_lt_of_ge hcq) hqc
        have hlt2 : P2.card < n := by
          have := Finset.card_lt_card hproper2
          simpa [hP0card] using this
        have hrestricted2 : ∀ d ∈ s, q < d → d ≤ y →
            IsLocallyTranslationAt f a b d := by
          intro d hds hqd hdy
          exact h d hds (lt_trans hxc (lt_of_le_of_lt hcq hqd)) hdy
        have hrec2 : f y - y = f q - q :=
          ih P2.card hlt2 q y hqy hqdom hy hrestricted2 (by simp [P2])
        calc
          f y - y = f q - q := hrec2
          _ = f c - c := hcq_eq
          _ = f p - p := hpc_eq.symm
          _ = f x - x := hrec1
      · have hnotsep : ¬ Separated s x y := by
          rintro ⟨c, hcs, hcint⟩
          have hcint' : x < c ∧ c ≤ y := by
            simpa [min_eq_left hxy, max_eq_right hxy] using hcint
          exact hne ⟨c, by
            simp only [Finset.mem_filter]
            exact ⟨hcs, hcint'⟩⟩
        exact hs.transl_of_not_separated x y hx hy hnotsep
  exact main ((s.filter (fun c => x < c ∧ c ≤ y)).card) x y hxy hx hy h rfl

/-- The displacement of `f` is constant across non-jumps. -/
theorem IsCutSet.transl_of_locally {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ} (hs : IsCutSet f a b s)
    {x y : ℝ} (hx : x ∈ Set.Ico a b) (hy : y ∈ Set.Ico a b)
    (h : ∀ c ∈ s, min x y < c → c ≤ max x y → IsLocallyTranslationAt f a b c) :
    f y - y = f x - x := by
  sorry
