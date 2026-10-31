/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib

/-!
Cut sets and their cells.

An interval exchange on `[a, b)` translates each interval of a finite partition of `[a, b)`.  This
file sets up that partition: `IsCutSet f a b s` says that the finite set `s ⊆ [a, b)` is a set of
cuts for `f` (so that `f` translates each interval between consecutive cuts), and the API around it
is the cells `[β i, β (i+1))` (`cellStarts`, `cellPos`), their lengths `cellLen`, the left end
`cellLeft` of the cell containing a point, and the two halves of the statement that the images of
the cells form the same kind of partition (`Equiv.IsIET.tiling`, `tiling_disjoint`).

Nothing here is measure-theoretic: this is the combinatorial substrate of the development.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

/-- `C` separates `x` from `y`: some cut lies in `(min x y, max x y]`.  With the `Ico` convention
the pieces are `[α, β)`, so a cut `β` that equals `max x y` is a boundary point: it belongs to the
*next* piece and hence separates. -/
def Separated (C : Finset ℝ) (x y : ℝ) : Prop := ∃ c ∈ C, c ∈ Set.Ioc (min x y) (max x y)

/-- **A point of `(min x y, max x y]`, in the monotone form**: for `x ≤ y` it lies in `(x, y]`.
This is the raw-membership companion of `Separated.exists_of_le`, for the places where the cut is
already known and only its position has to be read off. -/
theorem mem_Ioc_min_max (x y : ℝ) {c : ℝ} (hxy : x ≤ y) :
    c ∈ Set.Ioc (min x y) (max x y) ↔ x < c ∧ c ≤ y := by
  rw [Set.mem_Ioc, min_eq_left hxy, max_eq_right hxy]

/-- The same in the other orientation: for `y ≤ x`, a point of `(min x y, max x y]` lies in
`(y, x]`. -/
theorem mem_Ioc_min_max_of_le {x y c : ℝ} (hyx : y ≤ x) :
    c ∈ Set.Ioc (min x y) (max x y) ↔ y < c ∧ c ≤ x := by
  rw [min_comm, max_comm]
  exact mem_Ioc_min_max y x hyx

/-- Separation survives passing to a larger set of cuts. -/
theorem Separated.mono {C C' : Finset ℝ} {x y : ℝ} (h : Separated C x y) (hsub : C ⊆ C') :
    Separated C' x y :=
  let ⟨c, hc, hci⟩ := h
  ⟨c, hsub hc, hci⟩

/-- Separation is symmetric: this is why the definition is stated with `min` and `max`. -/
theorem Separated.symm {C : Finset ℝ} {x y : ℝ} (h : Separated C x y) : Separated C y x := by
  simpa only [Separated, min_comm, max_comm] using h

/-- Separation is symmetric. -/
theorem Separated.comm {C : Finset ℝ} {x y : ℝ} : Separated C x y ↔ Separated C y x :=
  ⟨Separated.symm, Separated.symm⟩

/-- **A separating cut, in the monotone form**: if `x ≤ y`, some cut lies in `(x, y]`. -/
theorem Separated.exists_of_le {C : Finset ℝ} {x y : ℝ} (h : Separated C x y) (hxy : x ≤ y) :
    ∃ c ∈ C, x < c ∧ c ≤ y := by
  obtain ⟨c, hc, hci⟩ := h
  rw [Set.mem_Ioc, min_eq_left hxy, max_eq_right hxy] at hci
  exact ⟨c, hc, hci.1, hci.2⟩

/-- **To separate two points it suffices to exhibit a cut in `(x, y]`.**  No order between `x` and
`y` is needed: `min x y ≤ x` and `y ≤ max x y` whatever the order. -/
theorem Separated.of_lt_le {C : Finset ℝ} {x y c : ℝ} (hc : c ∈ C) (h1 : x < c) (h2 : c ≤ y) :
    Separated C x y :=
  ⟨c, hc, Set.mem_Ioc.mpr
    ⟨lt_of_le_of_lt (min_le_left x y) h1, le_trans h2 (le_max_right x y)⟩⟩

/-- `s` is a **cut set** for `f` on `[a, b)`: `f` is the identity below `a` and above `b`, maps
`[a, b)` into itself, `a` and every cut of `s` lie in `[a, b)`, and `f` is a translation on each
piece cut by `s`.

`a` itself is required to be a cut (`a_mem`).  This is what makes the cell of a point `x ∈ [a, b)`
well defined (`cellLeft`: the largest cut not exceeding `x` always exists, since `a` qualifies), and
it forces `a < b` (`IsCutSet.lt`).  Conversely, a cut set can always be enlarged by adding `a`. -/
structure IsCutSet (f : ℝ → ℝ) (a b : ℝ) (s : Finset ℝ) : Prop where
  /-- `f` is the identity below `a`. -/
  apply_eq_self_of_lt : ∀ x, x < a → f x = x
  /-- `f` is the identity from `b` on. -/
  apply_eq_self_of_le : ∀ x, b ≤ x → f x = x
  /-- `f` maps `[a, b)` into itself. -/
  mapsTo : ∀ x, x ∈ Set.Ico a b → f x ∈ Set.Ico a b
  /-- **`a` is a cut.** -/
  a_mem : a ∈ s
  /-- every cut lies in `[a, b)`. -/
  cuts_mem : ∀ c ∈ s, c ∈ Set.Ico a b
  /-- `f` is a translation on each piece cut by `s`. -/
  transl_of_not_separated : ∀ x y : ℝ, x ∈ Set.Ico a b → y ∈ Set.Ico a b → ¬ Separated s x y →
    f y - y = f x - x

-- the data of one cut set, in scope for the API below (`hs` stays a binder of each declaration)
section CutSetData

variable {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}

/-- **A cut set forces `a < b`**: `a` is one of its cuts, hence lies in `[a, b)`. -/
theorem IsCutSet.lt (hs : IsCutSet f a b s) : a < b :=
  (hs.cuts_mem a hs.a_mem).2

/-- A cut set is nonempty (it contains `a`). -/
theorem IsCutSet.nonempty (hs : IsCutSet f a b s) :
    s.Nonempty :=
  ⟨a, hs.a_mem⟩

/-- A cut set has positive cardinality. -/
theorem IsCutSet.card_pos (hs : IsCutSet f a b s) :
    0 < s.card :=
  Finset.card_pos.mpr hs.nonempty

/-- **The left end of the cell of `x`**: the largest cut not exceeding `x`.  The hypothesis `x ∈
[a, b)` is all that is needed: `a` is a cut and `a ≤ x`, so the set of candidates is nonempty. -/
noncomputable def IsCutSet.cellLeft (hs : IsCutSet f a b s)
    (x : ℝ) (hx : x ∈ Set.Ico a b) : ℝ :=
  (s.filter (fun c => c ≤ x)).max' ⟨a, Finset.mem_filter.mpr ⟨hs.a_mem, hx.1⟩⟩

/-- The left end of the cell of `x` is a cut. -/
theorem IsCutSet.cellLeft_mem (hs : IsCutSet f a b s)
    (x : ℝ) (hx : x ∈ Set.Ico a b) : hs.cellLeft x hx ∈ s := by
  have hmem : (s.filter (fun c => c ≤ x)).max'
      ⟨a, Finset.mem_filter.mpr ⟨hs.a_mem, hx.1⟩⟩ ∈ s.filter (fun c => c ≤ x) :=
    Finset.max'_mem _ _
  unfold IsCutSet.cellLeft
  exact (Finset.mem_filter.mp hmem).1

/-- The left end of the cell of `x` lies in `[a, b)`. -/
theorem IsCutSet.cellLeft_mem_Ico (hs : IsCutSet f a b s)
    (x : ℝ) (hx : x ∈ Set.Ico a b) : hs.cellLeft x hx ∈ Set.Ico a b :=
  hs.cuts_mem _ (hs.cellLeft_mem x hx)

/-- The left end of the cell of `x` is at most `x`. -/
theorem IsCutSet.cellLeft_le (hs : IsCutSet f a b s)
    (x : ℝ) (hx : x ∈ Set.Ico a b) : hs.cellLeft x hx ≤ x := by
  have hmem : (s.filter (fun c => c ≤ x)).max'
      ⟨a, Finset.mem_filter.mpr ⟨hs.a_mem, hx.1⟩⟩ ∈ s.filter (fun c => c ≤ x) :=
    Finset.max'_mem _ _
  unfold IsCutSet.cellLeft
  exact (Finset.mem_filter.mp hmem).2

/-- Every cut below `x` is below the left end of the cell of `x`. -/
theorem IsCutSet.le_cellLeft (hs : IsCutSet f a b s)
    {x c : ℝ} (hx : x ∈ Set.Ico a b) (hc : c ∈ s) (hcx : c ≤ x) : c ≤ hs.cellLeft x hx :=
  Finset.le_max' _ c (Finset.mem_filter.mpr ⟨hc, hcx⟩)

/-- No cut lies strictly between a point and the left end of its cell. -/
theorem IsCutSet.not_separated_cellLeft (hs : IsCutSet f a b s) {x : ℝ} (hx : x ∈ Set.Ico a b) :
    ¬ Separated s (hs.cellLeft x hx) x := by
  intro h
  obtain ⟨c, hc, h1, h2⟩ := h.exists_of_le (hs.cellLeft_le x hx)
  exact absurd (hs.le_cellLeft hx hc h2) (not_le.mpr h1)

/-- **`f` is a translation on each cell**: on the cell `[cellLeft x, next cut)` the displacement of
`f` is constant, equal to `f (cellLeft x) - cellLeft x`. -/
theorem IsCutSet.map_eq_cell (hs : IsCutSet f a b s)
    {x : ℝ} (hx : x ∈ Set.Ico a b) :
    f x = x + (f (hs.cellLeft x hx) - hs.cellLeft x hx) := by
  have hdisp := hs.transl_of_not_separated (hs.cellLeft x hx) x
    (hs.cellLeft_mem_Ico x hx) hx (hs.not_separated_cellLeft hx)
  linarith

/-- **The inverse of an exchange stays in the interval**: `e.symm` maps `[a, b)` into itself.  This
is what lets the images of the cells cover `[a, b)`. -/
theorem Equiv.IsIET.symm_mapsTo {a b : ℝ} {e : Equiv ℝ ℝ} {s : Finset ℝ}
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
noncomputable def IsCutSet.cellStarts (_hs : IsCutSet f a b s) : Fin s.card → ℝ :=
  fun i => ((Finset.orderIsoOfFin (s) rfl) i : ℝ)

/-- The enumeration takes values among the cell starts. -/
theorem IsCutSet.cellStarts_mem (hs : IsCutSet f a b s) (i : Fin s.card) : hs.cellStarts i ∈ s :=
  (Finset.orderIsoOfFin (s) rfl i).2

/-- The enumeration is strictly increasing. -/
theorem IsCutSet.cellStarts_strictMono (hs : IsCutSet f a b s) : StrictMono hs.cellStarts :=
  fun _ _ h => (Finset.orderIsoOfFin (s) rfl).strictMono h

/-- Every cell start lies in `[a, b)`. -/
theorem IsCutSet.cellStarts_mem_Ico
    (hs : IsCutSet f a b s) (i : Fin s.card) : hs.cellStarts i ∈ Set.Ico a b :=
  hs.cuts_mem _ (hs.cellStarts_mem i)

/-- The first cell starts at `a`. -/
theorem IsCutSet.cellStarts_zero (hs : IsCutSet f a b s) : hs.cellStarts ⟨0, hs.card_pos⟩ = a := by
  classical
  have : NeZero s.card := ⟨hs.card_pos.ne'⟩
  have hne : 0 < s.card := hs.card_pos
  have hall : ∀ x ∈ s, a ≤ x := fun x hx => (hs.cuts_mem x hx).1
  -- the index at which `a` is enumerated
  set iso := Finset.orderIsoOfFin s rfl with hiso
  set j : Fin s.card := iso.symm ⟨a, hs.a_mem⟩ with hj
  have hjval : hs.cellStarts j = a := by
    have h1 : iso j = ⟨a, hs.a_mem⟩ := iso.apply_symm_apply _
    change ((iso j : {x // x ∈ s}) : ℝ) = a
    rw [h1]
  have hj0 : j = ⟨0, hne⟩ := by
    refine le_antisymm ?_ (Fin.zero_le _)
    by_contra hcon
    rw [not_le] at hcon
    have hlt : (⟨0, hne⟩ : Fin s.card) < j := hcon
    have h1 : hs.cellStarts ⟨0, hne⟩ < hs.cellStarts j := hs.cellStarts_strictMono hlt
    have h2 : a ≤ hs.cellStarts ⟨0, hne⟩ := hall _ (hs.cellStarts_mem _)
    rw [hjval] at h1
    linarith
  rw [← hj0]
  exact hjval

/-- The position function: `cellStarts` continued by `b` past the last index. -/
noncomputable def IsCutSet.cellPos (hs : IsCutSet f a b s) (k : ℕ) : ℝ :=
  if h : k < s.card then hs.cellStarts ⟨k, h⟩ else b

/-- The length of the `i`-th cell. -/
noncomputable def IsCutSet.cellLen (hs : IsCutSet f a b s) (i : Fin s.card) : ℝ :=
  hs.cellPos (i.val + 1) - hs.cellPos i.val

/-- Below the last index the position function is the enumeration. -/
theorem IsCutSet.cellPos_of_lt (hs : IsCutSet f a b s) {k : ℕ} (hk : k < s.card) :
    hs.cellPos k = hs.cellStarts ⟨k, hk⟩ := by
  unfold IsCutSet.cellPos
  exact dif_pos hk

/-- Past the last index the position function is `b`. -/
theorem IsCutSet.cellPos_top (hs : IsCutSet f a b s) :
    hs.cellPos s.card = b := by
  unfold IsCutSet.cellPos
  exact dif_neg (by omega)

/-- **The lengths of the cells sum to `b - a`**: the cells tile `[a, b)`. -/
theorem IsCutSet.sum_cellLen (hs : IsCutSet f a b s) :
    ∑ i, hs.cellLen i = b - a := by
  have hne : 0 < s.card := by
    have : a ∈ s := hs.a_mem
    exact Finset.card_pos.mpr ⟨a, this⟩
  have hfun : ∀ i : Fin s.card,
      hs.cellLen i = (fun k => hs.cellPos k) (i.val + 1) - (fun k => hs.cellPos k) i.val :=
    fun i => rfl
  simp only [hfun]
  rw [Fin.sum_univ_eq_sum_range (fun k => hs.cellPos (k + 1) - hs.cellPos k) s.card]
  rw [Finset.sum_range_sub]
  rw [hs.cellPos_top, hs.cellPos_of_lt (k := 0) hne, hs.cellStarts_zero]

/-- Every cell start is the value of the enumeration at some index. -/
theorem IsCutSet.cellStarts_surj (hs : IsCutSet f a b s) {c : ℝ} (hc : c ∈ s) :
    ∃ j : Fin s.card, hs.cellStarts j = c :=
  ⟨(Finset.orderIsoOfFin (s) rfl).symm ⟨c, hc⟩, by simp [IsCutSet.cellStarts]⟩

/-- The enumeration is strictly increasing, in index form. -/
theorem IsCutSet.cellStarts_lt_iff (hs : IsCutSet f a b s) {i j : Fin s.card} :
    hs.cellStarts i < hs.cellStarts j ↔ i < j :=
  (Finset.orderIsoOfFin (s) rfl).lt_iff_lt

/-- The right end of a cell is the next cell start, or `b` at the last index. -/
theorem IsCutSet.cellPos_succ (hs : IsCutSet f a b s) (i : Fin s.card) :
    (∃ h : i.val + 1 < s.card,
      hs.cellPos (i.val + 1) = hs.cellStarts ⟨i.val + 1, h⟩)
    ∨ (i.val + 1 = s.card ∧ hs.cellPos (i.val + 1) = b) := by
  by_cases h : i.val + 1 < s.card
  · exact Or.inl ⟨h, hs.cellPos_of_lt h⟩
  · refine Or.inr ⟨by omega, ?_⟩
    unfold IsCutSet.cellPos
    rw [dif_neg h]

/-- A cell is nondegenerate. -/
theorem IsCutSet.cellStarts_lt_cellPos (hs : IsCutSet f a b s) (i : Fin s.card) :
    hs.cellStarts i < hs.cellPos (i.val + 1) := by
  rcases hs.cellPos_succ i with ⟨h, hh⟩ | ⟨h, hh⟩
  · rw [hh]
    exact hs.cellStarts_lt_iff.mpr (Fin.lt_def.mpr (by simp))
  · rw [hh]
    exact (hs.cellStarts_mem_Ico i).2

/-- The right end of a cell lies in `(a, b]`. -/
theorem IsCutSet.cellPos_le (hs : IsCutSet f a b s) (k : ℕ) : hs.cellPos k ≤ b := by
  by_cases h : k < s.card
  · rw [hs.cellPos_of_lt h]
    exact le_of_lt (hs.cellStarts_mem_Ico ⟨k, h⟩).2
  · unfold IsCutSet.cellPos
    rw [dif_neg h]

/-- The right end of a cell is at most the left end of any later cell. -/
theorem IsCutSet.cellPos_le_cellStarts (hs : IsCutSet f a b s) {i j : Fin s.card} (hij : i < j) :
    hs.cellPos (i.val + 1) ≤ hs.cellStarts j := by
  have hlt : i.val < j.val := hij
  rcases hs.cellPos_succ i with ⟨h, hh⟩ | ⟨h, hh⟩
  · rw [hh]
    exact hs.cellStarts_strictMono.monotone (Fin.le_def.mpr (by simpa using Nat.succ_le_of_lt hlt))
  · rw [hh]
    exfalso
    omega

/-- A point of the `i`-th cell has `cellStarts i` as the left end of its cell. -/
theorem IsCutSet.cellLeft_eq
    (hs : IsCutSet f a b s) {i : Fin s.card} {x : ℝ} (hxmem : x ∈ Set.Ico a b)
    (h1 : hs.cellStarts i ≤ x) (h2 : x < hs.cellPos (i.val + 1)) :
    hs.cellLeft x hxmem = hs.cellStarts i := by
  refine le_antisymm ?_ (hs.le_cellLeft hxmem (hs.cellStarts_mem i) h1)
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨j, hj⟩ := hs.cellStarts_surj (hs.cellLeft_mem x hxmem)
  have hij : i < j := hs.cellStarts_lt_iff.mp (by rw [hj]; exact hcon)
  have hle := hs.cellPos_le_cellStarts hij
  have hlt : hs.cellLeft x hxmem < hs.cellPos (i.val + 1) :=
    lt_of_le_of_lt (hs.cellLeft_le x hxmem) h2
  rw [← hj] at hlt
  linarith

/-- Two distinct cells have disjoint images. -/
theorem IsCutSet.image_cell_disjoint (hs : IsCutSet f a b s) (hinj : Function.Injective f)
    {i j : Fin s.card} (hij : i ≠ j) :
    Disjoint (f '' Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1)))
      (f '' Set.Ico (hs.cellStarts j) (hs.cellPos (j.val + 1))) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨x, hx, hxz⟩ := hz
  obtain ⟨x', hx', hx'z⟩ := hz'
  have hxx : x = x' := hinj (by rw [hxz, hx'z])
  subst hxx
  have hβ := hs.cellStarts_mem_Ico j
  have hxmem : x ∈ Set.Ico a b :=
    ⟨le_trans hβ.1 hx'.1, lt_of_lt_of_le hx'.2 (hs.cellPos_le (j.val + 1))⟩
  have h1 := hs.cellLeft_eq hxmem hx.1 hx.2
  have h2 := hs.cellLeft_eq hxmem hx'.1 hx'.2
  have hval : hs.cellStarts i = hs.cellStarts j := by rw [← h1, ← h2]
  exact hij ((Finset.orderIsoOfFin s rfl).injective (Subtype.ext hval))

/-- **`f` translates the whole cell of `β i`.** -/
theorem IsCutSet.map_of_mem_cell (hs : IsCutSet f a b s) {i : Fin s.card} {x : ℝ}
    (hx : x ∈ Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1))) :
    f x = x + (f (hs.cellStarts i) - hs.cellStarts i) := by
  have hβ := hs.cellStarts_mem_Ico i
  have hxmem : x ∈ Set.Ico a b :=
    ⟨le_trans hβ.1 hx.1, lt_of_lt_of_le hx.2 (hs.cellPos_le (i.val + 1))⟩
  rw [hs.map_eq_cell hxmem, hs.cellLeft_eq hxmem hx.1 hx.2]

/-- **The image of a cell is the interval** `[f β, f β + λ)`. -/
theorem IsCutSet.image_cell (hs : IsCutSet f a b s) (i : Fin s.card) :
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
    rw [hs.map_of_mem_cell hx]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · intro hy
    refine ⟨y - (f (hs.cellStarts i) - hs.cellStarts i), ⟨?_, ?_⟩, ?_⟩
    · linarith [hy.1]
    · linarith [hy.2]
    · rw [hs.map_of_mem_cell ⟨by linarith [hy.1], by linarith [hy.2]⟩]
      ring

/-- **No image interval crosses another**: if the image of the `j`-th cell starts left of the
image of the `i`-th, it ends at or before it. -/
theorem IsCutSet.image_cell_le (hs : IsCutSet f a b s) (hinj : Function.Injective f)
    {i j : Fin s.card} (hij : i ≠ j)
    (hlt' : f (hs.cellStarts j) < f (hs.cellStarts i)) :
    f (hs.cellStarts j) + hs.cellLen j ≤ f (hs.cellStarts i) := by
  by_contra hcon
  rw [not_le] at hcon
  have hmem : f (hs.cellStarts i) ∈ f '' Set.Ico (hs.cellStarts j) (hs.cellPos (j.val + 1)) := by
    rw [hs.image_cell j]
    exact ⟨le_of_lt hlt', hcon⟩
  obtain ⟨x, hx, hfx⟩ := hmem
  have hxi : x = hs.cellStarts i := hinj hfx
  subst hxi
  have hmem' : hs.cellStarts i ∈ Set.Ico a b := hs.cellStarts_mem_Ico i
  have h1 := hs.cellLeft_eq hmem' hx.1 hx.2
  have h2 : hs.cellLeft (hs.cellStarts i) hmem' = hs.cellStarts i :=
    le_antisymm (hs.cellLeft_le _ hmem') (hs.le_cellLeft hmem' (hs.cellStarts_mem i) le_rfl)
  have hval : hs.cellStarts j = hs.cellStarts i := by rw [← h1, h2]
  exact hij ((Finset.orderIsoOfFin s rfl).injective (Subtype.ext hval.symm))

/-- The lengths of the cells before the `i`-th sum to `β i - a`. -/
theorem IsCutSet.sum_cellLen_lt (hs : IsCutSet f a b s) (i : Fin s.card) :
    ∑ j ∈ Finset.univ.filter (fun j => j < i), hs.cellLen j = hs.cellStarts i - a := by
  classical
  have hne : 0 < s.card := hs.card_pos
  have hpos : ∀ j : Fin s.card, hs.cellLen j = hs.cellPos (j.val + 1) - hs.cellPos j.val
    := by
    intro j
    have h1 := hs.cellPos_of_lt j.isLt
    unfold IsCutSet.cellLen
    rw [h1]
  have hbij : ∑ j ∈ Finset.univ.filter (fun j : Fin s.card => j < i), hs.cellLen j
      = ∑ k ∈ Finset.range i.val, (hs.cellPos (k + 1) - hs.cellPos k) := by
    refine Finset.sum_bij (fun (j : Fin s.card) _ => j.val) ?_ ?_ ?_ ?_
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
  rw [hs.cellPos_of_lt i.isLt, hs.cellPos_of_lt (k := 0) hne, hs.cellStarts_zero]

/-- The left endpoints of the images of the cells: the images of the cell starts. -/
noncomputable def IsCutSet.imageStarts (_hs : IsCutSet f a b s) : Finset ℝ :=
  (s).image f

/-- Membership in the set of image starts. -/
theorem IsCutSet.mem_imageStarts (hs : IsCutSet f a b s) {y : ℝ} :
    y ∈ hs.imageStarts ↔ ∃ β ∈ s, f β = y :=
  Finset.mem_image

/-- There are as many image starts as cell starts, provided `f` is injective. -/
theorem IsCutSet.imageStarts_card (hs : IsCutSet f a b s) (hinj : Function.Injective f) :
    hs.imageStarts.card = s.card :=
  Finset.card_image_of_injective _ hinj

/-- The image starts lie in `[a, b)`. -/
theorem IsCutSet.imageStarts_subset (hs : IsCutSet f a b s) :
    ∀ y ∈ hs.imageStarts, y ∈ Set.Ico a b := by
  intro y hy
  obtain ⟨β, hβ, rfl⟩ := hs.mem_imageStarts.mp hy
  exact hs.mapsTo β (hs.cuts_mem β hβ)

/-- **The permutation of the cells**: the `i`-th cell goes to the position of its image among the
image starts. -/
noncomputable def IsCutSet.cellPerm (hs : IsCutSet f a b s) (hinj : Function.Injective f) :
    Equiv.Perm (Fin s.card) :=
  let iso₁ := Finset.orderIsoOfFin (s) rfl
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
      change iso₂.symm ⟨f (iso₁ (iso₁.symm ⟨β, hβ⟩)), _⟩ = j
      rw [iso₁.apply_symm_apply]
      have himg : (⟨f β, hs.mem_imageStarts.mpr ⟨β, hβ, rfl⟩⟩ : ↥hs.imageStarts) = iso₂ j :=
        Subtype.ext hfβ
      rw [himg, iso₂.symm_apply_apply]⟩

/-- `cellPerm` lands on the position of the image of the cell start. -/
theorem IsCutSet.cellPerm_val
    (hs : IsCutSet f a b s) (hinj : Function.Injective f) (i : Fin s.card) :
    (Finset.orderIsoOfFin hs.imageStarts (hs.imageStarts_card hinj)) (hs.cellPerm hinj i)
      = ⟨f (hs.cellStarts i),
          hs.mem_imageStarts.mpr ⟨hs.cellStarts i, hs.cellStarts_mem i, rfl⟩⟩ := by
  unfold IsCutSet.cellPerm
  exact (Finset.orderIsoOfFin hs.imageStarts (hs.imageStarts_card hinj)).apply_symm_apply _

/-- `π j < π i` exactly when the image of the `j`-th cell starts left of the image of the `i`-th. -/
theorem IsCutSet.cellPerm_lt_iff
    (hs : IsCutSet f a b s) (hinj : Function.Injective f) {i j : Fin s.card} :
    hs.cellPerm hinj j < hs.cellPerm hinj i ↔ f (hs.cellStarts j) < f (hs.cellStarts i) := by
  have key : ∀ k : Fin s.card,
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
        < (Finset.orderIsoOfFin hs.imageStarts (hs.imageStarts_card hinj)) (hs.cellPerm hinj i) :=
          by
      rw [key j, key i]
      exact h
    exact (Finset.orderIsoOfFin hs.imageStarts (hs.imageStarts_card hinj)).lt_iff_lt.mp h2


end CutSetData

/-- **The image intervals of the cells whose image starts left of `f (β i)` cover `[a, f (β
i))`.** -/
theorem IsCutSet.image_union {e : Equiv ℝ ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet (⇑e) a b s) (i : Fin s.card) :
    (⋃ j : {j : Fin s.card // hs.cellPerm e.injective j < hs.cellPerm e.injective i},
        ⇑e '' Set.Ico (hs.cellStarts j.1) (hs.cellPos (j.1.val + 1)))
      = Set.Ico a (⇑e (hs.cellStarts i)) := by
  have hβi := hs.cellStarts_mem_Ico i
  ext y
  constructor
  · intro hy
    obtain ⟨j, yimg⟩ := Set.mem_iUnion.mp hy
    obtain ⟨x, hx, rfl⟩ := yimg
    have hpos : ⇑e (hs.cellStarts j.1) < ⇑e (hs.cellStarts i) :=
      (hs.cellPerm_lt_iff e.injective).mp j.2
    have hne' : j.1 ≠ i := fun h => absurd (h ▸ j.2) (lt_irrefl _)
    have hle := hs.image_cell_le e.injective (i := i) (j := j.1) hne'.symm hpos
    have hmap := hs.map_of_mem_cell hx
    have hxj := hs.cellStarts_mem_Ico j.1
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
    obtain ⟨j, hj⟩ := hs.cellStarts_surj (hs.cellLeft_mem _ hx)
    have hmemx : e.symm y ∈ Set.Ico (hs.cellStarts j) (hs.cellPos (j.val + 1)) := by
      refine ⟨?_, ?_⟩
      · rw [hj]; exact hs.cellLeft_le _ hx
      · rcases hs.cellPos_succ j with ⟨h, hh⟩ | ⟨h, hh⟩
        · rw [hh]
          by_contra hcon
          rw [not_lt] at hcon
          have hle2 : hs.cellStarts ⟨j.val + 1, h⟩ ≤ hs.cellStarts j := by
            rw [hj]
            exact hs.le_cellLeft hx (hs.cellStarts_mem _) hcon
          have hlt2 : hs.cellStarts j < hs.cellStarts ⟨j.val + 1, h⟩ :=
            hs.cellStarts_lt_iff.mpr (Fin.lt_def.mpr (by simp))
          linarith
        · rw [hh]; exact hx.2
    have hpos : ⇑e (hs.cellStarts j) < ⇑e (hs.cellStarts i) := by
      have hmap := hs.map_of_mem_cell hmemx
      have h1 : ⇑e (hs.cellStarts j) ≤ y := by
        rw [hxeq] at hmap
        linarith [hmemx.1]
      linarith [h1, hy.1, hy.2]
    exact Set.mem_iUnion.mpr ⟨⟨j, (hs.cellPerm_lt_iff e.injective).mpr hpos⟩,
      ⟨e.symm y, hmemx, hxeq⟩⟩

/-- **The sum of the lengths of the cells whose images start left of `f (β i)` is `f (β i) -
a`.** -/
theorem IsCutSet.sum_cellLen_image {e : Equiv ℝ ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet (⇑e) a b s) (i : Fin s.card) :
    ∑ j ∈ Finset.univ.filter (fun j => hs.cellPerm e.injective j < hs.cellPerm e.injective i),
        hs.cellLen j = ⇑e (hs.cellStarts i) - a := by
  classical
  set F := Finset.univ.filter (fun j => hs.cellPerm e.injective j < hs.cellPerm e.injective i) with
    hF
  have hnn : ∀ j ∈ F, 0 ≤ hs.cellLen j := by
    intro j _
    have h1 := hs.cellPos_of_lt j.isLt
    have h2 := hs.cellStarts_lt_cellPos j
    unfold IsCutSet.cellLen
    rw [h1]
    linarith
  -- the intervals are pairwise disjoint
  have hdisj : (↑F : Set (Fin s.card)).PairwiseDisjoint
      (fun j => Set.Ico (⇑e (hs.cellStarts j)) (⇑e (hs.cellStarts j) + hs.cellLen j)) := by
    intro j _ k _ hjk
    have hd := hs.image_cell_disjoint e.injective hjk
    rwa [hs.image_cell j, hs.image_cell k] at hd
  -- their union is `[a, f (β i))`
  have hunion : (⋃ j ∈ F, Set.Ico (⇑e (hs.cellStarts j)) (⇑e (hs.cellStarts j) + hs.cellLen j))
      = Set.Ico a (⇑e (hs.cellStarts i)) := by
    have h := hs.image_union i
    rw [Set.iUnion_subtype] at h
    simp only [hs.image_cell, hF, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
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
    have := (hs.mapsTo _ (hs.cellStarts_mem_Ico i)).1
    linarith
  exact (ENNReal.ofReal_eq_ofReal_iff hsum hfin).mp hof

/-- **Tiling, cover half**: every `y ∈ [a, b)` lies in the image of the cell of `e.symm y`, and that
cell starts at or below `y` — the left end of its image is `e β ≤ y`. -/
theorem Equiv.IsIET.tiling {a b : ℝ} {e : Equiv ℝ ℝ} {s : Finset ℝ}
    (hs : IsCutSet (⇑e) a b s) {y : ℝ} (hy : y ∈ Set.Ico a b) :
    ∃ β ∈ s, β ≤ e.symm y ∧ ⇑e β ≤ y := by
  have hx : e.symm y ∈ Set.Ico a b := Equiv.IsIET.symm_mapsTo (e := e) hs hy
  refine ⟨hs.cellLeft (e.symm y) hx, hs.cellLeft_mem _ hx, hs.cellLeft_le _ hx, ?_⟩
  have hm := hs.map_eq_cell (f := ⇑e) hx
  rw [Equiv.apply_symm_apply] at hm
  linarith [hs.cellLeft_le (e.symm y) hx]

/-- **Tiling, disjointness half**: two cells with different left endpoints have disjoint images —
`e` is injective and translates each cell. -/
theorem Equiv.IsIET.tiling_disjoint {a b : ℝ} {e : Equiv ℝ ℝ} {s : Finset ℝ}
    (hs : IsCutSet (⇑e) a b s) {x x' : ℝ} (hx : x ∈ Set.Ico a b) (hx' : x' ∈ Set.Ico a b)
    (hne : hs.cellLeft x hx ≠ hs.cellLeft x' hx') : ⇑e x ≠ ⇑e x' := by
  intro hcon
  have hxx' : x = x' := e.injective hcon
  subst hxx'
  exact hne rfl
