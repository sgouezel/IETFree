/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.CutSet

/-!
The cells tile the interval, and an exchange preserves Lebesgue measure.

The cells of a cut set (see `IETFree.CutSet`) cover `[a, b)` and are disjoint, and an exchange
translates each of them; hence the images of the cells also tile `[a, b)`, and an exchange preserves
the Lebesgue measure of `[a, b)` (`Equiv.IsIET.measure_preimage`).  With that at hand the file
proves that an exchange is measurable, that it has finite preimages, and the local structure of a
piecewise translation: such a map is determined by its translations (`IsLocallyTranslationAt`,
`IsCutSet.transl_of_locally`), which is what makes a finer cut set again a cut set (`IsCutSet.comp`,
`IsCutSet.inter`).
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal
/-! ## The cells tile the interval, and an exchange preserves Lebesgue measure

The cells `[β i, β (i+1))` of the cut set tile `[a, b)`, `f` translates each of them, and the images
of the cells tile `[a, b)` as well.  Hence an exchange preserves the restricted Lebesgue measure:
  the
mass of `A` equals the sum of the masses of `A` on the image cells, and each of those is the mass of
the preimage on the corresponding cell.
-/

-- the data of one cut set, in scope for the API below (`hs` stays a binder of each declaration)
section CutSetData

variable {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}

/-- **A point of `[a, b)` lies in one of the cells.** -/
theorem IsCutSet.exists_mem_cell (hs : IsCutSet f a b s) {x : ℝ} (hx : x ∈ Set.Ico a b) :
    ∃ i : Fin s.card,
      x ∈ Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1)) := by
  classical
  obtain ⟨i, hi⟩ := hs.cellStarts_surj (hs.cellLeft_mem x hx)
  refine ⟨i, ?_, ?_⟩
  · rw [hi]
    exact hs.cellLeft_le x hx
  · by_contra hcon
    rw [not_lt] at hcon
    rcases hs.cellPos_succ i with ⟨h, hh⟩ | ⟨h, hh⟩
    · rw [hh] at hcon
      have hmem : hs.cellStarts ⟨i.val + 1, h⟩ ∈ s := hs.cellStarts_mem _
      have h1 : hs.cellStarts ⟨i.val + 1, h⟩ ≤ hs.cellLeft x hx :=
        hs.le_cellLeft hx hmem hcon
      rw [← hi] at h1
      have h2 : hs.cellStarts i < hs.cellStarts ⟨i.val + 1, h⟩ :=
        hs.cellStarts_lt_iff.mpr (Fin.lt_def.mpr (by simp))
      linarith
    · rw [hh] at hcon
      exact absurd hcon (not_le.mpr hx.2)

/-- **The cells tile `[a, b)`.** -/
theorem IsCutSet.cells_union (hs : IsCutSet f a b s) :
    (⋃ i : Fin s.card,
      Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1))) = Set.Ico a b := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨le_trans (hs.cellStarts_mem_Ico i).1 hi.1,
      lt_of_lt_of_le hi.2 (hs.cellPos_le _)⟩
  · intro hx
    obtain ⟨i, hi⟩ := hs.exists_mem_cell hx
    rw [Set.mem_iUnion]
    exact ⟨i, hi⟩

/-- **The cells of `[a, b)` are pairwise disjoint.** -/
theorem IsCutSet.cells_disjoint (hs : IsCutSet f a b s) {i j : Fin s.card} (hij : i ≠ j) :
    Disjoint (Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1)))
      (Set.Ico (hs.cellStarts j) (hs.cellPos (j.val + 1))) := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [Set.disjoint_left]
    intro x hx hy
    have hle := hs.cellPos_le_cellStarts h
    exact absurd (lt_of_lt_of_le hx.2 hle) (not_lt.mpr hy.1)
  · rw [Set.disjoint_left]
    intro x hx hy
    have hle := hs.cellPos_le_cellStarts h
    exact absurd (lt_of_lt_of_le hy.2 hle) (not_lt.mpr hx.1)

/-- **The images of the cells tile `[a, b)`.** -/
theorem Equiv.IsIET.image_cells_union {a b : ℝ} {e : Equiv ℝ ℝ} {s : Finset ℝ}
    (hs : IsCutSet (⇑e) a b s) :
    (⋃ i : Fin s.card,
      ⇑e '' Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1))) = Set.Ico a b := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨i, x, hx, rfl⟩ := hy
    exact hs.mapsTo _ ⟨le_trans (hs.cellStarts_mem_Ico i).1 hx.1,
      lt_of_lt_of_le hx.2 (hs.cellPos_le _)⟩
  · intro hy
    have hx : e.symm y ∈ Set.Ico a b := Equiv.IsIET.symm_mapsTo (e := e) hs hy
    obtain ⟨i, hi⟩ := hs.exists_mem_cell hx
    rw [Set.mem_iUnion]
    exact ⟨i, e.symm y, hi, by simp⟩

/-- Translating a set does not change its measure. -/
theorem volume_image_add (d : ℝ) (S : Set ℝ) :
    volume ((fun x : ℝ => x + d) '' S) = volume S := by
  have h : (fun x : ℝ => x + d) '' S = (fun x : ℝ => x + (-d)) ⁻¹' S := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [sub_eq_add_neg] using hy
    · intro hx
      exact ⟨x - d, by simpa [sub_eq_add_neg] using hx, by ring⟩
  rw [h, measure_preimage_add_right]

/-- For any function, the image of the preimage of `A` inside `C` is `A` intersected with the image
of `C`. -/
theorem image_preimage_inter (f : ℝ → ℝ) (A C : Set ℝ) :
    f '' (f ⁻¹' A ∩ C) = A ∩ f '' C := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxA, hxC⟩, rfl⟩
    exact ⟨hxA, ⟨x, hxC, rfl⟩⟩
  · rintro ⟨hyA, x, hxC, rfl⟩
    exact ⟨x, ⟨hyA, hxC⟩, rfl⟩

/-- **A measure is the sum of its masses on the pieces of a finite tiling.** -/
theorem volume_inter_eq_sum {n : ℕ} {C : Fin n → Set ℝ} {T : Set ℝ}
    (hcover : (⋃ i, C i) = T) (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    {S : Set ℝ} (hmeas : ∀ i, MeasurableSet (S ∩ C i)) :
    volume (S ∩ T) = ∑ i, volume (S ∩ C i) := by
  have h : S ∩ T = ⋃ i, S ∩ C i := by
    rw [← hcover, Set.inter_iUnion]
  rw [h, measure_iUnion (f := fun i => S ∩ C i)
    (fun i j hij => (hdisj i j hij).mono Set.inter_subset_right Set.inter_subset_right)
    hmeas, tsum_fintype]

/-- On a cell, `e` acts as a fixed translation. -/
theorem IsCutSet.preimage_inter_cell {e : Equiv ℝ ℝ} {a b : ℝ} {s : Finset ℝ}
    (hs : IsCutSet (⇑e) a b s) (i : Fin s.card) (A : Set ℝ) :
    ⇑e ⁻¹' A ∩ Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1))
      = (fun z : ℝ => z + (⇑e (hs.cellStarts i) - hs.cellStarts i)) ⁻¹' A
        ∩ Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1)) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hx, hc⟩
    rw [hs.map_of_mem_cell hc] at hx
    exact ⟨hx, hc⟩
  · rintro ⟨hx, hc⟩
    refine ⟨?_, hc⟩
    rw [hs.map_of_mem_cell hc]
    exact hx

/-- **The measure of the preimage of `A` on one cell.** -/
theorem IsCutSet.volume_preimage_cell {a b : ℝ} {e : Equiv ℝ ℝ} {s : Finset ℝ}
    (hs : IsCutSet (⇑e) a b s) (i : Fin s.card) (A : Set ℝ) :
    volume (⇑e ⁻¹' A ∩ Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1)))
      = volume (A ∩ ⇑e '' Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1))) := by
  set C := Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1)) with hC
  set d := ⇑e (hs.cellStarts i) - hs.cellStarts i with hd
  have hpre := hs.preimage_inter_cell i A
  have htrans : ⇑e '' (⇑e ⁻¹' A ∩ C) = (fun z : ℝ => z + d) '' (⇑e ⁻¹' A ∩ C) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hC] at hx
      exact ⟨x, by rw [hC]; exact hx,
        by rw [hd]; exact (hs.map_of_mem_cell hx.2).symm⟩
    · rintro ⟨x, hx, rfl⟩
      rw [hC] at hx
      exact ⟨x, by rw [hC]; exact hx, by rw [hd]; exact hs.map_of_mem_cell hx.2⟩
  have hCe : ⇑e '' C = (fun z : ℝ => z + d) '' C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hC] at hx
      exact ⟨x, hx, by rw [hd]; exact (hs.map_of_mem_cell hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      rw [hC] at hx
      exact ⟨x, hx, by rw [hd]; exact hs.map_of_mem_cell hx⟩
  calc volume (⇑e ⁻¹' A ∩ C)
      = volume ((fun z : ℝ => z + d) ⁻¹' A ∩ C) := by rw [hpre, hC]
    _ = volume ((fun z : ℝ => z + d) '' ((fun z : ℝ => z + d) ⁻¹' A ∩ C)) :=
        (volume_image_add d _).symm
    _ = volume (⇑e '' (⇑e ⁻¹' A ∩ C)) := by rw [hC, ← hpre, htrans]
    _ = volume (A ∩ ⇑e '' C) := by rw [image_preimage_inter]

/-- **An exchange preserves Lebesgue measure on its interval.** -/
theorem Equiv.IsIET.measure_preimage {a b : ℝ} {e : Equiv ℝ ℝ} {s : Finset ℝ}
    (hs : IsCutSet (⇑e) a b s) {A : Set ℝ} (hA : MeasurableSet A) :
    volume (⇑e ⁻¹' A ∩ Set.Ico a b) = volume (A ∩ Set.Ico a b) := by
  classical
  calc volume (⇑e ⁻¹' A ∩ Set.Ico a b)
      = ∑ i, volume (⇑e ⁻¹' A ∩ Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1))) := by
        refine volume_inter_eq_sum (hs.cells_union) (fun i j hij => hs.cells_disjoint hij)
          (fun i => ?_)
        rw [hs.preimage_inter_cell i A]
        exact (hA.preimage (by fun_prop : Measurable fun z : ℝ => z + _)).inter measurableSet_Ico
    _ = ∑ i, volume (A ∩ ⇑e '' Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1))) :=
        Finset.sum_congr rfl (fun i _ => hs.volume_preimage_cell i A)
    _ = volume (A ∩ Set.Ico a b) := by
        refine (volume_inter_eq_sum (Equiv.IsIET.image_cells_union hs)
          (fun i j hij => hs.image_cell_disjoint e.injective hij) (fun i => ?_)).symm
        rw [hs.image_cell]
        exact hA.inter measurableSet_Ico
/-! ## Measurability

An exchange is the identity outside `[a, b)` and a translation on each of its finitely many cells,
so it is measurable.
-/

/-- **`f` is `x +` the sum of the displacements of its cells** (each cell contributing an
indicator): this exhibits `f` as a finite sum of measurable functions. -/
theorem IsCutSet.eq_add_sum_indicator (hs : IsCutSet f a b s) (x : ℝ) :
    f x = x + ∑ i : Fin s.card,
      (Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1))).indicator
        (fun _ : ℝ => (f (hs.cellStarts i) - hs.cellStarts i)) x := by
  classical
  set F : Fin s.card → ℝ := fun j =>
    (Set.Ico (hs.cellStarts j) (hs.cellPos (j.val + 1))).indicator
      (fun _ : ℝ => (f (hs.cellStarts j) - hs.cellStarts j)) x with hF
  change f x = x + ∑ i, F i
  by_cases hx : x ∈ Set.Ico a b
  · obtain ⟨i, hi⟩ := hs.exists_mem_cell hx
    have hsum : ∑ j, F j = f (hs.cellStarts i) - hs.cellStarts i := by
      rw [Finset.sum_eq_single i]
      · rw [hF]
        exact Set.indicator_of_mem hi _
      · intro j _ hji
        rw [hF]
        refine Set.indicator_of_notMem ?_ _
        intro hxj
        exact Set.disjoint_left.mp (hs.cells_disjoint hji) hxj hi
      · intro hnot
        exact absurd (Finset.mem_univ i) hnot
    rw [hsum, hs.map_of_mem_cell hi]
  · have hx2 : ∀ i : Fin s.card,
        x ∉ Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1)) := by
      intro i hxi
      exact hx ((hs.cells_union).symm ▸ Set.mem_iUnion.mpr ⟨i, hxi⟩)
    have hself : f x = x := by
      rcases not_and_or.mp hx with h | h
      · exact hs.apply_eq_self_of_lt x (not_le.mp h)
      · exact hs.apply_eq_self_of_le x (not_lt.mp h)
    have hzero : ∑ j, F j = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [hF]
      exact Set.indicator_of_notMem (hx2 j) _
    rw [hself, hzero, add_zero]

/-- **An exchange is measurable**: it is the identity outside `[a, b)` and a translation on each of
its finitely many cells. -/
theorem IsCutSet.measurable (hs : IsCutSet f a b s) :
    Measurable f := by
  have hfun : f = fun x => x + ∑ i : Fin s.card,
      (Set.Ico (hs.cellStarts i) (hs.cellPos (i.val + 1))).indicator
        (fun _ : ℝ => (f (hs.cellStarts i) - hs.cellStarts i)) x := by
    funext x
    exact hs.eq_add_sum_indicator x
  rw [hfun]
  refine Measurable.add measurable_id (Finset.measurable_sum _ (fun i _ => ?_))
  exact measurable_const.indicator measurableSet_Ico

/-- **The preimage of a finite set under an exchange is finite**: on each of the finitely many
cells `f` is a translation, so each cut of `t` has at most one preimage per cell. -/
theorem IsCutSet.finite_preimage (hs : IsCutSet f a b s)
    (t : Finset ℝ) : (f ⁻¹' (t : Set ℝ)).Finite := by
  classical
  refine Set.Finite.subset (t.finite_toSet.union
    ((t ×ˢ s).image (fun p : ℝ × ℝ => p.1 - (f p.2 - p.2))).finite_toSet) ?_
  intro x hx
  simp only [Set.mem_preimage, Set.mem_union, Finset.mem_coe] at hx ⊢
  by_cases hxa : x < a
  · exact Or.inl (by rw [hs.apply_eq_self_of_lt x hxa] at hx; exact hx)
  rcases lt_or_ge x b with hxb | hxb
  · right
    have hxab : x ∈ Set.Ico a b := ⟨not_lt.mp hxa, hxb⟩
    have hβmem : hs.cellLeft x hxab ∈ s := hs.cellLeft_mem x hxab
    have hdisp : f x - x = f (hs.cellLeft x hxab) - hs.cellLeft x hxab :=
      hs.transl_of_not_separated (hs.cellLeft x hxab) x (hs.cellLeft_mem_Ico x hxab) hxab
        (hs.not_separated_cellLeft hxab)
    refine Finset.mem_image.mpr
      ⟨(f x, hs.cellLeft x hxab), Finset.mem_product.mpr ⟨hx, hβmem⟩, ?_⟩
    change f x - (f (hs.cellLeft x hxab) - hs.cellLeft x hxab) = x
    linarith
  · exact Or.inl (by rw [hs.apply_eq_self_of_le x hxb] at hx; exact hx)

/-- The preimage of a finite set, as a finset, for an exchange. -/
noncomputable def IsCutSet.preimage (hs : IsCutSet f a b s) (t : Finset ℝ) : Finset ℝ :=
  (hs.finite_preimage t).toFinset

/-- Membership in the set of preimages. -/
theorem IsCutSet.mem_preimage (hs : IsCutSet f a b s)
    {t : Finset ℝ} {p : ℝ} : p ∈ hs.preimage t ↔ f p ∈ t := by
  unfold IsCutSet.preimage
  rw [Set.Finite.mem_toFinset]
  exact Iff.rfl

/-- The cuts of the preimage set lie in `[a, b)`. -/
theorem IsCutSet.preimage_subset (hs : IsCutSet f a b s)
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
theorem IsCutSet.locallyTranslationAt_of_not_mem
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
    intro hsep
    rcases le_total z c with h | h
    · obtain ⟨u, hu, h1, h2⟩ := hsep.exists_of_le h
      have huc : u ≠ c := by rintro rfl; exact absurd hu hcs
      have h3 : |u - c| ≤ |z - c| := by
        rw [abs_of_nonpos (by linarith : u - c ≤ 0),
          abs_of_nonpos (by linarith : z - c ≤ 0)]
        linarith
      linarith [hδ u hu huc, hzc]
    · obtain ⟨u, hu, h1, h2⟩ := hsep.symm.exists_of_le h
      have huc : u ≠ c := by rintro rfl; exact absurd hu hcs
      have h3 : |u - c| ≤ |z - c| := by
        rw [abs_of_nonneg (by linarith : 0 ≤ u - c),
          abs_of_nonneg (by linarith : 0 ≤ z - c)]
        linarith
      linarith [hδ u hu huc, hzc]
  have hdisp := hs.transl_of_not_separated z c hz hc hns
  linarith

/-- **Composition of cut sets**: the cuts of `g ∘ f` are those of `f` together with the preimages
under `f` of the cuts of `g` — finite because `f` is finite-to-one. -/
theorem IsCutSet.comp {s t : Finset ℝ} {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IsCutSet f a b s) (hg : IsCutSet g a b t) :
    IsCutSet (g ∘ f) a b (s ∪ hf.preimage t) := by
  classical
  have ht_sub : ∀ c ∈ t, c ∈ Set.Ico a b := hg.cuts_mem
  refine ⟨?_, ?_, ?_, Finset.mem_union_left _ hf.a_mem, ?_, ?_⟩
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
      intro hsep
      rcases le_total x y with hxy | hyx
      · have hfxle : f x ≤ f y := by linarith
        obtain ⟨c, hc, hc1, hc2⟩ := hsep.exists_of_le hfxle
        set p : ℝ := c - (f y - y) with hp
        have hpx : x < p := by rw [hp]; linarith
        have hpy : p ≤ y := by rw [hp]; linarith
        have hpdom : p ∈ Set.Ico a b :=
          ⟨le_of_lt (lt_of_le_of_lt hx.1 hpx), lt_of_le_of_lt hpy hy.2⟩
        have hns_sp : ¬ Separated s x p := by
          intro hsep2
          obtain ⟨d, hd, hd1, hd2⟩ := hsep2.exists_of_le hpx.le
          exact hns_s (Separated.of_lt_le hd hd1 (le_trans hd2 hpy))
        have hfp : f p - p = f x - x := hf.transl_of_not_separated x p hx hpdom hns_sp
        have hfpc : f p = c := by rw [hp]; linarith
        have hpmem : p ∈ s ∪ hf.preimage t :=
          Finset.mem_union_right _ (hf.mem_preimage.mpr (by rw [hfpc]; exact hc))
        exact hns (Separated.of_lt_le hpmem hpx hpy)
      · have hfyle : f y ≤ f x := by linarith
        obtain ⟨c, hc, hc1, hc2⟩ := hsep.symm.exists_of_le hfyle
        set p : ℝ := c - (f x - x) with hp
        have hpy : y < p := by rw [hp]; linarith
        have hpx : p ≤ x := by rw [hp]; linarith
        have hpdom : p ∈ Set.Ico a b :=
          ⟨le_of_lt (lt_of_le_of_lt hy.1 hpy), lt_of_le_of_lt hpx hx.2⟩
        have hns_sp : ¬ Separated s y p := by
          intro hsep2
          obtain ⟨d, hd, hd1, hd2⟩ := hsep2.exists_of_le hpy.le
          exact hns_s (Separated.of_lt_le hd hd1 (le_trans hd2 hpx)).symm
        have hfp : f p - p = f y - y := hf.transl_of_not_separated y p hy hpdom hns_sp
        have hfpc : f p = c := by rw [hp]; linarith
        have hpmem : p ∈ s ∪ hf.preimage t :=
          Finset.mem_union_right _ (hf.mem_preimage.mpr (by rw [hfpc]; exact hc))
        exact hns (Separated.of_lt_le hpmem hpy hpx).symm
    have hgd : g (f y) - f y = g (f x) - f x :=
      hg.transl_of_not_separated (f x) (f y) (hf.mapsTo x hx) (hf.mapsTo y hy) hns_t
    change g (f y) - y = g (f x) - x
    linarith

/-- **The displacement is constant across non-jumps.**  If every cut of `s` strictly between `x`
and `y` is a point where `f` is locally a translation, then the displacement of `f` at `x` and at
`y` agree. -/
private lemma transl_of_locally_le (hs : IsCutSet f a b s) {x y : ℝ} (hxy : x ≤ y)
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
          have hcint' : x < c ∧ c ≤ y := (mem_Ioc_min_max x y hxy).mp hcint
          exact hne ⟨c, by
            simp only [Finset.mem_filter]
            exact ⟨hcs, hcint'⟩⟩
        exact hs.transl_of_not_separated x y hx hy hnotsep
  exact main ((s.filter (fun c => x < c ∧ c ≤ y)).card) x y hxy hx hy h rfl

/-- The displacement of `f` is constant across non-jumps. -/
theorem IsCutSet.transl_of_locally (hs : IsCutSet f a b s)
    {x y : ℝ} (hx : x ∈ Set.Ico a b) (hy : y ∈ Set.Ico a b)
    (h : ∀ c ∈ s, min x y < c → c ≤ max x y → IsLocallyTranslationAt f a b c) :
    f y - y = f x - x := by
  rcases le_total x y with hxy | hyx
  · exact transl_of_locally_le hs hxy hx hy (by
      intro c hcs hxc hcy
      obtain ⟨h1, h2⟩ := (mem_Ioc_min_max x y hxy).mpr ⟨hxc, hcy⟩
      exact h c hcs h1 h2)
  · have hswap : f x - x = f y - y :=
      transl_of_locally_le hs hyx hy hx (by
        intro c hcs hyc hcx
        obtain ⟨h1, h2⟩ := (mem_Ioc_min_max y x hyx).mpr ⟨hyc, hcx⟩
        exact h c hcs (by simpa only [min_comm] using h1) (by simpa only [max_comm] using h2))
    exact hswap.symm

/-- **The intersection of two cut sets is a cut set.**  Every true discontinuity lies in both
(`IsCutSet.locallyTranslationAt_of_not_mem`), so a piece of `s ∩ t` contains no jump of `f` and the
displacement is constant on it. -/
theorem IsCutSet.inter {s t : Finset ℝ} {f : ℝ → ℝ} {a b : ℝ}
    (hs : IsCutSet f a b s) (ht : IsCutSet f a b t) : IsCutSet f a b (s ∩ t) := by
  refine ⟨hs.apply_eq_self_of_lt, hs.apply_eq_self_of_le, hs.mapsTo,
    Finset.mem_inter.mpr ⟨hs.a_mem, ht.a_mem⟩, ?_, ?_⟩
  · intro c hc
    exact hs.cuts_mem c (Finset.mem_inter.mp hc).1
  · intro x y hx hy hns
    refine hs.transl_of_locally hx hy ?_
    intro c hc h1 h2
    by_contra hj
    have hcab : c ∈ Set.Ico a b :=
      ⟨le_of_lt (lt_of_le_of_lt (le_min hx.1 hy.1) h1),
        lt_of_le_of_lt h2 (lt_of_lt_of_le (max_lt hx.2 hy.2) le_rfl)⟩
    have hct : c ∈ t := by
      by_contra hmem
      exact hj (ht.locallyTranslationAt_of_not_mem (s := t) hcab hmem)
    exact hns ⟨c, Finset.mem_inter.mpr ⟨hc, hct⟩, ⟨h1, h2⟩⟩


end CutSetData
