/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.LengthMap

/-!
The transfer of almost-sure statements to a rescaled sub-interval.

Lemma 3.4 applies Theorem 2.6 to the exchange `g ∘ f` **restricted to a block and rescaled to
`[0, 1)`**, and then transports the word back.  The measure-theoretic content of the first step is
that rescaling a length vector to total mass `1` does not create measure from nothing: a null set of
rescaled length vectors pulls back to a null set of length vectors.  Since the length vector of
`g ∘ f` is almost surely absolutely continuous with respect to Lebesgue measure (Lemma 3.1,
`BlockData.compLen_absolutelyContinuousAt`), an almost-sure statement about the *rescaled* length
vector of a sub-interval is an almost-sure statement about the parameters.

The file proves the two ingredients, both free of any interval-exchange structure:

* `volume_normalize_preimage_null`: the normalisation `y ↦ y / ∑ y` pulls null sets back to null
  sets on the positive orthant — the preimage of a null set is the cone over it, i.e. the image
  of a null set under a polynomial map, and a differentiable map sends null sets to null sets
  (`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`);
* `absolutelyContinuous_map_rescaleSub`: the same for the map `rescaleSub` sending the free
  coordinates of `simplexRegion n` to the free coordinates of the rescaled sub-interval made of the
  cells `k, …, k + r - 1`: split the coordinates into the block and the rest (`splitMapLast`, an
  injective affine map, `splitMapLast_injective`), then normalise.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-- **Rescaling a length vector to total mass `1` preserves null sets.**  On the positive orthant
(where the total mass is positive) the normalisation `y ↦ y / ∑ y` pulls null sets back to null
sets: the preimage is the cone over the null set, which is the image of a null set under the
polynomial map `(z, s) ↦ s • (z, 1 - ∑ z)`. -/
theorem volume_normalize_preimage_null {r : ℕ} {Z : Set (Fin r → ℝ)} (hZ : volume Z = 0) :
    volume {t : Fin (r + 1) → ℝ |
      (∀ i, 0 < t i) ∧ (fun i : Fin r => t i.castSucc / ∑ j, t j) ∈ Z} = 0 := by
  classical
  obtain ⟨Z', hZsub, hZ'meas, hZ'⟩ := exists_measurable_superset_of_null hZ
  -- the parameters of the cone: the `r` free coordinates lie in `Z'`
  set A : Set (Fin (r + 1) → ℝ) := {t | (fun i : Fin r => t i.castSucc) ∈ Z'} with hAdef
  have hA : volume A = 0 := by
    have hpres := volume_preserving_piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) (Fin.last r)
    have hpre : ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) (Fin.last r)) ⁻¹'
        (Set.univ ×ˢ Z') = A := by
      ext t
      have h2 : ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) (Fin.last r)) t).2
          = fun i : Fin r => t i.castSucc := by
        rw [show ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) (Fin.last r)) t).2
            = fun i : Fin r => t ((Fin.last r).succAbove i) from rfl, Fin.succAbove_last]
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, hAdef, Set.mem_ofPred_eq,
        h2]
    have hmap : volume (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ)
        (Fin.last r)) ⁻¹' (Set.univ ×ˢ Z'))
        = (volume.prod volume : Measure (ℝ × (Fin r → ℝ))) (Set.univ ×ˢ Z') := by
      rw [← Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ.prod hZ'meas),
        hpres.map_eq]
      rfl
    rw [← hpre, hmap, Measure.prod_prod, hZ', mul_zero]
  -- the polynomial map that parametrises the cone
  set G : (Fin (r + 1) → ℝ) → (Fin (r + 1) → ℝ) := fun x j =>
    x (Fin.last r) * if j.val = r then (1 - ∑ i : Fin r, x i.castSucc) else x j with hGdef
  have hGdiff : Differentiable ℝ G := by
    refine differentiable_pi.mpr (fun j => ?_)
    by_cases hj : j.val = r
    · have heq : (fun x : Fin (r + 1) → ℝ => G x j)
          = fun x => x (Fin.last r) * (1 - ∑ i : Fin r, x i.castSucc) := by
        funext x
        simp only [hGdef, if_pos hj]
      rw [heq]
      fun_prop
    · have heq : (fun x : Fin (r + 1) → ℝ => G x j) = fun x => x (Fin.last r) * x j := by
        funext x
        simp only [hGdef, if_neg hj]
      rw [heq]
      fun_prop
  have hGA : volume (G '' A) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (μ := volume)
      hGdiff.differentiableOn hA
  refine measure_mono_null (fun t ht => ?_) hGA
  obtain ⟨hpos, htZ⟩ := ht
  set S : ℝ := ∑ j, t j with hSdef
  have hSpos : 0 < S := Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty
  have hSne : S ≠ 0 := hSpos.ne'
  set z : Fin r → ℝ := fun i => t i.castSucc / S with hzdef
  have hz : z ∈ Z' := hZsub htZ
  have hsum : (∑ i : Fin r, t i.castSucc) = S - t (Fin.last r) := by
    rw [hSdef, Fin.sum_univ_castSucc]; ring
  have hsumz : (∑ i : Fin r, z i) = (S - t (Fin.last r)) / S := by
    rw [hzdef]
    simp only [← Finset.sum_div]
    rw [hsum]
  have hlast : S * (1 - ∑ i : Fin r, z i) = t (Fin.last r) := by
    rw [hsumz]
    field_simp
    ring
  have hcast : ∀ i : Fin r, S * z i = t i.castSucc := by
    intro i
    rw [hzdef]
    field_simp
  refine ⟨Fin.snoc (α := fun _ : Fin (r + 1) => ℝ) z S, ?_, ?_⟩
  · have hcast' : (Fin.snoc z S ∘ Fin.castSucc : Fin r → ℝ) = z := by
      funext i
      simp [Fin.snoc_castSucc]
    change (Fin.snoc z S ∘ Fin.castSucc : Fin r → ℝ) ∈ Z'
    rwa [hcast']
  · funext j
    by_cases hj : j.val = r
    · have hjlast : j = Fin.last r := Fin.ext (by simp only [Fin.val_last]; omega)
      subst hjlast
      have hx : (Fin.snoc (α := fun _ : Fin (r + 1) => ℝ) z S) (Fin.last r) = S :=
        Fin.snoc_last ..
      have hs : (∑ i : Fin r, (Fin.snoc (α := fun _ : Fin (r + 1) => ℝ) z S) i.castSucc)
          = ∑ i : Fin r, z i := by
        simp only [Fin.snoc_castSucc]
      simp only [hGdef, Fin.val_last, hx, hs]
      exact hlast
    · obtain ⟨i, hi⟩ : ∃ i : Fin r, i.castSucc = j :=
        ⟨⟨j.val, by have h1 := j.isLt; have h2 : j.val ≠ r := hj; omega⟩,
          Fin.ext (by simp only [Fin.val_castSucc])⟩
      subst hi
      have hx : (Fin.snoc (α := fun _ : Fin (r + 1) => ℝ) z S) (Fin.last r) = S :=
        Fin.snoc_last ..
      have hx2 : (Fin.snoc (α := fun _ : Fin (r + 1) => ℝ) z S) (i.castSucc) = z i :=
        Fin.snoc_castSucc ..
      have hj' : ¬ (i.castSucc).val = r := by simp only [Fin.val_castSucc]; omega
      simp only [hGdef, hj', if_false, hx, hx2]
      exact hcast i
/-- The length of the `m`-th cell of the simplex point with free coordinates `x`. -/
noncomputable def cellLen {n : ℕ} (x : Fin (n - 1) → ℝ) (m : ℕ) : ℝ :=
  if h : m < n - 1 then x ⟨m, h⟩ else 1 - ∑ j, x j

/-- The cell lengths of the block `k, …, k + r - 1`, of which there are `r`. -/
noncomputable def blockLen {n : ℕ} (k r : ℕ) (x : Fin (n - 1) → ℝ) : Fin r → ℝ :=
  fun i => cellLen x (k + i)

/-- **The free coordinates of the rescaled length vector of a block of cells.**  The block
`k, …, k + r - 1` has `r` cells; its length vector rescales to the simplex `Δ_r`, whose free
coordinates are the first `r - 1` normalised lengths.  This is the map `F` of Lemma 3.4: rescaling a
sub-interval to `[0, 1)`. -/
noncomputable def rescaleSub {n : ℕ} (k r : ℕ) (x : Fin (n - 1) → ℝ) : Fin (r - 1) → ℝ :=
  fun i => blockLen k r x ⟨i.val, by have := i.isLt; omega⟩ / ∑ j, blockLen k r x j

variable {m k r : ℕ}

/-- The enumeration of `Fin m` by the `r` indices of the block `k, …, k + r - 1` followed by the
`m - r` indices outside it. -/
def eIdx (hk : k + r ≤ m) : Fin r ⊕ Fin (m - r) → Fin m
  | Sum.inl i => ⟨k + i.val, by omega⟩
  | Sum.inr j => if h : j.val < k then ⟨j.val, by omega⟩ else ⟨j.val + r, by omega⟩

theorem eIdx_injective (hk : k + r ≤ m) : Function.Injective (eIdx hk) := by
  rintro (i | j) (i' | j') h
  · simp only [eIdx] at h
    have hv : k + i.val = k + i'.val := congrArg Fin.val h
    exact congrArg Sum.inl (Fin.ext (by omega))
  · by_cases hj : j'.val < k
    · simp only [eIdx, dif_pos hj] at h
      exfalso
      have hv := congrArg (Fin.val : Fin m → ℕ) h
      simp only at hv
      omega
    · simp only [eIdx, dif_neg hj] at h
      exfalso
      have hv := congrArg (Fin.val : Fin m → ℕ) h
      simp only at hv
      have hi := i.isLt
      omega
  · by_cases hj : j.val < k
    · simp only [eIdx, dif_pos hj] at h
      exfalso
      have hv := congrArg Fin.val h
      simp only at hv
      omega
    · simp only [eIdx, dif_neg hj] at h
      exfalso
      have hv := congrArg Fin.val h
      simp only at hv
      have hi := i'.isLt
      omega
  · by_cases hj : j.val < k <;> by_cases hj' : j'.val < k
    · simp only [eIdx, dif_pos hj, dif_pos hj'] at h
      have hv := congrArg (Fin.val : Fin m → ℕ) h
      simp only at hv
      exact congrArg Sum.inr (Fin.ext (by omega))
    · simp only [eIdx, dif_pos hj, dif_neg hj'] at h
      exfalso
      have hv := congrArg (Fin.val : Fin m → ℕ) h
      simp only at hv
      omega
    · simp only [eIdx, dif_neg hj, dif_pos hj'] at h
      exfalso
      have hv := congrArg (Fin.val : Fin m → ℕ) h
      simp only at hv
      omega
    · simp only [eIdx, dif_neg hj, dif_neg hj'] at h
      have hv := congrArg (Fin.val : Fin m → ℕ) h
      simp only at hv
      exact congrArg Sum.inr (Fin.ext (by omega))

theorem eIdx_surjective (hk : k + r ≤ m) : Function.Surjective (eIdx hk) := by
  have hb : Function.Bijective (eIdx hk) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨eIdx_injective hk, ?_⟩
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  exact hb.2

/-- **Injectivity of the linear part of `Φ` in the generic case**: when the block does not contain
the last cell, its `r` cell lengths together with the `n - 1 - r` free coordinates outside the block
determine the parameters.  The other case (the block containing the last cell) has its own
`eIdx`-type enumeration, where the block vector determines the *sum* `∑_{i<k} x i` rather than the
individual coordinates below it. -/
theorem injective_split {n k r : ℕ} (hk : k + r ≤ n - 1) :
    Function.Injective (fun v : Fin (n - 1) → ℝ =>
      ((fun i : Fin r => v ⟨k + i.val, by omega⟩),
        (fun j : Fin (n - 1 - r) =>
          if h : j.val < k then v ⟨j.val, by omega⟩ else v ⟨j.val + r, by omega⟩))) := by
  intro v w h
  have h1 : ∀ i : Fin r, v ⟨k + i.val, by omega⟩ = w ⟨k + i.val, by omega⟩ :=
    fun i => congrArg (fun p => p.1 i) h
  have h2 : ∀ j : Fin (n - 1 - r),
      (if h : j.val < k then v ⟨j.val, by omega⟩ else v ⟨j.val + r, by omega⟩)
        = (if h : j.val < k then w ⟨j.val, by omega⟩ else w ⟨j.val + r, by omega⟩) :=
    fun j => congrArg (fun p => p.2 j) h
  funext t
  obtain ⟨p, hp⟩ := eIdx_surjective (m := n - 1) (k := k) (r := r) hk t
  rw [← hp]
  rcases p with i | j
  · exact h1 i
  · by_cases hj : j.val < k
    · simpa only [eIdx, dif_pos hj] using h2 j
    · simpa only [eIdx, dif_neg hj] using h2 j

theorem cellLen_of_lt {n m : ℕ} (x : Fin (n - 1) → ℝ) (h : m < n - 1) :
    cellLen x m = x ⟨m, h⟩ := by
  simp only [cellLen, dif_pos h]

theorem cellLen_of_not_lt {n m : ℕ} (x : Fin (n - 1) → ℝ) (h : ¬ m < n - 1) :
    cellLen x m = 1 - ∑ j, x j := by
  simp only [cellLen, dif_neg h]

theorem blockLen_of_lt {n k r : ℕ} (x : Fin (n - 1) → ℝ) (i : Fin r) (h : k + i.val < n - 1) :
    blockLen k r x i = x ⟨k + i.val, h⟩ := by
  simp only [blockLen, cellLen_of_lt x h]

theorem blockLen_of_not_lt {n k r : ℕ} (x : Fin (n - 1) → ℝ) (i : Fin r)
    (h : ¬ k + i.val < n - 1) : blockLen k r x i = 1 - ∑ j, x j := by
  simp only [blockLen, cellLen_of_not_lt x h]

/-- In the case where the block does not contain the last cell, its lengths are free
coordinates. -/
theorem blockLen_eq_of_le {n k r : ℕ} (hk : k + r ≤ n - 1) (x : Fin (n - 1) → ℝ) :
    blockLen k r x = fun i : Fin r => x ⟨k + i.val, by omega⟩ := by
  funext i
  exact blockLen_of_lt x i (by omega)

/-- The lengths of all the cells of a point of the open simplex add up to `1`. -/
theorem sum_cellLen {m : ℕ} (x : Fin m → ℝ) :
    (∑ i : Fin (m + 1), cellLen (n := m + 1) x i) = 1 := by
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ i : Fin m, cellLen (n := m + 1) x i.castSucc = x i := by
    intro i
    rw [cellLen, dif_pos (by simp)]
    exact congrArg x (Fin.ext rfl)
  have h2 : cellLen (n := m + 1) x (Fin.last m) = 1 - ∑ j, x j := by
    rw [cellLen, dif_neg (by rw [Fin.val_last]; omega)]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => h1 i), h2]
  ring

/-- The matching-dimension split in the case where the block `k, …, k + r - 1` does not contain
the last cell: the `r` cell lengths of the block together with the `n - 1 - r` free coordinates
outside it. -/
noncomputable def splitMap {n k r : ℕ} (hk : k + r ≤ n - 1) :
    (Fin (n - 1) → ℝ) →ᵃ[ℝ] ((Fin r → ℝ) × (Fin (n - 1 - r) → ℝ)) :=
  ((LinearMap.pi fun i : Fin r => LinearMap.proj (R := ℝ) ⟨k + i.val, by omega⟩).prod
    (LinearMap.pi fun j : Fin (n - 1 - r) =>
      if h : j.val < k then LinearMap.proj (R := ℝ) ⟨j.val, by omega⟩
      else LinearMap.proj (R := ℝ) ⟨j.val + r, by omega⟩)).toAffineMap

theorem splitMap_apply {n k r : ℕ} (hk : k + r ≤ n - 1) (x : Fin (n - 1) → ℝ) :
    splitMap hk x = (blockLen k r x, fun j : Fin (n - 1 - r) =>
      if h : j.val < k then x ⟨j.val, by omega⟩ else x ⟨j.val + r, by omega⟩) := by
  rw [splitMap, LinearMap.coe_toAffineMap, LinearMap.prod_apply, Function.prod, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · funext i
    rw [LinearMap.pi_apply, blockLen_of_lt x i (by omega)]
    rfl
  · funext j
    rw [LinearMap.pi_apply]
    by_cases h : j.val < k
    · rw [dif_pos h, dif_pos h]
      rfl
    · rw [dif_neg h, dif_neg h]
      rfl

theorem splitMap_injective {n k r : ℕ} (hk : k + r ≤ n - 1) :
    Function.Injective (splitMap (k := k) (r := r) hk).linear := by
  have hA : ∀ x : Fin (n - 1) → ℝ,
      splitMap (k := k) (r := r) hk x = (splitMap (k := k) (r := r) hk).linear x
        + splitMap (k := k) (r := r) hk 0 := by
    intro x
    have h := AffineMap.map_vadd (splitMap (k := k) (r := r) hk) (0 : Fin (n - 1) → ℝ) x
    rw [vadd_eq_add, add_zero] at h
    simpa using h
  have hF : (fun x : Fin (n - 1) → ℝ =>
      ((fun i : Fin r => x ⟨k + i.val, by omega⟩),
        fun j : Fin (n - 1 - r) =>
          if h : j.val < k then x ⟨j.val, by omega⟩ else x ⟨j.val + r, by omega⟩)) =
      (fun x : Fin (n - 1) → ℝ => (blockLen k r x, fun j : Fin (n - 1 - r) =>
        if h : j.val < k then x ⟨j.val, by omega⟩ else x ⟨j.val + r, by omega⟩)) := by
    funext x
    rw [blockLen_eq_of_le hk x]
  have hfun : Function.Injective (fun x : Fin (n - 1) → ℝ => (blockLen k r x,
      fun j : Fin (n - 1 - r) =>
        if h : j.val < k then x ⟨j.val, by omega⟩ else x ⟨j.val + r, by omega⟩)) := by
    rw [← hF]
    exact injective_split hk
  intro v w hvw
  refine hfun ?_
  beta_reduce
  rw [← splitMap_apply hk v, ← splitMap_apply hk w]
  rw [hA v, hA w, hvw]

/-- The last cell length `1 - ∑ x` of a length vector, as an affine function of the free
coordinates. -/
noncomputable def lastAffine {n : ℕ} : (Fin (n - 1) → ℝ) →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ (Fin (n - 1) → ℝ) 1
    - ∑ j : Fin (n - 1), (LinearMap.proj (R := ℝ) j).toAffineMap

theorem lastAffine_apply {n : ℕ} (x : Fin (n - 1) → ℝ) : lastAffine x = 1 - ∑ j, x j := by
  rw [lastAffine, AffineMap.coe_sub, Pi.sub_apply, AffineMap.const_apply, AffineMap.sum_apply]
  simp

/-- The matching-dimension split in the case where the block `k, …, k + r - 1` contains the last
cell: the `r` cell lengths of the block (the last one being `1 - ∑`) together with the free
coordinates `x 0, …, x (k - 2)` below the block. -/
noncomputable def splitMapLast {n k r : ℕ} :
    (Fin (n - 1) → ℝ) →ᵃ[ℝ] ((Fin r → ℝ) × (Fin (n - 1 - r) → ℝ)) :=
  (AffineMap.pi fun i : Fin r =>
      if h : k + i.val < n - 1 then (LinearMap.proj (R := ℝ) ⟨k + i.val, h⟩).toAffineMap
      else lastAffine).prod
    (AffineMap.pi fun j : Fin (n - 1 - r) =>
      (LinearMap.proj (R := ℝ) ⟨j.val, by omega⟩).toAffineMap)

theorem splitMapLast_apply {n k r : ℕ} (x : Fin (n - 1) → ℝ) :
    splitMapLast (n := n) (k := k) (r := r) x
      = (blockLen k r x, fun j : Fin (n - 1 - r) => x ⟨j.val, by omega⟩) := by
  rw [splitMapLast, AffineMap.prod_apply, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · funext i
    rw [AffineMap.pi_apply]
    by_cases h : k + i.val < n - 1
    · rw [dif_pos h, blockLen_of_lt x i h]
      rfl
    · rw [dif_neg h, blockLen_of_not_lt x i h, lastAffine_apply]
  · funext j
    rw [AffineMap.pi_apply]
    rfl

theorem splitMapLast_injective {n k r : ℕ} (hn : 0 < n) (hr : 1 ≤ r) (hk : k + r = n) :
    Function.Injective (fun x : Fin (n - 1) → ℝ =>
      (blockLen k r x, fun j : Fin (n - 1 - r) => x ⟨j.val, by omega⟩)) := by
  intro v w h
  have h1 : ∀ i : Fin r, blockLen k r v i = blockLen k r w i :=
    fun i => congrArg (fun p => p.1 i) h
  have h2 : ∀ j : Fin (n - 1 - r), v ⟨j.val, by omega⟩ = w ⟨j.val, by omega⟩ :=
    fun j => congrArg (fun p => p.2 j) h
  -- a coordinate of the block, read through the block lengths
  have hblk : ∀ (t : ℕ) (ht : t < n - 1), k ≤ t → v ⟨t, ht⟩ = w ⟨t, ht⟩ := by
    intro t ht hkt
    obtain ⟨i, hi⟩ : ∃ i : Fin r, i.val = t - k := ⟨⟨t - k, by omega⟩, rfl⟩
    have hlt : k + i.val < n - 1 := by omega
    have hb := h1 i
    rw [blockLen_of_lt v i hlt, blockLen_of_lt w i hlt] at hb
    have hidx : (⟨t, ht⟩ : Fin (n - 1)) = ⟨k + i.val, hlt⟩ := by
      refine Fin.ext ?_
      change t = k + i.val
      omega
    simpa only [hidx] using hb
  -- a coordinate below the block, read off the second component
  have hbelow : ∀ t : Fin (n - 1), t.val < k - 1 → v t = w t := by
    intro t ht
    have h2t := h2 ⟨t.val, by omega⟩
    have hidx : (⟨t.val, by omega⟩ : Fin (n - 1)) = t := Fin.ext rfl
    simpa only [hidx] using h2t
  funext m
  by_cases hk0 : k = 0
  · exact hblk m.val m.isLt (by omega)
  have hk1 : 1 ≤ k := by omega
  by_cases hm : m.val < k - 1
  · exact hbelow m hm
  · by_cases hm2 : m.val = k - 1
    · -- the coordinate just below the block: use that the total mass is `1`
      have hsum : (∑ j, v j) = ∑ j, w j := by
        obtain ⟨i, hi⟩ : ∃ i : Fin r, i.val = r - 1 := ⟨⟨r - 1, by omega⟩, rfl⟩
        have hlt : ¬ k + i.val < n - 1 := by omega
        have hb := h1 i
        rw [blockLen_of_not_lt v i hlt, blockLen_of_not_lt w i hlt] at hb
        linarith
      set m0 : Fin (n - 1) := ⟨k - 1, by omega⟩ with hm0
      have hoff : ∀ t : Fin (n - 1), t ≠ m0 → v t = w t := by
        intro t htne
        rcases lt_trichotomy t.val (k - 1) with hlt | heq | hgt
        · exact hbelow t hlt
        · exact absurd (Fin.ext heq) htne
        · exact hblk t.val t.isLt (by omega)
      have hmem : m0 ∈ Finset.univ := Finset.mem_univ _
      have hve := Finset.add_sum_erase (Finset.univ : Finset (Fin (n - 1))) v hmem
      have hwe := Finset.add_sum_erase (Finset.univ : Finset (Fin (n - 1))) w hmem
      have heq : (∑ t ∈ Finset.univ.erase m0, v t) = ∑ t ∈ Finset.univ.erase m0, w t :=
        Finset.sum_congr rfl (fun t ht => hoff t (Finset.ne_of_mem_erase ht))
      have hkey : v m0 = w m0 := by linarith [hve, hwe, heq, hsum]
      have hm0m : m0 = m := by
        have h1 : m0.val = k - 1 := by rw [hm0]
        refine Fin.ext ?_
        show m0.val = m.val
        omega
      rw [hm0m] at hkey
      exact hkey
    · exact hblk m.val m.isLt (by omega)

theorem blockLen_pos {n k r : ℕ} {x : Fin (n - 1) → ℝ} (hx : x ∈ simplexRegion n)
    (i : Fin r) : 0 < blockLen k r x i := by
  by_cases h : k + i.val < n - 1
  · rw [blockLen_of_lt x i h]
    exact hx.1 ⟨k + i.val, h⟩
  · rw [blockLen_of_not_lt x i h]
    linarith [hx.2]

theorem finrank_split {n r : ℕ} (hrn : r ≤ n - 1) :
    Module.finrank ℝ (Fin (n - 1) → ℝ)
      = Module.finrank ℝ ((Fin r → ℝ) × (Fin (n - 1 - r) → ℝ)) := by
  simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
  omega

theorem splitMapLast_linear_injective {n k r : ℕ} (hn : 0 < n) (hr : 1 ≤ r) (hk : k + r = n) :
    Function.Injective (splitMapLast (n := n) (k := k) (r := r)).linear := by
  have hA : ∀ x : Fin (n - 1) → ℝ,
      splitMapLast (n := n) (k := k) (r := r) x
        = (splitMapLast (n := n) (k := k) (r := r)).linear x
          + splitMapLast (n := n) (k := k) (r := r) 0 := by
    intro x
    have h := AffineMap.map_vadd (splitMapLast (n := n) (k := k) (r := r))
      (0 : Fin (n - 1) → ℝ) x
    rw [vadd_eq_add, add_zero] at h
    simpa using h
  intro v w hvw
  refine splitMapLast_injective hn hr hk ?_
  beta_reduce
  rw [← splitMapLast_apply v, ← splitMapLast_apply w]
  rw [hA v, hA w, hvw]

theorem measurable_cellLen {n : ℕ} (m : ℕ) :
    Measurable fun x : Fin (n - 1) → ℝ => cellLen x m := by
  by_cases h : m < n - 1
  · have heq : (fun x : Fin (n - 1) → ℝ => cellLen x m) = fun x => x ⟨m, h⟩ := by
      funext x; rw [cellLen_of_lt x h]
    rw [heq]
    exact measurable_pi_apply _
  · have heq : (fun x : Fin (n - 1) → ℝ => cellLen x m) = fun x => 1 - ∑ j, x j := by
      funext x; rw [cellLen_of_not_lt x h]
    rw [heq]
    exact measurable_const.sub (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))

theorem measurable_rescaleSub {n k r : ℕ} : Measurable (rescaleSub (n := n) k r) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  have hnum : Measurable fun x : Fin (n - 1) → ℝ => blockLen k r x ⟨i.val, by omega⟩ :=
    measurable_cellLen (k + i.val)
  have hden : Measurable fun x : Fin (n - 1) → ℝ => ∑ j, blockLen k r x j :=
    Finset.measurable_sum _ (fun j _ => measurable_cellLen (k + j.val))
  exact hnum.div hden

/-- The rescaled length vector of a block is again a point of the open simplex: all its coordinates
are positive and its total mass is less than `1` because the last cell length is positive. -/
theorem rescaleSub_mem_simplexRegion {n k m : ℕ} {x : Fin (n - 1) → ℝ}
    (hx : x ∈ simplexRegion n) : rescaleSub k (m + 1) x ∈ simplexRegion (m + 1) := by
  have hS : 0 < ∑ j : Fin (m + 1), blockLen k (m + 1) x j :=
    Finset.sum_pos (fun j _ => blockLen_pos hx j) Finset.univ_nonempty
  have hcast : ∀ i : Fin m, (⟨i.val, by omega⟩ : Fin (m + 1)) = i.castSucc :=
    fun i => Fin.ext rfl
  refine ⟨fun i => ?_, ?_⟩
  · change 0 < blockLen k (m + 1) x ⟨i.val, by omega⟩ / ∑ j, blockLen k (m + 1) x j
    exact div_pos (blockLen_pos hx _) hS
  · change (∑ i : Fin m, blockLen k (m + 1) x ⟨i.val, by omega⟩
      / ∑ j, blockLen k (m + 1) x j) < 1
    rw [← Finset.sum_div, div_lt_one hS]
    have hsum : (∑ i : Fin m, blockLen k (m + 1) x ⟨i.val, by omega⟩)
        = ∑ i : Fin m, blockLen k (m + 1) x i.castSucc := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hcast i]
    rw [hsum, Fin.sum_univ_castSucc]
    have := blockLen_pos (k := k) (r := m + 1) hx (Fin.last m)
    linarith

/-- **Rescaling a sub-interval does not create measure.**  A null set of rescaled length vectors has
a null preimage in the parameters of the whole length vector: full-measure sets pull back to
full-measure sets.  With Lemma 3.1 (`BlockData.compLen_absolutelyContinuousAt`) this is what
carries an almost-sure statement about the rescaled exchange of a block to the parameters.

The proof splits the free coordinates of `simplexRegion n` into the `r` cell lengths of the block
and the `n - 1 - r` coordinates that they do not determine (`absolutelyContinuous_map_affine` for
the resulting injective affine map, which has matching dimensions), and then applies
`volume_normalize_preimage_null` to the normalisation of the block vector.  **The split is not
uniform**: when the block contains the last cell, its length vector determines the *sum*
`∑_{i<k} x i` rather than the individual coordinates `x i` (`i < k`), so the remaining coordinates
are `x 0, …, x (k - 2)` — there are `k - 1 = n - 1 - r` of them and `x (k - 1)` is recovered from
the sum; when it does not, they are the free coordinates outside the block. -/
theorem absolutelyContinuous_map_rescaleSub {n : ℕ} (hn : 0 < n) {k r : ℕ} (hk : k + r ≤ n) :
    (volume.restrict (simplexRegion n)).map (rescaleSub k r) ≪
      volume.restrict (simplexRegion r) := by
  classical
  rcases Nat.eq_zero_or_pos r with hr0 | hr
  · -- `r = 0`: the target is a single point
    subst hr0
    refine Measure.AbsolutelyContinuous.mk (fun s _ hs => ?_)
    have hregion : simplexRegion 0 = (Set.univ : Set (Fin (0 - 1) → ℝ)) := by
      ext x
      exact ⟨fun _ => Set.mem_univ x, fun _ => ⟨fun i => i.elim0, by simp⟩⟩
    rw [hregion, Measure.restrict_univ] at hs
    have hne : volume (Set.univ : Set (Fin (0 - 1) → ℝ)) ≠ 0 :=
      ne_of_gt (isOpen_univ.measure_pos (μ := volume) ⟨0, Set.mem_univ _⟩)
    rcases Set.eq_empty_or_nonempty s with h | ⟨a, ha⟩
    · rw [h]; simp
    · have hs' : s = Set.univ := by
        refine Set.eq_univ_of_forall (fun x => ?_)
        have hxa : x = a := by
          funext i
          exact absurd i.isLt (by simp)
        rw [hxa]
        exact ha
      exact absurd (hs' ▸ hs) hne
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, (Nat.sub_one_add_one (by omega)).symm⟩
  clear hr
  -- the two non-degenerate cases share everything after the construction of `Φ`
  have key : ∀ (Φ : (Fin (n - 1) → ℝ) →ᵃ[ℝ]
        ((Fin (m + 1) → ℝ) × (Fin (n - 1 - (m + 1)) → ℝ)))
      (_hΦinj : Function.Injective Φ.linear)
      (_hΦdim : Module.finrank ℝ (Fin (n - 1) → ℝ)
        = Module.finrank ℝ ((Fin (m + 1) → ℝ) × (Fin (n - 1 - (m + 1)) → ℝ)))
      (_hΦapp : ∀ x : Fin (n - 1) → ℝ, (Φ x).1 = blockLen k (m + 1) x),
      (volume.restrict (simplexRegion n)).map (rescaleSub k (m + 1)) ≪
        volume.restrict (simplexRegion (m + 1)) := by
    intro Φ hΦinj hΦdim hΦapp
    have : Measure.IsAddHaarMeasure (volume : Measure ((Fin (m + 1) → ℝ)
        × (Fin (n - 1 - (m + 1)) → ℝ))) := by
      have : Measure.IsAddHaarMeasure ((volume : Measure (Fin (m + 1) → ℝ)).prod
          (volume : Measure (Fin (n - 1 - (m + 1)) → ℝ))) :=
        { toIsFiniteMeasureOnCompacts := inferInstance, toIsAddLeftInvariant := inferInstance,
          toIsOpenPosMeasure := inferInstance }
      infer_instance
    refine Measure.AbsolutelyContinuous.mk (fun Z hZmeas hZ => ?_)
    have hZ0 : volume (Z ∩ simplexRegion (m + 1)) = 0 := by
      rw [← Measure.restrict_apply hZmeas]
      exact hZ
    obtain ⟨Z', hZsub, hZ'meas, hZ'null⟩ := exists_measurable_superset_of_null hZ0
    have hA1 : volume {t : Fin (m + 1) → ℝ |
        (∀ i, 0 < t i) ∧ (fun i : Fin m => t i.castSucc / ∑ j, t j) ∈ Z'} = 0 :=
        volume_normalize_preimage_null (r := m) hZ'null
    set A : Set ((Fin (m + 1) → ℝ) × (Fin (n - 1 - (m + 1)) → ℝ)) :=
      {u | (∀ i, 0 < u.1 i) ∧ (fun i : Fin m => u.1 i.castSucc / ∑ j, u.1 j) ∈ Z'}
      with hAdef
    have hAnull : volume A = 0 := by
      have hprod : A = {t : Fin (m + 1) → ℝ |
          (∀ i, 0 < t i) ∧ (fun i : Fin m => t i.castSucc / ∑ j, t j) ∈ Z'}
          ×ˢ (Set.univ : Set (Fin (n - 1 - (m + 1)) → ℝ)) := by
        ext u
        simp only [hAdef, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true]
      have hvol : (volume : Measure ((Fin (m + 1) → ℝ) × (Fin (n - 1 - (m + 1)) → ℝ)))
          = volume.prod volume := rfl
      rw [hprod, hvol, Measure.prod_prod, hA1]
      simp
    set A' := toMeasurable (volume : Measure ((Fin (m + 1) → ℝ)
      × (Fin (n - 1 - (m + 1)) → ℝ))) A with hA'def
    have hA'meas : MeasurableSet A' := measurableSet_toMeasurable _ _
    have hA'null : volume A' = 0 := by
      rw [hA'def, measure_toMeasurable]
      exact hAnull
    have hΦmeas : Measurable ⇑Φ := (AffineMap.continuous_of_finiteDimensional Φ).measurable
    have hsub : rescaleSub k (m + 1) ⁻¹' Z ∩ simplexRegion n
        ⊆ ⇑Φ ⁻¹' A' ∩ simplexRegion n := by
      rintro x ⟨hxZ, hxO⟩
      refine ⟨?_, hxO⟩
      have hxA : Φ x ∈ A := by
        have h1 : (Φ x).1 = blockLen k (m + 1) x := hΦapp x
        refine ⟨fun i => ?_, ?_⟩
        · rw [h1]
          exact blockLen_pos hxO i
        · show (fun i : Fin m => (Φ x).1 i.castSucc / ∑ j, (Φ x).1 j) ∈ Z'
          rw [h1]
          have hres : (fun i : Fin m => blockLen k (m + 1) x i.castSucc
              / ∑ j, blockLen k (m + 1) x j) = rescaleSub k (m + 1) x := rfl
          rw [hres]
          exact hZsub ⟨hxZ, rescaleSub_mem_simplexRegion hxO⟩
      exact subset_toMeasurable _ _ hxA
    have hac : ((volume.restrict (simplexRegion n)).map Φ) A' = 0 :=
      (absolutelyContinuous_map_affine (O := simplexRegion n) hΦinj hΦdim) hA'null
    refine le_antisymm ?_ bot_le
    calc (volume.restrict (simplexRegion n)).map (rescaleSub k (m + 1)) Z
        = (volume.restrict (simplexRegion n)) (rescaleSub k (m + 1) ⁻¹' Z) :=
          Measure.map_apply measurable_rescaleSub hZmeas
      _ ≤ (volume.restrict (simplexRegion n)) (⇑Φ ⁻¹' A') := by
          rw [Measure.restrict_apply (measurable_rescaleSub hZmeas),
            Measure.restrict_apply (hΦmeas hA'meas)]
          exact measure_mono hsub
      _ = ((volume.restrict (simplexRegion n)).map Φ) A' :=
          (Measure.map_apply hΦmeas hA'meas).symm
      _ = 0 := hac
  by_cases hcase : k + (m + 1) ≤ n - 1
  · refine key (splitMap (k := k) (r := m + 1) hcase) (splitMap_injective hcase)
      (finrank_split (by omega)) (fun x => ?_)
    rw [splitMap_apply (k := k) (r := m + 1) hcase x]
  · have hk2 : k + (m + 1) = n := by omega
    by_cases hk0 : k = 0
    · -- the block is everything: the rescaling is the identity
      subst hk0
      have hneq : n = m + 1 := by omega
      subst hneq
      have hrescale : rescaleSub (n := m + 1) 0 (m + 1) = id := by
        funext x i
        have hi : i.val < m := by have := i.isLt; omega
        have hden : (∑ j : Fin (m + 1), blockLen 0 (m + 1) x j) = 1 := by
          have hb : (∑ j : Fin (m + 1), blockLen 0 (m + 1) x j)
              = ∑ j : Fin (m + 1), cellLen (n := m + 1) x j :=
            Finset.sum_congr rfl (fun j _ => by
              change cellLen (n := m + 1) x (0 + j.val) = cellLen (n := m + 1) x j
              rw [Nat.zero_add])
          rw [hb]
          exact sum_cellLen x
        have hnum : blockLen 0 (m + 1) x ⟨i.val, by omega⟩ = x i := by
          rw [blockLen_of_lt x ⟨i.val, by omega⟩ (by simp)]
          simp only [Nat.zero_add]
        simp only [rescaleSub, hden, hnum, div_one]
        rfl
      rw [hrescale, Measure.map_id]
    · refine key (splitMapLast (n := n) (k := k) (r := m + 1))
        (splitMapLast_linear_injective hn (by omega) hk2) (finrank_split (by omega)) (fun x => ?_)
      rw [splitMapLast_apply (n := n) (k := k) (r := m + 1) x]
