/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.Basic
import IETFree.RauzyVeech.SimplexAe

/-!
# Invariant probability measures of an exchange

This file provides the measure-theoretic objects of the Rauzy–Veech development: Lebesgue measure on
`[0, 1)` as an invariant probability measure (`lebesgue`, `invariant_unitMeas`), the cells of an
exchange and the *length vector* of a measure — the vector of their masses (`cellOf`, `lambdaOf`) —
and the uniqueness step: an invariant probability measure carried by `[0, 1)` is determined by its
length vector once every such length vector lies in the ray `ℝ • lam` and the length map is
injective (`existsUnique_of_lengths`, `masurVeech_of_components`).

Nothing here uses the measure estimates of the source's Lemmas 1–6: the file is where the remaining
inputs (the a.e. shrink, the tower formula and the injectivity of the length map) are plugged in.

**The measures considered lie on `[0,1)`.**  An exchange `P.toIET lam` is the identity off the
interval `[0,1)` (`mkIETFun_of_notMem`), so *every* probability measure on `[0,1)ᶜ` is invariant:
the unrestricted statement `∃! μ, Invariant μ (P.toIET lam)` is false for every `lam` (Lebesgue's
measure and the Dirac mass at `2` are both invariant, and they disagree on `[0,1)`).  The measures
are therefore required to satisfy `μ (Ico 0 1) = 1`, which is the source's setting (an exchange *of
the interval*); `existsUnique_of_lengths` and `masurVeech_of_components` carry this condition
explicitly.

The shape of the argument.  Fix irreducible combinatorial data `P` and a length vector `lam` of
total mass `1`, and let `len : ProbabilityMeasure ℝ → α → ℝ` be the length map of an invariant
probability measure (for the exchange `P.toIET lam`) with `μ (Ico 0 1) = 1`.  If

* Lebesgue's length vector is `lam` (`hLeb`),
* every such invariant probability measure has its length vector in the ray `ℝ • lam` (`h_ray`),
* the length map is injective on such invariant probability measures (`h_inj`),

then there is **exactly one** invariant probability measure with `μ (Ico 0 1) = 1`.  The mass
condition `∑ a, len μ a = 1` used below is not a hypothesis: it is `sum_lambdaOf`, the fact that the
bottom cells partition `Ico 0 1`.

Indeed, two invariant measures have length vectors `c • lam` and `d • lam` with `c = d = 1` (their
coordinates sum to `1` and `∑ lam = 1`), hence equal length vectors, hence are equal by injectivity;
and Lebesgue is one of them. -/

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace InvariantMeasure

variable {α : Type*} [Fintype α]

/-- **Uniqueness from the length vector.** If the length map of an invariant probability measure is
injective and every such length vector lies in the ray of `lam`, then there is exactly one invariant
probability measure. -/
theorem existsUnique_of_lengths (T : IET 0 1) (len : ProbabilityMeasure ℝ → α → ℝ) (lam : α → ℝ)
    (hsum_lam : ∑ a, lam a = 1) (lebesgue : ProbabilityMeasure ℝ) (hLeb : len lebesgue = lam)
    (hLebInv : Invariant lebesgue T) (hLebMass : (lebesgue : Measure ℝ) (Set.Ico 0 1) = 1)
    (h_ray : ∀ μ : ProbabilityMeasure ℝ, Invariant μ T → (μ : Measure ℝ) (Set.Ico 0 1) = 1 →
      ∃ c : ℝ, len μ = c • lam)
    (hsum : ∀ μ : ProbabilityMeasure ℝ, Invariant μ T → (μ : Measure ℝ) (Set.Ico 0 1) = 1 →
      ∑ a, len μ a = 1)
    (h_inj : ∀ μ ν : ProbabilityMeasure ℝ, Invariant μ T → Invariant ν T →
      (μ : Measure ℝ) (Set.Ico 0 1) = 1 → (ν : Measure ℝ) (Set.Ico 0 1) = 1 →
      len μ = len ν → μ = ν) :
    ∃! μ : ProbabilityMeasure ℝ, Invariant μ T ∧ (μ : Measure ℝ) (Set.Ico 0 1) = 1 := by
  refine ⟨lebesgue, ⟨hLebInv, hLebMass⟩, ?_⟩
  rintro μ ⟨hμ, hmass⟩
  obtain ⟨c, hc⟩ := h_ray μ hμ hmass
  have hc1 : c = 1 := by
    have h1 : ∑ a, len μ a = 1 := hsum μ hμ hmass
    rw [hc] at h1
    simpa only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hsum_lam, mul_one] using h1
  have hlen : len μ = len lebesgue := by rw [hc, hc1, one_smul, hLeb]
  exact (h_inj μ lebesgue hμ hLebInv hmass hLebMass hlen).symm ▸ rfl

/-- Lebesgue measure on `[0,1)` is invariant under an exchange. -/
theorem invariant_unitMeas (T : IET 0 1) :
    Invariant (⟨unitMeas, inferInstance⟩ : ProbabilityMeasure ℝ) T := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply T.measurable hA]
  exact IET.unitMeas_preimage T hA

/-- The cell of the letter `a`: the interval it occupies in the bottom order. -/
noncomputable def cellOf {α : Type*} [Fintype α] {n : ℕ} (P : IETDatum₂ α n) (lam : α → ℝ≥0)
    (a : α) : Set ℝ :=
  Set.Ico (leftEnd (P.lengthsInBottom lam) (P.piBottom a))
    (upperEnd (P.lengthsInBottom lam) (P.piBottom a))

/-- The length vector of a measure: the masses of the cells. -/
noncomputable def lambdaOf {α : Type*} [Fintype α] {n : ℕ} (μ : ProbabilityMeasure ℝ)
    (P : IETDatum₂ α n) (lam : α → ℝ≥0) : α → ℝ :=
  fun a => (μ : Measure ℝ).real (cellOf P lam a)

/-- Lebesgue as a probability measure on `[0,1)`. -/
noncomputable def lebesgue : ProbabilityMeasure ℝ := ⟨unitMeas, inferInstance⟩

/-- **The length vector of Lebesgue measure is the length vector.**  Each cell `[leftEnd, upperEnd)`
of the bottom order lies in `[0,1)` (because the lengths sum to `1`) and has Lebesgue measure equal
to the length of its letter. -/
theorem lambdaOf_lebesgue {α : Type*} [Fintype α] {n : ℕ} (P : IETDatum₂ α n)
    {lam : α → ℝ≥0} (h : lam ∈ simplexOn α) :
    lambdaOf lebesgue P lam = fun a : α => (lam a : ℝ) := by
  have hsum : ∑ j, (P.lengthsInBottom lam j : ℝ) = 1 := by
    have h' := P.sum_lengthsInBottom h
    exact_mod_cast h'
  funext a
  have hli : (P.lengthsInBottom lam (P.piBottom a) : ℝ) = (lam a : ℝ) := by
    simp [IETDatum₂.lengthsInBottom]
  have h0 : (0 : ℝ) ≤ leftEnd (P.lengthsInBottom lam) (P.piBottom a) :=
    leftEnd_nonneg _ _
  have h1 : upperEnd (P.lengthsInBottom lam) (P.piBottom a) ≤ 1 := by
    have h' := upperEnd_le_total (P.lengthsInBottom lam) (P.piBottom a)
    rwa [hsum] at h'
  have hset : Set.Ico (leftEnd (P.lengthsInBottom lam) (P.piBottom a))
        (upperEnd (P.lengthsInBottom lam) (P.piBottom a)) ∩ Set.Ico (0 : ℝ) 1
      = Set.Ico (leftEnd (P.lengthsInBottom lam) (P.piBottom a))
        (upperEnd (P.lengthsInBottom lam) (P.piBottom a)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ico]
    constructor
    · exact fun hx => hx.1
    · rintro ⟨hx1, hx2⟩
      exact ⟨⟨hx1, hx2⟩, ⟨le_trans h0 hx1, lt_of_lt_of_le hx2 h1⟩⟩
  have key : unitMeas.real (cellOf P lam a) = (lam a : ℝ) := by
    rw [Measure.real, unitMeas, cellOf, Measure.restrict_apply measurableSet_Ico,
      hset, Real.volume_Ico,
      ENNReal.toReal_ofReal (by linarith [upperEnd_eq (P.lengthsInBottom lam) (P.piBottom a)]),
      upperEnd_eq, hli]
    ring
  simp only [lambdaOf, lebesgue]
  exact key


/-! ## The bottom cells partition `[0, 1)`

`cellOf P lam a` is the interval of the letter `a` in the bottom order.  When `lam` is a point of
the simplex these intervals are pairwise disjoint and cover `[0, 1)`, so for a finite measure `μ`
the masses of the cells add up to `μ [0, 1)`.  This is what turns `μ (Ico 0 1) = 1` into the mass
hypothesis `∑ a, lambdaOf μ P lam a = 1` of `existsUnique_of_lengths`. -/

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- `leftEnd` is monotone in the index. -/
theorem leftEnd_mono (lam : Fin n → ℝ≥0) {i j : Fin n} (h : i ≤ j) :
    leftEnd lam i ≤ leftEnd lam j := by
  rw [leftEnd, leftEnd]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_)
    (fun k _ _ => (lam k).coe_nonneg)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact lt_of_lt_of_le hk h

omit [NeZero n] in
/-- The left end of the `(i+1)`-st interval is the right end of the `i`-th. -/
theorem leftEnd_succ_eq_upperEnd (lam : Fin n → ℝ≥0) (i : Fin n) (h : i.val + 1 < n) :
    leftEnd lam ⟨i.val + 1, h⟩ = upperEnd lam i := by
  rw [leftEnd, upperEnd]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fin.lt_def, Fin.le_def]
  dsimp only [Fin.val_mk]
  omega

omit [NeZero n] in
/-- Distinct intervals of the arrangement are ordered. -/
theorem upperEnd_le_leftEnd (lam : Fin n → ℝ≥0) {i j : Fin n} (h : i < j) :
    upperEnd lam i ≤ leftEnd lam j := by
  have hij : i.val + 1 < n := by
    have := j.isLt
    rw [Fin.lt_def] at h
    omega
  have h1 : leftEnd lam ⟨i.val + 1, hij⟩ ≤ leftEnd lam j := by
    refine leftEnd_mono lam ?_
    rw [Fin.le_def]
    dsimp only [Fin.val_mk]
    rw [Fin.lt_def] at h
    omega
  rwa [leftEnd_succ_eq_upperEnd lam i hij] at h1

/-- The arrangement covers `[0, ∑ lam)`: a point there lies in the interval of its index `idx`. -/
theorem mem_cellOf_idx (P : IETDatum₂ α n) (lam : α → ℝ≥0) {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) (∑ i, (P.lengthsInBottom lam i : ℝ))) :
    x ∈ cellOf P lam (P.piBottom.symm (idx (P.lengthsInBottom lam) x hx.1)) := by
  have hk : P.piBottom (P.piBottom.symm (idx (P.lengthsInBottom lam) x hx.1))
      = idx (P.lengthsInBottom lam) x hx.1 := Equiv.apply_symm_apply _ _
  simp only [cellOf, hk]
  exact ⟨idx_mem _ _ hx.1, lt_upperEnd_idx _ hx⟩

omit [NeZero n] in
/-- Every cell sits in `[0, ∑ lam)`. -/
theorem cellOf_subset (P : IETDatum₂ α n) (lam : α → ℝ≥0) (a : α) :
    cellOf P lam a ⊆ Set.Ico (0 : ℝ) (∑ i, (P.lengthsInBottom lam i : ℝ)) :=
  Set.Ico_subset_Ico (leftEnd_nonneg _ _) (upperEnd_le_total _ _)

omit [NeZero n] in
/-- The cells of distinct letters are disjoint. -/
theorem disjoint_cellOf (P : IETDatum₂ α n) (lam : α → ℝ≥0) {a b : α} (h : a ≠ b) :
    Disjoint (cellOf P lam a) (cellOf P lam b) := by
  have hne : P.piBottom a ≠ P.piBottom b := fun hc => h (P.piBottom.injective hc)
  refine Set.disjoint_left.mpr fun x hxa hxb => ?_
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd (lt_of_lt_of_le hxa.2 (upperEnd_le_leftEnd _ hlt)) (not_lt.mpr hxb.1)
  · exact absurd (lt_of_lt_of_le hxb.2 (upperEnd_le_leftEnd _ hlt)) (not_lt.mpr hxa.1)

/-- For a point of the simplex the cells cover `[0, 1)`. -/
theorem iUnion_cellOf (P : IETDatum₂ α n) {lam : α → ℝ≥0} (h : lam ∈ simplexOn α) :
    (⋃ a, cellOf P lam a) = Set.Ico (0 : ℝ) 1 := by
  have hsum : (∑ i, (P.lengthsInBottom lam i : ℝ)) = 1 := by
    have h' := P.sum_lengthsInBottom h
    exact_mod_cast h'
  rw [← hsum]
  refine Set.Subset.antisymm (Set.iUnion_subset fun a => cellOf_subset P lam a) ?_
  intro x hx
  exact Set.mem_iUnion_of_mem _ (mem_cellOf_idx P lam hx)

/-- **The length vector of a measure carried by `[0, 1)` has total mass `1`.** -/
theorem sum_lambdaOf (P : IETDatum₂ α n) (μ : ProbabilityMeasure ℝ) {lam : α → ℝ≥0}
    (h : lam ∈ simplexOn α) (hmass : (μ : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1) :
    ∑ a, lambdaOf μ P lam a = 1 := by
  have hdisj : (↑(Finset.univ : Finset α) : Set α).PairwiseDisjoint (cellOf P lam) :=
    fun a _ b _ hne => disjoint_cellOf P lam hne
  have hmeas : ∀ a, MeasurableSet (cellOf P lam a) := fun _ => measurableSet_Ico
  have hne_top : ∀ a, (μ : Measure ℝ) (cellOf P lam a) ≠ ⊤ := fun a => measure_ne_top _ _
  have hunion : (⋃ a ∈ (Finset.univ : Finset α), cellOf P lam a) = Set.Ico (0 : ℝ) 1 := by
    rw [← iUnion_cellOf P h]
    simp
  calc ∑ a, lambdaOf μ P lam a
      = ((∑ a, (μ : Measure ℝ) (cellOf P lam a) : ℝ≥0∞)).toReal := by
        rw [ENNReal.toReal_sum (fun a _ => hne_top a)]
        rfl
    _ = ((μ : Measure ℝ) (⋃ a ∈ (Finset.univ : Finset α), cellOf P lam a)).toReal := by
        rw [measure_biUnion_finset hdisj (fun a _ => hmeas a)]
    _ = ((μ : Measure ℝ) (Set.Ico (0:ℝ) 1)).toReal := by rw [hunion]
    _ = 1 := by rw [hmass]; norm_num

/-- Lebesgue on `[0,1)` has mass `1` there. -/
theorem lebesgue_Ico : (lebesgue : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1 := by
  change volume.restrict (Set.Ico (0 : ℝ) 1) (Set.Ico (0 : ℝ) 1) = 1
  rw [Measure.restrict_apply measurableSet_Ico, Set.inter_self, Real.volume_Ico, sub_zero]
  norm_num

/-- **The assembly.**  The main theorem follows from two a.e. statements about the length map of an
invariant probability measure carried by `[0,1)`:

* `h_ray` — the ray criterion: the length vector of any such invariant probability measure lies in
  the ray of `lam` (the a.e. shrinking of the cylinders and the tower formula are used here);
* `h_inj` — the length map is injective on such invariant probability measures (the towers refine
  with mesh going to zero).

The mass condition `∑ a, lambdaOf μ P lam a = 1` is not a hypothesis: it is `sum_lambdaOf`, the
partition of `[0,1)` into the bottom cells.  This lemma turns the two a.e. statements into
uniqueness of the invariant probability measure. -/
theorem masurVeech_of_components {α : Type*} [Fintype α] [Nonempty α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n)
    (h_ray : ∀ᵐ lam ∂(simplexVolumeOn α), ∀ μ : ProbabilityMeasure ℝ,
      Invariant μ (P.toIET lam) → (μ : Measure ℝ) (Set.Ico 0 1) = 1 →
        ∃ c : ℝ, lambdaOf μ P lam = c • (fun a : α => (lam a : ℝ)))
    (h_inj : ∀ᵐ lam ∂(simplexVolumeOn α), ∀ μ ν : ProbabilityMeasure ℝ,
      Invariant μ (P.toIET lam) → Invariant ν (P.toIET lam) →
        (μ : Measure ℝ) (Set.Ico 0 1) = 1 → (ν : Measure ℝ) (Set.Ico 0 1) = 1 →
        lambdaOf μ P lam = lambdaOf ν P lam → μ = ν) :
    ∀ᵐ lam ∂(simplexVolumeOn α), ∃! μ : ProbabilityMeasure ℝ,
      Invariant μ (P.toIET lam) ∧ (μ : Measure ℝ) (Set.Ico 0 1) = 1 := by
  filter_upwards [ae_mem_simplexOn_of_nonempty (α := α), h_ray, h_inj] with lam hmem h_ray' h_inj'
  exact existsUnique_of_lengths (P.toIET lam) (fun μ => lambdaOf μ P lam)
    (fun a : α => (lam a : ℝ)) (by exact_mod_cast hmem) ⟨unitMeas, inferInstance⟩
    (lambdaOf_lebesgue P hmem) (invariant_unitMeas _) lebesgue_Ico h_ray'
    (fun μ _ hmass => sum_lambdaOf P μ hmem hmass) h_inj'

end InvariantMeasure
