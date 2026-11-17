/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Analysis lemmas for Mathlib

Five facts the interval-exchange development needs that Mathlib does not have, stated at the
generality the proofs allow: an injectivity criterion for the linear part of an affine map, the
`dist` of two `ℝ≥0`-valued functions under the coercion to `ℝ`, the image of a pairwise disjoint
family of sets under an injection, the measure of a slice of a finite partition, and the
measurability of a set covered, at every level of a sequence of partitions, by measurable pieces.
Each docstring names the file the lemma would go in.
-/

public section

open MeasureTheory
open scoped NNReal

/-- **A set covered by measurable pieces at one level of a sequence of partitions is measurable.**
If, for every `n`, the sets of `P n` are measurable, sit inside `I`, and cover `I`, then `I` is
measurable — one level suffices, and the sequence is there because that is how the partitions are
produced.

Natural home: `Mathlib/MeasureTheory/MeasurableSpace/Borel.lean` or a new
`Mathlib/MeasureTheory/MeasurableSpace/Partition.lean`. -/
theorem MeasureTheory.measurableSet_of_partitions {X : Type*} [MeasurableSpace X] (I : Set X)
    (P : ℕ → Finset (Set X)) (hmeas : ∀ n A, A ∈ P n → MeasurableSet A)
    (hsub : ∀ n A, A ∈ P n → A ⊆ I) (hcov : ∀ n x, x ∈ I → ∃ A ∈ P n, x ∈ A) :
    MeasurableSet I := by
  have h0 : I = ⋃ A ∈ P 0, A := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      obtain ⟨A, hA, hxA⟩ := hcov 0 x hx
      exact Set.mem_biUnion hA hxA
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨A, hA, hxA⟩ := hx
      exact hsub 0 A hA hxA
  rw [h0]
  exact Finset.measurableSet_biUnion _ fun A hA => hmeas 0 A hA

/-- **The measure of a slice of a finite partition.**  If the sets `C i` are pairwise disjoint and
cover `T`, then the measure of `S ∩ T` is the sum of the measures of the `S ∩ C i`.

Natural home: `Mathlib/MeasureTheory/Measure/MeasureSpace.lean`, beside `measure_iUnion`. -/
theorem MeasureTheory.measure_inter_eq_sum {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}
    {C : Fin n → Set X} {T : Set X} (hcover : (⋃ i, C i) = T)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j)) {S : Set X}
    (hmeas : ∀ i, MeasurableSet (S ∩ C i)) :
    μ (S ∩ T) = ∑ i, μ (S ∩ C i) := by
  have h : S ∩ T = ⋃ i, S ∩ C i := by rw [← hcover, Set.inter_iUnion]
  rw [h, measure_iUnion (f := fun i => S ∩ C i)
    (fun i j hij => (hdisj i j hij).mono Set.inter_subset_right Set.inter_subset_right) hmeas,
    tsum_fintype]

/-- **Disjointness is preserved by an injective image of the sets.**

Natural home: `Mathlib/Data/Set/Pairwise/Basic.lean`, beside `Set.PairwiseDisjoint.image_of_le`. -/
theorem Set.PairwiseDisjoint.image_of_injective {ι X Y : Type*} {f : X → Y}
    (hf : Function.Injective f) {s : Finset ι} {g : ι → Set X} (h : Set.PairwiseDisjoint (↑s) g) :
    Set.PairwiseDisjoint (↑s) fun i => f '' g i := by
  intro i hi j hj hij
  exact (h hi hj hij).image hf.injOn (Set.subset_univ _) (Set.subset_univ _)

/-- **The `dist` of two `ℝ≥0`-valued functions is the `dist` of their coercions to `ℝ`.**

Natural home: `Mathlib/Topology/MetricSpace/PiNat.lean`, or `Mathlib/Data/NNReal/Basic.lean`
beside `NNReal.dist_eq`. -/
theorem NNReal.dist_pi_coe {α : Type*} [Fintype α] (x y : α → ℝ≥0) :
    dist (fun a => (x a : ℝ)) (fun a => (y a : ℝ)) = dist x y := by
  rw [dist_pi_def, dist_pi_def]
  exact congrArg (fun r : ℝ≥0 => (r : ℝ))
    (Finset.sup_congr rfl fun a _ => rfl)

/-- **The linear part of an affine map injective on a nonempty open set is injective.**  The affine
map itself is then injective too, which is the form the absolute-continuity argument uses: a
nonvanishing linear part gives the change-of-variables formula.

Natural home: `Mathlib/Analysis/Normed/Affine/Isometry.lean`, beside `AffineMap.isOpenMap`. -/
theorem AffineMap.injective_linear_of_injOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup F] [Module ℝ F]
    {O : Set E} (hOo : IsOpen O) (hne : O.Nonempty) {A : E →ᵃ[ℝ] F}
    (hinj : Set.InjOn A O) : Function.Injective A.linear := by
  intro v w hvw
  by_contra hne'
  have hz : A.linear (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have hune : v - w ≠ 0 := sub_ne_zero.mpr hne'
  obtain ⟨p, hp⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hOo p hp
  set u := v - w with hu
  set t := ε / (2 * (‖u‖ + 1)) with ht
  have htpos : 0 < t := by
    rw [ht]; positivity
  have hnorm : 0 < ‖u‖ + 1 := by positivity
  have htlt : t * ‖u‖ < ε := by
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg u]
  have hmem : p + t • u ∈ O := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos htpos]
    exact htlt
  have hAp : A (p + t • u) = A p := by
    have h := AffineMap.map_vadd A p (t • u)
    rw [vadd_eq_add, map_smul, hz, smul_zero, add_comm (t • u) p] at h
    simpa using h
  have hfin := hinj hmem hp hAp
  have hzu : t • u = 0 := by
    have := congrArg (fun x => x - p) hfin
    simpa using this
  rcases smul_eq_zero.mp hzu with h | h
  · exact absurd h (ne_of_gt htpos)
  · exact hune h
