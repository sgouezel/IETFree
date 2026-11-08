/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The abstract transfer argument for the split interval

This file is the abstract transfer argument, in the setting of a compact Hausdorff space `X`
carrying a measurable map `p : X → ℝ` that is injective off the preimage of a countable set `D`,
together with an injective measurable self-map `G` of `X` playing the role of the germ
homeomorphism `T̃`.

The statements are

* `measure_singleton_map` — mass is constant along the orbits of an injective invariant map
  (Lemma 4.3);
* `measure_singleton_eq_zero_of_injOn_orbit` — an atom with infinite orbit carries no mass
  (Lemma 4.5(i));
* `map_map_eq_self` — vanishing of the defect, i.e. transfer of invariance (Theorem 4.6).

The lift lemma that the germ-map construction uses is the corrected `MeasPrep.lift_unique_on_Ico`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace IntervalExchange.UniqueErgodicity

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [T2Space X]

omit [CompactSpace X] in
/-- Lemma 4.3 of the blueprint: mass is constant along an orbit of an injective invariant map. -/
theorem measure_singleton_map (G : X → X) (hG : Function.Injective G) (hGm : Measurable G)
    {ν : Measure X} (hν : ν.map G = ν) (z : X) :
    ν {G z} = ν {z} := by
  conv_lhs => rw [← hν]
  rw [Measure.map_apply hGm (measurableSet_singleton (G z))]
  congr 1
  ext w
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact hG.eq_iff

omit [CompactSpace X] in
/-- Lemma 4.5(i) of the blueprint, abstract form: an atom of a probability measure whose orbit
under an injective invariant map is infinite carries no mass. -/
theorem measure_singleton_eq_zero_of_injOn_orbit (G : X → X) (hGinj : Function.Injective G)
    (hGm : Measurable G) {ν : Measure X} [IsProbabilityMeasure ν] (hν : ν.map G = ν) (z : X)
    (hinf : ∀ i j : ℕ, G^[i] z = G^[j] z → i = j) : ν {z} = 0 := by
  set m : ℝ≥0∞ := ν {z} with hm
  have hstep (i : ℕ) : ν {G^[i] z} = m := by
    induction i with
    | zero => exact hm.symm
    | succ i ih =>
        rw [Function.iterate_succ_apply']
        exact (measure_singleton_map G hGinj hGm hν (G^[i] z)).trans ih
  have hbound (N : ℕ) : (N : ℝ≥0∞) * m ≤ 1 := by
    have hdisj : (Finset.range N : Set ℕ).PairwiseDisjoint (fun i => ({(G^[i] z)} : Set X)) := by
      intro i _ j _ hij
      refine Set.disjoint_left.2 fun w hw1 hw2 => ?_
      simp only [Set.mem_singleton_iff] at hw1 hw2
      exact hij (hinf i j (hw1.symm.trans hw2))
    have hunion : ν (⋃ i ∈ Finset.range N, ({(G^[i] z)} : Set X))
        = ∑ i ∈ Finset.range N, ν ({(G^[i] z)} : Set X) :=
      measure_biUnion_finset hdisj fun i _ => measurableSet_singleton _
    have hsum : ∑ i ∈ Finset.range N, ν ({(G^[i] z)} : Set X) = (N : ℝ≥0∞) * m := by
      rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    rw [← hsum, ← hunion]
    calc ν (⋃ i ∈ Finset.range N, ({(G^[i] z)} : Set X)) ≤ ν Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  by_contra hm0
  have hmtop : m ≠ ⊤ := by
    have hle : m ≤ 1 := by
      rw [hm]
      have h := measure_mono (Set.subset_univ ({z} : Set X)) (μ := ν)
      rwa [measure_univ] at h
    exact ne_top_of_le_ne_top (by simp) hle
  have hpos : 0 < m.toReal := ENNReal.toReal_pos hm0 hmtop
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / m.toReal)
  have hN' : (1 : ℝ) < (N : ℝ) * m.toReal := by
    rw [div_lt_iff₀ hpos] at hN
    exact hN
  have hle : (N : ℝ) * m.toReal ≤ 1 := by
    have h3 : ((N : ℝ≥0∞) * m).toReal ≤ (1 : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono (by simp) (hbound N)
    simpa [ENNReal.toReal_mul] using h3
  linarith

omit [CompactSpace X] in
/-- Lemma 4.4 of the blueprint, in the form needed for the transfer of invariance: the defect
identity for bounded measurable test functions.  Here `e c` is the germ of `p` at the jump `c`,
`L` is the left limit of the interval exchange and `T` its right-continuous branch map; `hpe`,
`hdef` and `hTeq` say that the germs project to their labels, that the germ map sends the germ
at `c` to the left limit `L c`, and that it acts as `T` away from the finite set of germs.  The
injectivity of `G` is not needed for the identity; it is kept for interface compatibility. -/
theorem defect_identity_meas (G : X → X) (hGm : Measurable G)
    {ν : Measure X} [IsProbabilityMeasure ν] (hν : ν.map G = ν)
    (p : X → ℝ) (hp : Measurable p)
    (T L : ℝ → ℝ) (hT : Measurable T) (J : Finset ℝ) (e : ℝ → X)
    (hpe : ∀ c ∈ J, p (e c) = c)
    (hdef : ∀ c ∈ J, p (G (e c)) = L c)
    (hTeq : ∀ z : X, (∀ c ∈ J, z ≠ e c) → p (G z) = T (p z))
    {g : ℝ → ℝ} (hgm : Measurable g) {C : ℝ} (hgC : ∀ y, |g y| ≤ C) :
    (∫ y, g y ∂(ν.map p)) - ∫ y, g y ∂((ν.map p).map T)
      = ∑ c ∈ J, (ν {e c}).toReal * (g (L c) - g (T c)) := by
  classical
  -- the three integrands are bounded by `C`, hence integrable
  have hInt1 : Integrable (fun z => g (p z)) ν :=
    Integrable.of_bound (hgm.comp hp).aestronglyMeasurable C
      (ae_of_all _ fun z => by simpa using hgC (p z))
  have hInt2 : Integrable (fun z => g (T (p z))) ν :=
    Integrable.of_bound (hgm.comp (hT.comp hp)).aestronglyMeasurable C
      (ae_of_all _ fun z => by simpa using hgC (T (p z)))
  have hInt3 : Integrable (fun z => g (p (G z))) ν :=
    Integrable.of_bound (hgm.comp (hp.comp hGm)).aestronglyMeasurable C
      (ae_of_all _ fun z => by simpa using hgC (p (G z)))
  -- push the integrals to `ν`: first through `p`, then through `T`
  have hA : ∫ y, g y ∂(ν.map p) = ∫ z, g (p z) ∂ν :=
    integral_map (μ := ν) (φ := p) hp.aemeasurable hgm.aestronglyMeasurable
  have hB : ∫ y, g y ∂((ν.map p).map T) = ∫ z, g (T (p z)) ∂ν := by
    have hB1 : ∫ y, g y ∂((ν.map p).map T) = ∫ z, g (T z) ∂(ν.map p) :=
      integral_map (μ := ν.map p) (φ := T) hT.aemeasurable hgm.aestronglyMeasurable
    have hB2 : ∫ z, g (T z) ∂(ν.map p) = ∫ z, g (T (p z)) ∂ν :=
      integral_map (μ := ν) (φ := p) hp.aemeasurable (hgm.comp hT).aestronglyMeasurable
    rw [hB1, hB2]
  -- invariance of `ν` under `G` replaces `p z` by `p (G z)`
  have hstep1 : ∫ z, g (p z) ∂ν = ∫ z, g (p (G z)) ∂ν := by
    have h2 : ∫ y, (fun w => g (p w)) y ∂(ν.map G) = ∫ z, g (p (G z)) ∂ν :=
      integral_map (μ := ν) (φ := G) hGm.aemeasurable (hgm.comp hp).aestronglyMeasurable
    calc ∫ z, g (p z) ∂ν = ∫ y, (fun w => g (p w)) y ∂(ν.map G) := by rw [hν]
      _ = ∫ z, g (p (G z)) ∂ν := h2
  -- pointwise: `L c` at a germ `e c`, and `T` of the label everywhere else
  have hHeq : (fun z => g (p (G z)) - g (T (p z)))
      = fun z => ∑ c ∈ J, if z = e c then (g (L c) - g (T c)) else 0 := by
    funext z
    by_cases hz : ∃ c ∈ J, z = e c
    · obtain ⟨c, hc, rfl⟩ := hz
      have hsingle (c') (hc' : c' ∈ J) (hne : c' ≠ c) : ¬ (e c = e c') := by
        intro h
        exact hne (by rw [← hpe c hc, ← hpe c' hc', h])
      rw [hdef c hc, hpe c hc]
      rw [Finset.sum_eq_single c]
      · rw [ite_eq_left rfl]
      · intro c' hc' hne
        rw [ite_eq_right (hsingle c' hc' hne)]
      · intro hc'
        exact absurd hc hc'
    · have h0 (c) (hc : c ∈ J) : z ≠ e c := fun h =>
      hz ⟨c, hc, h⟩
      rw [hTeq z h0, sub_self]
      refine (Finset.sum_eq_zero ?_).symm
      intro c hc
      exact ite_eq_right (h0 c hc)
  -- integrate the finite sum: each term is a constant on the single point `e c`
  have hFint : ∫ z, (∑ c ∈ J, if z = e c then (g (L c) - g (T c)) else 0) ∂ν
      = ∑ c ∈ J, (g (L c) - g (T c)) * (ν {e c}).toReal := by
    have h := integral_finsetSum (μ := ν) (s := J)
      (f := fun c z => if z = e c then (g (L c) - g (T c)) else 0) (fun c _ => ?_)
    · rw [h]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hfun : (fun z : X => if z = e c then (g (L c) - g (T c)) else (0 : ℝ))
          = ({e c} : Set X).indicator (fun _ => (g (L c) - g (T c))) := by
        funext z
        by_cases hz : z = e c <;> simp [hz]
      rw [hfun, integral_indicator (measurableSet_singleton (e c)), setIntegral_const]
      simp [Measure.real, smul_eq_mul, mul_comm]
    · have hfun : (fun z : X => if z = e c then (g (L c) - g (T c)) else (0 : ℝ))
          = ({e c} : Set X).indicator (fun _ => (g (L c) - g (T c))) := by
        funext z
        by_cases hz : z = e c <;> simp [hz]
      rw [hfun]
      exact (integrable_const (g (L c) - g (T c))).indicator (measurableSet_singleton (e c))
  calc (∫ y, g y ∂(ν.map p)) - ∫ y, g y ∂((ν.map p).map T)
      = ∫ z, g (p z) ∂ν - ∫ z, g (T (p z)) ∂ν := by rw [hA, hB]
    _ = ∫ z, g (p (G z)) ∂ν - ∫ z, g (T (p z)) ∂ν := by rw [hstep1]
    _ = ∫ z, (g (p (G z)) - g (T (p z))) ∂ν := (integral_sub hInt3 hInt2).symm
    _ = ∫ z, (∑ c ∈ J, if z = e c then (g (L c) - g (T c)) else 0) ∂ν := by rw [hHeq]
    _ = ∑ c ∈ J, (g (L c) - g (T c)) * (ν {e c}).toReal := hFint
    _ = ∑ c ∈ J, (ν {e c}).toReal * (g (L c) - g (T c)) :=
        Finset.sum_congr rfl fun c _ => mul_comm _ _

omit [CompactSpace X] in
/-- Theorem 4.6 of the blueprint, abstract form: if the germs of the jumps carry no mass, then
the pushforward of an invariant probability is invariant. -/
theorem map_map_eq_self (G : X → X) (hGm : Measurable G)
    {ν : Measure X} [IsProbabilityMeasure ν] (hν : ν.map G = ν)
    (p : X → ℝ) (hp : Measurable p)
    (T L : ℝ → ℝ) (hT : Measurable T) (J : Finset ℝ) (e : ℝ → X)
    (hpe : ∀ c ∈ J, p (e c) = c)
    (hdef : ∀ c ∈ J, p (G (e c)) = L c)
    (hTeq : ∀ z : X, (∀ c ∈ J, z ≠ e c) → p (G z) = T (p z))
    (hvan : ∀ c ∈ J, ν {e c} = 0) : (ν.map p).map T = ν.map p := by
  refine Measure.ext fun A hA => ?_
  have hgm : Measurable (A.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hA
  have hgC (y) : |(A.indicator fun _ => (1 : ℝ)) y| ≤ 1 := by
    by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, hy]
  have hmain := defect_identity_meas G hGm hν p hp T L hT J e hpe hdef hTeq hgm hgC
  have hzero : ∑ c ∈ J, (ν {e c}).toReal * ((A.indicator fun _ => (1 : ℝ)) (L c)
      - (A.indicator fun _ => (1 : ℝ)) (T c)) = 0 := by
    refine Finset.sum_eq_zero fun c hc => ?_
    rw [hvan c hc]
    simp
  rw [hzero, sub_eq_zero] at hmain
  have hII (ρ : Measure ℝ) : ∫ y, (A.indicator fun _ => (1 : ℝ)) y ∂ρ = (ρ A).toReal := by
    rw [integral_indicator hA, setIntegral_const]
    simp [Measure.real]
  rw [hII, hII] at hmain
  have h1 : ((ν.map p).map T) A ≠ ⊤ := measure_ne_top _ _
  have h2 : (ν.map p) A ≠ ⊤ := measure_ne_top _ _
  exact (ENNReal.toReal_eq_toReal_iff' h1 h2).1 hmain.symm

end IntervalExchange.UniqueErgodicity

end
