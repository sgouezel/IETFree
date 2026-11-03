/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib

/-!
# Tool 1: uniform Birkhoff convergence on a compact space

For a continuous self-map `f` of a compact Hausdorff space `X` with a unique invariant Borel
probability measure `μ`, the Birkhoff averages of every continuous function `φ` converge to
`∫ φ dμ` uniformly on `X`.

This file contains the empirical (Birkhoff) measures `birkhoffMeasure`, the exact shift identity
for their pushforwards, and the two headline convergence theorems (absolute and relative form).
-/

namespace IETFree.UniqueErgodicity

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction Topology

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [T2Space X]

/-! ### The empirical measure -/

/-- The empirical (Birkhoff) probability measure of the orbit of `x` up to time `n`. -/
noncomputable def birkhoffMeasure (f : X → X) (x : X) (n : ℕ) (hn : n ≠ 0) :
    ProbabilityMeasure X :=
  ⟨(n : ℝ≥0∞)⁻¹ • ((∑ i ∈ Finset.range n, Measure.dirac (f^[i] x)) : Measure X), by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
    have hsum : (∑ i ∈ Finset.range n, ((Measure.dirac (f^[i] x) : Measure X)) Set.univ)
        = (n : ℝ≥0∞) := by simp
    rw [hsum]
    exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hn) (ENNReal.natCast_ne_top n)⟩

omit [CompactSpace X] in
/-- The integral of a continuous test function against a finite sum of Dirac masses is the
corresponding finite sum of values. -/
theorem integral_finset_sum_dirac (g : X →ᵇ ℝ) (s : Finset ℕ) (y : ℕ → X) :
    ∫ x, g x ∂((∑ i ∈ s, Measure.dirac (y i)) : Measure X) = ∑ i ∈ s, g (y i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, MeasureTheory.integral_add_measure
      (BoundedContinuousFunction.integrable (Measure.dirac (y a)) g)
      (BoundedContinuousFunction.integrable _ g), ih, MeasureTheory.integral_dirac]

omit [CompactSpace X] in
/-- (2.1): testing the empirical measure gives the Birkhoff average. -/
theorem integral_birkhoffMeasure (f : X → X) (x : X) (n : ℕ) (hn : n ≠ 0) (g : X →ᵇ ℝ) :
    ∫ y, g y ∂(birkhoffMeasure f x n hn : Measure X) =
      birkhoffAverage ℝ f (fun y => g y) n x := by
  conv_lhs => rw [birkhoffMeasure]
  rw [ProbabilityMeasure.coe_mk, MeasureTheory.integral_smul_measure,
    integral_finset_sum_dirac, birkhoffAverage, birkhoffSum, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [T2Space X] in
/-- Shifting the argument in a Birkhoff average: averaging `g ∘ f` at `x` is the same as
averaging `g` at `f x`. -/
theorem birkhoffAverage_comp_apply (f : X → X) (g : X → ℝ) (n : ℕ) (x : X) :
    birkhoffAverage ℝ f (fun y => g (f y)) n x = birkhoffAverage ℝ f g n (f x) := by
  simp only [birkhoffAverage, birkhoffSum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Function.iterate_succ_apply' f i x, Function.iterate_succ_apply]

omit [CompactSpace X] in
/-- (2.2): pushing the empirical measure forward by `f` moves it by two atoms, hence the
integrals against any bounded continuous `g` differ by at most `2 ‖g‖ / n`. -/
theorem abs_integral_map_sub_le (f : X → X) (hf : Continuous f) (x : X) (n : ℕ) (hn : n ≠ 0)
    (g : X →ᵇ ℝ) :
    |∫ y, g y ∂((birkhoffMeasure f x n hn : Measure X).map f)
      - ∫ y, g y ∂(birkhoffMeasure f x n hn : Measure X)| ≤ 2 * ‖g‖ / n := by
  have hmap : ∫ y, g y ∂((birkhoffMeasure f x n hn : Measure X).map f)
      = ∫ y, (g.compContinuous ⟨f, hf⟩) y ∂(birkhoffMeasure f x n hn : Measure X) :=
    MeasureTheory.integral_map hf.measurable.aemeasurable g.continuous.aestronglyMeasurable
  have hshift : ∫ y, (g.compContinuous ⟨f, hf⟩) y ∂(birkhoffMeasure f x n hn : Measure X)
      = birkhoffAverage ℝ f (fun y => g (f y)) n x :=
    integral_birkhoffMeasure f x n hn _
  have hbase : ∫ y, g y ∂(birkhoffMeasure f x n hn : Measure X)
      = birkhoffAverage ℝ f (fun y => g y) n x := integral_birkhoffMeasure f x n hn g
  have hdiff : birkhoffAverage ℝ f (fun y => g (f y)) n x
      - birkhoffAverage ℝ f (fun y => g y) n x
      = (n : ℝ)⁻¹ * (g (f^[n] x) - g x) := by
    rw [birkhoffAverage_comp_apply, birkhoffAverage_apply_sub_birkhoffAverage, smul_eq_mul]
  rw [hmap, hshift, hbase, hdiff]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hbound : |g (f^[n] x) - g x| ≤ 2 * ‖g‖ := by
    have h1 : |g (f^[n] x)| ≤ ‖g‖ := BoundedContinuousFunction.norm_coe_le_norm g _
    have h2 : |g x| ≤ ‖g‖ := BoundedContinuousFunction.norm_coe_le_norm g _
    calc |g (f^[n] x) - g x| ≤ |g (f^[n] x)| + |g x| := abs_sub _ _
      _ ≤ 2 * ‖g‖ := by linarith
  calc |(n : ℝ)⁻¹ * (g (f^[n] x) - g x)|
      = (n : ℝ)⁻¹ * |g (f^[n] x) - g x| := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hnpos)]
    _ ≤ (n : ℝ)⁻¹ * (2 * ‖g‖) := by gcongr
    _ = 2 * ‖g‖ / n := by field_simp

/-! ### A weak limit of empirical measures is invariant -/

omit [CompactSpace X] in
/-- A weak limit of empirical measures along a filter on which the averaging lengths tend to
infinity is invariant against every bounded continuous test function. -/
theorem integral_map_eq_of_tendsto_birkhoffMeasure (f : X → X) (hf : Continuous f)
    {ι : Type*} {p : Filter ι} [NeBot p] {x : ι → X} {n : ι → ℕ} (hn : ∀ i, n i ≠ 0)
    {ν : ProbabilityMeasure X}
    (hν : Tendsto (fun i => birkhoffMeasure f (x i) (n i) (hn i)) p (𝓝 ν))
    (hntop : Tendsto n p atTop) (g : X →ᵇ ℝ) :
    ∫ y, g y ∂((ν : Measure X).map f) = ∫ y, g y ∂(ν : Measure X) := by
  have hν' := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto (F := p)).mp hν
  have heq : ∀ μ : ProbabilityMeasure X,
      ∫ y, g y ∂((μ : Measure X).map f)
        = ∫ y, (g.compContinuous ⟨f, hf⟩) y ∂(μ : Measure X) := fun μ =>
    MeasureTheory.integral_map hf.measurable.aemeasurable g.continuous.aestronglyMeasurable
  have hshift : Tendsto
      (fun i => ∫ y, g y ∂(((birkhoffMeasure f (x i) (n i) (hn i)) : Measure X).map f)) p
      (𝓝 (∫ y, g y ∂((ν : Measure X).map f))) := by
    simpa only [heq] using hν' (g.compContinuous ⟨f, hf⟩)
  have hunshift : Tendsto
      (fun i => ∫ y, g y ∂((birkhoffMeasure f (x i) (n i) (hn i)) : Measure X)) p
      (𝓝 (∫ y, g y ∂(ν : Measure X))) := hν' g
  have hzero : Tendsto (fun i =>
      ∫ y, g y ∂(((birkhoffMeasure f (x i) (n i) (hn i)) : Measure X).map f)
        - ∫ y, g y ∂((birkhoffMeasure f (x i) (n i) (hn i)) : Measure X)) p (𝓝 0) := by
    refine tendsto_zero_iff_abs_tendsto_zero _ |>.mpr ?_
    have hlim : Tendsto (fun i => 2 * ‖g‖ / (n i)) p (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (2 * ‖g‖)).comp hntop
    exact squeeze_zero (fun i => abs_nonneg _)
      (fun i => abs_integral_map_sub_le f hf (x i) (n i) (hn i) g) hlim
  have hsub := hshift.sub hunshift
  have hfin := tendsto_nhds_unique hsub hzero
  linarith

/-! ### Passing to a regular invariant measure -/

/-- A regular finite measure which is invariant against every bounded continuous test function
is invariant.  Regularity is what makes closed sets accessible to Urysohn functions. -/
theorem map_eq_self_of_integral_eq (f : X → X) (hf : Continuous f) (ν₀ : Measure X)
    [Measure.Regular ν₀] [IsFiniteMeasure ν₀]
    (hint : ∀ g : X →ᵇ ℝ, ∫ x, g x ∂(ν₀.map f) = ∫ x, g x ∂ν₀) :
    ν₀.map f = ν₀ := by
  -- the key closed-set inequality, via Urysohn functions and outer regularity
  have hclosed : ∀ ⦃C : Set X⦄, IsCompact C → ν₀ (f ⁻¹' C) ≤ ν₀ C := by
    intro C hC
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨U, hCU, hUopen, hU⟩ :=
      Measure.OuterRegular.outerRegular (μ := ν₀) hC.measurableSet (ν₀ C + ↑ε)
        (ENNReal.lt_add_right (measure_lt_top _ _).ne (ENNReal.coe_ne_zero.mpr hε.ne'))
    obtain ⟨g, hgC, -, hgU, hg01⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hC hUopen hCU
    let gb : X →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact g
    have hmeas : MeasurableSet (f ⁻¹' C) := hf.measurable hC.measurableSet
    have hstep1 : ∫ x, (f ⁻¹' C).indicator (1 : X → ℝ) x ∂ν₀ ≤
        ∫ x, gb (f x) ∂ν₀ := by
      refine integral_mono ?_
        (BoundedContinuousFunction.integrable ν₀ (gb.compContinuous ⟨f, hf⟩)) ?_
      · exact (MeasureTheory.integrable_const (1 : ℝ)).indicator hmeas
      · intro x
        by_cases hx : x ∈ f ⁻¹' C
        · rw [Set.indicator_of_mem hx]; exact le_of_eq (hgC hx).symm
        · rw [Set.indicator_of_notMem hx]; exact (hg01 (f x)).1
    have hstep2 : ∫ x, gb (f x) ∂ν₀ = ∫ x, gb x ∂ν₀ := by
      rw [show ∫ x, gb (f x) ∂ν₀ = ∫ x, gb x ∂(ν₀.map f) from
        (MeasureTheory.integral_map (μ := ν₀) (φ := f) hf.measurable.aemeasurable
          gb.continuous.aestronglyMeasurable).symm]
      exact hint gb
    have hstep3 : ∫ x, gb x ∂ν₀ ≤ ν₀.real U := by
      rw [← integral_indicator_one hUopen.measurableSet]
      refine integral_mono (BoundedContinuousFunction.integrable ν₀ gb) ?_ ?_
      · exact (MeasureTheory.integrable_const (1 : ℝ)).indicator hUopen.measurableSet
      · intro x
        by_cases hx : x ∈ U
        · rw [Set.indicator_of_mem hx]; exact (hg01 x).2
        · rw [Set.indicator_of_notMem hx]
          exact le_of_eq (image_eq_zero_of_notMem_tsupport (fun hcon => hx (hgU hcon)))
    calc ν₀ (f ⁻¹' C)
        = ENNReal.ofReal ((ν₀ (f ⁻¹' C)).toReal) :=
          (ENNReal.ofReal_toReal (measure_lt_top _ _).ne).symm
      _ = ENNReal.ofReal (∫ x, (f ⁻¹' C).indicator (1 : X → ℝ) x ∂ν₀) := by
          rw [integral_indicator_one hmeas]; rfl
      _ ≤ ENNReal.ofReal (∫ x, gb (f x) ∂ν₀) := ENNReal.ofReal_le_ofReal hstep1
      _ = ENNReal.ofReal (∫ x, gb x ∂ν₀) := by rw [hstep2]
      _ ≤ ENNReal.ofReal (ν₀.real U) := ENNReal.ofReal_le_ofReal hstep3
      _ = ν₀ U := ENNReal.ofReal_toReal (measure_lt_top _ _).ne
      _ ≤ ν₀ C + ↑ε := hU.le
  -- Not dead code: `hinner` is never named again, but Lean uses local hypotheses of class type as
  -- instances, so it is what makes `MeasurableSet.measure_eq_iSup_isCompact` applicable below.
  have hinner : Measure.InnerRegular (ν₀.map f) :=
    Measure.InnerRegular.map_of_continuous hf
  have hfinite : IsFiniteMeasure (ν₀.map f) := ⟨by
    rw [Measure.map_apply hf.measurable MeasurableSet.univ, Set.preimage_univ]
    exact measure_lt_top _ _⟩
  have hle : ∀ A, MeasurableSet A → (ν₀.map f) A ≤ ν₀ A := by
    intro A hA
    rw [MeasurableSet.measure_eq_iSup_isCompact (μ := ν₀.map f) hA]
    refine iSup_le fun K => ?_
    refine iSup_le fun hKA => ?_
    refine iSup_le fun hK => ?_
    calc (ν₀.map f) K = ν₀ (f ⁻¹' K) := Measure.map_apply hf.measurable hK.measurableSet
      _ ≤ ν₀ K := hclosed hK
      _ ≤ ν₀ A := measure_mono hKA
  have hmass : (ν₀.map f) Set.univ = ν₀ Set.univ := by
    rw [Measure.map_apply hf.measurable MeasurableSet.univ, Set.preimage_univ]
  refine Measure.ext fun A hA => le_antisymm (hle A hA) ?_
  have hc1' : ν₀ Aᶜ ≠ ⊤ := (measure_lt_top _ _).ne
  have hc2' : (ν₀.map f) Aᶜ ≠ ⊤ := (measure_lt_top _ _).ne
  have hcompl : ν₀ A = ν₀ Set.univ - ν₀ Aᶜ := by
    simpa using measure_compl hA.compl hc1'
  have hcompl' : (ν₀.map f) A = ν₀ Set.univ - (ν₀.map f) Aᶜ := by
    have h := measure_compl (μ := ν₀.map f) hA.compl hc2'
    simp only [compl_compl] at h
    rw [h, hmass]
  rw [hcompl, hcompl']
  exact tsub_le_tsub_left (hle Aᶜ hA.compl) _

/-- If a probability measure is invariant against every bounded continuous test function, then
there is a *regular* probability measure with the same bounded continuous integrals which is
invariant. -/
theorem exists_regular_map_eq_self (f : X → X) (hf : Continuous f) (ν : ProbabilityMeasure X)
    (hν : ∀ g : X →ᵇ ℝ, ∫ y, g y ∂((ν : Measure X).map f) =
      ∫ y, g y ∂(ν : Measure X)) :
    ∃ ν₀ : ProbabilityMeasure X, (ν₀ : Measure X).Regular ∧
      (∀ g : X →ᵇ ℝ, ∫ y, g y ∂(ν : Measure X) = ∫ y, g y ∂(ν₀ : Measure X)) ∧
      (ν₀ : Measure X).map f = (ν₀ : Measure X) := by
  obtain ⟨ν₀, hreg, hfin, hint⟩ := Measure.exists_regular_eq_of_compactSpace (ν : Measure X)
  have hprob : ν₀ Set.univ = 1 := by
    have h1 : (ν₀ Set.univ).toReal = 1 := by
      have h : ν₀.real Set.univ = 1 := by
        simpa using (hint 1).symm
      simpa only [measureReal_def] using h
    rw [← ENNReal.ofReal_toReal hfin.measure_univ_lt_top.ne, h1, ENNReal.ofReal_one]
  -- invariance of `ν₀` tested against bounded continuous functions
  have hinv₀ (g : X →ᵇ ℝ) : ∫ x, g x ∂(ν₀.map f) = ∫ x, g x ∂ν₀ := by
    have h1 : ∫ x, g x ∂(ν₀.map f) = ∫ x, (g.compContinuous ⟨f, hf⟩) x ∂ν₀ :=
      MeasureTheory.integral_map (μ := ν₀) (φ := f) hf.measurable.aemeasurable
        g.continuous.aestronglyMeasurable
    have h2 : ∫ x, (g.compContinuous ⟨f, hf⟩) x ∂ν₀
        = ∫ x, (g.compContinuous ⟨f, hf⟩) x ∂ν := (hint _).symm
    have h3 : ∫ x, (g.compContinuous ⟨f, hf⟩) x ∂ν =
        ∫ x, g x ∂((ν : Measure X).map f) :=
      (MeasureTheory.integral_map (μ := (ν : Measure X)) (φ := f) hf.measurable.aemeasurable
        g.continuous.aestronglyMeasurable).symm
    rw [h1, h2, h3, hν g, hint g]
  exact ⟨⟨ν₀, ⟨hprob⟩⟩, hreg, hint,
    @map_eq_self_of_integral_eq X _ _ _ _ _ f hf ν₀ hreg hfin hinv₀⟩

/-! ### The empirical measure of an orbit staying in a measurable set -/

omit [TopologicalSpace X] [BorelSpace X] [CompactSpace X] [T2Space X] in
/-- If the first `n` points of the orbit of `x` all lie in a measurable set `C`, then the
empirical measure gives `C` full mass. -/
theorem birkhoffMeasure_apply_of_forall_mem (f : X → X) (x : X) (n : ℕ) (hn : n ≠ 0)
    {C : Set X} (hC : MeasurableSet C) (h : ∀ i ∈ Finset.range n, f^[i] x ∈ C) :
    ((birkhoffMeasure f x n hn : Measure X)) C = 1 := by
  conv_lhs => rw [birkhoffMeasure]
  rw [ProbabilityMeasure.coe_mk, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
  have hsum : (∑ i ∈ Finset.range n, ((Measure.dirac (f^[i] x) : Measure X)) C) =
      (n : ℝ≥0∞) := by
    have h1 : ∀ i ∈ Finset.range n, ((Measure.dirac (f^[i] x) : Measure X)) C = 1 := by
      intro i hi
      rw [Measure.dirac_apply' _ hC, Set.indicator_of_mem (h i hi)]
      rfl
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range,
      ← Nat.cast_smul_eq_nsmul ℝ≥0∞ n (1 : ℝ≥0∞), smul_eq_mul, mul_one]
  rw [hsum]
  exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hn) (ENNReal.natCast_ne_top n)

/-! ### The core uniform convergence argument -/

/-- **Core uniform convergence statement.** Assume that every invariant probability measure
giving full mass to a closed set `C` makes `φ` integrate to `c`, and that the orbit of every point
of `S` stays in `C`. Then the Birkhoff averages of `φ` converge to `c` uniformly on `S`. -/
theorem tendsto_uniform_birkhoffAverage_aux (f : X → X) (hf : Continuous f) (φ : X → ℝ)
    (hφ : Continuous φ) (c : ℝ) (C : Set X) (hC : IsClosed C)
    (h : ∀ ν : ProbabilityMeasure X, (ν : Measure X).map f = ν → (ν : Measure X) C = 1 →
      ∫ y, φ y ∂(ν : Measure X) = c)
    (S : Set X) (hS : ∀ x ∈ S, ∀ i : ℕ, f^[i] x ∈ C) :
    ∀ ε > 0, ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∀ x ∈ S,
      |birkhoffAverage ℝ f φ n x - c| ≤ ε := by
  intro ε hε
  by_contra hcon
  push Not at hcon
  have hspec : ∀ k : ℕ, ∃ n : ℕ, k + 1 ≤ n ∧ ∃ x : X, x ∈ S ∧
      ε < |birkhoffAverage ℝ f φ n x - c| := fun k => hcon (k + 1) (Nat.succ_pos k)
  choose n hn x hxS hx using hspec
  have hn_ne : ∀ k, n k ≠ 0 := by
    intro k
    have := hn k
    omega
  -- a nontrivial ultrafilter on the averaging times
  let p : Ultrafilter ℕ := Ultrafilter.of (atTop : Filter ℕ)
  have hp : (p : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  have hntop : Tendsto n (p : Filter ℕ) atTop := by
    refine (tendsto_atTop_atTop.mpr ?_).mono_left hp
    intro b
    exact ⟨b, fun a ha => by have := hn a; omega⟩
  -- compactness of the space of probability measures
  obtain ⟨ν, -, hν⟩ := IsCompact.ultrafilter_le_nhds' (s := Set.univ) isCompact_univ
    (p.map (fun k => birkhoffMeasure f (x k) (n k) (hn_ne k))) Filter.univ_mem
  have hνt : Tendsto (fun k => birkhoffMeasure f (x k) (n k) (hn_ne k))
      (p : Filter ℕ) (𝓝 ν) := hν
  -- the limit is invariant, hence regularisable and quantitatively controlled
  have hinv : ∀ g : X →ᵇ ℝ,
      ∫ y, g y ∂((ν : Measure X).map f) = ∫ y, g y ∂(ν : Measure X) :=
    fun g => integral_map_eq_of_tendsto_birkhoffMeasure f hf hn_ne hνt hntop g
  obtain ⟨ν₀, hreg, hint, hmap⟩ := exists_regular_map_eq_self f hf ν hinv
  -- `ν₀` gives full mass to `C`
  have hprobC : ((ν₀ : Measure X)) C = 1 := by
    have hCmeas : MeasurableSet C := hC.measurableSet
    refine le_antisymm ?_ ?_
    · calc ((ν₀ : Measure X)) C ≤ ((ν₀ : Measure X)) Set.univ :=
          measure_mono (Set.subset_univ C)
        _ = 1 := by simp
    · refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
      obtain ⟨U, hCU, hUopen, hU⟩ :=
        Measure.OuterRegular.outerRegular (μ := (ν₀ : Measure X)) hCmeas
          (((ν₀ : Measure X)) C + ↑δ)
          (ENNReal.lt_add_right (measure_lt_top _ _).ne (ENNReal.coe_ne_zero.mpr hδ.ne'))
      obtain ⟨g, hgC, -, hgU, hg01⟩ :=
        exists_continuousMap_one_of_isCompact_subset_isOpen hC.isCompact hUopen hCU
      let gb : X →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact g
      have hemp : ∀ k, (1 : ℝ) ≤
          ∫ y, gb y ∂((birkhoffMeasure f (x k) (n k) (hn_ne k)) : Measure X) := by
        intro k
        have hmem : ∀ i ∈ Finset.range (n k), f^[i] (x k) ∈ C := fun i _ => hS (x k) (hxS k) i
        have hmass : ((birkhoffMeasure f (x k) (n k) (hn_ne k) : Measure X)) C = 1 :=
          birkhoffMeasure_apply_of_forall_mem f (x k) (n k) (hn_ne k) hCmeas hmem
        have hgen : ((((birkhoffMeasure f (x k) (n k) (hn_ne k)) : Measure X)) C).toReal ≤
            ∫ y, gb y ∂((birkhoffMeasure f (x k) (n k) (hn_ne k)) : Measure X) := by
          rw [← measureReal_def, ← integral_indicator_one hCmeas]
          refine integral_mono ?_ (BoundedContinuousFunction.integrable _ gb) ?_
          · exact (MeasureTheory.integrable_const (1 : ℝ)).indicator hCmeas
          · intro y
            by_cases hy : y ∈ C
            · rw [Set.indicator_of_mem hy]; exact le_of_eq (hgC hy).symm
            · rw [Set.indicator_of_notMem hy]; exact (hg01 y).1
        rw [hmass] at hgen
        simpa using hgen
      have hlim : (1 : ℝ) ≤ ∫ y, gb y ∂((ν : Measure X)) :=
        ge_of_tendsto
          ((ProbabilityMeasure.tendsto_iff_forall_integral_tendsto
            (F := (p : Filter ℕ))).mp hνt gb)
          (Eventually.of_forall hemp)
      rw [hint gb] at hlim
      have hstep3 : ∫ y, gb y ∂((ν₀ : Measure X)) ≤ ((ν₀ : Measure X)).real U := by
        rw [← integral_indicator_one hUopen.measurableSet]
        refine integral_mono (BoundedContinuousFunction.integrable _ gb) ?_ ?_
        · exact (MeasureTheory.integrable_const (1 : ℝ)).indicator hUopen.measurableSet
        · intro y
          by_cases hy : y ∈ U
          · rw [Set.indicator_of_mem hy]; exact (hg01 y).2
          · rw [Set.indicator_of_notMem hy]
            exact le_of_eq (image_eq_zero_of_notMem_tsupport (fun hcon => hy (hgU hcon)))
      have hone : (1 : ℝ≥0∞) ≤ ((ν₀ : Measure X)) U := by
        rw [← ENNReal.ofReal_one,
          ← ENNReal.ofReal_toReal (measure_lt_top ((ν₀ : Measure X)) U).ne]
        exact ENNReal.ofReal_le_ofReal (hlim.trans hstep3)
      exact hone.trans hU.le
  have hc : ∫ y, φ y ∂(ν₀ : Measure X) = c := h ν₀ hmap hprobC
  -- convergence of the `φ`-integrals along the ultrafilter
  let φb : X →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨φ, hφ⟩
  have hνφ : ∫ y, φb y ∂(ν : Measure X) = c := by
    rw [hint φb]
    exact hc
  have hφlim : Tendsto
      (fun k => ∫ y, φ y ∂((birkhoffMeasure f (x k) (n k) (hn_ne k)) : Measure X))
      (p : Filter ℕ) (𝓝 c) := by
    have hmain := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto
      (F := (p : Filter ℕ))).mp hνt φb
    rw [hνφ] at hmain
    exact hmain
  have hbound : ∀ k, ε ≤
      |∫ y, φ y ∂((birkhoffMeasure f (x k) (n k) (hn_ne k)) : Measure X) - c| := by
    intro k
    have hbk : ∫ y, φ y ∂((birkhoffMeasure f (x k) (n k) (hn_ne k)) : Measure X)
        = birkhoffAverage ℝ f φ (n k) (x k) :=
      integral_birkhoffMeasure f (x k) (n k) (hn_ne k) φb
    rw [hbk]
    exact (hx k).le
  have htend0 : Tendsto (fun k =>
      |∫ y, φ y ∂((birkhoffMeasure f (x k) (n k) (hn_ne k)) : Measure X) - c|)
      (p : Filter ℕ) (𝓝 0) := by
    have h1 := hφlim.sub_const c
    simpa using h1.abs
  have hε0 : ε ≤ 0 := ge_of_tendsto htend0 (Eventually.of_forall hbound)
  linarith

/-! ### The two headline theorems -/

/-- **Theorem 1.1.** A continuous self-map of a compact space whose only invariant probability
measure is `μ` has uniformly convergent Birkhoff averages. -/
theorem tendsto_uniform_birkhoffAverage (f : X → X) (hf : Continuous f)
    (μ : ProbabilityMeasure X)
    (huniq : ∀ ν : ProbabilityMeasure X, (ν : Measure X).map f = ν → ν = μ)
    (φ : X → ℝ) (hφ : Continuous φ) :
    ∀ ε > 0, ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∀ x : X,
      |birkhoffAverage ℝ f φ n x - ∫ y, φ y ∂(μ : Measure X)| ≤ ε := by
  have hmain : ∀ ε > 0, ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∀ x ∈ (Set.univ : Set X),
      |birkhoffAverage ℝ f φ n x - ∫ y, φ y ∂(μ : Measure X)| ≤ ε := by
    refine tendsto_uniform_birkhoffAverage_aux f hf φ hφ (∫ y, φ y ∂(μ : Measure X))
      Set.univ isClosed_univ ?_ Set.univ ?_
    · intro ν hinv _
      rw [huniq ν hinv]
    · intro x _ i
      exact Set.mem_univ _
  simpa using hmain

/-! ### Axioms -/

end IETFree.UniqueErgodicity
