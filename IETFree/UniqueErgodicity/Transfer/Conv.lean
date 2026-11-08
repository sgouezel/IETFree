/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.UniqueErgodicity.Basic
public import IETFree.UniqueErgodicity.Split

/-!
# Transferring uniform Birkhoff convergence along a factor

Tool 1 gives uniform convergence of the Birkhoff averages of a continuous map `G` on a compact
space.  The dynamics of the interval exchange `T` is a *factor* of the dynamics of the germ
map `G` on the split interval: the projection `π` satisfies `π ∘ G = T ∘ π`, and the right
germs form a section of `π` along which `G` is the lift of `T`.

This file proves the elementary transfer step used by `UniqueErgodicity.Theorem2`: uniform
convergence of the averages of `ψ ∘ π` for `G`, from every point of an invariant set `S` of the
split interval, gives uniform convergence of the averages of `ψ` for `T`, from every point of
`[0,1)`.  No measure theory enters; the only measure-theoretic input is the identification of the
two limits, which the caller supplies as `hint` (it follows from the transfer of Lebesgue measure,
in the form `MeasPrep.lift_unique_on_Ico` — a total section `ℝ → X` cannot exist for the split
interval).  The convergence hypothesis is asked on `S`, not on the whole space, and that is not a
convenience: the split interval has two isolated fixed points (`leftGerm 0`, `rightGerm 1`) at
which the averages cannot converge to `∫ ψ dμ`, so the unrestricted form is false.
`UniqueErgodicity.Theorem2` takes `S := SplitI.rightPart`, which is exactly what Tool 1 supplies.
See Blueprint 2, Remark 2.7.  The statement is purely about iterates of a section, so it is stated
for arbitrary types. -/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators
open IntervalExchange.IET

namespace IntervalExchange.UniqueErgodicity

section Section

variable {X Y : Type*}

/-- **Iterates of an equivariant section, on an invariant set**: it is enough that `Ω` is invariant
under `T` and that the equivariance holds on `Ω`. -/
theorem iterate_section_on {G : X → X} {T : Y → Y} {s : Y → X} {Ω : Set Y}
    (hΩ : ∀ y ∈ Ω, T y ∈ Ω) (hG : ∀ y ∈ Ω, G (s y) = s (T y)) (n : ℕ) ⦃y : Y⦄ (hy : y ∈ Ω) :
    G^[n] (s y) = s (T^[n] y) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
      have hTn : T^[n] y ∈ Ω := by
        clear ih
        induction n with
        | zero => exact hy
        | succ m hm => rw [Function.iterate_succ_apply']; exact hΩ _ hm
      rw [Function.iterate_succ_apply', ih hy, hG _ hTn,
        Function.iterate_succ_apply']

/-- **Iterating the section identity.**  If `π ∘ s = id` and `G ∘ s = s ∘ T` on the invariant set
`Ω`, then `π (G^[n] (s y)) = T^[n] y` for every `y ∈ Ω`. -/
theorem apply_iterate_section_on {G : X → X} {T : Y → Y} {s : Y → X} {π : X → Y}
    {Ω : Set Y}
    (hΩ : ∀ y ∈ Ω, T y ∈ Ω) (hπ : ∀ y ∈ Ω, π (s y) = y)
    (hG : ∀ y ∈ Ω, G (s y) = s (T y)) (n : ℕ) ⦃y : Y⦄ (hy : y ∈ Ω) :
    π (G^[n] (s y)) = T^[n] y := by
  rw [iterate_section_on hΩ hG n hy]
  exact hπ _ (by
    induction n with
    | zero => exact hy
    | succ n ih => rw [Function.iterate_succ_apply']; exact hΩ _ ih)

/-- **Birkhoff averages of a function of the section.**  Under the same hypotheses, the `n`-th
Birkhoff average of `φ ∘ π` at `s y` is that of `φ` at `T^[n] y`. -/
theorem birkhoffAverage_comp_section_on {G : X → X} {T : Y → Y} {s : Y → X} {π : X → Y}
    {Ω : Set Y} (hΩ : ∀ y ∈ Ω, T y ∈ Ω) (hπ : ∀ y ∈ Ω, π (s y) = y)
    (hG : ∀ y ∈ Ω, G (s y) = s (T y)) (φ : Y → ℝ) (n : ℕ) ⦃y : Y⦄ (hy : y ∈ Ω) :
    birkhoffAverage ℝ G (fun z => φ (π z)) n (s y) = birkhoffAverage ℝ T φ n y := by
  simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [apply_iterate_section_on hΩ hπ hG i hy]

/-- **Uniform convergence transfers along a factor.**  If the Birkhoff averages of `φ ∘ π` for
`G` converge to `c` uniformly from every point of `S`, then the Birkhoff averages of `φ` for `T`
converge to `c` uniformly from every point of the invariant set `Ω`. -/
theorem tendsto_uniform_birkhoffAverage_of_section {G : X → X} {T : Y → Y} {s : Y → X}
    {π : X → Y} {Ω : Set Y} {S : Set X} (hΩ : ∀ y ∈ Ω, T y ∈ Ω)
    (hs : ∀ y ∈ Ω, s y ∈ S)
    (hπ : ∀ y ∈ Ω, π (s y) = y) (hG : ∀ y ∈ Ω, G (s y) = s (T y)) (φ : Y → ℝ)
    {c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∀ x ∈ S,
      |birkhoffAverage ℝ G (fun z => φ (π z)) n x - c| ≤ ε)
    (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∀ y ∈ Ω,
      |birkhoffAverage ℝ T φ n y - c| ≤ ε := by
  obtain ⟨N, hN, hN'⟩ := h ε hε
  exact ⟨N, hN, fun n hn y hy => by
    rw [← birkhoffAverage_comp_section_on hΩ hπ hG φ n hy]
    exact hN' n hn (s y) (hs y hy)⟩

end Section

/-! ## The transfer of `UniformBirkhoff` from the split interval to the exchange -/

/-- **The last step of Theorem 2**: uniform convergence on the split interval, transferred to the
interval exchange along the right-germ section.

`G` is the germ map on the split interval `X` over the split set `D`, `π` the projection, `T` the
exchange, and `μ` the invariant measure of `G` which projects to Lebesgue measure `unitMeas`.  The
hypothesis `hG` is exactly `germMap_rightGerm`, and `hint` is the measure-theoretic statement that
the lifted measure projects to `unitMeas`.  `T` is a bundled exchange, and the convergence is stated
for its underlying function `⇑T`; the iterate of the group power is the iterate of that function
(`pow_apply_iterate`).

The convergence hypothesis is asked only on a set `S` containing the section of `[0,1)`, not on all
of `X`: this is what makes the theorem applicable, since the split space has two isolated fixed
points (`leftGerm 0`, `rightGerm 1`) outside the dynamics, at which the averages do not converge to
`∫ ψ dμ` — Blueprint 2, Remark 2.7.  The correct `S` is `SplitI.rightPart`. -/
theorem uniformBirkhoff_of_split {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (G : X → X) (π : X → ℝ) (sec : ℝ → X) (T : IET 0 1) (μ : Measure X)
    (hπc : Continuous π)
    (hTIco : ∀ x ∈ Set.Ico (0 : ℝ) 1, ⇑T x ∈ Set.Ico (0 : ℝ) 1)
    (S : Set X) (hS : ∀ x ∈ Set.Ico (0 : ℝ) 1, sec x ∈ S)
    (hsec : ∀ x ∈ Set.Ico (0 : ℝ) 1, π (sec x) = x)
    (hG : ∀ x ∈ Set.Ico (0 : ℝ) 1, G (sec x) = sec (⇑T x))
    (hconv : ∀ ψ : X → ℝ, Continuous ψ → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
      ∀ n ≥ N, ∀ z ∈ S, |birkhoffAverage ℝ G ψ n z - ∫ z, ψ z ∂μ| ≤ ε)
    (hint : ∀ φ : ℝ → ℝ, Continuous φ →
      ∫ z, φ (π z) ∂μ = ∫ y, φ y ∂unitMeas) :
    UniformBirkhoff T := by
  intro φ hφ ε hε
  have hφπ : Continuous fun z => φ (π z) := hφ.comp hπc
  have hunif := tendsto_uniform_birkhoffAverage_of_section
    (Ω := Set.Ico (0 : ℝ) 1) (S := S)
    hTIco hS hsec hG φ
    (c := ∫ z, φ (π z) ∂μ) (fun ε hε => by
      obtain ⟨N, hN, hN'⟩ := hconv (fun z => φ (π z)) hφπ ε hε
      exact ⟨N, hN, fun n hn x hx => hN' n hn x hx⟩) ε hε
  obtain ⟨N, hN, hN'⟩ := hunif
  refine ⟨N, hN, fun n hn x hx => ?_⟩
  have h1 := hN' n hn x hx
  rw [hint φ hφ] at h1
  exact h1

/-- **The two limits agree**: if the lift `μ` of Lebesgue measure on the split interval projects
to Lebesgue measure, then the integral of a lift `φ ∘ π` against `μ` is the integral of `φ`
against Lebesgue measure.  This is what discharges the hypothesis `hint` of
`uniformBirkhoff_of_split` from the measure-theoretic transfer (`MeasPrep.lift_unique_on_Ico`). -/
theorem integral_comp_of_map_eq {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {π : X → ℝ} (hπ : Continuous π) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hpush : μ.map π = unitMeas) :
    ∫ z, φ (π z) ∂μ = ∫ y, φ y ∂unitMeas := by
  rw [← hpush]
  exact (integral_map hπ.measurable.aemeasurable hφ.aestronglyMeasurable).symm

/-- **The last step of Theorem 2, in the split-interval setting**: if the germ map of the split
interval over `D` has uniformly convergent Birkhoff averages with limit given by a measure `μ`
which projects to Lebesgue measure, then the exchange is uniquely ergodic. -/
theorem uniformBirkhoff_of_proj {D : Set ℝ} [Countable D] (G : SplitI D → SplitI D)
    (T : IET 0 1)
    (μ : Measure (SplitI D))
    (hTIco : ∀ x ∈ Set.Ico (0 : ℝ) 1, ⇑T x ∈ Set.Ico (0 : ℝ) 1)
    (hG : ∀ x (hx : x ∈ Set.Ico (0 : ℝ) 1),
      G (SplitI.rightGerm x ⟨hx.1, le_of_lt hx.2⟩)
        = SplitI.rightGerm (⇑T x) ⟨(hTIco x hx).1, (hTIco x hx).2.le⟩)
    (hconv : ∀ ψ : SplitI D → ℝ, Continuous ψ → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∀ z ∈ SplitI.rightPart D,
        |birkhoffAverage ℝ G ψ n z - ∫ z, ψ z ∂μ| ≤ ε)
    (hpush : μ.map SplitI.proj = unitMeas) :
    UniformBirkhoff T := by
  refine uniformBirkhoff_of_split G SplitI.proj
    (fun y => SplitI.rightGerm (clampI y) (clampI_mem y)) T μ SplitI.continuous_proj hTIco
    (SplitI.rightPart D) ?_ ?_ ?_ hconv ?_
  · intro x hx
    simpa only [clampI_eq_self ⟨hx.1, le_of_lt hx.2⟩] using SplitI.rightGerm_mem_rightPart hx
  · intro x hx
    rw [SplitI.proj_rightGerm, clampI_eq_self ⟨hx.1, le_of_lt hx.2⟩]
  · intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, le_of_lt hx.2⟩
    have hsec : SplitI.rightGerm (D := D) (clampI x) (clampI_mem x)
        = SplitI.rightGerm (D := D) x hxIcc := by
      simp only [clampI_eq_self hxIcc]
    have hsec2 : SplitI.rightGerm (D := D) (⇑T x) ⟨(hTIco x hx).1, (hTIco x hx).2.le⟩
        = SplitI.rightGerm (D := D) (clampI (T x)) (clampI_mem (T x)) := by
      simp only [clampI_eq_self ⟨(hTIco x hx).1, (hTIco x hx).2.le⟩]
    rw [hsec, hG x hx]
    exact hsec2
  · intro φ hφ
    exact integral_comp_of_map_eq SplitI.continuous_proj hφ hpush

end IntervalExchange.UniqueErgodicity

end
