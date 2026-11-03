/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.RefiningPartition

/-!
# Injectivity of the length map: the measure-theoretic reduction

Two probability measures on `ℝ` carried by `[0, 1)` which agree on every atom of a refining sequence
of partitions of `[0, 1)` with mesh → `0` are equal.  This is the last step of the injectivity of
the length map: the towers supply the partitions (the level-`n` floors), the tower formula plus `det
Q(γ) = 1` supplies the agreement on atoms, and `RefiningPartition` does the rest. -/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators Topology

namespace LengthInjective

/-- A measure supported on `Ico 0 1` is its own restriction there. -/
theorem restrict_eq_of_ae_mem {μ : Measure ℝ} (h : ∀ᵐ x ∂μ, x ∈ Set.Ico (0 : ℝ) 1) :
    μ.restrict (Set.Ico (0:ℝ) 1) = μ :=
  Measure.restrict_eq_self_of_ae_mem h

/-- **Injectivity from a refining sequence of floor partitions.** -/
theorem measure_eq_of_floors {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (haeμ : ∀ᵐ x ∂μ, x ∈ Set.Ico (0 : ℝ) 1) (haeν : ∀ᵐ x ∂ν, x ∈ Set.Ico (0 : ℝ) 1)
    (Pf : ℕ → Finset (Set ℝ))
    (hmeas : ∀ k A, A ∈ Pf k → MeasurableSet A)
    (hsub : ∀ k A, A ∈ Pf k → A ⊆ Set.Ico (0 : ℝ) 1)
    (hcov : ∀ k x, x ∈ Set.Ico (0 : ℝ) 1 → ∃ A ∈ Pf k, x ∈ A)
    (hdisj : ∀ k A, A ∈ Pf k → ∀ B ∈ Pf k, A ≠ B → Disjoint A B)
    (href : ∀ k A, A ∈ Pf (k + 1) → ∃ B ∈ Pf k, A ⊆ B)
    (hmesh : ∀ ε > 0, ∀ᶠ k in atTop, ∀ A ∈ Pf k, ∀ x ∈ A, ∀ y ∈ A, dist x y < ε)
    (heq : ∀ k A, A ∈ Pf k → μ A = ν A) :
    μ = ν := by
  have hres := RefiningPartition.measure_restrict_eq_of_refining_partitions (μ := μ) (ν := ν)
    (Set.Ico (0:ℝ) 1) Pf hmeas hsub hcov hdisj href hmesh heq
  rw [restrict_eq_of_ae_mem haeμ, restrict_eq_of_ae_mem haeν] at hres
  exact hres

end LengthInjective

end
