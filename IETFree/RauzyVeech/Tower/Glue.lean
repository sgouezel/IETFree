/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.ClosureSimplex
public import IETFree.RauzyVeech.InvariantMeasure

/-!
# From the tower formula to the `qApply` hypothesis of the ray criterion

`eq_of_nonneg_preimage_of_diam` wants the length vector of an invariant measure written
as `qApply (Q (γ k)) (y k)` with `y k ≥ 0`.  The level-`n` tower formula gives it as an
`ℝ≥0∞`-valued sum with coefficients `(Q a b).toNat`.  This file is the translation: `Measure.real`
is `toReal`, the sum of `toReal`s is the `toReal` of the sum when everything is finite, and `(Q a
b).toNat : ℝ = Q a b` because `Q` has nonnegative entries. -/

@[expose] public section

open MeasureTheory Matrix Filter
open scoped NNReal ENNReal BigOperators Topology

namespace IntervalExchange.RauzyVeech

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- **The `qApply` form of the tower formula.** If the mass of each bottom cell of `lam` is a
`Q`-combination of the masses of the cells `κ b`, with `Q` nonnegative, then the length vector of
`μ` in the original coordinates is `qApply Q` of the real masses of the `κ b`. -/
theorem real_eq_qApply (P : IETDatum₂ α n) (μ : Measure ℝ) {lam : α → ℝ≥0} {γ : List Bool}
    {κ : α → Set ℝ}
    (hQ : ∀ a b, 0 ≤ IETDatum₂.Path.Q P γ a b)
    (hfin : ∀ b, μ (κ b) ≠ ⊤)
    (htower : ∀ a, μ (cellOf P lam a)
      = ∑ b, (((IETDatum₂.Path.Q P γ a b).toNat : ℝ≥0∞)) * μ (κ b)) :
    (fun a => μ.real (cellOf P lam a))
      = qApply (IETDatum₂.Path.Q P γ) (fun b => (μ (κ b)).toReal) := by
  funext a
  have hne (b) : (((IETDatum₂.Path.Q P γ a b).toNat : ℝ≥0∞)) * μ (κ b) ≠ ⊤ := ENNReal.mul_ne_top
      (by simp) (hfin b)
  rw [Measure.real, htower a, ENNReal.toReal_sum (fun b _ => hne b)]
  rw [qApply_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hcoee : (((IETDatum₂.Path.Q P γ a b).toNat : ℕ) : ℝ) = (IETDatum₂.Path.Q P γ a b : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (hQ a b)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, hcoee]

/-- **From the tower formula to the ray criterion.** If the cylinders along a path through `lam`
shrink to
`lam` (nested, bounded, diameters `→ 0`) and the length vector of an invariant probability measure
on `[0,1)` lies in `qApply (Q (w k))` of a nonnegative vector for every `k` — which is what the
level-`n` tower formula gives — then that length vector *is* `lam`. So the ray parameter is `c = 1`.
-/
theorem ray_of_shrink_and_tower (P : IETDatum₂ α n) {lam : α → ℝ≥0} (hlam : lam ∈ simplex α)
    {w : ℕ → List Bool}
    (hmem : ∀ k, lam ∈ IETDatum₂.simplexCyl P (w k))
    (hanti : Antitone fun k => IETDatum₂.simplexCyl P (w k))
    (hbdd : Bornology.IsBounded (IETDatum₂.simplexCyl P (w 0)))
    (hdiam : Tendsto (fun k => Metric.diam (IETDatum₂.simplexCyl P (w k))) atTop (𝓝 0))
    (μ : ProbabilityMeasure ℝ) (hmass : (μ : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1)
    (htower : ∀ k, ∃ y : α → ℝ, (∀ a, 0 ≤ y a) ∧
      (fun a => lambdaOf μ P lam a)
        = qApply (IETDatum₂.Path.Q P (w k)) y) :
    ∃ c : ℝ, (fun a => lambdaOf μ P lam a) = c • (fun a => (lam a : ℝ)) := by
  have hsum : ∑ a, lambdaOf μ P lam a = 1 :=
    sum_lambdaOf P μ hlam hmass
  refine ⟨1, ?_⟩
  rw [one_smul]
  exact eq_of_nonneg_preimage_of_diam P hanti hbdd hdiam hmem hsum
    (fun k a => (htower k).choose_spec.1 a)
    (fun k => (htower k).choose_spec.2)

end IntervalExchange.RauzyVeech

end
