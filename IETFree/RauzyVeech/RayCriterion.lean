/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.Nesting

/-!
# Two steps of the ray criterion

`(A)` In a metric space, a sequence of sets through a common point `x`, with diameters tending to
`0`, has `⋂ n, closure (S n) = {x}`.

`(B)` A nonnegative real vector of total mass `1` lying in the cone `C(γ)` of a path is a point of
the cylinder `Δ(γ)`.  Consequently, if the cylinders of a family of words have the single common
point `lam`, then every nonnegative `Σ` of mass `1` in all the cones `C(w n)` equals `lam`.  This is
how the tower formula (`λ(μ) ∈ C(γ_n)` for all `n`, §10.4) and the shrinking of the cylinders
(§10.5) combine into "the length vector of an invariant measure lies in the ray of `lam`". -/

@[expose] public section

open MeasureTheory Metric Filter
open scoped NNReal ENNReal BigOperators Topology

namespace RayCriterion

/-- **(A)** A sequence of sets through a common point, with diameters tending to `0`, has
intersection of closures the single point. -/
theorem iInter_closure_eq_singleton {E : Type*} [MetricSpace E] {S : ℕ → Set E} {x : E}
    (hx : ∀ n, x ∈ S n) (hanti : Antitone S) (hbdd : Bornology.IsBounded (S 0))
    (hdiam : Tendsto (fun n => Metric.diam (S n)) atTop (𝓝 0)) :
    (⋂ n, closure (S n)) = {x} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    have hle : ∀ n, dist x y ≤ Metric.diam (S n) := by
      intro n
      have hy' : y ∈ closure (S n) := Set.mem_iInter.mp hy n
      have hx' : x ∈ S n := hx n
      have hb : Bornology.IsBounded (closure (S n)) :=
        Metric.isBounded_closure_of_isBounded (hbdd.subset (hanti (Nat.zero_le n)))
      rw [← Metric.diam_closure (S n)]
      exact Metric.dist_le_diam_of_mem hb (subset_closure hx') hy'
    have h0 : dist x y ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hdiam (Eventually.of_forall hle)
    have hxy : dist x y = 0 := le_antisymm h0 dist_nonneg
    exact (dist_eq_zero.mp hxy).symm
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Set.mem_iInter.mpr fun n => subset_closure (hx n)

/-! ## (B) The cone-to-cylinder step -/

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- A nonnegative vector of total mass `1` in the cone of a path is a point of its cylinder. -/
theorem mem_simplexCyl_of_cone (P : IETDatum₂ α n) {w : List Bool} {Sig : α → ℝ}
    (hSig0 : ∀ a, 0 ≤ Sig a) (hsum : ∑ a, Sig a = 1)
    (h : Sig ∈ IETDatum₂.cone (IETDatum₂.Path.Q P w)) :
    (fun a => (⟨Sig a, hSig0 a⟩ : ℝ≥0)) ∈ IETDatum₂.simplexCyl P w := by
  let x : α → ℝ≥0 := fun a => ⟨Sig a, hSig0 a⟩
  change x ∈ IETDatum₂.simplexCyl P w
  have hcoe : (fun a => ((x a : ℝ))) = Sig := rfl
  have hsumNN : (∑ a, x a) = 1 := by
    refine NNReal.coe_injective ?_
    rw [NNReal.coe_sum, NNReal.coe_one, hcoe]
    exact hsum
  have hmem : x ∈ simplexOn α := by
    change (∑ a, x a) = 1
    exact hsumNN
  rw [show IETDatum₂.simplexCyl P w
      = {y : α → ℝ≥0 | (fun a => (y a : ℝ)) ∈ IETDatum₂.cone (IETDatum₂.Path.Q P w) ∧
          y ∈ simplexOn α} from rfl]
  exact ⟨by rw [hcoe]; exact h, hmem⟩

end RayCriterion

end
