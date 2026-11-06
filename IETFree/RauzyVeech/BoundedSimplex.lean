/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.BalancedSet

/-!
# Boundedness of the simplex and of its path cylinders

`isBounded_simplexOn`: every coordinate of a point of `simplexOn α` is at most `1`.
`isBounded_simplexCyl`: the same for the path cylinders `simplexCyl P γ`.  These are the two
boundedness inputs of the ray criterion (`RayCriterion.eq_of_nonneg_preimage_of_diam`), and they are
kept beside two elementary lemmas: `colR_eq_sum` (a column sum of an integer matrix, read in `ℝ`)
and `dist_co_co` (the sup-distance on `α → ℝ≥0` is the distance of the coerced real vectors). -/

@[expose] public section


open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace BoundedSimplex

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 3. The vertices of a path cylinder  `Δ(γ) = cone Q ∩ Δ` is the image of the open simplex
under the matrix `M = Q diag(Q_β)⁻¹`; its closure is the convex hull of the columns of `Q`
normalised by the column sums: `v_b = Q e_b / Q_β`.  Every point of `Δ(γ)` is a *convex combination*
of the `v_b`, with explicit weights `Q_β · ŵ_b` where `ŵ = Q⁻¹ x` is the renormalised length vector.
-/

/-- The `b`-th column sum of an integer matrix, as a real number. -/
noncomputable def colR (M : Matrix α α ℤ) (b : α) : ℝ := ((∑ a, M a b : ℤ) : ℝ)

omit [DecidableEq α] in
theorem colR_eq_sum (M : Matrix α α ℤ) (b : α) : colR M b = ∑ a, (M a b : ℝ) := by
  rw [colR]
  push_cast
  rfl

omit [DecidableEq α] in
/-- Distances are computed by the sup-norm on the coordinates: the `ℝ≥0` and the `ℝ`
versions coincide. -/
theorem dist_co_co (x y : α → ℝ≥0) :
    dist (fun a => (x a : ℝ)) (fun a => (y a : ℝ)) = dist x y := by
  rw [dist_pi_def, dist_pi_def]
  exact congrArg (fun r : ℝ≥0 => (r : ℝ))
    (Finset.sup_congr rfl fun a _ => rfl)

/-! ## 5. Boundedness of the simplex, and the vertices as limits of cylinder points -/

omit [DecidableEq α] in
/-- The simplex is bounded: every coordinate is at most `1`. -/
theorem isBounded_simplexOn : Bornology.IsBounded (simplexOn α) := by
  refine Metric.isBounded_iff.mpr ⟨1, fun x hx y hy => ?_⟩
  have hx1 (a) : (x a : ℝ) ≤ 1 := by
    rw [mem_simplexOn] at hx
    have h := Finset.single_le_sum (f := fun a => x a) (fun a _ => (x a).2)
      (Finset.mem_univ a)
    rw [hx] at h
    exact_mod_cast h
  have hy1 (a) : (y a : ℝ) ≤ 1 := by
    rw [mem_simplexOn] at hy
    have h := Finset.single_le_sum (f := fun a => y a) (fun a _ => (y a).2)
      (Finset.mem_univ a)
    rw [hy] at h
    exact_mod_cast h
  rw [dist_pi_le_iff zero_le_one]
  intro a
  have h1 := hx1 a
  have h2 := hy1 a
  have h3 : (0 : ℝ) ≤ (x a : ℝ) := (x a).2
  have h4 : (0 : ℝ) ≤ (y a : ℝ) := (y a).2
  rw [NNReal.dist_eq, abs_sub_le_iff]
  constructor <;> linarith

/-- The path cylinders are bounded. -/
theorem isBounded_simplexCyl (P : IETDatum₂ α n) (γ : List Bool) :
    Bornology.IsBounded (IETDatum₂.simplexCyl P γ) :=
  isBounded_simplexOn.subset (fun _ hx => hx.2)

/-! ## 6. The diameter half of Lemma 2 -/

end BoundedSimplex

end
