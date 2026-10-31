/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib

/-!
Statement file for the discovery run `ae-diophantine`: the library's `ae_diophantine`
(Proposition 2.5 of the paper), with the definitions inlined so that the file only imports
`Mathlib`.  The statement is checked against the library in `Tasks/Match.lean` once a proof is
ported.

The paper's proof (its Prop. 2.5): with `psi q = 1/q^c`, it suffices to show that almost surely
there are only finitely many integer vectors `(k, a, b)` with
`|k + sum a_i lam_i + sum b_j mu_j| < psi (sum |a_i| + sum |b_j|)`; the last coordinate of `lam`
(resp. `mu`) is `1 - sum`, so its contribution moves into the common integer `k`.  The easy
direction of Khintchine–Groshev then gives the result as soon as
`sum_q q^(d + e - 3) * psi q < infinity`, e.g. for `c = d + e - 1`.  Nothing deep: it is a
Borel–Cantelli argument — the solutions form a slightly thickened hyperplane, and the sum of their
measures over the varying integer vectors converges.

Orientation for this formalisation.  `simplexVolume d` is the pushforward of Lebesgue measure on the
free region `simplexRegion d = {v : Fin (d-1) → ℝ | (∀ i, 0 < v i) ∧ ∑ i, v i < 1}` under
`simplexMap d`, which sends `v` to the length vector whose first `d - 1` coordinates are `v` and
whose last coordinate is `1 - ∑ v`.  So it is enough to prove the statement almost everywhere on
`simplexRegion d × simplexRegion e` with respect to Lebesgue measure (a null set for that measure
pushes forward to a null set; `MeasureTheory.Measure.map_eq_zero_iff` or
`MeasureTheory.Measure.quasiMeasurePreserving_of_measurable` plus `ae_map_iff` are the tools).  In
those coordinates the linear form is *affine*, with integer coefficients, and its gradient has
`l1`-norm at least `max (coeffMax a) (coeffMax b)` (up to the fixed bookkeeping of the last
coordinate).  The two ingredients are then

* counting: `#{a : Fin d → ℤ | coeffMax a ≤ N} = (2N+1)^d`, so there are `O(N^(d+e-1))` vectors
  with `max (coeffMax a) (coeffMax b) = N`;
* measure: for an affine form with a gradient of `l1`-norm `≥ N` on a bounded region, the set where
  `|L| < C/N^c` has measure `≤ const * C/N^c` (Fubini in the coordinate where the gradient is
  large, or `MeasureTheory.measure_le`/`volume_le_diam`-style estimates).

Summing `N^(d+e-1) * C / N^c` over `N` converges for `c > d + e`; Borel–Cantelli
(`MeasureTheory.ae_eventually_notMem`-style, `ProbabilityTheory.measure_limsup_eq_zero` /
`ae_frequently` machinery, or `MeasureTheory.measure_limsup_eq_zero` for a
`∑ μ s_N < ∞` family) then gives the result.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-- The largest absolute value of the coefficients. -/
def coeffMax {d : ℕ} (a : Fin d → ℤ) : ℕ := Finset.univ.sup fun i => (a i).natAbs

/-- Definition 2.3: the pair `(lam, mu)` is Diophantine. -/
def IsDiophantine {d e : ℕ} (lam : Fin d → ℝ≥0) (mu : Fin e → ℝ≥0) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (a : Fin d → ℤ) (b : Fin e → ℤ),
    (∑ i, (a i : ℝ) * (lam i : ℝ) + ∑ j, (b j : ℝ) * (mu j : ℝ)) ≠ 0 →
      C / ((max (coeffMax a) (coeffMax b) : ℕ) : ℝ) ^ c ≤
        |∑ i, (a i : ℝ) * (lam i : ℝ) + ∑ j, (b j : ℝ) * (mu j : ℝ)|

/-- The simplex of length vectors of total mass `1`. -/
def simplex (d : ℕ) : Set (Fin d → ℝ≥0) := {lam | ∑ i, lam i = 1}

/-- The free region: the `d - 1` free coordinates are positive and have total mass less than `1`,
so that every coordinate of the image, including the last one `1 - ∑`, is positive. -/
def simplexRegion (d : ℕ) : Set (Fin (d - 1) → ℝ) :=
  {v | (∀ i, 0 < v i) ∧ ∑ i, v i < 1}

/-- The parametrisation of the simplex: the `d - 1` free coordinates, the last being `1 - ∑`. -/
noncomputable def simplexMap (d : ℕ) (v : Fin (d - 1) → ℝ) : Fin d → ℝ≥0 :=
  fun i =>
    if h : i.val + 1 = d then (1 - ∑ j, v j).toNNReal
    else (v ⟨i.val, by have := i.isLt; omega⟩).toNNReal

/-- **Lebesgue measure on the simplex**: Lebesgue measure on the `d - 1` free coordinates,
restricted to the region where their total mass is less than `1`, transported by the
parametrisation `lam_d = 1 - ∑_{i<d} lam_i`.  Almost every point of the image is in the simplex. -/
noncomputable def simplexVolume (d : ℕ) : Measure (Fin d → ℝ≥0) :=
  Measure.map (simplexMap d) (volume.restrict (simplexRegion d))

/-- **Proposition 2.5**: almost every pair of length vectors is Diophantine. -/
theorem ae_diophantine {d e : ℕ} (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
      p.1 ∈ simplex d → p.2 ∈ simplex e → IsDiophantine p.1 p.2 := by
  sorry
