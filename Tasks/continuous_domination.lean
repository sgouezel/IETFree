/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib

/-!
Statement file for the discovery run `continuous-domination`.

Lemma 2.9 of the paper needs the following: a finite union of half-open intervals admits a
continuous function above its indicator whose integral exceeds its measure by no more than `ε`.
The paper gets it from unique ergodicity after blowing up the singularities; in the Lean
development `UniqueErgodic` is assumed in its strong (uniform Birkhoff) form, so the only missing
ingredient is this approximation, which needs nothing but Mathlib.

The statement is checked against the library in `Tasks/Match.lean`.
-/

open MeasureTheory

/-- `S` is a finite union of half-open intervals `[a, b)`. -/
def IsFiniteUnionIntervals (S : Set ℝ) : Prop :=
  ∃ cuts : Finset ℝ, ∀ x : ℝ, x ∈ S ↔ ∃ a ∈ cuts, ∃ b ∈ cuts, a < b ∧ x ∈ Set.Ico a b

/-! A route that works, for orientation: `S = ⋃ p ∈ P, [p.1, p.2)` with `P` finite.  Its closure is
`⋃ p ∈ P, [p.1, p.2]`, a finite union of closed intervals, and `closure S \ S` is contained in the
finite set of the endpoints, hence null, so `volume (closure S) = volume S`.  By outer regularity
(`MeasurableSet.exists_isOpen_diff_lt`, which needs `volume S ≠ ⊤`) there is an open `U ⊇ closure S`
with `volume (U \ closure S) < ε`.  Urysohn (Mathlib: `exists_continuous_zero_one_of_isClosed`,
or `exists_continuous_forall_le_...`) gives a continuous `ψ` with `ψ = 1` on `closure S`, `ψ = 0`
outside `U` and `0 ≤ ψ ≤ 1`; then `ψ ≥ 1_S` and `∫ ψ ≤ volume U ≤ volume S + ε`.  (Summing naive
tent functions over `P` does not work when the pieces overlap.) -/

/-- **A finite union of half-open intervals has a continuous dominating function whose integral is
at most the measure of the set plus `ε`.** -/
theorem exists_continuous_indicator_le (S : Set ℝ) (hS : IsFiniteUnionIntervals S) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ (∀ x, 0 ≤ ψ x) ∧
      (∀ x, S.indicator (fun _ => (1 : ℝ)) x ≤ ψ x) ∧
      ∫ x, ψ x ≤ (volume S).toReal + ε := by
  sorry
