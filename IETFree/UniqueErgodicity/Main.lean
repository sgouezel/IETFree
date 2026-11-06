/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.UniqueErgodicity.Basic
public import IETFree.UniqueErgodicity.MainTheorem

/-!
# The a.e. Birkhoff form of Masur–Veech

`masurVeech_ae_unique_invariant_perm` states that for almost every length vector of the simplex the
exchange `mkIET1' lam π h` has a unique invariant probability measure carried by `[0, 1)`.  That
measure is Lebesgue measure on `[0, 1)`: the latter is invariant
(`InvariantMeasure.invariant_unitMeas`) and has mass `1` there, so the uniqueness forces the two to
coincide.

This measure form *is* unique ergodicity (`UniqueErgodic`, `IETFree/IET.lean`): Theorem 2
(`UniqueErgodicity.uniformBirkhoff_mkIET1`, and `uniformBirkhoff_of_uniqueErgodic` for an arbitrary
exchange) upgrades it to uniform convergence of the Birkhoff averages, and Lemma 2.9
(`UniqueErgodicity.exists_uniform_birkhoff`) is the form the free-group development consumes.

Nothing else is used: no positivity of the lengths, and no condition on the left limit.
-/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

namespace IETFree.UniqueErgodicity

/-- Lebesgue measure on `[0, 1)` has mass `1` on `[0, 1)`. -/
theorem unitMeas_Ico : unitMeas (Set.Ico (0 : ℝ) 1) = 1 := by
  rw [unitMeas, Measure.restrict_apply measurableSet_Ico, Set.inter_self,
    Real.volume_Ico, sub_zero, ENNReal.ofReal_one]

/-- Lebesgue measure on `[0, 1)` has no atoms: this is the `hlam` hypothesis of
`MeasPrep.lift_unique_on_Ico`. -/
theorem unitMeas_singleton (x : ℝ) : unitMeas {x} = 0 := by
  rw [unitMeas, Measure.restrict_apply (measurableSet_singleton x)]
  exact measure_mono_null Set.inter_subset_left Real.volume_singleton

end IETFree.UniqueErgodicity

end
