/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.FirstReturn

/-!
# Iterating the exchange: measurability, the level map, and the renormalised data

* `measurableSet_image_iterate`: an iterate of an exchange sends measurable sets to measurable
  sets (through `image_iterate_eq_preimage_symm`, which is `FirstReturn`'s);
* `mapsTo_mkIETFun`: an exchange maps its interval `[a, b)` into itself;
* the level cells `cellHat` of the tower, and their renormalised data.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace IntervalExchange.RauzyVeech

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## 1. Measurability of the floors -/

/-- **Every floor is measurable.** -/
theorem measurableSet_image_iterate (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0)
    {A : Set ℝ} (hA : MeasurableSet A) (j : ℕ) :
    MeasurableSet ((mkIETFun lam π 0)^[j] '' A) := by
  rw [image_iterate_eq_preimage_symm]
  exact hA.preimage (measurable_mkIETFun_symm_iterate π lam j)

/-! ## 2. Composing the two first returns -/

/-- The exchange preserves its own interval. -/
theorem mapsTo_mkIETFun (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (totalLength lam)) :
    mkIETFun lam π 0 y ∈ Set.Ico 0 (totalLength lam) := by
  have h : IsIET 0 (0 + totalLength lam) (mkIETFun lam π 0) :=
    isIET_mkIETFun lam π 0 (t := totalLength lam) le_rfl
  simpa using IsIET.mapsTo h (x := y) (by simpa using hy)

end

end IntervalExchange.RauzyVeech

end
