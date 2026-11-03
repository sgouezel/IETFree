/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.FirstReturn

/-!
# Iterating the exchange: measurability, the level map, and the renormalised data

* `image_iterate_eq_preimage_symm`, `measurableSet_image_iterate`: an iterate of an exchange sends
  measurable sets to measurable sets;
* `mapsTo_exch`: an exchange maps its interval `[a, b)` into itself;
* the level cells `cellHat` of the tower, and their renormalised data.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace TowerN

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## 1. Measurability of the floors -/

/-- The `j`-th iterate of the exchange applied to `A`, as the preimage under the `j`-th iterate of
the inverse exchange: this is the missing measurability input of the tower decomposition. -/
theorem image_iterate_eq_preimage_symm (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (j : ℕ)
    (A : Set ℝ) :
    (Tower.exch π lam)^[j] '' A = ((⇑(Tower.exchEquiv π lam).symm)^[j]) ⁻¹' A := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    change (⇑(Tower.exchEquiv π lam).symm)^[j] ((⇑(Tower.exchEquiv π lam))^[j] a) ∈ A
    rw [Tower.exch_symm_apply_iterate π lam j a]
    exact ha
  · intro hx
    exact ⟨_, hx, Tower.exch_apply_iterate_symm π lam j x⟩

/-- **Every floor is measurable.** -/
theorem measurableSet_image_iterate (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0)
    {A : Set ℝ} (hA : MeasurableSet A) (j : ℕ) :
    MeasurableSet ((Tower.exch π lam)^[j] '' A) := by
  rw [image_iterate_eq_preimage_symm]
  exact hA.preimage (Tower.measurable_exch_symm_iterate π lam j)

/-! ## 3. The level-two objects: the renormalised exchange at the vertex `P → false`

The first return map of `T` to `[0, cut π lam)` is the exchange of the data at the vertex `P →
false`: same alphabet, permutation `piHat π` and lengths `lamHat π lam`.  The level-two cells and
return times are therefore those of `Tower.cellHat (piHat π) (lamHat π lam)` and `Tower.returnB
(piHat π)` on the interval `[0, tot (lamHat π lam)) = [0, cut π lam)`. -/

/-! ## 4. Composing the two first returns -/

/-- The exchange preserves its own interval. -/
theorem mapsTo_exch (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) {y : ℝ}
    (hy : y ∈ Set.Ico 0 (Tower.tot lam)) :
    Tower.exch π lam y ∈ Set.Ico 0 (Tower.tot lam) := by
  have h : IsIET 0 (0 + Tower.tot lam) (Tower.exch π lam) :=
    isIET_mkIETFun lam π 0 (t := Tower.tot lam) le_rfl
  simpa using IsIET.mapsTo h (x := y) (by simpa using hy)

/-! ## 5. All levels: the word of type `false` repeated `k` times

The level-`k` objects are indexed by the vertex reached after `k` Rauzy steps of type `false`. The
level-`(k+1)` cell of `β` is `Tower.cellHat (permAfter π k) (lamAfter π lam k) β`, which is exactly
the cell `Ico (leftEnd (lamAfter π lam (k+1)) β) (upperEnd (lamAfter π lam (k+1)) β)` of the
exchange `mkIETFun (lamAfter π lam (k+1)) (permAfter π (k+1)) 0` at that vertex.  The lemmas below
say, uniformly in `k`, that the level-`(k+1)` cells refine the level-`k` ones, that the level-`k`
base splits into the floors of the level-`(k+1)` towers, and that the level-`(k+1)` base is reached
from every point of the level-`k` base. -/

end

end TowerN

end
