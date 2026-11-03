/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.RauzyVeech.FirstReturn
import IETFree.RauzyVeech.TowerLevelN

/-!
# The cell of the first-return map inside its domain cell

`cellHat_subset_dom` places the cell of the first-return map inside the corresponding domain cell of
the level-`k` exchange — the inclusion used by the tower decomposition. -/

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace TowerCells

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## 2. Inclusion of the levels -/

/-- The cell of the first return map sits inside the corresponding domain cell. -/
theorem cellHat_subset_dom (π' : Equiv.Perm (Fin n)) (L' : Fin n → ℝ≥0) (β : Fin n) :
    Tower.cellHat π' L' β ⊆ Set.Ico (leftEnd L' β) (upperEnd L' β) := by
  have h1 : leftEnd (Tower.lamHat π' L') β = leftEnd L' β := Tower.leftEnd_lamHat _ _ β
  have h2 : Tower.lamHat π' L' β ≤ L' β := by
    rw [Tower.lamHat]
    split
    · exact tsub_le_self
    · exact le_rfl
  have h2' : ((Tower.lamHat π' L') β : ℝ) ≤ (L' β : ℝ) := by exact_mod_cast h2
  intro y hy
  simp only [Tower.cellHat, Set.mem_Ico] at hy ⊢
  refine ⟨?_, ?_⟩
  · rw [← h1]; exact hy.1
  · have hle : upperEnd (Tower.lamHat π' L') β ≤ upperEnd L' β := by
      rw [upperEnd_eq, upperEnd_eq, h1]; linarith
    exact lt_of_lt_of_le hy.2 hle

end

end TowerCells
