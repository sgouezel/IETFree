/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.RichPath.RichPathAssembly

/-!
# The balance constant of the induction step

The `Γ₃` mass estimate of the induction is the statement of
`straddleMassCard_of_goodMass_straddle` (from a clean-stop mass bound) and
`straddleMassCard_of_unclean` (unconditionally, for every cardinality), both in
`lean`.

This file keeps the other half of the step — the balance constant `balanceConstant` delivered by
`Γ₂`, and
the fact that `A'`-balance is preserved by the growth bound (`bal_of_growth`) — which
`MassFunction.balanceStep_of_extMassGen` consumes. -/

open Finset IntervalExchange.IETDatum₂
open scoped BigOperators

@[expose] public section

namespace IntervalExchange.RauzyVeech.RichPath

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. The balance constant delivered by the assembly -/

/-- `A'`-balance is preserved by the growth bound of `Γ₂`. -/
theorem bal_of_growth (P : IETDatum₂ α n) {Cb C2 : ℝ} (hC2 : 1 ≤ C2) (hCb : 1 ≤ Cb)
    {w w' : List Bool} {A' : Finset α}
    (hbal : ∀ b ∈ A', (1 / Cb) * mkMass 1 (colSum P w) ≤ colSum P w b)
    (hmono : ∀ b, colSum P w b ≤ colSum P w' b)
    (hgr : mkMass 1 (colSum P w') ≤ C2 * mkMass 1 (colSum P w)) (b : α) (hb : b ∈ A') :
    (1 / (C2 * Cb)) * mkMass 1 (colSum P w') ≤ colSum P w' b := by
  have h1 := hbal b hb
  have h3 := hmono b
  have hC2pos : (0 : ℝ) < C2 := by linarith
  have hCbpos : (0 : ℝ) < Cb := by linarith
  have h4 : (1 / (C2 * Cb)) * mkMass 1 (colSum P w')
      ≤ (1 / (C2 * Cb)) * (C2 * mkMass 1 (colSum P w)) :=
    mul_le_mul_of_nonneg_left hgr (by positivity)
  have h5 : (1 / (C2 * Cb)) * (C2 * mkMass 1 (colSum P w))
      = (1 / Cb) * mkMass 1 (colSum P w) := by
    field_simp
  linarith

end IntervalExchange.RauzyVeech.RichPath

end
