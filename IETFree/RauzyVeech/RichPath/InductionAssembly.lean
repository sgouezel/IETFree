/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.RauzyVeech.RichPath.MassGrowth
import IETFree.RauzyVeech.RichPath.LevelMass
import IETFree.RauzyVeech.RichPath.Potential

/-!
# The induction step, from `Γ₂` and `Γ₃`: the assembly

Contents (namespace `Assemble`):

* the `Γ₂`-mass `g2Mass`, with `g2Mass_pos`;
* `straddleMass_of_cards_ge_two`: the reduction of the `Γ₃` mass estimate to the card form for `2 ≤
  #A'`;
* the `Γ₂`-free assembly of the induction step: `balanceStep_of_straddleMass` and
  `inductionStep_of_straddleMass`.

The unconditional proof of the `Γ₃` estimate itself is in
`IETFree/RauzyVeech/RichPath/Potential.lean`
 (`Potential.straddleMassCard_of_unclean`). Axiom-clean.
-/

open Finset
open scoped BigOperators

namespace Assemble

open IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 2. The unclean family carries less than a half  The two statements below are the same
inequality written from the two sides (see §3); both are restricted to the node that
the `Γ₃` estimate actually asks about — `Cb`-balanced and **straddling** — and to a *single* level
`N` that already covers every word by a threshold crossing.  This is a genuine weakening of the
earlier formulation, which quantifies over every node (blocked ones included) and every level. -/

/-! ## 5. The assembly above `Γ₃`, with `Γ₂` discharged  `Γ₂` is unconditional
(`MassGrowth.exists_extMassGen_sharp`: a single minimal exit word gives the mass `(1+ε)·(1 +
2^L·Cb)^L`), so the only input left is the `Γ₃` estimate, which is
`Potential.straddleMassCard_of_unclean`. -/

/-- The mass constant of the sharp `Γ₂` at diagram diameter `L`, at `ε = 1`. -/
noncomputable def g2Mass (L : ℕ) : ℝ → ℝ := fun Cb => 2 * (1 + 2 ^ L * Cb) ^ L

theorem g2Mass_pos (L : ℕ) {Cb : ℝ} (hCb : 1 ≤ Cb) : 0 < g2Mass L Cb := by
  have h1 : (0 : ℝ) < 1 + 2 ^ L * Cb := by
    have : (0 : ℝ) ≤ 2 ^ L * Cb := by positivity
    linarith
  exact mul_pos (by norm_num) (pow_pos h1 L)

/-- **`NodeHeight.BalanceStep`**, unconditionally: the sharp `Γ₂` plus
`balanceStep_of_extMassGen`, fed by the unconditional `Γ₃` estimate
`Potential.straddleMassCard_of_unclean`. -/
theorem balanceStep_of_straddleMass (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∃ L : ℕ, NodeHeight.BalanceStep P (Induction.KeeGen (α := α) (g2Mass L) (2 ^ L)) := by
  obtain ⟨L, hB⟩ := MassGrowth.exists_extMassGen_sharp P hP hn
  have hB2 : Induction.ExtMassGen P (fun Cb : ℝ => 2 * (1 + 2 ^ L * Cb) ^ L) (2 ^ L) := by
    simpa only [one_add_one_eq_two] using hB 1 one_pos
  exact ⟨L, Induction.balanceStep_of_extMassGen P hP hn (M := g2Mass L) (C2 := 2 ^ L)
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (fun Cb hCb => g2Mass_pos L hCb)
    hB2 (fun Cb hCb k A' w hcard hklt hne hbal hex =>
      Potential.straddleMassCard_of_unclean P hP hn k Cb hCb A' w hcard hklt hne hbal hex)⟩

/-- **`InductionStep`**, unconditionally. -/
theorem inductionStep_of_straddleMass (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    Induction.InductionStep P := by
  obtain ⟨L, hbal⟩ := balanceStep_of_straddleMass P hP hn
  refine Induction.inductionStep_of_balance P hbal ?_
  intro Cb hCb
  exact le_of_lt (Induction.one_lt_KeeGen (M := g2Mass L) (C2 := 2 ^ L) (Cb := Cb)
    (g2Mass_pos L hCb) (by positivity) hCb)

end Assemble

