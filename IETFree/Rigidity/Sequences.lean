/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.TopBotFormalism
import IETFree.Rigidity.Veech

/-!
# From "arbitrarily large return times" to rigidity by translations

The almost-everywhere weak-rigidity statement `ae_rigid_step` says, for a.e. length vector and
every `ε > 0` and every
`N₀`, that there is an exact translation `x ↦ x + t` on a set of measure `≥ 1 - ε` after `q ≥ N₀`
steps.  Taking `ε k = 1/(k+1)` and `N₀ = k` turns it into the sequence form of
`IsRigidByTranslations`: `q k ≥ k` so `q → ∞`, `|t k| ≤ 1/(k+1)` so `t → 0`, and the measure of
`B k` is squeezed between `1 - 1/(k+1)` and `1`.

-/

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

namespace IETFree.Rigidity

/-- **(R2) implies rigidity by translations.**  For a.e. length vector, choose the data of the
a.e. statement at the precision `ε k = 1/(k+1)` and the target time `N₀ = k`; then `q k ≥ k`, so
`q → ∞`, `|t k| ≤ 1/(k+1)`, so `t → 0`, and the set `B k ⊆ [0,1)` has `unitMeas`-measure
`≥ 1 - 1/(k+1)`, so its measure tends to `1`. -/
theorem ae_isRigidByTranslations {α : Type*} [Fintype α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∀ᵐ lam ∂(simplexVolumeOn α), IsRigidByTranslations (P.toIET lam) := by
  classical
  filter_upwards [Internal.ae_rigid_step P hP hn] with lam hlam
  have hk : ∀ k : ℕ, ∃ (q : ℕ) (t : ℝ) (B : Set ℝ),
      k ≤ q ∧ |t| ≤ 1 / ((k : ℝ) + 1) ∧ B ⊆ Set.Ico (0:ℝ) 1 ∧ MeasurableSet B ∧
      1 - 1 / ((k : ℝ) + 1) ≤ (volume B).toReal ∧
      ∀ x ∈ B, (⇑(P.toIET lam))^[q] x = x + t :=
    fun k => hlam (1 / ((k : ℝ) + 1)) (by positivity) k
  choose q t B hq ht hsub hmeas hvol hex using hk
  refine ⟨q, t, B, ?_, ?_, hsub, hmeas, ?_, ?_⟩
  · exact tendsto_atTop_mono (fun k => hq k) tendsto_id
  · have hlo : Tendsto (fun k : ℕ => -(1 / ((k : ℝ) + 1))) atTop (nhds 0) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using h.neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      (fun k => (abs_le.mp (ht k)).1) (fun k => (abs_le.mp (ht k)).2)
  · -- the measure of `B k` is its volume, and it is sandwiched between `1 - 1/(k+1)` and `1`
    have hcoe : ∀ k, unitMeas.real (B k) = (volume (B k)).toReal := by
      intro k
      rw [unitMeas, Measure.real, Measure.restrict_apply (hmeas k),
        Set.inter_eq_left.mpr (hsub k)]
    have hIco : unitMeas (Set.Ico (0:ℝ) 1) = 1 := by
      rw [unitMeas, Measure.restrict_apply measurableSet_Ico, Set.inter_self,
        Real.volume_Ico]
      norm_num
    have hle : ∀ k, unitMeas.real (B k) ≤ 1 := by
      intro k
      have h1 : unitMeas (B k)
          ≤ unitMeas (Set.Ico (0:ℝ) 1) := measure_mono (hsub k)
      have hne : unitMeas (Set.Ico (0:ℝ) 1) ≠ ⊤ := by
        rw [hIco]
        simp
      calc unitMeas.real (B k)
          = (unitMeas (B k)).toReal := rfl
        _ ≤ (unitMeas (Set.Ico (0:ℝ) 1)).toReal :=
            ENNReal.toReal_mono hne h1
        _ = 1 := by rw [hIco]; simp
    have hlow : Tendsto (fun k : ℕ => 1 - 1 / ((k : ℝ) + 1)) atTop (nhds 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun k => by rw [hcoe k]; exact hvol k) hle
  · intro k x hx
    rw [IET.pow_apply_iterate]
    exact hex k x hx

end IETFree.Rigidity
