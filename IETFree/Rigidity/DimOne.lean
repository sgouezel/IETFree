/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.Basic
import IETFree.RauzyVeech.Affine
import IETFree.RauzyVeech.SimplexAe

/-!
# The `d = 1` case of the root theorem

`veechRigidity` quantifies over `d` with `[NeZero d]` and **no** `2 ≤ d`, so `d = 1` is part of the
statement.  It is true and not vacuous: every `π : Equiv.Perm (Fin 1)` is irreducible and the
exchange `mkIET1' lam π h` is the identity on the simplex, so rigidity holds with `q n = n`,
`t = 0`, `B n = Set.Ico 0 1`.  This is the `d = 1` half of its proof.

Proofs taken from the probe of the audit `smvzfapws`/m1 (`A3Probe.lean`), where the `d = 1` branch
was first established; names and docstrings adapted.  Axioms: `[propext, Classical.choice,
Quot.sound]`.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators

namespace IETFree.Rigidity

/-! ## 1. The one-letter translation vector is zero -/

theorem translationVector_fin_one (π : Equiv.Perm (Fin 1)) (lam : Fin 1 → ℝ≥0) (i : Fin 1) :
    translationVector π lam i = 0 := by
  have himg : imageLeft π lam i = 0 := by
    simp only [imageLeft]
    have hempty : (Finset.univ.filter (fun j : Fin 1 => π j < π i)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j _hj
      rw [Subsingleton.elim j i]
      exact lt_irrefl _
    rw [hempty, Finset.sum_empty]
  have hleft : leftEnd lam i = 0 := by
    rw [Subsingleton.elim i 0]
    simp
  rw [translationVector, himg, hleft, sub_zero]

/-! ## 2. The one-letter exchange is the identity on the simplex -/

theorem mkIETFun_fin_one {lam : Fin 1 → ℝ≥0} (h : lam ∈ simplexOn (Fin 1))
    (π : Equiv.Perm (Fin 1)) (x : ℝ) : mkIETFun lam π 0 x = x := by
  have hsum : ∑ i, (lam i : ℝ) = 1 := by
    rw [← NNReal.coe_sum, h]
    simp
  unfold mkIETFun
  by_cases hx : x ∈ Set.Ico (0 : ℝ) (0 + ∑ i, (lam i : ℝ))
  · rw [dif_pos hx, translationVector_fin_one, add_zero]
  · rw [dif_neg hx]

theorem mkIETFun_fin_one_eq_id {lam : Fin 1 → ℝ≥0} (h : lam ∈ simplexOn (Fin 1))
    (π : Equiv.Perm (Fin 1)) : mkIETFun lam π 0 = id :=
  funext (mkIETFun_fin_one h π)

/-! ## 3. The `d = 1` case of the root, with the witnesses `q n = n`, `t = 0`, `B n = Ico 0 1` -/

theorem isRigidByTranslations_fin_one {lam : Fin 1 → ℝ≥0} (hm : lam ∈ simplex 1)
    (π : Equiv.Perm (Fin 1)) : IsRigidByTranslations (mkIET1' lam π hm) := by
  have hid := mkIETFun_fin_one_eq_id hm π
  refine ⟨fun n => n, fun _ => (0 : ℝ), fun _ => Set.Ico (0 : ℝ) 1,
    tendsto_id, tendsto_const_nhds, ?_, ?_, ?_, ?_⟩
  · intro n
    exact subset_rfl
  · intro n
    exact measurableSet_Ico
  · have hval : unitMeas.real (Set.Ico (0 : ℝ) 1) = 1 := by
      rw [unitMeas, Measure.real,
        Measure.restrict_apply measurableSet_Ico, Set.inter_self, Real.volume_Ico]
      norm_num
    simp only [hval]
    exact tendsto_const_nhds
  · intro n x _
    have hfun : ⇑(mkIET1' lam π hm) = mkIETFun lam π 0 := coe_mkIET1' lam π hm
    rw [IET.pow_apply_iterate, hfun, hid]
    simp

/-! ## 4. The a.e. form over `simplexVolume 1`, i.e. the `d = 1` instance of the root -/

theorem ae_fin_one (π : Equiv.Perm (Fin 1)) :
    ∀ᵐ lam ∂(simplexVolume 1), ∀ (hm : lam ∈ simplex 1),
      IsRigidByTranslations (mkIET1' lam π hm) := by
  rw [← simplexVolumeOn_fin 1]
  filter_upwards [ae_mem_simplexOn_of_nonempty (α := Fin 1)] with lam hlam hm
  exact isRigidByTranslations_fin_one hm π


end IETFree.Rigidity
