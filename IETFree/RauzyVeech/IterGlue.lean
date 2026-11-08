/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.Nesting
public import IETFree.RauzyVeech.TrueStep

/-!
# The one-step length identity

`hatLam ε lam` is the inverse of `rvMat ε` on length vectors, *provided the type condition* `λ (last
(!ε)) ≤ λ (last ε)` holds — `hatLam` uses truncated subtraction, so without it the identity fails.
This is the one-step input of `IsRauzyPath` for the greedy path. -/

@[expose] public section

open MeasureTheory Matrix
open scoped BigOperators ENNReal NNReal

namespace IntervalExchange.RauzyVeech

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

theorem qApply_rvMat_hatLam (P : IETDatum₂ α n) (ε : Bool)
    (hne : P.last ε ≠ P.last (!ε)) (lam : α → ℝ≥0)
    (hle : lam (P.last (!ε)) ≤ lam (P.last ε)) :
    qApply (P.rvMat ε) (fun a => (hatLam P ε lam a : ℝ))
      = fun a => (lam a : ℝ) := by
  funext a
  rw [qApply_apply]
  have hdiag (b : α) :
    (P.rvMat ε a b : ℝ)
      = (if a = b then 1 else 0) + (if a = P.last ε ∧ b = P.last (!ε) then 1 else 0) := by
    rw [IETDatum₂.rvMat]
    split_ifs with h1 h2 <;> simp_all
  have hval (b : α) :
    (hatLam P ε lam b : ℝ)
      = (lam b : ℝ) - (if b = P.last ε then (lam (P.last (!ε)) : ℝ) else 0) := by
    rw [hatLam]
    by_cases hb : b = P.last ε
    · rw [hb, ite_eq_left rfl, ite_eq_left rfl, NNReal.coe_sub hle]
    · rw [ite_eq_right hb, ite_eq_right hb, sub_zero]
  have hle' : (lam (P.last (!ε)) : ℝ) ≤ (lam (P.last ε) : ℝ) := by exact_mod_cast hle
  calc ∑ b, (P.rvMat ε a b : ℝ) * (hatLam P ε lam b : ℝ)
      = ∑ b, (if a = b then (lam b : ℝ) - (if b = P.last ε then (lam (P.last (!ε)) : ℝ) else 0)
          else 0)
        + ∑ b, (if a = P.last ε ∧ b = P.last (!ε) then (hatLam P ε lam b : ℝ) else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hdiag b, add_mul, hval b]
        by_cases hab : a = b
        · subst hab; simp
        · simp [hab]
    _ = ((lam a : ℝ) - (if a = P.last ε then (lam (P.last (!ε)) : ℝ) else 0))
        + (if a = P.last ε then (hatLam P ε lam (P.last (!ε)) : ℝ) else 0) := by
        have hsplit (b : α) :
          (if a = P.last ε ∧ b = P.last (!ε) then (hatLam P ε lam b : ℝ) else 0)
              = if b = P.last (!ε) then
                  (if a = P.last ε then (hatLam P ε lam b : ℝ) else 0) else 0 := by
          by_cases h1 : a = P.last ε <;> by_cases h2 : b = P.last (!ε) <;> simp [h1, h2]
        rw [Finset.sum_congr rfl fun b _ => hsplit b, Finset.sum_ite_eq]
        simp
    _ = (lam a : ℝ) := by
        by_cases ha : a = P.last ε
        · rw [ite_eq_left ha, ite_eq_left ha, hval, ite_eq_right (Ne.symm hne)]
          ring
        · rw [ite_eq_right ha, ite_eq_right ha, sub_zero, add_zero]

omit [DecidableEq α] in
/-- The type condition at a step, as an inequality of lengths. -/
theorem isRauzyStep_le (P : IETDatum₂ α n) {lam : α → ℝ≥0} {ε : Bool}
    (h : IsRauzyStep P lam ε) : lam (P.last (!ε)) ≤ lam (P.last ε) := by
  cases ε with
  | true => exact le_of_lt (isRauzyStep_true_iff P lam |>.mp h)
  | false => exact le_of_lt (isRauzyStep_false_iff P lam |>.mp h)

/-- **The renormalised length vector, transported along an `IsRauzyPath` word.** -/
theorem qApply_lamAfter (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) (lam : α → ℝ≥0) (hγ : IsRauzyPath P lam γ) :
    qApply (IETDatum₂.Path.Q P γ) (fun a => (lamAfter P γ lam a : ℝ))
      = fun a => (lam a : ℝ) := by
  induction γ generalizing P lam with
  | nil =>
    rw [qApply_eq]
    funext a
    simp [Matrix.one_apply]
  | cons e es ih =>
    have hstep : IsRauzyStep P lam e := by
      have := hγ
      rw [IsRauzyPath] at this
      exact this.1
    have hrest : IsRauzyPath (P.rvStep e) (hatLam P e lam) es := by
      have := hγ
      rw [IsRauzyPath] at this
      exact this.2
    rw [lamAfter_cons, IETDatum₂.Path.Q, qApply_mul,
      ih (P := P.rvStep e) (IETDatum₂.rvStep_irreducible P hP e) (hatLam P e lam) hrest]
    exact qApply_rvMat_hatLam P e (IETDatum₂.last_ne_last_not P hP hn e) lam
      (isRauzyStep_le P hstep)

end IntervalExchange.RauzyVeech

end
