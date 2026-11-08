/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.RichPath.LargeLetter

/-!
# The `k → k+1` dichotomy of the `Γ₃` step

The proof of AGY's distortion theorem has three steps at level `k`: `Γ₂` (extend each
minimal path to a vertex where a row end is outside `A'`), `Γ₃` (Kerckhoff bounds the
`A'`-coordinates) and `Γ₄` (a new large letter appears).  This library has `Γ₄`
(`newLetter_words`) and the assembly of the balance step from `Γ₃`
(`IETFree/RauzyVeech/RichPath/InductionAssembly.lean`); this file supplies the dichotomy that the
balance step consumes.

`dichotomy` is AGY's display in its `γ_s`-relative form with the constant `4·d·C₀·C₂`: from
a path `γ = γ_s γ_e` carrying the `Γ₃` bounds relative to `γ_s`, it produces `γ_s ≤ γ₁ ≤ γ_s γ_e`
and a letter `θ ∉ A'` with
`mkMass 1 (colSum P (w++γ₁)) ≤ 4·d·C₀·C₂ · min {mmin (A' ∪ {θ}) (colSum P (w++γ₁)),
  mkMass 1 (colSum P w)}`,
so that `A'₁ = insert θ A'` is the `(k+1)`-subset.
-/

open Finset IntervalExchange.IETDatum₂
open scoped BigOperators

@[expose] public section

namespace IntervalExchange.RauzyVeech.RichPath

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

variable [Nonempty α]

/-! ## 1. The dichotomy of AGY, `γ_s`-relative and with `4·d·C₀·C₂` -/

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- **`Γ₄` in AGY's `γ_s`-relative form.**  Let `γ = γ_s (ν ++ [e])` be a continuation of `w`
lying in `Γ₃`: along `γ_e = ν ++ [e]` no `A'`-height exceeds `2·d·M(q_{w γ_s})`, and the last arrow
of `γ_e` either is an exit arrow (`A' → α ∖ A'`) or the maximum has already crossed the threshold.
Assume moreover that `A'` is `C₀`-balanced at `w γ_s` (`m_{A'}(q) ≥ M(q)/C₀`) and that `M(q_{w γ_s})
≤ C₂·M(q_w)` — AGY's `Γ₂` maximum-growth bound, which the node-relative
`newLetter_words` folds away by working at `w γ_s` directly.  Then there are `γ₁` with
`γ_s ≤ γ₁ ≤ γ_s γ_e` and a letter `θ ∉ A'` with
`mkMass 1 (colSum P (w++γ₁)) ≤ 4·d·C₀·C₂ · min {mmin (A' ∪ {θ}) (colSum P (w++γ₁)),
  mkMass 1 (colSum P w)}`,
which is AGY's conclusion with `A'₁ = insert θ A'` the `(k+1)`-subset. -/
theorem dichotomy (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w γs ν : List Bool) (e : Bool) (A' : Finset α) {C0 C2 : ℝ}
    (hA'ne : A'.Nonempty) (hC0 : 1 ≤ C0) (hC2 : 1 ≤ C2)
    (hbal : ∀ b ∈ A',
      (1 / C0) * mkMass 1 (colSum P (w ++ γs)) ≤ colSum P (w ++ γs) b)
    (hAN : ∀ i, i ≤ (ν ++ [e]).length → ∀ b ∈ A',
      colSum P ((w ++ γs) ++ (ν ++ [e]).take i) b ≤
        2 * (Fintype.card α : ℝ) * mkMass 1 (colSum P (w ++ γs)))
    (hlast : (P.vertex ((w ++ γs) ++ ν)).last e ∈ A' ∧
        (P.vertex ((w ++ γs) ++ ν)).last (!e) ∉ A'
      ∨ 2 * (Fintype.card α : ℝ) * mkMass 1 (colSum P (w ++ γs)) <
          mkMass 1 (colSum P ((w ++ γs) ++ (ν ++ [e]))))
    (hC2bd : mkMass 1 (colSum P (w ++ γs))
      ≤ C2 * mkMass 1 (colSum P w)) :
    ∃ γ₁ : List Bool, γs <+: γ₁ ∧ γ₁ <+: γs ++ (ν ++ [e]) ∧ ∃ θ : α, θ ∉ A' ∧
      mkMass 1 (colSum P (w ++ γ₁)) ≤
        4 * (Fintype.card α : ℝ) * C0 * C2 *
          min (mmin (insert θ A') (colSum P (w ++ γ₁)))
            (mkMass 1 (colSum P w)) := by
  obtain ⟨i, hi, θ, hθ, hbound⟩ :=
    newLetter_words P hP hn (w ++ γs) ν e A' hA'ne hC0 hbal hAN hlast
  have hw : (w ++ γs) ++ (ν ++ [e]).take i = w ++ (γs ++ (ν ++ [e]).take i) :=
    List.append_assoc w γs _
  rw [hw] at hbound
  refine ⟨γs ++ (ν ++ [e]).take i, List.prefix_append γs _,
    append_prefix_append γs (List.take_prefix i (ν ++ [e])), θ, hθ, ?_⟩
  -- the `C₂` bookkeeping: `C₂ ≥ 1` and `M(q_{w γ_s}) ≤ C₂·M(q_w)`
  have hxpos : 0 < mmin (insert θ A')
      (colSum P (w ++ (γs ++ (ν ++ [e]).take i))) :=
    mmin_pos ⟨θ, Finset.mem_insert_self θ A'⟩ fun b => colSum_pos P _ b
  have h4 : (0 : ℝ) ≤ 4 * (Fintype.card α : ℝ) * C0 := by
    have h1 : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by
      have := P.card_pos
      exact_mod_cast this
    have h2 : (0 : ℝ) < C0 := by linarith
    positivity
  have hstep : min (mmin (insert θ A')
        (colSum P (w ++ (γs ++ (ν ++ [e]).take i))))
      (mkMass 1 (colSum P (w ++ γs))) ≤
      C2 * min (mmin (insert θ A')
        (colSum P (w ++ (γs ++ (ν ++ [e]).take i))))
        (mkMass 1 (colSum P w)) := by
    rcases le_total (mmin (insert θ A')
        (colSum P (w ++ (γs ++ (ν ++ [e]).take i))))
        (mkMass 1 (colSum P w)) with hle | hle
    · rw [min_eq_left hle]
      exact le_trans (min_le_left _ _) (le_mul_of_one_le_left (le_of_lt hxpos) hC2)
    · rw [min_eq_right hle]
      exact le_trans (min_le_right _ _) hC2bd
  calc mkMass 1 (colSum P (w ++ (γs ++ (ν ++ [e]).take i)))
      ≤ 4 * (Fintype.card α : ℝ) * C0 *
          min (mmin (insert θ A')
            (colSum P (w ++ (γs ++ (ν ++ [e]).take i))))
            (mkMass 1 (colSum P (w ++ γs))) := hbound
    _ ≤ 4 * (Fintype.card α : ℝ) * C0 *
          (C2 * min (mmin (insert θ A')
            (colSum P (w ++ (γs ++ (ν ++ [e]).take i))))
            (mkMass 1 (colSum P w))) := mul_le_mul_of_nonneg_left hstep h4
    _ = 4 * (Fintype.card α : ℝ) * C0 * C2 *
          min (mmin (insert θ A')
            (colSum P (w ++ (γs ++ (ν ++ [e]).take i))))
            (mkMass 1 (colSum P w)) := by ring

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

end IntervalExchange.RauzyVeech.RichPath

end
