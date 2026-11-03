/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.IterGlue
public import IETFree.RauzyVeech.RauzyPath

/-!
# `IterOK` glue, part 2: the greedy path is an `IterOK` word

The a.e. greedy path (`RauzyPath.pathWord`, built by choosing at each step the child cylinder that
contains the point) satisfies `IterOK` — the Rauzy type rule — and its renormalised length vector
(`Tower.lamAfter`) stays strictly positive.  The two statements are proved simultaneously:
positivity is what lets `IsRenorm.unique` identify the comparison from `mem_simplexCyl_append_iff`
with the `StepOK` of the algorithm. -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace IterGlue2

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- `IterOK` splits at the last letter of the word. -/
theorem iterOK_append_singleton (P : IETDatum₂ α n) (lam : α → ℝ≥0) (γ : List Bool) (e : Bool) :
    TowerTrue.IterOK P lam (γ ++ [e]) ↔
      TowerTrue.IterOK P lam γ ∧
        TowerTrue.StepOK (IETDatum₂.vertex P γ) (Tower.lamAfter P γ lam) e := by
  induction γ generalizing P lam with
  | nil =>
    rw [List.nil_append]
    simp [TowerTrue.IterOK, IETDatum₂.vertex, Tower.lamAfter]
  | cons b bs ih =>
    have hb := ih (P := P.rvStep b) (lam := Tower.hatLam P b lam)
    have hun1 : TowerTrue.IterOK P lam (b :: (bs ++ [e]))
        = (TowerTrue.StepOK P lam b ∧
            TowerTrue.IterOK (P.rvStep b) (Tower.hatLam P b lam) (bs ++ [e])) := rfl
    have hun2 : TowerTrue.IterOK P lam (b :: bs)
        = (TowerTrue.StepOK P lam b ∧
            TowerTrue.IterOK (P.rvStep b) (Tower.hatLam P b lam) bs) := rfl
    rw [List.cons_append, hun1, hun2, hb, Tower.lamAfter_cons, IETDatum₂.vertex_cons]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2.1⟩, h2.2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩

omit [DecidableEq α] in
/-- The type rule in the form of a strict comparison at the last letters. -/
theorem stepOK_last_iff (P : IETDatum₂ α n) (lam : α → ℝ≥0) (ε : Bool) :
    TowerTrue.StepOK P lam ε ↔ lam (P.last (!ε)) < lam (P.last ε) := by
  cases ε <;>
    simp [TowerTrue.stepOK_true_iff, TowerTrue.stepOK_false_iff]

/-- `lamAfter` splits at the last letter of the word. -/
theorem lamAfter_append_singleton (P : IETDatum₂ α n) (lam : α → ℝ≥0) (γ : List Bool) (e : Bool) :
    Tower.lamAfter P (γ ++ [e]) lam
      = Tower.hatLam (IETDatum₂.vertex P γ) e (Tower.lamAfter P γ lam) := by
  induction γ generalizing P lam with
  | nil => rw [List.nil_append]; rfl
  | cons b bs ih =>
    rw [List.cons_append, Tower.lamAfter_cons, IETDatum₂.vertex_cons,
      ih (P := P.rvStep b) (Tower.hatLam P b lam), Tower.lamAfter_cons]

/-- **The greedy path is an `IterOK` word, with a positive renormalised vector.** Proved
simultaneously: positivity is what lets `IsRenorm.unique` identify the renormalised vector produced
by `mem_simplexCyl_append_iff` with `lamAfter`, turning the strict length comparison of the child
cylinder into the algorithm's `StepOK`. -/
theorem iterOK_pathWord (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {x : α → ℝ≥0} (h0 : x ∈ IETDatum₂.simplexCyl P [])
    (hstop : ∀ γ : List Bool, x ∉ IETDatum₂.cylStop P γ) :
    ∀ k, TowerTrue.IterOK P x (IETDatum₂.pathWord P x k) ∧
      (∀ a, 0 < Tower.lamAfter P (IETDatum₂.pathWord P x k) x a) := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · change True; trivial
    · change ∀ a, 0 < x a
      exact (IETDatum₂.mem_simplexCyl_nil_iff P x).mp h0 |>.2
  | succ k ih =>
    obtain ⟨hOK, hpos⟩ := ih
    set γ := IETDatum₂.pathWord P x k with hγ
    set e := IETDatum₂.pathStep P x k with he
    have hstep : IETDatum₂.pathWord P x (k + 1) = γ ++ [e] := IETDatum₂.pathWord_succ P x k
    have hmem : x ∈ IETDatum₂.simplexCyl P (γ ++ [e]) := by
      rw [← hstep]
      exact IETDatum₂.mem_pathWord P hP hn h0 hstop (k + 1)
    obtain ⟨w, hw, hlt⟩ :=
      (IETDatum₂.mem_simplexCyl_append_iff P hP hn γ e x).mp hmem |>.2
    -- `lamAfter` is the same renormalised vector
    have hren : IETDatum₂.IsRenorm P γ x (fun a => (Tower.lamAfter P γ x a : ℝ)) := by
      refine (IETDatum₂.isRenorm_iff P γ x _).mpr ⟨hpos, ?_⟩
      have hq := IterGlue.qApply_lamAfter P hP hn γ x hOK
      rw [← hq]
    have hw_eq : w = fun a => (Tower.lamAfter P γ x a : ℝ) :=
      IETDatum₂.IsRenorm.unique hP hn hw hren
    have hcmp : Tower.lamAfter P γ x ((IETDatum₂.vertex P γ).last (!e))
        < Tower.lamAfter P γ x ((IETDatum₂.vertex P γ).last e) := by
      have h1 : (Tower.lamAfter P γ x ((IETDatum₂.vertex P γ).last (!e)) : ℝ)
          < (Tower.lamAfter P γ x ((IETDatum₂.vertex P γ).last e) : ℝ) := by
        have h1a := congrFun hw_eq ((IETDatum₂.vertex P γ).last (!e))
        have h1b := congrFun hw_eq ((IETDatum₂.vertex P γ).last e)
        rw [← h1a, ← h1b]
        exact hlt
      exact_mod_cast h1
    have hstepOK : TowerTrue.StepOK (IETDatum₂.vertex P γ) (Tower.lamAfter P γ x) e :=
      (stepOK_last_iff _ _ e).mpr hcmp
    have hOK' : TowerTrue.IterOK P x (γ ++ [e]) :=
      (IterGlue2.iterOK_append_singleton P x γ e).mpr ⟨hOK, hstepOK⟩
    refine ⟨?_, ?_⟩
    · rw [hstep]; exact hOK'
    · rw [hstep, lamAfter_append_singleton]
      intro a
      rw [Tower.hatLam]
      by_cases ha : a = (IETDatum₂.vertex P γ).last e
      · rw [if_pos ha]
        exact tsub_pos_of_lt (by rw [ha]; exact hcmp)
      · rw [if_neg ha]
        exact hpos a

end IterGlue2

end
