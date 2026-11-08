/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.IterGlue
public import IETFree.RauzyVeech.RauzyPath

/-!
# The greedy path is an `IsRauzyPath` word

The a.e. greedy path (`RauzyPath.pathWord`, built by choosing at each step the child cylinder that
contains the point) satisfies `IsRauzyPath` — the Rauzy type rule — and its renormalised length
vector (`lamAfter`) stays strictly positive.  The two statements are proved simultaneously:
positivity is what lets `IsRenorm.unique` identify the comparison from `mem_simplexCyl_append_iff`
with the `IsRauzyStep` of the algorithm. -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace IntervalExchange.RauzyVeech

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- `IsRauzyPath` splits at the last letter of the word. -/
theorem isRauzyPath_append_singleton (P : IETDatum₂ α n) (lam : α → ℝ≥0) (γ : List Bool)
    (e : Bool) :
    IsRauzyPath P lam (γ ++ [e]) ↔
      IsRauzyPath P lam γ ∧
        IsRauzyStep (IETDatum₂.vertex P γ) (lamAfter P γ lam) e := by
  induction γ generalizing P lam with
  | nil =>
    rw [List.nil_append]
    simp [IsRauzyPath, IETDatum₂.vertex, lamAfter]
  | cons b bs ih =>
    have hb := ih (P := P.rvStep b) (lam := hatLam P b lam)
    have hun1 : IsRauzyPath P lam (b :: (bs ++ [e]))
        = (IsRauzyStep P lam b ∧
            IsRauzyPath (P.rvStep b) (hatLam P b lam) (bs ++ [e])) := (rfl)
    have hun2 : IsRauzyPath P lam (b :: bs)
        = (IsRauzyStep P lam b ∧
            IsRauzyPath (P.rvStep b) (hatLam P b lam) bs) := (rfl)
    rw [List.cons_append, hun1, hun2, hb, lamAfter_cons, IETDatum₂.vertex_cons]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2.1⟩, h2.2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩

omit [DecidableEq α] in
/-- The type rule in the form of a strict comparison at the last letters. -/
theorem isRauzyStep_last_iff (P : IETDatum₂ α n) (lam : α → ℝ≥0) (ε : Bool) :
    IsRauzyStep P lam ε ↔ lam (P.last (!ε)) < lam (P.last ε) := by
  cases ε <;>
    simp [isRauzyStep_true_iff, isRauzyStep_false_iff]

/-- `lamAfter` splits at the last letter of the word. -/
theorem lamAfter_append_singleton (P : IETDatum₂ α n) (lam : α → ℝ≥0) (γ : List Bool) (e : Bool) :
    lamAfter P (γ ++ [e]) lam
      = hatLam (IETDatum₂.vertex P γ) e (lamAfter P γ lam) := by
  induction γ generalizing P lam with
  | nil => rw [List.nil_append]; rfl
  | cons b bs ih =>
    rw [List.cons_append, lamAfter_cons, IETDatum₂.vertex_cons,
      ih (P := P.rvStep b) (hatLam P b lam), lamAfter_cons]

/-- **The greedy path is an `IsRauzyPath` word, with a positive renormalised vector**, from the
stopping hypothesis along the path only.  Proved simultaneously: positivity is what lets
`IsRenorm.unique` identify the renormalised vector produced by `mem_simplexCyl_append_iff` with
`lamAfter`, turning the strict length comparison of the child cylinder into the algorithm's
`IsRauzyStep`. -/
theorem isRauzyPath_pathWord_of_notMem_cylStop (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {x : α → ℝ≥0} (h0 : x ∈ IETDatum₂.simplexCyl P [])
    (hstop : ∀ k, x ∉ IETDatum₂.cylStop P (IETDatum₂.pathWord P x k)) (k : ℕ) :
    IsRauzyPath P x (IETDatum₂.pathWord P x k) ∧
      (∀ a, 0 < lamAfter P (IETDatum₂.pathWord P x k) x a) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · trivial
    · simp only [IETDatum₂.pathWord, lamAfter]
      exact (IETDatum₂.mem_simplexCyl_nil_iff P x).mp h0 |>.2
  | succ k ih =>
    obtain ⟨hOK, hpos⟩ := ih
    set γ := IETDatum₂.pathWord P x k with hγ
    set e := IETDatum₂.pathStep P x k with he
    have hstep : IETDatum₂.pathWord P x (k + 1) = γ ++ [e] := IETDatum₂.pathWord_succ P x k
    have hmem : x ∈ IETDatum₂.simplexCyl P (γ ++ [e]) := by
      rw [← hstep]
      exact IETDatum₂.mem_pathWord_of_notMem_cylStop P hP hn h0 hstop (k + 1)
    obtain ⟨w, hw, hlt⟩ :=
      (IETDatum₂.mem_simplexCyl_append_iff P hP hn γ e x).mp hmem |>.2
    -- `lamAfter` is the same renormalised vector
    have hren : IETDatum₂.IsRenorm P γ x (fun a => (lamAfter P γ x a : ℝ)) := by
      refine (IETDatum₂.isRenorm_iff P γ x _).mpr ⟨hpos, ?_⟩
      have hq := qApply_lamAfter P hP hn γ x hOK
      rw [← hq]
    have hw_eq : w = fun a => (lamAfter P γ x a : ℝ) :=
      IETDatum₂.IsRenorm.unique hP hn hw hren
    have hcmp : lamAfter P γ x ((IETDatum₂.vertex P γ).last (!e))
        < lamAfter P γ x ((IETDatum₂.vertex P γ).last e) := by
      have h1 : (lamAfter P γ x ((IETDatum₂.vertex P γ).last (!e)) : ℝ)
          < (lamAfter P γ x ((IETDatum₂.vertex P γ).last e) : ℝ) := by
        have h1a := congrFun hw_eq ((IETDatum₂.vertex P γ).last (!e))
        have h1b := congrFun hw_eq ((IETDatum₂.vertex P γ).last e)
        rw [← h1a, ← h1b]
        exact hlt
      exact_mod_cast h1
    have hRVstep : IsRauzyStep (IETDatum₂.vertex P γ) (lamAfter P γ x) e :=
      (isRauzyStep_last_iff _ _ e).mpr hcmp
    have hOK' : IsRauzyPath P x (γ ++ [e]) :=
      (isRauzyPath_append_singleton P x γ e).mpr ⟨hOK, hRVstep⟩
    refine ⟨?_, ?_⟩
    · rw [hstep]; exact hOK'
    · rw [hstep, lamAfter_append_singleton]
      intro a
      rw [hatLam]
      by_cases ha : a = (IETDatum₂.vertex P γ).last e
      · rw [ite_eq_left ha]
        exact tsub_pos_of_lt (by rw [ha]; exact hcmp)
      · rw [ite_eq_right ha]
        exact hpos a

/-- **The greedy path is an `IsRauzyPath` word, with a positive renormalised vector**, from the
stopping hypothesis on every word. -/
theorem isRauzyPath_pathWord (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {x : α → ℝ≥0} (h0 : x ∈ IETDatum₂.simplexCyl P [])
    (hstop : ∀ γ : List Bool, x ∉ IETDatum₂.cylStop P γ) (k : ℕ) :
    IsRauzyPath P x (IETDatum₂.pathWord P x k) ∧
      (∀ a, 0 < lamAfter P (IETDatum₂.pathWord P x k) x a) :=
  isRauzyPath_pathWord_of_notMem_cylStop P hP hn h0 (fun _ => hstop _) k

end IntervalExchange.RauzyVeech

end
