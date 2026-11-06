/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.ClosureSimplex
public import IETFree.RauzyVeech.ColDiam
public import IETFree.RauzyVeech.CylinderGrowth
public import IETFree.RauzyVeech.InvariantMeasure
public import IETFree.RauzyVeech.IterGlue2
public import IETFree.RauzyVeech.MainComponents
public import IETFree.RauzyVeech.RayPath
public import IETFree.RauzyVeech.TowerGlue

/-!
# The pointwise ray criterion: coalescence of the normalised columns gives the ray condition

`RayPointwise.rayCondition_of_cols` proves the *pointwise* form of the ray criterion: given a length
vector `lam` in the root cylinder which is never in a stopping set along its own greedy path, and
such that the normalised columns of the Rauzy–Veech path matrices `Q(pathWord P lam k)` eventually
become pointwise close, the ray condition `RayCondition P lam` of
`IETFree/RauzyVeech/MainComponents.lean` holds.  It is the last step of the positive-block argument:
the analytic input (the columns coalescing along the greedy path of `lam`) is what the contraction
of the sup-norm spread of the columns produces.

The passage from "columns close" to "cylinders shrink" is
`ColShrink.tendsto_diam_of_cols_eventually_close`, applied to `p = IETDatum₂.pathStep P lam` and
rewritten with `IETDatum₂.pfx_pathStep`.  The stopping-set hypothesis is only required *along the
greedy path* (`lam ∉ cylStop P (pathWord P lam k)`), not for every word: this is
`iterOK_pathWord_of_notMem_cylStop` below, which re-runs the proof of `IterGlue2.iterOK_pathWord`
against `IETDatum₂.mem_pathWord_of_notMem_cylStop`. -/

@[expose] public section


open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators Topology

namespace RayPointwise

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. `IterOK` along the greedy path, from the along-path stopping hypothesis -/

/-- **The greedy path is an `IterOK` word, with a positive renormalised vector** — the version of
`IterGlue2.iterOK_pathWord` whose stopping hypothesis only speaks about the words that actually
occur, `IETDatum₂.pathWord P x k`. -/
theorem iterOK_pathWord_of_notMem_cylStop (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {x : α → ℝ≥0} (h0 : x ∈ IETDatum₂.simplexCyl P [])
    (hstop : ∀ k, x ∉ IETDatum₂.cylStop P (IETDatum₂.pathWord P x k)) :
    ∀ k, TowerTrue.IterOK P x (IETDatum₂.pathWord P x k) ∧
      (∀ a, 0 < Tower.lamAfter P (IETDatum₂.pathWord P x k) x a) := by
  intro k
  induction k with
  | zero =>
    exact ⟨trivial, (IETDatum₂.mem_simplexCyl_nil_iff P x).mp h0 |>.2⟩
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
      (IterGlue2.stepOK_last_iff _ _ e).mpr hcmp
    have hOK' : TowerTrue.IterOK P x (γ ++ [e]) :=
      (IterGlue2.iterOK_append_singleton P x γ e).mpr ⟨hOK, hstepOK⟩
    refine ⟨?_, ?_⟩
    · rw [hstep]; exact hOK'
    · rw [hstep, IterGlue2.lamAfter_append_singleton]
      intro a
      rw [Tower.hatLam]
      by_cases ha : a = (IETDatum₂.vertex P γ).last e
      · rw [ite_eq_left ha]
        exact tsub_pos_of_lt (by rw [ha]; exact hcmp)
      · rw [ite_eq_right ha]
        exact hpos a

/-! ## 2. Every path cylinder sits in the root cylinder  The composition of the peeling
(`HasPositiveBlocks` gives `lam ∈ simplexCyl P (w ++ v)` for some word) with `rayCondition_of_cols`
(which wants `lam ∈ simplexCyl P []`) needs the inclusion `simplexCyl P γ ⊆ simplexCyl P []`: `Q(γ)`
has a *positive diagonal* (`IETDatum₂.Path.one_le_Q_diag`), so every row of `Q(γ)` meets the
positive cone and `x = Q(γ) y` with `y > 0` is strictly positive. -/

/-- **A point of any path cylinder is a strictly positive point of the simplex.** -/
theorem mem_simplexCyl_nil_of_mem (P : IETDatum₂ α n) {γ : List Bool} {x : α → ℝ≥0}
    (h : x ∈ IETDatum₂.simplexCyl P γ) : x ∈ IETDatum₂.simplexCyl P [] := by
  obtain ⟨y, hy, hxy⟩ := h.1
  refine (IETDatum₂.mem_simplexCyl_nil_iff P x).mpr ⟨h.2, fun a => ?_⟩
  have hxa : (x a : ℝ) = ∑ b, (IETDatum₂.Path.Q P γ a b : ℝ) * y b := congrFun hxy a
  have hnn (b) : 0 ≤ (IETDatum₂.Path.Q P γ a b : ℝ) * y b :=
    mul_nonneg (by exact_mod_cast IETDatum₂.Path.Q_nonneg P γ a b) (le_of_lt (hy b))
  have hle : (IETDatum₂.Path.Q P γ a a : ℝ) * y a
      ≤ ∑ b, (IETDatum₂.Path.Q P γ a b : ℝ) * y b :=
    Finset.single_le_sum (f := fun b => (IETDatum₂.Path.Q P γ a b : ℝ) * y b)
      (fun b _ => hnn b) (Finset.mem_univ a)
  have hdiag : (1 : ℝ) ≤ (IETDatum₂.Path.Q P γ a a : ℝ) := by
    have := IETDatum₂.Path.one_le_Q_diag P γ a
    exact_mod_cast this
  have hya : (0 : ℝ) < y a := hy a
  have hpos : (0 : ℝ) < (x a : ℝ) := by rw [hxa]; nlinarith
  exact_mod_cast hpos

/-! ## 3. The shrinking of the cylinders from the columns, pointwise -/

/-- **Columns close ⟹ cylinders shrink**, pointwise in `lam`: the measure-free half of the shrinking
criterion `ColShrink.tendsto_diam_of_cols_eventually_close`. -/
theorem tendsto_diam_pathWord_of_cols (P : IETDatum₂ α n) {lam : α → ℝ≥0}
    (hcols : ∀ ε > 0, ∀ᶠ k in atTop, ∀ b b' a,
      |ColShrink.ncol P (IETDatum₂.pathWord P lam k) b a
        - ColShrink.ncol P (IETDatum₂.pathWord P lam k) b' a| ≤ ε) :
    Tendsto (fun k => Metric.diam (IETDatum₂.simplexCyl P (IETDatum₂.pathWord P lam k)))
      atTop (𝓝 0) := by
  have h := ColShrink.tendsto_diam_of_cols_eventually_close P (IETDatum₂.pathStep P lam)
    (fun ε hε => by
      filter_upwards [hcols ε hε] with k hk
      rw [IETDatum₂.pfx_pathStep]
      exact hk)
  simpa only [IETDatum₂.pfx_pathStep] using h

/-! ## 4. The ray condition from the coalescence of the normalised columns -/

/-- **The pointwise ray criterion.**  If the normalised columns of the Rauzy–Veech
matrices along the greedy path of `lam` eventually pairwise agree, then every invariant probability
measure carried by `[0,1)` has length vector proportional to `lam`. -/
theorem rayCondition_of_cols (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {lam : α → ℝ≥0} (h0 : lam ∈ IETDatum₂.simplexCyl P [])
    (hstop : ∀ k, lam ∉ IETDatum₂.cylStop P (IETDatum₂.pathWord P lam k))
    (hcols : ∀ ε > 0, ∀ᶠ k in atTop, ∀ b b' a,
      |ColShrink.ncol P (IETDatum₂.pathWord P lam k) b a
        - ColShrink.ncol P (IETDatum₂.pathWord P lam k) b' a| ≤ ε) :
    RayCondition P lam := by
  have hsim : lam ∈ simplexOn α := ((IETDatum₂.mem_simplexCyl_nil_iff P lam).mp h0).1
  intro μ hμ hmass
  have hiter := iterOK_pathWord_of_notMem_cylStop P hP hn h0 hstop
  -- the path hypotheses of the ray criterion
  have hmem (k) :
      lam ∈ IETDatum₂.simplexCyl P (PrefixWord.pfx (IETDatum₂.pathStep P lam) k) := by
    rw [IETDatum₂.pfx_pathStep]
    exact IETDatum₂.mem_pathWord_of_notMem_cylStop P hP hn h0 hstop k
  have hanti : Antitone fun k =>
      IETDatum₂.simplexCyl P (PrefixWord.pfx (IETDatum₂.pathStep P lam) k) :=
    RayCriterion.antitone_simplexCyl_pfx P hP hn _
  have hbdd : Bornology.IsBounded
      (IETDatum₂.simplexCyl P (PrefixWord.pfx (IETDatum₂.pathStep P lam) 0)) :=
    RayCriterion.isBounded_simplexCyl_pfx P _
  -- the coalescence of the columns is the shrinking of the cylinders
  have hdiam : Tendsto (fun k => Metric.diam
      (IETDatum₂.simplexCyl P (PrefixWord.pfx (IETDatum₂.pathStep P lam) k))) atTop (𝓝 0) := by
    simpa only [IETDatum₂.pfx_pathStep] using tendsto_diam_pathWord_of_cols P hcols
  -- the tower formula in `qApply` form along the greedy path
  have htower (k) : ∃ y : α → ℝ, (∀ a, 0 ≤ y a) ∧
      (fun a => InvariantMeasure.lambdaOf μ P lam a)
        = IETDatum₂.qApply
          (IETDatum₂.Path.Q P (PrefixWord.pfx (IETDatum₂.pathStep P lam) k)) y := by
    set γ := PrefixWord.pfx (IETDatum₂.pathStep P lam) k with hγ
    have hγ' : γ = IETDatum₂.pathWord P lam k := IETDatum₂.pfx_pathStep P lam k
    have hOK : TowerTrue.IterOK P lam γ := by
      rw [hγ']; exact (hiter k).1
    refine ⟨fun b => (μ : Measure ℝ).real (Tower.cellAt P γ lam b), fun b => ?_, ?_⟩
    · exact ENNReal.toReal_nonneg
    · have h := TowerGlue.real_eq_qApply P (μ : Measure ℝ) (lam := lam) (γ := γ)
        (κ := fun b => Tower.cellAt P γ lam b) (fun a b => IETDatum₂.Path.Q_nonneg P γ a b)
        (fun b => measure_ne_top _ _)
        (fun a => by
          rw [TowerTrue.tower_formula_level_pathQ_any P hP hn lam hsim (μ : Measure ℝ) hμ γ
            hOK a])
      have hfun : (fun a => InvariantMeasure.lambdaOf μ P lam a)
          = fun a => (μ : Measure ℝ).real (InvariantMeasure.cellOf P lam a) := rfl
      rw [hfun]
      exact h
  exact TowerGlue.ray_of_shrink_and_tower P hsim hmem hanti hbdd hdiam μ hmass htower

end RayPointwise

end
