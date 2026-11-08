/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.Tower.LevelOne

/-!
# The tower, read at a node

The level-`k` tower of `RauzyVeech/Tower/Tiling.lean` is stated along an **infinite** nested
sequence of words `γ : ℕ → List Bool`.  At a single node `γ` of the greedy path only the levels up
to `|γ|` exist, and the prefix sequence cannot be continued past `|γ|`: the renormalised lengths at
the node can have equal last letters, after which no step is `IsRauzyStep`.  So the tower
statements are re-proved here by induction on the word, node by node, which is the form the rigid
step consumes.

This module is below `Tower/Tiling.lean`, so the sequence version is derived from it there (apply
the node statement at `γ k` with the single step `γ (k+1) = γ k ++ [p k]`); the node statements are
strictly stronger, since they need `IsRauzyPath P lam (γ ++ [e])` for one step rather than
`∀ k, IsRauzyPath P lam (γ k)` along an infinite tower.

* `baseLen`: the length of the base interval at the node;
* `nodeExch` and its API: the exchange at the node, renormalised to the level-`γ` lengths;
* `levelCell_succ`, `height_nil`, `height_succ`, `height_*`: the level cells and heights in node
  form;
* `levelCell_sub_*`, `exchangeAt_image_*`: the level-one steps (a cell sits in its parent; the node
  exchange sends the secondary cell to the main one);
* `FR_list`, `levelOne_decomposition`: the first-return identity and the level-one decomposition of
  the base;
* `cover_step_false`, `cover_step_true`: a floor of the level-`γ` tower is a floor of the
  level-`γ ++ [e]` one.
-/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

namespace IntervalExchange.RauzyVeech

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- The length of the base interval at the node `γ`: `∑ a, (lamAfter P γ lam a : ℝ)`, in the
scale in which the original length vector sums to `1`. -/
noncomputable def baseLen {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) : ℝ :=
  ∑ a, (lamAfter P γ lam a : ℝ)

/-- **`baseLen` is the sum of the node's lengths.** -/
theorem baseLen_def {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) :
    baseLen P γ lam = ∑ a, (lamAfter P γ lam a : ℝ) := (rfl)

/-- The exchange at the node `γ`, renormalised to the level-`γ` lengths: the library's
`TowerStep.exchangeAt`
at that node. -/
noncomputable def nodeExch (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) :
    ℝ → ℝ :=
  mkIETFun ((IETDatum₂.vertex P γ).lengthsInBottom (lamAfter P γ lam))
    (IETDatum₂.vertex P γ).perm 0

/-- The exchange at the empty node is the exchange of `P` itself. -/
theorem nodeExch_nil {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hlam : lam ∈ simplex α) :
    nodeExch P [] lam = ⇑(P.toIET lam) := by
  simp only [nodeExch, IETDatum₂.vertex_nil, lamAfter_nil]
  exact (coe_toIET hlam).symm

/-- The exchange at the node `γ`, as `mkIETFun`. -/
theorem nodeExch_eq (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) :
    nodeExch P γ lam
      = mkIETFun ((IETDatum₂.vertex P γ).lengthsInBottom (lamAfter P γ lam))
          (IETDatum₂.vertex P γ).perm 0 := (rfl)

/-- The exchange at the node `γ ++ [e]`, read at the vertex `vertex P γ`. -/
theorem nodeExch_append (P : IETDatum₂ α n) (γ : List Bool) (e : Bool)
    (lam : α → ℝ≥0) (y : ℝ) :
    nodeExch P (γ ++ [e]) lam y
      = mkIETFun (((IETDatum₂.vertex P γ).rvStep e).lengthsInBottom
            (hatLam (IETDatum₂.vertex P γ) e (lamAfter P γ lam)))
          ((IETDatum₂.vertex P γ).rvStep e).perm 0 y := by
  simp only [nodeExch, IETDatum₂.vertex_append_singleton, lamAfter_append_singleton]

/-- The level-`γ` cell, read as a level-one cell of the vertex `vertex P γ`. -/
theorem cellAt_node (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) (b : α) :
    cellAt (IETDatum₂.vertex P γ) [] (lamAfter P γ lam) b
      = cellAt P γ lam b := (rfl)

/-- The height at the empty node is one. -/
theorem height_nil (P : IETDatum₂ α n) (b : α) : IETDatum₂.Path.height P [] b = 1 := by
  simp only [IETDatum₂.Path.height, IETDatum₂.Path.Q]
  refine (Finset.sum_congr rfl (fun x _ => ?_)).trans (sum_ite_single (c := b) 1)
  rw [Matrix.one_apply]
  split_ifs <;> simp

/-- **The height recursion**: passing from `γ` to `γ ++ [e]` adds the height of the letter `e`
exactly when the letter `b` is the *other* last letter of the vertex. -/
theorem height_succ {P : IETDatum₂ α n} (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) (e : Bool) (b : α) :
    IETDatum₂.Path.height P (γ ++ [e]) b = IETDatum₂.Path.height P γ b
      + if b = (IETDatum₂.vertex P γ).last (!e) then
          IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last e) else 0 := by
  have hne (e' : Bool) : (IETDatum₂.vertex P γ).last e' ≠ (IETDatum₂.vertex P γ).last (!e') :=
      IETDatum₂.vertex_last_ne_not P hP hn γ e'
  have hQ (a) : IETDatum₂.Path.Q P (γ ++ [e]) a b
      = IETDatum₂.Path.Q P γ a b
        + if b = (IETDatum₂.vertex P γ).last (!e) then
            IETDatum₂.Path.Q P γ a ((IETDatum₂.vertex P γ).last e) else 0 := by
    rw [IETDatum₂.Path.Q_append, IETDatum₂.Path.Q_singleton, Matrix.mul_apply]
    exact mulVec_rvMat (IETDatum₂.Path.Q P γ) (IETDatum₂.vertex P γ) e
      (hne e) a b
  have key (a : α) :
    (IETDatum₂.Path.Q P (γ ++ [e]) a b).toNat
      = (IETDatum₂.Path.Q P γ a b).toNat
        + (if b = (IETDatum₂.vertex P γ).last (!e) then
            (IETDatum₂.Path.Q P γ a ((IETDatum₂.vertex P γ).last e)).toNat else 0) := by
    rw [hQ a]
    have h1 : (0 : ℤ) ≤ IETDatum₂.Path.Q P γ a b := IETDatum₂.Path.Q_nonneg P _ a b
    have h2 : (0 : ℤ) ≤ (if b = (IETDatum₂.vertex P γ).last (!e) then
        IETDatum₂.Path.Q P γ a ((IETDatum₂.vertex P γ).last e) else 0) := by
      split
      · exact IETDatum₂.Path.Q_nonneg P _ a _
      · exact le_refl 0
    rw [Int.toNat_add h1 h2]
    congr 1
    split <;> simp
  simp only [IETDatum₂.Path.height]
  calc (∑ a, (IETDatum₂.Path.Q P (γ ++ [e]) a b).toNat)
      = ∑ a, ((IETDatum₂.Path.Q P γ a b).toNat
          + (if b = (IETDatum₂.vertex P γ).last (!e) then
              (IETDatum₂.Path.Q P γ a ((IETDatum₂.vertex P γ).last e)).toNat else 0)) :=
        Finset.sum_congr rfl (fun a _ => key a)
    _ = (∑ a, (IETDatum₂.Path.Q P γ a b).toNat)
          + ∑ a, (if b = (IETDatum₂.vertex P γ).last (!e) then
              (IETDatum₂.Path.Q P γ a ((IETDatum₂.vertex P γ).last e)).toNat else 0) :=
        Finset.sum_add_distrib
    _ = (∑ a, (IETDatum₂.Path.Q P γ a b).toNat)
          + (if b = (IETDatum₂.vertex P γ).last (!e) then
              (∑ a, (IETDatum₂.Path.Q P γ a ((IETDatum₂.vertex P γ).last e)).toNat) else 0) := by
        congr 1
        by_cases hb : b = (IETDatum₂.vertex P γ).last (!e)
        · simp only [ite_eq_left hb]
        · rw [ite_eq_right hb]
          exact Finset.sum_eq_zero (fun a _ => by simp only [ite_eq_right hb])

/-! ## 1. The nesting of the level-one cells, in the notation of the node -/

/-- False step: every level-one cell sits in the cell of the same name. -/
theorem cc_sub_false (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) (b : α) :
    cellAt P (γ ++ [false]) lam b ⊆ cellAt P γ lam b := by
  have h := names_false_sub (IETDatum₂.vertex P γ) (lamAfter P γ lam) b
  have h2 := cellAt_node P γ lam b
  rw [cellAt_succ]
  rw [← h2]
  exact h

/-- True step: every level-one cell but the secondary one sits in the cell of the same name. -/
theorem cc_sub_true {P : IETDatum₂ α n} {γ : List Bool} {lam : α → ℝ≥0}
    (hS : IsRauzyStep (IETDatum₂.vertex P γ) (lamAfter P γ lam) true) (b : α)
    (hb : b ≠ (IETDatum₂.vertex P γ).last false) :
    cellAt P (γ ++ [true]) lam b ⊆ cellAt P γ lam b := by
  have h := names_true_sub (IETDatum₂.vertex P γ) (lamAfter P γ lam) hS b hb
  have h2 := cellAt_node P γ lam b
  rw [cellAt_succ]
  rw [← h2]
  exact h

/-- True step: the secondary cell sits in the cell of the main name. -/
theorem cc_sub_true_scd {P : IETDatum₂ α n} {γ : List Bool} {lam : α → ℝ≥0}
    (hS : IsRauzyStep (IETDatum₂.vertex P γ) (lamAfter P γ lam) true) :
    cellAt P (γ ++ [true]) lam ((IETDatum₂.vertex P γ).last false)
      ⊆ cellAt P γ lam ((IETDatum₂.vertex P γ).last true) := by
  have h := names_true_sub_scd (IETDatum₂.vertex P γ) (lamAfter P γ lam) hS
  have h2 := cellAt_node P γ lam ((IETDatum₂.vertex P γ).last true)
  rw [cellAt_succ]
  rw [← h2]
  exact h

/-- False step: the image of the secondary cell under the node exchange is the main cell. -/
theorem kk_image_false_scd {P : IETDatum₂ α n} {γ : List Bool} {lam : α → ℝ≥0}
    (hS : IsRauzyStep (IETDatum₂.vertex P γ) (lamAfter P γ lam) false) :
    nodeExch P γ lam '' cellAt P (γ ++ [false]) lam ((IETDatum₂.vertex P γ).last true)
      ⊆ cellAt P γ lam ((IETDatum₂.vertex P γ).last false) := by
  have h := names_false_image (IETDatum₂.vertex P γ) (lamAfter P γ lam) hS
  have h2 := cellAt_node P γ lam ((IETDatum₂.vertex P γ).last false)
  have h3 : nodeExch P γ lam
      = mkIETFun ((IETDatum₂.vertex P γ).lengthsInBottom (lamAfter P γ lam))
          (IETDatum₂.vertex P γ).perm 0 := nodeExch_eq P γ lam
  rw [h3, cellAt_succ, ← h2]
  exact h

/-- True step: the image of the secondary cell under the node exchange is the same cell. -/
theorem kk_image_true_scd {P : IETDatum₂ α n} {γ : List Bool} {lam : α → ℝ≥0}
    (hS : IsRauzyStep (IETDatum₂.vertex P γ) (lamAfter P γ lam) true) :
    nodeExch P γ lam '' cellAt P (γ ++ [true]) lam ((IETDatum₂.vertex P γ).last false)
      ⊆ cellAt P γ lam ((IETDatum₂.vertex P γ).last false) := by
  have h := names_true_image (IETDatum₂.vertex P γ) (lamAfter P γ lam) hS
  have h2 := cellAt_node P γ lam ((IETDatum₂.vertex P γ).last false)
  have h3 : nodeExch P γ lam
      = mkIETFun ((IETDatum₂.vertex P γ).lengthsInBottom (lamAfter P γ lam))
          (IETDatum₂.vertex P γ).perm 0 := nodeExch_eq P γ lam
  rw [h3, cellAt_succ, ← h2]
  exact h

/-! ## 2. The first-return identity at a node -/

/-- **The first-return identity at a node.**  For a point of the level-`γ` cell of `b`, the
`height P γ b`-th iterate of `T` is the exchange of the node `γ`: this is Veech's (3.3) at the node,
with the node exchange as first return. -/
theorem FR_list {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible) (hn : 2 ≤ n)
    (hlam : lam ∈ simplex α) {γ : List Bool} (hOK : IsRauzyPath P lam γ) (b : α) (y : ℝ)
    (hy : y ∈ cellAt P γ lam b) :
      (⇑(P.toIET lam))^[IETDatum₂.Path.height P γ b] y = nodeExch P γ lam y := by
  induction γ using List.reverseRecOn generalizing b y with
  -- at the empty node the height is one and the exchange of the node is one step of `T`
  | nil =>
    rw [height_nil, Function.iterate_one, nodeExch_nil hlam]
  -- at `γ ++ [e]` the cell is cut out of the level-`γ` one, and one return is a node step
  | append_singleton γ e ih =>
    obtain ⟨hOK', hS⟩ := (isRauzyPath_append_singleton P lam γ e).mp hOK
    have hne (e' : Bool) :
        (IETDatum₂.vertex P γ).last e' ≠ (IETDatum₂.vertex P γ).last (!e') :=
            IETDatum₂.vertex_last_ne_not P hP hn γ e'
    have hy' : y ∈ cellAt (IETDatum₂.vertex P γ) [e] (lamAfter P γ lam) b := by
      rw [← cellAt_succ]
      exact hy
    have hfr : (mkIETFun ((IETDatum₂.vertex P γ).lengthsInBottom
          (lamAfter P γ lam)) (IETDatum₂.vertex P γ).perm 0)^[
          IETDatum₂.Path.height (IETDatum₂.vertex P γ) [e] b] y
        = mkIETFun (((IETDatum₂.vertex P γ).rvStep e).lengthsInBottom
              (hatLam (IETDatum₂.vertex P γ) e (lamAfter P γ lam)))
            ((IETDatum₂.vertex P γ).rvStep e).perm 0 y := by
      cases e with
      | false => exact firstReturn_false _ hne _ hS b hy'
      | true => exact firstReturn_true _ hne _ hS b hy'
    have hHs := height_succ hP hn γ e b
    -- a letter moved by the step has height two, so the node exchange is that of `γ` twice
    by_cases hb : b = (IETDatum₂.vertex P γ).last (!e)
    · have hheight : IETDatum₂.Path.height P (γ ++ [e]) b
          = IETDatum₂.Path.height P γ b
            + IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last e) := by
        rw [hHs, ite_eq_left hb]
      have hnode : nodeExch P (γ ++ [e]) lam y
          = nodeExch P γ lam (nodeExch P γ lam y) := by
        have hg2 : IETDatum₂.Path.height (IETDatum₂.vertex P γ) [e] b = 2 := by
          rw [height_singleton_eq _ hne, ite_eq_left hb]
        rw [nodeExch_append, ← hfr, hg2, nodeExch_eq P γ lam,
          ← one_add_one_eq_two, Function.iterate_add_apply, Function.iterate_one]
    -- its height is the sum of the heights of the two floors that the step exchanges
      cases e with
      | false =>
        have hb' : b = (IETDatum₂.vertex P γ).last true := by simpa using hb
        rw [hb'] at hy hheight ⊢
        have hy1 : y ∈ cellAt P γ lam ((IETDatum₂.vertex P γ).last true) :=
          cc_sub_false P γ lam _ hy
        have hmem : nodeExch P γ lam y
            ∈ cellAt P γ lam ((IETDatum₂.vertex P γ).last false) :=
          kk_image_false_scd (P := P) (γ := γ) (lam := lam) hS ⟨y, hy, rfl⟩
        have i1 := ih hOK' ((IETDatum₂.vertex P γ).last true) y hy1
        have i2 := ih hOK' ((IETDatum₂.vertex P γ).last false) (nodeExch P γ lam y) hmem
        rw [hnode]
        calc (⇑(P.toIET lam))^[IETDatum₂.Path.height P (γ ++ [false])
              ((IETDatum₂.vertex P γ).last true)] y
            = (⇑(P.toIET lam))^[IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last false)
                + IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last true)] y := by
              rw [hheight, Nat.add_comm]
          _ = (⇑(P.toIET lam))^[IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last false)]
                ((⇑(P.toIET lam))^[IETDatum₂.Path.height P γ
                  ((IETDatum₂.vertex P γ).last true)] y) := by
              rw [Function.iterate_add_apply]
          _ = (⇑(P.toIET lam))^[IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last false)]
                (nodeExch P γ lam y) := by rw [i1]
          _ = nodeExch P γ lam (nodeExch P γ lam y) := i2
      | true =>
        have hb' : b = (IETDatum₂.vertex P γ).last false := by simpa using hb
        rw [hb'] at hy hheight ⊢
        have hy1 : y ∈ cellAt P γ lam ((IETDatum₂.vertex P γ).last true) :=
          cc_sub_true_scd (P := P) (γ := γ) (lam := lam) hS hy
        have hmem : nodeExch P γ lam y
            ∈ cellAt P γ lam ((IETDatum₂.vertex P γ).last false) :=
          kk_image_true_scd (P := P) (γ := γ) (lam := lam) hS ⟨y, hy, rfl⟩
        have i1 := ih hOK' ((IETDatum₂.vertex P γ).last true) y hy1
        have i2 := ih hOK' ((IETDatum₂.vertex P γ).last false) (nodeExch P γ lam y) hmem
        rw [hnode]
        calc (⇑(P.toIET lam))^[IETDatum₂.Path.height P (γ ++ [true])
              ((IETDatum₂.vertex P γ).last false)] y
            = (⇑(P.toIET lam))^[IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last false)
                + IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last true)] y := by rw [hheight]
          _ = (⇑(P.toIET lam))^[IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last false)]
                ((⇑(P.toIET lam))^[IETDatum₂.Path.height P γ
                  ((IETDatum₂.vertex P γ).last true)] y) := by
              rw [Function.iterate_add_apply]
          _ = (⇑(P.toIET lam))^[IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last false)]
                (nodeExch P γ lam y) := by rw [i1]
          _ = nodeExch P γ lam (nodeExch P γ lam y) := i2
    -- a letter the step does not move keeps its height and its cell only shrinks
    · have hheight : IETDatum₂.Path.height P (γ ++ [e]) b = IETDatum₂.Path.height P γ b := by
        rw [hHs, ite_eq_right hb, add_zero]
      have hnode : nodeExch P (γ ++ [e]) lam y = nodeExch P γ lam y := by
        have hg1 : IETDatum₂.Path.height (IETDatum₂.vertex P γ) [e] b = 1 := by
          rw [height_singleton_eq _ hne, ite_eq_right hb, add_zero]
        rw [nodeExch_append, nodeExch_eq P γ lam, ← hfr, hg1, Function.iterate_one]
      have hy1 : y ∈ cellAt P γ lam b := by
        cases e with
        | false => exact cc_sub_false P γ lam b hy
        | true => exact cc_sub_true (P := P) (γ := γ) (lam := lam) hS b (by simpa using hb) hy
      rw [hheight, hnode]
      exact ih hOK' b y hy1

/-- The level-`γ` cell is the cell of the vertex `vertex P γ`. -/
theorem cellOf_node (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) (b : α) :
    cellOf (IETDatum₂.vertex P γ) (lamAfter P γ lam) b
      = cellAt P γ lam b := (rfl)

/-- The base length, as a sum. -/
theorem baseLen_eq_sum (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) :
    baseLen P γ lam = ∑ b, (lamAfter P γ lam b : ℝ) := (rfl)

/-- A level cell sits in the level base interval. -/
theorem cellAt_sub_base (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) (b : α) :
    cellAt P γ lam b ⊆ Set.Ico (0:ℝ) (baseLen P γ lam) := by
  have h := cellOf_subset (IETDatum₂.vertex P γ) (lamAfter P γ lam) b
  rw [cellOf_node] at h
  rw [show (∑ i, ((IETDatum₂.vertex P γ).lengthsInBottom (lamAfter P γ lam) i : ℝ))
      = ∑ c, (lamAfter P γ lam c : ℝ) from
    totalLength_lengthsInBottom _ _] at h
  rw [baseLen_eq_sum]
  exact h

/-- Two level cells with a common point have the same letter. -/
theorem cellAt_eq_of_mem (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0)
    {b c : α} {y : ℝ} (h1 : y ∈ cellAt P γ lam b) (h2 : y ∈ cellAt P γ lam c) :
    b = c := by
  by_contra hne
  have h := disjoint_cellOf (IETDatum₂.vertex P γ) (lamAfter P γ lam) hne
  rw [cellOf_node, cellOf_node] at h
  exact (Set.disjoint_left.mp h) h1 h2

/-- The height does not decrease in a false step. -/
theorem height_le_succ_false {P : IETDatum₂ α n} (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) (b : α) :
    IETDatum₂.Path.height P γ b ≤ IETDatum₂.Path.height P (γ ++ [false]) b := by
  rw [height_succ hP hn γ false b]
  split <;> omega

/-- The height does not change in a true step, off the secondary letter. -/
theorem height_succ_ne {P : IETDatum₂ α n} (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) (e : Bool) {c : α} (hc : c ≠ (IETDatum₂.vertex P γ).last (!e)) :
    IETDatum₂.Path.height P (γ ++ [e]) c = IETDatum₂.Path.height P γ c := by
  rw [height_succ hP hn γ e c, ite_eq_right hc, add_zero]

/-- The height recursion at the secondary letter of a true step. -/
theorem height_succ_true_scd {P : IETDatum₂ α n} (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) :
    IETDatum₂.Path.height P (γ ++ [true]) ((IETDatum₂.vertex P γ).last false)
      = IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last false)
        + IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last true) := by
  rw [height_succ hP hn γ true, Bool.not_true, ite_eq_left rfl]

/-- The height recursion at the secondary letter of a false step. -/
theorem height_succ_false_scd {P : IETDatum₂ α n} (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) :
    IETDatum₂.Path.height P (γ ++ [false]) ((IETDatum₂.vertex P γ).last true)
      = IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last true)
        + IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last false) := by
  rw [height_succ hP hn γ false, Bool.not_false, ite_eq_left rfl]

/-- **The level-one decomposition of the level base.**  The base interval at the node `γ` is the
disjoint union of the first `Path.height … [e]` iterates of the level-`γ ++ [e]` cells. -/
theorem levelOne_decomposition {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) (e : Bool) (hOK : IsRauzyPath P lam (γ ++ [e])) :
    Set.Ico 0 (baseLen P γ lam)
      = ⋃ b, ⋃ i : Fin (IETDatum₂.Path.height (IETDatum₂.vertex P γ) [e] b),
          (nodeExch P γ lam)^[(i : ℕ)] '' cellAt P (γ ++ [e]) lam b := by
  obtain ⟨-, hS⟩ := (isRauzyPath_append_singleton P lam γ e).mp hOK
  have hne (e' : Bool) : (IETDatum₂.vertex P γ).last e' ≠ (IETDatum₂.vertex P γ).last (!e') :=
      IETDatum₂.vertex_last_ne_not P hP hn γ e'
  have hcell (b : α) : cellAt P (γ ++ [e]) lam b
      = cellAt (IETDatum₂.vertex P γ) [e] (lamAfter P γ lam) b :=
          cellAt_succ P γ e lam b
  cases e with
  | false =>
    have h := level_tower_false (IETDatum₂.vertex P γ) hne
      (lamAfter P γ lam) hS
    rw [baseLen_eq_sum, h]
    refine Set.iUnion_congr (fun b => Set.iUnion_congr (fun i => ?_))
    rw [nodeExch_eq, hcell b]
  | true =>
    have h := level_tower_true (IETDatum₂.vertex P γ) hne
      (lamAfter P γ lam) hS
    rw [baseLen_def, h]
    refine Set.iUnion_congr (fun b => Set.iUnion_congr (fun i => ?_))
    rw [nodeExch_eq, hcell b]

/-- A false step lifts a floor of the level-`γ` tower to a floor of the level-`γ ++ [false]` one. -/
theorem cover_step_false {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible)
    (hn : 2 ≤ n) (hlam : lam ∈ simplex α) {γ : List Bool}
    (hOK : IsRauzyPath P lam (γ ++ [false])) {x : ℝ}
    (hx : ∃ (b : α) (j : ℕ), j < IETDatum₂.Path.height P γ b ∧
      x ∈ (⇑(P.toIET lam))^[j] '' cellAt P γ lam b) :
    ∃ (b : α) (j : ℕ), j < IETDatum₂.Path.height P (γ ++ [false]) b ∧
      x ∈ (⇑(P.toIET lam))^[j] '' cellAt P (γ ++ [false]) lam b := by
  obtain ⟨hOK', hS⟩ := (isRauzyPath_append_singleton P lam γ false).mp hOK
  obtain ⟨b, j, hj, y, hy, rfl⟩ := hx
  have hy' : y ∈ Set.Ico 0 (baseLen P γ lam) := cellAt_sub_base P γ lam b hy
  rw [levelOne_decomposition hP hn γ false hOK] at hy'
  obtain ⟨b', hb'⟩ := Set.mem_iUnion.mp hy'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hb'
  obtain ⟨z, hz1, hzy⟩ := hi
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hipos
  · rw [hi0, Function.iterate_zero_apply] at hzy
    rw [← hzy] at hy
    have hsub : cellAt P (γ ++ [false]) lam b' ⊆ cellAt P γ lam b' :=
      cc_sub_false P γ lam b'
    have hbb : b = b' := cellAt_eq_of_mem P γ lam hy (hsub hz1)
    refine ⟨b', j, ?_, ?_⟩
    · rw [hbb] at hj
      exact lt_of_lt_of_le hj (height_le_succ_false hP hn γ b')
    · exact ⟨z, hz1, by rw [hzy]⟩
  · have hi1 : (i : ℕ) = 1 := by
      have h2 := height_singleton_le_two (IETDatum₂.vertex P γ)
        (IETDatum₂.vertex_irreducible P γ hP) hn
        false b'
      omega
    rw [hi1, Function.iterate_one] at hzy
    rw [← hzy] at hy
    have hb't : b' = (IETDatum₂.vertex P γ).last true := by
      have hlt : b' = (IETDatum₂.vertex P γ).last (!false) := by
        by_contra hc
        have h1 := height_singleton_eq_one_of_ne (IETDatum₂.vertex P γ)
          (IETDatum₂.vertex_irreducible P γ hP) hn false hc
        omega
      simpa using hlt
    subst b'
    have hsub : cellAt P (γ ++ [false]) lam ((IETDatum₂.vertex P γ).last true)
        ⊆ cellAt P γ lam ((IETDatum₂.vertex P γ).last true) :=
      cc_sub_false P γ lam _
    have himg : nodeExch P γ lam ''
        cellAt P (γ ++ [false]) lam ((IETDatum₂.vertex P γ).last true)
        ⊆ cellAt P γ lam ((IETDatum₂.vertex P γ).last false) :=
      kk_image_false_scd (P := P) (γ := γ) (lam := lam) hS
    have hKz : nodeExch P γ lam z
        ∈ cellAt P γ lam ((IETDatum₂.vertex P γ).last false) := himg ⟨z, hz1, rfl⟩
    have hbb : b = (IETDatum₂.vertex P γ).last false := cellAt_eq_of_mem P γ lam hy hKz
    have hFRz := FR_list hP hn hlam hOK' ((IETDatum₂.vertex P γ).last true) z (hsub hz1)
    refine ⟨(IETDatum₂.vertex P γ).last true,
      j + IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last true), ?_, ?_⟩
    · have hHs := height_succ_false_scd hP hn γ
      rw [hbb] at hj
      rw [hHs]
      omega
    · exact ⟨z, hz1, by rw [Function.iterate_add_apply, hFRz, hzy]⟩

/-- A true step lifts a floor of the level-`γ` tower to a floor of the level-`γ ++ [true]` one. -/
theorem cover_step_true {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible)
    (hn : 2 ≤ n) (hlam : lam ∈ simplex α) {γ : List Bool}
    (hOK : IsRauzyPath P lam (γ ++ [true])) {x : ℝ}
    (hx : ∃ (b : α) (j : ℕ), j < IETDatum₂.Path.height P γ b ∧
      x ∈ (⇑(P.toIET lam))^[j] '' cellAt P γ lam b) :
    ∃ (b : α) (j : ℕ), j < IETDatum₂.Path.height P (γ ++ [true]) b ∧
      x ∈ (⇑(P.toIET lam))^[j] '' cellAt P (γ ++ [true]) lam b := by
  -- Case on the index `i` of the level-`γ` cell whose image contains the point: for `i = 0` the
  -- point sits in the node's own cell and the step is read off the definitions, for `i > 0` it is
  -- an image of a lower level and the induction hypothesis `hS` applies.
  obtain ⟨hOK', hS⟩ := (isRauzyPath_append_singleton P lam γ true).mp hOK
  obtain ⟨b, j, hj, y, hy, rfl⟩ := hx
  have hy' : y ∈ Set.Ico 0 (baseLen P γ lam) := cellAt_sub_base P γ lam b hy
  rw [levelOne_decomposition hP hn γ true hOK] at hy'
  obtain ⟨b', hb'⟩ := Set.mem_iUnion.mp hy'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hb'
  obtain ⟨z, hz1, hzy⟩ := hi
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hipos
  · rw [hi0, Function.iterate_zero_apply] at hzy
    rw [← hzy] at hy
    by_cases hbs : b' = (IETDatum₂.vertex P γ).last false
    · subst b'
      have hsub : cellAt P (γ ++ [true]) lam ((IETDatum₂.vertex P γ).last false)
          ⊆ cellAt P γ lam ((IETDatum₂.vertex P γ).last true) :=
        cc_sub_true_scd (P := P) (γ := γ) (lam := lam) hS
      have hbb : b = (IETDatum₂.vertex P γ).last true := cellAt_eq_of_mem P γ lam hy (hsub hz1)
      refine ⟨(IETDatum₂.vertex P γ).last false, j, ?_, ?_⟩
      · have hHs := height_succ_true_scd hP hn γ
        rw [hbb] at hj
        rw [hHs]
        omega
      · exact ⟨z, hz1, by rw [hzy]⟩
    · have hsub : cellAt P (γ ++ [true]) lam b' ⊆ cellAt P γ lam b' :=
        cc_sub_true (P := P) (γ := γ) (lam := lam) hS b' hbs
      have hbb : b = b' := cellAt_eq_of_mem P γ lam hy (hsub hz1)
      refine ⟨b', j, ?_, ?_⟩
      · have hHs := height_succ_ne hP hn γ true (c := b') (by simpa using hbs)
        rw [hbb] at hj
        rw [hHs]
        exact hj
      · exact ⟨z, hz1, by rw [hzy]⟩
  · have hi1 : (i : ℕ) = 1 := by
      have h2 := height_singleton_le_two (IETDatum₂.vertex P γ)
        (IETDatum₂.vertex_irreducible P γ hP) hn
        true b'
      omega
    rw [hi1, Function.iterate_one] at hzy
    rw [← hzy] at hy
    have hb'f : b' = (IETDatum₂.vertex P γ).last false := by
      have hlt : b' = (IETDatum₂.vertex P γ).last (!true) := by
        by_contra hc
        have h1 := height_singleton_eq_one_of_ne (IETDatum₂.vertex P γ)
          (IETDatum₂.vertex_irreducible P γ hP) hn true hc
        omega
      simpa using hlt
    subst b'
    have hsub : cellAt P (γ ++ [true]) lam ((IETDatum₂.vertex P γ).last false)
        ⊆ cellAt P γ lam ((IETDatum₂.vertex P γ).last true) :=
      cc_sub_true_scd (P := P) (γ := γ) (lam := lam) hS
    have himg : nodeExch P γ lam ''
        cellAt P (γ ++ [true]) lam ((IETDatum₂.vertex P γ).last false)
        ⊆ cellAt P γ lam ((IETDatum₂.vertex P γ).last false) :=
      kk_image_true_scd (P := P) (γ := γ) (lam := lam) hS
    have hKz : nodeExch P γ lam z
        ∈ cellAt P γ lam ((IETDatum₂.vertex P γ).last false) := himg ⟨z, hz1, rfl⟩
    have hbb : b = (IETDatum₂.vertex P γ).last false := cellAt_eq_of_mem P γ lam hy hKz
    have hFRz := FR_list hP hn hlam hOK' ((IETDatum₂.vertex P γ).last true) z (hsub hz1)
    refine ⟨(IETDatum₂.vertex P γ).last false,
      j + IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last true), ?_, ?_⟩
    · have hHs := height_succ_true_scd hP hn γ
      rw [hbb] at hj
      rw [hHs]
      omega
    · exact ⟨z, hz1, by rw [Function.iterate_add_apply, hFRz, hzy]⟩

end IntervalExchange.RauzyVeech
