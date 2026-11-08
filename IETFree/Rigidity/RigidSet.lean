/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.Tower.Tiling
public import IETFree.Rigidity.Defs

/-!
# The rigid set at a good node

This module is the geometric heart of the rigid step.  At a node `γ` of the greedy Rauzy path of a
length vector `lam`, with renormalised lengths `σ = lamAfter P γ lam`:

* the exchange `T = P.toIET lam` raised to the height `height P γ b` of the letter `b` acts on the
  level cell `cellAt P γ lam b` as a single translation `y ↦ y + τ`, with
  `|τ| ≤ baseLen P γ lam - σ b` (`exists_translation_eq_on_cellAt`);
* consequently, when the cell of `b` occupies a proportion `≥ 1 - δ` of the base, the set
  `B = ⋃_{i < height P γ b} T^i (cellAt ∩ (cellAt - τ))` has measure at least
  `(1 - 2δ) · baseLen · height` and `T^[height]` is the translation `x ↦ x + τ` on `B`
  (`exists_rigid_set`).

The first item is Veech's `(3.3)`–`(3.8)`; the second is where the exactness of the translation on
the floors is used (`SH_list`, proved here by induction on the word) and is what makes the
conclusion of `IsRigidByTranslations` exact rather than approximate.

The hypotheses are exactly those of `rigid_step`: `IsRauzyPath P lam γ` and nothing else. In
particular
`lam` need not be in the open simplex (`simplex` allows zero coordinates, and on that boundary the
stopping hypothesis is vacuous), and `λ` need not lie in the cylinder of the empty word. The tower
decomposition of `TowerTiling` is stated for an *infinite* nested sequence of
words; here only the levels up to `|γ|` exist, and the prefix sequence cannot be continued past
`|γ|` (the renormalised lengths at the node can have equal last letters, after which no step is
`IsRauzyStep`). So

The blueprint's §2–§7 re-prove the tower statements by induction on the word, which is the form the
rigid step
needs: `SH_list`, `FR_list`, `TL_node`, `CV_node`, `sigma_disjoint_node`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal
open IntervalExchange.RauzyVeech

namespace IntervalExchange.Rigidity

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. `T` is a translation on a level cell, up to its height -/

/-- The exchange acts on a cell as the translation by its own translation vector. -/
private theorem mkIETFun_eq_add_of_mem {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0} {i : Fin n}
    {y : ℝ} (hC : y ∈ Set.Ico (leftEnd lam i) (upperEnd lam i)) :
    mkIETFun lam π 0 y = y + translationVector π lam i := by
  have htot : y ∈ Set.Ico 0 (totalLength lam) :=
    ⟨le_trans (leftEnd_nonneg lam i) hC.1, lt_of_lt_of_le hC.2 (upperEnd_le_total lam i)⟩
  rw [mkIETFun_zero_of_mem htot, idx_eq lam htot hC.1 hC.2]

omit [NeZero n] in
/-- The translation vector of a cell is bounded by the total length minus the length of the
cell. -/
private theorem abs_translationVector_le (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0)
    (i : Fin n) :
    |translationVector π lam i| ≤ (∑ j, (lam j : ℝ)) - (lam i : ℝ) := by
  have h1 := imageLeft_add_le_total π lam i
  have h2 := leftEnd_add_le_total lam i
  have h3 := imageLeft_nonneg π lam i
  have h4 := leftEnd_nonneg lam i
  rw [translationVector, abs_le]
  constructor <;> linarith

/-- **The rigid set, in interval form.**  Let `T` act as a single translation `y ↦ y + ρ_j` on the
whole interval `C = [u,v)` for every `j ≤ h`, and as `y ↦ y + τ` at time `h`; suppose that the first
`h` images `T^j(C)` are disjoint and inside `[0,1)`, and that `τ` is small compared with the length
`Le` of the base and with the length `v - u` of `C`.  Then the union of the first `h` floors of the
inner set `{y ∈ C | y + τ ∈ C}` (an interval of length `(v-u) - |τ|`) has measure
`h · ((v-u) - |τ|) ≥ (1-2δ) · Le · h` and `T^[h]` is the translation by `τ` on it. -/
private theorem rigid_set_abstract (T : ℝ → ℝ) {u v Le τ δ : ℝ} {h : ℕ}
    (hLe : 0 ≤ Le) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (hτle : |τ| ≤ Le - (v - u)) (hbig : (1 - δ) * Le ≤ v - u)
    (hSH : ∀ j ≤ h, ∃ ρ : ℝ, ∀ y ∈ Set.Ico u v, T^[j] y = y + ρ)
    (hT : ∀ y ∈ Set.Ico u v, T^[h] y = y + τ)
    (hmaps : ∀ (j : ℕ) ⦃y : ℝ⦄, y ∈ Set.Ico u v → T^[j] y ∈ Set.Ico (0 : ℝ) 1)
    (hdisj : ∀ j j' : ℕ, j < h → j' < h → j ≠ j' →
      Disjoint (T^[j] '' Set.Ico u v) (T^[j'] '' Set.Ico u v)) :
    ∃ B : Set ℝ, B ⊆ Set.Ico (0:ℝ) 1 ∧ MeasurableSet B ∧
      (1 - 2 * δ) * Le * (h : ℝ) ≤ (volume B).toReal ∧
      ∀ x ∈ B, T^[h] x = x + τ := by
  -- the inner set, an interval
  set E : Set ℝ := Set.Ico (max u (u - τ)) (min v (v - τ)) with hE
  have hEin (y) (hy : y ∈ E) : y ∈ Set.Ico u v := by
    rw [hE] at hy
    simp only [Set.mem_Ico] at hy ⊢
    exact ⟨le_trans (le_max_left u (u - τ)) hy.1,
      lt_of_lt_of_le hy.2 (min_le_left v (v - τ))⟩
  have hEshift (y) (hy : y ∈ E) : y + τ ∈ Set.Ico u v := by
    rw [hE] at hy
    simp only [Set.mem_Ico] at hy ⊢
    exact ⟨by linarith [le_max_right u (u - τ), hy.1],
      by linarith [min_le_right v (v - τ), hy.2]⟩
  have hEle : min v (v - τ) - max u (u - τ) = (v - u) - |τ| := by
    by_cases hτ : 0 ≤ τ
    · rw [abs_of_nonneg hτ, min_eq_right (by linarith : v - τ ≤ v),
        max_eq_left (by linarith : u - τ ≤ u)]
      ring
    · have hτ' : τ < 0 := lt_of_not_ge hτ
      rw [abs_of_neg hτ', min_eq_left (by linarith : v ≤ v - τ),
        max_eq_right (by linarith : u ≤ u - τ)]
      ring
  have hkey : (1 - 2 * δ) * Le ≤ (v - u) - |τ| := by
    have h2 : (1 - 2 * δ) * Le ≤ 2 * (v - u) - Le := by nlinarith [hbig]
    linarith [hτle]
  have hElen : 0 ≤ min v (v - τ) - max u (u - τ) := by
    rw [hEle]
    exact le_trans (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - 2 * δ) hLe) hkey
  have hEvol : (volume E).toReal = (v - u) - |τ| := by
    rw [hE, Real.volume_Ico, ENNReal.toReal_ofReal hElen, hEle]
  -- the floors of `E` are intervals of the same length
  have hfloor (j) (hj : j < h) : ∃ a b : ℝ, T^[j] '' E = Set.Ico a b ∧ b - a = (v - u) - |τ| := by
    obtain ⟨ρ, hρ⟩ := hSH j (le_of_lt hj)
    refine ⟨max u (u - τ) + ρ, min v (v - τ) + ρ, ?_, ?_⟩
    · rw [hE]
      exact image_Ico_of_translation rfl
        (fun y hy => hρ y (hEin y (by rw [hE]; exact hy)))
    · have := hEle
      linarith
  have hmeas (j) (hj : j < h) : MeasurableSet (T^[j] '' E) := by
    obtain ⟨a, b, h1, -⟩ := hfloor j hj
    rw [h1]
    exact measurableSet_Ico
  have hvolfloor (j) (hj : j < h) : (volume (T^[j] '' E)).toReal = (v - u) - |τ| := by
    obtain ⟨a, b, h1, h2⟩ := hfloor j hj
    have h0 : 0 ≤ b - a := by rw [h2, ← hEvol]; exact ENNReal.toReal_nonneg
    rw [h1, Real.volume_Ico, ENNReal.toReal_ofReal h0, h2]
  have hdisjE (j j') (hj : j < h) (hj' : j' < h) (hne : j ≠ j') : Disjoint (T^[j] '' E)
      (T^[j'] '' E) := (hdisj j j' hj hj' hne).mono
      (Set.image_mono (fun y hy => hEin y hy)) (Set.image_mono (fun y hy => hEin y hy))
  refine ⟨⋃ j ∈ Finset.range h, T^[j] '' E, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop] at hx
    obtain ⟨j, hj, y, hy, rfl⟩ := hx
    exact hmaps j (hEin y hy)
  · exact MeasurableSet.biUnion (Finset.countable_toSet _)
      (fun j hj => hmeas j (Finset.mem_range.mp hj))
  · have hsum : volume (⋃ j ∈ Finset.range h, T^[j] '' E)
        = ∑ j ∈ Finset.range h, volume (T^[j] '' E) :=
      measure_biUnion_finset
        (fun j hj j' hj' hne => hdisjE j j' (Finset.mem_range.mp hj) (Finset.mem_range.mp hj') hne)
        (fun j hj => hmeas j (Finset.mem_range.mp hj))
    have hBvol : (volume (⋃ j ∈ Finset.range h, T^[j] '' E)).toReal
        = (h : ℝ) * ((v - u) - |τ|) := by
      rw [hsum, ENNReal.toReal_sum (fun j hj => ?_), Finset.sum_congr rfl
        (fun j hj => hvolfloor j (Finset.mem_range.mp hj)), Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      obtain ⟨a, b, h1, -⟩ := hfloor j (Finset.mem_range.mp hj)
      rw [h1, Real.volume_Ico]
      exact ENNReal.ofReal_ne_top
    rw [hBvol]
    have h2 : (0:ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
    calc (1 - 2 * δ) * Le * (h : ℝ) = ((1 - 2 * δ) * Le) * (h : ℝ) := by ring
      _ ≤ ((v - u) - |τ|) * (h : ℝ) := mul_le_mul_of_nonneg_right hkey h2
      _ = (h : ℝ) * ((v - u) - |τ|) := by ring
  · intro x hx
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop] at hx
    obtain ⟨j, hj, y, hy, rfl⟩ := hx
    obtain ⟨ρ, hρ⟩ := hSH j (le_of_lt hj)
    have h1 : T^[h] y = y + τ := hT y (hEin y hy)
    have h2 : T^[j] (y + τ) = (y + τ) + ρ := hρ (y + τ) (hEshift y hy)
    have h3 : T^[j] y = y + ρ := hρ y (hEin y hy)
    have e1 : T^[h] (T^[j] y) = T^[h + j] y :=
      (Function.iterate_add_apply (f := T) h j y).symm
    have e2 : T^[h + j] y = T^[j + h] y := by rw [Nat.add_comm]
    have e3 : T^[j + h] y = T^[j] (T^[h] y) := Function.iterate_add_apply (f := T) j h y
    rw [e1, e2, e3, h1, h2, h3]
    ring

/-! ## 2. The tower at a node of a finite word

`TowerTiling` develops the tower decomposition along an infinite nested sequence of
words.  At a node `γ` of an `IsRauzyPath` word only the levels up to `|γ|` exist, and the sequence
of prefixes of `γ` cannot be continued past `|γ|` in general (the renormalised lengths at the node
may have equal last letters, in which case no Rauzy step is `IsRauzyStep`).  So the statements of
`TowerTiling` are re-proved here by induction on the *word*, with the single hypothesis
`IsRauzyPath P lam γ`: this is the form the rigid step needs, and it is where the boundary of the
simplex (`lam` with a zero coordinate) is allowed.
-/

/-- **`T` is a translation on a level cell, up to its height.**  For every `j ≤ height P γ b` the
`j`-th iterate of `T` is a single translation on the whole level-`γ` cell of `b`. -/
private theorem SH_list {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible) (hn : 2 ≤ n)
    (hlam : lam ∈ simplex α) {γ : List Bool} (hOK : IsRauzyPath P lam γ) (b : α) (j : ℕ)
    (hj : j ≤ IETDatum₂.Path.height P γ b) : ∃ τ : ℝ,
      ∀ y ∈ cellAt P γ lam b, (⇑(P.toIET lam))^[j] y = y + τ := by
  induction γ using List.reverseRecOn generalizing b j with
  | nil =>
    -- at the empty word the height is at most one: the iterate is the identity or one step
    rw [height_nil] at hj
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with h0 | h1
    · exact ⟨0, fun y _ => by rw [h0, Function.iterate_zero_apply, add_zero]⟩
    · refine ⟨translationVector P.perm (P.lengthsInBottom lam) (P.piBottom b), fun y hy => ?_⟩
      rw [cellAt_nil] at hy
      rw [h1, Function.iterate_one, coe_toIET hlam]
      exact mkIETFun_eq_add_of_mem hy
  | append_singleton γ e ih =>
    -- take the last step of the word apart: its data and the recursion for the heights
    obtain ⟨hOK', hS⟩ := (isRauzyPath_append_singleton P lam γ e).mp hOK
    have hHs := height_succ hP hn γ e b
    -- the letter `b` is moved by that step exactly when it is the last letter on one of its sides
    by_cases hb : b = (IETDatum₂.vertex P γ).last (!e)
    · have hheight : IETDatum₂.Path.height P (γ ++ [e]) b
          = IETDatum₂.Path.height P γ b
            + IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last e) := by
        rw [hHs, ite_eq_left hb]
      -- if it is moved, `j` either lies in the source cell or continues into the image cell
      rw [hb] at hj hheight ⊢
      have hsub : cellAt P (γ ++ [e]) lam ((IETDatum₂.vertex P γ).last (!e))
          ⊆ cellAt P γ lam ((IETDatum₂.vertex P γ).last true) := by
        cases e
        · exact cc_sub_false P γ lam _
        · exact cc_sub_true_scd (P := P) (γ := γ) (lam := lam) hS
      have himg : nodeExch P γ lam ''
          cellAt P (γ ++ [e]) lam ((IETDatum₂.vertex P γ).last (!e))
          ⊆ cellAt P γ lam ((IETDatum₂.vertex P γ).last false) := by
        cases e
        · exact kk_image_false_scd (P := P) (γ := γ) (lam := lam) hS
        · exact kk_image_true_scd (P := P) (γ := γ) (lam := lam) hS
      by_cases hj1 : j ≤ IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last true)
      · obtain ⟨τ, hτ⟩ := ih hOK' _ j hj1
        exact ⟨τ, fun y hy => hτ y (hsub hy)⟩
      · push Not at hj1
        have hjp : j - IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last true)
            ≤ IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last false) := by
          rw [hheight] at hj
          by_cases he : e = false
          · subst he
            simp only [Bool.not_false] at hj
            omega
          · have he' : e = true := by cases e <;> simp_all
            subst he'
            simp only [Bool.not_true] at hj
            omega
        obtain ⟨τ1, hτ1⟩ := ih hOK' ((IETDatum₂.vertex P γ).last true)
          (IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last true)) le_rfl
        obtain ⟨τ2, hτ2⟩ := ih hOK' ((IETDatum₂.vertex P γ).last false)
          (j - IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last true)) hjp
        refine ⟨τ1 + τ2, fun y hy => ?_⟩
        have hmem1 : y ∈ cellAt P γ lam ((IETDatum₂.vertex P γ).last true) := hsub hy
        have hmem2 : nodeExch P γ lam y
            ∈ cellAt P γ lam ((IETDatum₂.vertex P γ).last false) := himg ⟨y, hy, rfl⟩
        have hfr := FR_list hP hn hlam hOK' _ y hmem1
        have e1 : j = (j - IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last true))
            + IETDatum₂.Path.height P γ ((IETDatum₂.vertex P γ).last true) := by omega
        rw [e1, Function.iterate_add_apply, hfr, hτ2 _ hmem2, ← hfr, hτ1 y hmem1]
        ring
    -- a letter the step does not move keeps its cell, shrunk, so the induction hypothesis descends
    · have hheight : IETDatum₂.Path.height P (γ ++ [e]) b = IETDatum₂.Path.height P γ b := by
        rw [hHs, ite_eq_right hb, add_zero]
      rw [hheight] at hj
      obtain ⟨τ, hτ⟩ := ih hOK' b j hj
      refine ⟨τ, fun y hy => hτ y ?_⟩
      cases e with
      | false => exact cc_sub_false P γ lam b hy
      | true => exact cc_sub_true (P := P) (γ := γ) (lam := lam) hS b (by simpa using hb) hy

/-- The level-`γ` cell, unfolded to its interval endpoints. -/
private theorem cellAt_Ico (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) (b : α) :
    cellAt P γ lam b
      = Set.Ico (leftEnd ((IETDatum₂.vertex P γ).lengthsInBottom (lamAfter P γ lam))
            ((IETDatum₂.vertex P γ).piBottom b))
          (upperEnd ((IETDatum₂.vertex P γ).lengthsInBottom (lamAfter P γ lam))
            ((IETDatum₂.vertex P γ).piBottom b)) := (rfl)

/-- **`T` is a translation on a level cell, up to its height.**  Veech's (3.3)–(3.4) at the node:
the `height P γ b`-th iterate of `T` is a single translation on the whole cell of `b`, with a
translation vector bounded by the base length minus the length of that cell. -/
theorem exists_translation_eq_on_cellAt {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {lam : α → ℝ≥0}
    (hlam : lam ∈ simplex α)
    {γ : List Bool} {b : α} (hOK : IsRauzyPath P lam γ) :
    ∃ τ : ℝ,
      (∀ y ∈ cellAt P γ lam b, (⇑(P.toIET lam))^[IETDatum₂.Path.height P γ b] y = y + τ) ∧
      |τ| ≤ baseLen P γ lam - (lamAfter P γ lam b : ℝ) := by
  refine ⟨translationVector (IETDatum₂.vertex P γ).perm
      ((IETDatum₂.vertex P γ).lengthsInBottom (lamAfter P γ lam))
      ((IETDatum₂.vertex P γ).piBottom b), ?_, ?_⟩
  · intro y hy
    rw [FR_list hP hn hlam hOK b y hy, nodeExch_eq]
    rw [cellAt_Ico] at hy
    exact mkIETFun_eq_add_of_mem hy
  · have hsum : (∑ k, (((IETDatum₂.vertex P γ).lengthsInBottom
        (lamAfter P γ lam)) k : ℝ))
        = ∑ a, (lamAfter P γ lam a : ℝ) :=
      totalLength_lengthsInBottom _ _
    have hval : (((IETDatum₂.vertex P γ).lengthsInBottom (lamAfter P γ lam))
        ((IETDatum₂.vertex P γ).piBottom b) : ℝ) = (lamAfter P γ lam b : ℝ) := by
      simp only [IETDatum₂.lengthsInBottom, Equiv.symm_apply_apply]
    have h := abs_translationVector_le (IETDatum₂.vertex P γ).perm
      ((IETDatum₂.vertex P γ).lengthsInBottom (lamAfter P γ lam))
      ((IETDatum₂.vertex P γ).piBottom b)
    rw [hsum, hval] at h
    exact h

/-! ## 3. The mass of the base, the floors, and the total-mass identity -/

/-- The base length at a node is at most one. -/
private theorem baseLen_le_one {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hlam : lam ∈ simplex α)
    (γ : List Bool) : baseLen P γ lam ≤ 1 :=
  le_trans (totalLength_lamAfter_le P lam γ) (le_of_eq (sum_coe_eq_one hlam))

/-- A level cell sits in the unit interval. -/
private theorem cellAt_sub_one {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hlam : lam ∈ simplex α)
    (γ : List Bool) (b : α) : cellAt P γ lam b ⊆ Set.Ico (0:ℝ) 1 :=
  cellAt_subset_totalLength_le P γ lam b (baseLen_le_one hlam γ)

/-- Every floor of a level cell sits in the unit interval. -/
private theorem floor_subset_unit {P : IETDatum₂ α n} {lam : α → ℝ≥0}
    (hlam : lam ∈ simplex α) (γ : List Bool) (b : α) (j : ℕ) :
    (⇑(P.toIET lam))^[j] '' cellAt P γ lam b ⊆ Set.Ico (0:ℝ) 1 := by
  rw [coe_toIET hlam]
  rintro x ⟨y, hy, rfl⟩
  exact mkIETFun_iterate_mapsTo_one hlam j (cellAt_sub_one hlam γ b hy)

/-- Every floor of a level cell is measurable. -/
private theorem measurableSet_floor_node {P : IETDatum₂ α n} {lam : α → ℝ≥0}
    (hlam : lam ∈ simplex α) (γ : List Bool) (b : α) (j : ℕ) :
    MeasurableSet ((⇑(P.toIET lam))^[j] '' cellAt P γ lam b) := by
  rw [coe_toIET hlam]
  exact measurableSet_image_iterate P.perm (P.lengthsInBottom lam) measurableSet_Ico j

/-- Every floor of a level cell is an interval of the length of that cell. -/
private theorem floor_Ico_node {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible)
    (hn : 2 ≤ n) (hlam : lam ∈ simplex α) {γ : List Bool} (hOK : IsRauzyPath P lam γ)
    (b : α) (j : ℕ) (hj : j ≤ IETDatum₂.Path.height P γ b) :
    ∃ u v : ℝ, (⇑(P.toIET lam))^[j] '' cellAt P γ lam b = Set.Ico u v ∧
      v - u = (lamAfter P γ lam b : ℝ) := by
  obtain ⟨τ, hτ⟩ := SH_list hP hn hlam hOK b j hj
  refine ⟨leftEnd ((IETDatum₂.vertex P γ).lengthsInBottom (lamAfter P γ lam))
        ((IETDatum₂.vertex P γ).piBottom b) + τ,
      upperEnd ((IETDatum₂.vertex P γ).lengthsInBottom (lamAfter P γ lam))
        ((IETDatum₂.vertex P γ).piBottom b) + τ, ?_, ?_⟩
  · exact image_Ico_of_translation (cellAt_Ico P γ lam b)
      (fun y hy => hτ y hy)
  · rw [upperEnd_eq, IETDatum₂.lengthsInBottom, Equiv.symm_apply_apply]
    ring

/-- The height, as a real sum. -/
private theorem height_coe (P : IETDatum₂ α n) (γ : List Bool) (b : α) :
    (IETDatum₂.Path.height P γ b : ℝ) = ∑ a, ((IETDatum₂.Path.Q P γ a b).toNat : ℝ) := by
  simp only [IETDatum₂.Path.height]
  push_cast
  rfl

/-- **The total-mass identity at a node**: `∑_b h_b · σ_b = 1`, Veech's (3.1) at the node. -/
private theorem TL_node {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible) (hn : 2 ≤ n)
    (hlam : lam ∈ simplex α) {γ : List Bool} (hOK : IsRauzyPath P lam γ) :
    (∑ b, (IETDatum₂.Path.height P γ b : ℝ) * (lamAfter P γ lam b : ℝ)) = 1 := by
  calc (∑ b, (IETDatum₂.Path.height P γ b : ℝ) * (lamAfter P γ lam b : ℝ))
      = ∑ b, (∑ a, ((IETDatum₂.Path.Q P γ a b).toNat : ℝ))
          * (lamAfter P γ lam b : ℝ) :=
        Finset.sum_congr rfl (fun b _ => by rw [height_coe])
    _ = ∑ b, ∑ a, ((IETDatum₂.Path.Q P γ a b).toNat : ℝ)
          * (lamAfter P γ lam b : ℝ) :=
        Finset.sum_congr rfl (fun b _ => Finset.sum_mul _ _ _)
    _ = ∑ a, ∑ b, ((IETDatum₂.Path.Q P γ a b).toNat : ℝ)
          * (lamAfter P γ lam b : ℝ) := Finset.sum_comm
    _ = ∑ a, (lam a : ℝ) :=
        Finset.sum_congr rfl (fun a _ => renorm_apply P hP hn hOK a)
    _ = 1 := sum_coe_eq_one hlam

/-! ## 4. The level-one decomposition, and the covering of the base -/

/-- The level-`γ` cell of the empty node is the cell of the initial partition. -/
private theorem cellAt_nil_cellOf (P : IETDatum₂ α n) (lam : α → ℝ≥0) (b : α) :
    cellAt P [] lam b = cellOf P lam b := (rfl)

/-- **The floors of the level-`γ` tower cover the unit interval.** -/
private theorem CV_node {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible) (hn : 2 ≤ n)
    (hlam : lam ∈ simplex α) {γ : List Bool} (hOK : IsRauzyPath P lam γ) (x : ℝ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) : ∃ (b : α) (j : ℕ), j < IETDatum₂.Path.height P γ b ∧
      x ∈ (⇑(P.toIET lam))^[j] '' cellAt P γ lam b := by
  induction γ using List.reverseRecOn generalizing x with
  | nil =>
    have hx' : x ∈ Set.Ico (0 : ℝ) (∑ i, (P.lengthsInBottom lam i : ℝ)) := by
      have h1 : (∑ i, (P.lengthsInBottom lam i : ℝ)) = ∑ a, (lam a : ℝ) :=
        totalLength_lengthsInBottom P lam
      have h2 : (∑ a, (lam a : ℝ)) = 1 := sum_coe_eq_one hlam
      rw [h1, h2]
      exact hx
    refine ⟨P.piBottom.symm (idx (P.lengthsInBottom lam) x hx'.1), 0, ?_, ?_⟩
    · rw [height_nil]
      exact Nat.one_pos
    · refine ⟨x, ?_, by simp⟩
      rw [cellAt_nil_cellOf]
      exact mem_cellOf_idx P lam hx'
  | append_singleton γ e ih =>
    have hOK' : IsRauzyPath P lam γ :=
      (isRauzyPath_append_singleton P lam γ e).mp hOK |>.1
    cases e with
    | false => exact cover_step_false hP hn hlam hOK (ih hOK' x hx)
    | true => exact cover_step_true hP hn hlam hOK (ih hOK' x hx)

/-- **The floors of one level are pairwise disjoint.**  Veech's (3.5) at the node: the floors
`T^j (cellAt P γ lam b)`, `j < height P γ b`, are pairwise disjoint.  They are intervals of total
length `1` inside `[0,1)` which cover `[0,1)`, so two of them cannot meet in an interval of positive
length. -/
private theorem sigma_disjoint_node {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible)
    (hn : 2 ≤ n) (hlam : lam ∈ simplex α) {γ : List Bool} (hOK : IsRauzyPath P lam γ)
    (p q : (Σ b : α, Fin (IETDatum₂.Path.height P γ b))) (hpq : p ≠ q) :
      Disjoint ((⇑(P.toIET lam))^[(p.2 : ℕ)] '' cellAt P γ lam p.1)
        ((⇑(P.toIET lam))^[(q.2 : ℕ)] '' cellAt P γ lam q.1) := by
  -- the floors of the level: the iterates `T^j` of a cell, for `j` below its height
  set fr : (Σ b : α, Fin (IETDatum₂.Path.height P γ b)) → Set ℝ :=
    fun r => (⇑(P.toIET lam))^[(r.2 : ℕ)] '' cellAt P γ lam r.1 with hfr
  -- each floor is a half-open interval inside `[0, 1)`, of the rescaled length of its letter
  have hIco (r : (Σ b : α, Fin (IETDatum₂.Path.height P γ b))) :
    ∃ u v : ℝ, fr r = Set.Ico u v ∧ v - u = (lamAfter P γ lam r.1 : ℝ) := by
    exact floor_Ico_node hP hn hlam hOK r.1 (r.2 : ℕ) (le_of_lt r.2.isLt)
  have hvol (r) : volume (fr r) = ENNReal.ofReal (lamAfter P γ lam r.1 : ℝ) := by
    obtain ⟨u, v, h1, h2⟩ := hIco r
    rw [h1, Real.volume_Ico, h2]
  have hfin (r) : volume (fr r) ≠ ⊤ := by
    rw [hvol r]
    exact ENNReal.ofReal_ne_top
  have hbdd (S : Set ℝ) (hS : S ⊆ Set.Ico (0 : ℝ) 1) : volume S ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hS)
    rw [Real.volume_Ico, sub_zero, ENNReal.ofReal_one]
    exact ENNReal.one_ne_top
  have hmeas (r) : MeasurableSet (fr r) := by
    exact measurableSet_floor_node hlam γ r.1 (r.2 : ℕ)
  have hsub (r) : fr r ⊆ Set.Ico (0 : ℝ) 1 := by
    exact floor_subset_unit hlam γ r.1 (r.2 : ℕ)
  -- the rescaled lengths add up to one over the whole level, and the floors cover the base
  have hsumR : (∑ r : (Σ b : α, Fin (IETDatum₂.Path.height P γ b)),
      (lamAfter P γ lam r.1 : ℝ)) = 1 := by
    have h2 (b : α) :
      (∑ _j : Fin (IETDatum₂.Path.height P γ b),
        (lamAfter P γ lam b : ℝ)) = (IETDatum₂.Path.height P γ b : ℝ)
          * (lamAfter P γ lam b : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.univ_sigma_univ,
      ← Finset.sum_sigma' (f := fun a (_ : Fin (IETDatum₂.Path.height P γ a)) =>
        (lamAfter P γ lam a : ℝ))]
    rw [Finset.sum_congr rfl (fun a _ => h2 a)]
    exact TL_node hP hn hlam hOK
  have hsum : (∑ r : (Σ b : α, Fin (IETDatum₂.Path.height P γ b)), (volume (fr r)).toReal) = 1 := by
    have h1 (r) : (volume (fr r)).toReal = (lamAfter P γ lam r.1 : ℝ) := by
      rw [hvol r, ENNReal.toReal_ofReal (lamAfter P γ lam r.1).coe_nonneg]
    simp only [h1]
    exact hsumR
  have hunion : (⋃ r : (Σ b : α, Fin (IETDatum₂.Path.height P γ b)), fr r) = Set.Ico (0 : ℝ) 1 := by
    refine Set.Subset.antisymm (Set.iUnion_subset hsub) ?_
    intro x hx
    obtain ⟨b, j, hj, hmem⟩ := CV_node hP hn hlam hOK x hx
    exact Set.mem_iUnion.mpr ⟨⟨b, ⟨j, hj⟩⟩, hmem⟩
  -- so the part of one floor that the others cover is null, the total being exactly one
  have key (p : (Σ b : α, Fin (IETDatum₂.Path.height P γ b))) :
    volume (fr p ∩ ⋃ r ∈ (Finset.univ :
        Finset (Σ b : α, Fin (IETDatum₂.Path.height P γ b))).erase p, fr r) = 0 := by
    set G : Set ℝ := ⋃ r ∈ (Finset.univ : Finset
      (Σ b : α, Fin (IETDatum₂.Path.height P γ b))).erase p, fr r with hG
    have hsplit : (⋃ r ∈ (Finset.univ : Finset (Σ b : α, Fin (IETDatum₂.Path.height P γ b))), fr r)
        = fr p ∪ G := by
      rw [hG]
      conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ p), Finset.set_biUnion_insert]
    have hiunion : (⋃ r : (Σ b : α, Fin (IETDatum₂.Path.height P γ b)), fr r)
        = ⋃ r ∈ (Finset.univ : Finset (Σ b : α, Fin (IETDatum₂.Path.height P γ b))), fr r := by
      ext x
      simp only [Set.mem_iUnion, exists_prop, Finset.mem_univ, true_and]
    have hGmeas : MeasurableSet G :=
      Finset.measurableSet_biUnion _ (fun r _ => hmeas r)
    have hGsub : G ⊆ Set.Ico (0 : ℝ) 1 := by
      rw [hG]
      exact Set.iUnion₂_subset (fun r _ => hsub r)
    have hUsub : fr p ∪ G ⊆ Set.Ico (0 : ℝ) 1 := by
      rw [← hsplit, ← hiunion]
      exact Set.iUnion_subset hsub
    have hadd : volume (fr p ∪ G) + volume (fr p ∩ G) = volume (fr p) + volume G :=
      measure_union_add_inter (fr p) hGmeas
    have e1 : (volume (fr p ∪ G)).toReal + (volume (fr p ∩ G)).toReal
        = (volume (fr p)).toReal + (volume G).toReal := by
      rw [← ENNReal.toReal_add (hbdd _ hUsub) (ne_top_of_le_ne_top (hfin p)
          (measure_mono (Set.inter_subset_left))),
        ← ENNReal.toReal_add (hfin p) (hbdd _ hGsub), hadd]
    have e2 : (volume (fr p ∪ G)).toReal = 1 := by
      rw [← hsplit, ← hiunion, hunion, Real.volume_Ico]
      norm_num
    have hsumG : (∑ r ∈ (Finset.univ : Finset (Σ b : α, Fin (IETDatum₂.Path.height P γ b))).erase p,
        (volume (fr r)).toReal) + (volume (fr p)).toReal = 1 := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ p)]
      exact hsum
    have hle : (volume G).toReal ≤ ∑ r ∈ (Finset.univ : Finset
        (Σ b : α, Fin (IETDatum₂.Path.height P γ b))).erase p, (volume (fr r)).toReal := by
      have h := measure_biUnion_finset_le (μ := volume)
        ((Finset.univ : Finset (Σ b : α, Fin (IETDatum₂.Path.height P γ b))).erase p) fr
      have hfs : (∑ r ∈ (Finset.univ : Finset (Σ b : α, Fin (IETDatum₂.Path.height P γ b))).erase p,
          volume (fr r)) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun r _ => hfin r)
      refine le_trans (ENNReal.toReal_mono hfs h) (le_of_eq ?_)
      exact ENNReal.toReal_sum (fun r _ => hfin r)
    have hx0 : (0 : ℝ) ≤ (volume (fr p ∩ G)).toReal := ENNReal.toReal_nonneg
    have hzero : (volume (fr p ∩ G)).toReal = 0 := by linarith
    rcases (ENNReal.toReal_eq_zero_iff _).mp hzero with h | h
    · exact h
    · exact absurd h (ne_top_of_le_ne_top (hfin p) (measure_mono (Set.inter_subset_left)))
  -- two distinct floors meet in an interval, which is then empty
  have hmem : volume (fr p ∩ fr q) = 0 := by
    refine measure_mono_null ?_ (key p)
    intro x hx
    exact ⟨hx.1, Set.mem_iUnion₂.mpr ⟨q, Finset.mem_erase.mpr
      ⟨fun h => hpq h.symm, Finset.mem_univ q⟩, hx.2⟩⟩
  obtain ⟨u, v, h1, h2⟩ := hIco p
  obtain ⟨u', v', h1', h2'⟩ := hIco q
  have hgoal : fr p ∩ fr q = Set.Ico (u ⊔ u') (v ⊓ v') := by rw [h1, h1', Set.Ico_inter_Ico]
  have hle : v ⊓ v' ≤ u ⊔ u' := by
    by_contra hcon
    push Not at hcon
    have hpos : volume (Set.Ico (u ⊔ u') (v ⊓ v')) ≠ 0 := by
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
    rw [← hgoal] at hpos
    exact hpos hmem
  rw [Set.disjoint_iff_inter_eq_empty, hgoal, Set.Ico_eq_empty_of_le hle]

/-- **The rigid set of a good node.**  If the cell of the letter `b` occupies a proportion `≥ 1 - δ`
of the base at the node `γ` (`δ ≤ 1/4`), then there are a translation vector `t` with
`|t| ≤ δ · baseLen` and a set `B ⊆ [0,1)` of measure at least `(1 - 2δ) · baseLen · height` on which
the `height`-th iterate of `T = P.toIET lam` is exactly the translation `x ↦ x + t`. -/
theorem exists_rigid_set {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {lam : α → ℝ≥0}
    (hlam : lam ∈ simplex α)
    {γ : List Bool} {b : α} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (hOK : IsRauzyPath P lam γ) (hbig : BigCell P γ lam δ b) :
    ∃ (t : ℝ) (B : Set ℝ),
      B ⊆ Set.Ico (0:ℝ) 1 ∧ MeasurableSet B ∧
      (1 - 2 * δ) * baseLen P γ lam * (IETDatum₂.Path.height P γ b : ℝ) ≤ (volume B).toReal ∧
      |t| ≤ δ * baseLen P γ lam ∧
      ∀ x ∈ B, (⇑(P.toIET lam))^[IETDatum₂.Path.height P γ b] x = x + t := by
  obtain ⟨τ, hτ, hτle⟩ := exists_translation_eq_on_cellAt P hP hn hlam hOK
  simp only [BigCell] at hbig
  set σ := lamAfter P γ lam with hσ
  set Le := baseLen P γ lam with hLe
  set hh := IETDatum₂.Path.height P γ b with hhh
  have hvu : upperEnd ((IETDatum₂.vertex P γ).lengthsInBottom σ)
        ((IETDatum₂.vertex P γ).piBottom b)
      - leftEnd ((IETDatum₂.vertex P γ).lengthsInBottom σ) ((IETDatum₂.vertex P γ).piBottom b)
      = (σ b : ℝ) := by
    rw [upperEnd_eq]
    simp only [IETDatum₂.lengthsInBottom, Equiv.symm_apply_apply]
    ring
  obtain ⟨B, hBsub, hBmeas, hBvol, hexact⟩ :=
    rigid_set_abstract (T := ⇑(P.toIET lam))
      (u := leftEnd ((IETDatum₂.vertex P γ).lengthsInBottom σ) ((IETDatum₂.vertex P γ).piBottom b))
      (v := upperEnd ((IETDatum₂.vertex P γ).lengthsInBottom σ) ((IETDatum₂.vertex P γ).piBottom b))
      (Le := Le) (τ := τ) (δ := δ) (h := hh)
      (by rw [hLe, baseLen_eq_sum]
          exact Finset.sum_nonneg (fun a _ => (lamAfter P γ lam a).coe_nonneg))
      hδ hδ1
      (by rw [hLe, hvu]; exact hτle)
      (by rw [hLe, hvu]; exact hbig)
      (fun j hj => by
        obtain ⟨ρ, hρ⟩ := SH_list hP hn hlam hOK b j hj
        exact ⟨ρ, fun y hy => hρ y hy⟩)
      (fun y hy => hτ y hy)
      (fun j y hy => floor_subset_unit hlam γ b j ⟨y, hy, rfl⟩)
      (fun j j' hj hj' hne => by
        refine sigma_disjoint_node hP hn hlam hOK
          ⟨b, (⟨j, hj⟩ : Fin hh)⟩ ⟨b, (⟨j', hj'⟩ : Fin hh)⟩ ?_
        intro h
        exact hne (congrArg (fun r => (r.2 : ℕ)) h))
  exact ⟨τ, B, hBsub, hBmeas, hBvol, by nlinarith [hτle, hbig, hLe], hexact⟩

end IntervalExchange.Rigidity

end
