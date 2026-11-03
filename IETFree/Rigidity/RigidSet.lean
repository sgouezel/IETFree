/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.Rigidity.Defs
import IETFree.RauzyVeech.InvariantMeasure
import IETFree.RauzyVeech.TowerTiling

/-!
# The rigid set at a good node

This module is the geometric heart of the rigid step.  At a node `γ` of the greedy Rauzy path of a
length vector `lam`, with renormalised lengths `σ = lamAfter P γ lam`:

* the exchange `T = P.toIET lam` raised to the height `height P γ b` of the letter `b` acts on the
  level cell `Tower.cellAt P γ lam b` as a single translation `y ↦ y + τ`, with
  `|τ| ≤ baseLen P γ lam - σ b` (`exists_translation_eq_on_cellAt`);
* consequently, when the cell of `b` occupies a proportion `≥ 1 - δ` of the base, the set
  `B = ⋃_{i < height P γ b} T^i (cellAt ∩ (cellAt - τ))` has measure at least
  `(1 - 2δ) · baseLen · height` and `T^[height]` is the translation `x ↦ x + τ` on `B`
  (`exists_rigid_set`).

The first item is Veech's `(3.3)`–`(3.8)`; the second is where the exactness of the translation on
the floors is used (`SH_list`, proved here by induction on the word) and is what makes the
conclusion of `IsRigidByTranslations` exact rather than approximate.

The hypotheses are exactly those of `rigid_step`: `IterOK P lam γ` and nothing else. In
particular
`lam` need not be in the open simplex (`simplexOn` allows zero coordinates, and on that boundary the
stopping hypothesis is vacuous), and `λ` need not lie in the cylinder of the empty word. The tower
decomposition of `TowerInjectivity.TowerTiling` is stated for an *infinite* nested sequence of
words; here only the levels up to `|γ|` exist, and the prefix sequence cannot be continued past
`|γ|` (the renormalised lengths at the node can have equal last letters, after which no step is
`StepOK`). So

§2–§7 re-prove the tower statements by induction on the word, which is the form the rigid step
needs: `SH_list`, `FR_list`, `TL_node`, `CV_node`, `sigma_disjoint_node`.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

namespace IETFree.Rigidity

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 2. `T` is a translation on a level cell, up to its height -/

/-- The left end of a cell plus its length is at most the total: the cells of the bottom order are
disjoint intervals. -/
private theorem leftEnd_add_le_total {d : ℕ} (lam : Fin d → ℝ≥0) (i : Fin d) :
    leftEnd lam i + (lam i : ℝ) ≤ ∑ j, (lam j : ℝ) := by
  have hmem : insert i (Finset.univ.filter (fun j : Fin d => j < i)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset_of_nonneg hmem
    (fun k _ _ => (lam k).coe_nonneg)
  rw [Finset.sum_insert (by simp)] at h
  rw [leftEnd]
  linarith

/-- The exchange acts on a cell as the translation by its own translation vector. -/
private theorem exch_eq_add_of_mem {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0} {i : Fin n}
    {y : ℝ} (hC : y ∈ Set.Ico (leftEnd lam i) (upperEnd lam i)) :
    Tower.exch π lam y = y + translationVector π lam i := by
  have htot : y ∈ Set.Ico 0 (Tower.tot lam) :=
    ⟨le_trans (leftEnd_nonneg lam i) hC.1, lt_of_lt_of_le hC.2 (upperEnd_le_total lam i)⟩
  rw [Tower.exch_of_mem π lam htot, idx_eq lam htot hC.1 hC.2]

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
  classical
  -- the inner set, an interval
  set E : Set ℝ := Set.Ico (max u (u - τ)) (min v (v - τ)) with hE
  have hEin : ∀ y ∈ E, y ∈ Set.Ico u v := by
    intro y hy
    rw [hE] at hy
    simp only [Set.mem_Ico] at hy ⊢
    exact ⟨le_trans (le_max_left u (u - τ)) hy.1,
      lt_of_lt_of_le hy.2 (min_le_left v (v - τ))⟩
  have hEshift : ∀ y ∈ E, y + τ ∈ Set.Ico u v := by
    intro y hy
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
  have hfloor : ∀ j, j < h → ∃ a b : ℝ, T^[j] '' E = Set.Ico a b ∧ b - a = (v - u) - |τ| := by
    intro j hj
    obtain ⟨ρ, hρ⟩ := hSH j (le_of_lt hj)
    refine ⟨max u (u - τ) + ρ, min v (v - τ) + ρ, ?_, ?_⟩
    · rw [hE]
      exact TowerInjectivity.image_Ico_of_translation rfl
        (fun y hy => hρ y (hEin y (by rw [hE]; exact hy)))
    · have := hEle
      linarith
  have hmeas : ∀ j, j < h → MeasurableSet (T^[j] '' E) := by
    intro j hj
    obtain ⟨a, b, h1, -⟩ := hfloor j hj
    rw [h1]
    exact measurableSet_Ico
  have hvolfloor : ∀ j, j < h → (volume (T^[j] '' E)).toReal = (v - u) - |τ| := by
    intro j hj
    obtain ⟨a, b, h1, h2⟩ := hfloor j hj
    have h0 : 0 ≤ b - a := by rw [h2, ← hEvol]; exact ENNReal.toReal_nonneg
    rw [h1, Real.volume_Ico, ENNReal.toReal_ofReal h0, h2]
  have hdisjE : ∀ j j', j < h → j' < h → j ≠ j' →
      Disjoint (T^[j] '' E) (T^[j'] '' E) :=
    fun j j' hj hj' hne => (hdisj j j' hj hj' hne).mono
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

/-! ## 3. The tower at a node of a finite word

`TowerInjectivity.TowerTiling` develops the tower decomposition along an infinite nested sequence of
words.  At a node `γ` of an `IterOK` word only the levels up to `|γ|` exist, and the sequence of
prefixes of `γ` cannot be continued past `|γ|` in general (the renormalised lengths at the node may
have equal last letters, in which case no Rauzy step is `StepOK`).  So the statements of
`TowerTiling` are re-proved here by induction on the *word*, with the single hypothesis
`IterOK P lam γ`: this is the form the rigid step needs, and it is where the boundary of the simplex
(`lam` with a zero coordinate) is allowed.
-/

/-- The exchange at the node `γ`, renormalised to the level-`γ` lengths: the library's
`TowerStep.KK`
at that node. -/
private noncomputable def nodeExch (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) :
    ℝ → ℝ :=
  Tower.exch (IETDatum₂.vertex P γ).perm
    ((IETDatum₂.vertex P γ).lengthsInBottom (Tower.lamAfter P γ lam))

/-- The exchange at the empty node is the exchange of `P` itself. -/
private theorem nodeExch_nil {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hlam : lam ∈ simplexOn α) :
    nodeExch P [] lam = ⇑(P.toIET lam) := by
  simp only [nodeExch, IETDatum₂.vertex_nil, Tower.lamAfter_nil]
  exact (TowerInjectivity.coe_toIET hlam).symm

/-- The exchange at the node `γ`, as a `Tower.exch`. -/
private theorem nodeExch_eq (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) :
    nodeExch P γ lam = Tower.exch (IETDatum₂.vertex P γ).perm
      ((IETDatum₂.vertex P γ).lengthsInBottom (Tower.lamAfter P γ lam)) := rfl

/-- The exchange at the node `γ ++ [e]`, read at the vertex `vertex P γ`. -/
private theorem nodeExch_append (P : IETDatum₂ α n) (γ : List Bool) (e : Bool)
    (lam : α → ℝ≥0) (y : ℝ) :
    nodeExch P (γ ++ [e]) lam y
      = Tower.exch ((IETDatum₂.vertex P γ).rvStep e).perm
          (((IETDatum₂.vertex P γ).rvStep e).lengthsInBottom
            (Tower.hatLam (IETDatum₂.vertex P γ) e (Tower.lamAfter P γ lam))) y := by
  simp only [nodeExch, IETDatum₂.vertex_append_singleton, IterGlue2.lamAfter_append_singleton]

/-- The level-`γ` cell, read as a level-one cell of the vertex `vertex P γ`. -/
private theorem cellAt_node (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) (b : α) :
    Tower.cellAt (IETDatum₂.vertex P γ) [] (Tower.lamAfter P γ lam) b
      = Tower.cellAt P γ lam b := rfl

/-- The height at the empty node is one. -/
private theorem height_nil (P : IETDatum₂ α n) (b : α) : height P [] b = 1 := by
  simp only [height, IETDatum₂.Path.Q]
  refine (Finset.sum_congr rfl (fun x _ => ?_)).trans (TowerInjectivity.sum_ite_single (c := b) 1)
  rw [Matrix.one_apply]
  split_ifs <;> simp

/-- **The height recursion**: passing from `γ` to `γ ++ [e]` adds the height of the letter `e`
exactly when the letter `b` is the *other* last letter of the vertex. -/
private theorem height_succ {P : IETDatum₂ α n} (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) (e : Bool) (b : α) :
    height P (γ ++ [e]) b = height P γ b
      + if b = (IETDatum₂.vertex P γ).last (!e) then
          height P γ ((IETDatum₂.vertex P γ).last e) else 0 := by
  classical
  have hne : ∀ e' : Bool, (IETDatum₂.vertex P γ).last e' ≠ (IETDatum₂.vertex P γ).last (!e') :=
    fun e' => IETDatum₂.vertex_last_ne_not P hP hn γ e'
  have hQ : ∀ a, IETDatum₂.Path.Q P (γ ++ [e]) a b
      = IETDatum₂.Path.Q P γ a b
        + if b = (IETDatum₂.vertex P γ).last (!e) then
            IETDatum₂.Path.Q P γ a ((IETDatum₂.vertex P γ).last e) else 0 := by
    intro a
    rw [IETDatum₂.Path.Q_append, IETDatum₂.Path.Q_singleton, Matrix.mul_apply]
    exact TowerInjectivity.mulVec_rvMat (IETDatum₂.Path.Q P γ) (IETDatum₂.vertex P γ) e
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
  simp only [height]
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
        · simp only [if_pos hb]
        · rw [if_neg hb]
          exact Finset.sum_eq_zero (fun a _ => by simp only [if_neg hb])

/-- The one-step heights are at most two. -/
private theorem hgt1_le_two (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (e : Bool) (c : α) : TowerInjectivity.hgt1 P e c ≤ 2 := by
  rw [TowerInjectivity.hgt1_eq _ (fun e' => IETDatum₂.last_ne_last_not P hP hn e')]
  split <;> omega

/-- The one-step height of a letter other than the secondary name is one. -/
private theorem hgt1_eq_one_of_ne (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (e : Bool) {c : α} (hc : c ≠ P.last (!e)) : TowerInjectivity.hgt1 P e c = 1 := by
  rw [TowerInjectivity.hgt1_eq _ (fun e' => IETDatum₂.last_ne_last_not P hP hn e')]
  simp only [if_neg hc, add_zero]

/-! ## 4. The nesting of the level-one cells, in the notation of the node -/

/-- False step: every level-one cell sits in the cell of the same name. -/
private theorem cc_sub_false (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) (b : α) :
    Tower.cellAt P (γ ++ [false]) lam b ⊆ Tower.cellAt P γ lam b := by
  have h := TowerInjectivity.names_false_sub (IETDatum₂.vertex P γ) (Tower.lamAfter P γ lam) b
  have h2 := cellAt_node P γ lam b
  rw [TowerInjectivity.cellAt_succ]
  rw [← h2]
  exact h

/-- True step: every level-one cell but the secondary one sits in the cell of the same name. -/
private theorem cc_sub_true {P : IETDatum₂ α n} {γ : List Bool} {lam : α → ℝ≥0}
    (hS : TowerTrue.StepOK (IETDatum₂.vertex P γ) (Tower.lamAfter P γ lam) true) (b : α)
    (hb : b ≠ (IETDatum₂.vertex P γ).last false) :
    Tower.cellAt P (γ ++ [true]) lam b ⊆ Tower.cellAt P γ lam b := by
  have h := TowerInjectivity.names_true_sub (IETDatum₂.vertex P γ) (Tower.lamAfter P γ lam) hS b hb
  have h2 := cellAt_node P γ lam b
  rw [TowerInjectivity.cellAt_succ]
  rw [← h2]
  exact h

/-- True step: the secondary cell sits in the cell of the main name. -/
private theorem cc_sub_true_scd {P : IETDatum₂ α n} {γ : List Bool} {lam : α → ℝ≥0}
    (hS : TowerTrue.StepOK (IETDatum₂.vertex P γ) (Tower.lamAfter P γ lam) true) :
    Tower.cellAt P (γ ++ [true]) lam ((IETDatum₂.vertex P γ).last false)
      ⊆ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last true) := by
  have h := TowerInjectivity.names_true_sub_scd (IETDatum₂.vertex P γ) (Tower.lamAfter P γ lam) hS
  have h2 := cellAt_node P γ lam ((IETDatum₂.vertex P γ).last true)
  rw [TowerInjectivity.cellAt_succ]
  rw [← h2]
  exact h

/-- False step: the image of the secondary cell under the node exchange is the main cell. -/
private theorem kk_image_false_scd {P : IETDatum₂ α n} {γ : List Bool} {lam : α → ℝ≥0}
    (hS : TowerTrue.StepOK (IETDatum₂.vertex P γ) (Tower.lamAfter P γ lam) false) :
    nodeExch P γ lam '' Tower.cellAt P (γ ++ [false]) lam ((IETDatum₂.vertex P γ).last true)
      ⊆ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last false) := by
  have h := TowerInjectivity.names_false_image (IETDatum₂.vertex P γ) (Tower.lamAfter P γ lam) hS
  have h2 := cellAt_node P γ lam ((IETDatum₂.vertex P γ).last false)
  have h3 : nodeExch P γ lam
      = Tower.exch (IETDatum₂.vertex P γ).perm
          ((IETDatum₂.vertex P γ).lengthsInBottom (Tower.lamAfter P γ lam)) := nodeExch_eq P γ lam
  rw [h3, TowerInjectivity.cellAt_succ, ← h2]
  exact h

/-- True step: the image of the secondary cell under the node exchange is the same cell. -/
private theorem kk_image_true_scd {P : IETDatum₂ α n} {γ : List Bool} {lam : α → ℝ≥0}
    (hS : TowerTrue.StepOK (IETDatum₂.vertex P γ) (Tower.lamAfter P γ lam) true) :
    nodeExch P γ lam '' Tower.cellAt P (γ ++ [true]) lam ((IETDatum₂.vertex P γ).last false)
      ⊆ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last false) := by
  have h := TowerInjectivity.names_true_image (IETDatum₂.vertex P γ) (Tower.lamAfter P γ lam) hS
  have h2 := cellAt_node P γ lam ((IETDatum₂.vertex P γ).last false)
  have h3 : nodeExch P γ lam
      = Tower.exch (IETDatum₂.vertex P γ).perm
          ((IETDatum₂.vertex P γ).lengthsInBottom (Tower.lamAfter P γ lam)) := nodeExch_eq P γ lam
  rw [h3, TowerInjectivity.cellAt_succ, ← h2]
  exact h

/-! ## 5. The first-return identity at a node -/

/-- **The first-return identity at a node.**  For a point of the level-`γ` cell of `b`, the
`height P γ b`-th iterate of `T` is the exchange of the node `γ`: this is Veech's (3.3) at the node,
with the node exchange as first return. -/
private theorem FR_list {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible) (hn : 2 ≤ n)
    (hlam : lam ∈ simplexOn α) {γ : List Bool} (hOK : TowerTrue.IterOK P lam γ) :
    ∀ (b : α) (y : ℝ), y ∈ Tower.cellAt P γ lam b →
      (⇑(P.toIET lam))^[height P γ b] y = nodeExch P γ lam y := by
  classical
  induction γ using List.reverseRecOn with
  | nil =>
    intro b y _
    rw [height_nil, Function.iterate_one, nodeExch_nil hlam]
  | append_singleton γ e ih =>
    intro b y hy
    obtain ⟨hOK', hS⟩ := (IterGlue2.iterOK_append_singleton P lam γ e).mp hOK
    have hne : ∀ e' : Bool,
        (IETDatum₂.vertex P γ).last e' ≠ (IETDatum₂.vertex P γ).last (!e') :=
      fun e' => IETDatum₂.vertex_last_ne_not P hP hn γ e'
    have hy' : y ∈ Tower.cellAt (IETDatum₂.vertex P γ) [e] (Tower.lamAfter P γ lam) b := by
      rw [← TowerInjectivity.cellAt_succ]
      exact hy
    have hfr : (Tower.exch (IETDatum₂.vertex P γ).perm
        ((IETDatum₂.vertex P γ).lengthsInBottom (Tower.lamAfter P γ lam)))^[
          TowerInjectivity.hgt1 (IETDatum₂.vertex P γ) e b] y
        = Tower.exch ((IETDatum₂.vertex P γ).rvStep e).perm
            (((IETDatum₂.vertex P γ).rvStep e).lengthsInBottom
              (Tower.hatLam (IETDatum₂.vertex P γ) e (Tower.lamAfter P γ lam))) y := by
      cases e with
      | false => exact TowerInjectivity.firstReturn_false _ hne _ hS b hy'
      | true => exact TowerInjectivity.firstReturn_true _ hne _ hS b hy'
    have hHs := height_succ hP hn γ e b
    by_cases hb : b = (IETDatum₂.vertex P γ).last (!e)
    · have hheight : height P (γ ++ [e]) b
          = height P γ b + height P γ ((IETDatum₂.vertex P γ).last e) := by
        rw [hHs, if_pos hb]
      have hnode : nodeExch P (γ ++ [e]) lam y
          = nodeExch P γ lam (nodeExch P γ lam y) := by
        have hg2 : TowerInjectivity.hgt1 (IETDatum₂.vertex P γ) e b = 2 := by
          rw [TowerInjectivity.hgt1_eq _ hne, if_pos hb]
        rw [nodeExch_append, ← hfr, hg2, nodeExch_eq P γ lam,
          show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one]
      cases e with
      | false =>
        have hb' : b = (IETDatum₂.vertex P γ).last true := by simpa using hb
        rw [hb'] at hy hheight ⊢
        have hy1 : y ∈ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last true) :=
          cc_sub_false P γ lam _ hy
        have hmem : nodeExch P γ lam y
            ∈ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last false) :=
          kk_image_false_scd (P := P) (γ := γ) (lam := lam) hS ⟨y, hy, rfl⟩
        have i1 := ih hOK' ((IETDatum₂.vertex P γ).last true) y hy1
        have i2 := ih hOK' ((IETDatum₂.vertex P γ).last false) (nodeExch P γ lam y) hmem
        rw [hnode]
        calc (⇑(P.toIET lam))^[height P (γ ++ [false]) ((IETDatum₂.vertex P γ).last true)] y
            = (⇑(P.toIET lam))^[height P γ ((IETDatum₂.vertex P γ).last false)
                + height P γ ((IETDatum₂.vertex P γ).last true)] y := by
              rw [hheight, Nat.add_comm]
          _ = (⇑(P.toIET lam))^[height P γ ((IETDatum₂.vertex P γ).last false)]
                ((⇑(P.toIET lam))^[height P γ ((IETDatum₂.vertex P γ).last true)] y) := by
              rw [Function.iterate_add_apply]
          _ = (⇑(P.toIET lam))^[height P γ ((IETDatum₂.vertex P γ).last false)]
                (nodeExch P γ lam y) := by rw [i1]
          _ = nodeExch P γ lam (nodeExch P γ lam y) := i2
      | true =>
        have hb' : b = (IETDatum₂.vertex P γ).last false := by simpa using hb
        rw [hb'] at hy hheight ⊢
        have hy1 : y ∈ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last true) :=
          cc_sub_true_scd (P := P) (γ := γ) (lam := lam) hS hy
        have hmem : nodeExch P γ lam y
            ∈ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last false) :=
          kk_image_true_scd (P := P) (γ := γ) (lam := lam) hS ⟨y, hy, rfl⟩
        have i1 := ih hOK' ((IETDatum₂.vertex P γ).last true) y hy1
        have i2 := ih hOK' ((IETDatum₂.vertex P γ).last false) (nodeExch P γ lam y) hmem
        rw [hnode]
        calc (⇑(P.toIET lam))^[height P (γ ++ [true]) ((IETDatum₂.vertex P γ).last false)] y
            = (⇑(P.toIET lam))^[height P γ ((IETDatum₂.vertex P γ).last false)
                + height P γ ((IETDatum₂.vertex P γ).last true)] y := by rw [hheight]
          _ = (⇑(P.toIET lam))^[height P γ ((IETDatum₂.vertex P γ).last false)]
                ((⇑(P.toIET lam))^[height P γ ((IETDatum₂.vertex P γ).last true)] y) := by
              rw [Function.iterate_add_apply]
          _ = (⇑(P.toIET lam))^[height P γ ((IETDatum₂.vertex P γ).last false)]
                (nodeExch P γ lam y) := by rw [i1]
          _ = nodeExch P γ lam (nodeExch P γ lam y) := i2
    · have hheight : height P (γ ++ [e]) b = height P γ b := by
        rw [hHs, if_neg hb, add_zero]
      have hnode : nodeExch P (γ ++ [e]) lam y = nodeExch P γ lam y := by
        have hg1 : TowerInjectivity.hgt1 (IETDatum₂.vertex P γ) e b = 1 := by
          rw [TowerInjectivity.hgt1_eq _ hne, if_neg hb, add_zero]
        rw [nodeExch_append, nodeExch_eq P γ lam, ← hfr, hg1, Function.iterate_one]
      have hy1 : y ∈ Tower.cellAt P γ lam b := by
        cases e with
        | false => exact cc_sub_false P γ lam b hy
        | true => exact cc_sub_true (P := P) (γ := γ) (lam := lam) hS b (by simpa using hb) hy
      rw [hheight, hnode]
      exact ih hOK' b y hy1

/-- The level-empty cell, unfolded. -/
private theorem cellAt_nil_Ico (P : IETDatum₂ α n) (lam : α → ℝ≥0) (b : α) :
    Tower.cellAt P [] lam b
      = Set.Ico (leftEnd (P.lengthsInBottom lam) (P.piBottom b))
          (upperEnd (P.lengthsInBottom lam) (P.piBottom b)) := rfl

/-- **`T` is a translation on a level cell, up to its height.**  For every `j ≤ height P γ b` the
`j`-th iterate of `T` is a single translation on the whole level-`γ` cell of `b`. -/
private theorem SH_list {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible) (hn : 2 ≤ n)
    (hlam : lam ∈ simplexOn α) {γ : List Bool} (hOK : TowerTrue.IterOK P lam γ) :
    ∀ (b : α) (j : ℕ), j ≤ height P γ b → ∃ τ : ℝ,
      ∀ y ∈ Tower.cellAt P γ lam b, (⇑(P.toIET lam))^[j] y = y + τ := by
  classical
  induction γ using List.reverseRecOn with
  | nil =>
    intro b j hj
    rw [height_nil] at hj
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with h0 | h1
    · exact ⟨0, fun y _ => by rw [h0, Function.iterate_zero_apply, add_zero]⟩
    · refine ⟨translationVector P.perm (P.lengthsInBottom lam) (P.piBottom b), fun y hy => ?_⟩
      rw [cellAt_nil_Ico] at hy
      rw [h1, Function.iterate_one, TowerInjectivity.coe_toIET hlam]
      exact exch_eq_add_of_mem hy
  | append_singleton γ e ih =>
    intro b j hj
    obtain ⟨hOK', hS⟩ := (IterGlue2.iterOK_append_singleton P lam γ e).mp hOK
    have hHs := height_succ hP hn γ e b
    by_cases hb : b = (IETDatum₂.vertex P γ).last (!e)
    · have hheight : height P (γ ++ [e]) b
          = height P γ b + height P γ ((IETDatum₂.vertex P γ).last e) := by
        rw [hHs, if_pos hb]
      cases e with
      | false =>
        have hb' : b = (IETDatum₂.vertex P γ).last true := by simpa using hb
        rw [hb'] at hj hheight ⊢
        have hsub : Tower.cellAt P (γ ++ [false]) lam ((IETDatum₂.vertex P γ).last true)
            ⊆ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last true) :=
          cc_sub_false P γ lam _
        have himg : nodeExch P γ lam ''
            Tower.cellAt P (γ ++ [false]) lam ((IETDatum₂.vertex P γ).last true)
            ⊆ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last false) :=
          kk_image_false_scd (P := P) (γ := γ) (lam := lam) hS
        by_cases hj1 : j ≤ height P γ ((IETDatum₂.vertex P γ).last true)
        · obtain ⟨τ, hτ⟩ := ih hOK' _ j hj1
          exact ⟨τ, fun y hy => hτ y (hsub hy)⟩
        · push Not at hj1
          have hjp : j - height P γ ((IETDatum₂.vertex P γ).last true)
              ≤ height P γ ((IETDatum₂.vertex P γ).last false) := by
            rw [hheight] at hj
            omega
          obtain ⟨τ1, hτ1⟩ := ih hOK' ((IETDatum₂.vertex P γ).last true)
            (height P γ ((IETDatum₂.vertex P γ).last true)) le_rfl
          obtain ⟨τ2, hτ2⟩ := ih hOK' ((IETDatum₂.vertex P γ).last false)
            (j - height P γ ((IETDatum₂.vertex P γ).last true)) hjp
          refine ⟨τ1 + τ2, fun y hy => ?_⟩
          have hmem1 : y ∈ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last true) := hsub hy
          have hmem2 : nodeExch P γ lam y
              ∈ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last false) := himg ⟨y, hy, rfl⟩
          have hfr := FR_list hP hn hlam hOK' _ y hmem1
          have e1 : j = (j - height P γ ((IETDatum₂.vertex P γ).last true))
              + height P γ ((IETDatum₂.vertex P γ).last true) := by omega
          rw [e1, Function.iterate_add_apply, hfr, hτ2 _ hmem2, ← hfr, hτ1 y hmem1]
          ring
      | true =>
        have hb' : b = (IETDatum₂.vertex P γ).last false := by simpa using hb
        rw [hb'] at hj hheight ⊢
        have hsub : Tower.cellAt P (γ ++ [true]) lam ((IETDatum₂.vertex P γ).last false)
            ⊆ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last true) :=
          cc_sub_true_scd (P := P) (γ := γ) (lam := lam) hS
        have himg : nodeExch P γ lam ''
            Tower.cellAt P (γ ++ [true]) lam ((IETDatum₂.vertex P γ).last false)
            ⊆ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last false) :=
          kk_image_true_scd (P := P) (γ := γ) (lam := lam) hS
        by_cases hj1 : j ≤ height P γ ((IETDatum₂.vertex P γ).last true)
        · obtain ⟨τ, hτ⟩ := ih hOK' _ j hj1
          exact ⟨τ, fun y hy => hτ y (hsub hy)⟩
        · push Not at hj1
          have hjp : j - height P γ ((IETDatum₂.vertex P γ).last true)
              ≤ height P γ ((IETDatum₂.vertex P γ).last false) := by
            rw [hheight] at hj
            omega
          obtain ⟨τ1, hτ1⟩ := ih hOK' ((IETDatum₂.vertex P γ).last true)
            (height P γ ((IETDatum₂.vertex P γ).last true)) le_rfl
          obtain ⟨τ2, hτ2⟩ := ih hOK' ((IETDatum₂.vertex P γ).last false)
            (j - height P γ ((IETDatum₂.vertex P γ).last true)) hjp
          refine ⟨τ1 + τ2, fun y hy => ?_⟩
          have hmem1 : y ∈ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last true) := hsub hy
          have hmem2 : nodeExch P γ lam y
              ∈ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last false) := himg ⟨y, hy, rfl⟩
          have hfr := FR_list hP hn hlam hOK' _ y hmem1
          have e1 : j = (j - height P γ ((IETDatum₂.vertex P γ).last true))
              + height P γ ((IETDatum₂.vertex P γ).last true) := by omega
          rw [e1, Function.iterate_add_apply, hfr, hτ2 _ hmem2, ← hfr, hτ1 y hmem1]
          ring
    · have hheight : height P (γ ++ [e]) b = height P γ b := by
        rw [hHs, if_neg hb, add_zero]
      rw [hheight] at hj
      obtain ⟨τ, hτ⟩ := ih hOK' b j hj
      refine ⟨τ, fun y hy => hτ y ?_⟩
      cases e with
      | false => exact cc_sub_false P γ lam b hy
      | true => exact cc_sub_true (P := P) (γ := γ) (lam := lam) hS b (by simpa using hb) hy

/-- The level-`γ` cell, unfolded to its interval endpoints. -/
private theorem cellAt_Ico (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) (b : α) :
    Tower.cellAt P γ lam b
      = Set.Ico (leftEnd ((IETDatum₂.vertex P γ).lengthsInBottom (Tower.lamAfter P γ lam))
            ((IETDatum₂.vertex P γ).piBottom b))
          (upperEnd ((IETDatum₂.vertex P γ).lengthsInBottom (Tower.lamAfter P γ lam))
            ((IETDatum₂.vertex P γ).piBottom b)) := rfl

/-- **`T` is a translation on a level cell, up to its height.**  Veech's (3.3)–(3.4) at the node:
the `height P γ b`-th iterate of `T` is a single translation on the whole cell of `b`, with a
translation vector bounded by the base length minus the length of that cell. -/
theorem exists_translation_eq_on_cellAt {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {lam : α → ℝ≥0}
    (hlam : lam ∈ simplexOn α)
    {γ : List Bool} {b : α} (hOK : TowerTrue.IterOK P lam γ) :
    ∃ τ : ℝ, (∀ y ∈ Tower.cellAt P γ lam b, (⇑(P.toIET lam))^[height P γ b] y = y + τ) ∧
      |τ| ≤ baseLen P γ lam - (Tower.lamAfter P γ lam b : ℝ) := by
  classical
  refine ⟨translationVector (IETDatum₂.vertex P γ).perm
      ((IETDatum₂.vertex P γ).lengthsInBottom (Tower.lamAfter P γ lam))
      ((IETDatum₂.vertex P γ).piBottom b), ?_, ?_⟩
  · intro y hy
    rw [FR_list hP hn hlam hOK b y hy, nodeExch_eq]
    rw [cellAt_Ico] at hy
    exact exch_eq_add_of_mem hy
  · have hsum : (∑ k, (((IETDatum₂.vertex P γ).lengthsInBottom
        (Tower.lamAfter P γ lam)) k : ℝ))
        = ∑ a, (Tower.lamAfter P γ lam a : ℝ) :=
      TowerInjectivity.tot_lengthsInBottom _ _
    have hval : (((IETDatum₂.vertex P γ).lengthsInBottom (Tower.lamAfter P γ lam))
        ((IETDatum₂.vertex P γ).piBottom b) : ℝ) = (Tower.lamAfter P γ lam b : ℝ) := by
      simp only [IETDatum₂.lengthsInBottom, Equiv.symm_apply_apply]
    have h := abs_translationVector_le (IETDatum₂.vertex P γ).perm
      ((IETDatum₂.vertex P γ).lengthsInBottom (Tower.lamAfter P γ lam))
      ((IETDatum₂.vertex P γ).piBottom b)
    rw [hsum, hval] at h
    exact h

/-! ## 6. The mass of the base, the floors, and the total-mass identity -/

/-- The total mass of the simplex vector. -/
private theorem sumA_eq_one {α : Type*} [Fintype α] {lam : α → ℝ≥0} (hlam : lam ∈ simplexOn α) :
    TowerTrue.sumA lam = 1 := by
  rw [TowerTrue.sumA]
  have h := congrArg (fun t : ℝ≥0 => (t : ℝ)) hlam
  push_cast at h
  exact h

/-- The base length at a node is at most one. -/
private theorem baseLen_le_one {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hlam : lam ∈ simplexOn α)
    (γ : List Bool) : baseLen P γ lam ≤ 1 :=
  le_trans (TowerTrue.sumA_lamAfter_le P lam γ) (le_of_eq (sumA_eq_one hlam))

/-- A level cell sits in the unit interval. -/
private theorem cellAt_sub_one {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hlam : lam ∈ simplexOn α)
    (γ : List Bool) (b : α) : Tower.cellAt P γ lam b ⊆ Set.Ico (0:ℝ) 1 :=
  TowerTrue.cellAt_subset_sumA_le P γ lam b (baseLen_le_one hlam γ)

/-- Every floor of a level cell sits in the unit interval. -/
private theorem floor_subset_unit {P : IETDatum₂ α n} {lam : α → ℝ≥0}
    (hlam : lam ∈ simplexOn α) (γ : List Bool) (b : α) (j : ℕ) :
    (⇑(P.toIET lam))^[j] '' Tower.cellAt P γ lam b ⊆ Set.Ico (0:ℝ) 1 := by
  rw [TowerInjectivity.coe_toIET hlam]
  rintro x ⟨y, hy, rfl⟩
  exact TowerInjectivity.exch_iterate_mapsTo_one hlam j (cellAt_sub_one hlam γ b hy)

/-- Every floor of a level cell is measurable. -/
private theorem measurableSet_floor_node {P : IETDatum₂ α n} {lam : α → ℝ≥0}
    (hlam : lam ∈ simplexOn α) (γ : List Bool) (b : α) (j : ℕ) :
    MeasurableSet ((⇑(P.toIET lam))^[j] '' Tower.cellAt P γ lam b) := by
  rw [TowerInjectivity.coe_toIET hlam]
  exact TowerN.measurableSet_image_iterate P.perm (P.lengthsInBottom lam) measurableSet_Ico j

/-- Every floor of a level cell is an interval of the length of that cell. -/
private theorem floor_Ico_node {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible)
    (hn : 2 ≤ n) (hlam : lam ∈ simplexOn α) {γ : List Bool} (hOK : TowerTrue.IterOK P lam γ)
    (b : α) (j : ℕ) (hj : j ≤ height P γ b) :
    ∃ u v : ℝ, (⇑(P.toIET lam))^[j] '' Tower.cellAt P γ lam b = Set.Ico u v ∧
      v - u = (Tower.lamAfter P γ lam b : ℝ) := by
  obtain ⟨τ, hτ⟩ := SH_list hP hn hlam hOK b j hj
  refine ⟨leftEnd ((IETDatum₂.vertex P γ).lengthsInBottom (Tower.lamAfter P γ lam))
        ((IETDatum₂.vertex P γ).piBottom b) + τ,
      upperEnd ((IETDatum₂.vertex P γ).lengthsInBottom (Tower.lamAfter P γ lam))
        ((IETDatum₂.vertex P γ).piBottom b) + τ, ?_, ?_⟩
  · exact TowerInjectivity.image_Ico_of_translation (cellAt_Ico P γ lam b)
      (fun y hy => hτ y hy)
  · rw [upperEnd_eq, IETDatum₂.lengthsInBottom, Equiv.symm_apply_apply]
    ring

/-- The height, as a real sum. -/
private theorem height_coe (P : IETDatum₂ α n) (γ : List Bool) (b : α) :
    (height P γ b : ℝ) = ∑ a, ((IETDatum₂.Path.Q P γ a b).toNat : ℝ) := by
  simp only [height]
  push_cast
  rfl

/-- **The total-mass identity at a node**: `∑_b h_b · σ_b = 1`, Veech's (3.1) at the node. -/
private theorem TL_node {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible) (hn : 2 ≤ n)
    (hlam : lam ∈ simplexOn α) {γ : List Bool} (hOK : TowerTrue.IterOK P lam γ) :
    (∑ b, (height P γ b : ℝ) * (Tower.lamAfter P γ lam b : ℝ)) = 1 := by
  calc (∑ b, (height P γ b : ℝ) * (Tower.lamAfter P γ lam b : ℝ))
      = ∑ b, (∑ a, ((IETDatum₂.Path.Q P γ a b).toNat : ℝ))
          * (Tower.lamAfter P γ lam b : ℝ) :=
        Finset.sum_congr rfl (fun b _ => by rw [height_coe])
    _ = ∑ b, ∑ a, ((IETDatum₂.Path.Q P γ a b).toNat : ℝ)
          * (Tower.lamAfter P γ lam b : ℝ) :=
        Finset.sum_congr rfl (fun b _ => Finset.sum_mul _ _ _)
    _ = ∑ a, ∑ b, ((IETDatum₂.Path.Q P γ a b).toNat : ℝ)
          * (Tower.lamAfter P γ lam b : ℝ) := Finset.sum_comm
    _ = ∑ a, (lam a : ℝ) :=
        Finset.sum_congr rfl (fun a _ => TowerInjectivity.renorm_apply P hP hn hOK a)
    _ = 1 := sumA_eq_one hlam

/-! ## 7. The level-one decomposition, and the covering of the base -/

/-- The level-`γ` cell is the cell of the vertex `vertex P γ`. -/
private theorem cellOf_node (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) (b : α) :
    InvariantMeasure.cellOf (IETDatum₂.vertex P γ) (Tower.lamAfter P γ lam) b
      = Tower.cellAt P γ lam b := rfl

/-- The base length, as a sum. -/
private theorem baseLen_eq_sum (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) :
    baseLen P γ lam = ∑ b, (Tower.lamAfter P γ lam b : ℝ) := rfl

/-- A level cell sits in the level base interval. -/
private theorem cellAt_sub_base (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) (b : α) :
    Tower.cellAt P γ lam b ⊆ Set.Ico (0:ℝ) (baseLen P γ lam) := by
  have h := InvariantMeasure.cellOf_subset (IETDatum₂.vertex P γ) (Tower.lamAfter P γ lam) b
  rw [cellOf_node] at h
  rw [show (∑ i, ((IETDatum₂.vertex P γ).lengthsInBottom (Tower.lamAfter P γ lam) i : ℝ))
      = ∑ c, (Tower.lamAfter P γ lam c : ℝ) from
    TowerInjectivity.tot_lengthsInBottom _ _] at h
  rw [baseLen_eq_sum]
  exact h

/-- Two level cells with a common point have the same letter. -/
private theorem cellAt_eq_of_mem (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0)
    {b c : α} {y : ℝ} (h1 : y ∈ Tower.cellAt P γ lam b) (h2 : y ∈ Tower.cellAt P γ lam c) :
    b = c := by
  by_contra hne
  have h := InvariantMeasure.disjoint_cellOf (IETDatum₂.vertex P γ) (Tower.lamAfter P γ lam) hne
  rw [cellOf_node, cellOf_node] at h
  exact (Set.disjoint_left.mp h) h1 h2

/-- The height does not decrease in a false step. -/
private theorem height_le_succ_false {P : IETDatum₂ α n} (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) (b : α) : height P γ b ≤ height P (γ ++ [false]) b := by
  rw [height_succ hP hn γ false b]
  split <;> omega

/-- The height does not change in a true step, off the secondary letter. -/
private theorem height_succ_ne {P : IETDatum₂ α n} (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) (e : Bool) {c : α} (hc : c ≠ (IETDatum₂.vertex P γ).last (!e)) :
    height P (γ ++ [e]) c = height P γ c := by
  rw [height_succ hP hn γ e c, if_neg hc, add_zero]

/-- The height recursion at the secondary letter of a true step. -/
private theorem height_succ_true_scd {P : IETDatum₂ α n} (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) :
    height P (γ ++ [true]) ((IETDatum₂.vertex P γ).last false)
      = height P γ ((IETDatum₂.vertex P γ).last false)
        + height P γ ((IETDatum₂.vertex P γ).last true) := by
  rw [height_succ hP hn γ true, Bool.not_true, if_pos rfl]

/-- The height recursion at the secondary letter of a false step. -/
private theorem height_succ_false_scd {P : IETDatum₂ α n} (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) :
    height P (γ ++ [false]) ((IETDatum₂.vertex P γ).last true)
      = height P γ ((IETDatum₂.vertex P γ).last true)
        + height P γ ((IETDatum₂.vertex P γ).last false) := by
  rw [height_succ hP hn γ false, Bool.not_false, if_pos rfl]

/-- **The level-one decomposition of the level base.**  The base interval at the node `γ` is the
disjoint union of the first `hgt1` iterates of the level-`γ ++ [e]` cells. -/
private theorem LVL1_node {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) (e : Bool) (hOK : TowerTrue.IterOK P lam (γ ++ [e])) :
    Set.Ico 0 (baseLen P γ lam)
      = ⋃ b, ⋃ i : Fin (TowerInjectivity.hgt1 (IETDatum₂.vertex P γ) e b),
          (nodeExch P γ lam)^[(i : ℕ)] '' Tower.cellAt P (γ ++ [e]) lam b := by
  obtain ⟨-, hS⟩ := (IterGlue2.iterOK_append_singleton P lam γ e).mp hOK
  have hne : ∀ e' : Bool, (IETDatum₂.vertex P γ).last e' ≠ (IETDatum₂.vertex P γ).last (!e') :=
    fun e' => IETDatum₂.vertex_last_ne_not P hP hn γ e'
  have hcell : ∀ b : α, Tower.cellAt P (γ ++ [e]) lam b
      = Tower.cellAt (IETDatum₂.vertex P γ) [e] (Tower.lamAfter P γ lam) b :=
    fun b => TowerInjectivity.cellAt_succ P γ e lam b
  cases e with
  | false =>
    have h := TowerInjectivity.level_tower_false (IETDatum₂.vertex P γ) hne
      (Tower.lamAfter P γ lam) hS
    rw [baseLen_eq_sum, h]
    refine Set.iUnion_congr (fun b => Set.iUnion_congr (fun i => ?_))
    rw [nodeExch_eq, hcell b]
  | true =>
    have h := TowerInjectivity.level_tower_true (IETDatum₂.vertex P γ) hne
      (Tower.lamAfter P γ lam) hS
    rw [show baseLen P γ lam = ∑ b, (Tower.lamAfter P γ lam b : ℝ) from rfl, h]
    refine Set.iUnion_congr (fun b => Set.iUnion_congr (fun i => ?_))
    rw [nodeExch_eq, hcell b]

/-- A false step lifts a floor of the level-`γ` tower to a floor of the level-`γ ++ [false]` one. -/
private theorem cover_step_false {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible)
    (hn : 2 ≤ n) (hlam : lam ∈ simplexOn α) {γ : List Bool}
    (hOK : TowerTrue.IterOK P lam (γ ++ [false])) {x : ℝ}
    (hx : ∃ (b : α) (j : ℕ), j < height P γ b ∧
      x ∈ (⇑(P.toIET lam))^[j] '' Tower.cellAt P γ lam b) :
    ∃ (b : α) (j : ℕ), j < height P (γ ++ [false]) b ∧
      x ∈ (⇑(P.toIET lam))^[j] '' Tower.cellAt P (γ ++ [false]) lam b := by
  obtain ⟨hOK', hS⟩ := (IterGlue2.iterOK_append_singleton P lam γ false).mp hOK
  obtain ⟨b, j, hj, y, hy, rfl⟩ := hx
  have hy' : y ∈ Set.Ico 0 (baseLen P γ lam) := cellAt_sub_base P γ lam b hy
  rw [LVL1_node hP hn γ false hOK] at hy'
  obtain ⟨b', hb'⟩ := Set.mem_iUnion.mp hy'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hb'
  obtain ⟨z, hz1, hzy⟩ := hi
  have hilt : (i : ℕ) < TowerInjectivity.hgt1 (IETDatum₂.vertex P γ) false b' := i.isLt
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hipos
  · rw [hi0, Function.iterate_zero_apply] at hzy
    rw [← hzy] at hy
    have hsub : Tower.cellAt P (γ ++ [false]) lam b' ⊆ Tower.cellAt P γ lam b' :=
      cc_sub_false P γ lam b'
    have hbb : b = b' := cellAt_eq_of_mem P γ lam hy (hsub hz1)
    refine ⟨b', j, ?_, ?_⟩
    · rw [hbb] at hj
      exact lt_of_lt_of_le hj (height_le_succ_false hP hn γ b')
    · exact ⟨z, hz1, by rw [hzy]⟩
  · have hi1 : (i : ℕ) = 1 := by
      have h2 := hgt1_le_two (IETDatum₂.vertex P γ) (IETDatum₂.vertex_irreducible P γ hP) hn
        false b'
      omega
    rw [hi1, Function.iterate_one] at hzy
    rw [← hzy] at hy
    have hb't : b' = (IETDatum₂.vertex P γ).last true := by
      have hlt : b' = (IETDatum₂.vertex P γ).last (!false) := by
        by_contra hc
        have h1 := hgt1_eq_one_of_ne (IETDatum₂.vertex P γ)
          (IETDatum₂.vertex_irreducible P γ hP) hn false hc
        omega
      simpa using hlt
    subst b'
    have hsub : Tower.cellAt P (γ ++ [false]) lam ((IETDatum₂.vertex P γ).last true)
        ⊆ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last true) :=
      cc_sub_false P γ lam _
    have himg : nodeExch P γ lam ''
        Tower.cellAt P (γ ++ [false]) lam ((IETDatum₂.vertex P γ).last true)
        ⊆ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last false) :=
      kk_image_false_scd (P := P) (γ := γ) (lam := lam) hS
    have hKz : nodeExch P γ lam z
        ∈ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last false) := himg ⟨z, hz1, rfl⟩
    have hbb : b = (IETDatum₂.vertex P γ).last false := cellAt_eq_of_mem P γ lam hy hKz
    have hFRz := FR_list hP hn hlam hOK' ((IETDatum₂.vertex P γ).last true) z (hsub hz1)
    refine ⟨(IETDatum₂.vertex P γ).last true,
      j + height P γ ((IETDatum₂.vertex P γ).last true), ?_, ?_⟩
    · have hHs := height_succ_false_scd hP hn γ
      rw [hbb] at hj
      rw [hHs]
      omega
    · exact ⟨z, hz1, by rw [Function.iterate_add_apply, hFRz, hzy]⟩

/-- A true step lifts a floor of the level-`γ` tower to a floor of the level-`γ ++ [true]` one. -/
private theorem cover_step_true {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible)
    (hn : 2 ≤ n) (hlam : lam ∈ simplexOn α) {γ : List Bool}
    (hOK : TowerTrue.IterOK P lam (γ ++ [true])) {x : ℝ}
    (hx : ∃ (b : α) (j : ℕ), j < height P γ b ∧
      x ∈ (⇑(P.toIET lam))^[j] '' Tower.cellAt P γ lam b) :
    ∃ (b : α) (j : ℕ), j < height P (γ ++ [true]) b ∧
      x ∈ (⇑(P.toIET lam))^[j] '' Tower.cellAt P (γ ++ [true]) lam b := by
  obtain ⟨hOK', hS⟩ := (IterGlue2.iterOK_append_singleton P lam γ true).mp hOK
  obtain ⟨b, j, hj, y, hy, rfl⟩ := hx
  have hy' : y ∈ Set.Ico 0 (baseLen P γ lam) := cellAt_sub_base P γ lam b hy
  rw [LVL1_node hP hn γ true hOK] at hy'
  obtain ⟨b', hb'⟩ := Set.mem_iUnion.mp hy'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hb'
  obtain ⟨z, hz1, hzy⟩ := hi
  have hilt : (i : ℕ) < TowerInjectivity.hgt1 (IETDatum₂.vertex P γ) true b' := i.isLt
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hipos
  · rw [hi0, Function.iterate_zero_apply] at hzy
    rw [← hzy] at hy
    by_cases hbs : b' = (IETDatum₂.vertex P γ).last false
    · subst b'
      have hsub : Tower.cellAt P (γ ++ [true]) lam ((IETDatum₂.vertex P γ).last false)
          ⊆ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last true) :=
        cc_sub_true_scd (P := P) (γ := γ) (lam := lam) hS
      have hbb : b = (IETDatum₂.vertex P γ).last true := cellAt_eq_of_mem P γ lam hy (hsub hz1)
      refine ⟨(IETDatum₂.vertex P γ).last false, j, ?_, ?_⟩
      · have hHs := height_succ_true_scd hP hn γ
        rw [hbb] at hj
        rw [hHs]
        omega
      · exact ⟨z, hz1, by rw [hzy]⟩
    · have hsub : Tower.cellAt P (γ ++ [true]) lam b' ⊆ Tower.cellAt P γ lam b' :=
        cc_sub_true (P := P) (γ := γ) (lam := lam) hS b' hbs
      have hbb : b = b' := cellAt_eq_of_mem P γ lam hy (hsub hz1)
      refine ⟨b', j, ?_, ?_⟩
      · have hHs := height_succ_ne hP hn γ true (c := b') (by simpa using hbs)
        rw [hbb] at hj
        rw [hHs]
        exact hj
      · exact ⟨z, hz1, by rw [hzy]⟩
  · have hi1 : (i : ℕ) = 1 := by
      have h2 := hgt1_le_two (IETDatum₂.vertex P γ) (IETDatum₂.vertex_irreducible P γ hP) hn
        true b'
      omega
    rw [hi1, Function.iterate_one] at hzy
    rw [← hzy] at hy
    have hb'f : b' = (IETDatum₂.vertex P γ).last false := by
      have hlt : b' = (IETDatum₂.vertex P γ).last (!true) := by
        by_contra hc
        have h1 := hgt1_eq_one_of_ne (IETDatum₂.vertex P γ)
          (IETDatum₂.vertex_irreducible P γ hP) hn true hc
        omega
      simpa using hlt
    subst b'
    have hsub : Tower.cellAt P (γ ++ [true]) lam ((IETDatum₂.vertex P γ).last false)
        ⊆ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last true) :=
      cc_sub_true_scd (P := P) (γ := γ) (lam := lam) hS
    have himg : nodeExch P γ lam ''
        Tower.cellAt P (γ ++ [true]) lam ((IETDatum₂.vertex P γ).last false)
        ⊆ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last false) :=
      kk_image_true_scd (P := P) (γ := γ) (lam := lam) hS
    have hKz : nodeExch P γ lam z
        ∈ Tower.cellAt P γ lam ((IETDatum₂.vertex P γ).last false) := himg ⟨z, hz1, rfl⟩
    have hbb : b = (IETDatum₂.vertex P γ).last false := cellAt_eq_of_mem P γ lam hy hKz
    have hFRz := FR_list hP hn hlam hOK' ((IETDatum₂.vertex P γ).last true) z (hsub hz1)
    refine ⟨(IETDatum₂.vertex P γ).last false,
      j + height P γ ((IETDatum₂.vertex P γ).last true), ?_, ?_⟩
    · have hHs := height_succ_true_scd hP hn γ
      rw [hbb] at hj
      rw [hHs]
      omega
    · exact ⟨z, hz1, by rw [Function.iterate_add_apply, hFRz, hzy]⟩

/-- The level-`γ` cell of the empty node is the cell of the initial partition. -/
private theorem cellAt_nil_cellOf (P : IETDatum₂ α n) (lam : α → ℝ≥0) (b : α) :
    Tower.cellAt P [] lam b = InvariantMeasure.cellOf P lam b := rfl

/-- **The floors of the level-`γ` tower cover the unit interval.** -/
private theorem CV_node {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible) (hn : 2 ≤ n)
    (hlam : lam ∈ simplexOn α) {γ : List Bool} (hOK : TowerTrue.IterOK P lam γ) :
    ∀ x ∈ Set.Ico (0:ℝ) 1, ∃ (b : α) (j : ℕ), j < height P γ b ∧
      x ∈ (⇑(P.toIET lam))^[j] '' Tower.cellAt P γ lam b := by
  classical
  induction γ using List.reverseRecOn with
  | nil =>
    intro x hx
    have hx' : x ∈ Set.Ico (0 : ℝ) (∑ i, (P.lengthsInBottom lam i : ℝ)) := by
      have h1 : (∑ i, (P.lengthsInBottom lam i : ℝ)) = ∑ a, (lam a : ℝ) :=
        TowerInjectivity.tot_lengthsInBottom P lam
      have h2 : (∑ a, (lam a : ℝ)) = 1 := sumA_eq_one hlam
      rw [h1, h2]
      exact hx
    refine ⟨P.piBottom.symm (idx (P.lengthsInBottom lam) x hx'.1), 0, ?_, ?_⟩
    · rw [height_nil]
      exact Nat.one_pos
    · refine ⟨x, ?_, by simp⟩
      rw [cellAt_nil_cellOf]
      exact InvariantMeasure.mem_cellOf_idx P lam hx'
  | append_singleton γ e ih =>
    intro x hx
    have hOK' : TowerTrue.IterOK P lam γ :=
      (IterGlue2.iterOK_append_singleton P lam γ e).mp hOK |>.1
    cases e with
    | false => exact cover_step_false hP hn hlam hOK (ih hOK' x hx)
    | true => exact cover_step_true hP hn hlam hOK (ih hOK' x hx)

/-- **The floors of one level are pairwise disjoint.**  Veech's (3.5) at the node: the floors
`T^j (cellAt P γ lam b)`, `j < height P γ b`, are pairwise disjoint.  They are intervals of total
length `1` inside `[0,1)` which cover `[0,1)`, so two of them cannot meet in an interval of positive
length. -/
private theorem sigma_disjoint_node {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hP : P.Irreducible)
    (hn : 2 ≤ n) (hlam : lam ∈ simplexOn α) {γ : List Bool} (hOK : TowerTrue.IterOK P lam γ) :
    ∀ p q : (Σ b : α, Fin (height P γ b)), p ≠ q →
      Disjoint ((⇑(P.toIET lam))^[(p.2 : ℕ)] '' Tower.cellAt P γ lam p.1)
        ((⇑(P.toIET lam))^[(q.2 : ℕ)] '' Tower.cellAt P γ lam q.1) := by
  classical
  set fr : (Σ b : α, Fin (height P γ b)) → Set ℝ :=
    fun r => (⇑(P.toIET lam))^[(r.2 : ℕ)] '' Tower.cellAt P γ lam r.1 with hfr
  have hIco (r : (Σ b : α, Fin (height P γ b))) :
    ∃ u v : ℝ, fr r = Set.Ico u v ∧ v - u = (Tower.lamAfter P γ lam r.1 : ℝ) := by
    exact floor_Ico_node hP hn hlam hOK r.1 (r.2 : ℕ) (le_of_lt r.2.isLt)
  have hvol : ∀ r, volume (fr r) = ENNReal.ofReal (Tower.lamAfter P γ lam r.1 : ℝ) := by
    intro r
    obtain ⟨u, v, h1, h2⟩ := hIco r
    rw [h1, Real.volume_Ico, h2]
  have hfin : ∀ r, volume (fr r) ≠ ⊤ := by
    intro r
    rw [hvol r]
    exact ENNReal.ofReal_ne_top
  have hbdd (S : Set ℝ) (hS : S ⊆ Set.Ico (0 : ℝ) 1) : volume S ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hS)
    rw [Real.volume_Ico, sub_zero, ENNReal.ofReal_one]
    exact ENNReal.one_ne_top
  have hmeas : ∀ r, MeasurableSet (fr r) := by
    intro r
    exact measurableSet_floor_node hlam γ r.1 (r.2 : ℕ)
  have hsub : ∀ r, fr r ⊆ Set.Ico (0 : ℝ) 1 := by
    intro r
    exact floor_subset_unit hlam γ r.1 (r.2 : ℕ)
  have hsumR : (∑ r : (Σ b : α, Fin (height P γ b)),
      (Tower.lamAfter P γ lam r.1 : ℝ)) = 1 := by
    have h2 (b : α) :
      (∑ _j : Fin (height P γ b),
        (Tower.lamAfter P γ lam b : ℝ)) = (height P γ b : ℝ)
          * (Tower.lamAfter P γ lam b : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.univ_sigma_univ,
      ← Finset.sum_sigma' (f := fun a (_ : Fin (height P γ a)) =>
        (Tower.lamAfter P γ lam a : ℝ))]
    rw [Finset.sum_congr rfl (fun a _ => h2 a)]
    exact TL_node hP hn hlam hOK
  have hsum : (∑ r : (Σ b : α, Fin (height P γ b)), (volume (fr r)).toReal) = 1 := by
    have h1 : ∀ r, (volume (fr r)).toReal = (Tower.lamAfter P γ lam r.1 : ℝ) := by
      intro r
      rw [hvol r, ENNReal.toReal_ofReal (Tower.lamAfter P γ lam r.1).coe_nonneg]
    simp only [h1]
    exact hsumR
  have hunion : (⋃ r : (Σ b : α, Fin (height P γ b)), fr r) = Set.Ico (0 : ℝ) 1 := by
    refine Set.Subset.antisymm (Set.iUnion_subset hsub) ?_
    intro x hx
    obtain ⟨b, j, hj, hmem⟩ := CV_node hP hn hlam hOK x hx
    exact Set.mem_iUnion.mpr ⟨⟨b, ⟨j, hj⟩⟩, hmem⟩
  have key (p : (Σ b : α, Fin (height P γ b))) :
    volume (fr p ∩ ⋃ r ∈ (Finset.univ :
        Finset (Σ b : α, Fin (height P γ b))).erase p, fr r) = 0 := by
    set G : Set ℝ := ⋃ r ∈ (Finset.univ : Finset
      (Σ b : α, Fin (height P γ b))).erase p, fr r with hG
    have hsplit : (⋃ r ∈ (Finset.univ : Finset (Σ b : α, Fin (height P γ b))), fr r)
        = fr p ∪ G := by
      rw [hG]
      conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ p), Finset.set_biUnion_insert]
    have hiunion : (⋃ r : (Σ b : α, Fin (height P γ b)), fr r)
        = ⋃ r ∈ (Finset.univ : Finset (Σ b : α, Fin (height P γ b))), fr r := by
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
    have hsumG : (∑ r ∈ (Finset.univ : Finset (Σ b : α, Fin (height P γ b))).erase p,
        (volume (fr r)).toReal) + (volume (fr p)).toReal = 1 := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ p)]
      exact hsum
    have hle : (volume G).toReal ≤ ∑ r ∈ (Finset.univ : Finset
        (Σ b : α, Fin (height P γ b))).erase p, (volume (fr r)).toReal := by
      have h := measure_biUnion_finset_le (μ := volume)
        ((Finset.univ : Finset (Σ b : α, Fin (height P γ b))).erase p) fr
      have hfs : (∑ r ∈ (Finset.univ : Finset (Σ b : α, Fin (height P γ b))).erase p,
          volume (fr r)) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun r _ => hfin r)
      refine le_trans (ENNReal.toReal_mono hfs h) (le_of_eq ?_)
      exact ENNReal.toReal_sum (fun r _ => hfin r)
    have hx0 : (0 : ℝ) ≤ (volume (fr p ∩ G)).toReal := ENNReal.toReal_nonneg
    have hzero : (volume (fr p ∩ G)).toReal = 0 := by linarith
    rcases (ENNReal.toReal_eq_zero_iff _).mp hzero with h | h
    · exact h
    · exact absurd h (ne_top_of_le_ne_top (hfin p) (measure_mono (Set.inter_subset_left)))
  intro p q hpq
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
  change Disjoint (fr p) (fr q)
  rw [Set.disjoint_iff_inter_eq_empty, hgoal, Set.Ico_eq_empty_of_le hle]

/-- **The rigid set of a good node.**  If the cell of the letter `b` occupies a proportion `≥ 1 - δ`
of the base at the node `γ` (`δ ≤ 1/4`), then there are a translation vector `t` with
`|t| ≤ δ · baseLen` and a set `B ⊆ [0,1)` of measure at least `(1 - 2δ) · baseLen · height` on which
the `height`-th iterate of `T = P.toIET lam` is exactly the translation `x ↦ x + t`. -/
theorem exists_rigid_set {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {lam : α → ℝ≥0}
    (hlam : lam ∈ simplexOn α)
    {γ : List Bool} {b : α} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (hOK : TowerTrue.IterOK P lam γ) (hbig : BigCell P γ lam δ b) :
    ∃ (t : ℝ) (B : Set ℝ),
      B ⊆ Set.Ico (0:ℝ) 1 ∧ MeasurableSet B ∧
      (1 - 2 * δ) * baseLen P γ lam * (height P γ b : ℝ) ≤ (volume B).toReal ∧
      |t| ≤ δ * baseLen P γ lam ∧
      ∀ x ∈ B, (⇑(P.toIET lam))^[height P γ b] x = x + t := by
  classical
  obtain ⟨τ, hτ, hτle⟩ := exists_translation_eq_on_cellAt P hP hn hlam hOK
  simp only [BigCell] at hbig
  set σ := Tower.lamAfter P γ lam with hσ
  set Le := baseLen P γ lam with hLe
  set hh := height P γ b with hhh
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
          exact Finset.sum_nonneg (fun a _ => (Tower.lamAfter P γ lam a).coe_nonneg))
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

end IETFree.Rigidity
