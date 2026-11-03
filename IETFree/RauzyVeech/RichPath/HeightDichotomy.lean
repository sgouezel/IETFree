/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.RauzyVeech.RichPath.LargeLetter
import IETFree.RauzyVeech.RichPath.LevelMass
import IETFree.RauzyVeech.RichPath.BadFirstStop

/-!
# The mass form of the `Γ₃` step, and the `k → k+1` dichotomy

The proof of the source's distortion theorem has three steps at level `k`: `Γ₂` (extend each minimal
path to a vertex where a row end is outside `A'`), `Γ₃` (Kerckhoff bounds the `A'`-coordinates) and
`Γ₄` (a new large letter appears).  This library has `Γ₄` (`LargeLetter.newLetter_words`) and the
assembly of the balance step from `Γ₃` (`IETFree/RauzyVeech/RichPath/InductionAssembly.lean`);
this file supplies the *mass* content of `Γ₃`.  Kerckhoff's estimate is stated for a family all of
whose arrows avoid **one** letter `b`; summing it over the finitely many letters of a set `S` costs
nothing beyond subadditivity (`kerckhoff_letter`), which is the form `Γ₃` consumes.  The file also
proves the source's `k → k+1` dichotomy in its `γ_s`-relative form with the constant `4·d·C₀·C₂`
(`dichotomy`).

* §1 **`kerckhoff_letter`**: a prefix-free family `F` of continuations of `w`, each avoiding a
  letter `b ∈ S` and with its `b`-height above `r b`, has `∑_{δ∈F} cond P w δ < ∑_{b∈S} cs P w b / r
  b` — Kerckhoff summed over `S`, by the fibre decomposition of `F` along the avoided letter.
* §3 **`dichotomy`**: from a path `γ = γ_s γ_e` carrying the `Γ₃` bounds relative to `γ_s`, produce
  `γ_s ≤ γ₁ ≤ γ_s γ_e` and a letter `θ ∉ A'` with
  `Mk 1 (st P (w++γ₁)) ≤ 4·d·C₀·C₂ · min {mmin (A' ∪ {θ}) (st P (w++γ₁)), Mk 1 (st P w)}` —
  the source's display, with `A'₁ = insert θ A'` the `(k+1)`-subset.
* §4 the single-letter case `A' = {b}`, for every `d`: an arrow is an exit arrow exactly when `b`
  wins (`exitArrow_singleton_iff`), so a bad word avoids `b` up to its first stop
  (`exists_noWin_crossing_singleton`), and §1 bounds the mass of the level-`N` bad words
  (`sum_cond_kerckhoff_singleton`, `sum_bad_singleton_le`), in the packaged forms
  `singleton_mass` and `card_one_mass`. Axiom-clean.
-/


open Finset NodeHeight
open scoped BigOperators

namespace HeightDichotomy

open IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Kerckhoff summed over a finite set of letters -/

variable [Nonempty α]

omit [Nonempty α] in
/-- **Kerckhoff for one letter**, with the threshold written as a height `r` instead of a factor
`T`: if every member of a prefix-free family avoids `b` and has its `b`-height above `r`, the mass
is `< cs P w b / r`.  (`CylinderMass.kerckhoff` with `T = r / cs P w b`.) -/
theorem kerckhoff_letter (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (b : α) {r : ℝ} (hr : 0 < r)
    (F : Finset (List Bool)) (hF : NodeHeight.PrefixFree F)
    (h : ∀ δ ∈ F, CylinderMass.NoWin P w b δ ∧ r < ColShrink.cs P (w ++ δ) b) :
    ∑ δ ∈ F, CylinderMass.cond P w δ < ColShrink.cs P w b / r := by
  have hcs : ColShrink.cs P w b ≠ 0 := ColShrink.cs_ne_zero P w b
  have hT : 0 < r / ColShrink.cs P w b := div_pos hr (ColShrink.cs_pos P w b)
  have hker := CylinderMass.kerckhoff P hP hn w b hT F hF (fun δ hδ => (h δ hδ).1)
    (fun δ hδ => by
      have h2 := (h δ hδ).2
      have h3 : (r / ColShrink.cs P w b) * ColShrink.cs P w b = r := div_mul_cancel₀ _ hcs
      rw [h3]
      exact h2)
  refine lt_of_lt_of_eq hker ?_
  rw [one_div_div]

end HeightDichotomy

/-! ## 3. The dichotomy of the source, `γ_s`-relative and with `4·d·C₀·C₂` -/

namespace HeightDichotomy

open IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- **`Γ₄` in the source's `γ_s`-relative form.**  Let `γ = γ_s (ν ++ [e])` be a continuation of `w`
lying in `Γ₃`: along `γ_e = ν ++ [e]` no `A'`-height exceeds `2·d·M(q_{w γ_s})`, and the last arrow
of `γ_e` either is an exit arrow (`A' → α ∖ A'`) or the maximum has already crossed the threshold.
Assume moreover that `A'` is `C₀`-balanced at `w γ_s` (`m_{A'}(q) ≥ M(q)/C₀`) and that `M(q_{w γ_s})
≤ C₂·M(q_w)` — the source's `Γ₂` maximum-growth bound, which the node-relative
`LargeLetter.newLetter_words` folds away by working at `w γ_s` directly.  Then there are `γ₁` with
`γ_s ≤ γ₁ ≤ γ_s γ_e` and a letter `θ ∉ A'` with  `Mk 1 (st P (w++γ₁)) ≤ 4·d·C₀·C₂ · min {mmin (A' ∪
{θ}) (st P (w++γ₁)), Mk 1 (st P w)}`,  which is the source's conclusion with `A'₁ = insert θ A'` the
`(k+1)`-subset. -/
theorem dichotomy (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w γs ν : List Bool) (e : Bool) (A' : Finset α) {C0 C2 : ℝ}
    (hA'ne : A'.Nonempty) (hC0 : 1 ≤ C0) (hC2 : 1 ≤ C2)
    (hbal : ∀ b ∈ A',
      (1 / C0) * NodeHeight.Mk 1 (NodeHeight.st P (w ++ γs)) ≤ NodeHeight.st P (w ++ γs) b)
    (hAN : ∀ i, i ≤ (ν ++ [e]).length → ∀ b ∈ A',
      NodeHeight.st P ((w ++ γs) ++ (ν ++ [e]).take i) b ≤
        2 * (Fintype.card α : ℝ) * NodeHeight.Mk 1 (NodeHeight.st P (w ++ γs)))
    (hlast : (P.vertex ((w ++ γs) ++ ν)).last e ∈ A' ∧
        (P.vertex ((w ++ γs) ++ ν)).last (!e) ∉ A'
      ∨ 2 * (Fintype.card α : ℝ) * NodeHeight.Mk 1 (NodeHeight.st P (w ++ γs)) <
          NodeHeight.Mk 1 (NodeHeight.st P ((w ++ γs) ++ (ν ++ [e]))))
    (hC2bd : NodeHeight.Mk 1 (NodeHeight.st P (w ++ γs))
      ≤ C2 * NodeHeight.Mk 1 (NodeHeight.st P w)) :
    ∃ γ₁ : List Bool, γs <+: γ₁ ∧ γ₁ <+: γs ++ (ν ++ [e]) ∧ ∃ θ : α, θ ∉ A' ∧
      NodeHeight.Mk 1 (NodeHeight.st P (w ++ γ₁)) ≤
        4 * (Fintype.card α : ℝ) * C0 * C2 *
          min (NodeHeight.mmin (insert θ A') (NodeHeight.st P (w ++ γ₁)))
            (NodeHeight.Mk 1 (NodeHeight.st P w)) := by
  obtain ⟨i, hi, θ, hθ, hbound⟩ :=
    LargeLetter.newLetter_words P hP hn (w ++ γs) ν e A' hA'ne hC0 hbal hAN hlast
  have hw : (w ++ γs) ++ (ν ++ [e]).take i = w ++ (γs ++ (ν ++ [e]).take i) :=
    List.append_assoc w γs _
  rw [hw] at hbound
  refine ⟨γs ++ (ν ++ [e]).take i, List.prefix_append γs _,
    NodeHeight.append_prefix_append γs (List.take_prefix i (ν ++ [e])), θ, hθ, ?_⟩
  -- the `C₂` bookkeeping: `C₂ ≥ 1` and `M(q_{w γ_s}) ≤ C₂·M(q_w)`
  have hxpos : 0 < NodeHeight.mmin (insert θ A')
      (NodeHeight.st P (w ++ (γs ++ (ν ++ [e]).take i))) :=
    NodeHeight.mmin_pos ⟨θ, Finset.mem_insert_self θ A'⟩ fun b => NodeHeight.st_pos P _ b
  have h4 : (0 : ℝ) ≤ 4 * (Fintype.card α : ℝ) * C0 := by
    have h1 : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by
      have := NodeHeight.card_pos P
      exact_mod_cast this
    have h2 : (0 : ℝ) < C0 := by linarith
    positivity
  have hstep : min (NodeHeight.mmin (insert θ A')
        (NodeHeight.st P (w ++ (γs ++ (ν ++ [e]).take i))))
      (NodeHeight.Mk 1 (NodeHeight.st P (w ++ γs))) ≤
      C2 * min (NodeHeight.mmin (insert θ A')
        (NodeHeight.st P (w ++ (γs ++ (ν ++ [e]).take i))))
        (NodeHeight.Mk 1 (NodeHeight.st P w)) := by
    rcases le_total (NodeHeight.mmin (insert θ A')
        (NodeHeight.st P (w ++ (γs ++ (ν ++ [e]).take i))))
        (NodeHeight.Mk 1 (NodeHeight.st P w)) with hle | hle
    · rw [min_eq_left hle]
      exact le_trans (min_le_left _ _) (le_mul_of_one_le_left (le_of_lt hxpos) hC2)
    · rw [min_eq_right hle]
      exact le_trans (min_le_right _ _) hC2bd
  calc NodeHeight.Mk 1 (NodeHeight.st P (w ++ (γs ++ (ν ++ [e]).take i)))
      ≤ 4 * (Fintype.card α : ℝ) * C0 *
          min (NodeHeight.mmin (insert θ A')
            (NodeHeight.st P (w ++ (γs ++ (ν ++ [e]).take i))))
            (NodeHeight.Mk 1 (NodeHeight.st P (w ++ γs))) := hbound
    _ ≤ 4 * (Fintype.card α : ℝ) * C0 *
          (C2 * min (NodeHeight.mmin (insert θ A')
            (NodeHeight.st P (w ++ (γs ++ (ν ++ [e]).take i))))
            (NodeHeight.Mk 1 (NodeHeight.st P w))) := mul_le_mul_of_nonneg_left hstep h4
    _ = 4 * (Fintype.card α : ℝ) * C0 * C2 *
          min (NodeHeight.mmin (insert θ A')
            (NodeHeight.st P (w ++ (γs ++ (ν ++ [e]).take i))))
            (NodeHeight.Mk 1 (NodeHeight.st P w)) := by ring

end HeightDichotomy

/-! ## 2. The single-letter case `A' = {b}`, for every `d`  The source's `Γ₃` needs the
continuations along which some `A'`-coordinate is stretched to be rare.  For `A' = {b}` this is
*provable from `CylinderMass.kerckhoff` alone*, because for a singleton "not an exit arrow" is
exactly "`b` does not win": a word whose first stop is unclean must therefore avoid `b` all the way
to that stop.  This gives the conclusion for every singleton `A'` and every `d`, with the sharp
constant `1 - 1/(2·#α)` — for `#α = 2` this is `3/4`, which cannot be improved. -/

namespace HeightDichotomy

open IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- The threshold `2·#α·M(q_w)` is positive. -/
theorem thr_pos (P : IETDatum₂ α n) (w : List Bool) : 0 < Stopping.thr P w := by
  have h1 : 0 < Stopping.Mx P w := Stopping.Mx_pos P w
  have h2 : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by
    have := NodeHeight.card_pos P
    exact_mod_cast this
  rw [Stopping.thr]
  nlinarith

omit [DecidableEq α] in
/-- For `A' = {b}`, an arrow is an exit arrow exactly when `b` wins. -/
theorem exitArrow_singleton_iff (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w μ : List Bool) (e : Bool) (b : α) :
    Stopping.ExitArrow P {b} w μ e ↔ (P.vertex (w ++ μ)).last e = b := by
  rw [Stopping.ExitArrow]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨h1, -⟩
    exact h1
  · intro h
    exact ⟨h, fun hh => vertex_last_ne_not P hP hn (w ++ μ) e (h.trans hh.symm)⟩

omit [DecidableEq α] in
/-- A word along which `b` never wins satisfies `NoWin`. -/
theorem noWin_of_last_ne (P : IETDatum₂ α n) (w μ : List Bool) (b : α)
    (h : ∀ g < μ.length, (P.vertex (w ++ μ.take g)).last (μ.getD g false) ≠ b) :
    CylinderMass.NoWin P w b μ := by
  induction μ generalizing w with
  | nil => exact trivial
  | cons e t ih =>
    have hlast : (P.vertex w).last e ≠ b := by
      have h0 := h 0 (by simp)
      simpa using h0
    refine ⟨hlast, ih (w ++ [e]) fun g hg => ?_⟩
    have h1 := h (g + 1) (by simp; omega)
    have htake : (e :: t).take (g + 1) = e :: t.take g := List.take_succ_cons
    have hget : (e :: t).getD (g + 1) false = t.getD g false := List.getD_cons_succ
    rw [htake, hget] at h1
    simpa [List.append_assoc] using h1

/-- Reading `j` letters of `δ` does not change the letters read. -/
theorem getD_take_take {δ : List Bool} {g j : ℕ} (hg : g < j) :
    (δ.take j).getD g false = δ.getD g false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
    if_pos hg]

/-- **A bad word stops at an unclean crossing, hence avoids the tracking letter up to that point.**
For `A' = {b}`: some `j ≤ |δ|` with `b` never winning on `δ.take j` and the `b`-height above the
threshold there. -/
theorem exists_noWin_crossing_singleton (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {w δ : List Bool} {b : α} (hb : Stopping.Bad P {b} w δ) :
    ∃ j ≤ δ.length, CylinderMass.NoWin P w b (δ.take j) ∧
      Stopping.thr P w < ColShrink.cs P (w ++ δ.take j) b := by
  classical
  obtain ⟨j, hj, -, hfirst, hclean⟩ := Stopping.bad_first_stop hb
  refine ⟨j, hj, ?_, ?_⟩
  · refine noWin_of_last_ne P w (δ.take j) b fun g hg => ?_
    rw [List.length_take] at hg
    have hgj : g < j := by omega
    have htake : (δ.take j).take g = δ.take g := by
      rw [List.take_take, Nat.min_eq_left (le_of_lt hgj)]
    rw [htake, getD_take_take hgj]
    intro hlast
    exact hfirst g hgj (Or.inr ⟨by omega,
      (exitArrow_singleton_iff P hP hn w (δ.take g) (δ.getD g false) b).mpr hlast⟩)
  · rw [Stopping.Clean] at hclean
    push Not at hclean
    obtain ⟨c, hc, hgt⟩ := hclean
    rw [Finset.mem_singleton] at hc
    rw [hc] at hgt
    exact hgt

/-- **Covering to Kerckhoff, one letter.**  Any prefix-free family of bad words for `A' = {b}` has
mass `< cs P w b / thr P w`, because its members extend the prefix-free family of minimal
`b`-avoiding `thr`-crossings, to which `CylinderMass.kerckhoff` applies. -/
theorem sum_cond_kerckhoff_singleton (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (b : α) (S : Finset (List Bool)) (hS : NodeHeight.PrefixFree S)
    (h : ∀ δ ∈ S, Stopping.Bad P {b} w δ) :
    ∑ δ ∈ S, CylinderMass.cond P w δ < ColShrink.cs P w b / Stopping.thr P w := by
  classical
  have hα : Nonempty α :=
    Fintype.card_pos_iff.mp (lt_of_lt_of_le Nat.zero_lt_one (NodeHeight.card_pos P))
  set U : Finset (List Bool) :=
    S.biUnion (fun δ => (Finset.range (δ.length + 1)).image (fun i => δ.take i)) with hU
  set U' : Finset (List Bool) :=
    U.filter (fun γ => CylinderMass.NoWin P w b γ ∧
      Stopping.thr P w < ColShrink.cs P (w ++ γ) b) with hU'
  have hcov : ∀ δ ∈ S, ∃ t ∈ U', t <+: δ := by
    intro δ hδ
    obtain ⟨j, hj, hnoWin, hcross⟩ := exists_noWin_crossing_singleton P hP hn (h δ hδ)
    have hmem : δ.take j ∈ U := by
      rw [hU]
      exact Finset.mem_biUnion.mpr ⟨δ, hδ, Finset.mem_image.mpr
        ⟨j, Finset.mem_range.mpr (by omega), rfl⟩⟩
    exact ⟨δ.take j, Finset.mem_filter.mpr ⟨hmem, hnoWin, hcross⟩, List.take_prefix j δ⟩
  obtain ⟨T, hTU', hTpf, hmass⟩ :=
    LargeLetter.exists_prefixFree_mass P hP hn w S U' hS hcov
  have hspec : ∀ t ∈ T, CylinderMass.NoWin P w b t ∧
      Stopping.thr P w < ColShrink.cs P (w ++ t) b :=
    fun t ht => (Finset.mem_filter.mp (hTU' ht)).2
  exact lt_of_le_of_lt hmass
    (kerckhoff_letter P hP hn w b (thr_pos P w) T hTpf hspec)

/-- **The single-letter conclusion, for any `d`.** The level-`N` words whose first stop is unclean
carry mass at most `1/(2·#α)`; equivalently the good words carry at least `1 - 1/(2·#α)`. -/
theorem sum_bad_singleton_le (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (b : α) (N : ℕ) :
    ∑ δ ∈ (Stopping.levelWords N).filter (fun δ => Stopping.Bad P {b} w δ),
        CylinderMass.cond P w δ ≤ 1 / (2 * (Fintype.card α : ℝ)) := by
  classical
  set S : Finset (List Bool) :=
    (Stopping.levelWords N).filter (fun δ => Stopping.Bad P {b} w δ) with hS
  have hSpf : NodeHeight.PrefixFree S := by
    intro δ hδ δ' hδ' hp
    have h1 : δ.length = N := by
      rw [hS] at hδ
      exact Stopping.length_of_mem_levelWords (Finset.mem_filter.mp hδ).1
    have h2 : δ'.length = N := by
      rw [hS] at hδ'
      exact Stopping.length_of_mem_levelWords (Finset.mem_filter.mp hδ').1
    have h3 : δ = δ' := hp.eq_of_length (by rw [h1, h2])
    rw [h3]
  have hbad : ∀ δ ∈ S, Stopping.Bad P {b} w δ := by
    intro δ hδ
    rw [hS] at hδ
    exact (Finset.mem_filter.mp hδ).2
  refine le_trans (le_of_lt (sum_cond_kerckhoff_singleton P hP hn w b S hSpf hbad)) ?_
  -- `cs P w b / thr P w ≤ 1/(2·#α)`
  have hd : (0 : ℝ) < (Fintype.card α : ℝ) := by
    have := NodeHeight.card_pos P
    exact_mod_cast this
  have hMx : 0 < Stopping.Mx P w := Stopping.Mx_pos P w
  have hb : ColShrink.cs P w b ≤ Stopping.Mx P w := Stopping.st_le_Mx P w b
  have hthr : Stopping.thr P w = 2 * (Fintype.card α : ℝ) * Stopping.Mx P w := rfl
  rw [hthr, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (Fintype.card α : ℝ) * Stopping.Mx P w)]
  have h2 : (1 / (2 * (Fintype.card α : ℝ))) *
      (2 * (Fintype.card α : ℝ) * Stopping.Mx P w) = Stopping.Mx P w := by
    field_simp
  rw [h2]
  exact hb

/-- The same statement in the good-words form: the good words at level `N` carry mass at least `1
- 1/(2·#α)`. -/
theorem singleton_mass (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (b : α) (w : List Bool) (N : ℕ) :
    1 - 1 / (2 * (Fintype.card α : ℝ)) ≤
      ∑ δ ∈ (Stopping.levelWords N).filter (fun δ => ¬ Stopping.Bad P {b} w δ),
        CylinderMass.cond P w δ := by
  classical
  have hspl := Stopping.sum_cond_levelWords P hP hn w N
  have hsplit : ∑ δ ∈ Stopping.levelWords N, CylinderMass.cond P w δ
      = ∑ δ ∈ (Stopping.levelWords N).filter (fun δ => Stopping.Bad P {b} w δ),
          CylinderMass.cond P w δ
        + ∑ δ ∈ (Stopping.levelWords N).filter (fun δ => ¬ Stopping.Bad P {b} w δ),
            CylinderMass.cond P w δ := by
    rw [Finset.sum_filter_add_sum_filter_not (s := Stopping.levelWords N)
      (p := fun δ => Stopping.Bad P {b} w δ) (f := fun δ => CylinderMass.cond P w δ)]
  have hle := sum_bad_singleton_le P hP hn w b N
  linarith

/-- **The `card = 1` case**, packaged without naming the letter. -/
theorem card_one_mass (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {A' : Finset α} (hcard : A'.card = 1) (w : List Bool) (N : ℕ) :
    1 - 1 / (2 * (Fintype.card α : ℝ)) ≤
      ∑ δ ∈ (Stopping.levelWords N).filter (fun δ => ¬ Stopping.Bad P A' w δ),
        CylinderMass.cond P w δ := by
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hcard
  exact singleton_mass P hP hn b w N

end HeightDichotomy

