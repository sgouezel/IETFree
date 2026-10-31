/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.SingularityList

/-!
The image side of `g ∘ f`, the partial sums, and the local presentation: the type `GoodRegion`.

This is where `IsCompType.image` and `IsCompPresentation.cell` are proved, on a ball of good
parameters:

* `exists_compImage_on_ball`: the cell `B k` of `g` that contains the image of the `k`-th marked
  cell is **locally constant**, with the two-sided interval condition;
* `markedImage_g` / `markedImage_gf`: consequently `g` at a marked image is affine, so
  `(g ∘ f) (s k)` is an affine function of the parameters;
* `partialSum_image` / `partialSum_cell`: the image starts and the cell starts are the partial
  sums of the cell lengths (the volume argument `sum_len_eq_of_tiling`);
* `exists_rank_perm` (from `IETFree.Presentation`) turns the order of the affine images into the
  permutation `ρ`;
* `exists_compPresentation_on_ball` assembles all of it, and `GoodRegion` /
  `ae_exists_goodRegion` is the resulting a.e. statement.

The file closes with the remark that `cell` must not be read as "`g ∘ f` maps cells onto cells": it
maps the `i`-th cell by `listImageLeft ρ s i - listLeftEnd s i`, which is the exchange `(ν, ρ)`
written in the coordinates of the list (see `IsCompPresentation`).

The type `GoodRegion` itself is at the end, with the two derived facts that keep its hypotheses out
of every statement (`simplexMap_mem_simplex_fst`, `simplexMap_mem_simplex_snd`); its fields `pres`
and `type` carry the presentation and the combinatorial type *at a point of the region* with no side
condition of their own, `G.pres q hq` and `G.type q hq`.  Next to it the two tuples of Section 3 are
bundled — `BlockIdx n`
(`k`, `l`, `hkl`, `hln`, with the `NeZero (l - k)` instance, in `IET.lean`), `Block` (`+ hstab`,
with `lam`, `perm` and the `Countable`
instance that makes "every block" a countable intersection) and `Fits` (`D.π = π`, `D.v = q.1`,
`E.π = σ`, `E.v = q.2`).
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-- **The explicit shape of the singularity list.**  Each entry of the marked list `s` of `g ∘ f` is
one of: `0`, `1`, a cut of `f` (a `leftEnd λ i`), or the preimage under `f` of a cut of `g` (a
`preimageCutAffine`).  This structure records *which* is which.

It is what the numerical statements of Section 3 need:

* the preimages of the marked points of `g` are in the list (`posG`), which is the input of
  `pairSplitting_mem_markedList`;
* every singularity is an integer affine function of the free parameters with explicitly bounded
  coefficients, which is what makes the block lengths Diophantine (Lemma 3.4);
* the μ-parts of the singularity functions are `0` for the cuts of `f` and the prefix sums of `μ`
  for the preimages, which is what makes them linearly independent — the "maximal rank" statement of
  Lemma 3.4.

The injectivity and disjointness fields make the count exact: there are `d - 1` cuts and `e - 1`
preimages, plus `0` and `1`, which is `n + 1 = d + e` points, so the list is exhausted by them. -/
structure SingularityShape {d e : ℕ} [NeZero d] [NeZero e] (n : ℕ) (π : Equiv.Perm (Fin d))
    (s : Fin (n + 1) → ParamAffine d e) (O : Set (PReal d e)) where
  /-- the cell of `f` whose image contains the `j`-th cut of `g` -/
  cellIdx : Fin (e - 1) → Fin d
  /-- the position in the list of the `i`-th cut of `f` -/
  posF : Fin (d - 1) → Fin (n + 1)
  /-- the position in the list of the preimage of the `j`-th cut of `g` -/
  posG : Fin (e - 1) → Fin (n + 1)
  posF_inj : Function.Injective posF
  posG_inj : Function.Injective posG
  posF_ne_posG : ∀ (i : Fin (d - 1)) (j : Fin (e - 1)), posF i ≠ posG j
  posF_ne_zero : ∀ i, posF i ≠ 0
  posF_ne_last : ∀ i, posF i ≠ Fin.last n
  posG_ne_zero : ∀ j, posG j ≠ 0
  posG_ne_last : ∀ j, posG j ≠ Fin.last n
  posF_spec : ∀ q ∈ O, ∀ i : Fin (d - 1),
    s (posF i) q = cutAffine (e := e) ⟨i.val + 1, by have := i.isLt; omega⟩ q
  posG_spec : ∀ q ∈ O, ∀ j : Fin (e - 1),
    s (posG j) q = preimageCutAffine π ⟨j.val + 1, by have := j.isLt; omega⟩ (cellIdx j) q
  /-- the `posG` entries really are the preimages under `f` of the cuts of `g`.  This is the strong
  form (an evaluation of `f⁻¹`, not the affine candidate), and it is what
  `pairSplitting_mem_markedList` consumes. -/
  posG_pre : ∀ q ∈ O, ∀ (j : Fin (e - 1)) (hl : simplexMap d q.1 ∈ simplex d),
    s (posG j) q = (mkIET1 (simplexMap d q.1) π hl)⁻¹
      (leftEnd (simplexMap e q.2) ⟨j.val + 1, by have := j.isLt; omega⟩)

/-- **The image of each marked cell lies in a single cell of `g`.**  At a good parameter pair, for
each marked cell `k` there is an index `B k` such that
`[f (s k), f (s k) + ν k) ⊆ [leftEnd μ (B k), leftEnd μ (B k) + μ (B k))`.

`B k` is `idx μ (f (s k))`.  The lower bound is `idx_mem`; the upper bound is
`no_gcut_inside_image` — if the image ran past `upperEnd μ (B k)` then the cut `leftEnd μ (B k + 1)`
would lie strictly inside it.  When `B k` is the last cell, the right end of the image is at most
`1` because the image is contained in `[0, 1)`. -/
theorem imageInG {d e n : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    {v : Fin (d - 1) → ℝ} {w : Fin (e - 1) → ℝ} (hv : v ∈ simplexRegion d)
    (hl : simplexMap d v ∈ simplex d) (hm : simplexMap e w ∈ simplex e)
    {τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1))} {s : Fin (n + 1) → ℝ}
    (hmono : StrictMono s) (hzero : s 0 = 0) (htop : s (Fin.last n) = 1)
    (hcut : ∀ i : Fin (d - 1),
      s ⟨(τ.symm (Sum.inl i)).val + 1, by have := (τ.symm (Sum.inl i)).isLt; omega⟩
        = leftEnd (simplexMap d v) ⟨i.val + 1, by have := i.isLt; omega⟩)
    (hpre : ∀ j : Fin (e - 1),
      s ⟨(τ.symm (Sum.inr j)).val + 1, by have := (τ.symm (Sum.inr j)).isLt; omega⟩
        = (mkIET1 (simplexMap d v) π hl)⁻¹
            (leftEnd (simplexMap e w) ⟨j.val + 1, by have := j.isLt; omega⟩)) :
    ∃ B : Fin n → Fin e, ∀ k : Fin n,
      leftEnd (simplexMap e w) (B k) ≤ mkIET1 (simplexMap d v) π hl (s k.castSucc) ∧
        mkIET1 (simplexMap d v) π hl (s k.castSucc) + (s k.succ - s k.castSucc)
          ≤ leftEnd (simplexMap e w) (B k) + (simplexMap e w (B k) : ℝ) := by
  classical
  have hsum_mu : (∑ j, (simplexMap e w j : ℝ)) = 1 := by
    rw [← NNReal.coe_sum]; exact_mod_cast hm
  -- `f (s k)` lies in `[0, 1)`
  have hk0 : ∀ k : Fin n, 0 ≤ s k.castSucc := by
    intro k; rw [← hzero]; exact hmono.monotone (Fin.zero_le _)
  have hk1 : ∀ k : Fin n, s k.castSucc < 1 := by
    intro k
    rw [← htop]
    exact hmono (by simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]; have := k.isLt; omega)
  have hks : ∀ k : Fin n, s k.succ ≤ 1 := by
    intro k
    rw [← htop]
    exact hmono.monotone (by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_last]; have := k.isLt; omega)
  have hfmem : ∀ k : Fin n,
      mkIET1 (simplexMap d v) π hl (s k.castSucc) ∈ Set.Ico (0 : ℝ) 1 :=
    fun k => (mkIET1 (simplexMap d v) π hl).isIET.mapsTo ⟨hk0 k, hk1 k⟩
  refine ⟨fun k => idx (simplexMap e w) (mkIET1 (simplexMap d v) π hl (s k.castSucc))
    (hfmem k).1, ?_⟩
  intro k
  constructor
  · exact idx_mem _ _ _
  · -- the right end
    by_contra hcon
    rw [not_le] at hcon
    -- the image identity and the containment of the image in `[0, 1)`
    obtain ⟨δ, hδ⟩ := markedCell_transl π hv hl hmono hzero htop hcut k
    have hcell : s k.castSucc < s k.succ := hmono (Fin.castSucc_lt_succ)
    have himg : mkIET1 (simplexMap d v) π hl '' Set.Ico (s k.castSucc) (s k.succ)
        = Set.Ico (mkIET1 (simplexMap d v) π hl (s k.castSucc))
            (mkIET1 (simplexMap d v) π hl (s k.castSucc) + (s k.succ - s k.castSucc)) := by
      have h := image_Ico_add hcell (f := mkIET1 (simplexMap d v) π hl) (δ := δ) hδ
      have h1' : s k.castSucc + δ = mkIET1 (simplexMap d v) π hl (s k.castSucc) :=
        (hδ _ le_rfl hcell).symm
      rw [h, h1']
      congr 1
      linarith [h1']
    have hsub : Set.Ico (mkIET1 (simplexMap d v) π hl (s k.castSucc))
        (mkIET1 (simplexMap d v) π hl (s k.castSucc) + (s k.succ - s k.castSucc))
        ⊆ Set.Ico (0 : ℝ) 1 := by
      rw [← himg]
      rintro y ⟨x, hx, rfl⟩
      exact (mkIET1 (simplexMap d v) π hl).isIET.mapsTo ⟨le_trans (hk0 k) hx.1,
        lt_of_lt_of_le hx.2 (hks k)⟩
    -- the index of the cell
    set c := idx (simplexMap e w) (mkIET1 (simplexMap d v) π hl (s k.castSucc)) (hfmem k).1 with hc
    beta_reduce at hcon
    rw [← hc, ← upperEnd_eq] at hcon
    have hup : mkIET1 (simplexMap d v) π hl (s k.castSucc) < upperEnd (simplexMap e w) c :=
      lt_upperEnd_idx (simplexMap e w) ⟨(hfmem k).1, by rw [hsum_mu]; exact (hfmem k).2⟩
    rcases eq_or_ne c (lastIdx e) with hcl | hcl
    · -- the last cell of `g`: `upperEnd = 1`
      have h1 : upperEnd (simplexMap e w) c = 1 := by
        rw [hcl, upperEnd_of_max (simplexMap e w) (fun j => by
          rw [Fin.le_def]; simp only [lastIdx]; have := j.isLt; omega), hsum_mu]
      rw [h1] at hup
      rw [h1] at hcon
      exact absurd (le_of_Ico_subset hup hsub) (not_le.mpr hcon)
    · -- not the last cell: the next cut lies strictly inside the image
      have hcv : c.val + 1 < e := by
        have h1 := c.isLt
        rcases Nat.lt_or_ge (c.val + 1) e with h | h
        · exact h
        · exfalso
          exact hcl (Fin.ext (by simp only [lastIdx]; omega))
      have hnext : upperEnd (simplexMap e w) c
          = leftEnd (simplexMap e w) ⟨c.val + 1, hcv⟩ := by
        rw [leftEnd_eq_upperEnd_of_succ (simplexMap e w) hcv, upperEnd_eq]
      have hleft : leftEnd (simplexMap e w) ⟨c.val + 1, hcv⟩ = upperEnd (simplexMap e w) c :=
        hnext.symm
      exact absurd ⟨by rw [hleft]; exact hup, by rw [hleft]; exact hcon⟩
        (no_gcut_inside_image π hv hl hmono hzero htop hcut hpre (k := k)
          (j := ⟨c.val, by have := c.isLt; omega⟩))

/-- **`g` translates the image of each marked cell.**  The cuts of `g` never lie strictly inside
such an image (`no_gcut_inside_image`), so the cut-set criterion applies with a vacuous
hypothesis. -/
theorem markedCell_g_transl {d e n : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) {v : Fin (d - 1) → ℝ} {w : Fin (e - 1) → ℝ}
    (hv : v ∈ simplexRegion d) (hw : w ∈ simplexRegion e) (hl : simplexMap d v ∈ simplex d)
    (hm : simplexMap e w ∈ simplex e)
    {τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1))} {s : Fin (n + 1) → ℝ}
    (hmono : StrictMono s) (hzero : s 0 = 0) (htop : s (Fin.last n) = 1)
    (hcut : ∀ i : Fin (d - 1),
      s ⟨(τ.symm (Sum.inl i)).val + 1, by have := (τ.symm (Sum.inl i)).isLt; omega⟩
        = leftEnd (simplexMap d v) ⟨i.val + 1, by have := i.isLt; omega⟩)
    (hpre : ∀ j : Fin (e - 1),
      s ⟨(τ.symm (Sum.inr j)).val + 1, by have := (τ.symm (Sum.inr j)).isLt; omega⟩
        = (mkIET1 (simplexMap d v) π hl)⁻¹
            (leftEnd (simplexMap e w) ⟨j.val + 1, by have := j.isLt; omega⟩))
    (k : Fin n) :
    ∃ δ : ℝ, ∀ x : ℝ, s k.castSucc ≤ x → x < s k.succ →
      mkIET1 (simplexMap e w) σ hm (mkIET1 (simplexMap d v) π hl x)
        = mkIET1 (simplexMap d v) π hl x + δ := by
  have hsum_mu : (∑ j, (simplexMap e w j : ℝ)) = 1 := by
    rw [← NNReal.coe_sum]; exact_mod_cast hm
  have hcs := isCutSet_mkIET1 (simplexMap e w) σ hm
  obtain ⟨δ, hδ⟩ := markedCell_transl π hv hl hmono hzero htop hcut k
  have hcell : s k.castSucc < s k.succ := hmono (Fin.castSucc_lt_succ)
  -- the image identity
  have himg : mkIET1 (simplexMap d v) π hl '' Set.Ico (s k.castSucc) (s k.succ)
      = Set.Ico (mkIET1 (simplexMap d v) π hl (s k.castSucc))
          (mkIET1 (simplexMap d v) π hl (s k.castSucc) + (s k.succ - s k.castSucc)) := by
    have h := image_Ico_add hcell (f := mkIET1 (simplexMap d v) π hl) (δ := δ) hδ
    have h1' : s k.castSucc + δ = mkIET1 (simplexMap d v) π hl (s k.castSucc) :=
      (hδ _ le_rfl hcell).symm
    rw [h, h1']
    congr 1
    linarith [h1']
  refine ⟨mkIET1 (simplexMap e w) σ hm (mkIET1 (simplexMap d v) π hl (s k.castSucc))
    - mkIET1 (simplexMap d v) π hl (s k.castSucc), ?_⟩
  intro x hx1 hx2
  -- `f x` lies in the image
  have hfx : mkIET1 (simplexMap d v) π hl x
      ∈ Set.Ico (mkIET1 (simplexMap d v) π hl (s k.castSucc))
          (mkIET1 (simplexMap d v) π hl (s k.castSucc) + (s k.succ - s k.castSucc)) := by
    rw [← himg]
    exact ⟨x, ⟨hx1, hx2⟩, rfl⟩
  -- `s k.castSucc` and `x` lie in `[0, 1)`
  have hk0 : 0 ≤ s k.castSucc := by
    rw [← hzero]; exact hmono.monotone (Fin.zero_le _)
  have hks : s k.succ ≤ 1 := by
    rw [← htop]
    exact hmono.monotone (by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_last]; have := k.isLt; omega)
  have hfk : mkIET1 (simplexMap d v) π hl (s k.castSucc) ∈ Set.Ico (0 : ℝ) 1 :=
    (mkIET1 (simplexMap d v) π hl).isIET.mapsTo ⟨hk0, lt_of_lt_of_le hcell hks⟩
  have hfxmem : mkIET1 (simplexMap d v) π hl x ∈ Set.Ico (0 : ℝ) 1 :=
    (mkIET1 (simplexMap d v) π hl).isIET.mapsTo
      ⟨le_trans hk0 hx1, lt_of_lt_of_le hx2 hks⟩
  have hkey : mkIET1 (simplexMap e w) σ hm (mkIET1 (simplexMap d v) π hl x)
        - mkIET1 (simplexMap d v) π hl x
      = mkIET1 (simplexMap e w) σ hm (mkIET1 (simplexMap d v) π hl (s k.castSucc))
        - mkIET1 (simplexMap d v) π hl (s k.castSucc) := by
    refine hcs.transl_of_locally (x := mkIET1 (simplexMap d v) π hl (s k.castSucc))
      (y := mkIET1 (simplexMap d v) π hl x) hfk hfxmem ?_
    intro c hc hmin hmax
    exfalso
    -- a cut of `g` in `(min, max]` would lie strictly inside the image
    obtain ⟨j, hj⟩ := (mem_mkIETCuts_one (pos_simplexMap hw) hsum_mu).mp hc
    have hmin' : mkIET1 (simplexMap d v) π hl (s k.castSucc) < c := by
      rw [min_eq_left hfx.1] at hmin; exact hmin
    have hmax' : c ≤ mkIET1 (simplexMap d v) π hl x := by
      rw [max_eq_right hfx.1] at hmax; exact hmax
    rcases eq_or_ne j 0 with rfl | hj0
    · rw [leftEnd_zero] at hj
      linarith [hfk.1, hmin', hj]
    · have hpos : 0 < j.val := by
        rcases Nat.eq_zero_or_pos j.val with h | h
        · exact absurd (Fin.ext (by simpa using h)) hj0
        · exact h
      have hjj : (⟨(⟨j.val - 1, by have := j.isLt; have := NeZero.pos e; omega⟩ :
          Fin (e - 1)).val + 1, by have := j.isLt; omega⟩ : Fin e) = j := by
        ext
        change (⟨j.val - 1, by have := j.isLt; have := NeZero.pos e; omega⟩ :
          Fin (e - 1)).val + 1 = j.val
        exact Nat.succ_pred_eq_of_pos hpos
      have key := no_gcut_inside_image π hv hl hmono hzero htop hcut hpre (k := k)
        (j := ⟨j.val - 1, by have := j.isLt; have := NeZero.pos e; omega⟩)
      rw [hjj] at key
      exact absurd ⟨by rw [hj]; exact hmin', by rw [hj]; linarith [hfx.2]⟩ key
  linarith

/-- **A marked image coincides with a cut of `g` only identically**: if `f (s k) = leftEnd μ j`
at one parameter of the ball (with `j ≠ 0`), then `s k` is the marked preimage of that cut and
`markedPos k = cutAffineRight j` as affine functions.

This is what makes the order of the marked images locally constant: `f (s k)` can only cross a cut
of `g` by sitting exactly on it, which happens only for the marked preimage of that cut. -/
theorem markedPos_eq_cut_of_eq {d e n : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (κ : Fin (e - 1) → Fin d) (τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1)))
    {hn : 1 ≤ n} {A : Fin (n - 1) → ParamAffine d e}
    (hA : ∀ m, A m = singAffine π κ (τ m)) {q₀ : PReal d e} {ε : ℝ}
    (hr : ∀ q ∈ Metric.ball q₀ ε, q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e)
    (hmono : ∀ q ∈ Metric.ball q₀ ε, StrictMono fun j => withEnds hn A j q)
    (hzero : ∀ q ∈ Metric.ball q₀ ε, withEnds hn A 0 q = 0)
    (hcut : ∀ q ∈ Metric.ball q₀ ε, ∀ i : Fin (d - 1),
      withEnds hn A ⟨(τ.symm (Sum.inl i)).val + 1,
          by have := (τ.symm (Sum.inl i)).isLt; omega⟩ q
        = leftEnd (simplexMap d q.1) ⟨i.val + 1, by have := i.isLt; omega⟩)
    (hpre : ∀ (q : PReal d e), q ∈ Metric.ball q₀ ε →
      ∀ (j : Fin (e - 1)) (hl : simplexMap d q.1 ∈ simplex d),
      withEnds hn A ⟨(τ.symm (Sum.inr j)).val + 1,
          by have := (τ.symm (Sum.inr j)).isLt; omega⟩ q
        = (mkIET1 (simplexMap d q.1) π hl)⁻¹
            (leftEnd (simplexMap e q.2) ⟨j.val + 1, by have := j.isLt; omega⟩))
    {j : Fin e} (hj : j ≠ 0) (k : Fin n)
    (h : ∃ q ∈ Metric.ball q₀ ε, markedPos (e := e) π τ k q = cutAffineRight (d := d) j q) :
    markedPos (e := e) π τ k = cutAffineRight (d := d) j := by
  obtain ⟨q, hq, heq⟩ := h
  have hrq := hr q hq
  have hl : simplexMap d q.1 ∈ simplex d := simplexMap_mem_simplex_fin hrq.1.1 hrq.1.2
  have hjpos : 0 < j.val := Fin.pos_iff_ne_zero.mpr hj
  have hjlt : j.val - 1 < e - 1 := by have := j.isLt; have := NeZero.pos e; omega
  set r' : Fin (e - 1) := ⟨j.val - 1, hjlt⟩ with hr'
  set m : Fin (n - 1) := τ.symm (Sum.inr r') with hm'
  have hjr : (⟨r'.val + 1, by have := r'.isLt; omega⟩ : Fin e) = j := by
    refine Fin.ext ?_
    simp only [hr']
    omega
  -- the marked point `s k` maps to the cut
  have hfk : mkIET1 (simplexMap d q.1) π hl (withEnds hn A k.castSucc q)
      = leftEnd (simplexMap e q.2) j := by
    rw [markedPos_spec (hn := hn) (A := A) (q := q) π κ τ hA hrq (hzero q hq)
      (fun i => hcut q hq i) (fun j' => hpre q hq j' hl)]
    rw [← cutAffineRight_eq_leftEnd (d := d) hrq.2]
    exact heq
  -- the marked preimage of that cut
  have hprej : withEnds hn A ⟨(τ.symm (Sum.inr r')).val + 1,
      by have := (τ.symm (Sum.inr r')).isLt; omega⟩ q
      = (mkIET1 (simplexMap d q.1) π hl)⁻¹ (leftEnd (simplexMap e q.2) j) := by
    have h := hpre q hq r' hl
    simp only [hjr] at h
    exact h
  have hsk : withEnds hn A k.castSucc q
      = withEnds hn A ⟨m.val + 1, by have := m.isLt; omega⟩ q := by
    rw [show (⟨m.val + 1, by have := m.isLt; omega⟩ : Fin (n + 1))
      = (⟨(τ.symm (Sum.inr r')).val + 1,
          by have := (τ.symm (Sum.inr r')).isLt; omega⟩ : Fin (n + 1)) from rfl]
    rw [hprej, ← hfk, IET.symm_apply_apply]
  -- so the indices coincide and the two affine functions are equal
  have hidx : k.castSucc = (⟨m.val + 1, by have := m.isLt; omega⟩ : Fin (n + 1)) :=
    (hmono q hq).injective hsk
  have hkval : k = (⟨m.val + 1, by have := m.isLt; omega⟩ : Fin n) :=
    Fin.ext (by simpa using congrArg Fin.val hidx)
  rw [hkval]
  have hsymm : τ m = Sum.inr r' := by rw [hm']; exact Equiv.apply_symm_apply τ _
  rw [markedPos_inr π τ m r' hsymm]
  exact congrArg (cutAffineRight (d := d)) hjr

/-- **The image of a marked cell lies in the `idx`-cell of `g`** — the pointwise form of
`imageInG`, with the index made explicit.  The two inequalities of `IsCompType.image` for
`B k = idx μ (f (s k))` follow from `imageInG` and the uniqueness of `idx` (the right end of a
nonempty image is above its left end, so the point is strictly inside the `g`-cell). -/
theorem imageInG_idx {d e n : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    {v : Fin (d - 1) → ℝ} {w : Fin (e - 1) → ℝ} (hv : v ∈ simplexRegion d)
    (hl : simplexMap d v ∈ simplex d) (hm : simplexMap e w ∈ simplex e)
    {τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1))} {s : Fin (n + 1) → ℝ}
    (hmono : StrictMono s) (hzero : s 0 = 0) (htop : s (Fin.last n) = 1)
    (hcut : ∀ i : Fin (d - 1),
      s ⟨(τ.symm (Sum.inl i)).val + 1, by have := (τ.symm (Sum.inl i)).isLt; omega⟩
        = leftEnd (simplexMap d v) ⟨i.val + 1, by have := i.isLt; omega⟩)
    (hpre : ∀ j : Fin (e - 1),
      s ⟨(τ.symm (Sum.inr j)).val + 1, by have := (τ.symm (Sum.inr j)).isLt; omega⟩
        = (mkIET1 (simplexMap d v) π hl)⁻¹
            (leftEnd (simplexMap e w) ⟨j.val + 1, by have := j.isLt; omega⟩))
    (k : Fin n)
    (hkmem : mkIET1 (simplexMap d v) π hl (s k.castSucc) ∈ Set.Ico (0 : ℝ) 1) :
    leftEnd (simplexMap e w)
        (idx (simplexMap e w) (mkIET1 (simplexMap d v) π hl (s k.castSucc)) hkmem.1)
      ≤ mkIET1 (simplexMap d v) π hl (s k.castSucc) ∧
      mkIET1 (simplexMap d v) π hl (s k.castSucc) + (s k.succ - s k.castSucc)
        ≤ leftEnd (simplexMap e w)
            (idx (simplexMap e w) (mkIET1 (simplexMap d v) π hl (s k.castSucc)) hkmem.1)
          + (simplexMap e w
            (idx (simplexMap e w) (mkIET1 (simplexMap d v) π hl (s k.castSucc)) hkmem.1) : ℝ) := by
  obtain ⟨B, hB⟩ := imageInG π hv hl hm hmono hzero htop hcut hpre
  obtain ⟨h1, h2⟩ := hB k
  have hsum_mu : (∑ j, (simplexMap e w j : ℝ)) = 1 := by
    rw [← NNReal.coe_sum]; exact_mod_cast hm
  have hpos : 0 < s k.succ - s k.castSucc :=
    sub_pos.mpr (hmono (Fin.castSucc_lt_succ (i := k)))
  have h2' : mkIET1 (simplexMap d v) π hl (s k.castSucc)
      < upperEnd (simplexMap e w) (B k) := by
    rw [upperEnd_eq]; linarith
  have hidx : idx (simplexMap e w) (mkIET1 (simplexMap d v) π hl (s k.castSucc)) hkmem.1
      = B k :=
    idx_eq (simplexMap e w) ⟨hkmem.1, by rw [hsum_mu]; exact hkmem.2⟩ h1 h2'
  rw [hidx]
  exact ⟨h1, h2⟩

/-- **The marked index of the `i`-th cut of `f`**: `a 0 = 0`, `a (Fin.last d) = Fin.last n`, and the
`i`-th cut (`i ≠ 0`) sits at the marked position recorded by `τ`. -/
noncomputable def compTypeA {d e n : ℕ} (τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1))) :
    Fin (d + 1) → Fin (n + 1) :=
  fun i => if h0 : i.val = 0 then 0
    else if hd : i.val = d then Fin.last n
    else ⟨(τ.symm (Sum.inl ⟨i.val - 1, by have := i.isLt; omega⟩)).val + 1, by
      have := (τ.symm (Sum.inl ⟨i.val - 1, by have := i.isLt; omega⟩)).isLt; omega⟩

theorem compTypeA_zero {d e n : ℕ} (τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1))) :
    compTypeA τ 0 = 0 := by
  simp [compTypeA]

theorem compTypeA_last {d e n : ℕ} [NeZero d]
    (τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1))) :
    compTypeA τ (Fin.last d) = Fin.last n := by
  simp [compTypeA, NeZero.ne d]

theorem compTypeA_succ {d e n : ℕ} (τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1)))
    (i : Fin (d - 1)) :
    compTypeA τ ⟨i.val + 1, by have := i.isLt; omega⟩
      = ⟨(τ.symm (Sum.inl i)).val + 1, by have := (τ.symm (Sum.inl i)).isLt; omega⟩ := by
  have h0 : ¬ ((⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (d + 1)).val = 0) := by
    simp
  have hd : ¬ ((⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (d + 1)).val = d) := by
    simp only []; have := i.isLt; omega
  have hidx : (⟨(⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (d + 1)).val - 1,
      by have := i.isLt; omega⟩ : Fin (d - 1)) = i :=
    Fin.ext (by simp)
  rw [compTypeA, dif_neg h0, dif_neg hd]
  simp only [hidx]

/-- **The cuts of `f` sit at the marked positions given by `a`**:
`s (a i.castSucc) = leftEnd λ i`. -/
theorem compTypeA_cut {d e n : ℕ} [NeZero d] {τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1))}
    {lam : Fin d → ℝ≥0} {s : Fin (n + 1) → ℝ} (hzero : s 0 = 0)
    (hcut : ∀ i : Fin (d - 1),
      s ⟨(τ.symm (Sum.inl i)).val + 1, by have := (τ.symm (Sum.inl i)).isLt; omega⟩
        = leftEnd lam ⟨i.val + 1, by have := i.isLt; omega⟩)
    (i : Fin d) : s (compTypeA τ i.castSucc) = leftEnd lam i := by
  rcases eq_or_ne i.val 0 with hi | hi
  · -- `i = 0`
    have hi0 : i = 0 := Fin.ext (by simpa using hi)
    subst hi0
    rw [show (0 : Fin d).castSucc = (0 : Fin (d + 1)) from Fin.ext rfl, compTypeA_zero, hzero,
      leftEnd_zero]
  · -- `i = i' + 1`
    have hpos : 0 < i.val := by
      rcases Nat.eq_zero_or_pos i.val with h | h
      · exact absurd h hi
      · exact h
    have hcast : (⟨(⟨i.val - 1, by have := i.isLt; have := NeZero.pos d; omega⟩ :
        Fin (d - 1)).val + 1, by have := i.isLt; omega⟩ : Fin (d + 1)) = i.castSucc := by
      ext
      change i.val - 1 + 1 = i.val
      exact Nat.succ_pred_eq_of_pos hpos
    rw [← hcast, compTypeA_succ, hcut]
    congr 1
    ext
    simp only []
    omega

theorem upperEndAffineRight_of_lt {d e : ℕ} [NeZero e] {j : Fin e} (h : j.val + 1 < e) :
    upperEndAffineRight (d := d) j = cutAffineRight (d := d) ⟨j.val + 1, h⟩ := by
  rw [upperEndAffineRight, dif_neg (by omega)]

theorem upperEndAffineRight_of_last {d e : ℕ} [NeZero e] {j : Fin e} (h : j.val + 1 = e) :
    upperEndAffineRight (d := d) j = AffineMap.const ℝ (PReal d e) (1 : ℝ) := by
  rw [upperEndAffineRight, dif_pos h]

/-- **The `g`-cell containing the image of each marked cell is locally constant**, with the
two-sided interval condition of `IsCompType.image`. -/
theorem exists_compImage_on_ball {d e n : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (κ : Fin (e - 1) → Fin d) (τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1)))
    {hn : 1 ≤ n} {A : Fin (n - 1) → ParamAffine d e}
    (hA : ∀ m, A m = singAffine π κ (τ m)) {q₀ : PReal d e} {ε : ℝ} (hε : 0 < ε)
    (hr : ∀ q ∈ Metric.ball q₀ ε, q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e)
    (hmono : ∀ q ∈ Metric.ball q₀ ε, StrictMono fun j => withEnds hn A j q)
    (hzero : ∀ q ∈ Metric.ball q₀ ε, withEnds hn A 0 q = 0)
    (htop : ∀ q ∈ Metric.ball q₀ ε, withEnds hn A (Fin.last n) q = 1)
    (hcut : ∀ q ∈ Metric.ball q₀ ε, ∀ i : Fin (d - 1),
      withEnds hn A ⟨(τ.symm (Sum.inl i)).val + 1,
          by have := (τ.symm (Sum.inl i)).isLt; omega⟩ q
        = leftEnd (simplexMap d q.1) ⟨i.val + 1, by have := i.isLt; omega⟩)
    (hpre : ∀ (q : PReal d e), q ∈ Metric.ball q₀ ε →
      ∀ (j : Fin (e - 1)) (hl : simplexMap d q.1 ∈ simplex d),
      withEnds hn A ⟨(τ.symm (Sum.inr j)).val + 1,
          by have := (τ.symm (Sum.inr j)).isLt; omega⟩ q
        = (mkIET1 (simplexMap d q.1) π hl)⁻¹
            (leftEnd (simplexMap e q.2) ⟨j.val + 1, by have := j.isLt; omega⟩)) :
    ∃ B : Fin n → Fin e, ∀ (q : PReal d e), q ∈ Metric.ball q₀ ε →
      ∀ (hl : simplexMap d q.1 ∈ simplex d) (k : Fin n),
      leftEnd (simplexMap e q.2) (B k)
          ≤ mkIET1 (simplexMap d q.1) π hl (withEnds hn A k.castSucc q) ∧
        mkIET1 (simplexMap d q.1) π hl (withEnds hn A k.castSucc q)
            + (withEnds hn A k.succ q - withEnds hn A k.castSucc q)
          ≤ leftEnd (simplexMap e q.2) (B k) + (simplexMap e q.2 (B k) : ℝ) := by
  classical
  have hq₀ : q₀ ∈ Metric.ball q₀ ε := Metric.mem_ball_self hε
  have hr₀ := hr q₀ hq₀
  have hl₀ : simplexMap d q₀.1 ∈ simplex d := simplexMap_mem_simplex_fin hr₀.1.1 hr₀.1.2
  have hm₀ : simplexMap e q₀.2 ∈ simplex e := simplexMap_mem_simplex_fin hr₀.2.1 hr₀.2.2
  have hsum_mu : (∑ j, (simplexMap e q₀.2 j : ℝ)) = 1 := by
    rw [← NNReal.coe_sum]; exact_mod_cast hm₀
  -- the marked points lie in `[0, 1)`
  have hk0 : ∀ (q : PReal d e), q ∈ Metric.ball q₀ ε → ∀ k : Fin n,
      0 ≤ withEnds hn A k.castSucc q := by
    intro q hq k
    rw [← hzero q hq]
    exact (hmono q hq).monotone (Fin.zero_le _)
  have hk1 : ∀ (q : PReal d e), q ∈ Metric.ball q₀ ε → ∀ k : Fin n,
      withEnds hn A k.castSucc q < 1 := by
    intro q hq k
    rw [← htop q hq]
    exact (hmono q hq) (by
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]; have := k.isLt; omega)
  -- the image of a marked point under `f` is `markedPos`
  have hP : ∀ (q : PReal d e) (hq : q ∈ Metric.ball q₀ ε) (k : Fin n)
      (hl : simplexMap d q.1 ∈ simplex d),
      mkIET1 (simplexMap d q.1) π hl (withEnds hn A k.castSucc q) = markedPos (e := e) π τ k q := by
    intro q hq k hl
    exact markedPos_spec (hn := hn) (A := A) (q := q) π κ τ hA (hr q hq) (hzero q hq)
      (fun i => hcut q hq i) (fun j' => hpre q hq j' hl) k
  -- the image lies in `[0, 1)`
  have hfmem : ∀ (q : PReal d e), q ∈ Metric.ball q₀ ε → ∀ k : Fin n,
      markedPos (e := e) π τ k q ∈ Set.Ico (0 : ℝ) 1 := by
    intro q hq k
    have hl : simplexMap d q.1 ∈ simplex d :=
      simplexMap_mem_simplex_fin (hr q hq).1.1 (hr q hq).1.2
    rw [← hP q hq k hl]
    exact (mkIET1 (simplexMap d q.1) π hl).isIET.mapsTo ⟨hk0 q hq k, hk1 q hq k⟩
  -- the index of the `g`-cell containing the image, at `q₀`
  let B : Fin n → Fin e := fun k =>
    idx (simplexMap e q₀.2) (markedPos (e := e) π τ k q₀) (hfmem q₀ hq₀ k).1
  have hidxmem : ∀ k : Fin n, (markedPos (e := e) π τ k q₀)
      ∈ Set.Ico (0 : ℝ) (∑ j, (simplexMap e q₀.2 j : ℝ)) := by
    intro k
    exact ⟨(hfmem q₀ hq₀ k).1, by rw [hsum_mu]; exact (hfmem q₀ hq₀ k).2⟩
  -- the image sits above the left end of its `g`-cell
  have hlow : ∀ (q : PReal d e), q ∈ Metric.ball q₀ ε → ∀ k : Fin n,
      cutAffineRight (d := d) (B k) q ≤ markedPos (e := e) π τ k q := by
    intro q hq k
    by_cases hB0 : B k = 0
    · rw [hB0, cutAffineRight_eq_leftEnd (d := d) (hr q hq).2, leftEnd_zero]
      exact (hfmem q hq k).1
    · have hGapp : ∀ x : PReal d e,
          (markedPos (e := e) π τ k - cutAffineRight (d := d) (B k)) x
            = markedPos (e := e) π τ k x - cutAffineRight (d := d) (B k) x := fun x => rfl
      have hres := nonneg_on_ball_of_vanish_imp (d := d) (e := e)
        (G := markedPos (e := e) π τ k - cutAffineRight (d := d) (B k)) hε ?_ ?_ q hq
      · have := hres
        rw [hGapp] at this
        linarith
      · -- vanishing at one point of the ball forces vanishing identically
        rintro q' hq' hzero'
        have heq' : markedPos (e := e) π τ k q' = cutAffineRight (d := d) (B k) q' := by
          rw [hGapp] at hzero'
          linarith
        have hBeq : markedPos (e := e) π τ k = cutAffineRight (d := d) (B k) :=
          markedPos_eq_cut_of_eq π κ τ hA hr hmono hzero hcut hpre hB0 k ⟨q', hq', heq'⟩
        exact sub_eq_zero.mpr hBeq
      · -- the value at `q₀` is nonnegative
        have hmem := idx_mem (simplexMap e q₀.2) (markedPos (e := e) π τ k q₀) (hfmem q₀ hq₀ k).1
        rw [hGapp, cutAffineRight_eq_leftEnd (d := d) hr₀.2]
        linarith
  -- the image ends below the upper end of its `g`-cell
  have hup : ∀ (q : PReal d e), q ∈ Metric.ball q₀ ε → ∀ k : Fin n,
      markedPos (e := e) π τ k q < upperEndAffineRight (d := d) (B k) q := by
    intro q hq k
    have hstr₀ : markedPos (e := e) π τ k q₀ < upperEndAffineRight (d := d) (B k) q₀ := by
      have hlt := lt_upperEnd_idx (simplexMap e q₀.2) (hidxmem k)
      rwa [← upperEndAffineRight_eq hr₀.2] at hlt
    rcases lt_or_eq_of_le (show (B k).val + 1 ≤ e by have := (B k).isLt; omega) with hlt | heq
    · -- not the last cell of `g`
      have hU : upperEndAffineRight (d := d) (B k) = cutAffineRight (d := d) ⟨(B k).val + 1, hlt⟩ :=
        upperEndAffineRight_of_lt hlt
      have hGapp : ∀ x : PReal d e,
          (upperEndAffineRight (d := d) (B k) - markedPos (e := e) π τ k) x
            = upperEndAffineRight (d := d) (B k) x - markedPos (e := e) π τ k x := fun x => rfl
      have hres := pos_on_ball_of_vanish_imp (d := d) (e := e)
        (G := upperEndAffineRight (d := d) (B k) - markedPos (e := e) π τ k) hε ?_ ?_ q hq
      · have := hres
        rw [hGapp] at this
        linarith
      · rintro q' hq' hzero'
        have heq' : markedPos (e := e) π τ k q'
            = cutAffineRight (d := d) ⟨(B k).val + 1, hlt⟩ q' := by
          rw [hGapp, hU] at hzero'
          linarith
        have hne : (⟨(B k).val + 1, hlt⟩ : Fin e) ≠ 0 := by
          intro hc
          have h2 := congrArg Fin.val hc
          simp only [Fin.val_zero] at h2
          have := (B k).isLt
          omega
        have hBeq := markedPos_eq_cut_of_eq π κ τ hA hr hmono hzero hcut hpre hne k ⟨q', hq', heq'⟩
        rw [hU]
        exact sub_eq_zero.mpr hBeq.symm
      · rw [hGapp]
        linarith
    · -- the last cell: its upper end is `1`
      have hU : upperEndAffineRight (d := d) (B k) = AffineMap.const ℝ (PReal d e) 1 :=
        upperEndAffineRight_of_last heq
      have hc : (AffineMap.const ℝ (PReal d e) (1 : ℝ)) q = 1 := rfl
      rw [hU, hc, ← hP q hq k (simplexMap_mem_simplex_fin (hr q hq).1.1 (hr q hq).1.2)]
      exact (mkIET1 (simplexMap d q.1) π
        (simplexMap_mem_simplex_fin (hr q hq).1.1 (hr q hq).1.2)).isIET.mapsTo
        ⟨hk0 q hq k, hk1 q hq k⟩ |>.2
  -- the `g`-cell of the image is `B k` at every parameter of the ball
  refine ⟨B, ?_⟩
  intro q hq hl k
  have hsum : (∑ j, (simplexMap e q.2 j : ℝ)) = 1 := by
    rw [← NNReal.coe_sum]
    exact_mod_cast simplexMap_mem_simplex_fin (hr q hq).2.1 (hr q hq).2.2
  have hkmem : mkIET1 (simplexMap d q.1) π hl (withEnds hn A k.castSucc q) ∈ Set.Ico (0 : ℝ) 1 :=
    (mkIET1 (simplexMap d q.1) π hl).isIET.mapsTo ⟨hk0 q hq k, hk1 q hq k⟩
  have hm : simplexMap e q.2 ∈ simplex e := simplexMap_mem_simplex_fin (hr q hq).2.1 (hr q hq).2.2
  obtain ⟨i1, i2⟩ := imageInG_idx π (hr q hq).1 hl hm (hmono q hq) (hzero q hq) (htop q hq)
    (fun i => hcut q hq i) (fun j' => hpre q hq j' hl) k hkmem
  have hidxB : idx (simplexMap e q.2) (mkIET1 (simplexMap d q.1) π hl (withEnds hn A k.castSucc q))
      hkmem.1 = B k := by
    refine idx_eq (simplexMap e q.2) ⟨hkmem.1, by rw [hsum]; exact hkmem.2⟩ ?_ ?_
    · rw [hP q hq k hl, ← cutAffineRight_eq_leftEnd (d := d) (hr q hq).2]
      exact hlow q hq k
    · rw [hP q hq k hl, ← upperEndAffineRight_eq (hr q hq).2 (B k)]
      exact hup q hq k
  simp only [hidxB] at i1 i2
  exact ⟨i1, i2⟩

/-- **`g` at a marked image is affine**: the image of the `i`-th marked cell lies inside the
`B i`-th cell of `g`, on which `g` is the translation by `translationVector σ μ (B i)`. -/
theorem markedImage_g {d e n : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) {s : Fin (n + 1) → ℝ}
    (hmono : StrictMono s) (hzero : s 0 = 0) (htop : s (Fin.last n) = 1)
    {v : Fin (d - 1) → ℝ} {w : Fin (e - 1) → ℝ} (hl : simplexMap d v ∈ simplex d)
    (hm : simplexMap e w ∈ simplex e) {P : Fin n → ℝ}
    (hP : ∀ i, mkIET1 (simplexMap d v) π hl (s i.castSucc) = P i) {B : Fin n → Fin e}
    (hB : ∀ i, leftEnd (simplexMap e w) (B i) ≤ P i ∧
      P i + (s i.succ - s i.castSucc) ≤ leftEnd (simplexMap e w) (B i) + (simplexMap e w (B i) : ℝ))
    (i : Fin n) :
    mkIET1 (simplexMap e w) σ hm (P i)
      = P i + translationVector σ (simplexMap e w) (B i) := by
  have hsum_mu : (∑ j, (simplexMap e w j : ℝ)) = 1 := by
    rw [← NNReal.coe_sum]; exact_mod_cast hm
  have hν : 0 < s i.succ - s i.castSucc := sub_pos.mpr (hmono (Fin.castSucc_lt_succ (i := i)))
  have hs0 : 0 ≤ s i.castSucc := by
    rw [← hzero]
    exact hmono.monotone (Fin.zero_le _)
  have hs1 : s i.castSucc < 1 := by
    rw [← htop]
    exact hmono (by
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]; have := i.isLt; omega)
  have hfm : mkIET1 (simplexMap d v) π hl (s i.castSucc) ∈ Set.Ico (0 : ℝ) 1 :=
    (mkIET1 (simplexMap d v) π hl).isIET.mapsTo ⟨hs0, hs1⟩
  have hmem0 : 0 ≤ P i := by rw [← hP i]; exact hfm.1
  have hmem1 : P i < upperEnd (simplexMap e w) (B i) := by
    rw [upperEnd_eq]
    linarith [(hB i).2, hν]
  have htot : upperEnd (simplexMap e w) (B i) ≤ 1 := by
    have h := upperEnd_le_total (simplexMap e w) (B i)
    rwa [hsum_mu] at h
  have hx : P i ∈ Set.Ico (0 : ℝ) (∑ j, (simplexMap e w j : ℝ)) :=
    ⟨hmem0, by rw [hsum_mu]; linarith⟩
  have hidx : idx (simplexMap e w) (P i) hx.1 = B i :=
    idx_eq (simplexMap e w) hx (hB i).1 hmem1
  have hx' : P i ∈ Set.Ico (0 : ℝ) (0 + ∑ j, (simplexMap e w j : ℝ)) :=
    ⟨hmem0, by rw [hsum_mu]; linarith⟩
  have hlink : (mkIET1 (simplexMap e w) σ hm) (P i)
      = mkIETFun (simplexMap e w) σ 0 (P i) := rfl
  rw [hlink, mkIETFun_of_mem _ _ 0 hx']
  simp only [sub_zero]
  rw [hidx]

/-- **`(g ∘ f)` at a marked point is affine**: it is `f (s i)` followed by the translation of the
`B i`-th cell of `g`, hence `markedPos i` plus the difference of two affine functions. -/
theorem markedImage_gf {d e n : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) {q : PReal d e} {s : Fin (n + 1) → ℝ} (hmono : StrictMono s)
    (hzero : s 0 = 0) (htop : s (Fin.last n) = 1)
    (hreg : q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e) {M : Fin n → ℝ}
    (hM : ∀ i, mkIET1 (simplexMap d q.1) π (simplexMap_mem_simplex_fin hreg.1.1 hreg.1.2)
      (s i.castSucc) = M i)
    {B : Fin n → Fin e} (hB : ∀ i,
      leftEnd (simplexMap e q.2) (B i) ≤ M i ∧
        M i + (s i.succ - s i.castSucc)
          ≤ leftEnd (simplexMap e q.2) (B i) + (simplexMap e q.2 (B i) : ℝ))
    (i : Fin n) :
    mkIET1 (simplexMap e q.2) σ (simplexMap_mem_simplex_fin hreg.2.1 hreg.2.2)
        (mkIET1 (simplexMap d q.1) π (simplexMap_mem_simplex_fin hreg.1.1 hreg.1.2) (s i.castSucc))
      = M i + ((imageLeftAffineRight (d := d) σ (B i) - cutAffineRight (d := d) (B i)) q) := by
  rw [hM i, markedImage_g π σ hmono hzero htop _ _ hM hB i, translationVector]
  have h1 : (imageLeftAffineRight (d := d) σ (B i)) q = imageLeft σ (simplexMap e q.2) (B i) :=
    imageLeftAffineRight_eq σ hreg.2 (B i)
  have h2 : (cutAffineRight (d := d) (B i)) q = leftEnd (simplexMap e q.2) (B i) :=
    cutAffineRight_eq_leftEnd (d := d) hreg.2 (B i)
  have h3 : ((imageLeftAffineRight (d := d) σ (B i) - cutAffineRight (d := d) (B i)) q)
      = (imageLeftAffineRight (d := d) σ (B i)) q - (cutAffineRight (d := d) (B i)) q := rfl
  rw [h3, h1, h2]

/-- **The image starts are the partial sums of the cell lengths**: if `F i q = (g ∘ f) (s i q)` on
the ball and `(g ∘ f)` is a translation on each marked cell, then the left end of the image of the
`i`-th cell is the total length of the cells whose image starts to its left. -/
theorem partialSum_image {d e n : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) {q₀ : PReal d e} {ε : ℝ} {s : Fin (n + 1) → ParamAffine d e}
    (hmono : ∀ q ∈ Metric.ball q₀ ε, StrictMono fun j => s j q)
    (hzero : ∀ q ∈ Metric.ball q₀ ε, (s 0) q = 0)
    (htop : ∀ q ∈ Metric.ball q₀ ε, s (Fin.last n) q = 1)
    {F : Fin n → ParamAffine d e}
    (hF : ∀ q ∈ Metric.ball q₀ ε, ∀ (hl : simplexMap d q.1 ∈ simplex d)
      (hm : simplexMap e q.2 ∈ simplex e), ∀ i : Fin n,
      (mkIET1 (simplexMap e q.2) σ hm * mkIET1 (simplexMap d q.1) π hl) (s i.castSucc q) = F i q)
    (htransl : ∀ q ∈ Metric.ball q₀ ε, ∀ (hl : simplexMap d q.1 ∈ simplex d)
      (hm : simplexMap e q.2 ∈ simplex e), ∀ i : Fin n, ∃ δ : ℝ, ∀ x : ℝ,
      s i.castSucc q ≤ x → x < s i.succ q →
        (mkIET1 (simplexMap e q.2) σ hm * mkIET1 (simplexMap d q.1) π hl) x = x + δ)
    (q : PReal d e) (hq : q ∈ Metric.ball q₀ ε)
    (hl : simplexMap d q.1 ∈ simplex d) (hm : simplexMap e q.2 ∈ simplex e) (i : Fin n) :
    F i q = ∑ j ∈ Finset.univ.filter (fun j : Fin n => F j q < F i q),
      (s j.succ q - s j.castSucc q) := by
  classical
  set h := mkIET1 (simplexMap e q.2) σ hm * mkIET1 (simplexMap d q.1) π hl with hh
  have hν : ∀ j : Fin n, 0 < s j.succ q - s j.castSucc q := fun j =>
    sub_pos.mpr ((hmono q hq) (Fin.castSucc_lt_succ (i := j)))
  have hν' : ∀ j : Fin n, 0 < s j.succ q - s j.castSucc q := hν
  -- `h` maps each cell into `[0, 1)` and is a bijection of `[0, 1)`
  have hmem_map : ∀ x ∈ Set.Ico (0 : ℝ) 1, h x ∈ Set.Ico (0 : ℝ) 1 := fun x hx =>
    h.isIET.mapsTo hx
  have hσinj : Function.Injective h := h.injective
  -- the images are the intervals `Ico (F j q) (F j q + ν j)`
  have himg : ∀ j : Fin n,
      h '' Set.Ico (s j.castSucc q) (s j.succ q)
        = Set.Ico (F j q) (F j q + (s j.succ q - s j.castSucc q)) := by
    intro j
    have hδ := htransl q hq hl hm j
    obtain ⟨δ, hδ⟩ := hδ
    rw [image_Ico_add (hmono q hq (Fin.castSucc_lt_succ (i := j))) (f := h) (δ := δ) hδ]
    have h1 : s j.castSucc q + δ = F j q := by
      rw [← hF q hq hl hm j]
      exact (hδ _ le_rfl (hmono q hq (Fin.castSucc_lt_succ (i := j)))).symm
    rw [h1]
    congr 1
    linarith [h1]
  -- the marked cells tile `[0, 1)`
  have hcover_cell : ∀ y ∈ Set.Ico (0 : ℝ) 1,
      ∃ j : Fin n, y ∈ Set.Ico (s j.castSucc q) (s j.succ q) := by
    intro y hy
    exact exists_cell_of_strictMono (hmono q hq) (hzero q hq) (htop q hq) hy
  -- the images tile `[0, 1)`
  have hdisj : ∀ i j : Fin n, i ≠ j →
      Disjoint (Set.Ico (F i q) (F i q + (s i.succ q - s i.castSucc q)))
        (Set.Ico (F j q) (F j q + (s j.succ q - s j.castSucc q))) := by
    intro i j hij
    rw [← himg i, ← himg j]
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨x, hx, rfl⟩ ⟨x', hx', hxx'⟩
    have h1 : x = x' := hσinj hxx'.symm
    subst h1
    -- the two cells are disjoint half-open intervals
    have hi := hmono q hq (Fin.castSucc_lt_succ (i := i))
    have hj := hmono q hq (Fin.castSucc_lt_succ (i := j))
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hle : s i.succ q ≤ s j.castSucc q := by
        refine (hmono q hq).monotone ?_
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        have := hlt
        omega
      exact absurd hx'.1 (not_le.mpr (lt_of_lt_of_le hx.2 hle))
    · have hle : s j.succ q ≤ s i.castSucc q := by
        refine (hmono q hq).monotone ?_
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        have := hgt
        omega
      exact absurd hx.1 (not_le.mpr (lt_of_lt_of_le hx'.2 hle))
  have hcover : ∀ y ∈ Set.Ico (0 : ℝ) 1,
      ∃ j : Fin n, y ∈ Set.Ico (F j q) (F j q + (s j.succ q - s j.castSucc q)) := by
    intro y hy
    -- a preimage of `y` lies in some cell
    obtain ⟨S, hS⟩ := h.isIET.exists_isCutSet (by norm_num : (0 : ℝ) < 1)
    have hpre : h.symm y ∈ Set.Ico (0 : ℝ) 1 := Equiv.IsIET.symm_mapsTo (e := h.toEquiv) hS hy
    obtain ⟨j, hj⟩ := hcover_cell (h.symm y) hpre
    refine ⟨j, ?_⟩
    rw [← himg j]
    exact ⟨h.symm y, hj, Equiv.apply_symm_apply h.toEquiv y⟩
  -- the marked points lie in `[0, 1)`
  have hlastlt : ∀ j : Fin n, j.castSucc < Fin.last n := by
    intro j
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]
    have := j.isLt
    omega
  have hmemcell : ∀ j : Fin n, s j.castSucc q ∈ Set.Ico (0 : ℝ) 1 := by
    intro j
    exact ⟨by rw [← hzero q hq]; exact (hmono q hq).monotone (Fin.zero_le _),
      by rw [← htop q hq]; exact hmono q hq (hlastlt j)⟩
  -- the bounds
  have h0 : ∀ j : Fin n, 0 ≤ F j q := by
    intro j
    rw [← hF q hq hl hm j]
    exact (hmem_map _ (hmemcell j)).1
  have hF1 : ∀ j : Fin n, F j q < 1 := by
    intro j
    rw [← hF q hq hl hm j]
    exact (hmem_map _ (hmemcell j)).2
  have h1' : ∀ j : Fin n, F j q + (s j.succ q - s j.castSucc q) ≤ 1 := by
    intro j
    have hlt := hmono q hq (Fin.castSucc_lt_succ (i := j))
    by_contra hcon
    rw [not_le] at hcon
    -- a point of the cell whose image is above `1`
    have hx1 : s j.castSucc q
        ≤ s j.succ q - (F j q + (s j.succ q - s j.castSucc q) - 1) / 2 := by
      linarith [hF1 j, hν j]
    have hx2 : s j.succ q - (F j q + (s j.succ q - s j.castSucc q) - 1) / 2 < s j.succ q := by
      have : 0 < (F j q + (s j.succ q - s j.castSucc q) - 1) / 2 := by linarith
      linarith
    obtain ⟨δ, hδ⟩ := htransl q hq hl hm j
    have hval : h (s j.succ q - (F j q + (s j.succ q - s j.castSucc q) - 1) / 2)
        = 1 + (F j q + (s j.succ q - s j.castSucc q) - 1) / 2 := by
      rw [hδ _ hx1 hx2]
      have hfoot : s j.castSucc q + δ = F j q := by
        rw [← hF q hq hl hm j]
        exact (hδ _ le_rfl hlt).symm
      linarith
    have hsj1 : s j.succ q ≤ 1 := by
      rw [← htop q hq]
      exact (hmono q hq).monotone (by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_last]; have := j.isLt; omega)
    have hmem := hmem_map _ (show s j.succ q - (F j q + (s j.succ q - s j.castSucc q) - 1) / 2
      ∈ Set.Ico (0 : ℝ) 1 from ⟨by linarith [(hmemcell j).1, hF1 j], by linarith [hsj1, hcon]⟩)
    rw [hval] at hmem
    linarith [hmem.2]
  exact sum_len_eq_of_tiling hν' h0 h1' hdisj hcover i

/-- **The cell starts are the partial sums of the cell lengths.** -/
theorem partialSum_cell {d e n : ℕ} {q₀ : PReal d e} {ε : ℝ}
    {s : Fin (n + 1) → ParamAffine d e}
    (hmono : ∀ q ∈ Metric.ball q₀ ε, StrictMono fun j => s j q)
    (hzero : ∀ q ∈ Metric.ball q₀ ε, (s 0) q = 0)
    (htop : ∀ q ∈ Metric.ball q₀ ε, s (Fin.last n) q = 1)
    (q : PReal d e) (hq : q ∈ Metric.ball q₀ ε) (i : Fin n) :
    s i.castSucc q = ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i),
      (s j.succ q - s j.castSucc q) := by
  classical
  have hν : ∀ j : Fin n, 0 < s j.succ q - s j.castSucc q := fun j =>
    sub_pos.mpr ((hmono q hq) (Fin.castSucc_lt_succ (i := j)))
  have h0 : ∀ j : Fin n, 0 ≤ s j.castSucc q := fun j => by
    rw [← hzero q hq]
    exact (hmono q hq).monotone (Fin.zero_le _)
  have hlast_le : ∀ j : Fin n, j.succ ≤ Fin.last n := by
    intro j
    simp only [Fin.le_def, Fin.val_succ, Fin.val_last]
    have := j.isLt
    omega
  have h1 : ∀ j : Fin n, s j.castSucc q + (s j.succ q - s j.castSucc q) ≤ 1 := by
    intro j
    rw [← htop q hq]
    have h := (hmono q hq).monotone (hlast_le j)
    linarith
  have hdisj : ∀ i j : Fin n, i ≠ j →
      Disjoint (Set.Ico (s i.castSucc q) (s i.castSucc q + (s i.succ q - s i.castSucc q)))
        (Set.Ico (s j.castSucc q) (s j.castSucc q + (s j.succ q - s j.castSucc q))) := by
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨hy1, hy2⟩ ⟨hy1', hy2'⟩
    rcases lt_or_gt_of_ne (Ne.symm hij) with hlt | hlt
    · -- `j < i`: the `i`-th cell starts at or after the end of the `j`-th
      have hle : s j.succ q ≤ s i.castSucc q := by
        refine (hmono q hq).monotone ?_
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        omega
      linarith
    · have hle : s i.succ q ≤ s j.castSucc q := by
        refine (hmono q hq).monotone ?_
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        omega
      linarith
  have hcover : ∀ y ∈ Set.Ico (0 : ℝ) 1, ∃ j : Fin n,
      y ∈ Set.Ico (s j.castSucc q) (s j.castSucc q + (s j.succ q - s j.castSucc q)) := by
    intro y hy
    obtain ⟨j, hj⟩ := exists_cell_of_strictMono (hmono q hq) (hzero q hq) (htop q hq) hy
    exact ⟨j, hj.1, by linarith [hj.2]⟩
  have hmain := sum_len_eq_of_tiling hν h0 h1 hdisj hcover i
  rwa [Finset.filter_congr (fun j _ => (hmono q hq).lt_iff_lt)] at hmain

/-- **The presentation is locally constant.**  Near any good parameter pair inside the open simplex
region there is a ball on which *one* fixed list `s` of affine functions and *one* fixed permutation
`ρ` present `g ∘ f`, with a fixed combinatorial type `a`, `B`.

This is the paper's "the map `gf` is an interval exchange transformation with respect to a
permutation `ρ` which does not depend on the parameters in `O`", in **local** form.  The pattern of
the singularities is determined by finitely many strict inequalities between affine functions of the
parameters (the order of the singularities of `f` and of `f⁻¹S_g`, which cell of `f` contains each
`f⁻¹` of a singularity of `g`, and which cell of `g` contains each image); each of those conditions
is open in the parameters.  So only *openness* is needed, and no connectedness or preconnectedness
hypothesis appears — this is why the local form is the right statement.

The ball also carries the two openness conditions on the ambient data: it lies in `goodParams`
(`isOpen_goodParams`) and inside the open simplex region (the coordinates of `f` and `g` are
positive there, so `simplexMap` really is the free-coordinate map and no length vanishes). -/
theorem exists_compPresentation_on_ball {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) (q₀ : PReal d e)
    (hq₀ : q₀ ∈ goodParams d e) (hr₀ : q₀.1 ∈ simplexRegion d ∧ q₀.2 ∈ simplexRegion e) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball q₀ ε ⊆ goodParams d e ∧
      (∀ q ∈ Metric.ball q₀ ε, q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e) ∧
        ∃ (n : ℕ) (s : Fin (n + 1) → ParamAffine d e) (ρ : Equiv.Perm (Fin n))
          (a : Fin (d + 1) → Fin (n + 1)) (B : Fin n → Fin e),
          ∃ (_shape : SingularityShape (d := d) (e := e) n π s (Metric.ball q₀ ε)),
          n = d + e - 1 ∧
            ∀ q ∈ Metric.ball q₀ ε,
              ∀ (hl : simplexMap d q.1 ∈ simplex d) (hm : simplexMap e q.2 ∈ simplex e),
                IsCompPresentation (simplexMap d q.1) π (simplexMap e q.2) σ hl hm n
                    (fun k => s k q) ρ ∧
                  IsCompType (simplexMap d q.1) π hl (simplexMap e q.2) (fun k => s k q) a B := by
  classical
  obtain ⟨k, ε₁, hε₁, hgood₁, hreg₁, hineq₁, hinv₁⟩ := exists_ball_forall_imageLeft_lt π hq₀ hr₀
  have hn : 1 ≤ d + e - 1 := by
    have hd := NeZero.pos d
    have he := NeZero.pos e
    omega
  obtain ⟨τ, A, ε, hε, hgood, hreg, hmono, hzero, htop, hcut, hpre, hA⟩ :=
    exists_markedList π hq₀ hr₀ hn hε₁ hgood₁ hreg₁ hineq₁ hinv₁
  obtain ⟨B, hB⟩ := exists_compImage_on_ball π k τ hA hε hreg hmono hzero htop hcut hpre
  -- the affine function `(g ∘ f) (s i)`
  set Ggf : Fin (d + e - 1) → ParamAffine d e := fun i =>
    markedPos π τ i + (imageLeftAffineRight (d := d) σ (B i) - cutAffineRight (d := d) (B i))
    with hGgfdef
  have hGgf : ∀ (q : PReal d e), q ∈ Metric.ball q₀ ε →
      ∀ (hl : simplexMap d q.1 ∈ simplex d) (hm : simplexMap e q.2 ∈ simplex e)
        (i : Fin (d + e - 1)),
      (mkIET1 (simplexMap e q.2) σ hm * mkIET1 (simplexMap d q.1) π hl)
        (withEnds hn A i.castSucc q) = Ggf i q := by
    intro q hq hl hm i
    have hM : ∀ i : Fin (d + e - 1),
        mkIET1 (simplexMap d q.1) π hl (withEnds hn A i.castSucc q) = markedPos (e := e) π τ i q :=
      fun i => markedPos_spec (hn := hn) (A := A) (q := q) π k τ hA (hreg q hq)
        (hzero q hq) (fun i => hcut q hq i) (fun j' => hpre q hq j' hl) i
    have hB' : ∀ i : Fin (d + e - 1),
        leftEnd (simplexMap e q.2) (B i) ≤ markedPos (e := e) π τ i q ∧
          markedPos (e := e) π τ i q
              + (withEnds hn A i.succ q - withEnds hn A i.castSucc q)
            ≤ leftEnd (simplexMap e q.2) (B i) + (simplexMap e q.2 (B i) : ℝ) := by
      intro i
      have h := hB q hq hl i
      rw [hM i] at h
      exact h
    have hres := markedImage_gf (M := fun i => markedPos (e := e) π τ i q) π σ
      (hmono q hq) (hzero q hq) (htop q hq) (hreg q hq) hM hB' i
    rw [IET.mul_apply, hres, hGgfdef]
    rfl
  -- the order of the images is fixed on the ball
  have hne : ∀ (i j : Fin (d + e - 1)), i ≠ j → ∀ q ∈ Metric.ball q₀ ε,
      Ggf i q ≠ Ggf j q := by
    intro i j hij q hq hcon
    have hl : simplexMap d q.1 ∈ simplex d :=
      simplexMap_mem_simplex_fin (hreg q hq).1.1 (hreg q hq).1.2
    have hm : simplexMap e q.2 ∈ simplex e :=
      simplexMap_mem_simplex_fin (hreg q hq).2.1 (hreg q hq).2.2
    rw [← hGgf q hq hl hm i, ← hGgf q hq hl hm j] at hcon
    have h1 : withEnds hn A i.castSucc q = withEnds hn A j.castSucc q :=
      (mkIET1 (simplexMap e q.2) σ hm * mkIET1 (simplexMap d q.1) π hl).injective hcon
    have h2 : i.castSucc = j.castSucc := (hmono q hq).injective h1
    exact hij (Fin.ext (by simpa using congrArg Fin.val h2))
  obtain ⟨ρ, hρ⟩ := exists_rank_perm Ggf hε hne
  -- the explicit shape of the singularity list: `posF`/`posG` are the positions of the cuts of `f`
  -- and of the preimages of the cuts of `g`
  have hshape : SingularityShape (d := d) (e := e) (d + e - 1) π (withEnds hn A)
      (Metric.ball q₀ ε) := by
    refine
      { cellIdx := k
        posF := fun i => ⟨(τ.symm (Sum.inl i)).val + 1, by
          have := (τ.symm (Sum.inl i)).isLt; omega⟩
        posG := fun j => ⟨(τ.symm (Sum.inr j)).val + 1, by
          have := (τ.symm (Sum.inr j)).isLt; omega⟩
        posF_inj := ?_
        posG_inj := ?_
        posF_ne_posG := ?_
        posF_ne_zero := ?_
        posF_ne_last := ?_
        posG_ne_zero := ?_
        posG_ne_last := ?_
        posF_spec := ?_
        posG_spec := ?_
        posG_pre := ?_ }
    · intro i i' h
      have h1 : (τ.symm (Sum.inl i)).val + 1 = (τ.symm (Sum.inl i')).val + 1 :=
        congrArg Fin.val h
      have h2 : τ.symm (Sum.inl i) = τ.symm (Sum.inl i') := Fin.ext (by omega)
      exact Sum.inl.inj (τ.symm.injective h2)
    · intro j j' h
      have h1 : (τ.symm (Sum.inr j)).val + 1 = (τ.symm (Sum.inr j')).val + 1 :=
        congrArg Fin.val h
      have h2 : τ.symm (Sum.inr j) = τ.symm (Sum.inr j') := Fin.ext (by omega)
      exact Sum.inr.inj (τ.symm.injective h2)
    · intro i j h
      have h1 : (τ.symm (Sum.inl i)).val + 1 = (τ.symm (Sum.inr j)).val + 1 :=
        congrArg Fin.val h
      have h2 : τ.symm (Sum.inl i) = τ.symm (Sum.inr j) := Fin.ext (by omega)
      exact absurd (τ.symm.injective h2) (by simp)
    · intro i h
      have h1 : (τ.symm (Sum.inl i)).val + 1 = 0 := congrArg Fin.val h
      omega
    · intro i h
      have h1 : (τ.symm (Sum.inl i)).val + 1 = d + e - 1 := congrArg Fin.val h
      have h2 := (τ.symm (Sum.inl i)).isLt
      omega
    · intro j h
      have h1 : (τ.symm (Sum.inr j)).val + 1 = 0 := congrArg Fin.val h
      omega
    · intro j h
      have h1 : (τ.symm (Sum.inr j)).val + 1 = d + e - 1 := congrArg Fin.val h
      have h2 := (τ.symm (Sum.inr j)).isLt
      omega
    · intro q _ i
      have h := withEnds_mid hn A (τ.symm (Sum.inl i))
      have h2 : A (τ.symm (Sum.inl i)) = cutAffine (e := e) ⟨i.val + 1, by
        have := i.isLt; omega⟩ := by
        rw [hA, Equiv.apply_symm_apply]
        rfl
      conv_lhs => rw [show (⟨(τ.symm (Sum.inl i)).val + 1, _⟩ : Fin (d + e - 1 + 1))
        = _ from Fin.ext rfl]
      rw [h, h2]
    · intro q _ j
      have h := withEnds_mid hn A (τ.symm (Sum.inr j))
      have h2 : A (τ.symm (Sum.inr j)) = preimageCutAffine π ⟨j.val + 1, by
        have := j.isLt; omega⟩ (k j) := by
        rw [hA, Equiv.apply_symm_apply]
        rfl
      conv_lhs => rw [show (⟨(τ.symm (Sum.inr j)).val + 1, _⟩ : Fin (d + e - 1 + 1))
        = _ from Fin.ext rfl]
      rw [h, h2]
    · intro q hq j hl
      exact hpre q hq j hl
  refine ⟨ε, hε, hgood, hreg, d + e - 1, withEnds hn A, ρ, compTypeA τ, B, hshape, rfl, ?_⟩
  intro q hq hl hm
  refine ⟨⟨hzero q hq, htop q hq, hmono q hq, ?_, ?_, ?_, rfl⟩,
    compTypeA_last τ, ?_, ?_⟩
  · -- `cell`
    intro i x hx1 hx2
    have hfl := markedCell_transl π (hreg q hq).1 hl (hmono q hq) (hzero q hq) (htop q hq)
      (fun i => hcut q hq i) i
    obtain ⟨δf, hδf⟩ := hfl
    obtain ⟨δg, hδg⟩ := markedCell_g_transl π σ (hreg q hq).1 (hreg q hq).2 hl hm
      (hmono q hq) (hzero q hq) (htop q hq) (fun i => hcut q hq i)
      (fun j' => hpre q hq j' hl) i
    have hν : withEnds hn A i.castSucc q < withEnds hn A i.succ q :=
      hmono q hq (Fin.castSucc_lt_succ (i := i))
    have h0 : (mkIET1 (simplexMap e q.2) σ hm * mkIET1 (simplexMap d q.1) π hl)
        (withEnds hn A i.castSucc q) = withEnds hn A i.castSucc q + (δf + δg) := by
      rw [IET.mul_apply, hδg _ le_rfl hν, hδf _ le_rfl hν]
      ring
    have hx : (mkIET1 (simplexMap e q.2) σ hm * mkIET1 (simplexMap d q.1) π hl) x
        = x + (δf + δg) := by
      rw [IET.mul_apply, hδg x hx1 hx2, hδf x hx1 hx2]
      ring
    -- the displacement is `Ggf i q - s i q`
    have hdisp : δf + δg = Ggf i q - withEnds hn A i.castSucc q := by
      have h := hGgf q hq hl hm i
      linarith [h0, h]
    rw [hx, hdisp]
    -- the two partial-sum identities
    have hsumI : Ggf i q = ∑ j ∈ Finset.univ.filter
        (fun j : Fin (d + e - 1) => Ggf j q < Ggf i q),
        (withEnds hn A j.succ q - withEnds hn A j.castSucc q) :=
      partialSum_image π σ (hmono) (hzero) (htop) (hGgf) (fun q hq hl hm i => by
        obtain ⟨δf, hδf⟩ := markedCell_transl π (hreg q hq).1 hl (hmono q hq) (hzero q hq)
          (htop q hq) (fun i => hcut q hq i) i
        obtain ⟨δg, hδg⟩ := markedCell_g_transl π σ (hreg q hq).1 (hreg q hq).2 hl hm
          (hmono q hq) (hzero q hq) (htop q hq) (fun i => hcut q hq i)
          (fun j' => hpre q hq j' hl) i
        exact ⟨δf + δg, fun x hx1 hx2 => by
          rw [IET.mul_apply, hδg x hx1 hx2, hδf x hx1 hx2]; ring⟩) q hq hl hm i
    have hsumC : withEnds hn A i.castSucc q = ∑ j ∈ Finset.univ.filter
        (fun j : Fin (d + e - 1) => j < i),
        (withEnds hn A j.succ q - withEnds hn A j.castSucc q) :=
      partialSum_cell hmono hzero htop q hq i
    have hfilt : Finset.univ.filter (fun j : Fin (d + e - 1) => ρ j < ρ i)
        = Finset.univ.filter (fun j : Fin (d + e - 1) => Ggf j q < Ggf i q) :=
      Finset.filter_congr (fun j _ => hρ q hq j i)
    have hLI : listImageLeft ρ (fun k => withEnds hn A k q) i = Ggf i q := by
      rw [listImageLeft, hfilt, ← hsumI]
    have hLE : listLeftEnd (fun k => withEnds hn A k q) i = withEnds hn A i.castSucc q := by
      rw [listLeftEnd, ← hsumC]
    rw [hLI, hLE]
  · -- `f_transl`
    intro i
    exact markedCell_transl π (hreg q hq).1 hl (hmono q hq) (hzero q hq) (htop q hq)
      (fun i => hcut q hq i) i
  · -- `g_transl`
    intro i
    exact markedCell_g_transl π σ (hreg q hq).1 (hreg q hq).2 hl hm
      (hmono q hq) (hzero q hq) (htop q hq) (fun i => hcut q hq i)
      (fun j' => hpre q hq j' hl) i
  · -- `IsCompType.cut`
    exact compTypeA_cut (τ := τ) (lam := simplexMap d q.1)
      (s := fun k => withEnds hn A k q) (hzero q hq) (fun i => hcut q hq i)
  · -- `IsCompType.image`
    exact fun k => hB q hq hl k

/-- **A good region around a parameter pair**: an open set containing `p₀` on which the
singularities of `g ∘ f` are one fixed list `s` of affine functions and its permutation `ρ` is
fixed.  This is the paper's "the pattern of pair-splitting singularities is constant over `O`", made
local at `p₀`.

It is the datum Section 3 runs on, and the reason the almost-sure statement has to produce the
region rather than merely an `s` at each point: Masur–Veech and Veech's rigidity are statements
about `mkIET1 ν ρ` for a *fixed* `ρ` and for a.e. `ν`, so the transfer of Lemma 3.1 fixes one `ρ`
and one simplex `Δ_ρ`, and the parameters for which that `ρ` is the permutation of `g ∘ f` have to
be known to form a neighbourhood of the point in question. -/
structure GoodRegion (d e : ℕ) [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) (q₀ : PReal d e) where
  /-- the region itself: a set of free parameters -/
  O : Set (PReal d e)
  isOpen_O : IsOpen O
  mem_O : q₀ ∈ O
  /-- the region lies in `goodParams`: no small integer relation vanishes on it -/
  subset_good : O ⊆ goodParams d e
  /-- the region lies in the **open** simplex region: the free coordinates of `f` and of `g` are
  positive there, so `simplexMap` is the free-coordinate map and no length of a cell vanishes -/
  subset_region : ∀ q ∈ O, q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e
  /-- the number of cells of `g ∘ f`, namely `d + e - 1` -/
  n : ℕ
  /-- the singularity list of `g ∘ f`, as affine functions of the free parameters -/
  s : Fin (n + 1) → ParamAffine d e
  /-- the permutation of `g ∘ f`, fixed on the region -/
  ρ : Equiv.Perm (Fin n)
  /-- the marked indices of the cuts of `f` -/
  a : Fin (d + 1) → Fin (n + 1)
  /-- the cell of `g` containing the image of each marked cell -/
  B : Fin n → Fin e
  /-- **the composition is presented by `s` and `ρ` at every point of the region**; the two simplex
  memberships are derived from `subset_region` rather than carried -/
  pres : ∀ (q) (hq : q ∈ O),
    IsCompPresentation (simplexMap d q.1) π (simplexMap e q.2) σ
      (simplexMap_mem_simplex_fin (subset_region q hq).1.1 (subset_region q hq).1.2)
      (simplexMap_mem_simplex_fin (subset_region q hq).2.1 (subset_region q hq).2.2)
      n (fun k => s k q) ρ
  /-- the combinatorial type is the same throughout the region -/
  type : ∀ (q) (hq : q ∈ O),
    IsCompType (simplexMap d q.1) π
      (simplexMap_mem_simplex_fin (subset_region q hq).1.1 (subset_region q hq).1.2)
      (simplexMap e q.2) (fun k => s k q) a B
  /-- **which singularity each entry of the list is**, explicitly: a cut of `f` or the preimage of a
  cut of `g` -/
  shape : SingularityShape n π s O

/-! ### The simplex memberships at a point of the region

The two proofs that `simplexMap d q.1` and `simplexMap e q.2` lie in the simplexes are determined by
`G.subset_region`, so they are derived rather than carried: the fields `G.pres` and `G.type` build
them from it, and these two lemmas give them their own names. -/

/-- `simplexMap d q.1` is in the simplex at a point of the region. -/
theorem GoodRegion.simplexMap_mem_simplex_fst {d e : ℕ} [NeZero d] [NeZero e]
    {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)} {q₀ : PReal d e}
    (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O) :
    simplexMap d q.1 ∈ simplex d :=
  simplexMap_mem_simplex_fin (G.subset_region q hq).1.1 (G.subset_region q hq).1.2

/-- `simplexMap e q.2` is in the simplex at a point of the region. -/
theorem GoodRegion.simplexMap_mem_simplex_snd {d e : ℕ} [NeZero d] [NeZero e]
    {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)} {q₀ : PReal d e}
    (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O) :
    simplexMap e q.2 ∈ simplex e :=
  simplexMap_mem_simplex_fin (G.subset_region q hq).2.1 (G.subset_region q hq).2.2

/-! ### Blocks of cells, and the data that fit a point of the region

Every block statement of Section 3 quantifies over the same tuple: two indices `k < l ≤ G.n` and the
invariance of the initial segments `{i | i < k}` and `{i | i < l}` under the permutation `ρ` of the
presentation.  The indices alone are `BlockIdx n` (in `IET.lean`, which also derives
`NeZero (l - k)`), and the two together are `Block`.  Likewise a statement about a pair of data `D`,
`E` always carries `D.π = π`, `D.v = q.1`, `E.π = σ`, `E.v = q.2`; that is the structure `Fits`. -/

namespace GoodRegion

/-- **A block of cells** of the composition: the indices of a block of its `G.n` cells (`BlockIdx`,
which also carries `NeZero (l - k)`), together with the invariance of the initial segments
`{i | i < k}` and `{i | i < l}` under `ρ`. -/
structure Block {d e : ℕ} [NeZero d] [NeZero e] {π : Equiv.Perm (Fin d)}
    {σ : Equiv.Perm (Fin e)} {q₀ : PReal d e} (G : GoodRegion d e π σ q₀)
    extends BlockIdx G.n where
  hstab : ∀ i : Fin G.n,
    (i.val < toBlockIdx.k ↔ (G.ρ i).val < toBlockIdx.k) ∧
      (i.val < toBlockIdx.l ↔ (G.ρ i).val < toBlockIdx.l)

namespace Block

variable {d e : ℕ} [NeZero d] [NeZero e] {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
  {q₀ : PReal d e} (G : GoodRegion d e π σ q₀)

/-- There are only countably many blocks: the two indices determine the block, since the invariance
and the index bounds are propositions.  This is what turns "every block" into a countable
intersection of almost-sure statements. -/
instance countable : Countable (Block G) :=
  Function.Injective.countable (f := fun B : Block G => (B.k, B.l)) (by
    rintro ⟨⟨k, l, hkl, hln⟩, hs⟩ ⟨⟨k', l', hkl', hln'⟩, hs'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl)

end Block

/-- **The data fit the parameters of the region**: the two data whose composition is `g ∘ f` have
the lengths and the permutations of the region at the point `q`. -/
structure Fits {d e : ℕ} [NeZero d] [NeZero e] {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
    {q₀ : PReal d e} (G : GoodRegion d e π σ q₀) (q : PReal d e) (D : IETDatum d)
    (E : IETDatum e) : Prop where
  hDπ : D.π = π
  hDv : D.v = q.1
  hEπ : E.π = σ
  hEv : E.v = q.2

end GoodRegion

/-- **A good region around any good point of the open simplex region**, from the local form of the
presentation.  No preconnectedness argument is needed any more: the region is the ball produced by
`exists_compPresentation_on_ball`. -/
theorem exists_goodRegion {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) (q₀ : PReal d e)
    (hq₀ : q₀ ∈ goodParams d e) (hr₀ : q₀.1 ∈ simplexRegion d ∧ q₀.2 ∈ simplexRegion e) :
    Nonempty (GoodRegion d e π σ q₀) := by
  obtain ⟨ε, hε, hball, hreg, n, s, ρ, a, B, hshape, _hcard, hpres⟩ :=
    exists_compPresentation_on_ball π σ q₀ hq₀ hr₀
  exact ⟨Metric.ball q₀ ε, Metric.isOpen_ball, Metric.mem_ball_self hε, hball, hreg, n, s, ρ, a, B,
    (fun q hq => (hpres q hq
      (simplexMap_mem_simplex_fin (hreg q hq).1.1 (hreg q hq).1.2)
      (simplexMap_mem_simplex_fin (hreg q hq).2.1 (hreg q hq).2.2)).1),
    (fun q hq => (hpres q hq
      (simplexMap_mem_simplex_fin (hreg q hq).1.1 (hreg q hq).1.2)
      (simplexMap_mem_simplex_fin (hreg q hq).2.1 (hreg q hq).2.2)).2), hshape⟩

/-- **Almost every parameter pair has a good region** — the corollary of `ae_goodParams` that
Section 3 runs on.  Almost every point of the product of the two open simplexes is good, and
`exists_goodRegion` then produces the ball around it. -/
theorem ae_exists_goodRegion {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) :
    ∀ᵐ q ∂((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))),
      Nonempty (GoodRegion d e π σ q) := by
  filter_upwards [ae_goodParams_real (d := d) (e := e),
    ae_mem_simplexRegion_prod (d := d) (e := e)] with q hq hreg
  exact exists_goodRegion π σ q hq hreg
