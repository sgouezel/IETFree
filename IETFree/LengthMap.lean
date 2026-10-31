/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.GoodRegion

/-!
Lemma 3.1: the length vector of `g ∘ f` determines the parameters; the affine length map.

The paper's Lemma 3.1 says that the map `L_O` associating to `(λ, μ)` the interval lengths of
`g ∘ f` is an invertible affine map from `O` to `Δ_ρ`.  Here `O` is a set of free parameters and
the singularity list is a family of affine maps, so `compLenAffine G.s` — the first `n - 1`
lengths as functions of the parameters — is affine as a whole.  The file splits it into

* `compLen_injective`: on the region the length vector determines `(λ, μ)` — each `λᵢ` and each `μⱼ`
  is a sum of lengths of marked cells (`IsCompPresentation.lam_eq_sum`, `.mu_eq_sum`);
* the pointwise description of that affine map: `monoAt` (the list is strictly increasing at a point
  of the region) and `compLenAffine_mem_regionAt` (its image lies in the open simplex there);
* `injective_linear_of_injOn`, the general tool by which an affine map injective on an open set
  gives an absolutely continuous pushforward.

The length vector is only ever used at a single point (`compLenVec s q (monoAt G hq)`, abbreviated
`G.cellLen hq`), because a global monotonicity hypothesis on the list is not derivable from the data
of a `GoodRegion`; the absolute continuity of the pushforward is therefore proved pointwise, in
`compLenAffine_absolutelyContinuousAt`/`compLen_absolutelyContinuousAt`, in `IETFree.BlockData`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-! ## 3. Lemma 3.1, reshaped

The paper's Lemma 3.1 is "the map `L_O` associating to `(λ, μ)` the interval lengths of `gf` is an
invertible affine map" from `O` to `Δ_ρ`.  Here `O` is a set of **free parameters**
(`PReal d e`) and the singularity list is a family of affine maps
`ParamAffine d e = PReal d e →ᵃ[ℝ] ℝ`, so the affine length map
`compLenAffine s : PReal d e →ᵃ[ℝ] (Fin (n - 1) → ℝ)` is affine as a whole.  Section 3 uses it
in three separable parts:

* affineness of each `ν i` — true by construction once the presentation is fixed on a region, so
  its content sits in `exists_compPresentation_on_ball` (in `IETFree.GoodRegion`);
* injectivity — `ν` determines `(λ, μ)` on the region (each `λᵢ` and each `μⱼ` is a sum of lengths
  of cells of `g ∘ f`): `compLen_injective`;
* absolute continuity of the pushforward — injectivity together with
  `injective_linear_of_injOn`; the pointwise forms
  `compLenAffine_absolutelyContinuousAt`/`compLen_absolutelyContinuousAt` are what the reduction
  consumes, and they live in `IETFree.BlockData`. -/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-- **Telescoping along consecutive indices.** -/
theorem sum_Ico_succ_sub (S : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) :
    ∑ k ∈ Finset.Ico A B, (S (k + 1) - S k) = S B - S A := by
  rw [Finset.sum_Ico_eq_sub (fun k => S (k + 1) - S k) hAB,
    Finset.sum_range_sub S B, Finset.sum_range_sub S A]
  ring

/-- The `ℕ`-indexed extension of a list on `Fin (n+1)`, constant above `n`. -/
noncomputable def markExt {n : ℕ} (s : Fin (n + 1) → ℝ) (m : ℕ) : ℝ :=
  s ⟨min m n, by have := Nat.min_le_right m n; omega⟩

theorem markExt_of_le {n : ℕ} (s : Fin (n + 1) → ℝ) {m : ℕ} (hm : m ≤ n) :
    markExt s m = s ⟨m, by omega⟩ := by
  simp only [markExt, Nat.min_eq_left hm]

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-- **A strictly increasing list is determined by its increments and its first term.**  Two lists
`s, t : Fin (n+1) → ℝ` with `s 0 = t 0` and equal increments `s (i+1) - s i = t (i+1) - t i` are
equal: the difference `s k - t k` is constant in `k`. -/
theorem eq_of_increments_eq {n : ℕ} {s t : Fin (n + 1) → ℝ} (hs0 : s 0 = t 0)
    (h : ∀ i : Fin n, s i.succ - s i.castSucc = t i.succ - t i.castSucc) : s = t := by
  funext k
  have key : ∀ m : ℕ, ∀ hm : m ≤ n, s ⟨m, by omega⟩ - t ⟨m, by omega⟩ = 0 := by
    intro m
    induction m with
    | zero => intro _; simp [hs0]
    | succ m ih =>
      intro hm
      have hm' : m ≤ n := by omega
      have hstep := h ⟨m, by omega⟩
      have hprev := ih hm'
      have e1 : ((⟨m, by omega⟩ : Fin n).succ) = (⟨m + 1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
      have e2 : ((⟨m, by omega⟩ : Fin n).castSucc) = (⟨m, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
      rw [e1, e2] at hstep
      linarith
  have := key k.val (by have := k.isLt; omega)
  simp only [Fin.eta, sub_eq_zero] at this
  exact this

/-! ### The lengths of `f` and `g` as sums of marked lengths

Two block-sum formulas, one for each factor.  The `i`-th cell of `f` is the union of the marked
cells with indices `a i.castSucc, …, a i.succ - 1` — a *consecutive* block, so `λᵢ` is the sum of
their lengths by telescoping.  The `j`-th cell of `g` is the union of the marked cells whose image
lies in it, i.e. of those with `B k = j` — a *scattered* block, so its length needs a measure
argument rather than telescoping.  Together they say that the marked length vector `ν` determines
`(λ, μ)` at a single parameter, which is the content of Lemma 3.1's injectivity. -/

/-- **The cells of an arrangement are disjoint**: two `Ico`-intervals with left ends `leftEnd` are
disjoint, since the cells of `f` are separated by its cuts. -/
theorem disjoint_leftEnd_Ico {m : ℕ} (lam : Fin m → ℝ≥0) {i j : Fin m} (h : i ≠ j) :
    Disjoint (Set.Ico (leftEnd lam i) (leftEnd lam i + (lam i : ℝ)))
      (Set.Ico (leftEnd lam j) (leftEnd lam j + (lam j : ℝ))) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have h1 : leftEnd lam i + (lam i : ℝ) ≤ leftEnd lam j := by
      rw [← upperEnd_eq]; exact upperEnd_le_leftEnd lam hlt
    linarith [hx.2, hx'.1]
  · have h1 : leftEnd lam j + (lam j : ℝ) ≤ leftEnd lam i := by
      rw [← upperEnd_eq]; exact upperEnd_le_leftEnd lam hlt
    linarith [hx'.2, hx.1]

/-- A cell of an arrangement whose lengths sum to `1` lies in `[0, 1)`. -/
theorem leftEnd_Ico_subset {m : ℕ} (lam : Fin m → ℝ≥0) (h : ∑ i, (lam i : ℝ) = 1)
    (j : Fin m) :
    Set.Ico (leftEnd lam j) (leftEnd lam j + (lam j : ℝ)) ⊆ Set.Ico (0 : ℝ) 1 := by
  intro x hx
  refine ⟨(leftEnd_nonneg lam j).trans hx.1, ?_⟩
  rw [← upperEnd_eq] at hx
  exact hx.2.trans_le ((upperEnd_le_total lam j).trans_eq h)

/-- The volume of a cell is its length. -/
theorem volume_leftEnd_Ico {m : ℕ} (lam : Fin m → ℝ≥0) (j : Fin m) :
    volume (Set.Ico (leftEnd lam j) (leftEnd lam j + (lam j : ℝ))) = ENNReal.ofReal (lam j) := by
  rw [Real.volume_Ico, add_sub_cancel_left]

/-- **The block-sum formula for `f`**: the length of the `i`-th cell of `f` is the total length of
the marked cells it contains.  Telescoping along the consecutive block `[a i.castSucc, a i.succ)`,
whose endpoints `s (a i.castSucc)` and `s (a i.succ)` are the two ends of the cell. -/
theorem IsCompPresentation.lam_eq_sum {d e n : ℕ} [NeZero d] [NeZero e]
    {lam : Fin d → ℝ≥0} {π : Equiv.Perm (Fin d)} {mu : Fin e → ℝ≥0} {σ : Equiv.Perm (Fin e)}
    {hl : (∑ i, lam i) = 1} {hm : (∑ j, mu j) = 1} {s : Fin (n + 1) → ℝ}
    {ρ : Equiv.Perm (Fin n)} {a : Fin (d + 1) → Fin (n + 1)} {B : Fin n → Fin e}
    (P : IsCompPresentation lam π mu σ hl hm n s ρ)
    (T : IsCompType lam π hl mu s a B) (i : Fin d) :
    (lam i : ℝ) = ∑ k ∈ Finset.Ico (a i.castSucc).val (a i.succ).val,
      (markExt s (k + 1) - markExt s k) := by
  have htop := T.top
  have hval := T.cut
  -- the value of `s` at the top of the `i`-th cell
  have hsucc : s (a i.succ) = upperEnd lam i := by
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt i.isLt) with hlt | heq
    · have hcast : i.succ = (⟨i.val + 1, hlt⟩ : Fin d).castSucc := Fin.ext rfl
      rw [hcast, hval ⟨i.val + 1, hlt⟩, leftEnd_eq_upperEnd_of_succ lam hlt]
    · have hlast : i.succ = Fin.last d := Fin.ext heq
      have h1 : (∑ j, (lam j : ℝ)) = 1 := by rw [← NNReal.coe_sum, hl]; norm_num
      rw [hlast, htop, P.top, upperEnd_of_max lam (fun j => by
        rw [Fin.le_def]
        have := j.isLt
        omega), h1]
  have hleft : s (a i.castSucc) = leftEnd lam i := hval i
  have hAB : (a i.castSucc).val ≤ (a i.succ).val := by
    have hle : s (a i.castSucc) ≤ s (a i.succ) := by
      rw [hleft, hsucc, upperEnd_eq]
      linarith [(lam i).coe_nonneg]
    exact Fin.le_def.mp (P.mono.le_iff_le.mp hle)
  rw [sum_Ico_succ_sub (markExt s) hAB, markExt_of_le s (Nat.lt_succ_iff.mp (a i.succ).isLt),
    markExt_of_le s (Nat.lt_succ_iff.mp (a i.castSucc).isLt)]
  have e1 : s ⟨(a i.succ).val, by omega⟩ = upperEnd lam i := by
    rw [show (⟨(a i.succ).val, by omega⟩ : Fin (n + 1)) = a i.succ from Fin.ext rfl]
    exact hsucc
  have e2 : s ⟨(a i.castSucc).val, by omega⟩ = leftEnd lam i := by
    rw [show (⟨(a i.castSucc).val, by omega⟩ : Fin (n + 1)) = a i.castSucc from Fin.ext rfl]
    exact hleft
  rw [e1, e2, upperEnd_eq]
  ring

/-- **The block-sum formula for `g`**: the length of the `j`-th cell of `g` is the total length of
the marked cells whose image lies in it.

The block is scattered, so there is no telescoping: instead, `f` preserves Lebesgue measure, the
cell of `g` is `Ico (leftEnd mu j) (leftEnd mu j + mu j)`, and its preimage under `f` is exactly
the union of the marked cells with `B k = j` — the two-sided interval condition in `IsCompType`
placed each marked cell's image inside the `B k`-th cell of `g`, and the cells of `g` are disjoint.
Comparing volumes gives the two sums of lengths. -/
theorem IsCompPresentation.mu_eq_sum {d e n : ℕ} [NeZero d] [NeZero e]
    {lam : Fin d → ℝ≥0} {π : Equiv.Perm (Fin d)} {mu : Fin e → ℝ≥0} {σ : Equiv.Perm (Fin e)}
    {hl : (∑ i, lam i) = 1} {hm : (∑ j, mu j) = 1} {s : Fin (n + 1) → ℝ}
    {ρ : Equiv.Perm (Fin n)} {a : Fin (d + 1) → Fin (n + 1)} {B : Fin n → Fin e}
    (P : IsCompPresentation lam π mu σ hl hm n s ρ)
    (T : IsCompType lam π hl mu s a B) (j : Fin e) :
    (mu j : ℝ) = ∑ k ∈ Finset.univ.filter (fun k : Fin n => B k = j),
      (s k.succ - s k.castSucc) := by
  classical
  have hB := T.image
  have hm1 : (∑ i, (mu i : ℝ)) = 1 := by rw [← NNReal.coe_sum, hm]; norm_num
  set f : ℝ → ℝ := ⇑(mkIET1 lam π hl) with hf
  set A : Set ℝ := Set.Ico (leftEnd mu j) (leftEnd mu j + (mu j : ℝ)) with hA
  -- the image of a marked cell lies in the `B`-cell of `g`
  have hstep : ∀ (k : Fin n) {x : ℝ}, s k.castSucc ≤ x → x < s k.succ →
      leftEnd mu (B k) ≤ f x ∧ f x < leftEnd mu (B k) + (mu (B k) : ℝ) := by
    intro k x hx1 hx2
    obtain ⟨δ, hδ⟩ := P.f_transl k
    have hlt : s k.castSucc < s k.succ := P.mono (Fin.castSucc_lt_succ (i := k))
    have hf0 : f (s k.castSucc) = s k.castSucc + δ := hδ _ le_rfl hlt
    have hfx : f x = x + δ := hδ x hx1 hx2
    obtain ⟨h1, h2⟩ := hB k
    rw [hf0] at h1 h2
    exact ⟨by rw [hfx]; linarith, by rw [hfx]; linarith⟩
  -- the preimage of the `j`-th cell of `g` is the union of the marked cells with `B = j`
  have hunion : f ⁻¹' A ∩ Set.Ico (0 : ℝ) 1
      = ⋃ k ∈ Finset.univ.filter (fun k : Fin n => B k = j),
          Set.Ico (s k.castSucc) (s k.succ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, Finset.mem_filter,
      Finset.mem_univ, true_and, exists_prop, hA, Set.mem_Ico]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, hx01⟩
      obtain ⟨k, hk1, hk2⟩ := exists_cell_of_strictMono P.mono P.zero P.top hx01
      obtain ⟨hk1', hk2'⟩ := hstep k hk1 hk2
      have hBj : B k = j := by
        by_contra hne
        exact (Set.disjoint_left.mp (disjoint_leftEnd_Ico mu hne) ⟨hk1', hk2'⟩) ⟨hx1, hx2⟩
      exact ⟨k, hBj, hk1, hk2⟩
    · rintro ⟨k, hk, hx1, hx2⟩
      obtain ⟨hk1', hk2'⟩ := hstep k hx1 hx2
      rw [hk] at hk1' hk2'
      refine ⟨⟨hk1', hk2'⟩, ?_, ?_⟩
      · have h0 : s 0 ≤ s k.castSucc := P.mono.monotone (Fin.zero_le k.castSucc)
        rw [P.zero] at h0
        linarith
      · have hle : k.succ ≤ Fin.last n := Fin.le_last _
        have h1 := P.mono.monotone hle
        rw [P.top] at h1
        linarith
  -- the two volumes
  have hvolA : volume (f ⁻¹' A ∩ Set.Ico (0 : ℝ) 1) = ENNReal.ofReal (mu j) := by
    rw [Equiv.IsIET.measure_preimage (isCutSet_mkIET1 lam π hl) measurableSet_Ico]
    rw [Set.inter_eq_left.mpr (leftEnd_Ico_subset mu hm1 j), volume_leftEnd_Ico]
  have hvol : volume (f ⁻¹' A ∩ Set.Ico (0 : ℝ) 1)
      = ∑ k ∈ Finset.univ.filter (fun k : Fin n => B k = j),
          ENNReal.ofReal (s k.succ - s k.castSucc) := by
    rw [hunion]
    rw [measure_biUnion_finset (f := fun k : Fin n => Set.Ico (s k.castSucc) (s k.succ)) ?_ ?_]
    · exact Finset.sum_congr rfl (fun k _ => Real.volume_Ico)
    · intro i _ k _ hik
      refine Set.disjoint_left.mpr ?_
      intro x hx hx'
      rcases lt_or_gt_of_ne hik with hlt | hlt
      · have h1 : s i.succ ≤ s k.castSucc := P.mono.monotone (by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega)
        linarith [hx.2, hx'.1]
      · have h1 : s k.succ ≤ s i.castSucc := P.mono.monotone (by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega)
        linarith [hx'.2, hx.1]
    · exact fun k _ => measurableSet_Ico
  rw [hvolA] at hvol
  have hnn : ∀ k ∈ Finset.univ.filter (fun k : Fin n => B k = j),
      0 ≤ s k.succ - s k.castSucc := fun k _ =>
    sub_nonneg.mpr (le_of_lt (P.mono (Fin.castSucc_lt_succ (i := k))))
  rw [← ENNReal.ofReal_sum_of_nonneg hnn] at hvol
  exact (ENNReal.ofReal_eq_ofReal_iff (mu j).coe_nonneg (Finset.sum_nonneg hnn)).mp hvol

/-- **Lemma 3.1, injectivity**: on a region of parameters of one combinatorial type, the length
vector of `g ∘ f` determines `(λ, μ)`, hence the parameter pair.

This is where the combinatorial type `IsCompType` is paid for: because the marked index `a` of the
cuts of `f` and the cell map `B` are fixed on the region, the two block-sum formulas
(`IsCompPresentation.lam_eq_sum`, `IsCompPresentation.mu_eq_sum`) express every `λᵢ` and every
`μⱼ` as a sum of lengths of marked cells.  So `ν = ν'` gives `λ = λ'` and `μ = μ'`, and
`toReal_simplexMap` (which needs the strict positivity in `G.subset_region`) turns that into
`q = q'`.

No goodness hypothesis is needed any more: the counterexample that forces one without the type
(data at `λ = 3/10, μ = 1/10` and `λ = 1/10, μ = 3/10` with `π = σ` the transposition) is separated
by `B`, which differs at the two points. -/
theorem compLen_injective {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) (O : Set (PReal d e))
    (hreg : ∀ q ∈ O, q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e)
    (n : ℕ) (s : Fin (n + 1) → ParamAffine d e) (ρ : Equiv.Perm (Fin n))
    (a : Fin (d + 1) → Fin (n + 1)) (B : Fin n → Fin e)
    (hpres : ∀ (q) (hq : q ∈ O),
      IsCompPresentation (simplexMap d q.1) π (simplexMap e q.2) σ
        (simplexMap_mem_simplex_fin (hreg q hq).1.1 (hreg q hq).1.2)
        (simplexMap_mem_simplex_fin (hreg q hq).2.1 (hreg q hq).2.2)
        n (fun k => s k q) ρ)
    (htype : ∀ (q) (hq : q ∈ O),
      IsCompType (simplexMap d q.1) π
        (simplexMap_mem_simplex_fin (hreg q hq).1.1 (hreg q hq).1.2)
        (simplexMap e q.2) (fun k => s k q) a B) :
    ∀ q ∈ O, ∀ q' ∈ O,
      (∀ i : Fin n, s i.succ q - s i.castSucc q = s i.succ q' - s i.castSucc q') → q = q' := by
  intro q hq q' hq' hν
  obtain ⟨hpq, hwq⟩ := hreg q hq
  obtain ⟨hpq', hwq'⟩ := hreg q' hq'
  -- **the marked positions agree**: the difference of the two lists is constant in the index, and
  -- both start at `0`
  have hs0 : (fun k => s k q) 0 = (fun k => s k q') 0 :=
    ((hpres q hq).zero).trans ((hpres q' hq').zero).symm
  have hs : (fun k => s k q) = fun k => s k q' := eq_of_increments_eq hs0 hν
  have hs' : ∀ k, s k q = s k q' := fun k => congrFun hs k
  have hmark : markExt (fun k => s k q) = markExt (fun k => s k q') := by
    funext m
    simp only [markExt]
    exact hs' _
  -- **the length vector of `f`**: a telescoping sum over the consecutive block of marked cells
  have hlam : simplexMap d q.1 = simplexMap d q'.1 := by
    funext i
    refine NNReal.eq ?_
    rw [IsCompPresentation.lam_eq_sum (hpres q hq) (htype q hq) i,
      IsCompPresentation.lam_eq_sum (hpres q' hq') (htype q' hq') i, hmark]
  -- **the length vector of `g`**: a sum over the marked cells with a given `B`
  have hmu : simplexMap e q.2 = simplexMap e q'.2 := by
    funext j
    refine NNReal.eq ?_
    rw [IsCompPresentation.mu_eq_sum (hpres q hq) (htype q hq) j,
      IsCompPresentation.mu_eq_sum (hpres q' hq') (htype q' hq') j]
    exact Finset.sum_congr rfl (fun k _ => by simp only [hs'])
  have h1 : (q.1, q.2) = (q'.1, q'.2) := by
    rw [← toReal_simplexMap (d := d) (e := e) hpq.1 hwq.1,
      ← toReal_simplexMap (d := d) (e := e) hpq'.1 hwq'.1, hlam, hmu]
  exact Prod.ext (Prod.ext_iff.mp h1).1 (Prod.ext_iff.mp h1).2

/-! ## 3'. The affine length map

The paper's Lemma 3.1 says that `(λ, μ) ↦ ν` is an invertible affine map, so it carries Lebesgue
measure to a measure absolutely continuous with respect to Lebesgue measure on the simplex.  Here
the affine map is `compLenAffine G.s : PReal d e →ᵃ[ℝ] (Fin (n - 1) → ℝ)`, sending a parameter pair
to the first `n - 1` lengths of the composition (the last one is `1` minus their sum), and `ν` is
`simplexMap n` of it.

This file has the map and the general tool: *an injective affine map between spaces of the same
dimension has injective linear part* (`injective_linear_of_injOn`; a linear equivalence carries Haar
measure to Haar measure, and any two Haar measures on a finite-dimensional real vector space are
mutually absolutely continuous).  The absolute continuity of the pushforward is stated pointwise,
where `compLenAffine G.s` is injective on `G.O` because the combinatorial type is fixed there
(`compLen_injective`) and its image lies in `simplexRegion n`; see
`compLenAffine_absolutelyContinuousAt` in `IETFree.BlockData`. -/

section AffineAbsoluteContinuous

/-- The linear part of an affine map injective on a nonempty open set is injective. -/
theorem injective_linear_of_injOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup F] [Module ℝ F]
    {O : Set E} (hOo : IsOpen O) (hne : O.Nonempty) {A : E →ᵃ[ℝ] F}
    (hinj : Set.InjOn A O) : Function.Injective A.linear := by
  intro v w hvw
  by_contra hne'
  have hz : A.linear (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have hune : v - w ≠ 0 := sub_ne_zero.mpr hne'
  obtain ⟨p, hp⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hOo p hp
  set u := v - w with hu
  set t := ε / (2 * (‖u‖ + 1)) with ht
  have htpos : 0 < t := by
    rw [ht]; positivity
  have hnorm : 0 < ‖u‖ + 1 := by positivity
  have htlt : t * ‖u‖ < ε := by
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg u]
  have hmem : p + t • u ∈ O := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos htpos]
    exact htlt
  have hAp : A (p + t • u) = A p := by
    have h := AffineMap.map_vadd A p (t • u)
    rw [vadd_eq_add, map_smul, hz, smul_zero, add_comm (t • u) p] at h
    simpa using h
  have hfin := hinj hmem hp hAp
  have hzu : t • u = 0 := by
    have := congrArg (fun x => x - p) hfin
    simpa using this
  rcases smul_eq_zero.mp hzu with h | h
  · exact absurd h (ne_of_gt htpos)
  · exact hune h

/-- **An injective affine map pushes Lebesgue measure to an absolutely continuous measure.**
The linear part of an injective affine map is a linear equivalence once the dimensions agree, and a
linear equivalence carries the Haar measure to a Haar measure. -/
theorem absolutelyContinuous_map_affine {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasureSpace F] [BorelSpace F]
    [FiniteDimensional ℝ F] [Measure.IsAddHaarMeasure (volume : Measure E)]
    [Measure.IsAddHaarMeasure (volume : Measure F)]
    [Measure.IsAddRightInvariant (volume : Measure F)]
    {O : Set E} {A : E →ᵃ[ℝ] F} (hinj : Function.Injective A.linear)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    (volume.restrict O).map A ≪ volume := by
  -- the linear part is a linear equivalence, and carries Haar measure to a Haar measure
  set e := LinearMap.linearEquivOfInjective A.linear hinj hdim with he
  have hecoe : (⇑e : E → F) = ⇑A.linear := by
    funext x
    exact LinearMap.linearEquivOfInjective_apply hinj hdim x
  have hlin : (volume : Measure E).map A.linear ≪ (volume : Measure F) := by
    have : ((volume : Measure E).map (⇑e)).IsAddHaarMeasure :=
      Measure.MapLinearEquiv.isAddHaarMeasure volume e
    have h := Measure.absolutelyContinuous_isAddHaarMeasure ((volume : Measure E).map (⇑e))
      (volume : Measure F)
    rwa [hecoe] at h
  have h1 : (volume.restrict O).map A.linear ≪ (volume : Measure F) :=
    (Measure.AbsolutelyContinuous.map (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
      A.linear.continuous_of_finiteDimensional.measurable).trans hlin
  -- `A` is its linear part followed by the translation by `A 0`
  have hA : ∀ x, A x = A.linear x + A 0 := by
    intro x
    have h := AffineMap.map_vadd A (0 : E) x
    rw [vadd_eq_add, add_zero] at h
    simpa using h
  have hstep : ((volume.restrict O).map A.linear).map (fun y : F => y + A 0)
      = (volume.restrict O).map A := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    exact (hA x).symm
  calc (volume.restrict O).map A
      = ((volume.restrict O).map A.linear).map (fun y : F => y + A 0) := hstep.symm
    _ ≪ volume := by
        have h2 : ((volume.restrict O).map A.linear).map (fun y : F => y + A 0)
            ≪ (volume : Measure F).map (fun y : F => y + A 0) :=
          Measure.AbsolutelyContinuous.map h1 (by fun_prop)
        rwa [Measure.IsAddRightInvariant.map_add_right_eq_self (μ := (volume : Measure F))
          (A 0)] at h2

/-- **The sum of consecutive differences.** -/
theorem sum_fin_sub {n : ℕ} (f : ℕ → ℝ) :
    (∑ j : Fin (n - 1), (f ((j : ℕ) + 1) - f (j : ℕ))) = f (n - 1) - f 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun m : ℕ => f (m + 1) - f m) (n - 1)]
  exact Finset.sum_range_sub f (n - 1)

variable {d e : ℕ}

/-- **The first `n - 1` lengths of the composition, as an affine map of the parameters.** -/
noncomputable def compLenAffine {n : ℕ} (s : Fin (n + 1) → ParamAffine d e) :
    PReal d e →ᵃ[ℝ] (Fin (n - 1) → ℝ) :=
  AffineMap.pi fun k : Fin (n - 1) =>
    s ⟨(k : ℕ) + 1, by have := k.isLt; omega⟩ - s ⟨(k : ℕ), by have := k.isLt; omega⟩

theorem compLenAffine_apply {n : ℕ} (s : Fin (n + 1) → ParamAffine d e)
    (q : PReal d e) (k : Fin (n - 1)) :
    compLenAffine s q k
      = s ⟨(k : ℕ) + 1, by have := k.isLt; omega⟩ q - s ⟨(k : ℕ), by have := k.isLt; omega⟩ q :=
  rfl


variable [NeZero d] [NeZero e]

/-- **The sum of the first `n - 1` lengths is the last marked position before `1`.** -/
theorem GoodRegion.sum_compLenAffine {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
    {q₀ : PReal d e} (G : GoodRegion d e π σ q₀) {q : PReal d e}
    (hq : q ∈ G.O) :
    (∑ j : Fin (G.n - 1), compLenAffine G.s q j) = G.s ⟨G.n - 1, by omega⟩ q := by
  classical
  have P := G.pres q hq
  -- there is at least one cell
  have hn1 : 1 ≤ G.n := by
    rcases Nat.eq_zero_or_pos G.n with h | h
    · exfalso
      have h0 : (0 : Fin (G.n + 1)) = Fin.last G.n := Fin.ext (by simp [h])
      have hc : (1 : ℝ) = 0 := by rw [← P.top, ← h0]; exact P.zero
      norm_num at hc
    · exact h
  -- telescoping over the first `n - 1` cells
  have htel : (∑ j : Fin (G.n - 1), compLenAffine G.s q j)
      = markExt (fun k => G.s k q) (G.n - 1) - markExt (fun k => G.s k q) 0 := by
    rw [← sum_fin_sub (fun m => markExt (fun k => G.s k q) m)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have h1 : (j : ℕ) + 1 ≤ G.n := by have := j.isLt; omega
    have h2 : (j : ℕ) ≤ G.n := by have := j.isLt; omega
    rw [compLenAffine_apply, markExt_of_le _ h1, markExt_of_le _ h2]
  rw [htel, markExt_of_le _ (by omega), markExt_of_le _ (by omega),
    show G.s (⟨0, by omega⟩ : Fin (G.n + 1)) q = 0 from P.zero]
  ring

/-! ### The pointwise monotonicity of the marked list and the pointwise length vector

A `GoodRegion` only knows that its list is strictly increasing *on the region*, so a global
monotonicity hypothesis `∀ q, StrictMono fun k => s k q` is not derivable.  These are the pointwise
forms used by the block construction of Lemma 3.4: `monoAt` at a point of the region, and the
membership of the affine length vector in the simplex from the pointwise monotonicity. -/

/-- **The marked list is strictly increasing at every point of the region.** -/
theorem monoAt {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)} {q₀ : PReal d e}
    (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O) :
    StrictMono fun k => G.s k q :=
  (G.pres q hq).mono

/-- **The affine length vector of the composition lies in the open simplex at a point of the
region.**  Neither the monotonicity of the list nor `1 ≤ G.n` is a hypothesis: the first is
`monoAt G hq` and the second follows from `G.n = d + e - 1`. -/
theorem compLenAffine_mem_regionAt {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
    {q₀ : PReal d e} (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O) :
    compLenAffine G.s q ∈ simplexRegion G.n := by
  have P := G.pres q hq
  have hmono : StrictMono fun k => G.s k q := monoAt G hq
  have hn1 : 1 ≤ G.n := by
    have hc := P.card_eq
    have := NeZero.pos d
    have := NeZero.pos e
    omega
  refine ⟨fun i => ?_, ?_⟩
  · have hlt := hmono (Fin.castSucc_lt_succ (i := (⟨(i : ℕ), by have := i.isLt; omega⟩ :
      Fin G.n)))
    beta_reduce at hlt
    simp only [Fin.succ_mk, Fin.castSucc_mk] at hlt
    rw [compLenAffine_apply]
    linarith
  · rw [G.sum_compLenAffine hq]
    have hlastlt : (⟨G.n - 1, Nat.lt_succ_of_le (Nat.sub_le G.n 1)⟩ : Fin (G.n + 1))
        < Fin.last G.n :=
      Fin.lt_def.mpr (by change G.n - 1 < G.n; omega)
    have hlt := hmono hlastlt
    beta_reduce at hlt
    rw [P.top] at hlt
    linarith

end AffineAbsoluteContinuous

/-- The measure-theoretic content of Lemma 3.1, in the abstract form in which it is used: an
almost-sure statement about an absolutely continuous image of the parameters holds for almost every
parameter. -/
theorem ae_of_ae_of_absolutelyContinuous {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν' : Measure β} {φ : α → β} (hφ : AEMeasurable φ μ) (hac : μ.map φ ≪ ν')
    {P : β → Prop} (hP : ∀ᵐ y ∂ν', P y) : ∀ᵐ x ∂μ, P (φ x) :=
  ae_of_ae_map hφ (hac.ae_le hP)

