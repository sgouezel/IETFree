/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.Presentation

/-!
The marked singularity list of `g ∘ f`, and the images of its points under `f`.

The singularities of `g ∘ f` are the non-trivial cuts of `f` and the preimages under `f` of the
non-trivial cuts of `g`; together with `0` and `1` they form a list `s` of `d + e` **affine**
functions of the free parameters which is strictly increasing on a ball (`singAffine`, `withEnds`,
`exists_markedList`).

The file then proves the two geometric facts the reduction needs about that list:

* `f` translates each marked cell and its image lies in a single cell of `g`
  (`markedCell_transl`, `no_cut_inside_markedCell`, `no_gcut_inside_image`);
* the image `f (s k)` of the `k`-th marked point is itself an **affine** function of the parameters
  (`markedPos`, `markedPos_spec`) — the case of `s k` (a cut of `f`, or a preimage of a cut of `g`)
  is decided by the combinatorics alone — and `f (s k)` sits on a cut of `g` only identically
  (`markedPos_eq_cut_of_eq`).
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-- **Sorting a finite family of affine functions by their values at a point.**  If `A : ι →
ParamAffine d e` takes pairwise distinct values at `q₀`, there is a bijection `σ : Fin (card ι) ≃ ι`
along which those values are strictly increasing: `σ` numbers the family in increasing order.

The construction is `Finset.orderEmbOfFin` applied to the finite set of values at `q₀`, composed
with the (chosen) inverse of `A · q₀`. -/
theorem exists_strictMono_comp {ι : Type*} [Fintype ι]
    {d e : ℕ} (A : ι → ParamAffine d e) {q₀ : PReal d e}
    (hA : Function.Injective (fun i => A i q₀)) :
    ∃ σ : Fin (Fintype.card ι) ≃ ι, StrictMono fun k => A (σ k) q₀ := by
  classical
  set v : ι → ℝ := fun i => A i q₀ with hv
  have hvA : Function.Injective v := hA
  -- the finite set of values, and its increasing enumeration
  have ht : (Finset.univ.image v).card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ hvA, Finset.card_univ]
  set g := Finset.orderEmbOfFin (Finset.univ.image v) ht with hg
  have hex : ∀ k : Fin (Fintype.card ι), ∃ i, v i = g k := by
    intro k
    have hk : g k ∈ Finset.univ.image v := Finset.orderEmbOfFin_mem _ _ k
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hk
    exact ⟨i, hi⟩
  refine ⟨Equiv.ofBijective (fun k => Classical.choose (hex k)) ⟨?_, ?_⟩, ?_⟩
  · -- injective
    intro k k' hkk'
    beta_reduce at hkk'
    have h1 : v (Classical.choose (hex k)) = v (Classical.choose (hex k')) := by rw [hkk']
    rw [Classical.choose_spec (hex k), Classical.choose_spec (hex k')] at h1
    exact g.injective h1
  · -- surjective
    intro i
    have hmap : Finset.univ.map g.toEmbedding = Finset.univ.image v := by
      have hsub : Finset.univ.map g.toEmbedding ⊆ Finset.univ.image v := by
        intro y hy
        obtain ⟨k, -, rfl⟩ := Finset.mem_map.mp hy
        exact Finset.orderEmbOfFin_mem _ _ k
      have hcard : (Finset.univ.image v).card ≤ (Finset.univ.map g.toEmbedding).card := by
        rw [Finset.card_image_of_injective _ hvA, Finset.card_map, Finset.card_univ,
          Finset.card_univ, Fintype.card_fin]
      exact Finset.eq_of_subset_of_card_le hsub hcard
    have hi : v i ∈ Finset.univ.map g.toEmbedding := by
      rw [hmap]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    obtain ⟨k, -, hk⟩ := Finset.mem_map.mp hi
    refine ⟨k, hvA ?_⟩
    rw [Classical.choose_spec (hex k)]
    exact hk
  · -- increasing
    intro k k' hkk'
    change v (Classical.choose (hex k)) < v (Classical.choose (hex k'))
    rw [Classical.choose_spec (hex k), Classical.choose_spec (hex k')]
    exact g.lt_iff_lt.mpr hkk'

/-- **The cuts are strictly increasing** when all the lengths are positive. -/
theorem leftEnd_lt_leftEnd {m : ℕ} {lam : Fin m → ℝ≥0} (hpos : Positive lam) {i i' : Fin m}
    (h : i < i') : leftEnd lam i < leftEnd lam i' := by
  have hsub : ∀ j : Fin m, j < i → j < i' := fun j hj => lt_trans hj h
  have hcongr : Finset.univ.filter (fun j : Fin m => j < i)
      = (Finset.univ.filter (fun j : Fin m => j < i')).filter (fun j : Fin m => j < i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      exact ⟨hsub j hj, hj⟩
    · rintro ⟨-, hj⟩
      exact hj
  have h1 : leftEnd lam i = ∑ j ∈ Finset.univ.filter (fun j : Fin m => j < i'),
      (if j < i then (lam j : ℝ) else 0) := by
    rw [leftEnd, hcongr, Finset.sum_filter]
  have h2 : leftEnd lam i' = ∑ j ∈ Finset.univ.filter (fun j : Fin m => j < i'),
      (lam j : ℝ) := by
    rw [leftEnd, Finset.sum_filter]
  rw [h1, h2]
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, ?_⟩
  · split_ifs with hji
    · exact le_rfl
    · exact (lam j).coe_nonneg
  · rw [if_neg (lt_irrefl i)]
    exact_mod_cast hpos i

/-- **At a good parameter pair, no image of a cut of `f` is a cut of `g`.** -/
theorem imageLeft_ne_leftEnd_of_good {d e : ℕ} [NeZero d] [NeZero e]
    {p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0)} (hp : ¬ IsBadParam (toReal p))
    (hl : p.1 ∈ simplex d) (hm : p.2 ∈ simplex e) {j : Fin e} (hj : j ≠ 0)
    (π : Equiv.Perm (Fin d)) (i : Fin d) :
    imageLeft π p.1 i ≠ leftEnd p.2 j := by
  intro h
  refine leftEnd_ne_sum_lam_of_good hp hl hm hj
    (Finset.univ.filter (fun m : Fin d => π m < π i)) ?_
  rw [← h]
  rfl

/-- **Simultaneously for all the cuts of `g`**: there is a ball around `q₀` on which each cut of `g`
sits strictly inside the image of a fixed cell of `f`, and `f⁻¹` of it is the corresponding affine
function. -/
theorem exists_ball_forall_imageLeft_lt {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) {q₀ : PReal d e} (hq₀ : q₀ ∈ goodParams d e)
    (hr₀ : q₀.1 ∈ simplexRegion d ∧ q₀.2 ∈ simplexRegion e) :
    ∃ (k : Fin (e - 1) → Fin d) (ε : ℝ), 0 < ε ∧ Metric.ball q₀ ε ⊆ goodParams d e ∧
      (∀ q ∈ Metric.ball q₀ ε, q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e) ∧
      (∀ q ∈ Metric.ball q₀ ε, ∀ j : Fin (e - 1),
        imageLeftAffine (e := e) π (k j) q
            < cutAffineRight (d := d) ⟨j.val + 1, by have := j.isLt; omega⟩ q ∧
          cutAffineRight (d := d) ⟨j.val + 1, by have := j.isLt; omega⟩ q
            < imageLeftAffine (e := e) π (k j) q + imageLenAffine (e := e) (k j) q) ∧
      (∀ q ∈ Metric.ball q₀ ε, ∀ j : Fin (e - 1), ∀ (hl : simplexMap d q.1 ∈ simplex d),
        (mkIET1 (simplexMap d q.1) π hl)⁻¹
            (leftEnd (simplexMap e q.2) ⟨j.val + 1, by have := j.isLt; omega⟩)
          = preimageCutAffine π ⟨j.val + 1, by have := j.isLt; omega⟩ (k j) q) := by
  classical
  -- for each cut of `g`, a cell of `f` and a ball
  have hstep : ∀ j : Fin (e - 1), ∃ (k : Fin d) (ε : ℝ), 0 < ε ∧
      Metric.ball q₀ ε ⊆ goodParams d e ∧
      (∀ q ∈ Metric.ball q₀ ε, q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e) ∧
      (∀ q ∈ Metric.ball q₀ ε,
        imageLeftAffine (e := e) π k q
            < cutAffineRight (d := d) ⟨j.val + 1, by have := j.isLt; omega⟩ q ∧
          cutAffineRight (d := d) ⟨j.val + 1, by have := j.isLt; omega⟩ q
            < imageLeftAffine (e := e) π k q + imageLenAffine (e := e) k q) ∧
      (∀ q ∈ Metric.ball q₀ ε, ∀ (hl : simplexMap d q.1 ∈ simplex d),
        (mkIET1 (simplexMap d q.1) π hl)⁻¹
            (leftEnd (simplexMap e q.2) ⟨j.val + 1, by have := j.isLt; omega⟩)
          = preimageCutAffine π ⟨j.val + 1, by have := j.isLt; omega⟩ k q) := by
    intro j
    have hj : (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin e) ≠ 0 := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_zero]
      have := j.isLt
      omega
    obtain ⟨k, ε, hε, h1, h2, h3, h4⟩ := exists_ball_imageLeft_lt π hq₀ hr₀ hj
    exact ⟨k, ε, hε, h1, h2, h3, h4⟩
  choose k ε hε hgood hreg hineq hinv using hstep
  -- the intersection of all the balls, of `goodParams` and of the open simplex region
  set V : Set (PReal d e) := (⋂ j, Metric.ball q₀ (ε j)) ∩ goodParams d e ∩
    (simplexRegion d ×ˢ simplexRegion e) with hV
  have hVopen : IsOpen V := by
    refine IsOpen.inter (IsOpen.inter ?_ (isOpen_goodParams d e)) ?_
    · exact isOpen_iInter_of_finite fun j => Metric.isOpen_ball
    · exact (isOpen_simplexRegion d).prod (isOpen_simplexRegion e)
  have hq₀V : q₀ ∈ V := by
    refine ⟨⟨?_, hq₀⟩, hr₀⟩
    simp only [Set.mem_iInter]
    exact fun j => Metric.mem_ball_self (hε j)
  obtain ⟨ε', hε', hball⟩ := Metric.isOpen_iff.mp hVopen q₀ hq₀V
  refine ⟨k, ε', hε', ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact (hball hq).1.2
  · intro q hq
    exact (hball hq).2
  · intro q hq j
    have hqV := (hball hq).1.1
    exact hineq j q (Set.mem_iInter.mp hqV j)
  · intro q hq j
    have hqV := (hball hq).1.1
    exact hinv j q (Set.mem_iInter.mp hqV j)

/-- **`f` at a cut**: the exchange sends the left end of a cell to the left end of its image. -/
theorem mkIET1_leftEnd {d : ℕ} [NeZero d] {v : Fin (d - 1) → ℝ} (hv : v ∈ simplexRegion d)
    (hl : simplexMap d v ∈ simplex d) (π : Equiv.Perm (Fin d)) (i : Fin d) :
    mkIET1 (simplexMap d v) π hl (leftEnd (simplexMap d v) i)
      = imageLeft π (simplexMap d v) i := by
  have hsum : (∑ k, (simplexMap d v k : ℝ)) = 1 := by
    rw [← NNReal.coe_sum]; exact_mod_cast hl
  have hpos : (0 : ℝ) < ((simplexMap d v) i : ℝ) := by exact_mod_cast pos_simplexMap hv i
  have hlt : leftEnd (simplexMap d v) i < ∑ k, (simplexMap d v k : ℝ) := by
    have h1 := upperEnd_le_total (simplexMap d v) i
    rw [upperEnd_eq] at h1
    linarith
  have h := mkIETFun_leftEnd (simplexMap d v) π 0 (i := i) hpos
    (by rw [zero_add, zero_add]; exact hlt)
  have hlink : (mkIET1 (simplexMap d v) π hl).toEquiv (leftEnd (simplexMap d v) i)
      = mkIETFun (simplexMap d v) π 0 (leftEnd (simplexMap d v) i) := rfl
  rw [hlink]
  simpa only [zero_add] using h

/-- **The singularity functions of `g ∘ f`**: the non-trivial cuts of `f` and the preimages of the
non-trivial cuts of `g`, indexed by `Fin (d-1) ⊕ Fin (e-1)`. -/
noncomputable def singAffine {d e : ℕ} [NeZero d] (π : Equiv.Perm (Fin d))
    (k : Fin (e - 1) → Fin d) : Fin (d - 1) ⊕ Fin (e - 1) → ParamAffine d e
  | Sum.inl i => cutAffine (e := e) ⟨i.val + 1, by have := i.isLt; omega⟩
  | Sum.inr j => preimageCutAffine π ⟨j.val + 1, by have := j.isLt; omega⟩ (k j)

theorem singAffine_inl {d e : ℕ} [NeZero d] (π : Equiv.Perm (Fin d))
    (k : Fin (e - 1) → Fin d) (i : Fin (d - 1)) :
    singAffine π k (Sum.inl i)
      = cutAffine (e := e) ⟨i.val + 1, by have := i.isLt; omega⟩ := rfl

theorem singAffine_inr {d e : ℕ} [NeZero d] (π : Equiv.Perm (Fin d))
    (k : Fin (e - 1) → Fin d) (j : Fin (e - 1)) :
    singAffine π k (Sum.inr j)
      = preimageCutAffine π ⟨j.val + 1, by have := j.isLt; omega⟩ (k j) := rfl

/-- **The singularity functions take pairwise distinct values** at a good parameter pair. -/
theorem singAffine_injective {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (k : Fin (e - 1) → Fin d) {q : PReal d e} (hq : q ∈ goodParams d e)
    (hr : q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e)
    (hinv : ∀ j : Fin (e - 1),
      (mkIET1 (simplexMap d q.1) π (simplexMap_mem_simplex_fin hr.1.1 hr.1.2))⁻¹
          (leftEnd (simplexMap e q.2) ⟨j.val + 1, by have := j.isLt; omega⟩)
        = preimageCutAffine π ⟨j.val + 1, by have := j.isLt; omega⟩ (k j) q) :
    Function.Injective (fun i => singAffine π k i q) := by
  have hl : simplexMap d q.1 ∈ simplex d := simplexMap_mem_simplex_fin hr.1.1 hr.1.2
  have hpos1 := pos_simplexMap hr.1
  have hpos2 := pos_simplexMap hr.2
  have hp : ¬ IsBadParam (toReal (simplexMap d q.1, simplexMap e q.2)) := by
    rw [toReal_simplexMap hr.1.1 hr.2.1]
    exact hq
  have hcut : ∀ i : Fin (d - 1),
      singAffine π k (Sum.inl i) q
        = leftEnd (simplexMap d q.1) ⟨i.val + 1, by have := i.isLt; omega⟩ := by
    intro i
    rw [singAffine_inl, cutAffine_eq_leftEnd hr.1]
  have hpre : ∀ j : Fin (e - 1),
      singAffine π k (Sum.inr j) q
        = (mkIET1 (simplexMap d q.1) π hl)⁻¹
            (leftEnd (simplexMap e q.2) ⟨j.val + 1, by have := j.isLt; omega⟩) := by
    intro j
    rw [singAffine_inr, hinv j]
  have hinjf : Function.Injective (⇑(mkIET1 (simplexMap d q.1) π hl)⁻¹) :=
    IET.injective ((mkIET1 (simplexMap d q.1) π hl)⁻¹)
  rintro (a | a) (b | b) h
  · -- two cuts of `f`
    beta_reduce at h
    rw [hcut a, hcut b] at h
    have hab : (⟨a.val + 1, by have := a.isLt; omega⟩ : Fin d)
        = ⟨b.val + 1, by have := b.isLt; omega⟩ := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact absurd h (ne_of_lt (leftEnd_lt_leftEnd hpos1 hlt))
      · exact absurd h.symm (ne_of_lt (leftEnd_lt_leftEnd hpos1 hlt))
    have : a.val = b.val := by
      have := congrArg Fin.val hab
      simp only at this
      omega
    simp only [Sum.inl.injEq, Fin.ext_iff]
    exact this
  · -- a cut of `f` and a preimage of a cut of `g`
    beta_reduce at h
    rw [hcut a, hpre b] at h
    have h2 : mkIET1 (simplexMap d q.1) π hl
        (leftEnd (simplexMap d q.1) ⟨a.val + 1, by have := a.isLt; omega⟩)
        = leftEnd (simplexMap e q.2) ⟨b.val + 1, by have := b.isLt; omega⟩ := by
      rw [h, IET.apply_symm_apply']
    rw [mkIET1_leftEnd hr.1 hl π (⟨a.val + 1, by have := a.isLt; omega⟩ : Fin d)] at h2
    refine absurd h2 (imageLeft_ne_leftEnd_of_good hp hl
      (simplexMap_mem_simplex_fin hr.2.1 hr.2.2) ?_ π _)
    intro hc
    have h1 := congrArg Fin.val hc
    change b.val + 1 = 0 at h1
    omega
  · -- a preimage of a cut of `g` and a cut of `f`
    beta_reduce at h
    rw [hcut b, hpre a] at h
    have h2 : mkIET1 (simplexMap d q.1) π hl
        (leftEnd (simplexMap d q.1) ⟨b.val + 1, by have := b.isLt; omega⟩)
        = leftEnd (simplexMap e q.2) ⟨a.val + 1, by have := a.isLt; omega⟩ := by
      rw [← h, IET.apply_symm_apply']
    rw [mkIET1_leftEnd hr.1 hl π (⟨b.val + 1, by have := b.isLt; omega⟩ : Fin d)] at h2
    refine absurd h2 (imageLeft_ne_leftEnd_of_good hp hl
      (simplexMap_mem_simplex_fin hr.2.1 hr.2.2) ?_ π _)
    intro hc
    have h1 := congrArg Fin.val hc
    change a.val + 1 = 0 at h1
    omega
  · -- two preimages of cuts of `g`
    beta_reduce at h
    rw [hpre a, hpre b] at h
    have h2 : leftEnd (simplexMap e q.2) ⟨a.val + 1, by have := a.isLt; omega⟩
        = leftEnd (simplexMap e q.2) ⟨b.val + 1, by have := b.isLt; omega⟩ := hinjf h
    have hab : (⟨a.val + 1, by have := a.isLt; omega⟩ : Fin e)
        = ⟨b.val + 1, by have := b.isLt; omega⟩ := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact absurd h2 (ne_of_lt (leftEnd_lt_leftEnd hpos2 hlt))
      · exact absurd h2.symm (ne_of_lt (leftEnd_lt_leftEnd hpos2 hlt))
    have : a.val = b.val := by
      have := congrArg Fin.val hab
      simp only at this
      omega
    simp only [Sum.inr.injEq, Fin.ext_iff]
    exact this

/-- **The marked list with the two ends**: `0`, the singularity functions `A`, then `1`. -/
noncomputable def withEnds {d e : ℕ} {n : ℕ} (hn : 1 ≤ n) (A : Fin (n - 1) → ParamAffine d e) :
    Fin (n + 1) → ParamAffine d e :=
  fun j => if h0 : j.val = 0 then 0
    else if h1 : j.val = n then AffineMap.const ℝ (PReal d e) 1
    else A ⟨j.val - 1, by have := j.isLt; omega⟩

theorem withEnds_zero {d e : ℕ} {n : ℕ} (hn : 1 ≤ n) (A : Fin (n - 1) → ParamAffine d e) :
    withEnds hn A 0 = 0 := by
  simp [withEnds]

theorem withEnds_last {d e : ℕ} {n : ℕ} (hn : 1 ≤ n) (A : Fin (n - 1) → ParamAffine d e) :
    withEnds hn A (Fin.last n) = AffineMap.const ℝ (PReal d e) 1 := by
  simp [withEnds, show n ≠ 0 by omega]

theorem withEnds_mid {d e : ℕ} {n : ℕ} (hn : 1 ≤ n) (A : Fin (n - 1) → ParamAffine d e)
    (k : Fin (n - 1)) :
    withEnds hn A ⟨k.val + 1, by have := k.isLt; omega⟩ = A k := by
  have h1 : (⟨k.val + 1, by have := k.isLt; omega⟩ : Fin (n + 1)).val ≠ 0 := by
    simp only []
    omega
  have h2 : (⟨k.val + 1, by have := k.isLt; omega⟩ : Fin (n + 1)).val ≠ n := by
    simp only []
    have := k.isLt
    omega
  simp only [withEnds, dif_neg h1, dif_neg h2]
  congr 1

theorem withEnds_apply_eq {d e n : ℕ} (hn : 1 ≤ n) (A : Fin (n - 1) → ParamAffine d e)
    (j : Fin (n + 1)) (q : PReal d e) :
    withEnds hn A j q = if h0 : j.val = 0 then 0 else if h1 : j.val = n then 1
      else A ⟨j.val - 1, by have := j.isLt; omega⟩ q := by
  by_cases h0 : j.val = 0
  · simp only [withEnds, dif_pos h0]
    rfl
  · by_cases h1 : j.val = n
    · simp only [withEnds, dif_neg h0, dif_pos h1]
      rfl
    · simp only [withEnds, dif_neg h0, dif_neg h1]

/-- **The marked list `0, A, 1` is strictly increasing** at a point where `A` is, with all its
values in `(0, 1)`. -/
theorem strictMono_withEnds {d e n : ℕ} (hn : 1 ≤ n) (A : Fin (n - 1) → ParamAffine d e)
    {q : PReal d e} (h0 : ∀ k, 0 < A k q) (h1 : ∀ k, A k q < 1)
    (hA : StrictMono fun k => A k q) : StrictMono fun j => withEnds hn A j q := by
  intro j j' hjj'
  change (withEnds hn A j) q < (withEnds hn A j') q
  rw [withEnds_apply_eq, withEnds_apply_eq]
  have hlt : j.val < j'.val := hjj'
  rcases eq_or_ne j.val 0 with hj | hj
  · rw [dif_pos hj]
    rcases eq_or_ne j'.val 0 with hj' | hj'
    · omega
    rw [dif_neg hj']
    rcases eq_or_ne j'.val n with hj'n | hj'n
    · rw [dif_pos hj'n]; norm_num
    · rw [dif_neg hj'n]
      exact h0 ⟨j'.val - 1, by have := j'.isLt; omega⟩
  · rw [dif_neg hj]
    rcases eq_or_ne j.val n with hjn | hjn
    · rw [dif_pos hjn]; omega
    · rw [dif_neg hjn]
      have hj'0 : ¬ (j'.val = 0) := by omega
      rw [dif_neg hj'0]
      rcases eq_or_ne j'.val n with hj'n | hj'n
      · rw [dif_pos hj'n]
        exact h1 ⟨j.val - 1, by have := j.isLt; omega⟩
      · rw [dif_neg hj'n]
        exact hA (by simp only [Fin.lt_def]; omega)

/-- On the open simplex region the `i`-th cut of `f` is positive for `i ≠ 0`. -/
theorem cutAffine_pos {d e : ℕ} [NeZero d] {q : PReal d e} (hq : q.1 ∈ simplexRegion d)
    {i : Fin d} (hi : i ≠ 0) : 0 < cutAffine (e := e) i q := by
  rw [cutAffine_eq_leftEnd hq, leftEnd]
  refine Finset.sum_pos' (fun j _ => (simplexMap d q.1 j).coe_nonneg) ⟨0, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.pos_iff_ne_zero.mpr hi
  · exact pos_simplexMap hq 0

/-- On the open simplex region every cut of `f` is less than `1`. -/
theorem cutAffine_lt_one {d e : ℕ} [NeZero d] {q : PReal d e} (hq : q.1 ∈ simplexRegion d)
    (i : Fin d) : cutAffine (e := e) i q < 1 := by
  have hsum : (∑ k, (simplexMap d q.1 k : ℝ)) = 1 := by
    rw [← NNReal.coe_sum]; exact_mod_cast simplexMap_mem_simplex_fin hq.1 hq.2
  have hmem : lastIdx d ∈ Finset.univ.filter (fun j : Fin d => ¬ j < i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    rw [Fin.le_def]
    change d - 1 ≥ i.val
    have := i.isLt
    omega
  have hpos : 0 < ∑ j ∈ Finset.univ.filter (fun j : Fin d => ¬ j < i),
      (simplexMap d q.1 j : ℝ) :=
    Finset.sum_pos' (fun j _ => (simplexMap d q.1 j).coe_nonneg)
      ⟨lastIdx d, hmem, pos_simplexMap hq _⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin d))
    (fun j : Fin d => j < i) (fun j => (simplexMap d q.1 j : ℝ))
  rw [cutAffine_eq_leftEnd hq, leftEnd]
  have hlt : (∑ j ∈ Finset.univ.filter (fun j : Fin d => j < i), (simplexMap d q.1 j : ℝ))
      < (∑ j ∈ Finset.univ.filter (fun j : Fin d => j < i), (simplexMap d q.1 j : ℝ))
        + ∑ j ∈ Finset.univ.filter (fun j : Fin d => ¬ j < i), (simplexMap d q.1 j : ℝ) := by
    linarith
  rw [hsplit, hsum] at hlt
  exact hlt

/-- **The preimages of the cuts of `g` lie in `(0, 1)`.** -/
theorem preimageCutAffine_mem {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    {q : PReal d e} (hq : q ∈ goodParams d e)
    (hr : q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e)
    {j : Fin e} (hj : j ≠ 0) (k : Fin d)
    (hinv : preimageCutAffine π j k q
      = (mkIET1 (simplexMap d q.1) π (simplexMap_mem_simplex_fin hr.1.1 hr.1.2))⁻¹
          (leftEnd (simplexMap e q.2) j)) :
    0 < preimageCutAffine π j k q ∧ preimageCutAffine π j k q < 1 := by
  have hl : simplexMap d q.1 ∈ simplex d := simplexMap_mem_simplex_fin hr.1.1 hr.1.2
  have hm : simplexMap e q.2 ∈ simplex e := simplexMap_mem_simplex_fin hr.2.1 hr.2.2
  have hp : ¬ IsBadParam (toReal (simplexMap d q.1, simplexMap e q.2)) := by
    rw [toReal_simplexMap hr.1.1 hr.2.1]
    exact hq
  have hsum : (∑ i, (simplexMap e q.2 i : ℝ)) = 1 := by
    rw [← NNReal.coe_sum]; exact_mod_cast hm
  have hmem : leftEnd (simplexMap e q.2) j ∈ Set.Ico (0 : ℝ) 1 := by
    refine ⟨leftEnd_nonneg _ _, ?_⟩
    rw [← hsum]
    have h1 := upperEnd_le_total (simplexMap e q.2) j
    rw [upperEnd_eq] at h1
    linarith [pos_simplexMap hr.2 j]
  have h1 : (mkIET1 (simplexMap d q.1) π hl)⁻¹ (leftEnd (simplexMap e q.2) j)
      ∈ Set.Ico (0 : ℝ) 1 := (mkIET1 (simplexMap d q.1) π hl)⁻¹.isIET.mapsTo hmem
  have h2 : (mkIET1 (simplexMap d q.1) π hl)⁻¹ (leftEnd (simplexMap e q.2) j) ≠ 0 := by
    intro hc
    have h3 : (mkIET1 (simplexMap d q.1) π hl)
        ((mkIET1 (simplexMap d q.1) π hl)⁻¹ (leftEnd (simplexMap e q.2) j))
        = leftEnd (simplexMap e q.2) j := IET.apply_symm_apply' _ _
    rw [hc] at h3
    have h4 : (mkIET1 (simplexMap d q.1) π hl) (0 : ℝ) = imageLeft π (simplexMap d q.1) 0 := by
      have h5 := mkIET1_leftEnd hr.1 hl π (0 : Fin d)
      rwa [leftEnd_zero] at h5
    exact imageLeft_ne_leftEnd_of_good hp hl hm hj π 0 (h4.symm.trans h3)
  rw [hinv]
  exact ⟨lt_of_le_of_ne h1.1 (Ne.symm h2), h1.2⟩

/-- **The marked list of `g ∘ f`.**  At a good parameter pair in the open simplex region there is a
ball on which

* the `d + e - 2` singularity functions of `g ∘ f` — the non-trivial cuts of `f` and the
  preimages of the non-trivial cuts of `g` — together with `0` and `1` form a strictly increasing
  list `s` of affine functions of the parameters,
* `s` starts at `0` and ends at `1`,
* and `τ` records which position each singularity occupies.

This is the combinatorial datum the presentation is built from. -/
theorem exists_markedList {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    {q₀ : PReal d e} (_hq₀ : q₀ ∈ goodParams d e)
    (_hr₀ : q₀.1 ∈ simplexRegion d ∧ q₀.2 ∈ simplexRegion e) (hn : 1 ≤ d + e - 1)
    {k : Fin (e - 1) → Fin d} {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (hgood₁ : Metric.ball q₀ ε₁ ⊆ goodParams d e)
    (hreg₁ : ∀ q ∈ Metric.ball q₀ ε₁, q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e)
    (_hineq₁ : ∀ q ∈ Metric.ball q₀ ε₁, ∀ j : Fin (e - 1),
      imageLeftAffine (e := e) π (k j) q
          < cutAffineRight (d := d) ⟨j.val + 1, by have := j.isLt; omega⟩ q ∧
        cutAffineRight (d := d) ⟨j.val + 1, by have := j.isLt; omega⟩ q
          < imageLeftAffine (e := e) π (k j) q + imageLenAffine (e := e) (k j) q)
    (hinv₁ : ∀ q ∈ Metric.ball q₀ ε₁, ∀ j : Fin (e - 1),
      ∀ (hl : simplexMap d q.1 ∈ simplex d),
      (mkIET1 (simplexMap d q.1) π hl)⁻¹
          (leftEnd (simplexMap e q.2) ⟨j.val + 1, by have := j.isLt; omega⟩)
        = preimageCutAffine π ⟨j.val + 1, by have := j.isLt; omega⟩ (k j) q) :
    ∃ (τ : Fin ((d + e - 1) - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1)))
      (A : Fin ((d + e - 1) - 1) → ParamAffine d e) (ε : ℝ),
      0 < ε ∧ Metric.ball q₀ ε ⊆ goodParams d e ∧
        (∀ q ∈ Metric.ball q₀ ε, q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e) ∧
        (∀ q ∈ Metric.ball q₀ ε, StrictMono fun j => withEnds hn A j q) ∧
        (∀ q ∈ Metric.ball q₀ ε, withEnds hn A 0 q = 0) ∧
        (∀ q ∈ Metric.ball q₀ ε, withEnds hn A (Fin.last (d + e - 1)) q = 1) ∧
        (∀ q ∈ Metric.ball q₀ ε, ∀ i : Fin (d - 1),
          withEnds hn A ⟨((τ.symm (Sum.inl i)).val) + 1,
              by have := (τ.symm (Sum.inl i)).isLt; omega⟩ q
            = leftEnd (simplexMap d q.1) ⟨i.val + 1, by have := i.isLt; omega⟩) ∧
        (∀ q ∈ Metric.ball q₀ ε, ∀ j : Fin (e - 1), ∀ (hl : simplexMap d q.1 ∈ simplex d),
          withEnds hn A ⟨((τ.symm (Sum.inr j)).val) + 1,
              by have := (τ.symm (Sum.inr j)).isLt; omega⟩ q
            = (mkIET1 (simplexMap d q.1) π hl)⁻¹
                (leftEnd (simplexMap e q.2) ⟨j.val + 1, by have := j.isLt; omega⟩)) ∧
        (∀ m, A m = singAffine π k (τ m)) := by
  classical
  have hmem₀ : q₀ ∈ Metric.ball q₀ ε₁ := Metric.mem_ball_self hε₁
  have hreg₀ := hreg₁ q₀ hmem₀
  have hl₀ : simplexMap d q₀.1 ∈ simplex d := simplexMap_mem_simplex_fin hreg₀.1.1 hreg₀.1.2
  have hm₀ : simplexMap e q₀.2 ∈ simplex e := simplexMap_mem_simplex_fin hreg₀.2.1 hreg₀.2.2
  have hinv₀ : ∀ j : Fin (e - 1),
      (mkIET1 (simplexMap d q₀.1) π hl₀)⁻¹
          (leftEnd (simplexMap e q₀.2) ⟨j.val + 1, by have := j.isLt; omega⟩)
        = preimageCutAffine π ⟨j.val + 1, by have := j.isLt; omega⟩ (k j) q₀ :=
    fun j => hinv₁ q₀ hmem₀ j hl₀
  have hinj₀ := singAffine_injective π k (hgood₁ hmem₀) hreg₀ hinv₀
  -- sorting
  have hcard : Fintype.card (Fin (d - 1) ⊕ Fin (e - 1)) = (d + e - 1) - 1 := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    have hd := NeZero.pos d
    have he := NeZero.pos e
    omega
  obtain ⟨σ, hσ⟩ := exists_strictMono_comp (singAffine π k) hinj₀
  let τ : Fin ((d + e - 1) - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1)) := (finCongr hcard).symm.trans σ
  have hτ : StrictMono fun kk => singAffine π k (τ kk) q₀ := by
    intro a b hab
    exact hσ (by simpa [τ, Equiv.trans_apply] using hab)
  let A : Fin ((d + e - 1) - 1) → ParamAffine d e := fun kk => singAffine π k (τ kk)
  let s : Fin (d + e - 1 + 1) → ParamAffine d e := withEnds hn A
  -- the values of `A` lie in `(0, 1)`
  have hApos : ∀ kk, 0 < A kk q₀ := by
    intro kk
    rcases h : τ kk with i | j
    · have heq : A kk q₀ = cutAffine (e := e) ⟨i.val + 1, by have := i.isLt; omega⟩ q₀ := by
        simp only [A, h, singAffine_inl]
      rw [heq]
      refine cutAffine_pos hreg₀.1 ?_
      simp only [ne_eq, Fin.ext_iff, Fin.val_zero]
      have := i.isLt
      omega
    · have heq : A kk q₀
          = preimageCutAffine π ⟨j.val + 1, by have := j.isLt; omega⟩ (k j) q₀ := by
        simp only [A, h, singAffine_inr]
      rw [heq]
      exact (preimageCutAffine_mem π (hgood₁ hmem₀) hreg₀
        (j := ⟨j.val + 1, by have := j.isLt; omega⟩)
        (by simp only [ne_eq, Fin.ext_iff, Fin.val_zero]; have := j.isLt; omega)
        (k j) (hinv₀ j).symm).1
  have hAlt : ∀ kk, A kk q₀ < 1 := by
    intro kk
    rcases h : τ kk with i | j
    · have heq : A kk q₀ = cutAffine (e := e) ⟨i.val + 1, by have := i.isLt; omega⟩ q₀ := by
        simp only [A, h, singAffine_inl]
      rw [heq]
      exact cutAffine_lt_one hreg₀.1 _
    · have heq : A kk q₀
          = preimageCutAffine π ⟨j.val + 1, by have := j.isLt; omega⟩ (k j) q₀ := by
        simp only [A, h, singAffine_inr]
      rw [heq]
      exact (preimageCutAffine_mem π (hgood₁ hmem₀) hreg₀
        (j := ⟨j.val + 1, by have := j.isLt; omega⟩)
        (by simp only [ne_eq, Fin.ext_iff, Fin.val_zero]; have := j.isLt; omega)
        (k j) (hinv₀ j).symm).2
  have hmono₀ : StrictMono fun j => s j q₀ := strictMono_withEnds hn A hApos hAlt hτ
  obtain ⟨ε₂, hε₂, hball₂⟩ := exists_ball_strictMono (fun j => s j) hmono₀
  -- the ball where everything holds
  have hVopen : IsOpen (Metric.ball q₀ ε₁ ∩ Metric.ball q₀ ε₂) :=
    Metric.isOpen_ball.inter Metric.isOpen_ball
  have hq₀V : q₀ ∈ Metric.ball q₀ ε₁ ∩ Metric.ball q₀ ε₂ :=
    ⟨Metric.mem_ball_self hε₁, Metric.mem_ball_self hε₂⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVopen q₀ hq₀V
  refine ⟨τ, A, ε, hε, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact hgood₁ (hball hq).1
  · intro q hq
    exact hreg₁ q (hball hq).1
  · intro q hq
    exact hball₂ q (hball hq).2
  · intro q _
    rw [withEnds_zero hn A]
    rfl
  · intro q _
    rw [withEnds_last hn A]
    rfl
  · intro q hq i
    have hmid : withEnds hn A ⟨((τ.symm (Sum.inl i)).val) + 1,
        by have := (τ.symm (Sum.inl i)).isLt; omega⟩ = A (τ.symm (Sum.inl i)) :=
      withEnds_mid hn A (τ.symm (Sum.inl i))
    rw [hmid]
    have heq : A (τ.symm (Sum.inl i)) q
        = cutAffine (e := e) ⟨i.val + 1, by have := i.isLt; omega⟩ q := by
      simp only [A, Equiv.apply_symm_apply, singAffine_inl]
    rw [heq, cutAffine_eq_leftEnd (hreg₁ q (hball hq).1).1]
  · intro q hq j hl
    have hmid : withEnds hn A ⟨((τ.symm (Sum.inr j)).val) + 1,
        by have := (τ.symm (Sum.inr j)).isLt; omega⟩ = A (τ.symm (Sum.inr j)) :=
      withEnds_mid hn A (τ.symm (Sum.inr j))
    rw [hmid]
    have heq : A (τ.symm (Sum.inr j)) q
        = preimageCutAffine π ⟨j.val + 1, by have := j.isLt; omega⟩ (k j) q := by
      simp only [A, Equiv.apply_symm_apply, singAffine_inr]
    rw [heq, ← hinv₁ q (hball hq).1 j hl]
  · exact fun m => rfl

/-- **No cut of `f` lies strictly inside a marked cell.**  The marked positions include every
non-trivial cut of `f` (the `inl` entries of `τ`), and the marked list is strictly increasing, so a
cut cannot sit strictly between two consecutive marked points. -/
theorem no_cut_inside_markedCell {d e n : ℕ} [NeZero d] (lam : Fin d → ℝ≥0)
    (τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1))) {s : Fin (n + 1) → ℝ}
    (hmono : StrictMono s)
    (hcut : ∀ i : Fin (d - 1),
      s ⟨(τ.symm (Sum.inl i)).val + 1, by have := (τ.symm (Sum.inl i)).isLt; omega⟩
        = leftEnd lam ⟨i.val + 1, by have := i.isLt; omega⟩)
    {k : Fin n} {c : Fin d} (hc : c ≠ 0) :
    ¬ (s k.castSucc < leftEnd lam c ∧ leftEnd lam c < s k.succ) := by
  rintro ⟨h1, h2⟩
  -- write `c` as `i.val + 1` with `i : Fin (d - 1)`
  have hpos : 0 < c.val := by
    rcases Nat.eq_zero_or_pos c.val with h | h
    · exact absurd (Fin.ext (by simp [h])) hc
    · exact h
  set i : Fin (d - 1) := ⟨c.val - 1, by have := c.isLt; have := NeZero.pos d; omega⟩ with hi
  have hival : i.val = c.val - 1 := by rw [hi]
  have hci : (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin d) = c := by
    ext
    simp only
    omega
  have hposn := hcut i
  rw [hci] at hposn
  -- the position of the cut in `s`
  have hlt1 : k.castSucc.val < (τ.symm (Sum.inl i)).val + 1 := by
    have h3 : s k.castSucc < s ⟨(τ.symm (Sum.inl i)).val + 1,
        by have := (τ.symm (Sum.inl i)).isLt; omega⟩ := by
      rw [hposn]; exact h1
    exact Fin.lt_def.mp (hmono.lt_iff_lt.mp h3)
  have hlt2 : (τ.symm (Sum.inl i)).val + 1 < k.succ.val := by
    have h3 : s ⟨(τ.symm (Sum.inl i)).val + 1,
        by have := (τ.symm (Sum.inl i)).isLt; omega⟩ < s k.succ := by
      rw [hposn]; exact h2
    exact Fin.lt_def.mp (hmono.lt_iff_lt.mp h3)
  simp only [Fin.val_succ, Fin.val_castSucc] at hlt1 hlt2
  omega

/-- **The cut set of `mkIET1`, described**: for lengths summing to `1`, the cut set
`mkIETCuts lam 0 1` is exactly the set of cuts `leftEnd lam i`. -/
theorem mem_mkIETCuts_one {n : ℕ} {lam : Fin n → ℝ≥0} (hpos : Positive lam)
    (hsum : (∑ i, (lam i : ℝ)) = 1) {c : ℝ} :
    c ∈ mkIETCuts lam 0 1 ↔ ∃ i : Fin n, leftEnd lam i = c := by
  rw [mkIETCuts, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨h | h, -⟩
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
      exact ⟨i, by simpa using hi⟩
    · rw [if_neg (by linarith)] at h
      exact absurd h (by simp)
  · rintro ⟨i, rfl⟩
    refine ⟨Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, by simp⟩), ?_⟩
    refine ⟨leftEnd_nonneg lam i, ?_⟩
    have h1 := upperEnd_le_total lam i
    rw [upperEnd_eq] at h1
    rw [← hsum]
    linarith [hpos i]

/-- **`f` translates each marked cell.**  The marked points include every non-trivial cut of `f`,
and no cut of `f` lies strictly inside a marked cell (`no_cut_inside_markedCell`), so the cut-set
criterion `IsCutSet.transl_of_locally` applies with a vacuous hypothesis. -/
theorem markedCell_transl {d e n : ℕ} [NeZero d] (π : Equiv.Perm (Fin d))
    {v : Fin (d - 1) → ℝ} (hv : v ∈ simplexRegion d) (hl : simplexMap d v ∈ simplex d)
    {τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1))} {s : Fin (n + 1) → ℝ}
    (hmono : StrictMono s) (hzero : s 0 = 0) (htop : s (Fin.last n) = 1)
    (hcut : ∀ i : Fin (d - 1),
      s ⟨(τ.symm (Sum.inl i)).val + 1, by have := (τ.symm (Sum.inl i)).isLt; omega⟩
        = leftEnd (simplexMap d v) ⟨i.val + 1, by have := i.isLt; omega⟩)
    (k : Fin n) :
    ∃ δ : ℝ, ∀ x : ℝ, s k.castSucc ≤ x → x < s k.succ →
      mkIET1 (simplexMap d v) π hl x = x + δ := by
  have hlam : (∑ i, (simplexMap d v i : ℝ)) = 1 := by
    rw [← NNReal.coe_sum]; exact_mod_cast hl
  have hpos : ∀ i, 0 < simplexMap d v i := pos_simplexMap hv
  have hcs := isCutSet_mkIET1 (simplexMap d v) π hl
  refine ⟨mkIET1 (simplexMap d v) π hl (s k.castSucc) - s k.castSucc, ?_⟩
  intro x hx1 hx2
  have hk0 : 0 ≤ s k.castSucc := by
    rw [← hzero]; exact hmono.monotone (Fin.zero_le _)
  have hk1 : s k.castSucc < 1 := by
    rw [← htop]
    exact hmono (by simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]; have := k.isLt; omega)
  have hks : s k.succ ≤ 1 := by
    rw [← htop]
    exact hmono.monotone (by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_last]; have := k.isLt; omega)
  have hx0 : 0 ≤ x := le_trans hk0 hx1
  have hx1' : x < 1 := lt_of_lt_of_le hx2 hks
  have hkey := hcs.transl_of_locally (x := s k.castSucc) (y := x) ⟨hk0, hk1⟩ ⟨hx0, hx1'⟩ ?_
  · linarith
  · intro c hc hmin hmax
    exfalso
    obtain ⟨i, hi⟩ := (mem_mkIETCuts_one hpos hlam).mp hc
    have hmin' : s k.castSucc < c := by
      rw [min_eq_left hx1] at hmin; exact hmin
    have hmax' : c ≤ x := by
      rw [max_eq_right hx1] at hmax; exact hmax
    rcases eq_or_ne i 0 with rfl | hi0
    · rw [leftEnd_zero] at hi
      linarith
    · refine no_cut_inside_markedCell (simplexMap d v) τ hmono hcut (k := k) hi0 ⟨?_, ?_⟩
      · rw [hi]; exact hmin'
      · rw [hi]; linarith

/-- The image of a half-open interval under a translation. -/
theorem image_Ico_add {a b : ℝ} (_h : a < b) {f : ℝ → ℝ} {δ : ℝ}
    (hf : ∀ x, a ≤ x → x < b → f x = x + δ) :
    f '' Set.Ico a b = Set.Ico (a + δ) (b + δ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hf x hx.1 hx.2]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨y - δ, ⟨by linarith, by linarith⟩, ?_⟩
    rw [hf _ (by linarith) (by linarith)]
    ring

/-- **No cut of `g` lies strictly inside the image of a marked cell.**  If one did, its preimage
under `f` — which is a marked point, by the `inr` entries of `τ` — would lie strictly between
`s k` and `s k+1`, contradicting `StrictMono s`. -/
theorem no_gcut_inside_image {d e n : ℕ} [NeZero d] (π : Equiv.Perm (Fin d))
    {v : Fin (d - 1) → ℝ} {w : Fin (e - 1) → ℝ} (hv : v ∈ simplexRegion d)
    (hl : simplexMap d v ∈ simplex d)
    {τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1))} {s : Fin (n + 1) → ℝ}
    (hmono : StrictMono s) (hzero : s 0 = 0) (htop : s (Fin.last n) = 1)
    (hcut : ∀ i : Fin (d - 1),
      s ⟨(τ.symm (Sum.inl i)).val + 1, by have := (τ.symm (Sum.inl i)).isLt; omega⟩
        = leftEnd (simplexMap d v) ⟨i.val + 1, by have := i.isLt; omega⟩)
    (hpre : ∀ j : Fin (e - 1),
      s ⟨(τ.symm (Sum.inr j)).val + 1, by have := (τ.symm (Sum.inr j)).isLt; omega⟩
        = (mkIET1 (simplexMap d v) π hl)⁻¹
            (leftEnd (simplexMap e w) ⟨j.val + 1, by have := j.isLt; omega⟩))
    (k : Fin n) {j : Fin (e - 1)} :
    ¬ (mkIET1 (simplexMap d v) π hl (s k.castSucc) < leftEnd (simplexMap e w) ⟨j.val + 1,
          by have := j.isLt; omega⟩ ∧
        leftEnd (simplexMap e w) ⟨j.val + 1, by have := j.isLt; omega⟩
          < mkIET1 (simplexMap d v) π hl (s k.castSucc) + (s k.succ - s k.castSucc)) := by
  rintro ⟨h1, h2⟩
  obtain ⟨δ, hδ⟩ := markedCell_transl π hv hl hmono hzero htop hcut k
  have hlt : s k.castSucc < s k.succ := hmono (Fin.castSucc_lt_succ)
  have himg : mkIET1 (simplexMap d v) π hl '' Set.Ico (s k.castSucc) (s k.succ)
      = Set.Ico (mkIET1 (simplexMap d v) π hl (s k.castSucc))
          (mkIET1 (simplexMap d v) π hl (s k.castSucc) + (s k.succ - s k.castSucc)) := by
    have h := image_Ico_add hlt (f := mkIET1 (simplexMap d v) π hl) (δ := δ) hδ
    have h1' : s k.castSucc + δ = mkIET1 (simplexMap d v) π hl (s k.castSucc) :=
      (hδ _ le_rfl hlt).symm
    rw [h, h1']
    congr 1
    linarith [h1']
  have hmem : leftEnd (simplexMap e w) ⟨j.val + 1, by have := j.isLt; omega⟩
      ∈ mkIET1 (simplexMap d v) π hl '' Set.Ico (s k.castSucc) (s k.succ) := by
    rw [himg]; exact ⟨le_of_lt h1, h2⟩
  obtain ⟨x, hx, hfx⟩ := hmem
  -- `x` is a marked point
  have hxpre : x = s ⟨(τ.symm (Sum.inr j)).val + 1,
      by have := (τ.symm (Sum.inr j)).isLt; omega⟩ := by
    rw [hpre j]
    rw [← hfx, IET.symm_apply_apply]
  -- so it is `s k.castSucc`, contradicting the strict inequality
  subst hxpre
  have hle : k.val ≤ (τ.symm (Sum.inr j)).val + 1 := by
    have h := hmono.le_iff_le.mp hx.1
    simpa using Fin.le_def.mp h
  have hlt' : (τ.symm (Sum.inr j)).val + 1 ≤ k.val := by
    have h := hmono.lt_iff_lt.mp hx.2
    have h2 := Fin.lt_def.mp h
    simp only [Fin.val_succ] at h2
    omega
  have heq : (⟨(τ.symm (Sum.inr j)).val + 1, by
      have := (τ.symm (Sum.inr j)).isLt; omega⟩ : Fin (n + 1)) = k.castSucc :=
    Fin.ext (by
      change (τ.symm (Sum.inr j)).val + 1 = k.val
      omega)
  rw [heq] at hfx
  linarith

/-- `leftEnd` at the successor index is `upperEnd` at the index. -/
theorem leftEnd_eq_upperEnd_of_succ {n : ℕ} (lam : Fin n → ℝ≥0) {i : Fin n}
    (h : i.val + 1 < n) : leftEnd lam ⟨i.val + 1, h⟩ = upperEnd lam i := by
  rw [leftEnd, upperEnd]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def, Fin.lt_def]
  omega

/-- **The `j`-th length of `g`, as an affine function of the free parameters**: the free coordinate
`q.2 j` at a free index, and the remaining mass `1 - ∑ q.2` at the last index.  The `g`-analogue of
`imageLenAffine`. -/
noncomputable def imageLenAffineRight {d e : ℕ} [NeZero e] (j : Fin e) : ParamAffine d e :=
  if h : j.val + 1 = e then
    AffineMap.const ℝ (PReal d e) (1 : ℝ) - ∑ m : Fin (e - 1), rightCoordAffine m
  else rightCoordAffine (d := d) ⟨j.val, by
    have h1 := j.isLt
    have h2 := NeZero.pos e
    omega⟩

theorem imageLenAffineRight_apply_last {d e : ℕ} [NeZero e] {j : Fin e} (h : j.val + 1 = e)
    (q : PReal d e) :
    imageLenAffineRight (d := d) j q = 1 - ∑ m : Fin (e - 1), q.2 m := by
  rw [imageLenAffineRight, dif_pos h]
  have hsub : ∀ (f g : ParamAffine d e), (f - g) q = f q - g q := fun f g => rfl
  rw [hsub, AffineMap.sum_apply]
  simp [rightCoordAffine_apply]

theorem imageLenAffineRight_apply_free {d e : ℕ} [NeZero e] {j : Fin e} (h : ¬ j.val + 1 = e)
    (q : PReal d e) :
    imageLenAffineRight (d := d) j q
      = q.2 ⟨j.val, by have h1 := j.isLt; have h2 := NeZero.pos e; omega⟩ := by
  simp only [imageLenAffineRight, dif_neg h, rightCoordAffine_apply]

/-- On the open simplex region, `imageLenAffineRight j` is the `j`-th length of `simplexMap`. -/
theorem imageLenAffineRight_eq {d e : ℕ} [NeZero e] {q : PReal d e}
    (hq : q.2 ∈ simplexRegion e) (j : Fin e) :
    imageLenAffineRight (d := d) j q = (simplexMap e q.2 j : ℝ) := by
  by_cases h : j.val + 1 = e
  · rw [imageLenAffineRight_apply_last h, simplexMap, dif_pos h,
      Real.coe_toNNReal _ (by linarith [hq.2])]
  · have hj' : j.val < e - 1 := by
      have h1 := j.isLt
      have h2 := NeZero.pos e
      omega
    rw [imageLenAffineRight_apply_free h, simplexMap_of_lt hq hj']

/-- **The left end of the image of the `k`-th cell of `g`, as an affine function of the free
parameters.**  The `g`-analogue of `imageLeftAffine`. -/
noncomputable def imageLeftAffineRight {d e : ℕ} [NeZero e] (σ : Equiv.Perm (Fin e))
    (k : Fin e) : ParamAffine d e :=
  ∑ m : Fin e, if σ m < σ k then imageLenAffineRight (d := d) m else 0

theorem imageLeftAffineRight_apply {d e : ℕ} [NeZero e] (σ : Equiv.Perm (Fin e)) (k : Fin e)
    (q : PReal d e) :
    imageLeftAffineRight (d := d) σ k q
      = ∑ m : Fin e, if σ m < σ k then imageLenAffineRight (d := d) m q else 0 := by
  rw [imageLeftAffineRight, AffineMap.sum_apply]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  by_cases h : σ m < σ k
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    rfl

/-- On the open simplex region the left end of the image of the `k`-th cell of `g` is the affine
function `imageLeftAffineRight σ k`. -/
theorem imageLeftAffineRight_eq {d e : ℕ} [NeZero e] (σ : Equiv.Perm (Fin e)) {q : PReal d e}
    (hq : q.2 ∈ simplexRegion e) (k : Fin e) :
    imageLeftAffineRight (d := d) σ k q = imageLeft σ (simplexMap e q.2) k := by
  rw [imageLeftAffineRight_apply, imageLeft, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  by_cases hmk : σ m < σ k
  · rw [if_pos hmk, if_pos hmk, imageLenAffineRight_eq hq]
  · rw [if_neg hmk, if_neg hmk]

/-- **The upper end of the `j`-th cell of `g`**, as an affine function of the free parameters: it is
`1` for the last cell and the next cut otherwise. -/
noncomputable def upperEndAffineRight {d e : ℕ} [NeZero e] (j : Fin e) : ParamAffine d e :=
  if h : j.val + 1 = e then AffineMap.const ℝ (PReal d e) 1
  else cutAffineRight (d := d) ⟨j.val + 1, by have := j.isLt; have := NeZero.pos e; omega⟩

/-- On the open simplex region the upper end of the `j`-th cell of `g` is `upperEnd μ j`. -/
theorem upperEndAffineRight_eq {d e : ℕ} [NeZero e] {q : PReal d e}
    (hq : q.2 ∈ simplexRegion e) (j : Fin e) :
    upperEndAffineRight (d := d) j q = upperEnd (simplexMap e q.2) j := by
  have hsum : (∑ m, (simplexMap e q.2 m : ℝ)) = 1 := by
    rw [← NNReal.coe_sum]; exact_mod_cast simplexMap_mem_simplex_fin hq.1 hq.2
  rw [upperEndAffineRight]
  by_cases h : j.val + 1 = e
  · rw [dif_pos h]
    rw [upperEnd_of_max (simplexMap e q.2) (fun m => by
      rw [Fin.le_def]; have := m.isLt; omega), hsum]
    rfl
  · rw [dif_neg h, cutAffineRight_eq_leftEnd (d := d) hq]
    have h1 : j.val + 1 < e := by have := j.isLt; have := NeZero.pos e; omega
    rw [leftEnd_eq_upperEnd_of_succ _ h1]

/-- If `Ico a b ⊆ Ico 0 1` and `a < 1`, then `b ≤ 1`: otherwise `1 ∈ Ico a b`. -/
theorem le_of_Ico_subset {a b : ℝ} (ha : a < 1) (h : Set.Ico a b ⊆ Set.Ico (0 : ℝ) 1) :
    b ≤ 1 := by
  by_contra hcon
  rw [not_le] at hcon
  have h2 := h (show (1 : ℝ) ∈ Set.Ico a b from ⟨le_of_lt ha, hcon⟩)
  rw [Set.mem_Ico] at h2
  linarith [h2.2]

/-- **The image under `f` of the `j`-th marked point, as an affine function of the parameters.**

The marked point `s j` is of one of three kinds, decided by the index `j` and by `τ` and not by the
parameters: `0` (then `f` maps it to the left end of the image of the first cell of `f`), a cut
`leftEnd λ i` of `f` with `i ≠ 0` (then `f` maps it to the left end of the image of the `i`-th
cell), or a preimage of a cut `leftEnd μ j'` of `g` (then `f` maps it to that cut).  Since the case
is fixed, `f_q (s j q)` is an affine function of `q`, which is what makes the *order* of the marked
images locally constant. -/
noncomputable def markedPos {d e n : ℕ} [NeZero d] (π : Equiv.Perm (Fin d))
    (τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1))) (j : Fin n) : ParamAffine d e :=
  if h0 : j.val = 0 then imageLeftAffine π 0
  else
    Sum.rec
      (fun i : Fin (d - 1) => imageLeftAffine π ⟨i.val + 1, by have := i.isLt; omega⟩)
      (fun j' : Fin (e - 1) => cutAffineRight (d := d) ⟨j'.val + 1, by have := j'.isLt; omega⟩)
      (τ ⟨j.val - 1, by have := j.isLt; omega⟩)

theorem markedPos_zero {d e n : ℕ} [NeZero d] [NeZero n] (π : Equiv.Perm (Fin d))
    (τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1))) :
    markedPos (e := e) π τ 0 = imageLeftAffine π 0 := by
  simp [markedPos]

theorem markedPos_inl {d e n : ℕ} [NeZero d] (π : Equiv.Perm (Fin d))
    (τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1))) (m : Fin (n - 1)) (i : Fin (d - 1))
    (hτ : τ m = Sum.inl i) :
    markedPos (e := e) π τ ⟨m.val + 1, by have := m.isLt; omega⟩
      = imageLeftAffine π ⟨i.val + 1, by have := i.isLt; omega⟩ := by
  have h0 : ¬ ((⟨m.val + 1, by have := m.isLt; omega⟩ : Fin n).val = 0) := by simp
  simp only [markedPos, dif_neg h0]
  rw [show (⟨(⟨m.val + 1, by have := m.isLt; omega⟩ : Fin n).val - 1,
      by have := m.isLt; omega⟩ : Fin (n - 1)) = m from Fin.ext (by simp), hτ]

theorem markedPos_inr {d e n : ℕ} [NeZero d] (π : Equiv.Perm (Fin d))
    (τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1))) (m : Fin (n - 1)) (j' : Fin (e - 1))
    (hτ : τ m = Sum.inr j') :
    markedPos (e := e) π τ ⟨m.val + 1, by have := m.isLt; omega⟩
      = cutAffineRight (d := d) ⟨j'.val + 1, by have := j'.isLt; omega⟩ := by
  have h0 : ¬ ((⟨m.val + 1, by have := m.isLt; omega⟩ : Fin n).val = 0) := by simp
  simp only [markedPos, dif_neg h0]
  rw [show (⟨(⟨m.val + 1, by have := m.isLt; omega⟩ : Fin n).val - 1,
      by have := m.isLt; omega⟩ : Fin (n - 1)) = m from Fin.ext (by simp), hτ]

/-- **The image of the `j`-th marked point is the affine function `markedPos j`**, on a good
parameter pair. -/
theorem markedPos_spec {d e n : ℕ} [NeZero d] (π : Equiv.Perm (Fin d))
    (κ : Fin (e - 1) → Fin d) (τ : Fin (n - 1) ≃ (Fin (d - 1) ⊕ Fin (e - 1)))
    {hn : 1 ≤ n} {A : Fin (n - 1) → ParamAffine d e}
    (hA : ∀ m, A m = singAffine π κ (τ m))
    {q : PReal d e} (hreg : q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e)
    (hzero : withEnds hn A 0 q = 0)
    (hcut : ∀ i : Fin (d - 1),
      withEnds hn A ⟨(τ.symm (Sum.inl i)).val + 1, by have := (τ.symm (Sum.inl i)).isLt; omega⟩ q
        = leftEnd (simplexMap d q.1) ⟨i.val + 1, by have := i.isLt; omega⟩)
    (hpre : ∀ j' : Fin (e - 1),
      withEnds hn A ⟨(τ.symm (Sum.inr j')).val + 1, by have := (τ.symm (Sum.inr j')).isLt; omega⟩ q
        = (mkIET1 (simplexMap d q.1) π (simplexMap_mem_simplex_fin hreg.1.1 hreg.1.2))⁻¹
            (leftEnd (simplexMap e q.2) ⟨j'.val + 1, by have := j'.isLt; omega⟩))
    (j : Fin n) :
    mkIET1 (simplexMap d q.1) π (simplexMap_mem_simplex_fin hreg.1.1 hreg.1.2)
        (withEnds (e := e) hn A j.castSucc q)
      = markedPos (e := e) π τ j q := by
  have hl : simplexMap d q.1 ∈ simplex d := simplexMap_mem_simplex_fin hreg.1.1 hreg.1.2
  have : NeZero n := ⟨by omega⟩
  rcases eq_or_ne j.val 0 with hj | hj
  · -- the marked point `s 0 = 0`
    have hj0 : j = 0 := Fin.ext (by simpa using hj)
    subst hj0
    have hcast : (0 : Fin n).castSucc = (0 : Fin (n + 1)) := Fin.ext rfl
    rw [hcast, hzero, markedPos_zero]
    have h1 : mkIET1 (simplexMap d q.1) π hl 0 = imageLeft π (simplexMap d q.1) 0 := by
      have h := mkIET1_leftEnd hreg.1 hl π (0 : Fin d)
      rwa [leftEnd_zero] at h
    rw [h1, imageLeftAffine_eq π hreg.1]
  · -- the marked point is `A m`
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k + 1 = j.val := ⟨j.val - 1, by have := j.isLt; omega⟩
    have hklt : k < n - 1 := by have := j.isLt; omega
    set m : Fin (n - 1) := ⟨k, hklt⟩ with hm
    have hmval : m.val = k := rfl
    have hjeq : j = (⟨k + 1, by have := j.isLt; omega⟩ : Fin n) := Fin.ext (by simp; omega)
    have hcast : (⟨k + 1, by have := j.isLt; omega⟩ : Fin n).castSucc
        = (⟨m.val + 1, by have := m.isLt; omega⟩ : Fin (n + 1)) := by
      ext
      simp only [Fin.val_castSucc]
      omega
    have hmid : withEnds (e := e) hn A (⟨m.val + 1, by have := m.isLt; omega⟩ : Fin (n + 1))
        = A m := withEnds_mid hn A m
    have hmidx : (⟨j.val - 1, by have := j.isLt; omega⟩ : Fin (n - 1)) = m := by
      ext
      simp only [hmval]
      omega
    rw [hjeq, hcast, hmid]
    rcases hτ : τ m with i | j'
    · -- a cut of `f`
      have hAm : A m = cutAffine (e := e) ⟨i.val + 1, by have := i.isLt; omega⟩ := by
        rw [hA m, hτ]; rfl
      have hleft : A m q = leftEnd (simplexMap d q.1) ⟨i.val + 1, by have := i.isLt; omega⟩ := by
        rw [hAm, cutAffine_eq_leftEnd hreg.1]
      have hsymm : τ.symm (Sum.inl i) = m := by rw [← hτ, Equiv.symm_apply_apply]
      have hidx : (⟨(τ.symm (Sum.inl i)).val + 1,
          by have := (τ.symm (Sum.inl i)).isLt; omega⟩ : Fin (n + 1))
        = (⟨m.val + 1, by have := m.isLt; omega⟩ : Fin (n + 1)) := by
        refine Fin.ext ?_
        change (τ.symm (Sum.inl i)).val + 1 = m.val + 1
        rw [hsymm]
      have hcutm := hcut i
      simp only [hidx] at hcutm
      rw [hmid] at hcutm
      rw [markedPos_inl π τ m i hτ, hleft, mkIET1_leftEnd hreg.1 hl π ⟨i.val + 1, _⟩,
        imageLeftAffine_eq π hreg.1]
    · -- a preimage of a cut of `g`
      have hApre : A m = preimageCutAffine π ⟨j'.val + 1, by have := j'.isLt; omega⟩ (κ j') := by
        rw [hA m, hτ]; rfl
      have hsymm : τ.symm (Sum.inr j') = m := by rw [← hτ, Equiv.symm_apply_apply]
      have hidx : (⟨(τ.symm (Sum.inr j')).val + 1,
          by have := (τ.symm (Sum.inr j')).isLt; omega⟩ : Fin (n + 1))
        = (⟨m.val + 1, by have := m.isLt; omega⟩ : Fin (n + 1)) := by
        refine Fin.ext ?_
        change (τ.symm (Sum.inr j')).val + 1 = m.val + 1
        rw [hsymm]
      have hprem := hpre j'
      simp only [hidx] at hprem
      rw [hmid] at hprem
      have hval : mkIET1 (simplexMap d q.1) π hl (A m q)
          = leftEnd (simplexMap e q.2) ⟨j'.val + 1, by have := j'.isLt; omega⟩ := by
        rw [hprem, IET.apply_symm_apply']
      rw [markedPos_inr π τ m j' hτ, hval, cutAffineRight_eq_leftEnd (d := d) hreg.2]
