/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.Pair.InvariantInterval
public import IETFree.Pair.SubintervalTransfer

/-!
# The shape of the singularity list, and the bookkeeping of Lemma 3.4

The consequences of the explicit shape, and the almost-sure bookkeeping of Lemma 3.4.

`SingularityShape` (in `GoodRegion`) records which singularity each entry of the marked list is.
This file draws three consequences that Lemma 3.4 needs:

* `GoodRegion.surj`: the list is *exhausted* by `0`, `1`, the `d - 1` cuts of `f` and the `e - 1`
  preimages of the cuts of `g`;
* `GoodRegion.mem_pairSplitting`: every pair-splitting point is one of the marked points (the
  two list-membership hypotheses of the pair-splitting lemma are discharged from `posG_pre`);
* `GoodRegion.block_endpoints`: the two endpoints of a block are marked points, with indices
  `i₀ < i₁`, so the block is a run of cells of the list; the same is true of the marked points of a
  datum (`GoodRegion.mem_markD`) and of the cuts of `f` (`mem_cutF`, `mem_cutList`).

It also holds the bookkeeping of A3 (`exists_countable_goodRegion_cover`) and the lengths of a block
**at a point of the region**,
which is what every block statement is stated with: `cellLen` (the cell lengths of the composition,
with `cellLen_pos` and `cellLen_sum`), `blockLam` (the block rescaled to mass `1`, with
`blockLam_sum`, `blockLam_coe` and the `rfl` rewrite rule `blockLam_def`), `blockLam_congr`, and the
structure API `Block.lam` (with `lam_sum`) and `Block.perm`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open IntervalExchange.IET

namespace IntervalExchange.Pair

variable {d e : ℕ} [NeZero d] [NeZero e]

/-! ## The explicit shape of the list -/

/-- **The number of cells is `d + e - 1`.** -/
theorem GoodRegion.n_eq {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)} {q₀ : PReal d e}
    (G : GoodRegion d e π σ q₀) : G.n = d + e - 1 := by
  have hr := G.subset_region q₀ G.mem_O
  exact (G.pres q₀ G.mem_O).card_eq

/-- **The list is exhausted by its four kinds of entries**: `0`, `1`, the cuts of `f` and the
preimages of the cuts of `g`.  This is a counting statement: the list has `n + 1 = d + e` entries
and the four kinds supply exactly that many different indices. -/
theorem GoodRegion.surj {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)} {q₀ : PReal d e}
    (G : GoodRegion d e π σ q₀) (k : Fin (G.n + 1)) :
    k = 0 ∨ k = Fin.last G.n ∨ (∃ i : Fin (d - 1), G.shape.posF i = k) ∨
      ∃ j : Fin (e - 1), G.shape.posG j = k := by
  -- `n + 1 = d + e` indices, as many as the four kinds supply between them
  have hcard := G.n_eq
  have hd := NeZero.pos d
  have he := NeZero.pos e
  have hn1 : 1 ≤ G.n := by omega
  -- the cuts of `f` and the preimages of the cuts of `g`, as sets of indices
  set SF : Finset (Fin (G.n + 1)) := Finset.univ.image G.shape.posF with hSF
  set SG : Finset (Fin (G.n + 1)) := Finset.univ.image G.shape.posG with hSG
  have hFcard : SF.card = d - 1 := by
    rw [hSF, Finset.card_image_of_injective _ G.shape.posF_inj, Finset.card_univ,
      Fintype.card_fin]
  have hGcard : SG.card = e - 1 := by
    rw [hSG, Finset.card_image_of_injective _ G.shape.posG_inj, Finset.card_univ,
      Fintype.card_fin]
  -- the two sets are disjoint and avoid both ends of the list
  have hdisj : Disjoint SF SG := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, hji⟩ := Finset.mem_image.mp ha'
    exact G.shape.posF_ne_posG i j hji.symm
  have h0SF : (0 : Fin (G.n + 1)) ∉ SF := by
    intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    exact G.shape.posF_ne_zero i hi
  have h0SG : (0 : Fin (G.n + 1)) ∉ SG := by
    intro h
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
    exact G.shape.posG_ne_zero j hj
  have hlSF : Fin.last G.n ∉ SF := by
    intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    exact G.shape.posF_ne_last i hi
  have hlSG : Fin.last G.n ∉ SG := by
    intro h
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
    exact G.shape.posG_ne_last j hj
  have h0l : (0 : Fin (G.n + 1)) ≠ Fin.last G.n := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  -- the union of the four kinds has the full cardinality
  have hScard : (insert (0 : Fin (G.n + 1)) (insert (Fin.last G.n) (SF ∪ SG))).card
      = G.n + 1 := by
    have hlast : Fin.last G.n ∉ SF ∪ SG := by
      rw [Finset.mem_union]
      push Not
      exact ⟨hlSF, hlSG⟩
    have hzero : (0 : Fin (G.n + 1)) ∉ insert (Fin.last G.n) (SF ∪ SG) := by
      rw [Finset.mem_insert, Finset.mem_union]
      push Not
      exact ⟨h0l, h0SF, h0SG⟩
    rw [Finset.card_insert_of_notMem hzero, Finset.card_insert_of_notMem hlast,
      Finset.card_union_of_disjoint hdisj, hFcard, hGcard]
    omega
  have heq : insert (0 : Fin (G.n + 1)) (insert (Fin.last G.n) (SF ∪ SG)) = Finset.univ := by
    refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
    rw [hScard, Finset.card_univ, Fintype.card_fin]
  have hmem : k ∈ insert (0 : Fin (G.n + 1)) (insert (Fin.last G.n) (SF ∪ SG)) := by
    rw [heq]
    exact Finset.mem_univ k
  -- so it is one of the four kinds
  rcases Finset.mem_insert.mp hmem with h | h
  · exact Or.inl h
  rcases Finset.mem_insert.mp h with h | h
  · exact Or.inr (Or.inl h)
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    exact Or.inr (Or.inr (Or.inl ⟨i, hi⟩))
  · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
    exact Or.inr (Or.inr (Or.inr ⟨j, hj⟩))

/-- The `0`-th entry of the list is `0`. -/
theorem GoodRegion.s_zero {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)} {q₀ : PReal d e}
    (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O) : G.s 0 q = 0 :=
  (G.pres q hq).zero

/-- The last entry of the list is `1`. -/
theorem GoodRegion.s_last {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)} {q₀ : PReal d e}
    (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O) :
    G.s (Fin.last G.n) q = 1 :=
  (G.pres q hq).top

/-- **`f⁻¹ 0` is the left end of the cell whose image starts at `0`.**  Note that `f 0` is not `0`
in general: the exchange sends the left end of a cell to the left end of its image. -/
theorem mkIET1_inv_zero {n : ℕ} [NeZero n] {lam : Fin n → ℝ≥0} (hpos : Positive lam)
    (π : Equiv.Perm (Fin n)) (hl : (∑ i, lam i) = 1) :
    (mkIET1' lam π hl)⁻¹ 0 = leftEnd lam (π.symm 0) := by
  have hsum : (∑ i, (lam i : ℝ)) = 1 := sum_coe_eq_one (hl)
  have himg : imageLeft π lam (π.symm 0) = 0 := by
    simp only [imageLeft]
    have hempty : Finset.univ.filter (fun j : Fin n => π j < π (π.symm 0)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j _ hj
      rw [Equiv.apply_symm_apply] at hj
      exact absurd hj (not_lt.mpr (Fin.zero_le (π j)))
    rw [hempty, Finset.sum_empty]
  have hval : mkIET1' lam π hl (leftEnd lam (π.symm 0)) = 0 := by
    have hb : (0 : ℝ) + leftEnd lam (π.symm 0) < 0 + ∑ i, (lam i : ℝ) := by
      have h1 := upperEnd_le_total lam (π.symm 0)
      rw [upperEnd_eq] at h1
      have h2 : (0 : ℝ) < (lam (π.symm 0) : ℝ) := hpos _
      linarith
    have h := mkIETFun_leftEnd (a := (0 : ℝ)) lam π (hpos _) hb
    rw [zero_add] at h
    simp only [mkIET1_eq_mkIETFun]
    rw [h, himg, add_zero]
  exact (Equiv.symm_apply_eq (mkIET1' lam π hl).toEquiv).mpr hval.symm

/-- **The cuts of `f` are on the list**, from the combinatorial type. -/
theorem GoodRegion.mem_cutF {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
    {q₀ : PReal d e} (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O) (k : Fin d) :
    ∃ i : Fin (G.n + 1), G.s i q = leftEnd (simplexMap d q.1) k :=
  ⟨G.a k.castSucc, (G.type q hq).cut k⟩

/-- **The `f`-preimages of the cuts of `g` are on the list.**  This is the strong form, in which the
preimage is evaluated as an actual `f⁻¹`: the `posG` entries of the shape are those preimages. -/
theorem GoodRegion.mem_cutList {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
    {q₀ : PReal d e} (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O) (j : Fin e) :
    ∃ i : Fin (G.n + 1), G.s i q
      = (mkIET1' (simplexMap d q.1) π (G.simplexMap_mem_simplex_fst hq))⁻¹
          (leftEnd (simplexMap e q.2) j) := by
  have hpos (i) : 0 < simplexMap d q.1 i := pos_simplexMap (G.subset_region q hq).1 i
  rcases Nat.eq_zero_or_pos j.val with h0 | hjpos
  · refine ⟨G.a (π.symm 0).castSucc, ?_⟩
    have hj0 : j = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    rw [hj0, leftEnd_zero, mkIET1_inv_zero hpos π (G.simplexMap_mem_simplex_fst hq)]
    exact (G.type q hq).cut (π.symm 0)
  · obtain ⟨c, hc⟩ : ∃ c : Fin (e - 1), c.val + 1 = j.val :=
      ⟨⟨j.val - 1, by have := j.isLt; omega⟩, by have := hjpos; simp only; omega⟩
    refine ⟨G.shape.posG c, ?_⟩
    have hidx : (⟨c.val + 1, by have := c.isLt; omega⟩ : Fin e) = j := Fin.ext hc
    rw [G.shape.posG_pre q hq c (G.simplexMap_mem_simplex_fst hq), hidx]

/-- **The `k`-th marked point, as the left end of a cell**, for `k` below the last index. -/
theorem IETDatum.mark_eq_leftEnd {n : ℕ} [NeZero n] (D : IETDatum n) {k : Fin (n + 1)}
    (hk : k.val < n) : D.mark k = leftEnd D.lam ⟨k.val, hk⟩ := by
  simp only [IETDatum.mark, leftEnd, Fin.lt_def]

/-- **The marked points of `D` are on the list.** -/
theorem GoodRegion.mem_markD {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
    {q₀ : PReal d e} (G : GoodRegion d e π σ q₀) (D : IETDatum d) {q : PReal d e}
    (hq : q ∈ G.O) (hv : D.v = q.1) (k : Fin (d + 1)) :
    ∃ i : Fin (G.n + 1), G.s i q = D.mark k := by
  have hr := G.subset_region q hq
  have hl : simplexMap d q.1 ∈ simplex (Fin d) := G.simplexMap_mem_simplex_fst hq
  have hm : simplexMap e q.2 ∈ simplex (Fin e) := G.simplexMap_mem_simplex_snd hq
  have hlam : D.lam = simplexMap d q.1 := by rw [IETDatum.lam, hv]
  rcases eq_or_ne k 0 with hk | hk
  · refine ⟨0, ?_⟩
    rw [hk, IETDatum.mark_zero, G.s_zero hq]
  rcases eq_or_ne k (Fin.last d) with hk' | hk'
  · refine ⟨Fin.last G.n, ?_⟩
    rw [hk', IETDatum.mark_last, G.s_last hq]
  · have hklt : k.val < d := by
      have h2 : k.val ≠ d := fun h => hk' (Fin.ext (by simp only [Fin.val_last]; omega))
      omega
    have hkk : k = (⟨k.val, hklt⟩ : Fin d).castSucc := Fin.ext rfl
    obtain ⟨i, hi⟩ := G.mem_cutF hq ⟨k.val, hklt⟩
    refine ⟨i, ?_⟩
    rw [hkk, IETDatum.mark_castSucc, hlam]
    exact hi

/-- **The pair-splitting points are marked points**, with the two list-membership hypotheses
discharged from the shape of the list. -/
theorem GoodRegion.mem_pairSplitting {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
    {q₀ : PReal d e} (G : GoodRegion d e π σ q₀) {D : IETDatum d} {E : IETDatum e}
    {q : PReal d e} (hq : q ∈ G.O) (hvD : D.v = q.1) (hπD : D.perm = π) (hvE : E.v = q.2)
    (hσE : E.perm = σ) {x : ℝ} (hx : IsPairSplitting D E x) :
    ∃ i : Fin (G.n + 1), G.s i q = x := by
  have hr := G.subset_region q hq
  have hl : simplexMap d q.1 ∈ simplex (Fin d) := G.simplexMap_mem_simplex_fst hq
  have hm : simplexMap e q.2 ∈ simplex (Fin e) := G.simplexMap_mem_simplex_snd hq
  -- replace `D` and `E` by the canonical data attached to `q`
  have hD : D = IETDatum.mk π q.1 hr.1 := by
    obtain ⟨a, b, c⟩ := D
    obtain rfl : a = π := hπD
    obtain rfl : b = q.1 := hvD
    obtain rfl : c = hr.1 := Subsingleton.elim c hr.1
    rfl
  have hE : E = IETDatum.mk σ q.2 hr.2 := by
    obtain ⟨a, b, c⟩ := E
    obtain rfl : a = σ := hσE
    obtain rfl : b = q.2 := hvE
    obtain rfl : c = hr.2 := Subsingleton.elim c hr.2
    rfl
  rw [hD, hE] at hx
  clear hD hE hvD hπD hvE hσE
  rcases hx with rfl | rfl | ⟨k, -, rfl, -⟩ | ⟨j, -, rfl, hf⟩
  · exact ⟨0, G.s_zero hq⟩
  · exact ⟨Fin.last G.n, G.s_last hq⟩
  · exact G.mem_markD _ hq rfl k
  · -- `E.mark j` lies in a fixed cell of `D`, so `D` fixes it, hence it is its own preimage,
    -- and the preimages of the marked points of `E` are on the list
    have hfix : (IETDatum.mk π q.1 hr.1).toIET (IETDatum.mark (IETDatum.mk σ q.2 hr.2) j)
        = IETDatum.mark (IETDatum.mk σ q.2 hr.2) j :=
      mark_fixed_of_inFixedCell (IETDatum.mk π q.1 hr.1) (IETDatum.mk σ q.2 hr.2) j hf
    have hfix' : (IETDatum.mk π q.1 hr.1).toFun (IETDatum.mark (IETDatum.mk σ q.2 hr.2) j)
        = IETDatum.mark (IETDatum.mk σ q.2 hr.2) j := hfix
    rcases eq_or_ne j 0 with hj | hj
    · refine ⟨0, ?_⟩
      rw [G.s_zero hq, hj, IETDatum.mark_zero]
    rcases eq_or_ne j (Fin.last e) with hj' | hj'
    · refine ⟨Fin.last G.n, ?_⟩
      rw [G.s_last hq, hj', IETDatum.mark_last]
    · have hjlt : j.val < e := by
        have h2 : j.val ≠ e := fun h => hj' (Fin.ext (by simp only [Fin.val_last]; omega))
        omega
      have hmark : IETDatum.mark (IETDatum.mk σ q.2 hr.2) j
          = leftEnd (simplexMap e q.2) ⟨j.val, hjlt⟩ := by
        rw [IETDatum.mark_eq_leftEnd _ hjlt]
        rfl
      obtain ⟨i, hi⟩ := G.mem_cutList hq ⟨j.val, hjlt⟩
      refine ⟨i, ?_⟩
      rw [hi, hmark]
      -- `D` fixes the point, so its `D`-preimage is the point itself
      have hpre : (mkIET1' (simplexMap d q.1) π hl)⁻¹
          (leftEnd (simplexMap e q.2) ⟨j.val, hjlt⟩)
          = leftEnd (simplexMap e q.2) ⟨j.val, hjlt⟩ := by
        have h2 : (mkIET1' (simplexMap d q.1) π hl)⁻¹
            (IETDatum.mark (IETDatum.mk σ q.2 hr.2) j)
            = IETDatum.mark (IETDatum.mk σ q.2 hr.2) j := by
          refine (IETDatum.mk π q.1 hr.1).toIET.injective ?_
          -- with the `toIET` coercion exposed, the form `apply_symm_apply'` rewrites
          change (IETDatum.mk π q.1 hr.1).toIET
              ((IETDatum.mk π q.1 hr.1).toIET⁻¹
                (IETDatum.mark (IETDatum.mk σ q.2 hr.2) j))
            = (IETDatum.mk π q.1 hr.1).toIET (IETDatum.mark (IETDatum.mk σ q.2 hr.2) j)
          rw [apply_symm_apply']
          exact ((IETDatum.toIET_apply _ _).trans hfix).symm
        rw [hmark] at h2
        exact h2
      rw [hpre]

/-- **The endpoints of a block are marked points**, and the left one comes first in the list: so a
block is exactly a run of cells `[s i₀, s i₁)` of the marked list. -/
theorem GoodRegion.block_endpoints {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
    {q₀ : PReal d e} (G : GoodRegion d e π σ q₀) {D : IETDatum d} {E : IETDatum e}
    {q : PReal d e} (hq : q ∈ G.O) (hvD : D.v = q.1) (hπD : D.perm = π) (hvE : E.v = q.2)
    (hσE : E.perm = σ) {u v : ℝ} (hb : IsBlock D E u v) :
    ∃ i₀ i₁ : Fin (G.n + 1), G.s i₀ q = u ∧ G.s i₁ q = v ∧ i₀ < i₁ := by
  have hr := G.subset_region q hq
  have hl : simplexMap d q.1 ∈ simplex (Fin d) := G.simplexMap_mem_simplex_fst hq
  have hm : simplexMap e q.2 ∈ simplex (Fin e) := G.simplexMap_mem_simplex_snd hq
  obtain ⟨i₀, hi₀⟩ := G.mem_pairSplitting hq hvD hπD hvE hσE hb.left
  obtain ⟨i₁, hi₁⟩ := G.mem_pairSplitting hq hvD hπD hvE hσE hb.right
  refine ⟨i₀, i₁, hi₀, hi₁, ?_⟩
  refine (monoAt G hq).lt_iff_lt.mp ?_
  rw [hi₀, hi₁]
  exact hb.lt

/-! ### From a countable family of regions to an almost-sure statement

Lemma 3.4 is proved one good region at a time: on a region `O` the singularity list and the
permutation of `g ∘ f` are fixed, so Masur–Veech and Veech's rigidity can be applied to the
*rescaled block* and pulled back by absolute continuity.  The regions are produced pointwise by
`exists_goodRegion`, and to pass from "almost everywhere on each region" to "almost everywhere" one
needs only countably many of them: the parameter space is second-countable, hence hereditarily
Lindelöf, so the cover of the good set by the regions has a countable subcover. -/

/-- **A countable family of good regions covering the good set.**  The index type is the subtype of
the countable subcover, so it is countable and the regions are genuine `GoodRegion`s. -/
theorem exists_countable_goodRegion_cover {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) :
    ∃ (ι : Type) (_ : Countable ι) (G : ι → Σ q : PReal d e, GoodRegion d e π σ q),
      ∀ z ∈ goodParams d e, z.1 ∈ simplexRegion d → z.2 ∈ simplexRegion e →
        ∃ i, z ∈ (G i).2.O := by
  set s : Set (PReal d e) := goodParams d e ∩ {z | z.1 ∈ simplexRegion d ∧ z.2 ∈ simplexRegion e}
    with hsdef
  have hcover : s ⊆ ⋃ i : (Σ q : PReal d e, GoodRegion d e π σ q), (i.2).O := by
    rintro z ⟨hz, h1, h2⟩
    obtain ⟨G⟩ := exists_goodRegion π σ z hz ⟨h1, h2⟩
    exact Set.mem_iUnion.mpr ⟨⟨z, G⟩, G.mem_O⟩
  obtain ⟨r, hrcount, hrcov⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_countable_subcover
    (fun i : (Σ q : PReal d e, GoodRegion d e π σ q) => (i.2).O) (fun i => i.2.isOpen_O) hcover
  refine ⟨r, hrcount, (fun i => i.1), ?_⟩
  intro z hz h1 h2
  obtain ⟨i, hir, hzi⟩ := Set.mem_iUnion₂.mp (hrcov ⟨hz, h1, h2⟩)
  exact ⟨⟨i, hir⟩, hzi⟩

/-- `blockLam` depends only on the length vector, not on the proof of positivity. -/
theorem blockLam_congr {n : ℕ} {lam lam' : Fin n → ℝ≥0} (h : lam = lam') {k l : ℕ}
    (hkl : k < l) (hln : l ≤ n) (hpos : Positive lam) (hpos' : Positive lam') :
    blockLam lam k hkl hln hpos = blockLam lam' k hkl hln hpos' := by
  cases h
  rfl

/-! ## The cell lengths and the block lengths of a region at a point

Almost everything in the block reduction is a statement about the length vector
`compLenVec G.s q (monoAt G hq)` of the composition at a single point of the region, and about the
rescaled block length vector `blockLam` of that vector.  Both get a name here, together with the two
facts every use needs: that the entries are positive, and that they add up to `1`.  This keeps
`monoAt` and the positivity proof out of the statements below, where they would otherwise be
repeated at every occurrence. -/

namespace GoodRegion

variable {d e : ℕ} [NeZero d] [NeZero e] {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
  {q₀ : PReal d e}

/-- **The lengths of the cells of the composition at a point of the region**, in the order of the
singularity list `G.s`. -/
noncomputable def cellLen (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O) :
    Fin G.n → ℝ≥0 :=
  compLenVec G.s q (monoAt G hq)

/-- **The unfolding of `cellLen`**: the cell lengths are `compLen` of the singularity list at the
point, and do not depend on which proof of monotonicity is supplied. -/
theorem cellLen_eq (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O)
    (hmono : StrictMono fun k => G.s k q) : G.cellLen hq = compLen hmono := (rfl)

/-- The cell lengths are positive. -/
theorem cellLen_pos (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O) (i : Fin G.n) :
    0 < G.cellLen hq i :=
  sub_pos.mpr (monoAt G hq (Fin.castSucc_lt_succ (i := i)))

/-- **The cells of the composition add up to `1`.** -/
theorem cellLen_sum (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O) :
    (∑ i, G.cellLen hq i) = 1 := by
  have P := G.pres q hq
  exact compLen_sum (monoAt G hq) P.zero P.top

/-- **The rescaled length vector of the block of cells `k, …, l - 1` at a point of the region**. -/
noncomputable def blockLam (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O)
    (k : ℕ) {l : ℕ} (hkl : k < l) (hln : l ≤ G.n) : Fin (l - k) → ℝ≥0 :=
  IntervalExchange.Pair.blockLam (G.cellLen hq) k hkl hln (G.cellLen_pos hq)

/-- The defining equation of `G.blockLam`, as a rewrite rule (the proof of positivity is
irrelevant, so this can be used to compare a `G.blockLam` with the `blockLam` of a length
vector). -/
@[simp] theorem blockLam_def (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O)
    (k : ℕ) {l : ℕ} (hkl : k < l) (hln : l ≤ G.n) :
    G.blockLam hq k hkl hln
      = IntervalExchange.Pair.blockLam (G.cellLen hq) k hkl hln (G.cellLen_pos hq) := (rfl)

/-- **The rescaled block lengths add up to `1`**, so that the block exchange is defined. -/
theorem blockLam_sum (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O)
    (k : ℕ) {l : ℕ} (hkl : k < l) (hln : l ≤ G.n) :
    (∑ j, G.blockLam hq k hkl hln j) = 1 :=
  IntervalExchange.Pair.blockLam_sum (G.cellLen hq) k hkl hln (G.cellLen_pos hq)

theorem blockLam_coe (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O)
    (k : ℕ) {l : ℕ} (hkl : k < l) (hln : l ≤ G.n) (j : Fin (l - k)) :
    (G.blockLam hq k hkl hln j : ℝ)
      = (G.cellLen hq ⟨k + j.val, by omega⟩ : ℝ) / blockMass (G.cellLen hq) k hln :=
  IntervalExchange.Pair.blockLam_coe (G.cellLen hq) k hkl hln (G.cellLen_pos hq) j

/-! ### The length vector and the permutation of a block

The two pieces of data that a block determines: its rescaled length vector at a point of the region
(`Block.lam`, with `lam_sum`) and the permutation of its cells (`Block.perm`). -/

namespace Block

variable {d e : ℕ} [NeZero d] [NeZero e] {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
  {q₀ : PReal d e} {G : GoodRegion d e π σ q₀}

/-- **The rescaled length vector of a block** at a point of the region. -/
noncomputable def lam (B : Block G) {q : PReal d e} (hq : q ∈ G.O) :
    Fin (B.l - B.k) → ℝ≥0 :=
  G.blockLam hq B.k B.hkl B.hln

/-- The rescaled block lengths add up to `1`. -/
theorem lam_sum (B : Block G) {q : PReal d e} (hq : q ∈ G.O) : (∑ j, B.lam hq j) = 1 :=
  G.blockLam_sum hq B.k B.hkl B.hln

/-- **The permutation of the cells of a block**, as a permutation of `Fin (l - k)`: `ρ` shifted by
`k`.  Its invariance hypothesis is part of the block. -/
noncomputable def perm (B : Block G) : Equiv.Perm (Fin (B.l - B.k)) :=
  blockPerm G.ρ B.k B.hkl B.hln B.hstab

end Block

end GoodRegion

/-! The assembly of Lemma 3.4 has to combine almost-sure statements stated for two different
measures: `ae_goodParams_real` and `ae_diophantine_real` are stated for the product of the two
restricted Lebesgue measures on the free regions, while the block statements (`ae_BlockGoodPt`) are
stated for the restriction of Lebesgue measure to the region `O` of a `GoodRegion`.  The two are
reconciled by absolute continuity against the ambient Lebesgue measure on the parameter space. -/

end IntervalExchange.Pair

end
