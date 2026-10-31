/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.BlockAssembly
import IETFree.BlockDatum
import IETFree.BlockData
import IETFree.BlockDiophantine
import IETFree.GeneratorChange

/-!
Lemma 3.4 and Theorem 1.1.

`exists_word_trivial_of_region` (A4) is the pointwise conclusion of Lemma 3.4: at a point of a good
region, from the almost-sure block data *at that point* (unique ergodicity and rigidity of every
block permutation, and the Diophantine condition for every block) every block of every pair of data
with those parameters carries a nontrivial word which is the identity on it.
`isDiophantine_blockPair` (A2) is the Diophantine condition at a block, from the integer-affine
description of the block lengths.

`exists_word_trivial_on_block` is Lemma 3.4 itself: it combines the almost-sure data of
`BlockData.exists_ae_block_good` (A3) with A4, A2 over the length vectors.  `main_theorem_of_blocks`
is Theorem 1.1 for the per-block words, and `exists_word_trivial_on_all_of_blocks` (in
`IETFree.BlockAssembly`) is what turns the per-block words of that statement into one word.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

-- `NeZero (l - k)` is an *instance* in the telescopes below (`mkIET1` needs it as such), so `haveI`
-- is the right binder; the style linter only sees that its value is a `Prop`.
set_option linter.style.haveILetI false
namespace GoodRegion

variable {d e : ℕ} [NeZero d] [NeZero e] {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
  {q₀ : PReal d e}

/-- **A4, the pointwise conclusion of Lemma 3.4.**  At a point `q` of a good region, given the
almost-sure block data *at that point* (unique ergodicity and rigidity for every block permutation,
and the Diophantine condition for every block), every block `[u,v)` of every pair of data with those
parameters carries a nontrivial word which is the identity on it. -/
theorem exists_word_trivial_of_region (G : GoodRegion d e π σ q₀) [NeZero G.n]
    {q : PReal d e} (hq : q ∈ G.O) (hgood : ¬ IsBadParam q)
    (hue : ∀ B : Block G, IsIrreduciblePerm B.perm → 2 ≤ B.l - B.k →
      ∀ h : B.lam hq ∈ simplex (B.l - B.k),
        UniqueErgodic (mkIET1 (B.lam hq) B.perm h))
    (hrig : ∀ B : Block G, IsIrreduciblePerm B.perm → 2 ≤ B.l - B.k →
      ∀ h : B.lam hq ∈ simplex (B.l - B.k),
        IsRigidByTranslations (mkIET1 (B.lam hq) B.perm h))
    (hdio : ∀ (i₀ i₁ : Fin (G.n + 1)) (hi : i₀ < i₁),
      IsDiophantine (G.blockLam hq i₀.val (l := i₁.val) hi (by omega))
        (RestrictIET.truncatedLengths (simplexMap e q.2) (G.s i₀ q) (G.s i₁ q) (monoAt G hq hi)))
    {D : IETDatum d} {E : IETDatum e} (h : G.Fits q D E)
    {u v : ℝ} (hb : IsBlock D E u v) :
    ∃ w : FreeGroup Gen, w ≠ 1 ∧ ∀ x : ℝ, u ≤ x → x < v → (evalWord w D.toIET E.toIET) x = x := by
  classical
  obtain ⟨hp, hw⟩ := G.subset_region q hq
  obtain ⟨i₀, i₁, hu, hv, hi⟩ := G.block_endpoints hq h.hDv h.hDπ h.hEv h.hEπ hb
  have hm : simplexMap e q.2 ∈ simplex e := G.simplexMap_mem_simplex_snd hq
  obtain rfl : u = G.s i₀ q := hu.symm
  obtain rfl : v = G.s i₁ q := hv.symm
  have hkl : i₀.val < i₁.val := hi
  have hln : i₁.val ≤ G.n := by have := i₁.isLt; omega
  have hne : NeZero (i₁.val - i₀.val) := ⟨by omega⟩
  haveI := hne
  have hpos := G.cellLen_pos hq
  -- the two rescaled exchanges of the block
  set F' : IET 0 1 := mkIET1 (G.blockLam hq i₀.val (l := i₁.val) hi (by omega))
    (G.blockPermOf hq h hi hb.left hb.right)
    (G.blockLam_sum hq i₀.val hi (by omega)) with hF'def
  set G' : IET 0 1 := mkIET1 (RestrictIET.truncatedLengths (simplexMap e q.2) (G.s i₀ q) (G.s i₁ q)
      (monoAt G hq hi)) σ (RestrictIET.sum_truncatedLengths (simplexMap e q.2) hm
        (by exact (hb.left.mem_Icc).1) (monoAt G hq hi) (by exact (hb.right.mem_Icc).2)) with hG'def
  -- the two halves of the pointwise conjugacy
  have hconjF : ∀ y ∈ Set.Ico (0 : ℝ) 1,
      (E.toIET * D.toIET) (rescaleMapInv (G.s i₀ q) (G.s i₁ q) y)
        = rescaleMapInv (G.s i₀ q) (G.s i₁ q) (F' y) := by
    intro y hy
    rw [hF'def]
    exact G.comp_conj_rescale hq h hi hb.left hb.right hy
  have hconjG : ∀ y ∈ Set.Ico (0 : ℝ) 1,
      E.toIET (rescaleMapInv (G.s i₀ q) (G.s i₁ q) y)
        = rescaleMapInv (G.s i₀ q) (G.s i₁ q) (G' y) := by
    intro y hy
    rw [hG'def]
    exact G.restrict_rescale hq h hi hb.left hb.right hy
  have hex : ∃ w : FreeGroup Gen, w ≠ 1 ∧ evalWord w F' G' = 1 := by
    by_cases h1 : i₁.val - i₀.val = 1
    · -- a single composition cell: the rescaled composition is the identity
      have hall : ∀ j : Fin (i₁.val - i₀.val),
          G.blockLam hq i₀.val (l := i₁.val) hi (by omega) j = 1 := by
        intro j
        rw [blockLam_def, blockLam_of_one hkl hln (G.cellLen_pos hq) h1]
      have hF'1 : F' = 1 := by
        rw [hF'def]
        exact mkIET1_of_all_one _ _ hall
      refine ⟨genX, genX_ne_one, ?_⟩
      rw [evalWord_genX, hF'1]
    · -- at least two cells: Theorem 2.6 on the block
      have h2 : 2 ≤ i₁.val - i₀.val := by omega
      let hB : Block G := G.blockOf hq h hi hb.left hb.right
      have hcompIrr : IsCompIrreducibleOn D E (G.s i₀ q) (G.s i₁ q) :=
        block_irreducible_on_good D E (by rw [h.hDv, h.hEv]; exact hgood) _ _ hb
      have hirrPerm : IsIrreduciblePerm hB.perm :=
        G.isIrreduciblePerm_blockPermOf hq h hi hb.left hb.right hcompIrr
      obtain ⟨w, hw, hw1⟩ := irreducible_case (G.blockPermOf hq h hi
        hb.left hb.right) σ
        (G.blockLam hq i₀.val (l := i₁.val) hi (by omega))
        (RestrictIET.truncatedLengths (simplexMap e q.2) (G.s i₀ q) (G.s i₁ q) (monoAt G hq hi))
        (G.blockLam_sum hq i₀.val hi (by omega))
        (RestrictIET.sum_truncatedLengths (simplexMap e q.2) hm (by exact (hb.left.mem_Icc).1)
          (monoAt G hq hi) (by exact (hb.right.mem_Icc).2))
        (hue hB hirrPerm h2 (hB.lam_sum hq))
        (hrig hB hirrPerm h2 (hB.lam_sum hq))
        (hdio i₀ i₁ hi)
      exact ⟨w, hw, hw1⟩
  exact exists_word_trivial_on_block_of_rescaled (monoAt G hq hi) hconjF hconjG hex

/-- **A2, the Diophantine condition at the block.**  If the pair `(f, g)` is Diophantine at `q`,
then so is the rescaled pair of the block `[s i₀, s i₁)`: its composition lengths and its `g`-piece
lengths are integer linear combinations of the parameters (`Fs`, `Hs`), so the paper's "multiply by
`u`" step applies. -/
theorem isDiophantine_blockPair (G : GoodRegion d e π σ q₀)
    {q : PReal d e} (hq : q ∈ G.O)
    {i₀ i₁ : Fin (G.n + 1)} (hi : i₀ < i₁)
    (hdio : IsDiophantine (simplexMap d q.1) (simplexMap e q.2)) :
    IsDiophantine (G.blockLam hq i₀.val (l := i₁.val) hi (by omega))
      (RestrictIET.truncatedLengths (simplexMap e q.2) (G.s i₀ q) (G.s i₁ q) (monoAt G hq hi)) := by
  classical
  have hkl : i₀.val < i₁.val := hi
  have hln : i₁.val ≤ G.n := by have := i₁.isLt; omega
  obtain ⟨hp, hw⟩ := G.subset_region q hq
  have hsl : simplexMap d q.1 ∈ simplex d := simplexMap_mem_simplex_fin hp.1 hp.2
  have hsm : simplexMap e q.2 ∈ simplex e := simplexMap_mem_simplex_fin hw.1 hw.2
  have hmonoq : StrictMono fun k => G.s k q := monoAt G hq
  have hzero : G.s 0 q = 0 := (G.pres q hq).zero
  have htop : G.s (Fin.last G.n) q = 1 := (G.pres q hq).top
  set L : ℝ := G.s i₁ q - G.s i₀ q with hLdef
  have hL0 : 0 < L := by
    rw [hLdef]
    exact sub_pos.mpr (hmonoq hi)
  have hL1 : L ≤ 1 := by
    rw [hLdef]
    have h1 : G.s i₁ q ≤ G.s (Fin.last G.n) q := hmonoq.monotone (Fin.le_last i₁)
    have h1' : G.s i₁ q ≤ 1 := by rw [htop] at h1; exact h1
    have h0 : G.s 0 q ≤ G.s i₀ q := hmonoq.monotone (Fin.zero_le i₀)
    have h0' : (0 : ℝ) ≤ G.s i₀ q := by rw [hzero] at h0; exact h0
    linarith [hLdef, h1', h0']
  obtain ⟨Hs, hHs, hHsval⟩ := G.exists_isIntAffine_truncatedLengths hq
  have hHnn : ∀ j, 0 ≤ Hs j q := by
    intro j
    rw [hHsval j]
    exact le_max_left _ _
  -- the composition lengths of the block
  set Fs : Fin (i₁.val - i₀.val) → ParamAffine d e :=
    fun j => G.sAffine ⟨i₀.val + j.val + 1, by have := j.isLt; omega⟩
      - G.sAffine ⟨i₀.val + j.val, by omega⟩ with hFsdef
  have hFs : ∀ j, IsIntAffine (Fs j) := fun j =>
    (G.isIntAffine_sAffine _).sub (G.isIntAffine_sAffine _)
  have hFval : ∀ j : Fin (i₁.val - i₀.val), (Fs j) q
      = ((G.cellLen hq ⟨i₀.val + j.val, by omega⟩ : ℝ≥0) : ℝ) := by
    intro j
    have hcoe := G.compLenVec_coe_eq hq ⟨i₀.val + j.val, by omega⟩
    have hsucc : ((⟨i₀.val + j.val, by omega⟩ : Fin G.n).succ)
        = ⟨i₀.val + j.val + 1, by omega⟩ := Fin.ext rfl
    have hcast : ((⟨i₀.val + j.val, by omega⟩ : Fin G.n).castSucc)
        = ⟨i₀.val + j.val, by omega⟩ := Fin.ext rfl
    rw [hFsdef]
    simp only [AffineMap.coe_sub, Pi.sub_apply]
    rw [← hsucc, ← hcast, ← hcoe]
  have hFnn : ∀ j, 0 ≤ (Fs j) q := fun j => by rw [hFval j]; exact NNReal.coe_nonneg _
  -- the block mass in terms of `L`
  have hmass : blockMass (G.cellLen hq) i₀.val hln = L := by
    have hadd : G.s i₀ q + blockMass (G.cellLen hq) i₀.val hln = G.s i₁ q := by
      have h := leftEnd_add_blockMass_compLen (monoAt G hq) hzero hi hln
      rw [leftEnd_compLen (monoAt G hq) hzero ⟨i₀.val, by omega⟩] at h
      exact h
    rw [hLdef]
    linarith [hadd]
  -- the packaging lemma
  have hdio' := IsDiophantine.of_intAffine_family hdio (Fs := Fs) (Hs := Hs) hFs hHs
    (by have := NeZero.pos e; omega) (q := q) (G.subset_region q hq) rfl rfl hL0 hL1 hFnn hHnn
  -- identify the two families with the block data
  have hFeq : (fun i => (⟨(Fs i) q / L, div_nonneg (hFnn i) hL0.le⟩ : ℝ≥0))
      = G.blockLam hq i₀.val (l := i₁.val) hi (by omega) := by
    funext i
    apply Subtype.ext
    change (Fs i) q / L = ((G.blockLam hq i₀.val (l := i₁.val) hi (by omega) i : ℝ≥0) : ℝ)
    rw [blockLam_coe, hmass, hFval i]
  have hHeq : (fun j => (⟨(Hs j) q / L, div_nonneg (hHnn j) hL0.le⟩ : ℝ≥0))
      = RestrictIET.truncatedLengths (simplexMap e q.2) (G.s i₀ q) (G.s i₁ q) (monoAt G hq hi) := by
    funext j
    apply Subtype.ext
    change (Hs j) q / L
      = max 0 (min (G.s i₁ q) (upperEnd (simplexMap e q.2) j : ℝ)
          - max (G.s i₀ q) (leftEnd (simplexMap e q.2) j : ℝ)) / (G.s i₁ q - G.s i₀ q)
    rw [hHsval j]
  rw [hFeq, hHeq] at hdio'
  exact hdio'

end GoodRegion

/-! ### Lemma 3.4

The last open step of Section 3: the per-block word, from the almost-sure block data of
`BlockData.exists_ae_block_good` (A3) and the pointwise conclusion of Lemma 3.2 (A4). -/

/-- **Lemma 3.4** (the per-block word), in free coordinates: for almost every point `z` of the free
region, every pair of data with those lengths and permutations, and every block of the pair, there
is a nontrivial word which is the identity on the block.

It applies Theorem 2.6 to the rescaled pair `(ẼD̃, Ẽ)` on the block, after Lemma 3.1 (absolute
continuity, `BlockData.exists_ae_block_good`) and Lemma 3.2 (irreducibility, `A4`). -/
theorem exists_word_trivial_on_block {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e))
    (hMV : MasurVeech) (hVR : VeechRigidity) :
    ∀ᵐ z ∂((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))),
      ∀ (D : IETDatum d) (E : IETDatum e), D.π = π → E.π = σ → D.v = z.1 → E.v = z.2 →
        ∀ u v : ℝ, IsBlock D E u v →
          ∃ w : FreeGroup Gen, w ≠ 1 ∧
            ∀ x : ℝ, u ≤ x → x < v → (evalWord w D.toIET E.toIET) x = x := by
  obtain ⟨ι, hι, Gfam, hcov, hae⟩ := BlockData.exists_ae_block_good π σ hMV hVR
  haveI := hι
  filter_upwards [hae] with z hz
  obtain ⟨hbad, hz1, hz2, hdio, hblk⟩ := hz
  intro D E hDπ hEπ hDv hEv u v hb
  obtain ⟨i, hzO⟩ := hcov z hbad hz1 hz2
  exact GoodRegion.exists_word_trivial_of_region (G := (Gfam i).2) hzO hbad
    (fun B hirr h2 h => (hblk i hzO B hirr h2).1 h)
    (fun B hirr h2 h => (hblk i hzO B hirr h2).2 h)
    (fun i₀ i₁ hi => GoodRegion.isDiophantine_blockPair (G := (Gfam i).2) hzO hi hdio)
    ⟨hDπ, hDv, hEπ, hEv⟩ hb

/-- **Theorem 1.1 from Lemma 3.4 plus the assembly.**  The blocks and the per-block words are
hypotheses here: the blocks are the intervals between consecutive pair-splitting singularities
(given by an enumeration `u v` of the pair-splitting points of the pair, which
`IsPairSplitting.iff_mem` turns into the invariance hypotheses of the assembly), and
`exists_word_trivial_on_block` supplies the words. -/
theorem main_theorem_of_blocks {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) (hMV : MasurVeech) (hVR : VeechRigidity) :
    ∀ᵐ z ∂((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))),
      ∀ (D : IETDatum d) (E : IETDatum e), D.π = π → E.π = σ → D.v = z.1 → E.v = z.2 →
        ∃ (n : ℕ) (u v : Fin n → ℝ),
          (∀ x ∈ Set.Ico (0 : ℝ) 1, ∃ i, u i ≤ x ∧ x < v i) ∧
            (∀ (i : Fin n) (x : ℝ), x ∈ Set.Ico (0 : ℝ) 1 →
              (u i ≤ x ∧ x < v i ↔ u i ≤ D.toFun x ∧ D.toFun x < v i)) ∧
            (∀ (i : Fin n) (x : ℝ), x ∈ Set.Ico (0 : ℝ) 1 →
              (u i ≤ x ∧ x < v i ↔ u i ≤ E.toFun x ∧ E.toFun x < v i)) ∧
              ∀ i : Fin n, ∃ w : FreeGroup Gen, w ≠ 1 ∧
                ∀ x : ℝ, u i ≤ x → x < v i → (evalWord w D.toIET E.toIET) x = x := by
  classical
  filter_upwards [exists_word_trivial_on_block (d := d) (e := e) π σ hMV hVR] with z hz
  intro D E hD hE hvD hvE
  -- the set of pair-splitting points
  set T : Finset ℝ := insert 0 (insert 1 ((D.markCuts ∪ E.markCuts).filter
    (fun x => IsPairSplitting D E x))) with hTdef
  have hT0 : (0 : ℝ) ∈ T := Finset.mem_insert_self _ _
  have hT1 : (1 : ℝ) ∈ T := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hTps : ∀ x ∈ T, IsPairSplitting D E x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inl rfl
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inr (Or.inl rfl)
    · exact (Finset.mem_filter.mp hx).2
  have hTin : ∀ x, IsPairSplitting D E x → x ∈ T := by
    intro x hx
    rcases hx with rfl | rfl | ⟨k, hk, rfl, hfix⟩ | ⟨j, hj, rfl, hfix⟩
    · exact hT0
    · exact hT1
    · have hx0 : D.mark k ∈ insert (0 : ℝ) (insert (1 : ℝ) D.markCuts) := mark_mem_insert D k
      rcases Finset.mem_insert.mp hx0 with h0 | hx0
      · rw [h0]; exact hT0
      rcases Finset.mem_insert.mp hx0 with h1 | hc
      · rw [h1]; exact hT1
      · refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
          ⟨Finset.mem_union_left _ hc, Or.inr (Or.inr (Or.inl ⟨k, hk, rfl, hfix⟩))⟩))
    · have hx0 : E.mark j ∈ insert (0 : ℝ) (insert (1 : ℝ) E.markCuts) := mark_mem_insert E j
      rcases Finset.mem_insert.mp hx0 with h0 | hx0
      · rw [h0]; exact hT0
      rcases Finset.mem_insert.mp hx0 with h1 | hc
      · rw [h1]; exact hT1
      · refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
          ⟨Finset.mem_union_right _ hc, Or.inr (Or.inr (Or.inr ⟨j, hj, rfl, hfix⟩))⟩))
  have hTbounds : ∀ x ∈ T, 0 ≤ x ∧ x ≤ 1 := fun x hx => (hTps x hx).mem_Icc
  have hcard : 0 < T.card := Finset.card_pos.mpr ⟨0, hT0⟩
  -- the increasing enumeration of `T`
  set iso := Finset.orderIsoOfFin T rfl with hiso
  have htmono : StrictMono fun k : Fin T.card => (iso k : ℝ) := fun a b h => iso.strictMono h
  have ht0 : (iso ⟨0, hcard⟩ : ℝ) = 0 := by
    have h1 : (iso ⟨0, hcard⟩ : ℝ) = T.min' ⟨0, hT0⟩ := by
      rw [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_zero rfl hcard]
    rw [h1]
    refine le_antisymm (Finset.min'_le T 0 hT0) ?_
    exact (hTbounds _ (Finset.min'_mem T ⟨0, hT0⟩)).1
  have htlast : (iso ⟨T.card - 1, by omega⟩ : ℝ) = 1 := by
    have h1 : (iso ⟨T.card - 1, by omega⟩ : ℝ) = T.max' ⟨0, hT0⟩ := by
      rw [Finset.coe_orderIsoOfFin_apply]
      exact Finset.orderEmbOfFin_last rfl hcard
    rw [h1]
    refine le_antisymm ?_ (Finset.le_max' T 1 hT1)
    exact (hTbounds _ (Finset.max'_mem T ⟨0, hT0⟩)).2
  -- the blocks
  refine ⟨T.card - 1, fun i => (iso (Fin.castLE (by omega) i.castSucc) : ℝ),
    fun i => (iso (Fin.castLE (by omega) i.succ) : ℝ), ?_, ?_, ?_, ?_⟩
  · -- the blocks cover `[0, 1)`
    have hmono : StrictMono fun j : Fin (T.card - 1 + 1) =>
        (iso (Fin.castLE (by omega) j) : ℝ) := fun a b h =>
      htmono (Fin.strictMono_castLE _ h)
    have hz0 : (iso (Fin.castLE (by omega) (0 : Fin (T.card - 1 + 1))) : ℝ) = 0 := by
      rw [show Fin.castLE (by omega) (0 : Fin (T.card - 1 + 1)) = ⟨0, hcard⟩ from Fin.ext rfl]
      exact ht0
    have hzl : (iso (Fin.castLE (by omega) (Fin.last (T.card - 1))) : ℝ) = 1 := by
      rw [show Fin.castLE (by omega) (Fin.last (T.card - 1)) = ⟨T.card - 1, by omega⟩ from
        Fin.ext (by simp)]
      exact htlast
    intro x hx
    exact exists_cell_of_strictMono hmono hz0 hzl hx
  · -- invariance of each block under `D`
    intro i x hx
    have hu : (iso (Fin.castLE (by omega) i.castSucc) : ℝ) ∈ T := (iso _).2
    have hv : (iso (Fin.castLE (by omega) i.succ) : ℝ) ∈ T := (iso _).2
    exact (IsPairSplitting.iff_mem (hTps _ hu) (hTps _ hv) hx).1
  · -- invariance under `E`
    intro i x hx
    have hu : (iso (Fin.castLE (by omega) i.castSucc) : ℝ) ∈ T := (iso _).2
    have hv : (iso (Fin.castLE (by omega) i.succ) : ℝ) ∈ T := (iso _).2
    exact (IsPairSplitting.iff_mem (hTps _ hu) (hTps _ hv) hx).2
  · -- the word on each block, from Lemma 3.4
    intro i
    have hu : (iso (Fin.castLE (by omega) i.castSucc) : ℝ) ∈ T := (iso _).2
    have hv : (iso (Fin.castLE (by omega) i.succ) : ℝ) ∈ T := (iso _).2
    have hlt : (iso (Fin.castLE (by omega) i.castSucc) : ℝ)
        < (iso (Fin.castLE (by omega) i.succ) : ℝ) := by
      refine htmono (Fin.strictMono_castLE _ ?_)
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
      omega
    refine hz D E hD hE hvD hvE _ _ ⟨hTps _ hu, hTps _ hv, hlt, ?_⟩
    intro w hw h1 h2
    have hwT : w ∈ T := hTin w hw
    obtain ⟨j, hj⟩ := iso.surjective ⟨w, hwT⟩
    have hwj : (iso j : ℝ) = w := by rw [hj]
    have h1' : Fin.castLE (by omega) i.castSucc < j := by
      exact htmono.lt_iff_lt.mp (by rw [hwj]; exact h1)
    have h2' : j < Fin.castLE (by omega) i.succ := by
      refine htmono.lt_iff_lt.mp ?_
      rw [hwj]
      exact h2
    simp only [Fin.lt_def, Fin.val_castLE, Fin.val_castSucc, Fin.val_succ] at h1' h2'
    omega
