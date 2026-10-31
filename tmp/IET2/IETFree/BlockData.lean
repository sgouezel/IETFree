/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.BlockEndpoints
import IETFree.BlockAETransfer
import IETFree.BlockDiophantine

/-!
The almost-sure block data of Lemma 3.4 over a countable family of good regions (A3).

Lemma 3.4 is proved one good region at a time: on a region `O` the singularity list and the
permutation of `g ∘ f` are fixed, so Masur–Veech and Veech's rigidity can be applied to the
*rescaled block* and pulled back by absolute continuity (Lemma 3.1).  The regions are produced
pointwise, and this file turns the pointwise statements into one almost-sure statement over the
whole parameter space:

* the pointwise length vector `compLenVec` and the absolute continuity of the affine length map
  at a point of the region (`compLenAffine_absolutelyContinuousAt`,
  `compLen_absolutelyContinuousAt`), which is where the global-monotonicity versions of
  `IETFree.LengthMap` are superseded;
* `BlockGood` and `ae_blockGood`: for almost every parameter of the region, every block
  `[s k, s l)` of the composition (a `GoodRegion.Block`) whose permutation is irreducible gives an
  exchange which is uniquely ergodic and rigid by translations (Masur–Veech and Veech), with
  `blockLamAt_eq` identifying the block length vector with the free coordinates.  There are only
  countably many blocks (`GoodRegion.Block.countable`), so this is a countable intersection;
* `BlockGoodAt`, `ae_BlockGoodPt`: the same at a point of the region, in the form the pointwise
  assembly consumes;
* `ae_block_good` and `exists_ae_block_good`: a countable cover of the good set by regions
  (`exists_countable_goodRegion_cover`, `ae_exists_of_countable` and `paramMeasure`, which live in
  `IETFree.BlockEndpoints`), together with the a.e. statement over all of them.

The design point is that every block statement is *pointwise*: a `GoodRegion` supplies the strict
monotonicity of its list only on the open set `O`, so there is no global
`hmono : ∀ q, StrictMono fun k => G.s k q` to index anything by.  The length vector of the
composition at a point is `G.cellLen hq` (which is `compLenVec G.s q (monoAt G hq)`), and the block
length vector is `G.blockLam hq k hkl hln`; both live in `IETFree.BlockEndpoints`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace BlockData

variable {d e : ℕ} [NeZero d] [NeZero e]

/-! ## Pointwise length vectors -/

/-- The number of cells of a good region is positive. -/
theorem n_pos {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)} {q₀ : PReal d e}
    (G : GoodRegion d e π σ q₀) : 0 < G.n := by
  have P := G.pres q₀ G.mem_O
  rcases Nat.eq_zero_or_pos G.n with h | h
  · exfalso
    have h0 : (0 : Fin (G.n + 1)) = Fin.last G.n := Fin.ext (by simp [h])
    have hc : (1 : ℝ) = 0 := by rw [← P.top, ← h0]; exact P.zero
    norm_num at hc
  · exact h

instance neZeroN {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)} {q₀ : PReal d e}
    (G : GoodRegion d e π σ q₀) : NeZero G.n := ⟨Nat.pos_iff_ne_zero.mp (n_pos G)⟩

/-- **The pointwise length vector is `simplexMap` of the affine length vector.** -/
theorem compLenVec_eq_simplexMap {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
    {q₀ : PReal d e} (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O) :
    compLenVec G.s q (monoAt G hq) = simplexMap G.n (compLenAffine G.s q) := by
  classical
  have hmono : StrictMono fun k => G.s k q := monoAt G hq
  have P := G.pres q hq
  have hn1 : 1 ≤ G.n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne G.n)
  have hPtop : G.s (Fin.last G.n) q = 1 := P.top
  have htel' := G.sum_compLenAffine hq
  funext k
  apply NNReal.eq
  by_cases hk : (k : ℕ) + 1 = G.n
  · -- the last cell
    have hlastk : k.succ = Fin.last G.n := Fin.ext hk
    have hcastk : k.castSucc = (⟨G.n - 1, by omega⟩ : Fin (G.n + 1)) := Fin.ext (by
      simp only [Fin.val_castSucc]; omega)
    have hL : ((compLenVec G.s q hmono k : ℝ)) = 1 - G.s ⟨G.n - 1, by omega⟩ q := by
      simp only [compLenVec, compLen, hlastk, hcastk, hPtop]
      rfl
    have hpos : 0 ≤ 1 - ∑ j : Fin (G.n - 1), compLenAffine G.s q j := by
      rw [htel']
      have hlt := hmono (Fin.castSucc_lt_succ (i := k))
      rw [hlastk, hcastk] at hlt
      beta_reduce at hlt
      rw [hPtop] at hlt
      linarith
    have hR : ((simplexMap G.n (compLenAffine G.s q) k : ℝ))
        = 1 - ∑ j : Fin (G.n - 1), compLenAffine G.s q j := by
      simp only [simplexMap]
      rw [dif_pos hk, Real.coe_toNNReal _ hpos]
    rw [hL, hR, htel']
  · -- any other cell
    have hkn : (k : ℕ) < G.n - 1 := by have := k.isLt; omega
    have hL : ((compLenVec G.s q hmono k : ℝ))
        = G.s ⟨(k : ℕ) + 1, by omega⟩ q - G.s ⟨(k : ℕ), by omega⟩ q := rfl
    have hnn : 0 ≤ compLenAffine G.s q ⟨(k : ℕ), hkn⟩ := by
      have hlt := hmono (Fin.castSucc_lt_succ (i := k))
      beta_reduce at hlt
      rw [compLenAffine_apply]
      linarith
    have hR : ((simplexMap G.n (compLenAffine G.s q) k : ℝ))
        = compLenAffine G.s q ⟨(k : ℕ), hkn⟩ := by
      simp only [simplexMap]
      rw [dif_neg hk, Real.coe_toNNReal _ hnn]
    rw [hR, compLenAffine_apply]
    simp only [hL]

/-! ## The absolute continuity of the affine length map, without global monotonicity -/

section Transfer

variable {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)} {q₀ : PReal d e}

/-- **The length vector of the composition is an absolutely continuous image of the parameters**,
with the monotonicity only assumed pointwise on the open set (so no hypothesis at all). -/
theorem compLenAffine_absolutelyContinuousAt (G : GoodRegion d e π σ q₀) :
    (volume.restrict G.O).map (compLenAffine G.s) ≪ volume.restrict (simplexRegion G.n) := by
  classical
  have : Measure.IsAddHaarMeasure (volume : Measure (PReal d e)) := by
    have : Measure.IsAddHaarMeasure
        ((volume : Measure (Fin (d - 1) → ℝ)).prod (volume : Measure (Fin (e - 1) → ℝ))) :=
      { toIsFiniteMeasureOnCompacts := inferInstance, toIsAddLeftInvariant := inferInstance,
        toIsOpenPosMeasure := inferInstance }
    infer_instance
  have : Measure.IsAddHaarMeasure (volume : Measure (Fin (G.n - 1) → ℝ)) := inferInstance
  have : Measure.IsAddRightInvariant (volume : Measure (Fin (G.n - 1) → ℝ)) := inferInstance
  -- the combinatorial type is the same everywhere on `O`, so the length vector is injective
  have hAinj : Set.InjOn (compLenAffine G.s) G.O := by
    intro q hq q' hq' hEq
    obtain ⟨hp, hw⟩ := G.subset_region q hq
    have P := G.pres q hq
    have P' := G.pres q' hq'
    refine compLen_injective π σ G.O G.subset_region G.n G.s G.ρ G.a G.B G.pres G.type q hq q'
      hq' (fun i => ?_)
    by_cases hi : (i : ℕ) + 1 = G.n
    · -- the last cell is determined by the others and the total length
      have hik : i.succ = Fin.last G.n := Fin.ext hi
      have hic : i.castSucc = (⟨G.n - 1, by omega⟩ : Fin (G.n + 1)) := by
        rw [Fin.ext_iff]
        simp only [Fin.val_castSucc]
        omega
      have hsum : (∑ j : Fin (G.n - 1), compLenAffine G.s q j)
          = ∑ j : Fin (G.n - 1), compLenAffine G.s q' j :=
        Finset.sum_congr rfl (fun j _ => congrFun hEq j)
      rw [hik, hic, P.top, P'.top, ← G.sum_compLenAffine hq,
        ← G.sum_compLenAffine hq', hsum]
    · -- any other increment is a coordinate of the affine map
      have hin : (i : ℕ) < G.n - 1 := by have := i.isLt; omega
      have h := congrFun hEq ⟨(i : ℕ), hin⟩
      rw [compLenAffine_apply, compLenAffine_apply] at h
      exact h
  -- dimensions agree
  have hcard : G.n = d + e - 1 := by
    exact (G.pres q₀ G.mem_O).card_eq
  have hdim : Module.finrank ℝ (PReal d e) = Module.finrank ℝ (Fin (G.n - 1) → ℝ) := by
    simp only [PReal, Module.finrank_prod, Module.finrank_pi, Fintype.card_fin, hcard]
    have hd : 0 < d := NeZero.pos d
    have he : 0 < e := NeZero.pos e
    omega
  have hinjlin : Function.Injective (compLenAffine G.s).linear :=
    injective_linear_of_injOn G.isOpen_O ⟨q₀, G.mem_O⟩ hAinj
  have hac : (volume.restrict G.O).map (compLenAffine G.s) ≪ volume :=
    absolutelyContinuous_map_affine hinjlin hdim
  -- the image is contained in the simplex region, so the measure lives there
  have hsupp : ∀ q ∈ G.O, compLenAffine G.s q ∈ simplexRegion G.n :=
    fun q hq => compLenAffine_mem_regionAt G hq
  have hcompl : (volume.restrict G.O).map (compLenAffine G.s) ((simplexRegion G.n)ᶜ) = 0 := by
    rw [Measure.map_apply (compLenAffine G.s).continuous_of_finiteDimensional.measurable
      (measurableSet_simplexRegion G.n).compl]
    have hempty : (compLenAffine G.s) ⁻¹' ((simplexRegion G.n)ᶜ) ∩ G.O = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro q ⟨hmem, hq⟩
      exact hmem (hsupp q hq)
    rw [Measure.restrict_apply (measurableSet_simplexRegion G.n |>.compl.preimage
      (compLenAffine G.s).continuous_of_finiteDimensional.measurable), hempty, measure_empty]
  refine Measure.AbsolutelyContinuous.mk (fun t _ htnull => ?_)
  rw [Measure.restrict_apply ‹MeasurableSet t›] at htnull
  have h1 : (volume.restrict G.O).map (compLenAffine G.s) (t ∩ simplexRegion G.n) = 0 :=
    hac htnull
  have h2 : (volume.restrict G.O).map (compLenAffine G.s) (t ∩ (simplexRegion G.n)ᶜ) = 0 :=
    measure_mono_null Set.inter_subset_right hcompl
  have h3 : t = (t ∩ simplexRegion G.n) ∪ (t ∩ (simplexRegion G.n)ᶜ) := by
    rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
  rw [h3]
  exact measure_union_null h1 h2

/-- **Lemma 3.1 at a good region**, in the form used below: the rescaled block length vector of the
composition is an absolutely continuous image of the parameter measure of the region. -/
theorem compLen_absolutelyContinuousAt (G : GoodRegion d e π σ q₀) :
    (volume.restrict G.O).map (fun q => simplexMap G.n (compLenAffine G.s q))
      ≪ simplexVolume G.n := by
  have hac' : (volume.restrict G.O).map (compLenAffine G.s)
      ≪ volume.restrict (simplexRegion G.n) :=
    compLenAffine_absolutelyContinuousAt G
  change Measure.map ((fun ν : Fin (G.n - 1) → ℝ => simplexMap G.n ν) ∘
    ⇑(compLenAffine G.s)) (volume.restrict G.O) ≪ simplexVolume G.n
  rw [← Measure.map_map (measurable_simplexMap G.n)
    (compLenAffine G.s).continuous_of_finiteDimensional.measurable]
  simpa [simplexVolume] using
    (Measure.AbsolutelyContinuous.map hac' (measurable_simplexMap G.n))

/-- **An almost-sure statement about the rescaled block length vector**, pulled back to the
parameters of the region. -/
theorem ae_block_of_ae_simplexVolume (G : GoodRegion d e π σ q₀) {k l : ℕ} (hkl : k < l)
    (hln : l ≤ G.n) {Q : (Fin (l - k) → ℝ≥0) → Prop}
    (hQ : ∀ᵐ ν ∂(simplexVolume (l - k)), Q ν) :
    ∀ᵐ q ∂(volume.restrict G.O),
      Q (simplexMap (l - k) (blockFree k l (simplexMap G.n (compLenAffine G.s q)))) := by
  haveI : NeZero G.n := neZeroN G
  refine ae_of_ae_of_absolutelyContinuous
    (φ := fun q : PReal d e => simplexMap G.n (compLenAffine G.s q))
    (P := fun ν => Q (simplexMap (l - k) (blockFree k l ν))) ?_
    (compLen_absolutelyContinuousAt G) ?_
  · exact ((measurable_simplexMap G.n).comp
      (compLenAffine G.s).continuous_of_finiteDimensional.measurable).aemeasurable
  · exact ae_blockFree_of_ae_simplexVolume hkl hln hQ

end Transfer

variable {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)} {q₀ : PReal d e}

/-! ## The block exchange of a good region -/

/-- A length vector with `r` cells and a permutation of `Fin r` give an exchange which is both
uniquely ergodic and rigid by translations. -/
def BlockGood {r : ℕ} [NeZero r] (lam : Fin r → ℝ≥0) (τ : Equiv.Perm (Fin r)) : Prop :=
  (∀ h : lam ∈ simplex r, UniqueErgodic (mkIET1 lam τ h)) ∧
    ∀ h : lam ∈ simplex r, IsRigidByTranslations (mkIET1 lam τ h)

/-- **Lemma 3.4 for the rescaled block, at a fixed block**: almost every parameter of the region
gives a block exchange which is uniquely ergodic and rigid by translations.  This is Masur--Veech
and Veech's rigidity for the block permutation, pulled back by the absolute continuity of the
rescaled block length vector. -/
theorem ae_blockGood_free (G : GoodRegion d e π σ q₀) (B : GoodRegion.Block G) (hMV : MasurVeech)
    (hVR : VeechRigidity) (hirr : IsIrreduciblePerm B.perm) (h2 : 2 ≤ B.l - B.k) :
    ∀ᵐ q ∂(volume.restrict G.O),
      BlockGood (simplexMap (B.l - B.k) (blockFree B.k B.l (simplexMap G.n (compLenAffine G.s q))))
        B.perm := by
  refine ae_block_of_ae_simplexVolume G B.hkl B.hln (Q := fun nu => BlockGood nu B.perm) ?_
  exact (hMV (B.l - B.k) h2 _ hirr).and (hVR (B.l - B.k) _ hirr)

/-- **All the blocks of a region at once**, in free coordinates: for almost every parameter, every
block whose permutation is irreducible gives a block exchange which is uniquely ergodic and rigid by
translations.  There are only countably many blocks (`Block.countable`), so this is a countable
intersection of the statements of `ae_blockGood_free`. -/
theorem ae_blockGood (G : GoodRegion d e π σ q₀) (hMV : MasurVeech) (hVR : VeechRigidity) :
    ∀ᵐ q ∂(volume.restrict G.O), ∀ B : GoodRegion.Block G,
      IsIrreduciblePerm B.perm → 2 ≤ B.l - B.k →
        BlockGood (simplexMap (B.l - B.k)
          (blockFree B.k B.l (simplexMap G.n (compLenAffine G.s q)))) B.perm := by
  rw [MeasureTheory.ae_all_iff]
  intro B
  by_cases h2 : 2 ≤ B.l - B.k
  · by_cases hirr : IsIrreduciblePerm B.perm
    · filter_upwards [ae_blockGood_free G B hMV hVR hirr h2] with q hq hirr' h2'
      exact hq
    · exact Filter.Eventually.of_forall (fun q hirr' _ => absurd hirr' hirr)
  · exact Filter.Eventually.of_forall (fun q _ h2' => absurd h2' h2)

/-- **The block length vector of a region at a point, in the two forms used below**: the rescaled
`blockLam` of the pointwise length vector of the composition, and the projective formula in the free
coordinates. -/
theorem blockLamAt_eq (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O)
    {k l : ℕ} (hkl : k < l) (hln : l ≤ G.n) :
    G.blockLam hq k hkl hln
      = simplexMap (l - k) (blockFree k l (simplexMap G.n (compLenAffine G.s q))) := by
  haveI : NeZero G.n := neZeroN G
  haveI : NeZero (l - k) := ⟨by omega⟩
  have hx : compLenAffine G.s q ∈ simplexRegion G.n := compLenAffine_mem_regionAt G hq
  have hcv : G.cellLen hq = simplexMap G.n (compLenAffine G.s q) :=
    compLenVec_eq_simplexMap G hq
  have hposx : ∀ i, 0 < simplexMap G.n (compLenAffine G.s q) i := fun i => pos_simplexMap hx i
  have hcongr : G.blockLam hq k hkl hln
      = blockLam (simplexMap G.n (compLenAffine G.s q)) k hkl hln hposx :=
    blockLam_congr hcv hkl hln _ hposx
  rw [hcongr, blockFree_simplexMap hx]
  exact blockLam_eq_simplexMap_rescaleSub hkl hln hx hposx

/-- **The conclusion of the a.e. transfer in the form the pointwise assembly consumes**: at a point
of the region, every block of the composition whose permutation is irreducible is uniquely ergodic
and rigid by translations. -/
def BlockGoodAt (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O) : Prop :=
  ∀ B : GoodRegion.Block G, IsIrreduciblePerm B.perm → 2 ≤ B.l - B.k → BlockGood (B.lam hq) B.perm

/-- `BlockGoodAt` as a predicate of the point, with the region membership proof existentially
quantified: the form in which it can appear in an almost-sure statement. -/
def BlockGoodPt (G : GoodRegion d e π σ q₀) (q : PReal d e) : Prop :=
  ∃ hq : q ∈ G.O, BlockGoodAt G hq

theorem blockGoodAt_of_pt (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O)
    (h : BlockGoodPt G q) : BlockGoodAt G hq := by
  obtain ⟨hq', h'⟩ := h
  exact h'

/-- **Almost every point of a good region satisfies `BlockGoodAt`.** -/
theorem ae_BlockGoodPt (G : GoodRegion d e π σ q₀) (hMV : MasurVeech) (hVR : VeechRigidity) :
    ∀ᵐ q ∂(volume.restrict G.O), BlockGoodPt G q := by
  filter_upwards [ae_blockGood G hMV hVR, ae_restrict_mem G.isOpen_O.measurableSet] with q hq1 hq2
  refine ⟨hq2, ?_⟩
  intro B hirr h2
  change BlockGood (G.blockLam hq2 B.k B.hkl B.hln) B.perm
  rw [blockLamAt_eq G hq2 B.hkl B.hln]
  exact hq1 B hirr h2

/-! ## The a.e. statement over the whole parameter space -/

/-- The product of the two restricted parameter measures is dominated by Lebesgue measure. -/
theorem prodRestrict_le_volume :
    ((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e)))
      ≤ (volume : Measure (PReal d e)) := by
  have h : (volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))
      ≤ volume.prod volume :=
    Measure.prod_mono (Measure.restrict_le_self (s := simplexRegion d))
      (Measure.restrict_le_self (s := simplexRegion e))
  exact h

/-- An almost-sure statement on the restriction of a measure transfers to an almost-sure implication
for a smaller measure. -/
theorem ae_imp_of_ae_restrict {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    (hμν : μ ≤ ν) {O : Set α} (hO : MeasurableSet O) {p : α → Prop}
    (h : ∀ᵐ x ∂ν.restrict O, p x) :
    ∀ᵐ x ∂μ, x ∈ O → p x := by
  rw [ae_iff] at h ⊢
  rw [Measure.restrict_apply' hO] at h
  have hset : {x : α | ¬ (x ∈ O → p x)} = {x | ¬ p x} ∩ O := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Classical.not_imp]
    tauto
  rw [hset]
  exact nonpos_iff_eq_zero.mp (le_trans (hμν _) (le_of_eq h))

/-- Countably many almost-sure statements combine. -/
theorem ae_forall_countable {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
    [Countable ι] {p : ι → α → Prop} (h : ∀ i, ∀ᵐ a ∂μ, p i a) :
    ∀ᵐ a ∂μ, ∀ i, p i a := by
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null (fun i => ae_iff.mp (h i)))
  intro a ha
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, not_forall] at ha ⊢
  exact ha

/-- **A3, the almost-sure glue of Lemma 3.4.**  For almost every pair of free parameters: the
pair is not bad, both length vectors are in the open simplexes, the pair is Diophantine, and at
every point of every region of the family covering the good set, every block of the composition with
a stable irreducible block permutation gives a block exchange which is uniquely ergodic and rigid by
translations. -/
theorem ae_block_good (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) (hMV : MasurVeech)
    (hVR : VeechRigidity) {ι : Type} [Countable ι]
    (Gfam : ι → Σ q : PReal d e, GoodRegion d e π σ q) :
    ∀ᵐ z ∂((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))),
      ¬ IsBadParam z ∧ z.1 ∈ simplexRegion d ∧ z.2 ∈ simplexRegion e ∧
        IsDiophantine (simplexMap d z.1) (simplexMap e z.2) ∧
        ∀ (i : ι) (hz : z ∈ (Gfam i).2.O), BlockGoodAt (Gfam i).2 hz := by
  classical
  have h1 : ∀ᵐ z ∂((volume.restrict (simplexRegion d)).prod
      (volume.restrict (simplexRegion e))),
      ¬ IsBadParam z := ae_goodParams_real
  have h2 : ∀ᵐ z ∂((volume.restrict (simplexRegion d)).prod
      (volume.restrict (simplexRegion e))),
      z.1 ∈ simplexRegion d ∧ z.2 ∈ simplexRegion e := ae_mem_simplexRegion_prod
  have h3 : ∀ᵐ z ∂((volume.restrict (simplexRegion d)).prod
      (volume.restrict (simplexRegion e))),
      IsDiophantine (simplexMap d z.1) (simplexMap e z.2) := ae_diophantine_real π σ
  have h4 : ∀ᵐ z ∂((volume.restrict (simplexRegion d)).prod
      (volume.restrict (simplexRegion e))),
      ∀ i : ι, z ∈ (Gfam i).2.O → BlockGoodPt (Gfam i).2 z := by
    refine ae_forall_countable (fun i => ?_)
    exact ae_imp_of_ae_restrict prodRestrict_le_volume (Gfam i).2.isOpen_O.measurableSet
      (ae_BlockGoodPt (Gfam i).2 hMV hVR)
  filter_upwards [h1, h2, h3, h4] with z hz1 hz2 hz3 hz4
  exact ⟨hz1, hz2.1, hz2.2, hz3, fun i hz => blockGoodAt_of_pt (Gfam i).2 hz (hz4 i hz)⟩

/-- **A3 with the countable cover built in.** -/
theorem exists_ae_block_good (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e))
    (hMV : MasurVeech) (hVR : VeechRigidity) :
    ∃ (ι : Type) (_ : Countable ι) (G : ι → Σ q : PReal d e, GoodRegion d e π σ q),
      (∀ z ∈ goodParams d e, z.1 ∈ simplexRegion d → z.2 ∈ simplexRegion e →
        ∃ i, z ∈ (G i).2.O) ∧
      ∀ᵐ z ∂((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))),
        ¬ IsBadParam z ∧ z.1 ∈ simplexRegion d ∧ z.2 ∈ simplexRegion e ∧
          IsDiophantine (simplexMap d z.1) (simplexMap e z.2) ∧
          ∀ (i : ι) (hz : z ∈ (G i).2.O), BlockGoodAt (G i).2 hz := by
  obtain ⟨ι, hι, Gfam, hcov⟩ := exists_countable_goodRegion_cover (d := d) (e := e) π σ
  exact ⟨ι, hι, Gfam, hcov, @ae_block_good d e _ _ π σ hMV hVR ι hι Gfam⟩

end BlockData
