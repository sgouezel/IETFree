/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.IET
import IETFree.Irreducible
import IETFree.Reduction
import IETFree.TranslationVector
import IETFree.SingularityBound

/-!
Axiom report for the refactored project.

`Challenge.lean` and `ChallengeWeak.lean` are display-only statement files and are imported by
nothing (see `ChallengeWeakSolved.lean` for the proof of the second one).
-/

-- the carrier and its API
#print axioms IsIET.id
#print axioms IsIET.mono
#print axioms IsIET.comp
#print axioms Equiv.IsIET.symm
#print axioms IET.id
#print axioms IET.ext

-- the exchange built from a length vector and a permutation
#print axioms mkIETEquiv
#print axioms isIET_mkIETEquiv
#print axioms mkIET1
#print axioms isIET_iff_exists_mkIETEquiv

-- the free-group theory behind Lemma 2.7 (LS Prop. 2.19 and root uniqueness)
#print axioms FreeGroup.commute_of_zpow_eq
#print axioms FreeGroup.exists_zpow_eq_of_mul_comm
#print axioms FreeGroup.exists_common_zpow

-- the commutator API: Mathlib's `⁅a, b⁆ = a * b * a⁻¹ * b⁻¹` and the paper's `[a, b] = ⁅a⁻¹, b⁻¹⁆`
#print axioms commutatorElement_inv_inv_eq_one_iff
#print axioms wordLength_commutatorElement_le
#print axioms wordLength_inv
#print axioms commutator_inv_genY_genX_pow_ne_one
#print axioms evalWord_commutatorElement
#print axioms commutator_inv_apply_eq
#print axioms commutator_inv_supp_subset
#print axioms unitMeas_real_supp_commutator_inv_le

-- Section 2
#print axioms exists_nontrivial_commutator
#print axioms exists_word_small_support
#print axioms exists_uniform_birkhoff
#print axioms iterate_word
#print axioms irreducible_case
#print axioms ae_diophantine

-- the translation-vector bound used by Theorem 2.6
#print axioms exists_lattice_displacement
#print axioms CutBound.exists_lattice_cuts
#print axioms evalWord_cuts
#print axioms exists_lattice_cell
#print axioms isFiniteUnionIntervals_ne_id
#print axioms isFiniteUnionIntervals_wordSupp
#print axioms MasurVeech
#print axioms VeechRigidity

-- Section 3
#print axioms perm_eq_of_preimage

-- Section 3, the interface for the reduction to the irreducible case
#print axioms Separated.exists_of_le
#print axioms Separated.of_lt_le
#print axioms mem_Ioc_min_max
#print axioms coeffs_eq_of_good
#print axioms ae_goodParams
#print axioms mkIETFun_leftEnd
#print axioms exists_cell_of_strictMono
#print axioms isCutSet_mkIETCuts
#print axioms coeffs_zero_of_good_with_const
#print axioms sum_eq_last_add_free
#print axioms relation_of_good
#print axioms ae_goodParams_real
#print axioms ae_mem_simplexRegion_prod
#print axioms isBadParam_iff
#print axioms toReal_simplexMap
#print axioms isOpen_goodParams
#print axioms coeffs_zero_of_good
#print axioms measure_zero_of_forall_exists_isOpen_null
#print axioms perm_eq_of_preimage
#print axioms IETDatum.isFixedCell_apply
#print axioms IETDatum.isSplitting_below
#print axioms IETDatum.isSplitting_above
#print axioms pairSplitting_invariant
#print axioms IsPairSplitting.invariant
#print axioms IsPairSplitting.iff_mem
#print axioms block_irreducible_on_good
#print axioms exists_pairSplitting_of_invariant
#print axioms exists_word_trivial_on_block
#print axioms exists_word_trivial_on_all_of_blocks
#print axioms main_theorem_of_blocks
#print axioms imageLeft_add
#print axioms imageLeft_add

-- the marked points as a cut set, and the refinement of two data
#print axioms IETDatum.lam_pos
#print axioms IETDatum.leftEnd_lt_sum
#print axioms IETDatum.mkIETCuts_eq_markCuts
#print axioms IETDatum.isCutSet_markCuts
#print axioms IETDatum.toFun_mark_castSucc
#print axioms IETDatum.toFun_eq_of_mem_cell
#print axioms isCutSet_comp_markCuts
#print axioms mem_comp_markCuts
#print axioms IsCutSet.sum_cellLen_filter

-- Case 1a of the case analysis of Lemma 3.2
#print axioms sum_ite_one_mul
#print axioms ite_one_sub_ite_one_eq_zero
#print axioms splitting_of_imageLeft_relation
#print axioms splitting_of_imageLeft_relation

-- Case 1b of the case analysis of Lemma 3.2 (needs the bound 4)
#print axioms ite_add_ite_sub_ite
#print axioms ite_sub_ite_sub_ite
#print axioms splitting_of_imageLeft_relation_add

-- the position lemma, and Case 1a of the case analysis of Lemma 3.2
#print axioms IsCutSet.exists_imageStart_of_mapsTo
#print axioms IETDatum.isSplitting_succ
#print axioms IETDatum.comp_toFun_mark_castSucc
#print axioms IsPairSplitting.eq_one_or_mem_markCuts
#print axioms IETDatum.pairSplitting_of_mark_image
#print axioms IETDatum.pairSplitting_of_mark_preimage
#print axioms IETDatum.false_of_preimage_mark
#print axioms IETDatum.pairSplitting_of_preimage_preimage
#print axioms leftEnd_eq_zero_of_imageLeft_eq
#print axioms isBadParam_swap
#print axioms imageLeft_eq_leftEnd_of_splitting

-- the free-parameter refactor of Section 3
#print axioms ae_exists_goodRegion
#print axioms ae_goodParams

-- Lemma 3.1's position step
#print axioms eq_of_increments_eq
#print axioms simplexMap_mem_simplex_fin

-- Lemma 3.1's two block-sum formulas, and injectivity
#print axioms disjoint_leftEnd_Ico
#print axioms leftEnd_Ico_subset
#print axioms volume_leftEnd_Ico
#print axioms IsCompPresentation.lam_eq_sum
#print axioms IsCompPresentation.mu_eq_sum
#print axioms compLen_injective

-- Lemma 3.1's absolute continuity
#print axioms injective_linear_of_injOn
#print axioms absolutelyContinuous_map_affine
#print axioms sum_fin_sub
#print axioms compLenAffine_apply
#print axioms GoodRegion.sum_compLenAffine

-- the assembly of Theorem 1.1 from the per-block words
#print axioms commutator_apply_eq_self_left
#print axioms commutator_apply_eq_self_right
#print axioms conj_apply_eq_self
#print axioms evalWord_mapsTo_of_invariant
#print axioms exists_word_trivial_on_all_of_blocks

-- the local form of the presentation: the cuts of `f` are affine in the free parameters
#print axioms simplexMap_of_lt
#print axioms leftEnd_simplexMap
#print axioms exists_goodRegion

-- Step 2 of the local presentation: a cut of `g` sits strictly inside a cell of `f`
#print axioms pos_simplexMap
#print axioms leftEnd_ne_sum_lam_of_good
#print axioms exists_lt_imageLeft_of_good
#print axioms mkIET1_inv_of_lt_imageLeft
#print axioms exists_lt_imageLeft_simplexMap

-- the cuts of `f` as affine functions of the free parameters
#print axioms leftCoordAffine_apply
#print axioms cutAffine_apply
#print axioms cutAffine_eq_leftEnd

-- item 1: the images of the cells of `f` as affine functions of the free parameters
#print axioms AffineMap.sum_apply
#print axioms imageLenAffine_apply_last
#print axioms imageLenAffine_apply_free
#print axioms imageLeftAffine_apply
#print axioms imageLeftAffine_eq
#print axioms imageLenAffine_eq
#print axioms isOpen_simplexRegion
#print axioms cutAffineRight_eq_leftEnd
-- item 2: the preimages of the cuts of `g`, and their local constancy
#print axioms preimageCutAffine_eq
#print axioms exists_ball_imageLeft_lt

-- item 3 (first half): the order of an affine list persists on a ball
#print axioms exists_ball_lt_of_lt
#print axioms exists_ball_strictMono

-- item 3: sorting, distinctness of the singularities, and the uniform ball
#print axioms exists_strictMono_comp
#print axioms leftEnd_lt_leftEnd
#print axioms imageLeft_ne_leftEnd_of_good
#print axioms exists_ball_forall_imageLeft_lt

-- injectivity of the singularity family, and the marked list with its two ends
#print axioms mkIET1_leftEnd
#print axioms singAffine_injective
#print axioms withEnds_zero
#print axioms withEnds_last
#print axioms withEnds_mid

-- strict monotonicity of the marked list
#print axioms withEnds_apply_eq
#print axioms strictMono_withEnds

-- the marked singularities lie in `(0, 1)`
#print axioms cutAffine_pos
#print axioms cutAffine_lt_one
#print axioms preimageCutAffine_mem

-- the marked list: the singularities of the composition, sorted and with the two ends
#print axioms exists_markedList

-- the image side: no cut of `f` strictly inside a marked cell
#print axioms no_cut_inside_markedCell

-- the image side: `f` translates each marked cell, and no cut of `g` inside the image
#print axioms mem_mkIETCuts_one
#print axioms markedCell_transl
#print axioms image_Ico_add
#print axioms no_gcut_inside_image

-- the image side: `B`, and the image of each marked cell inside one cell of `g`
#print axioms le_of_Ico_subset
#print axioms imageInG

-- the image side: `g` translates the image of each marked cell
#print axioms markedCell_g_transl

-- the marked index of the cuts of `f` (`IsCompType`'s `a`)
#print axioms compTypeA_zero
#print axioms compTypeA_last
#print axioms compTypeA_cut

-- the sign of an affine function of the parameters, and the constancy of the order of a family of
-- affine functions with no collisions (the local constancy of `rho` and of `B`)
#print axioms affine_comb

-- the upper end of a cell of `g` as an affine function of the free parameters
#print axioms upperEndAffineRight_eq

-- the image of a marked point under `f`, as an affine function of the free parameters
#print axioms markedPos_inl
#print axioms markedPos_inr
#print axioms markedPos_spec

-- a marked image sits on a cut of `g` only identically
#print axioms markedPos_eq_cut_of_eq

-- the two-sided interval condition for `B k = idx mu (f (s k))`
#print axioms imageInG_idx

-- positivity / nonnegativity propagating on the ball (the local constancy of `B`)
#print axioms pos_on_ball_of_vanish_imp
#print axioms nonneg_on_ball_of_vanish_imp

-- the `g`-cell containing the image of each marked cell is locally constant (`IsCompType.image`)
#print axioms upperEndAffineRight_of_lt
#print axioms upperEndAffineRight_of_last
#print axioms exists_compImage_on_ball

-- `g` at a marked image: an affine function, since `B` pins the `g`-cell
#print axioms markedImage_g

-- the order of a family of affine functions is constant on a ball with no collisions (`ρ`)
#print axioms sum_len_eq_of_tiling
#print axioms sign_congr_on_ball
#print axioms lt_iff_lt_of_ne_on_ball
#print axioms exists_rank_perm

-- the `g`-side image functions, and `(g ∘ f)` at a marked point
#print axioms imageLenAffineRight_eq
#print axioms imageLeftAffineRight_eq
#print axioms markedImage_gf

-- the image starts are the partial sums of the cell lengths
#print axioms partialSum_image

-- the cell starts are the partial sums of the cell lengths
#print axioms partialSum_cell

-- the local presentation of `g ∘ f` on a ball of good parameters
#print axioms exists_compImage_on_ball
#print axioms exists_compPresentation_on_ball
#print axioms exists_goodRegion

-- the block decomposition of `[0, 1)` by the pair-splitting singularities
#print axioms mark_mem_insert
#print axioms main_theorem_of_blocks

-- the rescaling of an exchange to an invariant interval, and the block permutation irreducibility
#print axioms rescaleMap_mem
#print axioms mkIET1_apply
#print axioms imageLeft_add_le_of_invariant
#print axioms irreduciblePerm_of_no_invariant_cut

-- naturality of `FreeGroup.lift`, and the `Equiv`-valued evaluation of a word

-- the `g`-side: pair-splitting points are marked points
#print axioms mark_fixed_of_inFixedCell
#print axioms pairSplitting_mem_markedList

-- monotonicity of the image starts in the image order, and consecutiveness on a block
#print axioms listImageLeft_lt

-- the rescaling transfer: null sets of rescaled length vectors
#print axioms volume_normalize_preimage_null
#print axioms eIdx_surjective
#print axioms injective_split
#print axioms absolutelyContinuous_map_rescaleSub
#print axioms splitMap_injective
#print axioms splitMapLast_injective
#print axioms rescaleSub_mem_simplexRegion

-- the word transport along a conjugacy of the generators
#print axioms evalWord_conj_apply

-- the block permutation and the rescaled restriction of an exchange to an invariant block
#print axioms blockLam_sum
#print axioms leftEnd_eq_sum_range
#print axioms leftEnd_blockLam
#print axioms leftEnd_le_leftEnd
#print axioms RescaleBlock.idx_rescaleMap_aux
#print axioms RescaleBlock.mkIET1_rescale_subinterval

-- the irreducibility of the block permutation, transported through the rescaling
#print axioms blockLam_pos
#print axioms leftEnd_lt_total
#print axioms leftEnd_pos_of_ne_zero
#print axioms irreduciblePerm_blockPerm
#print axioms IETDatum.irreduciblePerm_of_no_invariant_cut
#print axioms IsCompIrreducibleOn.toDatum

-- the presentation as a datum: the composition is the exchange of the marked list
#print axioms leftEnd_compLen
#print axioms upperEnd_compLen
#print axioms compLen_sum
#print axioms IsCompPresentation.eq_mkIET1

-- the datum of a good region, and Lemma 3.2 read on it
#print axioms GoodRegion.datum_markCuts
#print axioms GoodRegion.datum_hcuts
#print axioms GoodRegion.datum_toFun
#print axioms GoodRegion.irreducibleOn_datum

-- the explicit shape of the singularity list, and the block endpoints as marked points
#print axioms GoodRegion.n_eq
#print axioms GoodRegion.surj
#print axioms IETDatum.mark_eq_leftEnd
#print axioms mkIET1_inv_zero
#print axioms GoodRegion.mem_cutF
#print axioms GoodRegion.mem_cutList
#print axioms GoodRegion.mem_markD
#print axioms GoodRegion.mem_pairSplitting
#print axioms GoodRegion.block_endpoints

#print axioms GoodRegion.irreduciblePerm_blockPerm
#print axioms blockPerm_stab
#print axioms comp_image_cell

-- the a.e. irreducibility of the block permutation
#print axioms GoodRegion.isIrreduciblePerm_blockPermOf

-- integer-affine functions of the free parameters
#print axioms isIntAffine_leftCoordAffine
#print axioms isIntAffine_imageLenAffine
#print axioms isIntAffine_imageLeftAffine
#print axioms isIntAffine_preimageCutAffine

-- the Diophantine transfer (Lemma 3.4, the paper's "integer combination" step)
#print axioms natAbs_sum_mul_le
#print axioms IsDiophantine.of_int_combination

-- extracting the integer coefficients
#print axioms IsIntAffine.coeff_spec
#print axioms intAffineData

-- the change of generators `(f, g) ↦ (g ∘ f, g)`, and the transport of a word to the block
#print axioms substGen
#print axioms invSubstGen_substGen
#print axioms substGen_ne_one
#print axioms evalWord_substGen
#print axioms conj_inv_of_conj
#print axioms exists_word_trivial_on_block_of_rescaled

-- the free coordinates of the rescaled block are `rescaleSub` of those of the composition
#print axioms blockLen_simplexMap

-- from a countable family of good regions to an almost-sure statement
#print axioms exists_countable_goodRegion_cover
#print axioms ae_exists_of_countable

-- the Diophantine condition in the free coordinates (the form Lemma 3.4 consumes)
#print axioms ae_diophantine_real

-- the rescaled composition on a block, and the conjugacy of the composition with it
#print axioms GoodRegion.cellLen_pos
#print axioms GoodRegion.cellLen_sum
#print axioms GoodRegion.blockRescaled
#print axioms GoodRegion.comp_conj_rescale

-- the sign of an integer-affine difference is constant on a convex region, and the consequences for
-- the truncation pattern of the block lengths of `g`

-- the restriction of an exchange to an invariant interval is an exchange (`InvariantInterval`)
#print axioms RestrictIET.mkIET1_restrict_invariant
#print axioms RestrictIET.sum_truncatedLengths
#print axioms RestrictIET.leftEnd_truncatedLengths
#print axioms RestrictIET.truncatedLengths_clamp

-- the almost-sure transfer of Masur–Veech and Veech rigidity to a block (`BlockAETransfer`)
#print axioms blockLam_eq_simplexMap_rescaleSub
#print axioms absolutelyContinuous_map_blockFree
#print axioms ae_blockFree_of_ae_simplexVolume

-- the integer-affine data of the block, and the Diophantine transfer (`BlockDiophantine`)
#print axioms GoodRegion.exists_isIntAffine_s
#print axioms GoodRegion.isIntAffine_sAffine
#print axioms IsDiophantine.of_intAffine_family

-- the `g`-side of the block transport: `E` is its own rescaled restriction
#print axioms GoodRegion.restrict_rescale

-- the cell lengths of `g` in real coordinates: integer affine without `NNReal`
#print axioms gLenAffine
#print axioms gLenAffine_eq
#print axioms gUpperEnd
#print axioms gUpperEnd_eq

-- the `μ'` family of a block: the `g`-cell pieces as integer-affine functions
#print axioms GoodRegion.exists_isIntAffine_truncatedLengths

-- Lemma 3.4, the pointwise conclusion at a good region (A4), and the Diophantine condition at a
-- block (A2)
#print axioms GoodRegion.exists_word_trivial_of_region
#print axioms GoodRegion.isDiophantine_blockPair
#print axioms mkIET1_of_all_one
#print axioms GoodRegion.blockLam_of_one
#print axioms GoodRegion.genY_mul_genX_ne_one

-- the parameter measure of Lemma 3.4, and its absolute continuity

-- A3: the almost-sure block data over the countable family of regions (BlockData)
#print axioms BlockData.exists_ae_block_good
#print axioms BlockData.ae_block_good
#print axioms BlockData.compLen_absolutelyContinuousAt
#print axioms BlockData.blockLamAt_eq
#print axioms BlockData.ae_blockGood_free
#print axioms BlockData.ae_blockGood
#print axioms BlockData.ae_BlockGoodPt

-- the bundled tuples: a block of cells, and the data that fit a point of the region
#print axioms GoodRegion.Block.countable
#print axioms GoodRegion.Block.lam_sum
#print axioms GoodRegion.blockOf

-- the paper's irreducibility, and the two exclusions it now makes
#print axioms irreduciblePerm_of_no_invariant_cut
#print axioms IETDatum.irreduciblePerm_of_no_invariant_cut
#print axioms irreduciblePerm_blockPerm
#print axioms IsDiophantine.of_int_combination
