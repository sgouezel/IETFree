/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.ReductionData
import IETFree.Presentation
import IETFree.SingularityList
import IETFree.GoodRegion
import IETFree.LengthMap
import IETFree.SubintervalTransfer
import IETFree.BlockRescaling
import IETFree.InvariantInterval
import IETFree.BlockEndpoints
import IETFree.BlockAETransfer
import IETFree.BlockDiophantine
import IETFree.BlockData
import IETFree.BlockIrreducibility
import IETFree.BlockAssembly
import IETFree.BlockDatum
import IETFree.BlockLemma

/-!
Section 3 of the paper: the reduction of the general case to the irreducible case.

This is the umbrella module; the section is split, in dependency order, into

* `IETFree.ReductionData` — the blocks and the pair-splitting singularities, the good parameter set
  `O` (`IsBadParam`, `goodParams`, `ae_goodParams`) and the covering step;
* `IETFree.Presentation` — the presentation `IsCompPresentation` of `g ∘ f`, its combinatorial type
  `IsCompType` and the length vector `compLen`, plus the singularity functions and the cuts as
  affine functions of the free parameters;
* `IETFree.IntegerAffine` — integer-affine functions of the parameters: closure properties,
  extraction of the data, sign constancy on a convex region, and the truncation lemmas;
* `IETFree.SingularityList` — the marked singularity list `s` (`singAffine`, `withEnds`,
  `exists_markedList`) and the affine description `markedPos` of the images of its points under `f`;
* `IETFree.GoodRegion` — the image side `B`, the partial-sum identity, and the local presentation
  `exists_compPresentation_on_ball` with `GoodRegion` / `ae_exists_goodRegion`, the pointwise
  presentation `G.pres q hq` / `G.type q hq`, and the bundled tuples `BlockIdx` / `Block` / `Fits`;
* `IETFree.LengthMap` — Lemma 3.1: the length vector determines the parameters
  (`compLen_injective`) and the affine length map, whose absolute continuity is the pointwise
  `BlockData.compLen_absolutelyContinuousAt`;
* `IETFree.SubintervalTransfer` — the measure-theoretic transfer to a rescaled sub-interval: the
  normalisation `y ↦ y / ∑ y` pulls null sets back to null sets;
* `IETFree.BlockRescaling` — the rescaling of an exchange to an invariant interval, the
  irreducibility of the block permutation, and the block length vector and permutation
  (`blockLam`, `blockPerm`, `mkIET1_rescale_subinterval`);
* `IETFree.GeneratorChange` — the change of generators `(f, g) ↦ (g ∘ f, g)` and the transport of a
  word from the rescaled block back to the block;
* `IETFree.InvariantInterval` — the restriction of `g` itself to an invariant interval, rescaled,
  with the same permutation;
* `IETFree.BlockEndpoints` — the consequences of the explicit shape of the singularity list (the
  endpoints of a block are marked points), the almost-sure bookkeeping of Lemma 3.4 (`paramMeasure`,
  and the countable cover of `ae_exists_goodRegion`), and the lengths of a block at a point of the
  region (`cellLen`, `blockLam`, `Block.lam`, `Block.perm`);
* `IETFree.BlockAETransfer` — the almost-sure transfer of Masur–Veech and Veech's rigidity to the
  rescaled block;
* `IETFree.BlockDiophantine` — the integer-affine data of a block and the Diophantine transfer to
  the block pair;
* `IETFree.BlockData` — A3: the almost-sure block data over a countable family of good regions
  (`exists_ae_block_good`);
* `IETFree.BlockIrreducibility` — Lemma 3.2 (`block_irreducible_on_good`);
* `IETFree.BlockAssembly` — the per-block words combined into one word trivial on `[0, 1)`
  (`exists_word_trivial_on_all_of_blocks`);
* `IETFree.BlockDatum` — the datum of `g ∘ f` on a block, the invariance of the block, and the
  rescaled composition (`blockRescaled`, `comp_conj_rescale`, `restrict_rescale`);
* `IETFree.BlockLemma` — Lemma 3.4 (`exists_word_trivial_on_block`) and Theorem 1.1
  (`main_theorem_of_blocks`).
-/
