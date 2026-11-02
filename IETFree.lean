/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.BlockAETransfer
import IETFree.BlockAssembly
import IETFree.BlockData
import IETFree.BlockDatum
import IETFree.BlockDiophantine
import IETFree.BlockEndpoints
import IETFree.BlockIrreducibility
import IETFree.BlockLemma
import IETFree.BlockRescaling
import IETFree.Centralizer
import IETFree.ChallengeWeakSolved
import IETFree.Commensurable
import IETFree.CutSet
import IETFree.CutSetMeasure
import IETFree.Diophantine
import IETFree.GeneratorChange
import IETFree.GoodRegion
import IETFree.IET
import IETFree.IntegerAffine
import IETFree.InvariantInterval
import IETFree.Irreducible
import IETFree.LengthMap
import IETFree.MeasureTools
import IETFree.Presentation
import IETFree.ReductionData
import IETFree.SingularityBound
import IETFree.SingularityList
import IETFree.SubintervalTransfer
import IETFree.TranslationVector

/-!
Root module of the `IETFree` library: the Lean formalisation of

  S. Gouëzel, *almost every pair of interval exchange transformations does not generate a free
  group*.

`import IETFree` pulls in every module of the library — the import list below is *generated*, by
`lake exe mk_all --lib IETFree`, so a new module is added there and not by hand (a regeneration
replaces the whole file, so this docstring has to be put back afterwards).  It includes
`ChallengeWeakSolved` (the solution of the comparator challenge, which nothing else imports; it also
carries the single `#print axioms main` of the library).  The two statement files `Challenge.lean`
and `ChallengeWeak.lean` sit one directory above `IETFree/` and are not part of this module.  The
individual modules are

* `IETFree.CutSet`, `IETFree.CutSetMeasure`, `IETFree.IET` — interval exchanges: cut sets and their
  cells, the measure theory of a piecewise translation, then the predicate `IsIET`, the explicit
  construction `mkIETFun` / `mkIETEquiv` / `mkIET1`, the classification of an exchange by its
  cut-set data, and the type `IET a b` with its group structure;
* `IETFree.Diophantine` — the Diophantine condition and Proposition 2.5;
* `IETFree.Commensurable`, `IETFree.Centralizer` — the free-group theory (LS 2.19 and the
  centralizer lemmas);
* `IETFree.MeasureTools` — `unitMeas`, words in two generators and their supports;
* `IETFree.TranslationVector`, `IETFree.SingularityBound` — the lattice bounds on displacements and
  on the singularities of `w(f, g)`;
* `IETFree.Irreducible` — Section 2 (Lemmas 2.7–2.10 and Theorem 2.6);
* the Section 3 modules, i.e. the reduction of the general case to the irreducible case, split in
  dependency order:

  * `IETFree.ReductionData` — the blocks and the pair-splitting singularities, the good parameter
    set `O` (`IsBadParam`, `goodParams`) and the covering step;
  * `IETFree.Presentation` — the presentation `IsCompPresentation` of `g ∘ f`, its combinatorial
    type `IsCompType` and the length vector `compLen`, plus the singularity functions and the cuts
    as affine functions of the free parameters;
  * `IETFree.IntegerAffine` — integer-affine functions of the parameters: closure properties,
    extraction of the data, sign constancy on a convex region, and the truncation lemmas;
  * `IETFree.SingularityList` — the marked singularity list `s` (`singAffine`, `withEnds`,
    `exists_markedList`) and the affine description `markedPos` of the images of its points under
    `f`;
  * `IETFree.GoodRegion` — the image side `B`, the partial-sum identity, and the local presentation
    `exists_compPresentation_on_ball` and the type `GoodRegion`, the pointwise presentation
    `G.pres q hq` / `G.type q hq`, and the bundled tuples `BlockIdx` / `Block` / `Fits`;
  * `IETFree.LengthMap` — Lemma 3.1: the length vector determines the parameters
    (`compLen_injective`) and the affine length map, whose absolute continuity is the pointwise
    `BlockData.compLen_absolutelyContinuousAt`;
  * `IETFree.SubintervalTransfer` — the measure-theoretic transfer to a rescaled sub-interval: the
    normalisation `y ↦ y / ∑ y` pulls null sets back to null sets;
  * `IETFree.BlockRescaling` — the rescaling of an exchange to an invariant interval, the
    irreducibility of the block permutation, and the block length vector and permutation
    (`blockLam`, `blockPerm`, `mkIET1_rescale_subinterval`);
  * `IETFree.GeneratorChange` — the change of generators `(f, g) ↦ (g ∘ f, g)` and the transport of
    a word from the rescaled block back to the block;
  * `IETFree.InvariantInterval` — the restriction of `g` itself to an invariant interval, rescaled,
    with the same permutation;
  * `IETFree.BlockEndpoints` — the consequences of the explicit shape of the singularity list (the
    endpoints of a block are marked points), the almost-sure bookkeeping of Lemma 3.4, and the
    lengths of a block at a point of the region (`cellLen`, `blockLam`, `Block.lam`, `Block.perm`);
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

* `Challenge.lean`, `ChallengeWeak.lean` — the two statement files, one directory above `IETFree/`
  (modules `Challenge` and `ChallengeWeak`); they import only `Mathlib` and are imported by nothing.
  `Challenge` is display only (the frozen, unconditional challenge);
  `ChallengeWeak` is the comparator challenge of `comparator.json` (Theorem 1.1 with Masur–Veech and
  Veech's rigidity as hypotheses), and `IETFree.ChallengeWeakSolved` is its solution: it proves
  `main` and `coe_mkIETEquiv` from the library, and fills the definition hole `mkIETEquiv` with the
  library's definition.
-/
