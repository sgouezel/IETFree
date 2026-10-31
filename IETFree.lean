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
import IETFree.Check
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
import IETFree.Reduction
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
`ChallengeWeakSolved` (the solution of the comparator challenge, which nothing else imports) and
`Check` (the axiom report, whose `#print axioms` commands run when that module is compiled).  The
two statement files `Challenge.lean` and `ChallengeWeak.lean` sit one directory above `IETFree/` and
are not part of this module.  The individual modules are

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
* `IETFree.Reduction` — the umbrella module of the Section 3 development, which is split into
  `ReductionData` (blocks, pair-splitting singularities, the good set `O`), `Presentation` and
  `IntegerAffine` (the presentation of `g ∘ f` and its integer-affine functions), `SingularityList`,
  `GoodRegion`, `LengthMap` (Lemma 3.1), `SubintervalTransfer`, `BlockRescaling`, `GeneratorChange`,
  `InvariantInterval`, `BlockEndpoints`, `BlockAETransfer`, `BlockDiophantine`, `BlockData`,
  `BlockIrreducibility` (Lemma 3.2), `BlockAssembly`, `BlockDatum` and `BlockLemma` (Lemma 3.4 and
  Theorem 1.1);
* `Challenge.lean`, `ChallengeWeak.lean` — the two statement files, one directory above `IETFree/`
  (modules `Challenge` and `ChallengeWeak`); they import only `Mathlib` and are imported by nothing.
  `Challenge` is display only (the frozen, unconditional challenge);
  `ChallengeWeak` is the comparator challenge of `comparator.json` (Theorem 1.1 with Masur–Veech and
  Veech's rigidity as hypotheses), and `IETFree.ChallengeWeakSolved` is its solution: it proves
  `main` and `coe_mkIETEquiv` from the library, and fills the definition hole `mkIETEquiv` with the
  library's definition.
-/
