/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.ChallengeSolved
public import IETFree.CutSet.Basic
public import IETFree.CutSet.Measure
public import IETFree.FreeGroup.Centralizer
public import IETFree.FreeGroup.Commensurable
public import IETFree.IET
public import IETFree.ListPeriodicity
public import IETFree.Measure.CompactTool
public import IETFree.Measure.LevyRecurrence
public import IETFree.Measure.RefiningPartition
public import IETFree.Pair.Block.AETransfer
public import IETFree.Pair.Block.AeBlockGood
public import IETFree.Pair.Block.Assembly
public import IETFree.Pair.Block.BlockDatum
public import IETFree.Pair.Block.DiophantineTransfer
public import IETFree.Pair.Block.Endpoints
public import IETFree.Pair.Block.Irreducibility
public import IETFree.Pair.Block.Lemma
public import IETFree.Pair.Block.Rescaling
public import IETFree.Pair.Diophantine
public import IETFree.Pair.GeneratorChange
public import IETFree.Pair.GoodRegion
public import IETFree.Pair.IntegerAffine
public import IETFree.Pair.InvariantInterval
public import IETFree.Pair.Irreducible
public import IETFree.Pair.LengthMap
public import IETFree.Pair.MeasureTools
public import IETFree.Pair.Presentation
public import IETFree.Pair.ProductSimplex
public import IETFree.Pair.ReductionData
public import IETFree.Pair.RobustRelation.FreeParams
public import IETFree.Pair.RobustRelation.GoodParams
public import IETFree.Pair.RobustRelation.LetterData
public import IETFree.Pair.RobustRelation.OpenSet
public import IETFree.Pair.RobustRelation.Robustness
public import IETFree.Pair.RobustRelation.WordData
public import IETFree.Pair.Singularity.Bound
public import IETFree.Pair.Singularity.List
public import IETFree.Pair.SubintervalTransfer
public import IETFree.Pair.TranslationVector
public import IETFree.RauzyVeech.Affine
public import IETFree.RauzyVeech.BalancedSet
public import IETFree.RauzyVeech.BoundedSimplex
public import IETFree.RauzyVeech.ChildVolume
public import IETFree.RauzyVeech.ClosureSimplex
public import IETFree.RauzyVeech.CocycleVolume
public import IETFree.RauzyVeech.ColDiam
public import IETFree.RauzyVeech.Cylinder.Growth
public import IETFree.RauzyVeech.Cylinder.Recurrence
public import IETFree.RauzyVeech.FirstReturn
public import IETFree.RauzyVeech.InvariantMeasure
public import IETFree.RauzyVeech.IterGlue
public import IETFree.RauzyVeech.IterOKPath
public import IETFree.RauzyVeech.MainComponents
public import IETFree.RauzyVeech.MeshShrink
public import IETFree.RauzyVeech.NameInfinite
public import IETFree.RauzyVeech.Nesting
public import IETFree.RauzyVeech.PairReach
public import IETFree.RauzyVeech.Path
public import IETFree.RauzyVeech.Peel
public import IETFree.RauzyVeech.PosBlock
public import IETFree.RauzyVeech.PositiveBlocksRay
public import IETFree.RauzyVeech.PrefixWord
public import IETFree.RauzyVeech.RauzyPath
public import IETFree.RauzyVeech.RauzyReach
public import IETFree.RauzyVeech.Ray.Criterion
public import IETFree.RauzyVeech.Ray.PathHypotheses
public import IETFree.RauzyVeech.Ray.Pointwise
public import IETFree.RauzyVeech.RenormData
public import IETFree.RauzyVeech.RichPath.BoundedLag
public import IETFree.RauzyVeech.RichPath.CylinderMass
public import IETFree.RauzyVeech.RichPath.GradedInduction
public import IETFree.RauzyVeech.RichPath.HeightDichotomy
public import IETFree.RauzyVeech.RichPath.InductionAssembly
public import IETFree.RauzyVeech.RichPath.LargeLetter
public import IETFree.RauzyVeech.RichPath.LevelMass
public import IETFree.RauzyVeech.RichPath.LevelWords
public import IETFree.RauzyVeech.RichPath.MassFunction
public import IETFree.RauzyVeech.RichPath.MassGrowth
public import IETFree.RauzyVeech.RichPath.MinimalExit
public import IETFree.RauzyVeech.RichPath.MinimalExitMass
public import IETFree.RauzyVeech.RichPath.NodeHeight
public import IETFree.RauzyVeech.RichPath.Potential
public import IETFree.RauzyVeech.RichPath.RichGreedyPath
public import IETFree.RauzyVeech.RichPath.RichPathAssembly
public import IETFree.RauzyVeech.RichPath.Stopping
public import IETFree.RauzyVeech.RichPath.StraddleMass
public import IETFree.RauzyVeech.SimplexAe
public import IETFree.RauzyVeech.SimplexVolume
public import IETFree.RauzyVeech.Step
public import IETFree.RauzyVeech.Tower.Glue
public import IETFree.RauzyVeech.Tower.Injectivity
public import IETFree.RauzyVeech.Tower.Level
public import IETFree.RauzyVeech.Tower.LevelN
public import IETFree.RauzyVeech.Tower.LevelOne
public import IETFree.RauzyVeech.Tower.Node
public import IETFree.RauzyVeech.Tower.Tiling
public import IETFree.RauzyVeech.TrueStep
public import IETFree.Rigidity.Combinatorics
public import IETFree.Rigidity.Defs
public import IETFree.Rigidity.DimOne
public import IETFree.Rigidity.Hit
public import IETFree.Rigidity.Matrix
public import IETFree.Rigidity.RigidSet
public import IETFree.Rigidity.RigidStep
public import IETFree.Rigidity.Sequences
public import IETFree.Rigidity.Transport
public import IETFree.Rigidity.Veech
public import IETFree.TopBotFormalism
public import IETFree.UniqueErgodicity.Basic
public import IETFree.UniqueErgodicity.Germ.Basic
public import IETFree.UniqueErgodicity.Germ.Iterate
public import IETFree.UniqueErgodicity.Limits
public import IETFree.UniqueErgodicity.MainTheorem
public import IETFree.UniqueErgodicity.MeasPrep
public import IETFree.UniqueErgodicity.Split
public import IETFree.UniqueErgodicity.SubtypeConv
public import IETFree.UniqueErgodicity.Theorem2
public import IETFree.UniqueErgodicity.Transfer.Basic
public import IETFree.UniqueErgodicity.Transfer.Conv

/-!
# Interval exchange transformations

Root module of the `IETFree` library, which formalizes Theorem 1.1 of the paper: almost every pair
of interval exchange transformations does not generate a free group — Sébastien Gouëzel, *Almost
every pair of interval exchange transformations does not generate a free group*,
[arXiv:2610.29993](https://arxiv.org/abs/2610.29993) (2026).  The tree has a single-exchange layer
at the root, the two-bijection datum `TopBotFormalism` on top of it, the subject directories above
them (`CutSet`, `FreeGroup`, `Measure`, `Pair`, `RauzyVeech`, `Rigidity`, `UniqueErgodicity`), and
the challenge solution at the top.

**The three sources, and the short forms the docstrings use for them** (all eight references are
`sources:` entries of `formalization.yaml`, at the top of the project):

* *the paper* — Gouëzel, arXiv:2610.29993: the statement (Theorem 1.1), Definitions 2.1 and 2.2,
  Proposition 2.5 and the reduction of Section 3;
* *Yoccoz* — J.-C. Yoccoz, *Continued fraction algorithms for interval exchange maps: an
  introduction*: the Rauzy–Veech induction, the towers and the ray criterion, which is what
  `IETFree/RauzyVeech/` follows (its §5–§6 are not used);
* *AGY* — Appendix A of A. Avila, S. Gouëzel and J.-C. Yoccoz, *Exponential mixing for the
  Teichmüller flow*: the graded induction behind the rich path, which is what
  `IETFree/RauzyVeech/RichPath/` follows (its `Γ₁`–`Γ₄` are the appendix's).

Page numbers and numbered results ("Lemma 1 of Yoccoz (p. 16)", "AGY's `Γ₂`") resolve in the
document named.

* `IETFree/CutSet` (`Basic`, `Measure`), `IETFree/IET` — **one exchange**: cut sets and their
  cells, the measure theory of a piecewise translation, the predicate `IsIET`, the explicit
  construction `mkIETFun` / `mkIETEquiv` / `mkIET1'`, the simplex and its measure `simplexVolume`,
  the type `IET a b` with its group structure, and the three notions the main theorem is stated
  with, `Invariant`, `UniqueErgodic` (Definition 2.1) and `IsRigidByTranslations` (Definition 2.2).
  `unitMeas` (Lebesgue measure on `[0, 1)`) lives here too, since everything above uses it.

* `IETFree/TopBotFormalism` — interval exchanges in the Marmi–Moussa–Yoccoz framework for the
  Rauzy induction: a fixed alphabet with a top and a bottom permutation, the datum `IETDatum₂` and
  its simplex measure, and the translation to and from the single-permutation picture (`perm`,
  `ofPerm`).

* `IETFree/FreeGroup/` — the free-group facts the irreducible case uses: the computability of the
  length of a word, the centralizer of an element, and the commensurability criterion
  (`pow_eq_pow`), with the index `Fin 2` of the two generators introduced where it is needed.

* `IETFree/Measure/` — measure-theoretic tools that mention no exchange: the restriction to a
  refining partition (`RefiningPartition`) and Lévy's upward theorem for a filtration
  (`LevyRecurrence`).  Both are stated for a general measurable space, so they sit at the bottom of
  the tree rather than in the development that uses them.

* `IETFree/Pair/` — **two exchanges**: the free-group development (computability, the centralizer,
  the lattice bounds, Section 2's irreducible case, and Section 3's reduction to blocks: the length
  map, the good regions, the block rescalings, Lemmas 3.2–3.4 and the assembly of the per-block
  words).

* `IETFree/RauzyVeech/` — the Rauzy–Veech induction in the Marmi–Moussa–Yoccoz formalism: the step
  and the path matrices, the diagram, the volume of path cylinders, the columns and their spread,
  the ray criterion, the towers and their floors, and (in `RichPath/`) the proof that the greedy
  path is rich.  This is where almost every irreducible exchange is proved uniquely ergodic (after
  Kerckhoff) and rigid by translations (Veech's argument, phrased in Kerckhoff's framework), and it
  carries the invariant-measure side the induction steps use: `InvariantMeasure` (Lebesgue's
  measure, the cells and the length vector of a measure, and the uniqueness step) and
  `MainComponents` (the notions the ray criterion is phrased with).

* `IETFree/Rigidity/` — Veech's rigidity: a.e. rigidity by translations of an irreducible exchange,
  proved by the Rauzy–Veech induction.

* `IETFree/UniqueErgodicity/` — **unique ergodicity** of an exchange: the a.e. theorem and its
  assembly (`MainTheorem`), and the strong form — uniqueness of the invariant measure gives uniform
  convergence of the Birkhoff averages — through the compact-space tool `CompactTool` (Tool 1 of
  the Masur–Veech blueprint, reproduced in `HISTORY.md`, Part II), the split interval and its germ
  map, together with Lemma 2.9 (`exists_uniform_birkhoff`).

The theorem that uses them all is `IETFree/ChallengeSolved.lean`: the unconditional form of
Theorem 1.1, in the words of `Challenge.lean` (the comparator challenge one directory above).
-/

@[expose] public section

end
