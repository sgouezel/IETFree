/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.ChallengeSolved
public import IETFree.CutSet
public import IETFree.CutSetMeasure
public import IETFree.IET
public import IETFree.Pair.BlockAETransfer
public import IETFree.Pair.BlockAssembly
public import IETFree.Pair.BlockData
public import IETFree.Pair.BlockDatum
public import IETFree.Pair.BlockDiophantine
public import IETFree.Pair.BlockEndpoints
public import IETFree.Pair.BlockIrreducibility
public import IETFree.Pair.BlockLemma
public import IETFree.Pair.BlockRescaling
public import IETFree.Pair.Centralizer
public import IETFree.Pair.Commensurable
public import IETFree.Pair.Diophantine
public import IETFree.Pair.GeneratorChange
public import IETFree.Pair.GoodRegion
public import IETFree.Pair.IntegerAffine
public import IETFree.Pair.InvariantInterval
public import IETFree.Pair.Irreducible
public import IETFree.Pair.LengthMap
public import IETFree.Pair.MeasureTools
public import IETFree.Pair.Presentation
public import IETFree.Pair.ReductionData
public import IETFree.Pair.SingularityBound
public import IETFree.Pair.SingularityList
public import IETFree.Pair.SubintervalTransfer
public import IETFree.Pair.TranslationVector
public import IETFree.RauzyVeech.Affine
public import IETFree.RauzyVeech.BalancedSet
public import IETFree.RauzyVeech.BoundedSimplex
public import IETFree.RauzyVeech.ChildVolume
public import IETFree.RauzyVeech.ClosureSimplex
public import IETFree.RauzyVeech.ColDiam
public import IETFree.RauzyVeech.CylinderGrowth
public import IETFree.RauzyVeech.CylinderRecurrence
public import IETFree.RauzyVeech.CylinderVolume
public import IETFree.RauzyVeech.FirstReturn
public import IETFree.RauzyVeech.InvariantMeasure
public import IETFree.RauzyVeech.IterGlue
public import IETFree.RauzyVeech.IterGlue2
public import IETFree.RauzyVeech.LengthInjective
public import IETFree.RauzyVeech.LevelN
public import IETFree.RauzyVeech.LevyRecurrence
public import IETFree.RauzyVeech.MainComponents
public import IETFree.RauzyVeech.MeshShrink
public import IETFree.RauzyVeech.NameInfinite
public import IETFree.RauzyVeech.Nesting
public import IETFree.RauzyVeech.PairReach
public import IETFree.RauzyVeech.Path
public import IETFree.RauzyVeech.Peel
public import IETFree.RauzyVeech.PosBlock
public import IETFree.RauzyVeech.PosBlocks
public import IETFree.RauzyVeech.PrefixWord
public import IETFree.RauzyVeech.RauzyPath
public import IETFree.RauzyVeech.RauzyReach
public import IETFree.RauzyVeech.RayCriterion
public import IETFree.RauzyVeech.RayPath
public import IETFree.RauzyVeech.RayPointwise
public import IETFree.RauzyVeech.RefiningPartition
public import IETFree.RauzyVeech.RichPath.BadFirstStop
public import IETFree.RauzyVeech.RichPath.BoundedLag
public import IETFree.RauzyVeech.RichPath.CylinderMass
public import IETFree.RauzyVeech.RichPath.GradedInduction
public import IETFree.RauzyVeech.RichPath.HeightDichotomy
public import IETFree.RauzyVeech.RichPath.InductionAssembly
public import IETFree.RauzyVeech.RichPath.LargeLetter
public import IETFree.RauzyVeech.RichPath.LevelMass
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
public import IETFree.RauzyVeech.Step
public import IETFree.RauzyVeech.TowerCells
public import IETFree.RauzyVeech.TowerGlue
public import IETFree.RauzyVeech.TowerInjectivity
public import IETFree.RauzyVeech.TowerLevel
public import IETFree.RauzyVeech.TowerLevelN
public import IETFree.RauzyVeech.TowerLevelOne
public import IETFree.RauzyVeech.TowerTiling
public import IETFree.RauzyVeech.TrueStep
public import IETFree.RauzyVeech.Volume
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
public import IETFree.UniqueErgodicity.CompactTool
public import IETFree.UniqueErgodicity.Germ
public import IETFree.UniqueErgodicity.GermIterate
public import IETFree.UniqueErgodicity.IET
public import IETFree.UniqueErgodicity.Limits
public import IETFree.UniqueErgodicity.Main
public import IETFree.UniqueErgodicity.MainTheorem
public import IETFree.UniqueErgodicity.MeasPrep
public import IETFree.UniqueErgodicity.Split
public import IETFree.UniqueErgodicity.SubtypeConv
public import IETFree.UniqueErgodicity.Transfer
public import IETFree.UniqueErgodicity.TransferConv

/-!
# Interval exchange transformations

Root module of the `IETFree` library, which formalizes Theorem 1.1 of the paper: almost every pair
of interval exchange transformations does not generate a free group.  The tree has a single-exchange
layer at the root, the two-bijection datum `TopBotFormalism` on top of it, four thematic
subdirectories above them, and the challenge solution at the top.

* `IETFree/CutSet`, `IETFree/CutSetMeasure`, `IETFree/IET` — **one exchange**: cut sets and their
  cells, the measure theory of a piecewise translation, the predicate `IsIET`, the explicit
  construction `mkIETFun` / `mkIETEquiv` / `mkIET1'`, the simplex and its measure `simplexVolume`,
  the type `IET a b` with its group structure, and the three notions the main theorem is stated
  with, `Invariant`, `UniqueErgodic` (Definition 2.1) and `IsRigidByTranslations` (Definition 2.2).
  `unitMeas` (Lebesgue measure on `[0, 1)`) lives here too, since everything above uses it.

* `IETFree/TopBotFormalism` — interval exchanges in the Marmi–Moussa–Yoccoz framework for the
  Rauzy induction: a fixed alphabet with a top and a bottom permutation, the datum `IETDatum₂` and
  its simplex measure, and the translation to and from the single-permutation picture (`perm`,
  `ofPerm`).

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
  convergence of the Birkhoff averages — through the compact-space tool `CompactTool` (Tool 1 of the
  source), the split interval and its germ map, together with Lemma 2.9 (`exists_uniform_birkhoff`).

The theorem that uses them all is `IETFree/ChallengeSolved.lean`: the unconditional form of
Theorem 1.1, in the words of `Challenge.lean` (the comparator challenge one directory above).
-/

@[expose] public section

end
