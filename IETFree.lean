/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.Basic
import IETFree.ChallengeSolved
import IETFree.CutSet
import IETFree.CutSetMeasure
import IETFree.IET
import IETFree.Pair.BlockAETransfer
import IETFree.Pair.BlockAssembly
import IETFree.Pair.BlockData
import IETFree.Pair.BlockDatum
import IETFree.Pair.BlockDiophantine
import IETFree.Pair.BlockEndpoints
import IETFree.Pair.BlockIrreducibility
import IETFree.Pair.BlockLemma
import IETFree.Pair.BlockRescaling
import IETFree.Pair.Centralizer
import IETFree.Pair.Commensurable
import IETFree.Pair.Diophantine
import IETFree.Pair.GeneratorChange
import IETFree.Pair.GoodRegion
import IETFree.Pair.IntegerAffine
import IETFree.Pair.InvariantInterval
import IETFree.Pair.Irreducible
import IETFree.Pair.LengthMap
import IETFree.Pair.MeasureTools
import IETFree.Pair.Presentation
import IETFree.Pair.ReductionData
import IETFree.Pair.SingularityBound
import IETFree.Pair.SingularityList
import IETFree.Pair.SubintervalTransfer
import IETFree.Pair.TranslationVector
import IETFree.RauzyVeech.Affine
import IETFree.RauzyVeech.BalancedSet
import IETFree.RauzyVeech.BoundedSimplex
import IETFree.RauzyVeech.ChildVolume
import IETFree.RauzyVeech.ClosureSimplex
import IETFree.RauzyVeech.ColDiam
import IETFree.RauzyVeech.CylinderGrowth
import IETFree.RauzyVeech.CylinderRecurrence
import IETFree.RauzyVeech.CylinderVolume
import IETFree.RauzyVeech.FirstReturn
import IETFree.RauzyVeech.InvariantMeasure
import IETFree.RauzyVeech.IterGlue
import IETFree.RauzyVeech.IterGlue2
import IETFree.RauzyVeech.LengthInjective
import IETFree.RauzyVeech.LevelN
import IETFree.RauzyVeech.LevyRecurrence
import IETFree.RauzyVeech.MainComponents
import IETFree.RauzyVeech.MeshShrink
import IETFree.RauzyVeech.NameInfinite
import IETFree.RauzyVeech.Nesting
import IETFree.RauzyVeech.PairReach
import IETFree.RauzyVeech.Path
import IETFree.RauzyVeech.Peel
import IETFree.RauzyVeech.PosBlock
import IETFree.RauzyVeech.PosBlocks
import IETFree.RauzyVeech.PrefixWord
import IETFree.RauzyVeech.RauzyPath
import IETFree.RauzyVeech.RauzyReach
import IETFree.RauzyVeech.RayCriterion
import IETFree.RauzyVeech.RayPath
import IETFree.RauzyVeech.RayPointwise
import IETFree.RauzyVeech.RefiningPartition
import IETFree.RauzyVeech.RichPath.BadFirstStop
import IETFree.RauzyVeech.RichPath.BoundedLag
import IETFree.RauzyVeech.RichPath.CylinderMass
import IETFree.RauzyVeech.RichPath.GradedInduction
import IETFree.RauzyVeech.RichPath.HeightDichotomy
import IETFree.RauzyVeech.RichPath.InductionAssembly
import IETFree.RauzyVeech.RichPath.LargeLetter
import IETFree.RauzyVeech.RichPath.LevelMass
import IETFree.RauzyVeech.RichPath.MassFunction
import IETFree.RauzyVeech.RichPath.MassGrowth
import IETFree.RauzyVeech.RichPath.MinimalExit
import IETFree.RauzyVeech.RichPath.MinimalExitMass
import IETFree.RauzyVeech.RichPath.NodeHeight
import IETFree.RauzyVeech.RichPath.Potential
import IETFree.RauzyVeech.RichPath.RichGreedyPath
import IETFree.RauzyVeech.RichPath.RichPathAssembly
import IETFree.RauzyVeech.RichPath.Stopping
import IETFree.RauzyVeech.RichPath.StraddleMass
import IETFree.RauzyVeech.SimplexAe
import IETFree.RauzyVeech.Step
import IETFree.RauzyVeech.TowerCells
import IETFree.RauzyVeech.TowerGlue
import IETFree.RauzyVeech.TowerInjectivity
import IETFree.RauzyVeech.TowerLevel
import IETFree.RauzyVeech.TowerLevelN
import IETFree.RauzyVeech.TowerLevelOne
import IETFree.RauzyVeech.TowerTiling
import IETFree.RauzyVeech.TrueStep
import IETFree.RauzyVeech.Volume
import IETFree.Rigidity.Combinatorics
import IETFree.Rigidity.Defs
import IETFree.Rigidity.DimOne
import IETFree.Rigidity.Hit
import IETFree.Rigidity.Matrix
import IETFree.Rigidity.RigidSet
import IETFree.Rigidity.RigidStep
import IETFree.Rigidity.Sequences
import IETFree.Rigidity.Transport
import IETFree.Rigidity.Veech
import IETFree.UniqueErgodicity.Basic
import IETFree.UniqueErgodicity.Germ
import IETFree.UniqueErgodicity.GermIterate
import IETFree.UniqueErgodicity.IET
import IETFree.UniqueErgodicity.Limits
import IETFree.UniqueErgodicity.Main
import IETFree.UniqueErgodicity.MainTheorem
import IETFree.UniqueErgodicity.MeasPrep
import IETFree.UniqueErgodicity.Split
import IETFree.UniqueErgodicity.SubtypeConv
import IETFree.UniqueErgodicity.Transfer
import IETFree.UniqueErgodicity.TransferConv
import IETFree.UniqueErgodicity.CompactTool

/-!
# Interval exchange transformations

Root module of the `IETFree` library.  The tree has four thematic subdirectories above a
single-exchange layer:

* `IETFree/CutSet`, `IETFree/CutSetMeasure`, `IETFree/IET` — **one exchange**: cut sets and their
  cells, the measure theory of a piecewise translation, the predicate `IsIET`, the explicit
  construction `mkIETFun` / `mkIETEquiv` / `mkIET1'`, the simplex and its measure `simplexVolume`,
  the type `IET a b` with its group structure, and the two notions the main theorem is stated with,
  `Invariant` and `UniqueErgodic`.  `unitMeas` (Lebesgue measure on `[0, 1)`) lives here too, since
  everything above uses it.  `IETFree/Basic` holds the two-bijection datum `IETDatum₂` and
  `IsRigidByTranslations`.

* `IETFree/Pair/` — **two exchanges**: the free-group development (computability, the centralizer,
  the lattice bounds, Section 2's irreducible case, and Section 3's reduction to blocks: the length
  map, the good regions, the block rescalings, Lemmas 3.2–3.4 and the assembly of the per-block
  words).

* `IETFree/RauzyVeech/` — the Rauzy–Veech induction: the step and the path matrices, the diagram,
  the volume of path cylinders, the columns and their spread, the ray criterion, the towers and
  their floors, and (in `RichPath/`) the proof that the greedy path is rich.  It also carries
  `InvariantMeasure` and `MainComponents`, the invariant-measure side the induction steps use.

* `IETFree/Rigidity/` — Veech's rigidity: a.e. rigidity by translations of an irreducible exchange,
  proved by the Rauzy–Veech induction.

* `IETFree/UniqueErgodicity/` — **unique ergodicity** of an exchange: the a.e. theorem and its
  assembly (`MainTheorem`), and the Birkhoff-averages form, uniqueness of the invariant measure
  giving uniform convergence of the Birkhoff averages through the split interval and its germ map.
  The measure-theoretic input is in `IETFree/RauzyVeech/`: `InvariantMeasure` (Lebesgue as an
  invariant measure, the cells and the length vector of a measure, and the uniqueness step) and
  `MainComponents` (the notions the ray criterion is phrased with).

The theorem that uses them all is `IETFree/ChallengeSolved.lean`: the unconditional form of
Theorem 1.1, in the words of `Challenge.lean` (the comparator challenge one directory above).
-/
