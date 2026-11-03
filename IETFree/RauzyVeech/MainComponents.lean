/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.RauzyVeech.InvariantMeasure
import IETFree.Basic
import IETFree.RauzyVeech.ColDiam

/-!
# The ray condition, and the positive blocks that yield it

This module carries the two *statements* the last step of the Masur–Veech proof is phrased with, and
nothing else: `RayCondition` (every invariant probability measure carried by `[0, 1)` has length
vector proportional to `λ`) and the positive-block vocabulary `HasPositiveBlockAt` /
`HasPositiveBlocks` that the ray criterion is fed with.

Both are definitions of *notions*, not assumptions: the theorems that produce them are
`RauzyVeech.PosBlocks.positiveBlocksRay` (positive blocks with one entry bound at unbounded times
give the ray condition, an everywhere statement) and `RauzyVeech.RayPointwise.rayCondition_of_cols`.
The a.e. assembly — richness plus the uniform bound on the entries gives those blocks a.e., which
gives the ray condition a.e. — is in `IETFree/UniqueErgodicity/MainTheorem.lean`, above the modules
that prove its two inputs.

Why the definitions live *here*: `RauzyVeech/PosBlocks.lean`, `RayPointwise.lean` and
`RichPath/*` all state their results with `RayCondition` or `HasPositiveBlocks`, so the notions must
sit below them; the assembly, which needs their proofs, sits above.

The measure-theoretic content: a positive block contracts the spread of the normalised columns by a
factor `1 - 1/(d·M_block)` in terms of its *own* bound, so only a bound valid for every block makes
the product over a chain of blocks vanish; along a greedy path the word is the *same* at every time,
and its entries are bounded uniformly.  That bound is a *lemma*, not a hypothesis:
`IETDatum₂.exists_uniform_bound'` gives one constant `C₁ ≥ 1` bounding the entries of a strictly
positive Rauzy matrix at every irreducible vertex, for every `2 ≤ n`
(`IETFree/RauzyVeech/PairReach.lean`). -/

open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators Topology

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## Positivity of the Rauzy matrices, and unique ergodicity from positive blocks -/

/-- A **positive block at time `m`**, with a **bound `M` on the entries**: some prefix `w` of
`lam`'s greedy path (of length `m`) reaches a vertex `IETDatum₂.vertex P w`, the next letters `v`
are followed by `lam`, and the Rauzy matrix of `v` at that vertex is entrywise in `[1, M]`.  The
bound belongs to the statement: the contraction factor of a block is `1 - 1/(d·M_block)` in terms of
*that block's* entry bound, so only a bound valid for every block of a path makes the product over a
chain of blocks tend to `0`.  In the assembly the word `v` is the *same* at every time (it comes
from `IETDatum₂.exists_uniform_bound'`), so boundedness is automatic there; asking for a bound
rather than for a fixed word is the more general hypothesis that the proof supports. -/
def HasPositiveBlockAt (P : IETDatum₂ α n) (lam : α → ℝ≥0) (M : ℕ) (m : ℕ) : Prop :=
  ∃ (w v : List Bool), w.length = m ∧ lam ∈ IETDatum₂.simplexCyl P (w ++ v) ∧
    ∀ a b, 1 ≤ IETDatum₂.Path.Q (IETDatum₂.vertex P w) v a b ∧
      IETDatum₂.Path.Q (IETDatum₂.vertex P w) v a b ≤ (M : ℤ)

/-- Positive blocks, all with the *same* entry bound `M`, at unbounded times. -/
def HasPositiveBlocks (P : IETDatum₂ α n) (lam : α → ℝ≥0) (M : ℕ) : Prop :=
  ∀ k : ℕ, ∃ m ≥ k, HasPositiveBlockAt P lam M m

/-- The **ray condition** at a length vector: every invariant probability measure carried by `[0,1)`
has length vector proportional to `λ`. -/
def RayCondition (P : IETDatum₂ α n) (lam : α → ℝ≥0) : Prop :=
  ∀ μ : ProbabilityMeasure ℝ, Invariant μ (P.toIET lam) → (μ : Measure ℝ) (Set.Ico (0:ℝ) 1) = 1 →
    ∃ c : ℝ, InvariantMeasure.lambdaOf μ P lam = c • (fun a : α => (lam a : ℝ))
