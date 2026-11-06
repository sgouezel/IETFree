/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.BoundedSimplex
public import IETFree.RauzyVeech.ClosureSimplex
public import IETFree.RauzyVeech.RauzyPath

/-!
# The path hypotheses of the ray criterion

`RayCriterion.eq_of_nonneg_preimage_of_diam` needs, for a.e. `lam`, a sequence `w` of words with
`lam ∈ simplexCyl P (w k)` for all `k`, the cylinders antitone, and the first one bounded.  This
file records the two structural facts for the greedy path of `IETFree/RauzyVeech/RauzyPath.lean`:
the cylinders `simplexCyl P (pfx p k)` are antitone (`antitone_simplexCyl_pfx`) and the first one is
bounded (`isBounded_simplexCyl_pfx`). -/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators Topology

namespace RayCriterion

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- The cylinders along a path are antitone. -/
theorem antitone_simplexCyl_pfx (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (p : ℕ → Bool) : Antitone fun k => IETDatum₂.simplexCyl P (PrefixWord.pfx p k) := by
  refine antitone_nat_of_succ_le fun k => ?_
  have h := simplexCyl_pfx_succ_subset P hP hn p k
  exact h

/-- The first cylinder of a path is bounded. -/
theorem isBounded_simplexCyl_pfx (P : IETDatum₂ α n) (p : ℕ → Bool) :
    Bornology.IsBounded (IETDatum₂.simplexCyl P (PrefixWord.pfx p 0)) := by
  refine BoundedSimplex.isBounded_simplexCyl P (PrefixWord.pfx p 0)

end RayCriterion

end
