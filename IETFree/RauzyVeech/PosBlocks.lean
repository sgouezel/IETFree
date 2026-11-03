/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.RauzyVeech.MainComponents
import IETFree.RauzyVeech.Peel
import IETFree.RauzyVeech.RayPointwise

/-!
# Positive blocks give the ray condition

This file proves the ray criterion from positive blocks: if the greedy path of `lam` runs through
positive Rauzy matrices at unbounded times, the entries of those matrices being bounded by one fixed
`M`, then every invariant probability measure carried by `[0, 1)` has length vector proportional to
`lam` (`positiveBlocksRay`, stated in full below).

The proof has three pieces, each in its own file:

* `PosBlock.spread_append_contract` (`IETFree/RauzyVeech/PosBlock.lean`): a positive block with
  entries in `[1, M]` multiplies the spread of the normalised columns by at most `1 - 1/(d·M)`, and
  appending letters never increases the spread (`PosBlock.spread_append_le`);
* `PosBlock.peel_of_contract` (`IETFree/RauzyVeech/Peel.lean`): peeling a chain of disjoint
  positive blocks off the greedy path, the spread tends to `0`;
* `RayPointwise.rayCondition_of_cols` (`IETFree/RauzyVeech/RayPointwise.lean`): coalescence of
  the normalised columns along the greedy path gives the ray condition (through
  `ColShrink.diam_le_of_cols_close`, the tower formula and `TowerGlue.ray_of_shrink_and_tower`).

The uniform bound `M` is what makes the product of the contraction factors tend to `0`; richness and
uniform positivity supply it a.e. with a single `M` (`MainTheorem.hasPositiveBlocks_ae`), which is
why the assembly `MainTheorem.main_of_components` needs nothing else from this file.  Positivity of
the coordinates of `lam` is not assumed: a positive block at time `0` gives it
(`RayPointwise.mem_simplexCyl_nil_of_mem`). Axiom-clean. -/


open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators Topology

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- **Positive blocks give the ray condition**, an everywhere statement: positive blocks with
entries in a fixed `[1, M]`, at unbounded times along the greedy path of `lam`, give the ray
condition.  No measure theory and no balance hypothesis on the heights: the normalised columns
coalesce (`PosBlock.peel_of_contract`) and the pointwise criterion
(`RayPointwise.rayCondition_of_cols`) concludes.

The condition `lam ∉ cylStop P (pathWord P lam k)` for every `k` is a null-set condition
(`IETDatum₂.ae_notMem_cylStop_all`): `cylStop` is where the renormalised length vector has a tie,
which the tower formula cannot handle; discharged a.e. in
`MainTheorem.rayCondition_of_components`.
Positivity of the coordinates of `lam` (`lam ∈ simplexCyl P []`) is *not* assumed: it follows from a
positive block (`RayPointwise.mem_simplexCyl_nil_of_mem`). -/
theorem positiveBlocksRay (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∀ (M : ℕ) (lam : α → ℝ≥0),
      (∀ k, lam ∉ IETDatum₂.cylStop P (IETDatum₂.pathWord P lam k)) →
      HasPositiveBlocks P lam M → RayCondition P lam := by
  intro M lam hstop hbl
  have : Nonempty α := Fintype.card_pos_iff.mp (by
    rw [Fintype.card_congr P.piTop, Fintype.card_fin]
    exact Nat.pos_of_ne_zero (NeZero.ne n))
  rcases Nat.eq_zero_or_pos M with hM | hM
  · exfalso
    subst hM
    obtain ⟨m, -, w, v, -, -, hQ⟩ := hbl 0
    have h1 := (hQ (Classical.arbitrary α) (Classical.arbitrary α)).1
    have h2 := (hQ (Classical.arbitrary α) (Classical.arbitrary α)).2
    omega
  · obtain ⟨m, -, w, v, -, hmem, -⟩ := hbl 0
    have h0 : lam ∈ IETDatum₂.simplexCyl P [] := RayPointwise.mem_simplexCyl_nil_of_mem P hmem
    exact RayPointwise.rayCondition_of_cols P hP hn h0 hstop
      (PosBlock.peel_of_contract P hP hn hM hstop hbl
        (fun γ δ => PosBlock.spread_append_le P γ δ)
        (fun γ δ h1 h2 => PosBlock.spread_append_contract P γ δ hM h1 h2))


