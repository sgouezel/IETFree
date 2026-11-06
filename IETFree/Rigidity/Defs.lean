/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.TrueStep
public import IETFree.TopBotFormalism

/-!
# Veech rigidity: the node vocabulary

This is the vocabulary of a proof of Veech's rigidity — that almost every exchange is rigid by
translations, `veechRigidity` in `IETFree/Pair/Irreducible.lean` — which runs along the greedy Rauzy
path of the length vector and starts from the richness of that path
(`RichPath.richGreedyPath`).

This module fixes the vocabulary of a **node** of the Rauzy diagram, i.e. of a prefix `γ` of the
greedy path of a length vector `lam`:

* `height P γ b` — the height of the tower over the letter `b`, the `b`-th column sum of the
  Rauzy matrix `Path.Q P γ`;
* `baseLen P γ lam` — the length `∑ a, (lamAfter P γ lam a : ℝ)` of the base interval at
  that node (in the node's own scale, not normalised);
* `BigCell P γ lam δ b` — the cell of `b` occupies at least `1 - δ` of that base;
* `deltaOf ε M` — the relative precision used by `rigid_step` as a function of the target
  precision `ε` and of the comparability constant `M` of the heights.

Nothing here is a source statement: the source-facing theorem is `veechRigidity`
(`IETFree/Pair/Irreducible.lean`), while the intermediate `ae_rigid_step` and `rigid_step` are
proved in `Rigidity/Veech.lean` and
`Rigidity/RigidStep.lean`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

namespace IETFree.Rigidity

/-- The height of the level-`γ` tower over the letter `b`: the `b`-th column sum of
`Path.Q P γ`. -/
noncomputable def height {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (γ : List Bool) (b : α) : ℕ :=
  ∑ a, (IETDatum₂.Path.Q P γ a b).toNat

/-- The length of the base interval at the node `γ`: `∑ a, (lamAfter P γ lam a : ℝ)`, in the
scale in which the original length vector sums to `1`. -/
noncomputable def baseLen {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) : ℝ :=
  ∑ a, (Tower.lamAfter P γ lam a : ℝ)

/-- The cell of the letter `b` is big at the node `γ`, with relative precision `δ`: it occupies at
least `1 - δ` of the base interval. -/
noncomputable def BigCell {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) (δ : ℝ) (b : α) : Prop :=
  (1 - δ) * baseLen P γ lam ≤ (Tower.lamAfter P γ lam b : ℝ)

/-- The relative precision of `rigid_step`, as a function of the target precision `ε` and of the
comparability constant `M` of the heights (`deltaOf`). -/
noncomputable def deltaOf (ε : ℝ) (M : ℕ) : ℝ := min (1/4) (ε / (8 * ((M : ℝ) + 2)))

end IETFree.Rigidity

end
