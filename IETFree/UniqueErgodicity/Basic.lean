/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.RauzyVeech.InvariantMeasure
import IETFree.Basic

/-!
# The two forms of unique ergodicity: `UniqueErgodic` and `UniformBirkhoff`

`IETFree/IET.lean` defines `UniqueErgodic f` for an exchange `f` as the **weak** form, Definition
2.1 of the paper: there is exactly one invariant probability measure carried by `[0, 1)`.  This
directory proves the **strong** form, which the paper derives from it: the Birkhoff averages of
every continuous test function converge to their integral **uniformly** on `[0, 1)`.

The strong form is the predicate `UniformBirkhoff f` below, and the theorem that weak implies strong
is `UniqueErgodicity.uniformBirkhoff_of_uniqueErgodic`.  The transfer argument of this directory
works with the iterate `f^[i]` of the underlying function, hence the `birkhoffAverage` shape of the
averages (`UniformBirkhoff`, not the group power `f ^ i` of `IETFree/IET.lean`); `unitMeas` is the
library's Lebesgue measure on `[0, 1)`, from `IETFree/IET.lean`.

## What is proved where

The proof is in the modules of this directory:

* `UniqueErgodicity.CompactTool` — a continuous self-map of a compact space with a unique
  invariant probability measure has uniformly convergent Birkhoff averages (Tool 1 of the source,
  Yoccoz p. 55), in a "relative" form for later use;
* `UniqueErgodicity.Limits` — the one-sided limits of an interval exchange, and the fact that a
  periodic left limit of an exchange is a periodic interval, hence incompatible with unique
  ergodicity;
* `UniqueErgodicity.Split`, `UniqueErgodicity.Germ` — the split interval
  `[0+, 1-]` (the interval with only the interior singularities doubled) and the germ
  homeomorphism it carries;
* `UniqueErgodicity.Transfer` — the transfer of invariant measures from the split interval back
  to the exchange;
* `UniqueErgodicity.IET` — Theorem 2: `UniqueErgodic` implies `UniformBirkhoff`, first for
  `mkIET1 lam π` (via the germ map) and then for every exchange on `[0, 1)`, together with
  Lemma 2.9 (`exists_uniform_birkhoff`), the uniform bound on the Birkhoff sums of the indicator of
  a finite union of intervals.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

/-- **Uniform Birkhoff convergence**: the Birkhoff averages of every continuous test function
converge to their integral against Lebesgue measure on `[0, 1)`, uniformly over the initial point in
`[0, 1)`.

This is the *strong* form of unique ergodicity, stated in the form the transfer argument of this
directory produces.  It is not a second definition: `UniqueErgodic` (`IETFree/IET.lean`) is the
existence of a unique invariant probability measure carried by `[0, 1)`, and
`uniformBirkhoff_of_uniqueErgodic` (`UniqueErgodicity/IET.lean`) proves that unique ergodicity
implies this one — Theorem 2 of the blueprint. -/
def UniformBirkhoff (f : IET 0 1) : Prop :=
  ∀ ψ : ℝ → ℝ, Continuous ψ → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
    ∀ n ≥ N, ∀ x ∈ Set.Ico (0 : ℝ) 1,
      |birkhoffAverage ℝ ⇑f ψ n x - ∫ y, ψ y ∂unitMeas| ≤ ε

