/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.UniqueErgodicity.TransferConv
import IETFree.UniqueErgodicity.MeasPrep

/-!
# Restricting the germ map to its invariant part

Tool 1 is applied to the compact space `↥(SplitI.rightPart D)`, not to the whole split interval:
the two deleted points of Blueprint 2 Remark 2.7 are isolated fixed points, so unique ergodicity
holds on `rightPart` only.  This file is the glue between the two formulations: it identifies the
Birkhoff averages of a self-map `G` of the split interval, started at a point of `rightPart`, with
the Birkhoff averages of the restricted map of the subtype, and transfers uniform convergence
accordingly.

Nothing here is mathematical: it is the `Subtype` bookkeeping that the assembly in
`UniqueErgodicity.IET` needs, kept separate so that it is proved once.
-/

open MeasureTheory Filter
open scoped BigOperators

namespace IETFree.UniqueErgodicity

variable {D : Set ℝ}

/-- The germ map restricted to its invariant part `rightPart`, as a self-map of the compact space
`↥(SplitI.rightPart D)`. -/
def restrictTo (G : SplitI D → SplitI D)
    (hG : Set.MapsTo G (SplitI.rightPart D) (SplitI.rightPart D)) :
    ↥(SplitI.rightPart D) → ↥(SplitI.rightPart D) :=
  fun w => ⟨G w.1, hG w.2⟩

/-- **The iterates of the restricted map are the iterates of the map**, read in the ambient
space.  Stated through the coercion so that the proof component of the subtype never has to be
compared. -/
theorem coe_iterate_restrictTo (G : SplitI D → SplitI D)
    (hG : Set.MapsTo G (SplitI.rightPart D) (SplitI.rightPart D)) (n : ℕ) (z : SplitI D)
    (hz : z ∈ SplitI.rightPart D) :
    ((restrictTo G hG)^[n] ⟨z, hz⟩ : SplitI D) = G^[n] z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact congrArg G (ih z hz)

/-- **Birkhoff averages agree** between the map and its restriction, from a point of the invariant
part. -/
theorem birkhoffAverage_restrictTo (G : SplitI D → SplitI D)
    (hG : Set.MapsTo G (SplitI.rightPart D) (SplitI.rightPart D)) (ψ : SplitI D → ℝ) (n : ℕ)
    (z : SplitI D) (hz : z ∈ SplitI.rightPart D) :
    birkhoffAverage ℝ G ψ n z
      = birkhoffAverage ℝ (restrictTo G hG) (fun w => ψ w.1) n ⟨z, hz⟩ := by
  simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [coe_iterate_restrictTo G hG i z hz]

/-- **Uniform convergence on the subtype gives uniform convergence on the invariant part.** This is
the form in which Tool 1's conclusion is consumed by `TransferConv.uniqueErgodicFun_of_proj`. -/
theorem forall_mem_rightPart_of_subtype (G : SplitI D → SplitI D)
    (hG : Set.MapsTo G (SplitI.rightPart D) (SplitI.rightPart D)) (ψ : SplitI D → ℝ) {c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∀ w : ↥(SplitI.rightPart D),
      |birkhoffAverage ℝ (restrictTo G hG) (fun w => ψ w.1) n w - c| ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∀ z ∈ SplitI.rightPart D,
      |birkhoffAverage ℝ G ψ n z - c| ≤ ε := by
  intro ε hε
  obtain ⟨N, hN, hN'⟩ := h ε hε
  exact ⟨N, hN, fun n hn z hz => by
    rw [birkhoffAverage_restrictTo G hG ψ n z hz]
    exact hN' n hn ⟨z, hz⟩⟩

end IETFree.UniqueErgodicity

