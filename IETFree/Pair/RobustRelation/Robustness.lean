/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.Pair.RobustRelation.LetterData

/-!
# The robustness of a trivial word

A word which is trivial at a point `q₀` of the open region is trivial on a neighbourhood of `q₀`, at
least when `q₀` carries no nontrivial integer relation between the free lengths: that is the paper's
set `Ω'` (`∀ N, q₀ ∈ goodParamsAt N d e`), and it is the hypothesis of `evalWord_eventually_eq_one`.

The proof is in `WordData.lean`: the word's symbolic data at `q₀` exists (`exists_wordData_ne_nil`,
which starts from the four one-letter cases of `LetterData.lean` and composes them), and on the ball
where that data holds the word is a translation on each of its pieces, with displacements that
vanish at `q₀` by hypothesis and hence identically.

`evalWord_eventually_eq_one_of_goodParams` is the same statement with the numerical threshold
`4 * |w| + 4` in place of `Ω'` — the bound that the distinctness of the candidate cuts costs if one
keeps one — and `evalWord_eventually_eq_one_of_vanishesAt` is the form in which the vanishing
property is an explicit hypothesis, which is what makes the other two one-liners.
-/


@[expose] public section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace IntervalExchange.Pair

/-- **The robustness of a trivial word**: for a word `w`, if `w` is trivial at a point `q₀` of the
open region at which no nontrivial integer relation between the free lengths vanishes, then `w` is
trivial on a neighbourhood of `q₀`. -/
theorem evalWord_eventually_eq_one {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) (w : FreeGroup Gen) {q₀ : PReal d e}
    (hq₀ : q₀.1 ∈ simplexRegion d ∧ q₀.2 ∈ simplexRegion e)
    (hgood : ∀ N, q₀ ∈ goodParamsAt N (d := d) (e := e))
    (h1 : evalWord w (fOf π q₀) (gOf σ q₀) = 1) :
    ∀ᶠ q in 𝓝 q₀, evalWord w (fOf π q) (gOf σ q) = 1 :=
  evalWord_eventually_eq_one_of_vanishesAt π σ w (4 * (w.toWord).length + 4)
    (vanishesAt_of_omega hgood _) le_rfl h1 (exists_wordData_singleton π σ hq₀)

/-- **The robustness of a trivial word, at a numerical threshold**: the same statement with
`q₀ ∈ goodParamsAt (4 * |w| + 4)` in place of `Ω'`.  The two hypotheses are not interchangeable:
`∀ N, q₀ ∈ goodParamsAt N` implies `q₀ ∈ goodParamsAt (4|w|+4)` by `goodParamsAt_antitone`, so the
`Ω'` statement is the stronger one. -/
theorem evalWord_eventually_eq_one_of_goodParams {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) (w : FreeGroup Gen) {q₀ : PReal d e}
    (hq₀ : q₀.1 ∈ simplexRegion d ∧ q₀.2 ∈ simplexRegion e)
    (hgood : q₀ ∈ goodParamsAt (4 * (w.toWord).length + 4) (d := d) (e := e))
    (h1 : evalWord w (fOf π q₀) (gOf σ q₀) = 1) :
    ∀ᶠ q in 𝓝 q₀, evalWord w (fOf π q) (gOf σ q) = 1 :=
  evalWord_eventually_eq_one_of_vanishesAt π σ w (4 * (w.toWord).length + 4)
    (vanishesAt_of_goodParams hgood) le_rfl h1 (exists_wordData_singleton π σ hq₀)

end IntervalExchange.Pair
