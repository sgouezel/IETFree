/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.Pair.Presentation
public import IETFree.Pair.ProductSimplex

/-!
# The two exchanges of a parameter pair, and the bridge to the length vectors

`fOf π q` and `gOf σ q` are the two exchanges of a free parameter pair `q : PReal d e`, as elements
of the group `IET 0 1`: the total exchanges `mkIET1 (simplexMap d q.1) π`, which are the identity
off the simplex of length vectors, so that statements about them carry no side condition.
`HasRelation
π σ q` says that some nontrivial word is trivial for the two of them.

The a.e. statement of the main theorem, `ae_hasRelation`, is *not* here: it consumes `main` and so
lives in `ChallengeSolved.lean`, above all of this.  What is here is the machinery that carries an
almost-sure statement between the two descriptions of the parameters, which is what makes that
consumption possible, and which is also what the Section 3 development needs:

* on the open region the total exchanges are `mkIET1'` of the length vectors
  (`fOf_eq_mkIET1'`, `gOf_eq_mkIET1'`), and a word is trivial for them exactly when it is trivial
  for `mkIET1'` (`hasRelation_iff_mkIET1'`);
* `evalWord_mkIET1'_eq_one_iff` passes between the two formalisations of the evaluation
  (`evalWord` on `IET` and `evalWordEquiv` on the underlying permutations of `ℝ`);
* `ae_free_of_ae_prod` pulls an almost-sure statement about length vectors back to the free
  coordinates, along the chart `prodSimplexMap` of `Pair/ProductSimplex.lean`.  No measurability of
  the predicate is needed, only measurability of the chart — which matters, because the statement of
  the main theorem is an existential over words.

The parameter space is `PReal d e`, the free lengths of the two exchanges.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace IntervalExchange.Pair

/-! ## 1. A word trivial for the permutations is trivial for the exchanges

These are the lemmas of part 3 of the transport, stated for general `IET`s of `[0, 1)` rather than
for the two exchanges of a parameter pair, since they are the only place where the two vocabularies
(the `IET` of the library and the underlying `Equiv ℝ ℝ`) meet. -/

section Bridge

variable {n m : ℕ} [NeZero n] [NeZero m]

/-- **The bridge from permutations to exchanges**: a word is trivial for the two exchanges
`mkIET1' lam π hl` and `mkIET1' mu σ hm` if and only if it is trivial for their underlying
permutations `mkIETEquiv lam π 0` and `mkIETEquiv mu σ 0`.

The forward direction is `evalWord_toEquiv_eq_one`; the reverse one is `evalWord_toEquiv` together
with `IET.ext`, since two exchanges with the same underlying permutation are equal. -/
theorem evalWord_mkIET1'_eq_one_iff {lam : Fin n → ℝ≥0} {π : Equiv.Perm (Fin n)}
    (hl : (∑ i, lam i) = 1) {mu : Fin m → ℝ≥0} {σ : Equiv.Perm (Fin m)}
    (hm : (∑ j, mu j) = 1) (w : FreeGroup Gen) :
    evalWord w (mkIET1' lam π hl) (mkIET1' mu σ hm) = 1 ↔
      evalWordEquiv w (mkIETEquiv lam π 0) (mkIETEquiv mu σ 0) = 1 := by
  constructor
  · exact evalWord_toEquiv_eq_one
  · intro h
    -- the `Equiv` of the evaluated word is that of the permutations, which is trivial
    have hcoe : (evalWord w (mkIET1' lam π hl) (mkIET1' mu σ hm)).toEquiv = 1 := by
      rw [evalWord_toEquiv]
      exact h
    -- `IET.ext` turns equality of the underlying permutations into equality of the exchanges
    refine IET.ext fun x => ?_
    have hx := congrArg (fun φ : Equiv ℝ ℝ => φ x) hcoe
    simpa using hx

/-- **The forward half of `evalWord_mkIET1'_eq_one_iff` alone**, in the form `main` produces it. -/
theorem evalWord_mkIET1'_eq_one {lam : Fin n → ℝ≥0} {π : Equiv.Perm (Fin n)}
    (hl : (∑ i, lam i) = 1) {mu : Fin m → ℝ≥0} {σ : Equiv.Perm (Fin m)}
    (hm : (∑ j, mu j) = 1) {w : FreeGroup Gen}
    (h : evalWordEquiv w (mkIETEquiv lam π 0) (mkIETEquiv mu σ 0) = 1) :
    evalWord w (mkIET1' lam π hl) (mkIET1' mu σ hm) = 1 :=
  (evalWord_mkIET1'_eq_one_iff hl hm w).2 h

end Bridge

variable {d e : ℕ} [NeZero d] [NeZero e]

/-! ## 2. The two exchanges of a parameter pair -/

/-- **The first exchange of a parameter pair**, as an element of the group `IET 0 1`: the interval
exchange with lengths `simplexMap d q.1` and permutation `π`, placed on `[0, 1)`.

It is the total version of `mkIET1' (simplexMap d q.1) π hl` (`mkIET1`): off the simplex of length
vectors it is the identity, which is what makes it defined for *every* `q : PReal d e` without
carrying the proof of `∑ simplexMap d q.1 = 1` around.  On the region it is `fOf_eq_mkIET1'`. -/
noncomputable def fOf (π : Equiv.Perm (Fin d)) (q : PReal d e) : IET 0 1 :=
  mkIET1 (simplexMap d q.1) π

/-- **The second exchange of a parameter pair**, as an element of the group `IET 0 1`; the
counterpart of `fOf` for the second permutation `σ`. -/
noncomputable def gOf (σ : Equiv.Perm (Fin e)) (q : PReal d e) : IET 0 1 :=
  mkIET1 (simplexMap e q.2) σ

omit [NeZero e] in
/-- **On the region, `fOf` is the exchange `mkIET1'`**: the unfolding of the total definition
`mkIET1` on the simplex, the total-length proof coming from the region through
`simplexMap_mem_simplex_fin`. -/
theorem fOf_eq_mkIET1' (π : Equiv.Perm (Fin d)) {q : PReal d e} (hq : q.1 ∈ simplexRegion d) :
    fOf π q = mkIET1' (simplexMap d q.1) π (simplexMap_mem_simplex_fin hq.1 hq.2) :=
  mkIET1_of_mem _

omit [NeZero d] in
/-- **On the region, `gOf` is the exchange `mkIET1'`**: the counterpart of `fOf_eq_mkIET1'`. -/
theorem gOf_eq_mkIET1' (σ : Equiv.Perm (Fin e)) {q : PReal d e} (hq : q.2 ∈ simplexRegion e) :
    gOf σ q = mkIET1' (simplexMap e q.2) σ (simplexMap_mem_simplex_fin hq.1 hq.2) :=
  mkIET1_of_mem _

/-- **Some nontrivial word in the two exchanges is trivial**: the paper's `(λ, μ) ∈ Ω`, for the
two exchanges `fOf π q` and `gOf σ q` of a parameter pair. -/
def HasRelation (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e))
    (q : PReal d e) : Prop :=
  ∃ w : FreeGroup Gen, w ≠ 1 ∧ evalWord w (fOf π q) (gOf σ q) = 1

/-- **`HasRelation` in terms of `mkIET1'`**, at a parameter pair of the open region: the two
descriptions differ only by the total-length proofs, which the region supplies.  This is the
form in which the relation is applied to the exchanges of `main`. -/
theorem hasRelation_iff_mkIET1' {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)} {q : PReal d e}
    (h1 : q.1 ∈ simplexRegion d) (h2 : q.2 ∈ simplexRegion e) :
    HasRelation π σ q ↔
      ∃ w : FreeGroup Gen, w ≠ 1 ∧
        evalWord w (mkIET1' (simplexMap d q.1) π (simplexMap_mem_simplex_fin h1.1 h1.2))
          (mkIET1' (simplexMap e q.2) σ (simplexMap_mem_simplex_fin h2.1 h2.2)) = 1 := by
  rw [HasRelation, fOf_eq_mkIET1' π h1, gOf_eq_mkIET1' σ h2]

/-- **The bridge in free coordinates**, at a parameter pair of the open region: a word trivial for
the two permutations of `main` is trivial for `fOf` and `gOf`. -/
theorem evalWord_fOf_eq_one {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)} {q : PReal d e}
    (h1 : q.1 ∈ simplexRegion d) (h2 : q.2 ∈ simplexRegion e) {w : FreeGroup Gen}
    (h : evalWordEquiv w (mkIETEquiv (simplexMap d q.1) π 0)
      (mkIETEquiv (simplexMap e q.2) σ 0) = 1) :
    evalWord w (fOf π q) (gOf σ q) = 1 := by
  rw [fOf_eq_mkIET1' π h1, gOf_eq_mkIET1' σ h2]
  exact evalWord_mkIET1'_eq_one _ _ h

/-! ## 3. Pulling an almost-sure statement back to the free coordinates -/

omit [NeZero d] [NeZero e] in
/-- **The dual of `ae_prod_of_ae_free`**: an almost-sure statement about length vectors holds for
almost every pair of free coordinates.

`(simplexVolume d).prod (simplexVolume e)` is the pushforward of the product of the two restricted
Lebesgue measures under `prodSimplexMap d e` (`prod_simplexVolume_eq_map`), and
`MeasureTheory.ae_of_ae_map` pulls a hypothesis about a pushforward back along a measurable map.  No
measurability of the predicate is needed — that is the point of the lemma, since the statement of
Theorem 1.1 is an existential over words and is not known to be measurable. -/
theorem ae_free_of_ae_prod {P : (Fin d → ℝ≥0) × (Fin e → ℝ≥0) → Prop}
    (h : ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)), P p) :
    ∀ᵐ q ∂((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))),
      P (prodSimplexMap d e q) := by
  rw [prod_simplexVolume_eq_map] at h
  exact ae_of_ae_map (measurable_prodSimplexMap d e).aemeasurable h

end IntervalExchange.Pair
