/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.Pair.Block.Lemma
public import IETFree.Pair.ProductSimplex
public import IETFree.Pair.RobustRelation.FreeParams
public import IETFree.Pair.RobustRelation.OpenSet

/-!
# The solution of the challenge

`Challenge.main`, the unconditional form of Theorem 1.1 of Sébastien Gouëzel, *Almost every pair
of interval exchange transformations does not generate a free group* (arXiv:2610.29993), in the
words of the challenge.

`Challenge.lean`, one directory above `IETFree/`, states Theorem 1.1 in Mathlib-only language:

  for almost every pair of length vectors `(λ, μ)` of total mass `1`, the two exchanges
  `mkIETFun λ π 0` and `mkIETFun μ σ 0` satisfy a nontrivial relation in the group of permutations
  of `ℝ`.

It declares its own copies of the definitions the statement needs, with the same names and bodies as
the library's, so that the comparator holds declaration by declaration.  Two declarations are holes
there — the definition `mkIETEquiv` and the theorem `coe_mkIETEquiv` — and this file fills them with
the library's, exactly as `IETFree/IET.lean` has them.

## How the proof goes

`Challenge.main` is the statement that `IETFree/Pair/` proves *conditionally*, on two inputs:

* `masurVeech` — almost every irreducible exchange is uniquely ergodic;
* `veechRigidity` — almost every irreducible exchange is rigid by translations,

both stated for `mkIET1' λ π h : IET 0 1` and both proved (`IETFree/Pair/Irreducible.lean`, by the
Rauzy–Veech induction of `IETFree/RauzyVeech/` and by `IETFree/Rigidity/`), so nothing is left as a
hypothesis here either.

From there, the mathematical content is Lemma 3.4 for almost every length vector
(`exists_word_ae`, from `main_theorem_of_blocks` — the a.e. block data of
`exists_ae_block_good` plus the assembly `exists_word_trivial_on_all_of_blocks`),
repackaged into the permutations `mkIETEquiv p_i π 0` by `evalWord_toEquiv_eq_one`, with
`simplexMap d (toReal p).1 = p.1` almost everywhere (`ae_toReal_simplexMap`).

The root theorem `main` is `Challenge.main` in its words, and carries the proof above.

The remark that follows the main theorem is proved here as well, in the `Pair` namespace: an
open set of full measure of pairs not generating a free group, on the paper's `Δ_π × Δ_σ`
(`exists_isOpen_ae_exists_nontrivial_evalWordEquiv_eq_one`).  The machinery behind it is in
`IETFree/Pair/RobustRelation/`, which sits *below* this file: its assembly
(`exists_isOpen_subset_hasRelation_of_ae`) takes the almost-sure relation as a hypothesis precisely
so that it can, and the file proves that hypothesis from `main` — through the chart of
`Pair/ProductSimplex.lean` — and feeds it in.  The challenge's vocabulary (`evalWordEquiv`) lives in
`Pair/MeasureTools.lean` and that chart in `Pair/ProductSimplex.lean`, both below, where the
Section 3 machinery uses them too.

The file ends with the `#print axioms` reports of the tree: the main theorem and the two
conclusions of the remark.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open IntervalExchange.Pair IntervalExchange.RauzyVeech IntervalExchange.Rigidity
open IntervalExchange.UniqueErgodicity

namespace IntervalExchange

/-! ## The mathematical content of the theorem, in the library's language -/

/-- **Lemma 3.4 for almost every length vector**: every pair of data with those lengths carries a
nontrivial word which is the identity on `[0, 1)`.  This is the content of the weak challenge, with
the exchanges of the library. -/
theorem exists_word_ae {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
      ∀ (D : IETDatum d) (E : IETDatum e), D.perm = π → E.perm = σ →
        D.v = (toReal p).1 → E.v = (toReal p).2 →
          ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧ evalWord w D.toIET E.toIET = 1 := by
  refine ae_prod_of_ae_free (P := fun p => ∀ (D : IETDatum d) (E : IETDatum e),
    D.perm = π → E.perm = σ → D.v = (toReal p).1 → E.v = (toReal p).2 →
      ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧ evalWord w D.toIET E.toIET = 1) ?_
  filter_upwards [main_theorem_of_blocks π σ,
    ae_mem_simplexRegion_prod (d := d) (e := e)] with z hz hzmem
  obtain ⟨a, b⟩ := z
  have htw : toReal (prodSimplexMap d e (a, b)) = (a, b) :=
    toReal_prodSimplexMap hzmem.1 hzmem.2
  rw [htw]
  intro D E hDπ hEπ hDv hEv
  obtain ⟨n, u, v, hcover, hfu, hgu, hw⟩ := hz D E hDπ hEπ hDv hEv
  exact exists_word_trivial_on_all_of_blocks D E u v hcover hfu hgu hw

/-! ## The theorem of the challenge file -/

/-- **Theorem 1.1 of the paper**: for almost every pair of length vectors of total mass `1`, the two
exchanges satisfy a nontrivial relation in the group of permutations of `ℝ`.  This is
`Challenge.main`, in its words, with nothing left as a hypothesis: Masur–Veech's theorem and
Veech's rigidity are applied inside the proof.  The a.e. statement is not vacuous: the measure it is
taken with, `simplexVolume d × simplexVolume e`, is nonzero (`simplexVolume_ne_zero`), so "almost
every pair" is a set of positive measure. -/
theorem main {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
      ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧
        evalWordEquiv w (mkIETEquiv p.1 π 0) (mkIETEquiv p.2 σ 0) = 1 := by
  -- Lemma 3.4 in the library's language
  have hQ := exists_word_ae π σ
  -- the free coordinates of almost every length vector lie in the region
  have hregmeas : MeasurableSet {p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0) |
      toReal p ∈ simplexRegion d ×ˢ simplexRegion e} :=
    ((measurableSet_simplexRegion d).prod (measurableSet_simplexRegion e)).preimage
      continuous_toReal.measurable
  have hreg : ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
      toReal p ∈ simplexRegion d ×ˢ simplexRegion e := by
    rw [prod_simplexVolume_eq_map,
      MeasureTheory.ae_map_iff (measurable_prodSimplexMap d e).aemeasurable
        hregmeas]
    filter_upwards [ae_mem_simplexRegion_prod (d := d) (e := e)] with z hz
    obtain ⟨v, w⟩ := z
    rw [toReal_prodSimplexMap hz.1 hz.2]
    exact hz
  filter_upwards [hQ, hreg, ae_toReal_simplexMap (d := d) (e := e)]
    with p hp hpmem hfix
  -- the data with lengths `p`
  obtain ⟨w, hw1, hw2⟩ := hp ⟨π, (toReal p).1, hpmem.1⟩ ⟨σ, (toReal p).2, hpmem.2⟩ rfl rfl rfl rfl
  refine ⟨w, hw1, ?_⟩
  -- the same word, in the permutations of `ℝ`
  have hw3 : evalWordEquiv w (mkIETEquiv (simplexMap d (toReal p).1) π 0)
      (mkIETEquiv (simplexMap e (toReal p).2) σ 0) = 1 :=
    evalWord_toEquiv_eq_one hw2
  -- and the length vectors are those of `p`
  have hp1 : p.1 = simplexMap d (toReal p).1 := (congrArg Prod.fst hfix).symm
  have hp2 : p.2 = simplexMap e (toReal p).2 := (congrArg Prod.snd hfix).symm
  rwa [hp1, hp2]


/-! ## The remark after the main theorem

The remark that follows Theorem 1.1 states that the relation of a trivial word is robust, and that
therefore the pairs not generating a free group contain an open set of full measure.  The machinery
is in `IETFree/Pair/RobustRelation/` — the parametrised bad set, the symbolic data of an arbitrary
word with the robustness of a trivial word, and the assembly of the open set from an almost-sure
input.  That assembly takes the a.e. statement as a hypothesis, precisely so that it can sit below
this file; what is proved here is the hypothesis, from `main` through the chart of
`Pair/ProductSimplex.lean`, and then the conclusion on `Δ_π × Δ_σ`. -/

namespace Pair

/-- **The remark after the main theorem, on `Δ_π × Δ_σ`**: the pairs of length vectors not
generating a free group contain an open set of full measure, in the paper's coordinates.

The conclusion is written out — at every `p ∈ O` whose two vectors have total mass `1` there is a
nontrivial word `w` with `evalWordEquiv w (mkIETEquiv p.1 π 0) (mkIETEquiv p.2 σ 0) = 1` — rather
than through a predicate on the relation set, and the two normalisation conditions are hypotheses
rather
than an intersection with `simplex (Fin d) ×ˢ simplex (Fin e)`.  The statement therefore names only
`mkIETEquiv`, `evalWordEquiv`, `FreeGroup (Fin 2)`, `simplexVolume` and the measure — every one of
them declared by `Challenge.lean` — so it can be used as a standalone target without adding any
definition. -/
theorem exists_isOpen_ae_exists_nontrivial_evalWordEquiv_eq_one {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) :
    ∃ O : Set ((Fin d → ℝ≥0) × (Fin e → ℝ≥0)), IsOpen O ∧
      ((simplexVolume d).prod (simplexVolume e)) Oᶜ = 0 ∧
      (∀ p ∈ O, (∑ i, p.1 i = 1) → (∑ j, p.2 j = 1) →
        ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧
          evalWordEquiv w (mkIETEquiv p.1 π 0) (mkIETEquiv p.2 σ 0) = 1) := by
  -- the a.e. statement in the free coordinates, from `main` through the chart
  have hrel : ∀ᵐ q ∂((volume.restrict (simplexRegion d)).prod
      (volume.restrict (simplexRegion e))), HasRelation π σ q := by
    have hpull : ∀ᵐ q ∂((volume.restrict (simplexRegion d)).prod
        (volume.restrict (simplexRegion e))),
        ∃ w : FreeGroup Gen, w ≠ 1 ∧
          evalWordEquiv w (mkIETEquiv (simplexMap d q.1) π 0)
            (mkIETEquiv (simplexMap e q.2) σ 0) = 1 :=
      ae_free_of_ae_prod (main π σ)
    filter_upwards [hpull, ae_mem_simplexRegion_prod (d := d) (e := e)] with q hq hreg
    obtain ⟨w, hw_ne, hw⟩ := hq
    exact ⟨w, hw_ne, evalWord_fOf_eq_one hreg.1 hreg.2 hw⟩
  exact exists_isOpen_ae_exists_nontrivial_evalWordEquiv_eq_one_of_ae π σ hrel

end Pair

-- The axiom check of the library: the `#print axioms` reports of the tree, for the main theorem and
-- for the conclusion of the remark after it.
#print axioms main
#print axioms IntervalExchange.Pair.exists_isOpen_ae_exists_nontrivial_evalWordEquiv_eq_one

end IntervalExchange

end
