/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.Pair.BlockLemma
public import IETFree.UniqueErgodicity.IET

/-!
The **solution of the challenge**: `Challenge.main`, the unconditional form of Theorem 1.1, proved
with no `sorry` and no axiom.

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
`BlockData.exists_ae_block_good` plus the assembly `exists_word_trivial_on_all_of_blocks`),
repackaged into the permutations `mkIETEquiv p_i π 0` by `evalWord_toEquiv_eq_one`, with
`simplexMap d (toReal p).1 = p.1` almost everywhere (`ae_toReal_simplexMap`).

The root theorem `main` is `Challenge.main` in its words, and carries the proof above; it is the
only place in the library that mentions the challenge's vocabulary (`evalWordEquiv`), and it
carries the single `#print axioms` of the tree.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-! ## The `Equiv`-valued evaluation of a word

`evalWord` evaluates a word in two *exchanges* (`IET 0 1`), which is what the whole Section 3
development uses.  The statement of the challenge, on the other hand, speaks of the underlying
permutations of `ℝ` — `mkIETEquiv p π 0 : Equiv ℝ ℝ` — where no `IsIET` datum is available, so the
evaluation has to be defined there directly.  That is the only role of `evalWordEquiv`. -/

/-- **The evaluation of a word in two equivs**: the `Equiv`-valued analogue of `evalWord`, for a
pair of permutations of `ℝ`. -/
noncomputable def evalWordEquiv (w : FreeGroup (Fin 2)) (f g : Equiv ℝ ℝ) : Equiv ℝ ℝ :=
  FreeGroup.lift (fun i : Fin 2 => if i = 0 then f else g) w

/-- `evalWord` of `IET`s is `evalWordEquiv` of the underlying equivs: the two evaluations agree. -/
theorem evalWord_toEquiv (F G : IET 0 1) (w : FreeGroup (Fin 2)) :
    (evalWord w F G).toEquiv = evalWordEquiv w F.toEquiv G.toEquiv := by
  induction w using FreeGroup.induction_on with
  | C1 => rfl
  | of x => by_cases hx : x = 0 <;> simp [hx, evalWordEquiv, evalWord]
  | inv_of x ih =>
      have h1 : ((evalWord (FreeGroup.of x) F G)⁻¹).toEquiv
          = ((evalWord (FreeGroup.of x) F G).toEquiv)⁻¹ := rfl
      simp only [evalWord_inv, map_inv, evalWordEquiv, h1, ih]
  | mul x y ihx ihy =>
      have h1 : (evalWord x F G * evalWord y F G).toEquiv
          = (evalWord x F G).toEquiv * (evalWord y F G).toEquiv := rfl
      simp only [evalWord_mul, map_mul, evalWordEquiv, h1, ihx, ihy]

namespace ChallengeSolved

/-! ## A word trivial for an exchange is trivial for the permutation -/

/-- A word which is trivial for the library's exchanges is trivial for their permutations of `ℝ`. -/
theorem evalWord_toEquiv_eq_one {w : FreeGroup (Fin 2)} {F G : IET 0 1}
    (h : evalWord w F G = 1) : evalWordEquiv w F.toEquiv G.toEquiv = 1 := by
  have hone : (1 : IET 0 1).toEquiv = (1 : Equiv ℝ ℝ) := rfl
  have h1 : (evalWord w F G).toEquiv = (1 : Equiv ℝ ℝ) := by rw [h, hone]
  rwa [evalWord_toEquiv] at h1

/-! ## From the free coordinates to the length vectors

`simplexVolume d` is the pushforward of Lebesgue measure on the free region `simplexRegion d` under
`simplexMap d`, so `(simplexVolume d).prod (simplexVolume e)` is the pushforward under
`prodSimplexMap d e`.

Pushing an almost-sure statement *forward* along a map normally needs measurability of the
predicate, which the conclusion of Lemma 3.4 (an existential over words, with equality of functions)
does not have.  The `toReal` projection avoids it: a statement for almost every length vector `p` is
a statement for almost every `toReal p`, which is a *pullback*, and `toReal` inverts `simplexMap` on
the region. -/

/-- The product of the two parametrisations of the simplices.  (`Prod.map` is
`implicit_reducible` in the core library, so it is not unfolded by `rw`; a plain lambda is easier to
work with.) -/
noncomputable def prodSimplexMap (d e : ℕ) :
    PReal d e → (Fin d → ℝ≥0) × (Fin e → ℝ≥0) :=
  fun z => (simplexMap d z.1, simplexMap e z.2)

/-- **`toReal` inverts the parametrisation of the product of the two simplices**, at a point of
the product of the two regions: the counterpart of `toReal_simplexMap` for `prodSimplexMap`. -/
theorem toReal_prodSimplexMap {d e : ℕ} [NeZero d] [NeZero e] {z : PReal d e}
    (h1 : z.1 ∈ simplexRegion d) (h2 : z.2 ∈ simplexRegion e) :
    toReal (prodSimplexMap d e z) = z := by
  obtain ⟨v, w⟩ := z
  exact toReal_simplexMap h1.1 h2.1

theorem measurable_prodSimplexMap (d e : ℕ) : Measurable (prodSimplexMap d e) := by
  unfold prodSimplexMap
  exact ((measurable_simplexMap d).comp measurable_fst).prodMk
    ((measurable_simplexMap e).comp measurable_snd)

/-- The product of the two simplex measures is the pushforward of Lebesgue measure on the product of
the two free regions under `simplexMap d × simplexMap e`. -/
theorem prod_simplexVolume_eq_map (d e : ℕ) :
    (simplexVolume d).prod (simplexVolume e)
      = (((volume : Measure (Fin (d - 1) → ℝ)).restrict (simplexRegion d)).prod
          (volume.restrict (simplexRegion e))).map (prodSimplexMap d e) := by
  have h := MeasureTheory.Measure.map_prod_map
    ((volume : Measure (Fin (d - 1) → ℝ)).restrict (simplexRegion d))
    (volume.restrict (simplexRegion e)) (measurable_simplexMap d) (measurable_simplexMap e)
  rw [simplexVolume, simplexVolume, h]
  congr 1

/-- **On the support of the simplex measure, the free coordinates invert `simplexMap`.** -/
theorem ae_toReal_simplexMap {d e : ℕ} [NeZero d] [NeZero e] :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)), prodSimplexMap d e (toReal p) = p := by
  have hregion : ((volume.restrict (simplexRegion d)).prod
      (volume.restrict (simplexRegion e)))
      ((simplexRegion d ×ˢ simplexRegion e)ᶜ) = 0 := by
    rw [Measure.prod_restrict,
      Measure.restrict_apply
        ((measurableSet_simplexRegion d).prod (measurableSet_simplexRegion e)).compl,
      Set.compl_inter_self, measure_empty]
  have hS : MeasurableSet {p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0) |
      prodSimplexMap d e (toReal p) = p} :=
    measurableSet_eq_fun ((measurable_prodSimplexMap d e).comp continuous_toReal.measurable)
      measurable_id
  -- in the region, `toReal` inverts `simplexMap`
  have hfixpoint (z) (hz : z ∈ (simplexRegion d ×ˢ simplexRegion e)) :
      prodSimplexMap d e (toReal (prodSimplexMap d e z)) = prodSimplexMap d e z := by
    obtain ⟨v, w⟩ := z
    obtain ⟨hv, hw⟩ := hz
    rw [toReal_prodSimplexMap hv hw]
  rw [prod_simplexVolume_eq_map, ae_iff, ← Set.compl_ofPred,
    Measure.map_apply (measurable_prodSimplexMap d e) hS.compl]
  refine measure_mono_null (fun z hz => ?_) hregion
  simp only [Set.mem_preimage, Set.mem_compl_iff] at hz ⊢
  by_contra hmem
  exact hz (hfixpoint z hmem)

/-- **The transfer of an almost-sure statement from the free coordinates to the length vectors.** -/
theorem ae_prod_of_ae_free {d e : ℕ} [NeZero d] [NeZero e]
    {P : (Fin d → ℝ≥0) × (Fin e → ℝ≥0) → Prop}
    (h : ∀ᵐ z ∂((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))),
      P (prodSimplexMap d e z)) :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)), P p := by
  -- `toReal` inverts `simplexMap` almost everywhere
  have hcongr : ((((volume : Measure (Fin (d - 1) → ℝ)).restrict (simplexRegion d)).prod
      (volume.restrict (simplexRegion e))).map (prodSimplexMap d e)).map (toReal (d := d) (e := e))
      = ((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))) := by
    rw [Measure.map_map continuous_toReal.measurable (measurable_prodSimplexMap d e),
      Measure.map_congr ?_, Measure.map_id]
    filter_upwards [ae_mem_simplexRegion_prod (d := d) (e := e)] with z hz
    exact toReal_prodSimplexMap hz.1 hz.2
  -- the statement for almost every length vector, read through `toReal`
  have hA : ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
      P (prodSimplexMap d e (toReal p)) := by
    rw [prod_simplexVolume_eq_map]
    refine ae_of_ae_map (f := toReal (d := d) (e := e))
      (p := fun q => P (prodSimplexMap d e q)) continuous_toReal.aemeasurable ?_
    rw [hcongr]
    exact h
  filter_upwards [hA, ae_toReal_simplexMap (d := d) (e := e)] with p hp hfix
  rw [hfix] at hp
  exact hp

/-! ## The mathematical content of the theorem, in the library's language -/

/-- **Lemma 3.4 for almost every length vector**: every pair of data with those lengths carries a
nontrivial word which is the identity on `[0, 1)`.  This is the content of the weak challenge, with
the exchanges of the library. -/
theorem exists_word_ae {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
      ∀ (D : IETDatum d) (E : IETDatum e), D.π = π → E.π = σ →
        D.v = (toReal p).1 → E.v = (toReal p).2 →
          ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧ evalWord w D.toIET E.toIET = 1 := by
  refine ae_prod_of_ae_free (P := fun p => ∀ (D : IETDatum d) (E : IETDatum e),
    D.π = π → E.π = σ → D.v = (toReal p).1 → E.v = (toReal p).2 →
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


end ChallengeSolved

/-! ## The theorem of the challenge file -/

/-- **Theorem 1.1 of the paper**: for almost every pair of length vectors of total mass `1`, the two
exchanges satisfy a nontrivial relation in the group of permutations of `ℝ`.  This is
`Challenge.main`, in its words, with nothing left as a hypothesis: Masur–Veech's theorem and
Veech's rigidity are applied inside the proof. -/
theorem main {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
      ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧
        evalWordEquiv w (mkIETEquiv p.1 π 0) (mkIETEquiv p.2 σ 0) = 1 := by
  -- Lemma 3.4 in the library's language
  have hQ := ChallengeSolved.exists_word_ae π σ
  -- the free coordinates of almost every length vector lie in the region
  have hregmeas : MeasurableSet {p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0) |
      toReal p ∈ simplexRegion d ×ˢ simplexRegion e} :=
    ((measurableSet_simplexRegion d).prod (measurableSet_simplexRegion e)).preimage
      continuous_toReal.measurable
  have hreg : ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
      toReal p ∈ simplexRegion d ×ˢ simplexRegion e := by
    rw [ChallengeSolved.prod_simplexVolume_eq_map,
      MeasureTheory.ae_map_iff (ChallengeSolved.measurable_prodSimplexMap d e).aemeasurable
        hregmeas]
    filter_upwards [ae_mem_simplexRegion_prod (d := d) (e := e)] with z hz
    obtain ⟨v, w⟩ := z
    rw [ChallengeSolved.toReal_prodSimplexMap hz.1 hz.2]
    exact hz
  filter_upwards [hQ, hreg, ChallengeSolved.ae_toReal_simplexMap (d := d) (e := e)]
    with p hp hpmem hfix
  -- the data with lengths `p`
  obtain ⟨w, hw1, hw2⟩ := hp ⟨π, (toReal p).1, hpmem.1⟩ ⟨σ, (toReal p).2, hpmem.2⟩ rfl rfl rfl rfl
  refine ⟨w, hw1, ?_⟩
  -- the same word, in the permutations of `ℝ`
  have hw3 : evalWordEquiv w (mkIETEquiv (simplexMap d (toReal p).1) π 0)
      (mkIETEquiv (simplexMap e (toReal p).2) σ 0) = 1 :=
    ChallengeSolved.evalWord_toEquiv_eq_one hw2
  -- and the length vectors are those of `p`
  have hp1 : p.1 = simplexMap d (toReal p).1 := (congrArg Prod.fst hfix).symm
  have hp2 : p.2 = simplexMap e (toReal p).2 := (congrArg Prod.snd hfix).symm
  rwa [hp1, hp2]

-- The axiom check of the library: the single `#print axioms` of the tree, for the main theorem.
#print axioms main

end
