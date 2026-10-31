/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.BlockLemma
import IETFree.BlockAssembly

/-!
The **solution of the weak challenge**: `ChallengeWeak.main`, proved from the library, with no
`sorry` and no axiom.

`ChallengeWeak.lean` is the comparator challenge (`comparator.json`): it imports only
`Mathlib`, and it declares its own copies of the definitions the statement needs, with the *same
names and bodies* as the library's, so that the comparison holds declaration by declaration.
Everything that cannot be shared has the same name on both sides, and is what this file has to
supply:

| in the challenge | here |
|---|---|
| `UniqueErgodicFun`, `IsRigidByTranslationsFun` | the same two definitions, in `ℝ → ℝ` form |
| `MasurVeechFun`, `VeechRigidityFun` | the same two (the inputs, for `mkIETFun λ π 0`) |
| `mkIETEquiv` (a definition hole, `:= sorry`) | the library's `mkIETEquiv` |
| `coe_mkIETEquiv` (a statement) | the library's `coe_mkIETEquiv` (`IETFree/IET.lean`) |
| `main` (a statement) | proved below |

The four `…Fun` predicates are new definitions, not copies of library API: the library's
`UniqueErgodic` and `IsRigidByTranslations` are stated for an exchange `f : IET 0 1` and iterate it
with the group power, while the challenge states them for a self-map of `ℝ` iterated with `f^[·]`.
The two forms are the same condition (`IET.pow_apply_iterate`), which is what `uniqueErgodic_iff`
and `isRigidByTranslations_iff` record; `masurVeech_of_fun` and `veechRigidity_of_fun` then turn the
challenge's hypotheses into the library's — almost every length vector is in the simplex
(`simplexVolume_compl_simplex`), and the exchange `mkIET1 λ π h` is the map `mkIETFun λ π 0`.

`main_of_library` is the same theorem with the library's hypotheses, and its proof is the a.e.
statement of Lemma 3.4: `exists_word_ae` (from `main_theorem_of_blocks` — the a.e. block data of
`BlockData.exists_ae_block_good` plus the assembly `exists_word_trivial_on_all_of_blocks`),
repackaged into the permutations `mkIETEquiv p_i π 0` by `evalWord_toEquiv_eq_one`, with
`simplexMap d (toReal p).1 = p.1` almost everywhere (`ae_toReal_simplexMap`).
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-! ## The `Equiv`-valued evaluation of a word

`evalWord` evaluates a word in two *exchanges* (`IET 0 1`), which is what the whole Section 3
development uses.  The statement of the challenge, on the other hand, speaks of the underlying
permutations of `ℝ` — `mkIETEquiv p π 0 : Equiv ℝ ℝ` — where no `IsIET` datum is available, so the
evaluation has to be defined there directly.  That is the only role of `evalWordEquiv`, and this is
the only file that uses it.  The definition is the challenge's, word for word. -/

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

/-! ## The challenge's predicates

These four definitions are also in `ChallengeWeak.lean`, word for word: comparator
compares them declaration by declaration.  They are here and not in the library because the
library's `UniqueErgodic` and `IsRigidByTranslations` are stated for `f : IET 0 1`. -/

/-- **Definition 2.1** (unique ergodicity): the Birkhoff averages of every continuous test function
converge to their integral, uniformly. -/
def UniqueErgodicFun (f : ℝ → ℝ) : Prop :=
  ∀ ψ : ℝ → ℝ, Continuous ψ → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
    ∀ n ≥ N, ∀ x ∈ Set.Ico (0 : ℝ) 1,
      |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ψ (f^[i] x) - ∫ y, ψ y ∂unitMeas| ≤ ε

/-- **Definition 2.2**: rigid by translations. -/
def IsRigidByTranslationsFun (f : ℝ → ℝ) : Prop :=
  ∃ q : ℕ → ℕ, ∃ t : ℕ → ℝ, ∃ B : ℕ → Set ℝ,
    Tendsto q atTop atTop ∧ Tendsto t atTop (nhds 0) ∧
      (∀ n, B n ⊆ Set.Ico (0 : ℝ) 1) ∧ (∀ n, MeasurableSet (B n)) ∧
        Tendsto (fun n => unitMeas.real (B n)) atTop (nhds 1) ∧
          ∀ (n : ℕ) (x : ℝ), x ∈ B n → f^[q n] x = x + t n

/-- **Masur–Veech**: for `d ≥ 2` and every irreducible permutation, almost every length vector
gives a uniquely ergodic exchange.  The hypothesis is stated for the *map* `mkIETFun lam π 0`, not
for an `Equiv` packaging of it: unique ergodicity is a property of the self-map of `ℝ`.  (The
restriction `2 ≤ d` is necessary: on one cell the exchange is the identity for every length
vector, and the identity is not uniquely ergodic.) -/
def MasurVeechFun : Prop :=
  ∀ (d : ℕ) (_ : 2 ≤ d) [NeZero d] (π : Equiv.Perm (Fin d)), IsIrreduciblePerm π →
    ∀ᵐ lam ∂(simplexVolume d), UniqueErgodicFun (mkIETFun lam π 0)

/-- **Veech rigidity**: for every irreducible permutation, almost every length vector gives an
exchange rigid by translations.  Like `MasurVeech`, it is stated for the map `mkIETFun lam π 0`. -/
def VeechRigidityFun : Prop :=
  ∀ (d : ℕ) [NeZero d] (π : Equiv.Perm (Fin d)), IsIrreduciblePerm π →
    ∀ᵐ lam ∂(simplexVolume d), IsRigidByTranslationsFun (mkIETFun lam π 0)

namespace ChallengeWeakSolved

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
  classical
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
  have hfixpoint : ∀ z ∈ (simplexRegion d ×ˢ simplexRegion e),
      prodSimplexMap d e (toReal (prodSimplexMap d e z)) = prodSimplexMap d e z := by
    rintro ⟨v, w⟩ ⟨hv, hw⟩
    change (simplexMap d (toReal (simplexMap d v, simplexMap e w)).1,
      simplexMap e (toReal (simplexMap d v, simplexMap e w)).2) = (simplexMap d v, simplexMap e w)
    rw [toReal_simplexMap hv.1 hw.1]
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
  classical
  -- `toReal` inverts `simplexMap` almost everywhere
  have hcongr : ((((volume : Measure (Fin (d - 1) → ℝ)).restrict (simplexRegion d)).prod
      (volume.restrict (simplexRegion e))).map (prodSimplexMap d e)).map (toReal (d := d) (e := e))
      = ((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))) := by
    rw [Measure.map_map continuous_toReal.measurable (measurable_prodSimplexMap d e),
      Measure.map_congr ?_, Measure.map_id]
    filter_upwards [ae_mem_simplexRegion_prod (d := d) (e := e)] with z hz
    obtain ⟨v, w⟩ := z
    change toReal (simplexMap d v, simplexMap e w) = (v, w)
    exact toReal_simplexMap hz.1.1 hz.2.1
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
    (σ : Equiv.Perm (Fin e)) (hMV : MasurVeech) (hVR : VeechRigidity) :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
      ∀ (D : IETDatum d) (E : IETDatum e), D.π = π → E.π = σ →
        D.v = (toReal p).1 → E.v = (toReal p).2 →
          ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧ evalWord w D.toIET E.toIET = 1 := by
  refine ae_prod_of_ae_free (P := fun p => ∀ (D : IETDatum d) (E : IETDatum e),
    D.π = π → E.π = σ → D.v = (toReal p).1 → E.v = (toReal p).2 →
      ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧ evalWord w D.toIET E.toIET = 1) ?_
  filter_upwards [main_theorem_of_blocks π σ hMV hVR,
    ae_mem_simplexRegion_prod (d := d) (e := e)] with z hz hzmem
  obtain ⟨a, b⟩ := z
  have htw : toReal (prodSimplexMap d e (a, b)) = (a, b) := by
    change toReal (simplexMap d a, simplexMap e b) = (a, b)
    exact toReal_simplexMap hzmem.1.1 hzmem.2.1
  rw [htw]
  intro D E hDπ hEπ hDv hEv
  obtain ⟨n, u, v, hcover, hfu, hgu, hw⟩ := hz D E hDπ hEπ hDv hEv
  exact exists_word_trivial_on_all_of_blocks D E u v hcover hfu hgu hw

/-! ## From the challenge's hypotheses to the library's -/

/-- The library's `UniqueErgodic` and the challenge's `UniqueErgodicFun` are the same condition on
the same map: the group power `f ^ n` is the iterate `f^[n]`. -/
theorem uniqueErgodic_iff (f : IET 0 1) : UniqueErgodic f ↔ UniqueErgodicFun ⇑f := by
  simp only [UniqueErgodic, UniqueErgodicFun, IET.pow_apply_iterate]

/-- Likewise for rigidity by translations. -/
theorem isRigidByTranslations_iff (f : IET 0 1) :
    IsRigidByTranslations f ↔ IsRigidByTranslationsFun ⇑f := by
  simp only [IsRigidByTranslations, IsRigidByTranslationsFun, IET.pow_apply_iterate]

/-- **Masur–Veech in the library's form**, from the challenge's: almost every length vector is in
the simplex, and the exchange `mkIET1 lam π h` is the map `mkIETFun lam π 0`. -/
theorem masurVeech_of_fun (h : MasurVeechFun) : MasurVeech := by
  intro d hd hd' π hirr
  filter_upwards [h d hd π hirr,
    MeasureTheory.ae_iff.mpr (simplexVolume_compl_simplex (d := d))] with lam hlam hmem
  intro h'
  rw [uniqueErgodic_iff]
  have hfun : (⇑(mkIET1 lam π h') : ℝ → ℝ) = mkIETFun lam π 0 := rfl
  rwa [hfun]

/-- **Veech's rigidity in the library's form**, from the challenge's. -/
theorem veechRigidity_of_fun (h : VeechRigidityFun) : VeechRigidity := by
  intro d hd π hirr
  filter_upwards [h d π hirr,
    MeasureTheory.ae_iff.mpr (simplexVolume_compl_simplex (d := d))] with lam hlam hmem
  intro h'
  rw [isRigidByTranslations_iff]
  have hfun : (⇑(mkIET1 lam π h') : ℝ → ℝ) = mkIETFun lam π 0 := rfl
  rwa [hfun]

/-! ## The theorem of the challenge file -/


/-- **The weak challenge, with the library's hypotheses.**  Granting Masur–Veech's theorem and
Veech's rigidity, for almost every pair of length vectors of total mass `1` the two exchanges
satisfy a nontrivial relation in the group of permutations of `ℝ`.

The root theorem `main` below is the same statement with the hypotheses of the challenge. -/
theorem main_of_library (hMV : MasurVeech) (hVR : VeechRigidity) {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
      ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧
        evalWordEquiv w (mkIETEquiv p.1 π 0) (mkIETEquiv p.2 σ 0) = 1 := by
  -- Lemma 3.4 in the library's language
  have hQ := exists_word_ae π σ hMV hVR
  -- the free coordinates of almost every length vector lie in the region
  have hregmeas : MeasurableSet {p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0) |
      toReal p ∈ simplexRegion d ×ˢ simplexRegion e} :=
    ((measurableSet_simplexRegion d).prod (measurableSet_simplexRegion e)).preimage
      continuous_toReal.measurable
  have hreg : ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
      toReal p ∈ simplexRegion d ×ˢ simplexRegion e := by
    rw [prod_simplexVolume_eq_map,
      MeasureTheory.ae_map_iff (measurable_prodSimplexMap d e).aemeasurable hregmeas]
    filter_upwards [ae_mem_simplexRegion_prod (d := d) (e := e)] with z hz
    obtain ⟨v, w⟩ := z
    change toReal (simplexMap d v, simplexMap e w) ∈ simplexRegion d ×ˢ simplexRegion e
    rw [toReal_simplexMap hz.1.1 hz.2.1]
    exact hz
  filter_upwards [hQ, hreg, ae_toReal_simplexMap (d := d) (e := e)] with p hp hpmem hfix
  -- the data with lengths `p`
  have h1 : (toReal p).1 ∈ simplexRegion d := hpmem.1
  have h2 : (toReal p).2 ∈ simplexRegion e := hpmem.2
  obtain ⟨w, hw1, hw2⟩ := hp ⟨π, (toReal p).1, h1⟩ ⟨σ, (toReal p).2, h2⟩ rfl rfl rfl rfl
  refine ⟨w, hw1, ?_⟩
  -- the same word, in the permutations of `ℝ`
  have hw3 : evalWordEquiv w (mkIETEquiv (simplexMap d (toReal p).1) π 0)
      (mkIETEquiv (simplexMap e (toReal p).2) σ 0) = 1 :=
    evalWord_toEquiv_eq_one hw2
  -- and the length vectors are those of `p`
  have hp1 : p.1 = simplexMap d (toReal p).1 := (congrArg Prod.fst hfix).symm
  have hp2 : p.2 = simplexMap e (toReal p).2 := (congrArg Prod.snd hfix).symm
  rwa [hp1, hp2]

#print axioms evalWord_toEquiv
#print axioms evalWord_toEquiv_eq_one
#print axioms ae_prod_of_ae_free
#print axioms exists_word_ae
#print axioms main_of_library
#print axioms uniqueErgodic_iff
#print axioms isRigidByTranslations_iff
#print axioms masurVeech_of_fun
#print axioms veechRigidity_of_fun

end ChallengeWeakSolved

/-! ## The two theorems of the challenge -/

/-- **The weak challenge, proved**: `ChallengeWeak.main`, in its words. -/
theorem main (hMV : MasurVeechFun) (hVR : VeechRigidityFun) {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
    ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧
      evalWordEquiv w (mkIETEquiv p.1 π 0) (mkIETEquiv p.2 σ 0) = 1 :=
  ChallengeWeakSolved.main_of_library (ChallengeWeakSolved.masurVeech_of_fun hMV)
    (ChallengeWeakSolved.veechRigidity_of_fun hVR) π σ

#print axioms coe_mkIETEquiv
#print axioms main
