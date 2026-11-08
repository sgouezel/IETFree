/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.Pair.MeasureTools
public import IETFree.Pair.ReductionData

/-!
# The product of the two simplices and its free-coordinate chart

`simplexVolume d` is the pushforward of Lebesgue measure on the free region `simplexRegion d` under
`simplexMap d`, so the product of the two simplex measures is the pushforward under
`prodSimplexMap d e`.  The free-coordinate projection `toReal` inverts that chart on the open
region, which is what lets an almost-sure statement be transferred between the length vectors and
the free coordinates without ever asking for the measurability of the predicate.

The file sits below `ChallengeSolved.lean` and below the Section 3 machinery: both transport
statements in one direction or the other, so the chart cannot live in the challenge file itself.
The `Equiv`-valued word the challenge also speaks of (`evalWordEquiv`) is in `IETFree/IET.lean`,
beside `mkIETEquiv`; the bridges to `evalWord` are in `Pair/MeasureTools.lean`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open IntervalExchange.Pair

namespace IntervalExchange

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
end IntervalExchange
