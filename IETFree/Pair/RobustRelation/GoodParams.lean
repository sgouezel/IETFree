/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.Pair.ReductionData

/-!
# The parametrised bad set

`Pair/ReductionData.lean` fixes the paper's constant `4` in the enumeration `smallCoeffs` of the
coefficient vectors and in the bad set `IsBadParam`: a parameter pair is bad when a *nontrivial*
integer relation `k + ∑ aᵢλᵢ + ∑ bⱼμⱼ = 0` between the free coordinates vanishes there with all the
coefficients — the constant term included — bounded by `4`.

The robustness of a word of length `n` needs the same construction at a threshold growing with `n`:
a displacement of `w(f, g)` is a relation whose free-coordinate coefficients are bounded by `2n`
(`WordData.lean`, the `hD` field of `WordData`), while the candidate cuts of `w` are bounded by
`2n + 2` (`hsLat`), so a whole word is handled at `4 * |w| + 4`, the bound on the *difference* of
two candidates (`Robustness.lean`).  No constant appears in the statement of record: Theorem A is
stated at the paper's `Ω'`, the set of parameters good at *every* threshold
(`forall_goodParams_iff`), and the numeric bound survives only as the corollary
`evalWord_eventually_eq_one_of_goodParams`.  This file provides the parametrised versions and the
measure theory that goes with them.

## Contents

The definitions and the structural lemmas at an arbitrary threshold — `smallCoeffsAt`,
`mem_smallCoeffsAt`, `IsBadParamAt`, `goodParamsAt`, `isBadParamAt_iff_coeffs`,
`IsBadParamAt.mono`, `isClosed_badParamAt`, `isOpen_goodParamsAt`, `goodParamsAt_antitone`,
`coeffs_zero_of_good_with_const_at`, `isBadParamAt_mem_badSet` — are in
`Pair/ReductionData.lean`, beside the paper's `N = 4` case they generalise, which is stated
*through* them: `smallCoeffs := smallCoeffsAt 4`, `IsBadParam := IsBadParamAt 4`,
`goodParams := goodParamsAt 4`, and `isBadParam`/`isClosed_badParam`/`isOpen_goodParams`/
`isBadParam_mem_badSet` are the `N = 4` instances.  What is left here is what needs the threshold to
vary:

* **§1** `ae_goodParamsAt_all`, `ae_goodParamsAt_all_large`: the "countably many affine hyperplanes"
  of Remark 1.2 — almost every point is good at *some*, indeed at every *large*, threshold.  The
  proof goes through the Diophantine tube estimates of `Pair/Diophantine.lean` (`badSet`,
  `ae_eventually_notMem_badSet`), not through a separate hyperplane computation.
* **§2** `volume_eq_zero_intLinear_eq`, `volume_eq_zero_relReal`: the zero set of a nontrivial
  integer affine form is null, by slicing along a coordinate on which the form does not vanish.
* **§3** `compl_iUnion_goodParamsAt_subset`, `volume_iUnion_relReal_eq_zero`,
  `volume_compl_iUnion_goodParamsAt`, `measure_compl_iUnion_goodParamsAt`: the complement of the
  union of the good sets is contained in a countable union of null hyperplanes.
* **§4** `relation_of_good_at`, `relation_of_good_simplexMap_at`,
  `comb_simplexMap_eq_zero_of_good_at`: the threshold `2n` itself — a lattice combination of the
  lengths with coefficients bounded by `N` that vanishes at a point good at `2 * N` is constant with
  the two constants cancelling, hence vanishes identically on the simplex.

The parameter space is `PReal d e`, the **free** lengths of the two exchanges, and the threshold is
a natural number `N` against which the coefficients of the relations — the constant term included —
are compared.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace IntervalExchange.Pair

/-! ## 1. Almost every point is good at some threshold

The "countably many affine hyperplanes" of the source.  The argument is the one of
`ae_goodParams_real`, with the scale `4` replaced by the scale `N` at which the point is measured:
at a point of the two free regions, being inside the tube `badSet N` is incompatible with the
Diophantine-tube estimate applied to the relation itself, and almost every point is outside
`badSet N` for all large `N`. -/

/-- **Almost every point of the product of the two free regions is good at some threshold**: the
complement of `⋃ N, goodParamsAt N` is a countable union of affine hyperplanes, hence null. -/
theorem ae_goodParamsAt_all {d e : ℕ} [NeZero d] [NeZero e] :
    ∀ᵐ z ∂((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))),
      ∃ N, z ∈ goodParamsAt N d e := by
  filter_upwards [ae_eventually_notMem_badSet (simplexRegion d) (simplexRegion e),
    ae_mem_simplexRegion_prod (d := d) (e := e)] with z hz hmemz
  obtain ⟨N₀, hzN⟩ := Filter.eventually_atTop.mp hz
  refine ⟨N₀, ?_⟩
  intro hbad
  refine hzN N₀ le_rfl (isBadParamAt_mem_badSet ⟨simplexRegion_subset_ubox d hmemz.1,
    simplexRegion_subset_ubox e hmemz.2⟩ le_rfl ?_)
  rwa [toReal_simplexMap hmemz.1.1 hmemz.2.1]

/-! ## 2. The hyperplanes are null

The measure-zero statement behind "countably many affine hyperplanes": the zero set of a nontrivial
integer affine form on `Fin m → ℝ` is null.  The proof slices along a coordinate on which the form
does not vanish, where every slice is a singleton. -/

/-- **The zero set of a nontrivial integer affine form is null.** -/
theorem volume_eq_zero_intLinear_eq {m : ℕ} {f : Fin m → ℤ} (i : Fin m) (hi : f i ≠ 0)
    {k c : ℝ} : volume {x : Fin m → ℝ | k + ∑ j, (f j : ℝ) * x j = c} = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := i.isLt; omega⟩
  set S : Set (Fin (n + 1) → ℝ) := {x | k + ∑ j, (f j : ℝ) * x j = c} with hS
  have hcont : Continuous fun x : Fin (n + 1) → ℝ => k + ∑ j, (f j : ℝ) * x j := by
    have h1 : Continuous fun x : Fin (n + 1) → ℝ => ∑ j, (f j : ℝ) * x j :=
      continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
    exact continuous_const.add h1
  have hSmeas : MeasurableSet S := by
    rw [hS]
    exact (measurableSet_singleton c).preimage hcont.measurable
  set ee : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with hee
  have hpres : MeasurePreserving ee volume volume := volume_preserving_piFinSuccAbove _ i
  have key (t : ℝ) (s : Fin n → ℝ) : ((t, s) ∈ ee '' S) ↔ (ee.symm (t, s) ∈ S) := by
    rw [Set.mem_image]
    constructor
    · rintro ⟨x, hxS, hx⟩
      have h1 : ee.symm (t, s) = x := by
        rw [← hx]
        simp
      rwa [h1]
    · rintro h
      exact ⟨ee.symm (t, s), h, by simp⟩
  have himg : volume S = volume (ee '' S) := by
    have h := hpres.measure_preimage_equiv (ee '' S)
    rwa [Set.preimage_image_eq S ee.injective] at h
  have hfib : volume (ee '' S) = ∫⁻ s : Fin n → ℝ, volume {t : ℝ | (t, s) ∈ ee '' S} :=
    Measure.prod_apply_symm ((MeasurableEquiv.measurableSet_image ee).mpr hSmeas)
  have hfi : (f i : ℝ) ≠ 0 := by exact_mod_cast hi
  have hslice (s : Fin n → ℝ) : volume {t : ℝ | (t, s) ∈ ee '' S} = 0 := by
    have hset : {t : ℝ | (t, s) ∈ ee '' S}
        = {((c - (k + ∑ j : Fin n, (f (i.succAbove j) : ℝ) * s j)) / (f i : ℝ))} := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      rw [key t s, MeasurableEquiv.piFinSuccAbove_symm_apply, insertNthEquiv_apply_pair]
      rw [hS]
      simp only [Set.mem_ofPred_eq, sum_insertNth]
      constructor
      · intro h
        rw [eq_div_iff hfi]
        linarith
      · intro h
        rw [eq_div_iff hfi] at h
        linarith
    rw [hset, Real.volume_singleton]
  calc volume S = volume (ee '' S) := himg
    _ = ∫⁻ s : Fin n → ℝ, volume {t : ℝ | (t, s) ∈ ee '' S} := hfib
    _ = 0 := by simp only [hslice, lintegral_zero]

/-- **The zero set of a nontrivial relation is null**: `NontrivialCoeff t` gives
`volume {q | relReal t q = 0} = 0`, so the complement of `⋃ N, goodParamsAt N` is a countable
union of null hyperplanes.  The relation is affine in the two blocks of coordinates; a block on
which it is not constant gives a hyperplane slice (`volume_eq_zero_intLinear_eq`), and if it is
constant in both blocks then it is a nonzero constant. -/
theorem volume_eq_zero_relReal {d e : ℕ} {t : CoeffData d e} (hnt : NontrivialCoeff t) :
    volume {q : PReal d e | relReal t q = 0} = 0 := by
  set a : Fin (d - 1) → ℤ := fun i => t (Sum.inl (Sum.inl i)) with ha_def
  set b : Fin (e - 1) → ℤ := fun j => t (Sum.inl (Sum.inr j)) with hb_def
  set k : ℤ := constCoeff t with hk_def
  have hrel : ∀ q : PReal d e, relReal t q
      = (k : ℝ) + (∑ i, (a i : ℝ) * q.1 i) + ∑ j, (b j : ℝ) * q.2 j := by
    intro q
    simp only [relReal, constCoeff, ha_def, hb_def, hk_def]
  have hSmeas : MeasurableSet {q : PReal d e | relReal t q = 0} :=
    (measurableSet_singleton 0).preimage (continuous_relReal t).measurable
  by_cases ha : ∃ i, a i ≠ 0
  · obtain ⟨i, hi⟩ := ha
    rw [Measure.volume_eq_prod, Measure.prod_apply_symm hSmeas]
    have hslice (y : Fin (e - 1) → ℝ) :
        volume ((fun x : Fin (d - 1) → ℝ => (x, y)) ⁻¹'
          {q : PReal d e | relReal t q = 0}) = 0 := by
      have hset : ((fun x : Fin (d - 1) → ℝ => (x, y)) ⁻¹' {q : PReal d e | relReal t q = 0})
          = {x : Fin (d - 1) → ℝ | ((k : ℝ) + ∑ j, (b j : ℝ) * y j)
              + ∑ i, (a i : ℝ) * x i = 0} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, hrel]
        constructor <;> intro h <;> linarith
      rw [hset]
      exact volume_eq_zero_intLinear_eq i hi
    simp only [hslice, lintegral_zero]
  · push Not at ha
    by_cases hb : ∃ j, b j ≠ 0
    · obtain ⟨j, hj⟩ := hb
      rw [Measure.volume_eq_prod, Measure.prod_apply hSmeas]
      have hslice (x : Fin (d - 1) → ℝ) :
          volume (Prod.mk x ⁻¹' {q : PReal d e | relReal t q = 0}) = 0 := by
        have hset : (Prod.mk x ⁻¹' {q : PReal d e | relReal t q = 0})
            = {y : Fin (e - 1) → ℝ | (k : ℝ) + ∑ j, (b j : ℝ) * y j = 0} := by
          ext y
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, hrel, ha, Int.cast_zero, zero_mul,
            Finset.sum_const_zero, add_zero]
        rw [hset]
        exact volume_eq_zero_intLinear_eq j hj
      simp only [hslice, lintegral_zero]
    · push Not at hb
      have hk : k ≠ 0 := by
        rcases hnt with h | ⟨i, hi⟩ | ⟨j, hj⟩
        · exact h
        · exact absurd (ha i) hi
        · exact absurd (hb j) hj
      have hempty : {q : PReal d e | relReal t q = 0} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro q hq
        rw [Set.mem_ofPred_eq, hrel] at hq
        simp only [ha, hb, Int.cast_zero, zero_mul, Finset.sum_const_zero, add_zero] at hq
        exact hk (Int.cast_eq_zero.mp hq)
      rw [hempty, measure_empty]

/-! ## 3. The countable union of hyperplanes

The two set-theoretic facts behind "there is a full measure set `Ω'` such that, for `(λ, μ) ∈ Ω'`,
a linear combination vanishes only when all the integers are zero, as this amounts to excluding
countably many affine hyperplanes".

Note the direction: the union `⋃ N, goodParamsAt N` is *not* the set on which no nontrivial relation
vanishes — a point can be good at a small threshold and bad at a large one.  What is true, and all
that is used, is that the complement of the union is contained in the union of the hyperplanes. -/

/-- **The complement of the union of the good sets lies in the union of the hyperplanes**: a point
that is bad at every threshold is in particular bad at threshold `1`, so some nontrivial relation
vanishes there. -/
theorem compl_iUnion_goodParamsAt_subset {d e : ℕ} :
    (⋃ N, goodParamsAt N d e)ᶜ
      ⊆ ⋃ t : CoeffData d e, {q : PReal d e | NontrivialCoeff t ∧ relReal t q = 0} := by
  intro q hq
  rw [Set.mem_compl_iff, Set.mem_iUnion] at hq
  have h1 : IsBadParamAt 1 q := by
    by_contra h
    exact hq ⟨1, h⟩
  obtain ⟨t, -, hnt, hrel⟩ := h1
  exact Set.mem_iUnion.mpr ⟨t, hnt, hrel⟩

/-- **The union of the hyperplanes is null**: countably many hyperplanes with a nonzero normal
(`volume_eq_zero_relReal`). -/
theorem volume_iUnion_relReal_eq_zero {d e : ℕ} :
    volume (⋃ t : CoeffData d e, {q : PReal d e | NontrivialCoeff t ∧ relReal t q = 0}) = 0 := by
  refine measure_iUnion_null fun t => ?_
  by_cases ht : NontrivialCoeff t
  · have hset : {q : PReal d e | NontrivialCoeff t ∧ relReal t q = 0}
        = {q : PReal d e | relReal t q = 0} := by
      ext q
      simp only [Set.mem_ofPred_eq, ht, true_and]
    rw [hset]
    exact volume_eq_zero_relReal ht
  · have hset : {q : PReal d e | NontrivialCoeff t ∧ relReal t q = 0} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro q ⟨h1, -⟩
      exact ht h1
    rw [hset, measure_empty]

/-- **The union of the good sets is conull**: its complement is a countable union of null
hyperplanes. -/
theorem volume_compl_iUnion_goodParamsAt {d e : ℕ} :
    volume ((⋃ N, goodParamsAt N d e)ᶜ : Set (PReal d e)) = 0 :=
  measure_mono_null compl_iUnion_goodParamsAt_subset volume_iUnion_relReal_eq_zero

/-- **The complement is null for the measure of the two free regions**: the complement of the union
of the good sets is null for the measure `(volume|_{Δ}) × (volume|_{Δ})` of the two simplices. -/
theorem measure_compl_iUnion_goodParamsAt {d e : ℕ} :
    ((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e)))
      ((⋃ N, goodParamsAt N d e)ᶜ : Set (PReal d e)) = 0 := by
  rw [Measure.prod_restrict]
  refine le_antisymm ?_ (bot_le)
  calc (volume.prod volume).restrict (simplexRegion d ×ˢ simplexRegion e)
        ((⋃ N, goodParamsAt N d e)ᶜ : Set (PReal d e))
      ≤ volume ((⋃ N, goodParamsAt N d e)ᶜ : Set (PReal d e)) := Measure.restrict_apply_le _ _
    _ = 0 := volume_compl_iUnion_goodParamsAt

/-! ## 4. The threshold `2 n`

The threshold of the robustness theorem is `2 n` for a word of length `n`.  The reason is here: a
displacement of `w(f, g)` on one of its pieces is a sum of `n` letter translation vectors, each of
which is a lattice combination `∑ aᵢ λᵢ + ∑ bⱼ μⱼ` of the *full* lengths with `|aᵢ|, |bⱼ| ≤ 1`;
hence the displacement is such a combination with `|aᵢ|, |bⱼ| ≤ n`.  The passage to the free
coordinates multiplies the bound by `2`, and a point of `goodParamsAt (2 * n)` kills it.

`relation_of_good_at` is `relation_of_good` with the paper's `2`/`4` replaced by `n`/`2 * n`: a
vanishing combination with coefficients bounded by `n` at a point good at `2 * n` must be constant,
with the two constants cancelling — in particular it vanishes identically on the simplex
(`comb_simplexMap_eq_zero_of_good_at`). -/

/-- **The `2 n` threshold, in the length vectors**: a lattice combination of the lengths whose
coefficients are bounded by `N` and which vanishes at a pair which is good at threshold `2 * N` is
constant on each block, and the two constants cancel. -/
theorem relation_of_good_at {d e : ℕ} [NeZero d] [NeZero e] {p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0)}
    {N : ℕ} (hp : ¬ IsBadParamAt (2 * N) (toReal p)) {a : Fin d → ℤ} {b : Fin e → ℤ}
    (ha : ∀ i, |a i| ≤ (N : ℤ)) (hb : ∀ j, |b j| ≤ (N : ℤ))
    (hl : p.1 ∈ simplex (Fin d)) (hm : p.2 ∈ simplex (Fin e))
    (h : (∑ i, (a i : ℝ) * (p.1 i : ℝ)) + (∑ j, (b j : ℝ) * (p.2 j : ℝ)) = 0) :
    (∀ i, a i = a (lastPos d)) ∧ (∀ j, b j = b (lastPos e)) ∧
      a (lastPos d) + b (lastPos e) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by have := NeZero.pos d; omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, e = l + 1 := ⟨e - 1, by have := NeZero.pos e; omega⟩
  rw [lastPos_eq_last, lastPos_eq_last]
  have h1 := sum_eq_last_add_free p.1 hl (fun i => (a i : ℝ))
  have h2 := sum_eq_last_add_free p.2 hm (fun j => (b j : ℝ))
  -- the relation, in the free coordinates
  have e1 : (∑ i : Fin m, (((a i.castSucc - a (Fin.last m)) : ℤ) : ℝ) * (p.1 i.castSucc : ℝ))
      = (∑ i, (a i : ℝ) * (p.1 i : ℝ)) - (a (Fin.last m) : ℝ) := by
    rw [h1]
    push_cast
    ring
  have e2 : (∑ j : Fin l, (((b j.castSucc - b (Fin.last l)) : ℤ) : ℝ) * (p.2 j.castSucc : ℝ))
      = (∑ j, (b j : ℝ) * (p.2 j : ℝ)) - (b (Fin.last l) : ℝ) := by
    rw [h2]
    push_cast
    ring
  have hrel : ((a (Fin.last m) + b (Fin.last l) : ℤ) : ℝ)
      + (∑ i : Fin m, (((a i.castSucc - a (Fin.last m)) : ℤ) : ℝ) * (p.1 i.castSucc : ℝ))
      + (∑ j : Fin l, (((b j.castSucc - b (Fin.last l)) : ℤ) : ℝ) * (p.2 j.castSucc : ℝ)) = 0 := by
    rw [e1, e2]
    push_cast
    linarith
  -- the free coefficients are bounded by `2 * N`
  have hda (i : Fin m) : |(a i.castSucc - a (Fin.last m) : ℤ)| ≤ ((2 * N : ℕ) : ℤ) := by
    have h1 := abs_le.mp (ha i.castSucc)
    have h2 := abs_le.mp (ha (Fin.last m))
    rw [abs_le]
    constructor <;> omega
  have hdb (j : Fin l) : |(b j.castSucc - b (Fin.last l) : ℤ)| ≤ ((2 * N : ℕ) : ℤ) := by
    have h1 := abs_le.mp (hb j.castSucc)
    have h2 := abs_le.mp (hb (Fin.last l))
    rw [abs_le]
    constructor <;> omega
  have hk : |a (Fin.last m) + b (Fin.last l)| ≤ ((2 * N : ℕ) : ℤ) := by
    have h1 := abs_le.mp (ha (Fin.last m))
    have h2 := abs_le.mp (hb (Fin.last l))
    rw [abs_le]
    constructor <;> omega
  obtain ⟨hk0, ha0, hb0⟩ := coeffs_zero_of_good_with_const_at (N := 2 * N) hp
    (k := a (Fin.last m) + b (Fin.last l))
    (a := fun i => a i.castSucc - a (Fin.last m))
    (b := fun j => b j.castSucc - b (Fin.last l)) hda hdb hk hrel
  refine ⟨?_, ?_, hk0⟩
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have := congrFun ha0 j
      simp only [Pi.zero_apply] at this
      omega
    · rfl
  · intro j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · have := congrFun hb0 k
      simp only [Pi.zero_apply] at this
      omega
    · rfl

/-- **The `2 n` threshold, in the free coordinates**: `relation_of_good_at` for the length vectors
`simplexMap d q.1`, `simplexMap e q.2` of a point of the two free regions. -/
theorem relation_of_good_simplexMap_at {d e : ℕ} [NeZero d] [NeZero e] {q : PReal d e} {N : ℕ}
    (hreg : q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e)
    (hgood : ¬ IsBadParamAt (2 * N) q) {a : Fin d → ℤ} {b : Fin e → ℤ}
    (ha : ∀ i, |a i| ≤ (N : ℤ)) (hb : ∀ j, |b j| ≤ (N : ℤ))
    (h : (∑ i, (a i : ℝ) * (simplexMap d q.1 i : ℝ))
        + (∑ j, (b j : ℝ) * (simplexMap e q.2 j : ℝ)) = 0) :
    (∀ i, a i = a (lastPos d)) ∧ (∀ j, b j = b (lastPos e)) ∧
      a (lastPos d) + b (lastPos e) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by have := NeZero.pos d; omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, e = l + 1 := ⟨e - 1, by have := NeZero.pos e; omega⟩
  refine relation_of_good_at (p := (simplexMap (m + 1) q.1, simplexMap (l + 1) q.2)) ?_ ha hb
    (simplexMap_mem_simplex (p := m) hreg.1.1 hreg.1.2)
    (simplexMap_mem_simplex (p := l) hreg.2.1 hreg.2.2) h
  rwa [toReal_simplexMap hreg.1.1 hreg.2.1]

/-- **A vanishing combination at a good point vanishes identically**: the form of
`relation_of_good_simplexMap_at` used for the displacements of a word, which are lattice
combinations of the lengths with no constant term and coefficients bounded by the length of the
word. -/
theorem comb_simplexMap_eq_zero_of_good_at {d e : ℕ} [NeZero d] [NeZero e] {q₀ : PReal d e}
    {N : ℕ} (hreg : q₀.1 ∈ simplexRegion d ∧ q₀.2 ∈ simplexRegion e)
    (hgood : ¬ IsBadParamAt (2 * N) q₀) {a : Fin d → ℤ} {b : Fin e → ℤ}
    (ha : ∀ i, |a i| ≤ (N : ℤ)) (hb : ∀ j, |b j| ≤ (N : ℤ))
    (h : (∑ i, (a i : ℝ) * (simplexMap d q₀.1 i : ℝ))
        + (∑ j, (b j : ℝ) * (simplexMap e q₀.2 j : ℝ)) = 0) :
    ∀ q : PReal d e, q.1 ∈ simplexRegion d → q.2 ∈ simplexRegion e →
      (∑ i, (a i : ℝ) * (simplexMap d q.1 i : ℝ))
        + (∑ j, (b j : ℝ) * (simplexMap e q.2 j : ℝ)) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by have := NeZero.pos d; omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, e = l + 1 := ⟨e - 1, by have := NeZero.pos e; omega⟩
  obtain ⟨hac, hbc, hsum⟩ := relation_of_good_simplexMap_at hreg hgood ha hb h
  intro q hq1 hq2
  have hlam : (∑ i, (simplexMap (m + 1) q.1 i : ℝ)) = 1 :=
    sum_coe_eq_one (simplexMap_mem_simplex (p := m) hq1.1 hq1.2)
  have hmu : (∑ j, (simplexMap (l + 1) q.2 j : ℝ)) = 1 :=
    sum_coe_eq_one (simplexMap_mem_simplex (p := l) hq2.1 hq2.2)
  have e1 : (∑ i, (a i : ℝ) * (simplexMap (m + 1) q.1 i : ℝ))
      = (a (lastPos (m + 1)) : ℝ) := by
    calc (∑ i : Fin (m + 1), (a i : ℝ) * (simplexMap (m + 1) q.1 i : ℝ))
        = ∑ i, (a (lastPos (m + 1)) : ℝ) * (simplexMap (m + 1) q.1 i : ℝ) :=
          Finset.sum_congr rfl fun i _ => by rw [hac i]
      _ = (a (lastPos (m + 1)) : ℝ) * (∑ i, (simplexMap (m + 1) q.1 i : ℝ)) := by
          rw [Finset.mul_sum]
      _ = (a (lastPos (m + 1)) : ℝ) := by rw [hlam, mul_one]
  have e2 : (∑ j, (b j : ℝ) * (simplexMap (l + 1) q.2 j : ℝ))
      = (b (lastPos (l + 1)) : ℝ) := by
    calc (∑ j : Fin (l + 1), (b j : ℝ) * (simplexMap (l + 1) q.2 j : ℝ))
        = ∑ j, (b (lastPos (l + 1)) : ℝ) * (simplexMap (l + 1) q.2 j : ℝ) :=
          Finset.sum_congr rfl fun j _ => by rw [hbc j]
      _ = (b (lastPos (l + 1)) : ℝ) * (∑ j, (simplexMap (l + 1) q.2 j : ℝ)) := by
          rw [Finset.mul_sum]
      _ = (b (lastPos (l + 1)) : ℝ) := by rw [hmu, mul_one]
  rw [e1, e2]
  exact_mod_cast hsum

/-- **Almost every point is good at every large threshold**: the form needed when the threshold is
imposed by the word rather than by the point, since the witness of the relation at a point is fixed
(`w`) while the threshold provided by `ae_goodParamsAt_all` is not. -/
theorem ae_goodParamsAt_all_large {d e : ℕ} [NeZero d] [NeZero e] :
    ∀ᵐ z ∂((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))),
      ∀ᶠ N in atTop, z ∈ goodParamsAt N d e := by
  filter_upwards [ae_eventually_notMem_badSet (simplexRegion d) (simplexRegion e),
    ae_mem_simplexRegion_prod (d := d) (e := e)] with z hz hmemz
  refine hz.mono ?_
  intro N hN hbad
  exact hN (isBadParamAt_mem_badSet ⟨simplexRegion_subset_ubox d hmemz.1,
    simplexRegion_subset_ubox e hmemz.2⟩ le_rfl (by rwa [toReal_simplexMap hmemz.1.1 hmemz.2.1]))

end IntervalExchange.Pair
