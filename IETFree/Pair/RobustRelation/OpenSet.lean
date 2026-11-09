/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.Pair.ProductSimplex
public import IETFree.Pair.RobustRelation.FreeParams
public import IETFree.Pair.RobustRelation.GoodParams
public import IETFree.Pair.RobustRelation.Robustness

/-!
# An open set of parameters of full measure carrying a relation

`goodParamsAt N d e` is the set of parameter pairs at which no nontrivial integer relation between
the free lengths vanishes with all its coefficients — the constant term included — bounded by `N`,
and
`HasRelation π σ q` says that some nontrivial word in the two exchanges `fOf π q` and `gOf σ q` is
trivial.

Almost every pair is good at *every* threshold: the good sets decrease with the threshold
(`goodParamsAt_antitone`), so being good at all sufficiently large thresholds — which holds almost
everywhere — is being good at every fixed threshold (`ae_goodParamsAt_all_thresholds`).  The other
almost-sure input, that almost every pair carries a nontrivial relation, is the content of the main
theorem and is not available here: this file sits below `ChallengeSolved.lean`, so the assembly
takes it as a hypothesis — `exists_isOpen_subset_hasRelation_of_robust` takes both inputs, and
`exists_isOpen_subset_hasRelation_of_ae` takes only the relation, discharging robustness from
`Robustness.lean`.  The unconditional statement is in `ChallengeSolved.lean`, fed with `main`.

The third ingredient is the robustness of a relation at a good parameter: a word which is trivial
at a parameter good at every threshold is trivial on a whole neighbourhood of that pair
(`evalWord_eventually_eq_one`).  With it almost every pair is *interior* to the set of parameters
carrying a relation: robustness says that the set on which the witnessed word is trivial is a
neighbourhood of the point, and that set is contained in the relation set, the same word witnessing
the relation.  So the relation set has an open subset of full measure, in the free coordinates.

The last section states the same in the paper's coordinates: on the product `Δ_π × Δ_σ` of the two
simplices of length vectors, which has empty interior in the ambient space
`(Fin d → ℝ≥0) × (Fin e → ℝ≥0)`, so that the open set can only be an open set of the ambient space
whose *trace* on the product carries the relation.

What is proved is thus not that the relation set itself is open — it need not be — but that its
interior is conull.  No measurability of the relation set is used anywhere: an almost-sure statement
is a statement that a complement has measure zero, so `∀ᵐ q ∂μ, q ∈ interior Z` *is* the assertion
`μ ((interior Z)ᶜ) = 0`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace IntervalExchange.Pair

/-! ## The assembly in the free coordinates -/

/-- **A point which is good at all large thresholds is good at every threshold**: by
`goodParamsAt_antitone` the good sets decrease as the threshold grows, so a point of
`goodParamsAt M` is a point of `goodParamsAt N` for every `N ≤ M`. -/
theorem goodParamsAt_forall_of_eventually {d e : ℕ} {q : PReal d e}
    (h : ∀ᶠ N in atTop, q ∈ goodParamsAt N d e) : ∀ N, q ∈ goodParamsAt N d e := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  intro N
  exact goodParamsAt_antitone (le_max_left N N₀) (hN₀ (max N N₀) (le_max_right N N₀))

/-- **Almost every parameter pair is good at every threshold.**

The a.e. statement at all sufficiently large thresholds is `ae_goodParamsAt_all_large`; the passage
from "for all large `N`" to "for every `N`" is the antitonicity of the good sets, so no further
measure theory is needed. -/
theorem ae_goodParamsAt_all_thresholds {d e : ℕ} [NeZero d] [NeZero e] :
    ∀ᵐ q ∂((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))),
      ∀ N, q ∈ goodParamsAt N d e := by
  filter_upwards [ae_goodParamsAt_all_large (d := d) (e := e)] with q hq
  exact goodParamsAt_forall_of_eventually hq

/-- **A fixed nontrivial word which is trivial certifies a relation**: the set of parameters at
which a given nontrivial word evaluates to the identity is contained in the relation set, with that
word as the witness.  This is how a neighbourhood of triviality of one word becomes a neighbourhood
of the relation set. -/
theorem evalWord_eq_one_subset_hasRelation {d e : ℕ} [NeZero d] [NeZero e]
    {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)} {w : FreeGroup Gen} (hw : w ≠ 1) :
    {q : PReal d e | evalWord w (fOf π q) (gOf σ q) = 1} ⊆ {q | HasRelation π σ q} :=
  fun _ hq => ⟨w, hw, hq⟩

/-- **A good parameter carrying a relation is interior to the relation set.**

Let `w ≠ 1` be trivial at `q`.  Robustness at the good parameter `q` gives a neighbourhood of `q`
on which the *same* word `w` is trivial, and that neighbourhood is contained in the relation set
since `w` witnesses the relation at each of its points.  So the relation set is a neighbourhood
of `q`. -/
theorem mem_interior_hasRelation {d e : ℕ} [NeZero d] [NeZero e] {π : Equiv.Perm (Fin d)}
    {σ : Equiv.Perm (Fin e)} {q : PReal d e}
    (hreg : q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e)
    (hgood : ∀ N, q ∈ goodParamsAt N d e) (hrel : HasRelation π σ q)
    (hA : ∀ (w : FreeGroup Gen) {q₀ : PReal d e}, q₀.1 ∈ simplexRegion d →
      q₀.2 ∈ simplexRegion e → (∀ N, q₀ ∈ goodParamsAt N d e) →
      evalWord w (fOf π q₀) (gOf σ q₀) = 1 →
      ∀ᶠ q' in 𝓝 q₀, evalWord w (fOf π q') (gOf σ q') = 1) :
    q ∈ interior {q | HasRelation π σ q} := by
  obtain ⟨w, hw, hwq⟩ := hrel
  have hnbh : {q' : PReal d e | evalWord w (fOf π q') (gOf σ q') = 1} ∈ 𝓝 q :=
    hA w hreg.1 hreg.2 hgood hwq
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset hnbh (evalWord_eq_one_subset_hasRelation hw))

/-- **The relation set has an open subset of full measure.**

Almost every pair is in the two open regions (`ae_mem_simplexRegion_prod`), carries a relation —
the theorem's hypothesis `hrel` — and is good at every threshold (`ae_goodParamsAt_all_thresholds`);
at each such pair the relation set is a neighbourhood (`mem_interior_hasRelation`).  So almost every
pair lies in the interior `U` of the relation set, which is therefore conull as well as open and
contained in it.

`U` is taken to be the interior rather than the relation set itself: the relation set need not be
open, and `∀ᵐ q ∂μ, q ∈ U` is by definition `μ Uᶜ = 0`, with no measurability of the relation set
required.  Points outside the two regions cost nothing, the measure being the product of the two
restrictions to the regions. -/
theorem exists_isOpen_subset_hasRelation_of_robust {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e))
    (hrel : ∀ᵐ q ∂((volume.restrict (simplexRegion d)).prod
      (volume.restrict (simplexRegion e))), HasRelation π σ q)
    (hA : ∀ (w : FreeGroup Gen) {q₀ : PReal d e}, q₀.1 ∈ simplexRegion d →
      q₀.2 ∈ simplexRegion e → (∀ N, q₀ ∈ goodParamsAt N d e) →
      evalWord w (fOf π q₀) (gOf σ q₀) = 1 →
      ∀ᶠ q' in 𝓝 q₀, evalWord w (fOf π q') (gOf σ q') = 1) :
    ∃ U : Set (PReal d e), IsOpen U ∧
      ((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))) Uᶜ = 0 ∧
      U ⊆ {q | HasRelation π σ q} := by
  have hae : ∀ᵐ q ∂((volume.restrict (simplexRegion d)).prod
      (volume.restrict (simplexRegion e))), q ∈ interior {q : PReal d e | HasRelation π σ q} := by
    filter_upwards [hrel, ae_goodParamsAt_all_thresholds (d := d) (e := e),
      ae_mem_simplexRegion_prod (d := d) (e := e)] with q hrelq hgood hreg
    exact mem_interior_hasRelation hreg hgood hrelq hA
  rw [MeasureTheory.ae_iff] at hae
  exact ⟨interior {q : PReal d e | HasRelation π σ q}, isOpen_interior, hae, interior_subset⟩

/-- **The set of parameter pairs carrying a nontrivial relation has an open subset of full
measure.**

Almost every pair is in the two open regions (`ae_mem_simplexRegion_prod`), is good at every
threshold (`ae_goodParamsAt_all_thresholds`) and carries a relation — the hypothesis `hrel`, which
`ChallengeSolved.lean` proves from `main`; at each such pair the relation is robust
(`evalWord_eventually_eq_one`), so the relation set is a neighbourhood of it.  The interior `U` of
the relation set is therefore open, contained in the relation set, and conull — which is the
statement that the pairs not generating a free group contain an open set of full measure.

`U` is the interior rather than the relation set itself: the relation set need not be open, and
`∀ᵐ q ∂μ, q ∈ U` is by definition `μ Uᶜ = 0`, with no measurability of the relation set required.
Points outside the two regions cost nothing, the measure being the product of the two restrictions
to the regions.

The relation set is in fact larger than the region: off it the total exchanges `fOf` and `gOf` are
often the identity already (`mkIET1` is the identity when the lengths do not sum to `1`), so `U`
contains points far from the region as well.  The content of the statement is on the region, where
`U` has null complement. -/
theorem exists_isOpen_subset_hasRelation_of_ae {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e))
    (hrel : ∀ᵐ q ∂((volume.restrict (simplexRegion d)).prod
      (volume.restrict (simplexRegion e))), HasRelation π σ q) :
    ∃ U : Set (PReal d e), IsOpen U ∧
      ((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))) Uᶜ = 0 ∧
      U ⊆ {q | HasRelation π σ q} :=
  exists_isOpen_subset_hasRelation_of_robust π σ hrel fun w _ h1 h2 hgood hw =>
    evalWord_eventually_eq_one π σ w ⟨h1, h2⟩ hgood hw

/-! ## The free coordinates of a point of the simplex -/

/-- **The free coordinates invert `simplexMap` on the simplex**: if the length vector `lam` has
total mass `1`, then the length vector of its first `d - 1` coordinates is `lam` itself.  Unlike
`toReal_simplexMap` this needs no positivity of the free coordinates, only the total mass, so it
applies on the whole simplex, boundary included. -/
theorem simplexMap_toReal {d : ℕ} [NeZero d] {lam : Fin d → ℝ≥0}
    (h : ∑ i, lam i = 1) :
    simplexMap d (fun i : Fin (d - 1) => (lam (Fin.castLE (Nat.sub_le d 1) i) : ℝ)) = lam := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  have hcast : ∀ i : Fin m,
      (lam (Fin.castLE (Nat.sub_le (m + 1) 1) i) : ℝ) = (lam i.castSucc : ℝ) := by
    intro i
    rw [show Fin.castLE (Nat.sub_le (m + 1) 1) i = i.castSucc from Fin.ext rfl]
  have hsum : ∑ i : Fin m, (lam (Fin.castLE (Nat.sub_le (m + 1) 1) i) : ℝ)
      = 1 - (lam (Fin.last m) : ℝ) := by
    rw [Finset.sum_congr rfl fun i _ => hcast i]
    have hsplit := Fin.sum_univ_castSucc fun i : Fin (m + 1) => (lam i : ℝ)
    rw [sum_coe_eq_one (mem_simplex.mpr h)] at hsplit
    linarith
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [simplexMap_last, hsum]
    rw [show (1 : ℝ) - (1 - (lam (Fin.last m) : ℝ)) = (lam (Fin.last m) : ℝ) by ring]
    exact Real.toNNReal_coe
  · rw [simplexMap_castSucc, hcast i]
    exact Real.toNNReal_coe

/-- **The free coordinates of a point of the simplex invert `simplexMap`**, first factor: the
first length vector of a pair is recovered from its first `d - 1` coordinates when its total mass
is `1`. -/
theorem simplexMap_toReal_fst {d e : ℕ} [NeZero d] {p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0)}
    (hp : p.1 ∈ simplex (Fin d)) : simplexMap d (toReal p).1 = p.1 :=
  simplexMap_toReal (mem_simplex.mp hp)

/-- **The free coordinates of a point of the simplex invert `simplexMap`**, second factor: the
counterpart of `simplexMap_toReal_fst` for the second length vector. -/
theorem simplexMap_toReal_snd {d e : ℕ} [NeZero e] {p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0)}
    (hp : p.2 ∈ simplex (Fin e)) : simplexMap e (toReal p).2 = p.2 :=
  simplexMap_toReal (mem_simplex.mp hp)

/-- **On the simplex, the first exchange of a pair of length vectors is `mkIET1`**: the free
coordinates `toReal p` and the length vector `p.1` give the same exchange `mkIET1`. -/
theorem fOf_toReal {d e : ℕ} [NeZero d] (π : Equiv.Perm (Fin d))
    (p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0)) (hp : p.1 ∈ simplex (Fin d)) :
    fOf π (toReal p) = mkIET1 p.1 π := by
  rw [fOf, simplexMap_toReal_fst hp]

/-- **On the simplex, the second exchange of a pair of length vectors is `mkIET1`**: the
counterpart of `fOf_toReal` for the second permutation. -/
theorem gOf_toReal {d e : ℕ} [NeZero e] (σ : Equiv.Perm (Fin e))
    (p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0)) (hp : p.2 ∈ simplex (Fin e)) :
    gOf σ (toReal p) = mkIET1 p.2 σ := by
  rw [gOf, simplexMap_toReal_snd hp]

/-! ## The statement in the paper's coordinates -/

/-- **The relation set of the paper's coordinates has an open trace of full measure**, the open
set being one of the ambient space `(Fin d → ℝ≥0) × (Fin e → ℝ≥0)`.

`O` is the preimage under the free coordinates `toReal` of the open set `U` of
`exists_isOpen_subset_hasRelation_of_robust`, so it is open and, `toReal` inverting `prodSimplexMap`
almost everywhere, of null complement for `simplexVolume d × simplexVolume e`.  A point `p` of its
trace on the product of the two simplices carries the relation witnessed at `toReal p`, since the
two exchanges agree there (`fOf_toReal`, `gOf_toReal`).

The conclusion is spelled out — at every `p ∈ O` whose two vectors have total mass `1`, a nontrivial
word trivial for `mkIETEquiv p.1 π 0` and `mkIETEquiv p.2 σ 0` — so that it names nothing but
`mkIETEquiv`, `evalWordEquiv` and the measure, and can be read as a statement on its own.  Writing
the two summations as hypotheses rather than intersecting `O` with the product of the two simplices
keeps `simplex` out of the statement, which is what a standalone target needs.

The set `O` cannot be replaced by an open subset of the product of the simplices: that product has
empty interior in the ambient space, so the openness can only be that of a trace, which is exactly
the paper's topology on `Δ_π × Δ_σ`. -/
theorem exists_isOpen_ae_exists_nontrivial_evalWordEquiv_eq_one_of_robust {d e : ℕ}
    [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e))
    (hrel : ∀ᵐ q ∂((volume.restrict (simplexRegion d)).prod
      (volume.restrict (simplexRegion e))), HasRelation π σ q)
    (hA : ∀ (w : FreeGroup Gen) {q₀ : PReal d e}, q₀.1 ∈ simplexRegion d →
      q₀.2 ∈ simplexRegion e → (∀ N, q₀ ∈ goodParamsAt N d e) →
      evalWord w (fOf π q₀) (gOf σ q₀) = 1 →
      ∀ᶠ q' in 𝓝 q₀, evalWord w (fOf π q') (gOf σ q') = 1) :
    ∃ O : Set ((Fin d → ℝ≥0) × (Fin e → ℝ≥0)), IsOpen O ∧
      ((simplexVolume d).prod (simplexVolume e)) Oᶜ = 0 ∧
      (∀ p ∈ O, (∑ i, p.1 i = 1) → (∑ j, p.2 j = 1) →
        ∃ w : FreeGroup Gen, w ≠ 1 ∧
          evalWordEquiv w (mkIETEquiv p.1 π 0) (mkIETEquiv p.2 σ 0) = 1) := by
  obtain ⟨U, hUopen, hUnull, hUsub⟩ := exists_isOpen_subset_hasRelation_of_robust π σ hrel hA
  refine ⟨toReal ⁻¹' U, hUopen.preimage continuous_toReal, ?_, ?_⟩
  · have hae : ∀ᵐ q ∂((volume.restrict (simplexRegion d)).prod
        (volume.restrict (simplexRegion e))), prodSimplexMap d e q ∈ toReal ⁻¹' U := by
      filter_upwards [ae_mem_simplexRegion_prod (d := d) (e := e),
        MeasureTheory.ae_iff.mpr hUnull] with q hq hqU
      rw [Set.mem_preimage, toReal_prodSimplexMap hq.1 hq.2]
      exact hqU
    have hpre : ((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e)))
        {q | toReal (prodSimplexMap d e q) ∉ U} = 0 :=
      MeasureTheory.ae_iff.mp hae
    have hset : (prodSimplexMap d e ⁻¹' (toReal ⁻¹' U)ᶜ)
        = {q | toReal (prodSimplexMap d e q) ∉ U} := by
      ext q
      simp
    rw [prod_simplexVolume_eq_map,
      Measure.map_apply (measurable_prodSimplexMap d e)
        (hUopen.preimage continuous_toReal).measurableSet.compl,
      hset]
    exact hpre
  · intro p hpO h1 h2
    obtain ⟨w, hwne, hw⟩ := hUsub hpO
    refine ⟨w, hwne, ?_⟩
    have hw' : evalWord w (mkIET1 p.1 π) (mkIET1 p.2 σ) = 1 := by
      rw [← fOf_toReal π p (mem_simplex.mpr h1), ← gOf_toReal σ p (mem_simplex.mpr h2)]
      exact hw
    have hw'' : evalWordEquiv w (mkIET1 p.1 π).toEquiv (mkIET1 p.2 σ).toEquiv = 1 :=
      evalWord_toEquiv_eq_one hw'
    rw [mkIET1_of_mem h1, mkIET1_of_mem h2] at hw''
    exact hw''

/-- **Almost every pair of length vectors carries a nontrivial relation, on an open trace.**

This is the paper's conclusion in its own coordinates: the pairs of length vectors not generating a
free group contain an open set of `Δ_π × Δ_σ` (the trace of `O`) which has full measure for the
product of the two simplex measures.  The robustness input of
`exists_isOpen_ae_exists_nontrivial_evalWordEquiv_eq_one_of_robust` is
`evalWord_eventually_eq_one`. -/
theorem exists_isOpen_ae_exists_nontrivial_evalWordEquiv_eq_one_of_ae {d e : ℕ}
    [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e))
    (hrel : ∀ᵐ q ∂((volume.restrict (simplexRegion d)).prod
      (volume.restrict (simplexRegion e))), HasRelation π σ q) :
    ∃ O : Set ((Fin d → ℝ≥0) × (Fin e → ℝ≥0)), IsOpen O ∧
      ((simplexVolume d).prod (simplexVolume e)) Oᶜ = 0 ∧
      (∀ p ∈ O, (∑ i, p.1 i = 1) → (∑ j, p.2 j = 1) →
        ∃ w : FreeGroup Gen, w ≠ 1 ∧
          evalWordEquiv w (mkIETEquiv p.1 π 0) (mkIETEquiv p.2 σ 0) = 1) :=
  exists_isOpen_ae_exists_nontrivial_evalWordEquiv_eq_one_of_robust π σ hrel
    fun w _ h1 h2 hgood hw => evalWord_eventually_eq_one π σ w ⟨h1, h2⟩ hgood hw

end IntervalExchange.Pair
