/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib
public import IETFree.UniqueErgodicity.Split
public import IETFree.UniqueErgodicity.Limits
public import IETFree.UniqueErgodicity.Transfer

/-!
# Measurability preparation for the split interval

This file collects the measure-theoretic facts that the germ-map construction (`IET.lean`) needs
from the
split interval, and none of which is in `Split.lean`, `Limits.lean` or `Transfer.lean`:

* `splitSet_countable`: the split set is countable (the `hD` hypothesis of the lift lemma);
* the `BorelSpace` instances on `SplitI D` and on the right part `[0⁺, 1⁻]`, which instance
  search supplies only under `[Countable D]` (a countable product of second countable spaces is
  second countable), together with the compactness of the right part;
* `measurable_proj`: the projection of the split interval is measurable;
* `germSection`, a *total* measurable section of the projection on `[0, 1)`, obtained by clamping
  the real line into `[0, 1]` and taking the right germ;
* `lift_unique_on_Ico`: the corrected lift lemma.  The blueprint's Lemma 4.1 asks for a section
  `s : ℝ → X` with `p (s x) = x` for *every* `x : ℝ`, which cannot hold as soon as `p` has
  bounded image (the split interval is the case at hand: `proj` maps onto `[0, 1]`).  The version
  below only asks for the section identity on `[0, 1)`, and for the pushforward to be carried by
  `[0, 1)`.
-/

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal BigOperators

namespace IETFree.UniqueErgodicity

/-! ## The split set -/

section SplitSet

variable {T : ℝ ≃ ℝ} {s : Finset ℝ}

/-- **The split set is countable**: a countable union over `ℤ` of images of the finite set
`s ∪ {1}`. -/
theorem splitSet_countable (T : ℝ ≃ ℝ) (s : Finset ℝ) : (splitSet T s).Countable := by
  have hunion : splitSet T s = ⋃ k : ℤ, ⇑(T ^ k) '' ((s : Set ℝ) ∪ {1}) := rfl
  rw [hunion]
  exact Set.countable_iUnion fun k =>
    ((s.finite_toSet.union (Set.finite_singleton 1)).image (⇑(T ^ k))).countable

end SplitSet

/-! ## Measurable structure on the split interval -/

section MeasurableStructure

namespace SplitI

variable {D : Set ℝ}

/-- The split interval over a countable split set is a Borel space.  The countability hypothesis is
not removable: it is what makes `D → Bool` second countable. -/
instance instBorelSpace [Countable D] : BorelSpace (SplitI D) := inferInstance

/-- With a countable split set, the measurable space of the split interval (the one induced by its
embedding into `ℝ × (D → Bool)`) is the Borel `σ`-algebra of its topology. -/
theorem measurableSpace_eq_borel [Countable D] :
    (inferInstance : MeasurableSpace (SplitI D)) = borel (SplitI D) :=
  BorelSpace.measurable_eq

/-- The right part `[0⁺, 1⁻]` of the split interval, a closed subset of a compact space, is a
Borel space for a countable split set. -/
instance instBorelSpaceRightPart [Countable D] : BorelSpace (rightPart D) := inferInstance

/-- The right part `[0⁺, 1⁻]` of the split interval is compact (`[0⁺, 1⁻]` is closed). -/
instance instCompactSpaceRightPart : CompactSpace (rightPart D) :=
  isCompact_iff_compactSpace.mp (isCompact_rightPart D)

/-- **The fibre of the projection over a point outside the split set is a single point.**  This is
the injectivity hypothesis `hinj` of the (corrected) lift lemma, for the split interval and for
every split set: two points with the same projection outside `D` have the same side choices. -/
theorem eq_of_proj_eq_of_notMem {z z' : SplitI D} (h : proj z = proj z')
    (hz : proj z ∉ D) : z = z' := by
  refine ext h (funext fun d => ?_)
  rcases lt_trichotomy (d : ℝ) (proj z) with hlt | heq | hgt
  · rw [coord_of_lt hlt, coord_of_lt (h ▸ hlt)]
  · exact absurd (heq ▸ d.2) hz
  · rw [coord_of_lt' hgt, coord_of_lt' (h ▸ hgt)]

end SplitI

/-- **The projection of the split interval is measurable** (it is even continuous). -/
theorem measurable_proj {D : Set ℝ} : Measurable (SplitI.proj (D := D)) :=
  measurable_fst.comp measurable_subtype_coe

/-- A `Bool`-valued function is measurable as soon as the preimage of `true` is measurable (the
measurable space of `Bool` is discrete). -/
theorem measurable_of_measurableSet_eq_true {α : Type*} [MeasurableSpace α] {f : α → Bool}
    (h : MeasurableSet {a | f a = true}) : Measurable f := by
  intro s _
  by_cases ht : true ∈ s
  · by_cases hf : false ∈ s
    · have hsu : s = Set.univ := by
        ext b
        cases b <;> simp [ht, hf]
      rw [hsu, Set.preimage_univ]
      exact MeasurableSet.univ
    · have hs : s = {true} := by
        ext b
        cases b <;> simp [ht, hf]
      rw [hs]
      exact h
  · by_cases hf : false ∈ s
    · have hs : s = {false} := by
        ext b
        cases b <;> simp [ht, hf]
      have hpre : f ⁻¹' ({false} : Set Bool) = {a | f a = true}ᶜ := by
        ext a
        cases hfa : f a <;> simp [hfa]
      rw [hs, hpre]
      exact h.compl
    · have hs : s = ∅ := by
        ext b
        cases b <;> simp [ht, hf]
      rw [hs, Set.preimage_empty]
      exact MeasurableSet.empty

/-- **The side choice of the split interval is measurable** for a countable split set: the set of
points whose side choice is `true` is the union of the points projecting outside `D` and, for each
`d : D`, of the points projecting to `d` with `d`-th coordinate `true` (a countable union, which is
where the countability of `D` is used). -/
theorem SplitI.measurable_side {D : Set ℝ} [Countable D] :
    Measurable (SplitI.side (D := D)) := by
  have hD : MeasurableSet D :=
    (Set.countable_coe_iff.mp (inferInstance : Countable ↥D)).measurableSet
  have hset : {z : SplitI D | SplitI.side z = true}
      = {z : SplitI D | SplitI.proj z ∉ D} ∪ ⋃ d : D,
          ({z : SplitI D | SplitI.proj z = (d : ℝ)} ∩ {z : SplitI D | z.1.2 d = true}) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hz
      by_cases hzD : SplitI.proj z ∈ D
      · refine Or.inr ⟨⟨SplitI.proj z, hzD⟩, rfl, ?_⟩
        rwa [SplitI.side, dif_pos hzD] at hz
      · exact Or.inl hzD
    · rintro (hz | ⟨d, hzd, hzcoord⟩)
      · rw [SplitI.side, dif_neg hz]
      · have hzdD : SplitI.proj z ∈ D := hzd ▸ d.2
        rw [SplitI.side, dif_pos hzdD,
          show (⟨SplitI.proj z, hzdD⟩ : D) = d from Subtype.ext hzd]
        exact hzcoord
  have hmeas : MeasurableSet {z : SplitI D | SplitI.side z = true} := by
    rw [hset]
    refine MeasurableSet.union (hD.compl.preimage measurable_proj) (MeasurableSet.iUnion ?_)
    intro d
    have hcoord : MeasurableSet {z : SplitI D | z.1.2 d = true} :=
      (measurableSet_singleton (true : Bool)).preimage (SplitI.continuous_coord d).measurable
    exact ((measurableSet_singleton (d : ℝ)).preimage measurable_proj).inter hcoord
  have hfun : SplitI.side (D := D)
      = fun z : SplitI D =>
          if z ∈ {z : SplitI D | SplitI.side z = true} then true else false := by
    funext z
    by_cases hz : z ∈ {z : SplitI D | SplitI.side z = true}
    · rw [if_pos hz]
      exact hz
    · rw [if_neg hz]
      cases hsz : SplitI.side z with
      | false => rfl
      | true => exact absurd hsz hz
  rw [hfun]
  exact Measurable.ite hmeas measurable_const measurable_const

end MeasurableStructure

/-! ## A total measurable section of the projection -/

section GermSection

variable {D : Set ℝ}

/-- The clamp of a real number into `[0, 1]`, used to make the germ section total. -/
noncomputable def clampI (x : ℝ) : ℝ := min (max x 0) 1

theorem continuous_clampI : Continuous clampI :=
  (continuous_id.max continuous_const).min continuous_const

theorem measurable_clampI : Measurable clampI := continuous_clampI.measurable

theorem clampI_mem (x : ℝ) : clampI x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min (le_max_right x 0) zero_le_one, min_le_right _ _⟩

theorem clampI_eq_self {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : clampI x = x := by
  unfold clampI
  rw [max_eq_left hx.1, min_eq_left hx.2]

/-- **The germ section** of the split interval: the right germ of the clamp of `x` into `[0, 1]`.
It is a total function `ℝ → SplitI D`, a measurable section of the projection on `[0, 1)`. -/
noncomputable def germSection (x : ℝ) : SplitI D :=
  SplitI.rightGerm (clampI x) (clampI_mem x)

/-- **The germ section is a section of the projection on `[0, 1)`.** -/
theorem proj_germSection {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    SplitI.proj (germSection (D := D) x) = x := by
  have h : clampI x = x := clampI_eq_self ⟨hx.1, le_of_lt hx.2⟩
  simp only [germSection, h, SplitI.proj_rightGerm]

/-- The value of the germ section, as a point of the ambient product `ℝ × (D → Bool)`.  This is
the function whose measurability gives that of the germ section. -/
noncomputable def germSectionVal (x : ℝ) : ℝ × (D → Bool) :=
  (clampI x, fun d : D => decide ((d : ℝ) ≤ clampI x))

theorem measurable_germSectionVal : Measurable (germSectionVal (D := D)) := by
  refine Measurable.prodMk measurable_clampI ?_
  rw [measurable_pi_iff]
  intro d
  have hif : (fun x : ℝ => decide ((d : ℝ) ≤ clampI x))
      = fun x : ℝ => if (d : ℝ) ≤ clampI x then true else false := by
    funext x
    by_cases h : (d : ℝ) ≤ clampI x <;> simp [h]
  rw [hif]
  exact Measurable.ite (measurableSet_Ici.preimage measurable_clampI) measurable_const
    measurable_const

/-- **The germ section is measurable**, for the measurable space of the split interval induced by
its embedding into `ℝ × (D → Bool)`. -/
theorem measurable_germSection : Measurable (germSection (D := D)) := by
  unfold germSection
  exact Measurable.subtype_mk measurable_germSectionVal

end GermSection

/-! ## The corrected lift lemma -/

section LiftUnique

/-- **Lemma 4.1 of the blueprint, corrected form.**  An atomless probability measure has at most
one lift along a measurable map that is injective off the preimage of a countable set, provided the
section identity `p (s x) = x` holds on `[0, 1)` only and the pushforward is carried by `[0, 1)`.

The total-section hypothesis of the blueprint's Lemma 4.1 (`∀ x : ℝ, p (s x) = x`) cannot be met
by the split interval: `proj` takes its values in `[0, 1]`, so no `s` and no `x > 1` satisfy
`proj (s x) = x`.  Here the section identity is only required where the measure lives, and the null
set `ν (p ⁻¹' D)` is replaced by the union of `p ⁻¹' D` and the complement of `p ⁻¹' [0, 1)`. -/
theorem lift_unique_on_Ico {X : Type*} [MeasurableSpace X]
    {lam : Measure ℝ} (hlam : ∀ x, lam {x} = 0) (D : Set ℝ) (hD : D.Countable) (p : X → ℝ)
    (s : ℝ → X) (hp : Measurable p) (hs : ∀ x ∈ Set.Ico (0 : ℝ) 1, p (s x) = x)
    (hsB : Measurable s)
    (hinj : ∀ z z' : X, p z = p z' → p z ∉ D → z = z')
    {ν : Measure X} [IsProbabilityMeasure ν] (hpush : ν.map p = lam)
    (hsupp : lam (Set.Ico (0 : ℝ) 1) = 1) : ν = lam.map s := by
  have hinst : NullSingletonClass (ν.map p) := by
    rw [hpush]
    exact ⟨hlam⟩
  have hDmeas : MeasurableSet D := hD.measurableSet
  have hDnull : ν (p ⁻¹' D) = 0 := by
    rw [← Measure.map_apply hp hDmeas]
    exact @Set.Countable.measure_zero ℝ _ D hD (ν.map p) hinst
  have hIcomeas : MeasurableSet (Set.Ico (0 : ℝ) 1) := measurableSet_Ico
  have hsupp' : ν (p ⁻¹' Set.Ico (0 : ℝ) 1) = 1 := by
    rw [← Measure.map_apply hp hIcomeas, hpush, hsupp]
  have hcompl : ν ((p ⁻¹' Set.Ico (0 : ℝ) 1)ᶜ) = 0 := by
    rw [measure_compl (hIcomeas.preimage hp) (measure_ne_top ν _), hsupp', measure_univ]
    simp
  have hnull : ν (p ⁻¹' D ∪ (p ⁻¹' Set.Ico (0 : ℝ) 1)ᶜ) = 0 :=
    measure_union_null hDnull hcompl
  have hae : (fun z => s (p z)) =ᵐ[ν] (id : X → X) := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null ?_ hnull
    intro z hz
    by_cases hzD : p z ∈ D
    · exact Or.inl hzD
    · by_cases hzI : p z ∈ Set.Ico (0 : ℝ) 1
      · refine absurd ?_ hz
        exact (hinj z (s (p z)) (hs (p z) hzI).symm hzD).symm
      · exact Or.inr (by simpa using hzI)
  calc ν = ν.map (fun z => s (p z)) := by rw [Measure.map_congr hae, Measure.map_id]
    _ = (ν.map p).map s := (Measure.map_map hsB hp).symm
    _ = lam.map s := by rw [hpush]

end LiftUnique

end IETFree.UniqueErgodicity

end
