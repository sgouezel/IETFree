/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.UniqueErgodicity.Split
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Measurability preparation for the split interval

This file collects the measure-theoretic facts that the germ-map construction (`IET.lean`) needs
from the
split interval, and none of which is in `Split.lean`, `Limits.lean` or `Transfer/Basic.lean`:

* `splitSet_countable`: the split set is countable (the `hD` hypothesis of the lift lemma);
* the `BorelSpace` instances on `SplitI D` and on the right part `[0⁺, 1⁻]`, which instance
  search supplies only under `[Countable D]` (a countable product of second countable spaces is
  second countable), together with the compactness of the right part;
* `measurable_proj`: the projection of the split interval is measurable;
* `germSectionIco`, a *total* measurable section of the projection on `[0, 1)`, obtained by
  clamping the real line into `[0, 1]` and taking the right germ;
* `lift_unique_on_Ico`: the corrected lift lemma.  The blueprint's Lemma 4.1 asks for a section
  `s : ℝ → X` with `p (s x) = x` for *every* `x : ℝ`, which cannot hold as soon as `p` has
  bounded image (the split interval is the case at hand: `proj` maps onto `[0, 1]`).  The version
  below only asks for the section identity on `[0, 1)`, and for the pushforward to be carried by
  `[0, 1)`.
-/

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal BigOperators

/-! ## The split set -/

namespace IntervalExchange.UniqueErgodicity

section SplitSet

variable {T : ℝ ≃ ℝ} {s : Finset ℝ}

/-- **The split set is countable**: a countable union over `ℤ` of images of the finite set
`s ∪ {1}`. -/
theorem splitSet_countable (T : ℝ ≃ ℝ) (s : Finset ℝ) : (splitSet T s).Countable := by
  have hunion : splitSet T s = ⋃ k : ℤ, ⇑(T ^ k) '' ((s : Set ℝ) ∪ {1}) := (rfl)
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

/-- The right part `[0⁺, 1⁻]` of the split interval, a closed subset of a compact space, is a
Borel space for a countable split set. -/
instance instBorelSpaceRightPart [Countable D] : BorelSpace (rightPart D) := inferInstance

/-- The right part `[0⁺, 1⁻]` of the split interval is compact (`[0⁺, 1⁻]` is closed). -/
instance instCompactSpaceRightPart : CompactSpace (rightPart D) :=
  isCompact_iff_compactSpace.mp (isCompact_rightPart D)

end SplitI

/-- **The projection of the split interval is measurable** (it is even continuous). -/
theorem measurable_proj {D : Set ℝ} : Measurable (SplitI.proj (D := D)) :=
  measurable_fst.comp measurable_subtype_coe

end MeasurableStructure

/-! ## A total measurable section of the projection -/

section GermSection

variable {D : Set ℝ}

/-- `clampI` is measurable: it is continuous (`continuous_clampI`, in `Split.lean`). -/
theorem measurable_clampI : Measurable clampI := continuous_clampI.measurable

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

end IntervalExchange.UniqueErgodicity

end
