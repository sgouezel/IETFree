/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.TopBotFormalism

/-!
Almost every point of `simplexVolumeOn α` lies in the simplex `simplexOn α`.

The file is self-contained apart from `IETFree.TopBotFormalism` (which provides `simplexOn`,
`simplexVolumeOn`, and, through `IETFree.IET`, `simplexRegion`, `simplexMap`,
 `simplexVolume`). Deliverables:
* `ae_mem_simplexOn_of_card_ne_zero` — the statement with the hypothesis `Fintype.card α ≠ 0`;
* `ae_mem_simplexOn_of_nonempty` — the same with `[Nonempty α]`.

**The statement as written (only `[Fintype α]`) is false**: for the empty alphabet the simplex
`simplexOn α` is empty while `simplexVolumeOn α` is a probability measure.  Every use in the project
has `α ≃ Fin n` with `n ≠ 0`, so the extra hypothesis is available. -/

@[expose] public section


open MeasureTheory
open scoped BigOperators ENNReal NNReal

/-! ## Measurability of the sets involved -/

/-- The simplex `{lam | ∑ lam = 1}` is measurable: a level set of a continuous function on the
product space. -/
theorem measurableSet_simplexOn (α : Type*) [Fintype α] : MeasurableSet (simplexOn α) := by
  have h : Measurable fun lam : α → ℝ≥0 => ∑ a, lam a :=
    Finset.measurable_sum _ fun a _ => measurable_pi_apply a
  simpa [simplexOn] using measurableSet_eq_fun h measurable_const

/-- On the free region, the coordinates of `simplexMap (m + 1) v` are nonnegative and sum to `1`. -/
theorem sum_simplexMap {m : ℕ} {v : Fin m → ℝ} (hv : v ∈ simplexRegion (m + 1)) :
    ∑ i : Fin (m + 1), simplexMap (m + 1) v i = 1 := by
  -- `hv` lives in the `Fin ((m + 1) - 1)` shape; restate it in the `Fin m` shape.
  have hv2 : ∑ j : Fin m, v j < 1 := hv.2
  have hlast : ((1 - ∑ j, v j).toNNReal : ℝ) = 1 - ∑ j, v j :=
    Real.coe_toNNReal _ (by linarith)
  have hcast (j : Fin m) : ((v j).toNNReal : ℝ) = v j := Real.coe_toNNReal _ (le_of_lt (hv.1 j))
  apply NNReal.coe_injective
  simp only [NNReal.coe_sum, NNReal.coe_one]
  rw [Fin.sum_univ_castSucc]
  simp only [simplexMap_castSucc, simplexMap_last, hlast, hcast]
  ring

/-! ## The a.e. statement, in the `Fin d` shape -/

/-- Almost every length vector of `simplexVolume d` is a probability vector (`d ≥ 1`; for `d = 0`
the statement is false). -/
theorem ae_mem_simplexOn_fin {d : ℕ} (hd : d ≠ 0) :
    ∀ᵐ l ∂(simplexVolume d), l ∈ simplexOn (Fin d) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  rw [simplexVolume]
  refine (ae_map_iff (f := simplexMap (m + 1))
    (μ := volume.restrict (simplexRegion (m + 1)))
    (measurable_simplexMap (m + 1)).aemeasurable
    (measurableSet_simplexOn (Fin (m + 1)))).mpr ?_
  filter_upwards [ae_restrict_mem (measurableSet_simplexRegion (m + 1))] with v hv
  exact sum_simplexMap hv

/-! ## The a.e. statement in the alphabet shape -/

/-- **Almost-everywhere membership**, with the necessary hypothesis `Fintype.card α ≠ 0`: almost
every point of `simplexVolumeOn α` lies in the simplex `simplexOn α`.  The transfer along
`simplexVolumeOn α = (simplexVolume (card α)).map (reindexing)` is `MeasureTheory.ae_map_iff`, which
needs two measurability side conditions: `AEMeasurable` of the reindexing map (`measurable_pi_apply`
coordinatewise) and measurability of `simplexOn α` (`measurableSet_simplexOn`). -/
theorem ae_mem_simplexOn_of_card_ne_zero {α : Type*} [Fintype α]
    (hα : Fintype.card α ≠ 0) :
    ∀ᵐ lam ∂(simplexVolumeOn α), lam ∈ simplexOn α := by
  have hmeas : Measurable
      (fun l : Fin (Fintype.card α) → ℝ≥0 => fun a => l (Fintype.equivFin α a)) := by
    refine measurable_pi_iff.mpr fun a => ?_
    exact measurable_pi_apply (Fintype.equivFin α a)
  rw [simplexVolumeOn]
  refine (ae_map_iff (f := fun l : Fin (Fintype.card α) → ℝ≥0 => fun a => l (Fintype.equivFin α a))
    (μ := simplexVolume (Fintype.card α)) hmeas.aemeasurable
    (measurableSet_simplexOn α)).mpr ?_
  filter_upwards [ae_mem_simplexOn_fin hα] with l hl
  rw [mem_simplexOn] at hl
  rwa [Equiv.sum_comp (Fintype.equivFin α) l]

/-- The same statement with the hypothesis as a typeclass: the shape closest to the target
statement of the project (which is stated for `[Fintype α]` only, and is false for `α` empty). -/
theorem ae_mem_simplexOn_of_nonempty {α : Type*} [Fintype α] [Nonempty α] :
    ∀ᵐ lam ∂(simplexVolumeOn α), lam ∈ simplexOn α :=
  ae_mem_simplexOn_of_card_ne_zero Fintype.card_ne_zero

/-! ## The hypothesis `Nonempty α` cannot be dropped  For the empty alphabet the statement above is
**false**: `simplexOn (Fin 0)` is empty, while `simplexVolumeOn (Fin 0)` is a probability measure
(the length vector of the empty family of intervals is the empty vector, and `Fin 0 → ℝ≥0` is a
one-point space).  We record the counterexample, but it is not needed below. -/

end
