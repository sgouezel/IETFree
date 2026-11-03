/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.CylinderVolume
public import IETFree.RauzyVeech.Nesting

/-!
# The region model of the simplex, and positivity of cylinder volumes

`simplexVolumeOn α` is the Lebesgue measure of the simplex seen in the free coordinates of the
chart, `region m ⊆ (Fin m → ℝ)`: the open region is nonempty (`region_nonempty`) and sits in the
unit box (`region_subset_box`), so it has positive finite Lebesgue measure (`volume_region_pos`,
`volume_region_ne_top`); the chart preimage of the simplex is the whole region
(`gchart_mem_simplexOn`), whence `simplexVolumeOn α (simplexOn α) = volume (region m)`
(`simplexVolumeOn_simplexOn_eq_region`, from `IETDatum₂.simplexVolumeOn_apply_gchart`).

From that positivity: `volume_simplexOn_pos` (the simplex has positive mass) and
`volume_simplexCyl_pos` (every path cylinder has positive mass, using Lemma 1 in the form
`volume_simplexCyl` of `IETFree/RauzyVeech/CylinderVolume.lean`).  These are what the strict
inequality of the contraction needs.

The matrix identity `colsum_mul_one_add_single` is the elementary column-sum computation behind the
step `Q(γ ++ [e]) = Q(γ) · (1 + E_{α_e α_{1-e}})`: only the column of the *secondary* name changes,
and it grows by the column of the name.

The volume of the child cylinder (Lemma 3 of the source) is the ratio `vol Δ(γ ++ [δ]) / vol Δ(γ) =
∏_b colsum_b(γ) / colsum_b(γ ++ δ)`, proved in `IETFree/RauzyVeech/BalancedSet.lean` as
`BalancedCylinders.volume_append_mul`. -/

@[expose] public section

open MeasureTheory Matrix
open scoped BigOperators ENNReal NNReal

namespace RegionVolume

/-! ## 1. The column sums of `Q · (1 + E_{c c'})`  `1 + E_{c c'}` is `rvMat e` in the coordinates `c
= α_e`, `c' = α_{1-e}`; the lemma is stated for an arbitrary integer matrix so that it is
independent of the path. -/

section MatrixColsum

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Only the column `c'` changes, and it grows by the column `c`.** -/
theorem colsum_mul_one_add_single (M : Matrix α α ℤ) (c c' β : α) :
    (∑ a, (M * (1 + Matrix.single c c' (1 : ℤ))) a β)
      = (∑ a, M a β) + (if β = c' then ∑ a, M a c else 0) := by
  have hM : M * (1 + Matrix.single c c' (1 : ℤ)) = M + M * Matrix.single c c' (1 : ℤ) := by
    rw [Matrix.mul_add, Matrix.mul_one]
  rw [hM]
  have hsplit : (∑ a, (M + M * Matrix.single c c' (1 : ℤ)) a β)
      = (∑ a, M a β) + ∑ a, (M * Matrix.single c c' (1 : ℤ)) a β := by
    simp only [Matrix.add_apply, Finset.sum_add_distrib]
  rw [hsplit]
  congr 1
  by_cases h : β = c'
  · subst h
    simp
  · rw [if_neg h]
    simp [h]

end MatrixColsum

/-! ## 2. Positivity of the cylinder volumes  `vol Δ(γ ++ [e]) < vol Δ(γ)` needs `vol Δ(γ) ≠ 0` and
`≠ ∞`, i.e. the free region of the simplex chart has positive finite Lebesgue measure.  Since the
region is open and nonempty it has positive measure (`IsOpen.measure_pos` for the `IsOpenPosMeasure`
volume of `Fin m → ℝ`), and it sits in the unit box, so its measure is finite.  The link between the
region and `simplexVolumeOn α (simplexOn α)` is `IETDatum₂.simplexVolumeOn_apply_gchart` of
`Nesting`: the chart preimage of the simplex is the whole region. -/

section Region

theorem isOpen_region (m : ℕ) : IsOpen (region m) := by
  have h1 : IsOpen {v : Fin m → ℝ | ∀ i, 0 < v i} := by
    rw [show {v : Fin m → ℝ | ∀ i, 0 < v i} = ⋂ i, {v | 0 < v i} from by ext v; simp]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have h2 : IsOpen {v : Fin m → ℝ | ∑ i, v i < 1} :=
    isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  simpa only [region, Set.ofPred_and] using h1.inter h2

theorem region_nonempty (m : ℕ) : (region m).Nonempty := by
  refine ⟨fun _ => (((m : ℝ) + 1)⁻¹ / 2), ?_, ?_⟩
  · intro i; positivity
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 : (0:ℝ) < (m : ℝ) + 1 := by positivity
    rw [show (m : ℝ) * (((m : ℝ) + 1)⁻¹ / 2) = (m:ℝ) / (2 * ((m:ℝ)+1)) from by field_simp]
    rw [div_lt_one (by positivity)]
    linarith

/-- **The free region has positive measure.** -/
theorem volume_region_pos (m : ℕ) : 0 < volume (region m) :=
  (isOpen_region m).measure_pos volume (region_nonempty m)

theorem region_subset_box (m : ℕ) :
    region m ⊆ Set.pi Set.univ (fun _ : Fin m => Set.Ioo (0:ℝ) 1) := by
  intro v hv
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
  refine fun i => ⟨hv.1 i, ?_⟩
  have h2 : v i ≤ ∑ j, v j :=
    Finset.single_le_sum (f := v) (fun j _ => le_of_lt (hv.1 j)) (Finset.mem_univ i)
  linarith [hv.2]

/-- **The free region has finite measure.** -/
theorem volume_region_ne_top (m : ℕ) : volume (region m) ≠ ⊤ := by
  have hle : volume (region m) ≤ volume (Set.pi Set.univ (fun _ : Fin m => Set.Ioo (0:ℝ) 1)) :=
    measure_mono (region_subset_box m)
  rw [Real.volume_pi_Ioo] at hle
  refine ne_of_lt (lt_of_le_of_lt hle ?_)
  exact ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top

end Region

section RegionSimplex

variable {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}

open IETDatum₂

omit [DecidableEq α] in
theorem gchart_mem_simplexOn (P : IETDatum₂ α (m + 1)) {v : Fin m → ℝ} (hv : v ∈ region m) :
    v ∈ gchart P ⁻¹' simplexOn α := by
  simp only [Set.mem_preimage, gchart, simplexOn, Set.mem_ofPred_eq]
  have hpos : ∀ i, 0 < chart m v i := fun i => chart_pos hv i
  refine NNReal.coe_injective ?_
  rw [NNReal.coe_sum, NNReal.coe_one]
  calc ∑ a, ((chart m v (P.piBottom a)).toNNReal : ℝ)
      = ∑ a, chart m v (P.piBottom a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Real.coe_toNNReal _ (le_of_lt (hpos _))
    _ = ∑ i, chart m v i := Equiv.sum_comp P.piBottom _
    _ = 1 := chart_sum v

omit [DecidableEq α] in
/-- **`simplexVolumeOn α` of the simplex is the Lebesgue measure of the free region.** -/
theorem simplexVolumeOn_simplexOn_eq_region (P : IETDatum₂ α (m + 1)) :
    simplexVolumeOn α (simplexOn α) = volume (region m) := by
  rw [IETDatum₂.simplexVolumeOn_apply_gchart P (simplexOn α) (measurableSet_simplexOn α)]
  rw [show gchart P ⁻¹' simplexOn α ∩ region m = region m from
    Set.inter_eq_right.mpr fun v hv => gchart_mem_simplexOn P hv]

end RegionSimplex

section Positivity

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

open IETDatum₂

omit [DecidableEq α] in
theorem volume_simplexOn_pos (P : IETDatum₂ α n) : 0 < simplexVolumeOn α (simplexOn α) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
  rw [simplexVolumeOn_simplexOn_eq_region P]
  exact volume_region_pos m

/-- **Every path cylinder has positive measure.** -/
theorem volume_simplexCyl_pos (P : IETDatum₂ α n) (γ : List Bool) :
    0 < simplexVolumeOn α (simplexCyl P γ) := by
  rw [volume_simplexCyl]
  have hp : (0 : ℝ≥0∞) < ((∏ b, (colsumNN (Path.Q P γ) b)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_zero, ENNReal.coe_lt_coe]
    exact Finset.prod_pos fun b _ => inv_pos.mpr (colsumNN_pos P γ b)
  exact ENNReal.mul_pos (ne_of_gt hp) (ne_of_gt (volume_simplexOn_pos P))

end Positivity

end RegionVolume

end
