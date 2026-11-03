/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.TopBotFormalism

/-!
# Volumes on the simplex

Everything here is stated for a simplex in dimension `n + 1`, whose
free coordinates live on `Fin n`: this is the indexing in which `Fin.snoc` applies, and it avoids
the `Fin (d - 1 + 1)` versus `Fin d` friction.  The bridge to the copied `simplexVolume d`, which
is `simplexMap d` on `Fin (d - 1)` and `Fin d`, is the lemma `simplexVolume_eq_chartVolume`.

Proved here (the geometric layer):

* `chart`, `region` and their API (`chart_sum`, `chart_injective`, `chart_pos`, measurability);
* `inducedMap`, the map of the free coordinates induced by a matrix `M` with column sums `1`, and
  `chart_inducedMap`: **in the chart, `l ↦ M • l` is `inducedMap M`**.

The analytic layer is in `IETFree/RauzyVeech/Affine.lean`: the determinant `det (inducedMap M) =
det M`, the change-of-variables formula, Lemma 1 and the consequences for `simplexVolumeOn`. -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

/-! ## The chart, in the `n → n + 1` indexing -/

/-- The chart from the free coordinates `Fin n` to the hyperplane `{∑ = 1}` of `ℝ^{n+1}`:
`v ↦ Fin.snoc v (1 - ∑ v)`. -/
noncomputable def chart (n : ℕ) (v : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc v (1 - ∑ i, v i)

/-- The open simplex of free coordinates. -/
def region (n : ℕ) : Set (Fin n → ℝ) := {v | (∀ i, 0 < v i) ∧ ∑ i, v i < 1}

@[simp] theorem chart_castSucc {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    chart n v i.castSucc = v i :=
  Fin.snoc_castSucc _ _ _

@[simp] theorem chart_last {n : ℕ} (v : Fin n → ℝ) :
    chart n v (Fin.last n) = 1 - ∑ i, v i :=
  Fin.snoc_last _ _

theorem chart_sum {n : ℕ} (v : Fin n → ℝ) : ∑ i, chart n v i = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp [chart_last]

theorem chart_injective {n : ℕ} : Function.Injective (chart n) := by
  intro v w h
  funext i
  have := congrFun h i.castSucc
  simpa using this

theorem chart_pos {n : ℕ} {v : Fin n → ℝ} (hv : v ∈ region n) : ∀ j, 0 < chart n v j := by
  intro j
  refine Fin.lastCases ?_ ?_ j
  · rw [chart_last]
    have := hv.2
    linarith
  · intro i
    rw [chart_castSucc]
    exact hv.1 i

theorem measurableSet_region (n : ℕ) : MeasurableSet (region n) := by
  have h1 : MeasurableSet {v : Fin n → ℝ | ∀ i, 0 < v i} := by
    simpa only [Set.ofPred_forall] using
      MeasurableSet.iInter fun i =>
        measurableSet_lt measurable_const (continuous_apply i).measurable
  have h2 : MeasurableSet {v : Fin n → ℝ | ∑ i, v i < 1} :=
    measurableSet_lt (Finset.measurable_sum _ fun i _ => (continuous_apply i).measurable)
      measurable_const
  exact h1.inter h2

/-! ## The induced map of the free coordinates -/

/-- The **linear** chart `v ↦ Fin.snoc v (-∑ v)`, whose image is the hyperplane `{∑ = 0}`; the
chart `chart` is `linChart` plus the constant vector `e_last`. -/
noncomputable def linChart (n : ℕ) (v : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc v (-∑ i, v i)

@[simp] theorem linChart_castSucc {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    linChart n v i.castSucc = v i :=
  Fin.snoc_castSucc _ _ _

@[simp] theorem linChart_last {n : ℕ} (v : Fin n → ℝ) :
    linChart n v (Fin.last n) = -∑ i, v i :=
  Fin.snoc_last _ _

theorem linChart_add {n : ℕ} (v w : Fin n → ℝ) :
    linChart n (v + w) = linChart n v + linChart n w := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · simp only [linChart_last, Pi.add_apply, Finset.sum_add_distrib]; ring
  · intro i; simp only [linChart_castSucc, Pi.add_apply]

theorem linChart_smul {n : ℕ} (c : ℝ) (v : Fin n → ℝ) :
    linChart n (c • v) = c • linChart n v := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · simp only [linChart_last, Pi.smul_apply, smul_eq_mul]
    rw [mul_neg, Finset.mul_sum]
  · intro i; simp only [linChart_castSucc, Pi.smul_apply]

theorem chart_eq_linChart_add {n : ℕ} (v : Fin n → ℝ) :
    chart n v = linChart n v + fun j => if j = Fin.last n then (1 : ℝ) else 0 := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · rw [chart_last, Pi.add_apply, linChart_last]
    simp
    ring
  · intro i
    rw [chart_castSucc, Pi.add_apply, linChart_castSucc]
    simp

/-- The affine map of the free coordinates induced by a matrix `M`: in the chart, the map
`l ↦ M • l` of the hyperplane becomes `v ↦ inducedMap M v` when the column sums of `M` are `1`. -/
noncomputable def inducedMap {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, M i.castSucc j * chart n v j

/-- The **linear part** of `inducedMap M`, i.e. `linChart`-based. -/
noncomputable def linInducedMap {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, M i.castSucc j * linChart n v j

theorem linInducedMap_add {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (v w : Fin n → ℝ) :
    linInducedMap M (v + w) = linInducedMap M v + linInducedMap M w := by
  funext i
  simp only [linInducedMap, Pi.add_apply, linChart_add, mul_add, Finset.sum_add_distrib]

theorem linInducedMap_smul {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (c : ℝ)
    (v : Fin n → ℝ) : linInducedMap M (c • v) = c • linInducedMap M v := by
  funext i
  simp only [linInducedMap, Pi.smul_apply, linChart_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The chart identity.**  If the column sums of `M` are `1` (`Mᵀ * 1 = 1`), then in the chart the
linear map `l ↦ M • l` of the hyperplane is `inducedMap M` on the free coordinates. -/
theorem chart_inducedMap {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hM : ∀ j, ∑ i, M i j = 1) (v : Fin n → ℝ) :
    chart n (inducedMap M v) = fun j => ∑ k, M j k * chart n v k := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · rw [chart_last]
    have hsum : (∑ i : Fin n, inducedMap M v i)
        = ∑ k, (∑ i : Fin n, M i.castSucc k) * chart n v k := by
      simp only [inducedMap, Finset.sum_mul]
      rw [Finset.sum_comm]
    calc 1 - ∑ i : Fin n, inducedMap M v i
        = ∑ k, chart n v k - ∑ k, (∑ i : Fin n, M i.castSucc k) * chart n v k := by
          rw [hsum, chart_sum]
      _ = ∑ k, (chart n v k - (∑ i : Fin n, M i.castSucc k) * chart n v k) := by
          rw [Finset.sum_sub_distrib]
      _ = ∑ k, (1 - ∑ i : Fin n, M i.castSucc k) * chart n v k := by
          refine Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ k, M (Fin.last n) k * chart n v k := by
          refine Finset.sum_congr rfl fun k _ => by
            have hk : 1 - ∑ i : Fin n, M i.castSucc k = M (Fin.last n) k := by
              have h := hM k
              rw [Fin.sum_univ_castSucc] at h
              linarith
            rw [hk]
  · intro i
    rw [chart_castSucc, inducedMap]

end
