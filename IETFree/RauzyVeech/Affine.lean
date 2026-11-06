/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.SimplexAe
public import IETFree.RauzyVeech.Volume

/-!
# The analytic layer of the volume computation

This is the analytic layer of the volume computation, on top of the geometric layer of
`IETFree/RauzyVeech/Volume.lean`:

* `det_sub_last_col` — the pure matrix identity `det (Q - b·1ᵀ) = det M` for a matrix with column
  sums `1` (by row and column operations);
* `det_linInducedMap` — the determinant of the linear part of `inducedMap M` is `det M`;
* `AffineVolume.*` — the affine decomposition `inducedMap M = linInducedMap M + b`, the change of
  variables `volume (inducedMap M '' S) = |det M| · volume S`, injectivity and region membership
  under the hypotheses that are actually needed, and the counterexamples showing that the
  hypotheses cannot be dropped.

The hypotheses that the project's statements carry — column sums `1` and `det M ≠ 0` — are exactly
the ones used below (`AffineVolume.volume_image_inducedMap_of_det`,
`AffineVolume.inducedMap_mem_region`). -/

@[expose] public section


open MeasureTheory Matrix
open scoped BigOperators ENNReal NNReal

/-! ## The pure matrix identity

With `Q` the top-left `n × n` block of `M`, `b` the top part of the last column and `A = Q - b·1ᵀ`,
multiply `M` on the left by `L` (add every row to the last row) and on the right by `E` (subtract
the last column from each of the first `n` columns).  Both are lower triangular with diagonal `1`,
hence have determinant `1`; the column sums of `M` give `L * M * E = ![A, b; 0, 1]`, whose
determinant is `det A` by Laplace expansion along the last row. -/

/-- The elementary matrix that adds every row to the last row. -/
def lastRowOp (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => if i = Fin.last n then 1 else if i = j then 1 else 0

/-- The elementary matrix whose first `n` columns are `e_j - e_last` and whose last column is
`e_last` (i.e. the column operation "subtract the last column from all the others"). -/
def lastColOp (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j =>
    if j = Fin.last n then (if i = Fin.last n then 1 else 0)
    else if i = j then 1 else if i = Fin.last n then -1 else 0

theorem lastColOp_apply_last (n : ℕ) (i : Fin (n + 1)) :
    lastColOp n i (Fin.last n) = if i = Fin.last n then 1 else 0 := by
  simp [lastColOp]

theorem lastColOp_apply_castSucc (n : ℕ) (i : Fin (n + 1)) (j : Fin n) :
    lastColOp n i j.castSucc = if i = j.castSucc then 1 else if i = Fin.last n then -1 else 0 := by
  rw [lastColOp, ite_eq_right (Fin.castSucc_ne_last j)]

theorem lastRowOp_apply_last (n : ℕ) (j : Fin (n + 1)) : lastRowOp n (Fin.last n) j = 1 := by
  simp [lastRowOp]

theorem lastRowOp_apply_castSucc (n : ℕ) (i : Fin n) (j : Fin (n + 1)) :
    lastRowOp n i.castSucc j = if i.castSucc = j then 1 else 0 := by
  rw [lastRowOp, ite_eq_right (Fin.castSucc_ne_last i)]

theorem isLowerTriangular_lastRowOp (n : ℕ) : (lastRowOp n).IsLowerTriangular := by
  intro i j hij
  -- `toDual j < toDual i` means `i < j`
  have hi : i ≠ Fin.last n := ne_of_lt ((show i < j from hij).trans_le (Fin.le_last j))
  have hijne : i ≠ j := ne_of_lt (show i < j from hij)
  simp [lastRowOp, hi, hijne]

theorem isLowerTriangular_lastColOp (n : ℕ) : (lastColOp n).IsLowerTriangular := by
  intro i j hij
  have hi : i ≠ Fin.last n := ne_of_lt ((show i < j from hij).trans_le (Fin.le_last j))
  have hijne : i ≠ j := ne_of_lt (show i < j from hij)
  simp [lastColOp, hi, hijne]

theorem det_lastRowOp (n : ℕ) : (lastRowOp n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (isLowerTriangular_lastRowOp n)]
  refine Finset.prod_eq_one fun i _ => ?_
  simp only [lastRowOp]
  by_cases h : i = Fin.last n <;> simp [h]

theorem det_lastColOp (n : ℕ) : (lastColOp n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (isLowerTriangular_lastColOp n)]
  refine Finset.prod_eq_one fun i _ => ?_
  simp only [lastColOp]
  by_cases h : i = Fin.last n <;> simp [h]

/-! ## The two elementary operations, entrywise -/

theorem mul_lastColOp_apply_last {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i : Fin (n + 1)) :
    (M * lastColOp n) i (Fin.last n) = M i (Fin.last n) := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  have h1 (b : Fin n) : lastColOp n b.castSucc (Fin.last n) =
      0 := by rw [lastColOp_apply_last, ite_eq_right (Fin.castSucc_ne_last b)]
  have h2 : lastColOp n (Fin.last n) (Fin.last n) = 1 := by
    rw [lastColOp_apply_last, ite_eq_left rfl]
  rw [h2]
  simp [h1]

theorem mul_lastColOp_apply_castSucc {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i : Fin (n + 1)) (j : Fin n) :
    (M * lastColOp n) i j.castSucc = M i j.castSucc - M i (Fin.last n) := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  have h1 (b : Fin n) : lastColOp n b.castSucc j.castSucc = if b = j then 1 else 0 := by
    rw [lastColOp_apply_castSucc]
    by_cases hbj : b = j
    · subst hbj; simp
    · rw [ite_eq_right (fun h => hbj (Fin.castSucc_injective n h)),
        ite_eq_right (Fin.castSucc_ne_last b),
        ite_eq_right hbj]
  have h2 : lastColOp n (Fin.last n) j.castSucc = -1 := by
    rw [lastColOp_apply_castSucc, ite_eq_right (Fin.castSucc_ne_last j).symm, ite_eq_left rfl]
  rw [h2]
  simp only [h1, mul_neg, mul_one]
  have hsum : (∑ b : Fin n, M i b.castSucc * (if b = j then 1 else 0)) = M i j.castSucc := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; rw [ite_eq_right hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hsum]
  ring

theorem lastRowOp_mul_apply_last {n : ℕ} (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (j : Fin (n + 1)) :
    (lastRowOp n * P) (Fin.last n) j = ∑ k, P k j := by
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [lastRowOp_apply_last, one_mul]

theorem lastRowOp_mul_apply_castSucc {n : ℕ} (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i : Fin n) (j : Fin (n + 1)) :
    (lastRowOp n * P) i.castSucc j = P i.castSucc j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i.castSucc]
  · rw [lastRowOp_apply_castSucc, ite_eq_left rfl, one_mul]
  · intro b _ hb
    rw [lastRowOp_apply_castSucc, ite_eq_right (Ne.symm hb), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The main computation -/

/-- `L * M * E` is `![A, b; 0, 1]`, entrywise. -/
theorem lastRowOp_mul_lastColOp {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hM : ∀ j, ∑ i, M i j = 1) :
    lastRowOp n * M * lastColOp n
      = fun i j => if i = Fin.last n then (if j = Fin.last n then 1 else 0)
          else (if j = Fin.last n then M i (Fin.last n) else M i j - M i (Fin.last n)) := by
  ext i j
  rw [Matrix.mul_assoc]
  refine Fin.lastCases ?_ ?_ i
  · -- the last row
    refine Fin.lastCases ?_ ?_ j
    · -- last row, last column
      rw [lastRowOp_mul_apply_last,
        Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => mul_lastColOp_apply_last M k),
        hM, ite_eq_left rfl, ite_eq_left rfl]
    · intro j'
      rw [lastRowOp_mul_apply_last,
        Finset.sum_congr rfl
          (fun k (_ : k ∈ Finset.univ) => mul_lastColOp_apply_castSucc M k j'),
        Finset.sum_sub_distrib, hM, hM, ite_eq_left rfl, ite_eq_right (Fin.castSucc_ne_last j')]
      ring
  · intro i'
    refine Fin.lastCases ?_ ?_ j
    · rw [lastRowOp_mul_apply_castSucc, mul_lastColOp_apply_last,
        ite_eq_right (Fin.castSucc_ne_last i'),
        ite_eq_left rfl]
    · intro j'
      rw [lastRowOp_mul_apply_castSucc, mul_lastColOp_apply_castSucc,
        ite_eq_right (Fin.castSucc_ne_last i'), ite_eq_right (Fin.castSucc_ne_last j')]

/-- **The determinant identity.**  Subtracting the last column from each of the first `n` columns
of a matrix whose column sums are all `1` does not change the determinant. -/
theorem det_sub_last_col {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hM : ∀ j, ∑ i, M i j = 1) :
    (Matrix.of fun i j : Fin n => M i.castSucc j.castSucc - M i.castSucc (Fin.last n)).det
      = M.det := by
  set A : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j => M i.castSucc j.castSucc - M i.castSucc (Fin.last n) with hA
  set N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    fun i j => if i = Fin.last n then (if j = Fin.last n then 1 else 0)
      else (if j = Fin.last n then M i (Fin.last n) else M i j - M i (Fin.last n)) with hN
  have h1 : (lastRowOp n * M * lastColOp n).det = M.det := by
    rw [Matrix.det_mul, Matrix.det_mul, det_lastRowOp, det_lastColOp, one_mul, mul_one]
  have h2 : lastRowOp n * M * lastColOp n = N := lastRowOp_mul_lastColOp M hM
  have hNsub : N.submatrix Fin.castSucc Fin.castSucc = A := by
    ext i j
    simp only [Matrix.submatrix_apply]
    rw [hN, hA]
    simp only [Matrix.of_apply]
    rw [ite_eq_right (Fin.castSucc_ne_last i), ite_eq_right (Fin.castSucc_ne_last j)]
  have h3 : N.det = A.det := by
    rw [Matrix.det_succ_row N (Fin.last n), Finset.sum_eq_single (Fin.last n)]
    · rw [Fin.succAbove_last, hNsub, hN]
      have hsign : (-1 : ℝ) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) = 1 := by
        rw [Fin.val_last, show n + n = 2 * n by ring, pow_mul]
        norm_num
      rw [hsign]
      simp
    · intro j _ hj
      rw [hN]
      simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [← h3, ← h2, h1]

/-! ## The determinant of the linear part of `inducedMap` -/

namespace AffineVolume

/-! ## 1. The affine decomposition `inducedMap M = linInducedMap M + const` -/

/-- `inducedMap M` is its linear part plus the constant vector made of the last column of `M`. -/
theorem inducedMap_eq_linInducedMap_add {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (v : Fin n → ℝ) :
    inducedMap M v = linInducedMap M v + fun i => M i.castSucc (Fin.last n) := by
  have hsum (i : Fin n) :
    (∑ j : Fin (n + 1), M i.castSucc j *
        (if j = Fin.last n then (1 : ℝ) else 0)) = M i.castSucc (Fin.last n) := by
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  funext i
  simp only [inducedMap, linInducedMap, Pi.add_apply, chart_eq_linChart_add, Pi.add_apply,
    mul_add, Finset.sum_add_distrib, hsum]

/-- `linInducedMap M` as a linear map. -/
noncomputable def linInducedMapLinear {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  { toFun := linInducedMap M
    map_add' := linInducedMap_add M
    map_smul' := linInducedMap_smul M }

@[simp] theorem linInducedMapLinear_apply {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (v : Fin n → ℝ) : linInducedMapLinear M v = linInducedMap M v := rfl

/-- Row form of the linear part: on the standard basis its matrix is
`i j ↦ M i.castSucc j.castSucc - M i.castSucc (Fin.last n)`. -/
theorem linInducedMap_apply_eq_matrix {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (v : Fin n → ℝ) (i : Fin n) :
    linInducedMap M v i
      = ∑ j, (M i.castSucc j.castSucc - M i.castSucc (Fin.last n)) * v j := by
  have hA : linInducedMap M v i
      = (∑ j : Fin n, M i.castSucc j.castSucc * v j)
        - ∑ j : Fin n, M i.castSucc (Fin.last n) * v j := by
    rw [linInducedMap, Fin.sum_univ_castSucc, linChart_last, mul_neg, Finset.mul_sum]
    simp only [linChart_castSucc]
    ring
  rw [hA, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The matrix of `linInducedMap M` in the standard basis. -/
theorem toMatrix'_linInducedMapLinear {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    LinearMap.toMatrix' (linInducedMapLinear M)
      = fun i j => M i.castSucc j.castSucc - M i.castSucc (Fin.last n) := by
  ext i j
  rw [LinearMap.toMatrix'_apply, linInducedMapLinear_apply, linInducedMap_apply_eq_matrix,
    Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem det_linInducedMap_of_toMatrix_det {n : ℕ}
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hdet : (LinearMap.toMatrix' (linInducedMapLinear M)).det = M.det) :
    LinearMap.det (linInducedMapLinear M) = M.det := by
  rw [← LinearMap.det_toMatrix', hdet]

/-- Interface with `det_sub_last_col`, the pure matrix identity of this file: it is exactly the
hypothesis `hdet` here, because `toMatrix'_linInducedMapLinear` identifies the matrix of the linear
part with `i j ↦ M i.castSucc j.castSucc - M i.castSucc (Fin.last n)`. -/
theorem det_linInducedMap_of_matrix {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hdet : (Matrix.of fun i j : Fin n =>
      M i.castSucc j.castSucc - M i.castSucc (Fin.last n)).det = M.det) :
    LinearMap.det (linInducedMapLinear M) = M.det :=
  det_linInducedMap_of_toMatrix_det (by rw [toMatrix'_linInducedMapLinear]; exact hdet)

/-! ## 3. Membership in the region -/

/-- `inducedMap M` maps the open region into itself for a nonnegative `M` with column sums `1` and
`det M ≠ 0`.  The determinant hypothesis is necessary. -/
theorem inducedMap_mem_region {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hM0 : ∀ i j, 0 ≤ M i j) (hM : ∀ j, ∑ i, M i j = 1) (hdet : M.det ≠ 0)
    {v : Fin n → ℝ} (hv : v ∈ region n) : inducedMap M v ∈ region n := by
  -- `det M ≠ 0` forces every row of `M` to have a strictly positive entry
  have hrow (k : Fin (n + 1)) : ∃ j, 0 < M k j := by
    by_contra h
    rw [not_exists] at h
    refine hdet (Matrix.det_eq_zero_of_row_eq_zero k fun j => ?_)
    exact le_antisymm (not_lt.mp (h j)) (hM0 k j)
  have hchart := chart_pos hv
  constructor
  · intro i
    rw [inducedMap]
    obtain ⟨j, hj⟩ := hrow i.castSucc
    exact Finset.sum_pos' (fun b _ => mul_nonneg (hM0 _ _) (le_of_lt (hchart b)))
      ⟨j, Finset.mem_univ _, mul_pos hj (hchart j)⟩
  · have hlast : (1 : ℝ) - ∑ i, inducedMap M v i
        = ∑ k, M (Fin.last n) k * chart n v k := by
      have h := congrFun (chart_inducedMap (M := M) hM v) (Fin.last n)
      rwa [chart_last] at h
    obtain ⟨j, hj⟩ := hrow (Fin.last n)
    have hpos : 0 < ∑ k, M (Fin.last n) k * chart n v k :=
      Finset.sum_pos' (fun b _ => mul_nonneg (hM0 _ _) (le_of_lt (hchart b)))
        ⟨j, Finset.mem_univ _, mul_pos hj (hchart j)⟩
    linarith

/-! ## 4. Change of variables -/

/-- Core change of variables: only the determinant of the linear part is needed, and the conclusion
holds for **every** set `S` (no measurability, no inclusion in the region).  Axiom-free. -/
theorem volume_image_inducedMap_of_det {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hdet_eq : LinearMap.det (linInducedMapLinear M) = M.det) (S : Set (Fin n → ℝ)) :
    volume (inducedMap M '' S) = ENNReal.ofReal |M.det| * volume S := by
  set b : Fin n → ℝ := fun i => M i.castSucc (Fin.last n) with hb
  -- the Lebesgue measure on `Fin n → ℝ` is translation invariant
  have htrans (T : Set (Fin n → ℝ)) : volume ((fun y => y + b) '' T) = volume T := by
    rw [← measure_preimage_add_right volume b ((fun y => y + b) '' T),
      (add_left_injective b).preimage_image]
  have hdecomp : inducedMap M = fun v : Fin n → ℝ => linInducedMapLinear M v + b := by
    funext v
    rw [inducedMap_eq_linInducedMap_add, hb]
    rfl
  rw [hdecomp]
  have himg : (fun v : Fin n → ℝ => linInducedMapLinear M v + b) '' S
      = (fun y : Fin n → ℝ => y + b) '' (linInducedMapLinear M '' S) := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨linInducedMapLinear M v, ⟨v, hv, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
  calc volume ((fun v : Fin n → ℝ => linInducedMapLinear M v + b) '' S)
      = volume ((fun y : Fin n → ℝ => y + b) '' (linInducedMapLinear M '' S)) := by rw [himg]
    _ = volume (linInducedMapLinear M '' S) := htrans _
    _ = ENNReal.ofReal |LinearMap.det (linInducedMapLinear M)| * volume S :=
        Measure.addHaar_image_linearMap volume (linInducedMapLinear M) S
    _ = ENNReal.ofReal |M.det| * volume S := by rw [hdet_eq]

end AffineVolume

/-! ## The determinant of the linear part -/

/-- The determinant of the linear part of `inducedMap M`, deduced from `det_sub_last_col`. -/
theorem det_linInducedMap {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hM : ∀ j, ∑ i, M i j = 1) : LinearMap.det (AffineVolume.linInducedMapLinear M) = M.det :=
  AffineVolume.det_linInducedMap_of_matrix (det_sub_last_col M hM)

/-! ## Permutation invariance of the volume  `chartVolume_map_perm` says that `l ↦ l ∘ σ` is
`inducedMap (permMat σ)` in the chart, `permMat σ` has nonnegative entries, column sums `1` and
determinant `±1`, and `inducedMap (permMat σ)` maps the region onto itself (inverse `permMat σ⁻¹`),
so the change of variables with `|det| = 1` gives the invariance. -/

/-! ## The permutation matrix -/

/-- The matrix of the permutation `σ`; it acts on vectors by `l ↦ l ∘ σ`. -/
def permMat {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => if σ i = j then 1 else 0

theorem permMat_apply {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1)) :
    permMat σ i j = if σ i = j then (1 : ℝ) else 0 := rfl

theorem permMat_eq_one {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))} {i j : Fin (n + 1)}
    (h : σ i = j) : permMat σ i j = 1 := by
  rw [permMat_apply, ite_eq_left h]

theorem permMat_eq_zero {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))} {i j : Fin (n + 1)}
    (h : σ i ≠ j) : permMat σ i j = 0 := by
  rw [permMat_apply, ite_eq_right h]

theorem permMat_nonneg {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    ∀ i j, 0 ≤ permMat σ i j := by
  intro i j
  rw [permMat_apply]
  split <;> norm_num

theorem permMat_col_sum {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    ∀ j, ∑ i, permMat σ i j = 1 := by
  intro j
  refine (Finset.sum_eq_single (σ.symm j) ?_ ?_).trans ?_
  · intro b _ hb
    exact permMat_eq_zero (fun h => hb ((Equiv.eq_symm_apply σ).mpr h))
  · intro h; exact absurd (Finset.mem_univ _) h
  · exact permMat_eq_one (σ.apply_symm_apply j)

theorem permMat_mul_symm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    permMat σ * permMat σ.symm = 1 := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.one_apply]
  refine (Finset.sum_eq_single (σ i) ?_ ?_).trans ?_
  · intro b _ hb
    exact mul_eq_zero_of_left (permMat_eq_zero (Ne.symm hb)) _
  · intro h; exact absurd (Finset.mem_univ _) h
  · simp [permMat_apply]

theorem permMat_transpose_mul {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    (permMat σ)ᵀ * permMat σ = 1 := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply]
  refine (Finset.sum_eq_single (σ.symm i) ?_ ?_).trans ?_
  · intro b _ hb
    exact mul_eq_zero_of_left
      (permMat_eq_zero (fun h => hb ((Equiv.eq_symm_apply σ).mpr h))) _
  · intro h; exact absurd (Finset.mem_univ _) h
  · simp [permMat_apply]

/-- `det (permMat σ) * det (permMat σ) = 1`, from `(permMat σ)ᵀ * permMat σ = 1`. -/
theorem permMat_det_mul_self {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    (permMat σ).det * (permMat σ).det = 1 := by
  have h := congrArg Matrix.det (permMat_transpose_mul σ)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  exact h

theorem permMat_det_ne_zero {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    (permMat σ).det ≠ 0 := by
  intro h
  have := permMat_det_mul_self σ
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem permMat_abs_det {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    |(permMat σ).det| = 1 := by
  have h2 : (permMat σ).det ^ 2 = 1 := by
    rw [sq]; exact permMat_det_mul_self σ
  rcases sq_eq_one_iff.mp h2 with h | h
  · rw [h, abs_one]
  · rw [h, abs_neg, abs_one]

/-! ## The induced maps: composition and the unit matrix -/

theorem inducedMap_one {n : ℕ} (v : Fin n → ℝ) :
    inducedMap (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) v = v := by
  funext i
  simp only [inducedMap]
  rw [Finset.sum_eq_single i.castSucc]
  · rw [Matrix.one_apply, ite_eq_left rfl, one_mul, chart_castSucc]
  · intro b _ hb
    rw [Matrix.one_apply, ite_eq_right (Ne.symm hb), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Composition of induced maps**: `inducedMap M ∘ inducedMap N = inducedMap (M * N)` when the
column sums of `N` are `1`. -/
theorem inducedMap_comp {n : ℕ} {M N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hN : ∀ j, ∑ i, N i j = 1) (v : Fin n → ℝ) :
    inducedMap M (inducedMap N v) = inducedMap (M * N) v := by
  have hpt (j : Fin (n + 1)) : chart n (inducedMap N v) j = ∑ k, N j k * chart n v k := congrFun
      (chart_inducedMap (M := N) hN v) j
  funext i
  simp only [inducedMap]
  simp only [Matrix.mul_apply, hpt, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `inducedMap (permMat σ) ∘ inducedMap (permMat σ⁻¹) = id`. -/
theorem inducedMap_permMat_comp {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (v : Fin n → ℝ) :
    inducedMap (permMat σ) (inducedMap (permMat σ.symm) v) = v := by
  rw [inducedMap_comp (M := permMat σ) (N := permMat σ.symm) (permMat_col_sum σ.symm),
    permMat_mul_symm, inducedMap_one]

/-- **The chart identity for permutation matrices**: in the chart, `inducedMap (permMat σ)` is the
permutation of the coordinates `l ↦ l ∘ σ`. -/
theorem chart_inducedMap_permMat {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (v : Fin n → ℝ) :
    chart n (inducedMap (permMat σ) v) = fun j => chart n v (σ j) := by
  rw [chart_inducedMap (M := permMat σ) (permMat_col_sum σ)]
  funext j
  refine (Finset.sum_eq_single (σ j) ?_ ?_).trans ?_
  · intro b _ hb
    exact mul_eq_zero_of_left (permMat_eq_zero (Ne.symm hb)) _
  · intro h; exact absurd (Finset.mem_univ _) h
  · rw [permMat_eq_one rfl, one_mul]

/-! ## Continuity of the chart and of the induced maps -/

theorem continuous_chart (n : ℕ) : Continuous (chart n) := by
  refine continuous_pi fun j => ?_
  refine Fin.lastCases ?_ ?_ j
  · have h : (fun v : Fin n → ℝ => chart n v (Fin.last n)) = fun v => 1 - ∑ i, v i := by
      funext v; exact chart_last v
    rw [h]
    exact continuous_const.sub (continuous_finsetSum _ fun i _ => continuous_apply i)
  · intro i
    have h : (fun v : Fin n → ℝ => chart n v i.castSucc) = fun v => v i := by
      funext v; exact chart_castSucc v i
    rw [h]
    exact continuous_apply i

theorem continuous_inducedMap {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Continuous (inducedMap M) := by
  have h : inducedMap M
          = fun v : Fin n → ℝ =>
              AffineVolume.linInducedMapLinear M v + (fun i => M i.castSucc (Fin.last n)) := by
    funext v
    rw [AffineVolume.inducedMap_eq_linInducedMap_add]
    rfl
  rw [h]
  exact (AffineVolume.linInducedMapLinear M).continuous_of_finiteDimensional.add continuous_const

theorem continuous_permCoord {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    Continuous (fun l : Fin (n + 1) → ℝ => fun i => l (σ i)) :=
  continuous_pi fun i => continuous_apply (σ i)

/-! ## `inducedMap (permMat σ)` maps the open region onto itself -/

theorem inducedMap_permMat_image_region {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    inducedMap (permMat σ) '' region n = region n := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact AffineVolume.inducedMap_mem_region (permMat_nonneg σ) (permMat_col_sum σ)
      (permMat_det_ne_zero σ) hv
  · intro y hy
    exact ⟨inducedMap (permMat σ.symm) y,
      AffineVolume.inducedMap_mem_region (permMat_nonneg σ.symm) (permMat_col_sum σ.symm)
        (permMat_det_ne_zero σ.symm) hy,
      inducedMap_permMat_comp σ y⟩

/-! ## `inducedMap (permMat σ)` preserves `volume.restrict (region n)` -/

theorem map_restrict_permMat {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    (volume.restrict (region n)).map (inducedMap (permMat σ)) = volume.restrict (region n) := by
  have hmeas : Measurable (inducedMap (permMat σ)) := (continuous_inducedMap _).measurable
  have himage := inducedMap_permMat_image_region σ
  -- `inducedMap (permMat σ)` does not change the volume of any set
  have hcov (S : Set (Fin n → ℝ)) : volume (inducedMap (permMat σ) '' S) = volume S := by
    rw [AffineVolume.volume_image_inducedMap_of_det
      (M := permMat σ) (det_linInducedMap (permMat_col_sum σ)) S, permMat_abs_det σ,
      ENNReal.ofReal_one, one_mul]
  ext B hB
  rw [Measure.map_apply hmeas hB, Measure.restrict_apply hB,
    Measure.restrict_apply (hmeas hB)]
  have hset : inducedMap (permMat σ) ''
      (inducedMap (permMat σ) ⁻¹' B ∩ region n) = B ∩ region n := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxB, hxreg⟩, rfl⟩
      exact ⟨hxB, himage ▸ Set.mem_image_of_mem _ hxreg⟩
    · rintro ⟨hyB, hyreg⟩
      rw [← himage] at hyreg
      obtain ⟨x, hxreg, hxQ⟩ := hyreg
      exact ⟨x, ⟨by rw [Set.mem_preimage, hxQ]; exact hyB, hxreg⟩, hxQ⟩
  rw [← hcov (inducedMap (permMat σ) ⁻¹' B ∩ region n), hset]

/-! ## The target: permutation invariance of the chart volume -/

/-- **Permutation invariance of the volume**: the chart volume
`(volume.restrict (region n)).map (chart n)` is invariant under `l ↦ l ∘ σ`.

The proof goes through the change of variables of `AffineVolume` for the permutation matrix of `σ`.
-/
theorem chartVolume_map_perm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    ((volume.restrict (region n)).map (chart n)).map (fun l i => l (σ i))
      = (volume.restrict (region n)).map (chart n) := by
  have hperm : Measurable (fun l : Fin (n + 1) → ℝ => fun i => l (σ i)) :=
    (continuous_permCoord σ).measurable
  have hchart : Measurable (chart n) := (continuous_chart n).measurable
  have hQ : Measurable (inducedMap (permMat σ)) := (continuous_inducedMap _).measurable
  have hcomp : (fun l : Fin (n + 1) → ℝ => fun i => l (σ i)) ∘ chart n
      = chart n ∘ inducedMap (permMat σ) := by
    funext v
    exact (chart_inducedMap_permMat σ v).symm
  rw [Measure.map_map hperm hchart, hcomp, ← Measure.map_map hchart hQ, map_restrict_permMat σ]

/-! ## The bridge to the copied `simplexVolume`  `simplexRegion (n+1) = region n` is
**definitional**, and on the region `simplexMap (n+1)` coincides with `chart n` after the `ℝ≥0 →
ℝ` coercion. -/

/-! ## The pointwise identity of the two charts -/

/-- **The two charts agree.**  On the open region, the coordinates of the copied `simplexMap` are
the coordinates of `chart`: the first `n` are the free coordinates, the last is `1 - ∑`. -/
theorem coe_simplexMap_eq_chart {n : ℕ} {v : Fin n → ℝ} (hv : v ∈ region n) (i : Fin (n + 1)) :
    ((simplexMap (n + 1) v i : ℝ≥0) : ℝ) = chart n v i := by
  refine Fin.lastCases ?_ ?_ i
  · rw [simplexMap_last, chart_last]
    exact Real.coe_toNNReal _ (by linarith [hv.2])
  · intro j
    rw [simplexMap_castSucc, chart_castSucc]
    exact Real.coe_toNNReal _ (le_of_lt (hv.1 j))

/-- The same, as an equality of functions. -/
theorem coe_simplexMap_fun_eq_chart {n : ℕ} {v : Fin n → ℝ} (hv : v ∈ region n) :
    (fun i => ((simplexMap (n + 1) v i : ℝ≥0) : ℝ)) = chart n v :=
  funext fun i => coe_simplexMap_eq_chart hv i

/-! ## Measurability of the coordinatewise coercion `ℝ≥0 → ℝ` -/

/-- The coercion of a length vector to a real vector is measurable. -/
theorem measurable_coe_lengths (n : ℕ) :
    Measurable (fun l : Fin (n + 1) → ℝ≥0 => fun i => (l i : ℝ)) := by
  refine measurable_pi_iff.mpr fun i => ?_
  exact measurable_subtype_coe.comp (measurable_pi_apply i)

/-! ## The bridge -/

/-- **The bridge.**  The copied `simplexVolume (n + 1)`, transported to real vectors, is the volume
of the open region of the chart pushed forward by `chart n`. -/
theorem simplexVolume_eq_chartVolume (n : ℕ) :
    (simplexVolume (n + 1)).map (fun l : Fin (n + 1) → ℝ≥0 => fun i => (l i : ℝ))
      = (volume.restrict (region n)).map (chart n) := by
  rw [simplexVolume, Measure.map_map (measurable_coe_lengths n) (measurable_simplexMap (n + 1))]
  refine Measure.map_congr ?_
  filter_upwards [ae_restrict_mem (measurableSet_region n)] with v hv
  exact coe_simplexMap_fun_eq_chart hv

/-! ## Permutation invariance of `simplexVolume`  The coordinatewise coercion ι : (Fin m → ℝ≥0) →
(Fin m → ℝ) has left inverse c x = fun i => (x i).toNNReal, so simplexVolume (n+1) is the image
under c of the chart volume; the permutation acts on both sides compatibly, and chartVolume_map_perm
gives the invariance. For d = 0 the space is a point. -/

theorem measurable_coord_toNNReal (m : ℕ) :
    Measurable (fun x : Fin m → ℝ => fun i => (x i).toNNReal) := by
  refine measurable_pi_iff.mpr fun i => ?_
  exact continuous_real_toNNReal.measurable.comp (measurable_pi_apply i)

/-- `Real.toNNReal` is a left inverse of the coercion, coordinatewise: `c ∘ ι = id`. -/
theorem toNNReal_comp_coe (m : ℕ) :
    (fun x : Fin m → ℝ => fun i => (x i).toNNReal) ∘
      (fun l : Fin m → ℝ≥0 => fun i => (l i : ℝ)) = id := by
  funext l i
  simp

/-! ## Reading the bridge `simplexVolume_eq_chartVolume` backwards -/

/-- **The chart form of the simplex measure.**  `simplexVolume (n + 1)` is the chart volume of the
open region pushed forward by the coordinatewise coercion `ℝ → ℝ≥0`.  This is
`simplexVolume_eq_chartVolume n` with the coercion inserted, which changes nothing because
`Real.toNNReal` is a left inverse of the coercion. -/
theorem simplexVolume_succ_eq_map_toNNReal (n : ℕ) :
    simplexVolume (n + 1)
      = ((volume.restrict (region n)).map (chart n)).map
          (fun x : Fin (n + 1) → ℝ => fun i => (x i).toNNReal) := by
  have h1 : (((simplexVolume (n + 1)).map
        (fun l : Fin (n + 1) → ℝ≥0 => fun i => (l i : ℝ)))).map
        (fun x : Fin (n + 1) → ℝ => fun i => (x i).toNNReal) = simplexVolume (n + 1) := by
    rw [Measure.map_map (measurable_coord_toNNReal (n + 1)) (measurable_coe_lengths n),
      toNNReal_comp_coe, Measure.map_id]
  rw [← h1, simplexVolume_eq_chartVolume n]

/-! ## Permutation invariance of the simplex measure -/

/-- **Permutation invariance.**  Reindexing a length vector by a permutation of `Fin d` does not
change the simplex measure. -/
theorem simplexVolume_map_perm {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    (simplexVolume d).map (fun l i => l (σ i)) = simplexVolume d := by
  cases d with
  | zero =>
    -- `Fin 0 → ℝ≥0` is a one-point space: the reindexing is the identity.
    have h : (fun l : Fin 0 → ℝ≥0 => fun i => l (σ i)) = id := by
      funext l i
      exact Fin.elim0 i
    rw [h, Measure.map_id]
  | succ n =>
    rw [simplexVolume_succ_eq_map_toNNReal n]
    have hπ : Measurable (fun l : Fin (n + 1) → ℝ≥0 => fun i => l (σ i)) := by
      refine measurable_pi_iff.mpr fun i => measurable_pi_apply (σ i)
    have hπℝ : Measurable (fun x : Fin (n + 1) → ℝ => fun i => x (σ i)) := by
      refine measurable_pi_iff.mpr fun i => measurable_pi_apply (σ i)
    -- `π ∘ c = c ∘ πℝ`
    have hcomp : (fun l : Fin (n + 1) → ℝ≥0 => fun i => l (σ i)) ∘
        (fun x : Fin (n + 1) → ℝ => fun i => (x i).toNNReal)
        = (fun x : Fin (n + 1) → ℝ => fun i => (x i).toNNReal) ∘
          (fun x : Fin (n + 1) → ℝ => fun i => x (σ i)) := by
      funext x i
      simp
    rw [Measure.map_map hπ (measurable_coord_toNNReal (n + 1)), hcomp,
      ← Measure.map_map (measurable_coord_toNNReal (n + 1)) hπℝ,
      chartVolume_map_perm σ, ← simplexVolume_succ_eq_map_toNNReal n]

/-- The theorem above, restated in the abstract shape in which it is applied. -/
theorem map_reindex_eq {α : Type*} {n : ℕ} (ν : Measure (Fin n → ℝ≥0))
    (hν : ∀ τ : Equiv.Perm (Fin n), ν.map (fun l i => l (τ i)) = ν)
    (e₁ e₂ : α ≃ Fin n) :
    ν.map (fun l a => l (e₁ a)) = ν.map (fun l a => l (e₂ a)) := by
  set τ : Equiv.Perm (Fin n) := e₂.symm.trans e₁ with hτ
  have hτa (a : α) : τ (e₂ a) = e₁ a := by
    rw [hτ, Equiv.trans_apply, Equiv.symm_apply_apply]
  have hmeas₂ : Measurable (fun l : Fin n → ℝ≥0 => fun a => l (e₂ a)) := by
    refine measurable_pi_iff.mpr fun a => measurable_pi_apply (e₂ a)
  have hmeasτ : Measurable (fun l : Fin n → ℝ≥0 => fun i => l (τ i)) := by
    refine measurable_pi_iff.mpr fun i => measurable_pi_apply (τ i)
  have hcomp : (fun l : Fin n → ℝ≥0 => fun a => l (e₁ a))
      = (fun l : Fin n → ℝ≥0 => fun a => l (e₂ a)) ∘
        (fun l : Fin n → ℝ≥0 => fun i => l (τ i)) := by
    funext l a
    exact congrArg (fun j => l j) (hτa a).symm
  rw [hcomp, ← Measure.map_map hmeas₂ hmeasτ, hν τ]

/-! ## Independence of the labelling -/

/-- **Independence of the labelling.**  `simplexVolumeOn α` is the reindexing of `simplexVolume n`
along `piBottom`; in particular it does not depend on the combinatorial data. -/
theorem simplexVolumeOn_eq_map {α : Type*} [Fintype α] {n : ℕ} (P : IETDatum₂ α n) :
    simplexVolumeOn α = (simplexVolume n).map (fun l a => l (P.piBottom a)) := by
  have hcard : n = Fintype.card α :=
    ((Fintype.card_congr P.piBottom).trans (Fintype.card_fin n)).symm
  subst hcard
  exact map_reindex_eq (simplexVolume (Fintype.card α))
    (fun τ => simplexVolume_map_perm τ) (Fintype.equivFin α) P.piBottom

/-- On `Fin n`, the alphabet-indexed simplex measure is the copied `simplexVolume n`. -/
theorem simplexVolumeOn_fin (n : ℕ) : simplexVolumeOn (Fin n) = simplexVolume n := by
  have h := simplexVolumeOn_eq_map (P := IETDatum₂.ofPerm (Equiv.refl (Fin n)))
  simpa using h

end
