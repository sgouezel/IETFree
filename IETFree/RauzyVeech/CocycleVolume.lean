/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.Affine
public import IETFree.RauzyVeech.Path

/-!
# The volume of a path cylinder

Lemma 1 of Yoccoz (p. 16): for a finite path `γ` of the Rauzy–Veech algorithm with
matrix `Q = Path.Q P γ`, the volume of the path cylinder `Δ(γ) = cone Q ∩ Δ` is
`(∏_β Q_β)⁻¹` times the volume of the simplex.

The proof goes through the set identity `Δ(γ) = M • Δ°` with `M = Q diag(Q_β)⁻¹`, whose column sums
are `1`, followed by the change of variables `volume_image_inducedMap_of_det` and the
determinant computation `det M = det Q / ∏ Q_β = (∏ Q_β)⁻¹` (all `Path.Q` are unimodular). -/

@[expose] public section

open MeasureTheory Matrix
open scoped BigOperators ENNReal NNReal

/-! ## 1. `Path.Q` is unimodular, with positive column sums  `rvMat P ε` is `1 + single
(last ε) (last (!ε)) 1`, i.e. `1` when the two last letters coincide and an elementary transvection
otherwise.  Hence its column sums are `≥ 1` and its determinant is `1`; both properties are
preserved by products along a path.  (Nonnegativity of `rvMat` and of `Path.Q` is
`IETDatum₂.rvMat_nonneg` in `RauzyVeech/Step.lean` and `Path.Q_nonneg` in
`RauzyVeech/Path.lean`.) -/

namespace IntervalExchange

namespace IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

end IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- `rvMat` is `1` when the two last letters coincide. -/
theorem rvMat_eq_one_of_last_eq (P : IETDatum₂ α n) (ε : Bool) (h : P.last ε = P.last (!ε)) :
    P.rvMat ε = 1 := by
  ext a b
  rw [rvMat, Matrix.one_apply]
  by_cases hab : a = b
  · rw [ite_eq_left hab, ite_eq_left hab]
  · have hP : ¬ (a = P.last ε ∧ b = P.last (!ε)) := by
      rintro ⟨h1, h2⟩
      exact hab (h1.trans (h.trans h2.symm))
    rw [ite_eq_right hab, ite_eq_right hP, ite_eq_right hab]

/-- `rvMat` is the elementary transvection `1 + single (last ε) (last (!ε)) 1` when the two last
letters differ. -/
theorem rvMat_eq_one_add_single (P : IETDatum₂ α n) (ε : Bool) (h : P.last ε ≠ P.last (!ε)) :
    P.rvMat ε = 1 + Matrix.single (P.last ε) (P.last (!ε)) (1 : ℤ) := by
  ext a b
  rw [rvMat, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    have hP : ¬ (P.last ε = a ∧ P.last (!ε) = a) := fun ⟨h1, h2⟩ => h (h1.trans h2.symm)
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right hP, add_zero]
  · rw [ite_eq_right hab, ite_eq_right hab]
    by_cases hP : (a = P.last ε ∧ b = P.last (!ε))
    · have hQ : (P.last ε = a ∧ P.last (!ε) = b) := ⟨hP.1.symm, hP.2.symm⟩
      rw [ite_eq_left hP, ite_eq_left hQ, zero_add]
    · have hQ : ¬ (P.last ε = a ∧ P.last (!ε) = b) :=
        fun ⟨h1, h2⟩ => hP ⟨h1.symm, h2.symm⟩
      rw [ite_eq_right hP, ite_eq_right hQ, zero_add]

theorem det_rvMat (P : IETDatum₂ α n) (ε : Bool) : (P.rvMat ε).det = 1 := by
  by_cases h : P.last ε = P.last (!ε)
  · rw [rvMat_eq_one_of_last_eq P ε h, Matrix.det_one]
  · rw [rvMat_eq_one_add_single P ε h]
    exact det_one_add_single_of_ne _ _ h 1

/-- **The renormalisation matrix is unimodular**: `det Q(γ) = 1`. -/
theorem Path.Q_det (P : IETDatum₂ α n) (γ : List Bool) : (Path.Q P γ).det = 1 := by
  induction γ generalizing P with
  | nil => simp
  | cons e es ih =>
    rw [Path.Q_cons, Matrix.det_mul, det_rvMat, ih, one_mul]

end IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

theorem rvMat_colsum_ge (P : IETDatum₂ α n) (ε : Bool) (b : α) :
    1 ≤ ∑ a, P.rvMat ε a b := by
  by_cases h : P.last ε = P.last (!ε)
  · rw [rvMat_eq_one_of_last_eq P ε h, colsum_one]
  · rw [rvMat_eq_one_add_single P ε h]
    have h1 : (∑ a, (1 + Matrix.single (P.last ε) (P.last (!ε)) (1 : ℤ) : Matrix α α ℤ) a b)
        = 1 + ∑ a, Matrix.single (P.last ε) (P.last (!ε)) (1 : ℤ) a b := by
      simp only [Matrix.add_apply, Finset.sum_add_distrib, colsum_one]
    rw [h1]
    have h2 : 0 ≤ ∑ a, Matrix.single (P.last ε) (P.last (!ε)) (1 : ℤ) a b :=
      Finset.sum_nonneg fun a _ => by
        rw [Matrix.single_apply]; split <;> norm_num
    linarith

theorem Path.Q_colsum_pos (P : IETDatum₂ α n) (γ : List Bool) (b : α) :
    0 < ∑ a, Path.Q P γ a b := by
  induction γ generalizing P with
  | nil => rw [Path.Q_nil, colsum_one]; norm_num
  | cons e es ih =>
    rw [Path.Q_cons]
    have hstep : (∑ a, (P.rvMat e * Path.Q (P.rvStep e) es) a b)
        = ∑ k, (∑ a, P.rvMat e a k) * Path.Q (P.rvStep e) es k b := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [hstep]
    obtain ⟨k, hk⟩ : ∃ k, 0 < Path.Q (P.rvStep e) es k b := by
      by_contra hc
      push Not at hc
      have hpos := ih (P.rvStep e)
      have hzero : ∑ k, Path.Q (P.rvStep e) es k b ≤ 0 := Finset.sum_nonpos fun k _ => hc k
      linarith
    refine Finset.sum_pos' (fun k _ => ?_) ⟨k, Finset.mem_univ _, ?_⟩
    · exact mul_nonneg (Finset.sum_nonneg fun a _ => rvMat_nonneg P e a k)
        (Path.Q_nonneg (P.rvStep e) es k b)
    · exact mul_pos (by linarith [rvMat_colsum_ge P e k]) hk

end IETDatum₂

end IntervalExchange

namespace IntervalExchange.RauzyVeech

/-! ## 2. The open real simplex, the chart, and the matrix `M = Q diag(Q_β)⁻¹`  Everything from now
on is stated for a matrix `N : Matrix (Fin (m+1)) (Fin (m+1)) ℤ` with `det N = 1`, nonnegative
entries and positive column sums; `Path.Q P γ` satisfies these (Section 1). The matrix `M = N ·
diag(N_β)⁻¹ ∈ M_{m+1}(ℝ)` has column sums `1` and `det M = (∏ N_β)⁻¹`, and its action on the open
simplex is the path cylinder. -/

section FinVersion

variable {m : ℕ}

/-- The open real simplex, in `Fin (m+1)` coordinates. -/
def openRealSimplex (m : ℕ) : Set (Fin (m+1) → ℝ) := {x | (∀ i, 0 < x i) ∧ ∑ i, x i = 1}

/-- **The chart parametrises the open real simplex.** -/
theorem chart_image_region (m : ℕ) : chart m '' region m = openRealSimplex m := by
  have key (x : Fin (m+1) → ℝ) : (∀ i, 0 < x i) → ∑ i, x i = 1 →
      ∑ i : Fin m, x i.castSucc = 1 - x (Fin.last m) := by
    intro _ hsum
    rw [Fin.sum_univ_castSucc] at hsum
    linarith
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨chart_pos hv, chart_sum v⟩
  · rintro ⟨hx, hsum⟩
    have hsplit := key x hx hsum
    have hlast : (0:ℝ) < x (Fin.last m) := hx _
    refine ⟨fun i => x i.castSucc, ⟨fun i => hx _, by rw [hsplit]; linarith⟩, ?_⟩
    funext j
    refine Fin.lastCases ?_ ?_ j
    · rw [chart_last, hsplit]; ring
    · intro i; rw [chart_castSucc]

/-- The coordinatewise coercion `ℝ≥0 → ℝ`, as a function. -/
abbrev lengthsToReal (m : ℕ) : (Fin (m+1) → ℝ≥0) → (Fin (m+1) → ℝ) := fun l i => (l i : ℝ)

theorem range_lengthsToReal (m : ℕ) :
    Set.range (lengthsToReal m) = {x : Fin (m+1) → ℝ | ∀ i, 0 ≤ x i} := by
  ext x
  constructor
  · rintro ⟨l, rfl⟩ i; exact (l i).2
  · intro hx
    exact ⟨fun i => ⟨x i, hx i⟩, by funext i; rfl⟩

theorem measurableSet_range_lengthsToReal (m : ℕ) :
    MeasurableSet (Set.range (lengthsToReal m)) := by
  have h : {x : Fin (m+1) → ℝ | ∀ i, 0 ≤ x i} = ⋂ i, {x : Fin (m+1) → ℝ | 0 ≤ x i} := by
    ext x; simp
  rw [range_lengthsToReal, h]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le (measurable_const (a := (0:ℝ))) (continuous_apply i).measurable

/-- **The real matrix `M = N diag(N_β)⁻¹`**, whose column sums are `1` and whose determinant is
`(∏ N_β)⁻¹` when `det N = 1`. -/
noncomputable def rvRealMat (N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) :
    Matrix (Fin (m+1)) (Fin (m+1)) ℝ :=
  N.map (fun x : ℤ => (x : ℝ)) * Matrix.diagonal (fun b => (((∑ i, N i b : ℤ)) : ℝ)⁻¹)

theorem rvRealMat_apply (N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (a b : Fin (m + 1)) :
    rvRealMat N a b = (N a b : ℝ) * (((∑ i, N i b : ℤ)) : ℝ)⁻¹ := by
  rw [rvRealMat, Matrix.mul_diagonal, Matrix.map_apply]

theorem rvRealMat_colsum (N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (hpos : ∀ b, 0 < ∑ i, N i b) (b : Fin (m + 1)) : ∑ a, rvRealMat N a b = 1 := by
  have hC : (((∑ i, N i b : ℤ)) : ℝ) ≠ 0 := by
    have := hpos b
    exact_mod_cast (ne_of_gt this)
  have hsum : (∑ a, (N a b : ℝ)) = (((∑ a, N a b : ℤ)) : ℝ) := by push_cast; rfl
  simp only [rvRealMat_apply, ← Finset.sum_mul, hsum, mul_inv_cancel₀ hC]

theorem rvRealMat_det (N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (hdet : N.det = 1) :
    (rvRealMat N).det = ∏ b, (((∑ i, N i b : ℤ)) : ℝ)⁻¹ := by
  rw [rvRealMat, Matrix.det_mul, Matrix.det_diagonal, ← Int.cast_det, hdet, Int.cast_one, one_mul]

theorem rvRealMat_nonneg (N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (hnn : ∀ a b, 0 ≤ N a b) (hpos : ∀ b, 0 < ∑ i, N i b) (a b : Fin (m + 1)) :
    0 ≤ rvRealMat N a b := by
  rw [rvRealMat_apply]
  have hC : (0:ℝ) < (((∑ i, N i b : ℤ)) : ℝ) := by exact_mod_cast hpos b
  exact mul_nonneg (by exact_mod_cast hnn a b) (le_of_lt (inv_pos.mpr hC))

/-- Pointwise form of `M = N diag(N_β)⁻¹` acting on a vector. -/
theorem rvRealMat_mulVec_apply (N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (z : Fin (m + 1) → ℝ)
    (a : Fin (m + 1)) :
    (rvRealMat N *ᵥ z) a = ∑ b, (N a b : ℝ) * ((((∑ i, N i b : ℤ)) : ℝ)⁻¹ * z b) := by
  simp only [Matrix.mulVec_apply, Matrix.row, dotProduct, rvRealMat_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **The path cylinder is the image of the open simplex under `M = Q diag(Q_β)⁻¹`.**  `cone N ∩ {∑
= 1} = M • Δ°`:  the substitution `z_β = Q_β y_β` converts `x = Q y`, `y > 0`, `∑_β Q_β y_β = 1`
into `x = M z`, `z > 0`, `∑_β z_β = 1`. -/
theorem cone_inter_eq (N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (hpos : ∀ b, 0 < ∑ i, N i b) :
    {x : Fin (m+1) → ℝ | x ∈ cone N ∧ ∑ i, x i = 1}
      = (fun z => rvRealMat N *ᵥ z) '' openRealSimplex m := by
  have hC (b) : (0:ℝ) < (((∑ i, N i b : ℤ)) : ℝ) := by exact_mod_cast hpos b
  have hCne (b) : (((∑ i, N i b : ℤ)) : ℝ) ≠ 0 := ne_of_gt (hC b)
  ext x
  constructor
  · rintro ⟨⟨y, hy, hxy⟩, hsum⟩
    subst hxy
    refine ⟨fun b => (((∑ i, N i b : ℤ)) : ℝ) * y b, ⟨fun b => mul_pos (hC b) (hy b), ?_⟩, ?_⟩
    · have hterm (b) : (((∑ i, N i b : ℤ)) : ℝ) * y b = ∑ a, (N a b : ℝ) * y b := by
        rw [← Finset.sum_mul, ← Int.cast_sum]
      simp only [hterm]
      rw [Finset.sum_comm]
      exact hsum
    · funext a
      dsimp only
      rw [rvRealMat_mulVec_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [inv_mul_cancel_left₀ (hCne b)]
  · rintro ⟨z, ⟨hz, hzsum⟩, rfl⟩
    refine ⟨⟨fun b => (((∑ i, N i b : ℤ)) : ℝ)⁻¹ * z b,
      fun b => mul_pos (inv_pos.mpr (hC b)) (hz b), ?_⟩, ?_⟩
    · funext a
      dsimp only
      rw [rvRealMat_mulVec_apply]
    · simp only [rvRealMat_mulVec_apply]
      rw [Finset.sum_comm]
      have hterm (b) : ∑ a, (N a b : ℝ) * ((((∑ i, N i b : ℤ)) : ℝ)⁻¹ * z b) = z b := by
        have hCX : (∑ a, (N a b : ℝ)) = (((∑ i, N i b : ℤ)) : ℝ) := by push_cast; rfl
        rw [← Finset.sum_mul, hCX, ← mul_assoc, mul_inv_cancel₀ (hCne b), one_mul]
      simp only [hterm, hzsum]

/-- `M *ᵥ chart v = chart (inducedMap M v)` for a matrix with column sums `1`. -/
theorem mulVec_chart {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hcol : ∀ j, ∑ i, M i j = 1)
    (v : Fin m → ℝ) : M *ᵥ chart m v = chart m (inducedMap M v) := by
  rw [chart_inducedMap hcol v]
  funext j
  simp only [Matrix.mulVec_apply, Matrix.row, dotProduct]

/-- **In the chart, `M •` is `inducedMap M`**:  the image of the open simplex under `M` is the chart
image of the image of the region under `inducedMap M`. -/
theorem image_openRealSimplex_eq (N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (hpos : ∀ b, 0 < ∑ i, N i b) (hnn : ∀ a b, 0 ≤ N a b) (hdet : N.det = 1) :
    (fun z => rvRealMat N *ᵥ z) '' openRealSimplex m
      = chart m '' (inducedMap (rvRealMat N) '' region m) := by
  set M := rvRealMat N with hM
  have hcol (j) : ∑ i, M i j = 1 := rvRealMat_colsum N hpos j
  have hdetne : M.det ≠ 0 := by
    rw [hM, rvRealMat_det N hdet]
    refine Finset.prod_ne_zero_iff.mpr fun b _ => ?_
    have hb (b) : (0:ℝ) < (((∑ i, N i b : ℤ)) : ℝ) := by exact_mod_cast hpos b
    exact inv_ne_zero (ne_of_gt (hb b))
  have hM0 (i j) : 0 ≤ M i j := rvRealMat_nonneg N hnn hpos i j
  have hmem (v) (hv : v ∈ region m) : inducedMap M v ∈ region m :=
      inducedMap_mem_region hM0 hcol hdetne hv
  have hchartv (v : Fin m → ℝ) : M *ᵥ chart m v = chart m (inducedMap M v) :=
    mulVec_chart hcol v
  rw [← chart_image_region]
  ext x
  constructor
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨v, hvreg, hzv⟩ := hz
    subst hzv
    rw [← hzx]
    exact ⟨inducedMap M v, ⟨v, hvreg, rfl⟩, (hchartv v).symm⟩
  · rintro ⟨w, ⟨v, hvreg, rfl⟩, rfl⟩
    exact ⟨chart m v, ⟨v, hvreg, rfl⟩, hchartv v⟩

theorem colsum_one_real (b : Fin (m + 1)) :
    (∑ a : Fin (m+1), (1 : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) a b) = 1 := by
  rw [Finset.sum_eq_single b]
  · rw [Matrix.one_apply, ite_eq_left rfl]
  · intro a _ ha; rw [Matrix.one_apply, ite_eq_right ha]
  · intro h; exact absurd (Finset.mem_univ b) h

/-- The column sums of the inverse of a stochastic invertible matrix are `1`. -/
theorem inv_colsum {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hcol : ∀ j, ∑ i, M i j = 1)
    (hdet : M.det ≠ 0) (j : Fin (m + 1)) : ∑ i, M⁻¹ i j = 1 := by
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hmul : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hunit
  have key : (∑ i', (M * M⁻¹) i' j) = ∑ i, M⁻¹ i j := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hcol i, one_mul]
  rw [← key, hmul]
  exact colsum_one_real j

/-- `inducedMap (M⁻¹)` is a left and right inverse of `inducedMap M`. -/
theorem inducedMap_inv_left {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hcol : ∀ j, ∑ i, M i j = 1)
    (hdet : M.det ≠ 0) (v : Fin m → ℝ) : inducedMap M⁻¹ (inducedMap M v) = v := by
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hmul : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunit
  refine chart_injective ?_
  rw [← mulVec_chart (inv_colsum hcol hdet) (inducedMap M v), ← mulVec_chart hcol v,
    Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]

theorem inducedMap_inv_right {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hcol : ∀ j, ∑ i, M i j = 1)
    (hdet : M.det ≠ 0) (v : Fin m → ℝ) : inducedMap M (inducedMap M⁻¹ v) = v := by
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hmul : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hunit
  refine chart_injective ?_
  rw [← mulVec_chart hcol (inducedMap M⁻¹ v), ← mulVec_chart (inv_colsum hcol hdet) v,
    Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]

/-- The image of the region under `inducedMap M` is the preimage under `inducedMap (M⁻¹)`: in
particular it is measurable. -/
theorem inducedMap_image_region_eq {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hcol : ∀ j, ∑ i, M i j = 1) (hdet : M.det ≠ 0) :
    inducedMap M '' region m = (inducedMap M⁻¹) ⁻¹' region m := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [Set.mem_preimage, inducedMap_inv_left hcol hdet]
    exact hv
  · intro hx
    exact ⟨inducedMap M⁻¹ x, hx, inducedMap_inv_right hcol hdet x⟩

/-- The chart image of a subset of the region, described in `Δ°`. -/
theorem chart_image_of_subset {W : Set (Fin m → ℝ)} (hW : W ⊆ region m) :
    chart m '' W
      = {x : Fin (m+1) → ℝ | x ∈ openRealSimplex m ∧ (fun i : Fin m => x i.castSucc) ∈ W} := by
  have key (x : Fin (m+1) → ℝ) : (∀ i, 0 < x i) → ∑ i, x i = 1 →
      ∑ i : Fin m, x i.castSucc = 1 - x (Fin.last m) := by
    intro _ hsum
    rw [Fin.sum_univ_castSucc] at hsum
    linarith
  ext x
  constructor
  · rintro ⟨v, hvW, rfl⟩
    refine ⟨⟨chart_pos (hW hvW), chart_sum v⟩, ?_⟩
    rw [funext fun i => chart_castSucc v i]
    exact hvW
  · rintro ⟨⟨hx, hsum⟩, hxW⟩
    have hsplit := key x hx hsum
    have hlast : (0:ℝ) < x (Fin.last m) := hx _
    refine ⟨fun i => x i.castSucc, hxW, ?_⟩
    funext j
    refine Fin.lastCases ?_ ?_ j
    · rw [chart_last, hsplit]; ring
    · intro i; rw [chart_castSucc]

theorem measurableSet_openRealSimplex (m : ℕ) : MeasurableSet (openRealSimplex m) := by
  have h1 : MeasurableSet {x : Fin (m+1) → ℝ | ∀ i, 0 < x i} := by
    simpa only [Set.ofPred_forall] using
      MeasurableSet.iInter (fun i : Fin (m+1) =>
        measurableSet_lt (measurable_const (a := (0:ℝ))) (continuous_apply i).measurable)
  have h2 : MeasurableSet {x : Fin (m+1) → ℝ | ∑ i, x i = 1} :=
    measurableSet_eq_fun (Finset.measurable_sum _ fun i (_ : i ∈ Finset.univ) =>
      (continuous_apply i).measurable) measurable_const
  exact h1.inter h2

/-- **Measurability of the path cylinder `M • Δ°`.** -/
theorem measurableSet_image_openRealSimplex (N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (hpos : ∀ b, 0 < ∑ i, N i b) (hnn : ∀ a b, 0 ≤ N a b) (hdet : N.det = 1) :
    MeasurableSet ((fun z => rvRealMat N *ᵥ z) '' openRealSimplex m) := by
  set M := rvRealMat N with hM
  have hcol (j) : ∑ i, M i j = 1 := rvRealMat_colsum N hpos j
  have hdetne : M.det ≠ 0 := by
    rw [hM, rvRealMat_det N hdet]
    refine Finset.prod_ne_zero_iff.mpr fun b _ => ?_
    have hb : (0:ℝ) < (((∑ i, N i b : ℤ)) : ℝ) := by exact_mod_cast hpos b
    exact inv_ne_zero (ne_of_gt hb)
  have hM0 (i j) : 0 ≤ M i j := rvRealMat_nonneg N hnn hpos i j
  have hsub : inducedMap M '' region m ⊆ region m := by
    rintro x ⟨v, hv, rfl⟩
    exact inducedMap_mem_region hM0 hcol hdetne hv
  have hW : MeasurableSet (inducedMap M '' region m) := by
    rw [inducedMap_image_region_eq hcol hdetne]
    exact (continuous_inducedMap M⁻¹).measurable (measurableSet_region m)
  rw [image_openRealSimplex_eq N hpos hnn hdet, chart_image_of_subset hsub]
  exact measurableSet_openRealSimplex m |>.inter
    (hW.preimage (continuous_pi fun i => continuous_apply i.castSucc).measurable)

/-- The coefficientwise coercion commutes with the total mass. -/
theorem lengthsToReal_preimage_simplex (m : ℕ) :
    lengthsToReal m ⁻¹' {x : Fin (m+1) → ℝ | ∑ i, x i = 1} = simplex (Fin (m+1)) := by
  ext l
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, mem_simplex, lengthsToReal]
  constructor
  · intro h
    refine NNReal.coe_injective ?_
    simpa [NNReal.coe_sum] using h
  · intro h
    have h' := congrArg (fun r : ℝ≥0 => (r : ℝ)) h
    simpa using h'

/-- **The elementary measure computation**: for a measurable `T`,
`simplexVolume (lengthsToReal ⁻¹' T)` is the Lebesgue measure of the part of the chart region whose
chart image lies in `T ∩ {x ≥ 0}`. -/
theorem simplexVolume_lengthsToReal_preimage (T : Set (Fin (m + 1) → ℝ)) (hT : MeasurableSet T) :
    simplexVolume (m+1) (lengthsToReal m ⁻¹' T)
      = volume (region m ∩ chart m ⁻¹' (T ∩ Set.range (lengthsToReal m))) := by
  have hco : Measurable (lengthsToReal m) :=
    measurable_pi_iff.mpr fun i => measurable_subtype_coe.comp (measurable_pi_apply i)
  have hchart : Measurable (chart m) := (continuous_chart m).measurable
  have hTr : MeasurableSet (T ∩ Set.range (lengthsToReal m)) :=
    hT.inter (measurableSet_range_lengthsToReal m)
  have hpre : lengthsToReal m ⁻¹' (T ∩ Set.range (lengthsToReal m)) = lengthsToReal m ⁻¹' T := by
    rw [Set.preimage_inter, Set.preimage_range, Set.inter_univ]
  rw [← hpre]
  rw [← Measure.map_apply hco hTr,
    simplexVolume_eq_chartVolume m,
    Measure.map_apply hchart hTr,
    Measure.restrict_apply (hchart hTr)]
  rw [Set.inter_comm]

/-- The open simplex has the same measure as the region.  That measure is `1 / m!`, so
`simplexVolume` is a probability only in the smallest case `m = 1`. -/
theorem simplexVolume_simplex (m : ℕ) :
    simplexVolume (m+1) (simplex (Fin (m+1))) = volume (region m) := by
  have hT : MeasurableSet {x : Fin (m+1) → ℝ | ∑ i, x i = 1} :=
    measurableSet_eq_fun (Finset.measurable_sum _ fun i (_ : i ∈ Finset.univ) =>
      (continuous_apply i).measurable) measurable_const
  rw [← lengthsToReal_preimage_simplex m, simplexVolume_lengthsToReal_preimage _ hT]
  have hset : region m ∩ chart m ⁻¹' ({x : Fin (m+1) → ℝ | ∑ i, x i = 1} ∩ Set.range (lengthsToReal
  m))
      = region m := by
    refine Set.Subset.antisymm (Set.inter_subset_left ..) ?_
    intro v hv
    refine ⟨hv, chart_sum v, ?_⟩
    rw [range_lengthsToReal]
    exact fun i => le_of_lt (chart_pos hv i)
  rw [hset]

/-- The column sums of a nonnegative integer matrix, as a nonnegative real. -/
noncomputable def colsumNN {ι : Type*} [Fintype ι] (N : Matrix ι ι ℤ) (b : ι) : ℝ≥0 :=
  Real.toNNReal (((∑ i, N i b : ℤ)) : ℝ)

theorem coe_colsumNN {ι : Type*} [Fintype ι] {N : Matrix ι ι ℤ} {b : ι}
    (h : 0 < ∑ i, N i b) : ((colsumNN N b : ℝ≥0) : ℝ) = ((∑ i, N i b : ℤ) : ℝ) :=
  Real.coe_toNNReal _ (le_of_lt (by exact_mod_cast h))

theorem lengthsToReal_sum_eq_one (l : Fin (m + 1) → ℝ≥0) : (∑ i, l i = 1) ↔ (∑ i, lengthsToReal m l
i = 1) := by
  constructor
  · intro h
    simpa [lengthsToReal, NNReal.coe_sum] using congrArg (fun r : ℝ≥0 => (r : ℝ)) h
  · intro h
    refine NNReal.coe_injective ?_
    simpa [lengthsToReal, NNReal.coe_sum] using h

/-- **Lemma 1 of Yoccoz (volumes)**, for a unimodular nonnegative integer matrix with positive
column sums: the volume of `Δ(γ) = cone N ∩ Δ` is `(∏_β N_β)⁻¹` times the volume of the simplex. -/
theorem volume_cylinder_fin (N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (hdet : N.det = 1) (hpos : ∀ b, 0 < ∑ i, N i b) (hnn : ∀ a b, 0 ≤ N a b) :
    simplexVolume (m+1) {l : Fin (m+1) → ℝ≥0 | lengthsToReal m l ∈ cone N ∧ ∑ i, l i = 1}
      = (∏ b, (colsumNN N b)⁻¹ : ℝ≥0) * simplexVolume (m+1) (simplex (Fin (m+1))) := by
  set M := rvRealMat N with hM
  have hcol (j) : ∑ i, M i j = 1 := rvRealMat_colsum N hpos j
  have hM0 (i j) : 0 ≤ M i j := rvRealMat_nonneg N hnn hpos i j
  have hCpos (b) : (0:ℝ) < (((∑ i, N i b : ℤ)) : ℝ) := by exact_mod_cast hpos b
  have hdetM : M.det = ∏ b, (((∑ i, N i b : ℤ)) : ℝ)⁻¹ := by
    rw [hM]; exact rvRealMat_det N hdet
  have hdetne : M.det ≠ 0 := by
    rw [hdetM]
    exact Finset.prod_ne_zero_iff.mpr fun b _ => inv_ne_zero (ne_of_gt (hCpos b))
  have hcnn (b) : ((colsumNN N b : ℝ≥0) : ℝ) = (((∑ i, N i b : ℤ)) : ℝ) := coe_colsumNN (hpos b)
  -- the set identity: the cylinder is `lengthsToReal ⁻¹' (M • Δ°)`
  have hset : {l : Fin (m+1) → ℝ≥0 | lengthsToReal m l ∈ cone N ∧ ∑ i, l i = 1}
      = lengthsToReal m ⁻¹' ((fun z => M *ᵥ z) '' openRealSimplex m) := by
    ext l
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [lengthsToReal_sum_eq_one l]
    simpa only [Set.mem_ofPred_eq] using
      (Set.ext_iff.mp (cone_inter_eq N hpos) (lengthsToReal m l))
  rw [hset, simplexVolume_lengthsToReal_preimage _ (measurableSet_image_openRealSimplex N hpos hnn
  hdet)]
  -- `M • Δ°` is contained in `{x ≥ 0}`
  have hsub : ((fun z => M *ᵥ z) '' openRealSimplex m) ⊆ Set.range (lengthsToReal m) := by
    rintro x ⟨z, ⟨hz, _⟩, hzx⟩
    rw [← hzx, range_lengthsToReal]
    intro a
    -- after unfolding `range_lengthsToReal`: the form `rw [hM]` applies to
    change 0 ≤ (M *ᵥ z) a
    rw [hM, rvRealMat_mulVec_apply]
    refine Finset.sum_nonneg fun b _ =>
      mul_nonneg (by exact_mod_cast hnn a b) (mul_nonneg ?_ (le_of_lt (hz b)))
    exact le_of_lt (inv_pos.mpr (hCpos b))
  rw [Set.inter_eq_left.mpr hsub]
  -- the chart preimage of `M • Δ°` is `inducedMap M '' region`
  have hchart : region m ∩ chart m ⁻¹' ((fun z => M *ᵥ z) '' openRealSimplex m)
      = inducedMap M '' region m := by
    rw [image_openRealSimplex_eq N hpos hnn hdet, ← hM]
    ext v
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨_, w, hw, hvw⟩
      rw [(chart_injective hvw).symm]
      exact hw
    · intro hv
      obtain ⟨w, hw, rfl⟩ := hv
      exact ⟨inducedMap_mem_region hM0 hcol hdetne hw, inducedMap M w,
        ⟨w, hw, rfl⟩, rfl⟩
  rw [hchart, volume_image_inducedMap_of_det (det_linInducedMap hcol) (region m),
    hdetM,
    simplexVolume_simplex]
  have habs : |∏ b, (((∑ i, N i b : ℤ)) : ℝ)⁻¹| = ((∏ b, (colsumNN N b)⁻¹ : ℝ≥0) : ℝ) := by
    rw [Finset.abs_prod, NNReal.coe_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [abs_of_pos (inv_pos.mpr (hCpos b)), NNReal.coe_inv, hcnn b]
  rw [habs, ENNReal.ofReal_coe_nnreal]

/-- Reindexing length vectors along an equivalence of alphabets, as a measurable equivalence. -/
def piEquivMeas {α : Type*} {m : ℕ} (e : α ≃ Fin (m + 1)) :
    (Fin (m+1) → ℝ≥0) ≃ᵐ (α → ℝ≥0) where
  toFun l a := l (e a)
  invFun x i := x (e.symm i)
  left_inv l := by funext i; simp
  right_inv x := by funext a; simp
  measurable_toFun := measurable_pi_iff.mpr fun a => measurable_pi_apply (e a)
  measurable_invFun := measurable_pi_iff.mpr fun i => measurable_pi_apply (e.symm i)

/-- **Reindexing a cone**: `x = l ∘ e` lies in `cone Q` iff `l` lies in the cone of the reindexed
matrix `Q.submatrix e.symm e.symm`. -/
theorem cone_comp_iff {α : Type*} [Fintype α] {m : ℕ} (Q : Matrix α α ℤ)
    (e : α ≃ Fin (m + 1)) (l : Fin (m + 1) → ℝ) :
    (fun a => l (e a)) ∈ cone Q ↔
      l ∈ cone (Q.submatrix (⇑e.symm) (⇑e.symm)) := by
  constructor
  · rintro ⟨z, hz, hxz⟩
    refine ⟨fun i => z (e.symm i), fun i => hz _, ?_⟩
    funext i
    have h : l i = ∑ b, (Q (e.symm i) b : ℝ) * z b := by
      have h0 := congrFun hxz (e.symm i)
      rwa [Equiv.apply_symm_apply] at h0
    rw [h, ← Equiv.sum_comp e.symm (fun b => (Q (e.symm i) b : ℝ) * z b)]
    simp only [Matrix.submatrix_apply]
  · rintro ⟨w, hw, hxw⟩
    refine ⟨fun b => w (e b), fun b => hw _, ?_⟩
    funext a
    have h : l (e a) = ∑ j, ((Q.submatrix (⇑e.symm) (⇑e.symm)) (e a) j : ℝ) * w j :=
      congrFun hxw (e a)
    rw [h]
    have hstep (j) : ((Q.submatrix (⇑e.symm) (⇑e.symm)) (e a) j : ℝ) * w j
        = ((fun b => (Q a b : ℝ) * w (e b)) (e.symm j)) := by simp
    simp only [hstep]
    exact Equiv.sum_comp e.symm (fun b => (Q a b : ℝ) * w (e b))

/-- **Lemma 1 of Yoccoz (volumes)** for the path cylinder of a finite Rauzy–Veech path:
the volume of `Δ(γ) = cone (Path.Q P γ) ∩ Δ` is `(∏_β Q_β)⁻¹` times the volume of the simplex. -/
theorem volume_simplexCyl {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (γ : List Bool) :
    simplexVolumeOn α (IETDatum₂.simplexCyl P γ)
      = (∏ b, (colsumNN (IETDatum₂.Path.Q P γ) b)⁻¹ : ℝ≥0) * simplexVolumeOn α (simplex α) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
  set Q := IETDatum₂.Path.Q P γ with hQ
  set e : α ≃ Fin (m+1) := P.piBottom with he
  set N : Matrix (Fin (m+1)) (Fin (m+1)) ℤ := Q.submatrix (⇑e.symm) (⇑e.symm) with hN
  set Ψ : (Fin (m+1) → ℝ≥0) ≃ᵐ (α → ℝ≥0) := piEquivMeas e with hΨ
  have hΨl (l : Fin (m+1) → ℝ≥0) : ⇑Ψ l = fun a => l (e a) := (rfl)
  -- properties of `N`
  have hNdet : N.det = 1 := by
    rw [hN, Matrix.det_submatrix_equiv_self, hQ]
    exact IETDatum₂.Path.Q_det P γ
  have hNnn (a) (b) : 0 ≤ N a b := by
    rw [hN, Matrix.submatrix_apply, hQ]
    exact IETDatum₂.Path.Q_nonneg P γ _ _
  have hNcolsum (i) : ∑ j, N j i = ∑ a, Q a (e.symm i) := by
    rw [hN]
    simp only [Matrix.submatrix_apply]
    exact Equiv.sum_comp e.symm (fun b => Q b (e.symm i))
  have hNpos (i) : 0 < ∑ j, N j i := by
    rw [hNcolsum i, hQ]; exact IETDatum₂.Path.Q_colsum_pos P γ _
  -- the set identities
  have hsumΨ (l : Fin (m+1) → ℝ≥0) : (∑ a, (⇑Ψ l) a) = ∑ i, l i := by
    rw [hΨl l]
    exact Equiv.sum_comp e l
  have key : Ψ ⁻¹' (IETDatum₂.simplexCyl P γ)
      = {l : Fin (m+1) → ℝ≥0 | lengthsToReal m l ∈ cone N ∧ ∑ i, l i = 1} := by
    ext l
    have hcone : (fun a => ((⇑Ψ l) a : ℝ)) ∈ cone Q ↔ lengthsToReal m l ∈ cone N
    := by
      have h1 : (fun a => ((⇑Ψ l) a : ℝ)) = fun a => lengthsToReal m l (e a) := by
        simp only [hΨl, lengthsToReal]
      rw [h1, hN]
      exact cone_comp_iff Q e (lengthsToReal m l)
    have hone : (∑ a, (⇑Ψ l) a = 1) ↔ (∑ i, l i = 1) := by rw [hsumΨ l]
    rw [Set.mem_preimage, IETDatum₂.simplexCyl, Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← hQ]
    exact ⟨fun h => ⟨hcone.mp h.1, hone.mp h.2⟩, fun h => ⟨hcone.mpr h.1, hone.mpr h.2⟩⟩
  have key' : Ψ ⁻¹' (simplex α) = simplex (Fin (m+1)) := by
    ext l
    rw [Set.mem_preimage, mem_simplex, mem_simplex]
    rw [hsumΨ l]
  -- the measure transport
  have hcoe_apply (s : Set (α → ℝ≥0)) : simplexVolumeOn α s = simplexVolume (m+1) (Ψ ⁻¹' s) := by
    rw [simplexVolumeOn_eq_map P]
    have heq : (fun l : Fin (m+1) → ℝ≥0 => fun a => l (P.piBottom a)) = ⇑Ψ := by
      funext l; rw [hΨl l, he]
    rw [heq]
    exact MeasurableEmbedding.map_apply Ψ.measurableEmbedding (simplexVolume (m+1)) s
  rw [hcoe_apply, hcoe_apply, key, key', volume_cylinder_fin N hNdet hNpos hNnn]
  congr 1
  have hcolNN (i : Fin (m+1)) : colsumNN N i = colsumNN Q (e.symm i) := by
    rw [colsumNN, colsumNN, hNcolsum i]
  have hprod : (∏ b, (colsumNN N b)⁻¹ : ℝ≥0) = ∏ b, (colsumNN Q b)⁻¹ := by
    refine Fintype.prod_equiv e.symm (fun i => (colsumNN N i)⁻¹) (fun b => (colsumNN Q b)⁻¹) ?_
    intro i
    rw [hcolNN i]
  rw [hprod]

end FinVersion

/-! ## 3. Sanity checks and the degenerate case of a one-letter alphabet -/

section Checks

variable {m : ℕ}

/-- The column sums of `Path.Q` are positive, so the constant `(∏ Q_β)⁻¹` is never `0`. -/
theorem colsumNN_pos {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (γ : List Bool) (b : α) : 0 < colsumNN (IETDatum₂.Path.Q P γ) b := by
  rw [colsumNN, ← NNReal.coe_pos]
  rw [Real.coe_toNNReal _ (le_of_lt (by exact_mod_cast IETDatum₂.Path.Q_colsum_pos P γ b))]
  exact_mod_cast IETDatum₂.Path.Q_colsum_pos P γ b

end Checks

end IntervalExchange.RauzyVeech

end
