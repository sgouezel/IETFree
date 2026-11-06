/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.BoundedSimplex
public import IETFree.RauzyVeech.CylinderVolume
public import IETFree.RauzyVeech.MeshShrink

/-!
# The shrinking of the path cylinders, and the coalescence of the normalised columns

For a finite word `γ` put `Q = Path.Q P γ` (the Rauzy–Veech path matrix), `c_b = ∑_a Q_{ab}` (the
*heights* of the level-`|γ|` tower) and `ŵ_b = Q e_b / c_b` (the *normalised columns*, i.e. the
vertices of the closed cylinder `Δ̄(γ) = conv{ŵ_b}`; `ColShrink.cs`, `ColShrink.ncol`). This file
proves

* `ColShrink.exists_weights`: every point of `Δ(γ)` is a convex combination of the `ŵ_b`, with
  nonnegative weights summing to `1`;
* `ColShrink.abs_sub_le_of_cols_close` and `ColShrink.diam_le_of_cols_close`: if the normalised
  columns are pairwise close, then so are the coordinates of the points of `Δ(γ)`, hence
  `diam Δ(γ) ≤ 2 · max_{b,b',a} |ŵ_{b,a} - ŵ_{b',a}|`;
* `ColShrink.tendsto_diam_of_cols_eventually_close`: consequently, along a path of the Rauzy–Veech
  algorithm, eventual pointwise closeness of the normalised columns of `Q(γ_k)` forces `diam Δ(γ_k)
  → 0`.

So the shrinking of the cylinders follows from the coalescence of the normalised columns of the
cocycle `k ↦ Q(γ_k(λ))`, which `PosBlock` and `Peel` produce from positive blocks.  The argument is
purely geometric: no statement about the *volume* of `Δ(γ_k)` is used. -/

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace ColShrink

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 0. The column sums and the normalised columns -/

/-- The `b`-th column sum of the path matrix `Q(γ)`: the number of level-`|γ|` floors of the tower
over the letter `b`. -/
noncomputable def cs (P : IETDatum₂ α n) (γ : List Bool) (b : α) : ℝ :=
  ∑ a, (IETDatum₂.Path.Q P γ a b : ℝ)

/-- The `b`-th **normalised column** of `Q(γ)`, i.e. the vertex `Q e_b / c_b` of the closed
cylinder `Δ̄(γ)` attached to the letter `b`. -/
noncomputable def ncol (P : IETDatum₂ α n) (γ : List Bool) (b : α) : α → ℝ :=
  fun a => (IETDatum₂.Path.Q P γ a b : ℝ) / cs P γ b

theorem cs_pos (P : IETDatum₂ α n) (γ : List Bool) (b : α) : 0 < cs P γ b := by
  have h := IETDatum₂.Path.Q_colsum_pos P γ b
  have h2 : ((∑ a, IETDatum₂.Path.Q P γ a b : ℤ) : ℝ)
      = ∑ a, (IETDatum₂.Path.Q P γ a b : ℝ) := by
    push_cast
    ring
  rw [cs, ← h2]
  exact_mod_cast h

theorem cs_nonneg (P : IETDatum₂ α n) (γ : List Bool) (b : α) : 0 ≤ cs P γ b :=
  le_of_lt (cs_pos P γ b)

theorem cs_ne_zero (P : IETDatum₂ α n) (γ : List Bool) (b : α) : cs P γ b ≠ 0 :=
  ne_of_gt (cs_pos P γ b)

/-! ## 1. The barycentric representation of a point of the cylinder -/

/-- **Every point of `Δ(γ)` is a convex combination of the normalised columns `ŵ_b`.** -/
theorem exists_weights (P : IETDatum₂ α n) (γ : List Bool) {x : α → ℝ≥0}
    (hx : x ∈ IETDatum₂.simplexCyl P γ) :
    ∃ t : α → ℝ, (∀ b, 0 ≤ t b) ∧ (∑ b, t b = 1) ∧
      ∀ a, (x a : ℝ) = ∑ b, t b * ncol P γ b a := by
  obtain ⟨hsim, w, hw⟩ := (IETDatum₂.mem_simplexCyl_iff P γ x).mp hx
  rw [IETDatum₂.IsRenorm] at hw
  obtain ⟨hwpos, hwx⟩ := hw
  have hsumw : ∑ a, (x a : ℝ) = 1 := by
    have h1 : ((∑ a, x a : ℝ≥0) : ℝ) = ((1 : ℝ≥0) : ℝ) := by rw [hsim]
    push_cast at h1 ⊢
    exact h1
  have hcolsumw : ∑ b, cs P γ b * w b = 1 := by
    have h1 : ∑ b, cs P γ b * w b
        = ∑ a, IETDatum₂.qApply (IETDatum₂.Path.Q P γ) w a := by
      rw [IETDatum₂.sum_qApply]
      simp only [cs]
      push_cast
      ring
    have h2 : ∑ a, IETDatum₂.qApply (IETDatum₂.Path.Q P γ) w a = ∑ a, (x a : ℝ) := by
      rw [← hwx]
    rw [h1, h2, hsumw]
  refine ⟨fun b => cs P γ b * w b, fun b => mul_nonneg (cs_nonneg P γ b) (le_of_lt (hwpos b)),
    hcolsumw, fun a => ?_⟩
  rw [show (x a : ℝ) = IETDatum₂.qApply (IETDatum₂.Path.Q P γ) w a from by rw [← hwx],
    IETDatum₂.qApply_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hc : cs P γ b ≠ 0 := cs_ne_zero P γ b
  rw [ncol]
  field_simp

/-! ## 2. Two points of the same cylinder are close if the columns are -/

/-- **The diameter bound.**  If all normalised columns of `Q(γ)` are pairwise within `r` in every
coordinate, then `Δ(γ)` has diameter at most `2 r`. -/
theorem abs_sub_le_of_cols_close (P : IETDatum₂ α n) (γ : List Bool) {r : ℝ}
    (hr : ∀ b b' a, |ncol P γ b a - ncol P γ b' a| ≤ r)
    {x x' : α → ℝ≥0} (hx : x ∈ IETDatum₂.simplexCyl P γ)
    (hx' : x' ∈ IETDatum₂.simplexCyl P γ) (a : α) :
    |(x a : ℝ) - (x' a : ℝ)| ≤ 2 * r := by
  obtain ⟨t, ht0, ht1, htx⟩ := exists_weights P γ hx
  obtain ⟨t', ht'0, ht'1, htx'⟩ := exists_weights P γ hx'
  have hcard : Fintype.card α = n := by
    rw [Fintype.card_congr P.piTop, Fintype.card_fin]
  have : Nonempty α := by
    rw [← Fintype.card_pos_iff, hcard]
    exact Nat.pos_of_ne_zero (NeZero.ne n)
  let b₀ : α := Classical.arbitrary α
  -- the difference of the two representations, with `∑ (t_b - t'_b) = 0`
  have hzero : ∑ b, (t b - t' b) = 0 := by rw [Finset.sum_sub_distrib, ht1, ht'1, sub_self]
  have hdiff : (x a : ℝ) - (x' a : ℝ)
      = ∑ b, (t b - t' b) * (ncol P γ b a - ncol P γ b₀ a) := by
    have h1 (b) : (t b - t' b) * (ncol P γ b a - ncol P γ b₀ a)
        = (t b - t' b) * ncol P γ b a - (t b - t' b) * ncol P γ b₀ a := by ring
    have h2 (b) : (t b - t' b) * ncol P γ b a
        = t b * ncol P γ b a - t' b * ncol P γ b a := by ring
    rw [Finset.sum_congr rfl fun b (_ : b ∈ (Finset.univ : Finset α)) => h1 b,
      Finset.sum_sub_distrib, ← Finset.sum_mul, hzero, zero_mul, sub_zero,
      Finset.sum_congr rfl fun b (_ : b ∈ (Finset.univ : Finset α)) => h2 b,
      Finset.sum_sub_distrib, ← htx a, ← htx' a]
  have hbound (b) : |(t b - t' b) * (ncol P γ b a - ncol P γ b₀ a)| ≤ |t b - t' b| * r := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hr b b₀ a) (abs_nonneg _)
  have hsumabs : ∑ b, |t b - t' b| ≤ 2 := by
    have h1 : ∑ b, |t b - t' b| ≤ ∑ b, (t b + t' b) := by
      refine Finset.sum_le_sum fun b _ => ?_
      exact abs_sub_le_iff.mpr ⟨by linarith [ht'0 b], by linarith [ht0 b]⟩
    have h2 : ∑ b, (t b + t' b) = 2 := by
      rw [Finset.sum_add_distrib, ht1, ht'1]; norm_num
    linarith
  calc |(x a : ℝ) - (x' a : ℝ)|
      = |∑ b, (t b - t' b) * (ncol P γ b a - ncol P γ b₀ a)| := by rw [hdiff]
    _ ≤ ∑ b, |(t b - t' b) * (ncol P γ b a - ncol P γ b₀ a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, |t b - t' b| * r := Finset.sum_le_sum fun b _ => hbound b
    _ = (∑ b, |t b - t' b|) * r := by rw [Finset.sum_mul]
    _ ≤ 2 * r := by
        refine mul_le_mul_of_nonneg_right hsumabs ?_
        exact (abs_nonneg (ncol P γ b₀ a - ncol P γ b₀ a)).trans (by simpa using hr b₀ b₀ a)

/-- **The diameter of a cylinder is bounded by the spread of its normalised columns.** -/
theorem diam_le_of_cols_close (P : IETDatum₂ α n) (γ : List Bool) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : ∀ b b' a, |ncol P γ b a - ncol P γ b' a| ≤ r) :
    Metric.diam (IETDatum₂.simplexCyl P γ) ≤ 2 * r := by
  refine Metric.diam_le_of_forall_dist_le (by linarith) fun x hx y hy => ?_
  rw [dist_pi_le_iff (by linarith)]
  intro a
  rw [NNReal.dist_eq]
  exact abs_sub_le_of_cols_close P γ hr hx hy a

/-! ## 3. From the coalescence of the columns to the shrinking of the cylinders -/

/-- **The shrinking of the path cylinders from the coalescence of the normalised columns.** If the
normalised columns of `Q(γ_k)` become eventually pairwise close along a path `p`, the path cylinders
shrink to points. -/
theorem tendsto_diam_of_cols_eventually_close (P : IETDatum₂ α n) (p : ℕ → Bool)
    (h : ∀ ε > 0, ∀ᶠ k in atTop,
      ∀ b b' a, |ncol P (PrefixWord.pfx p k) b a
        - ncol P (PrefixWord.pfx p k) b' a| ≤ ε) :
    Tendsto (fun k => Metric.diam (IETDatum₂.simplexCyl P (PrefixWord.pfx p k)))
      atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [Filter.Eventually.of_forall
      (fun k => Metric.diam_nonneg (s := IETDatum₂.simplexCyl P (PrefixWord.pfx p k)))]
      with k hk
    linarith
  · filter_upwards [h (a / 4) (by linarith)] with k hk
    have := diam_le_of_cols_close P (PrefixWord.pfx p k) (by linarith) hk
    linarith

end ColShrink

end
