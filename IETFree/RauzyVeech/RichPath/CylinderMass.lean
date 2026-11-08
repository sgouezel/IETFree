/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.BalancedSet
public import IETFree.RauzyVeech.ColDiam

/-!
# The cylinder mass of a child cylinder

Everything here is about the Rauzy--Veech path matrices and the exact cylinder mass formula; no
measure theory on a projective space is used.

Write `h_b = colSum P w b > 0` for the column sums of `Path.Q P w` (the heights of the tower) and

`cond P w δ = (∏ b, colSum P w b) / (∏ b, colSum P (w ++ δ) b) = σ(Δ_{wδ}) / σ(Δ_w)`

for the mass of the child cylinder relative to its parent
 (`volume_append_mul`). Main results:

* `cond_arrow`: for one letter `e`, if `α` is the winner of `e` at `vertex P w` and `β` its loser,
  then `cond P w [e] = h_β / (h_α + h_β)` (the loser's height over the sum).
* `state_mono`: `colSum P w b ≤ colSum P (w ++ δ) b` (heights are non-decreasing).
-/

open Finset IntervalExchange.IETDatum₂
open scoped BigOperators NNReal ENNReal

@[expose] public section

namespace IntervalExchange.RauzyVeech.RichPath

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Definitions -/

/-- The mass of the child cylinder `Δ(w ++ δ)` relative to its parent `Δ(w)`, i.e. the ratio
of the products of the column sums. -/
noncomputable def cond (P : IETDatum₂ α n) (w δ : List Bool) : ℝ :=
  (∏ b, colSum P w b) / ∏ b, colSum P (w ++ δ) b

/-! ## 2. The column sums and the conditional mass of one more letter -/

/-- The column sums in `ℝ`, one letter later: the loser's height grows by the winner's. -/
theorem colSum_append_singleton (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (e : Bool) (b : α) :
    colSum P (w ++ [e]) b =
      colSum P w b +
        (if b = (P.vertex w).last (!e) then colSum P w ((P.vertex w).last e) else 0) := by
  have h := colsum_append_singleton P hP hn w e b
  have h2 := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at h2
  simpa [colSum] using h2

/-- One factor of a product changed. -/
theorem prod_ite_eq_mul {M : Type*} [CommMonoid M] (f : α → M) (β : α) (y : M) :
    (∏ b, (if b = β then y else f b)) = (∏ b ∈ Finset.univ.erase β, f b) * y := by
  rw [← Finset.prod_erase_mul (s := Finset.univ) (f := fun b => if b = β then y else f b)
    (Finset.mem_univ β)]
  congr 1
  · exact Finset.prod_congr rfl fun b hb => by rw [ite_eq_right (Finset.ne_of_mem_erase hb)]
  · rw [ite_eq_left rfl]

/-- The product of the column sums one letter later. -/
theorem prod_cs_append_singleton (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (e : Bool) :
    (∏ b, colSum P (w ++ [e]) b) =
      (∏ b ∈ Finset.univ.erase ((P.vertex w).last (!e)), colSum P w b) *
        (colSum P w ((P.vertex w).last (!e))
          + colSum P w ((P.vertex w).last e)) := by
  have h1 : (∏ b, colSum P (w ++ [e]) b) =
      ∏ b, (if b = (P.vertex w).last (!e) then colSum P w ((P.vertex w).last (!e))
        + colSum P w ((P.vertex w).last e) else colSum P w b) := by
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [colSum_append_singleton P hP hn w e b]
    by_cases hb : b = (P.vertex w).last (!e)
    · rw [ite_eq_left hb, ite_eq_left hb, hb]
    · rw [ite_eq_right hb, ite_eq_right hb, add_zero]
  rw [h1, prod_ite_eq_mul]

/-- **The conditional mass of one letter**: the loser's height over the sum of the two heights
(`P_q(γ | π) = q_β/(q_α + q_β)` in AGY, `α` the winner and `β` the loser). -/
theorem cond_arrow (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (e : Bool) :
    cond P w [e] = colSum P w ((P.vertex w).last (!e)) /
      (colSum P w ((P.vertex w).last (!e)) + colSum P w ((P.vertex w).last e)) := by
  have hprod := prod_cs_append_singleton P hP hn w e
  have herase : (∏ b ∈ Finset.univ.erase ((P.vertex w).last (!e)), colSum P w b) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun b _ => colSum_ne_zero P w b
  have hsplit : (∏ b, colSum P w b) =
      (∏ b ∈ Finset.univ.erase ((P.vertex w).last (!e)), colSum P w b) *
        colSum P w ((P.vertex w).last (!e)) :=
    (Finset.prod_erase_mul (s := Finset.univ) (f := fun b => colSum P w b)
      (Finset.mem_univ _)).symm
  rw [cond, hprod, hsplit]
  exact mul_div_mul_left _ _ herase

/-- The mass of the empty continuation is `1`. -/
@[simp]
theorem cond_nil (P : IETDatum₂ α n) (w : List Bool) : cond P w [] = 1 := by
  have h : (∏ b, colSum P w b) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun b _ => colSum_ne_zero P w b
  simpa [cond] using div_self h

/-- **The chain rule** for the conditional masses. -/
theorem cond_append (P : IETDatum₂ α n) (w δ δ' : List Bool) :
    cond P w (δ ++ δ') = cond P w δ * cond P (w ++ δ) δ' := by
  have h2 : (∏ b, colSum P (w ++ δ) b) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun b _ => colSum_ne_zero P (w ++ δ) b
  simp only [cond]
  rw [div_mul_div_comm, mul_comm (∏ b, colSum P w b) (∏ b, colSum P (w ++ δ) b),
    mul_div_mul_left _ _ h2, List.append_assoc]

/-- The height of the child in terms of the path matrix of the continuation — the direction's
`∑ c, (Path.Q (P.vertex P w) δ c α : ℝ) * colSum P w c`. -/
theorem colSum_append_eq_sum (P : IETDatum₂ α n) (w δ : List Bool) (b : α) :
    colSum P (w ++ δ) b
      = ∑ c, (IETDatum₂.Path.Q (P.vertex w) δ c b : ℝ) * colSum P w c := by
  simp only [colSum]
  have h3 : ((∑ a, IETDatum₂.Path.Q P (w ++ δ) a b : ℤ) : ℝ)
      = ∑ c, (IETDatum₂.Path.Q (P.vertex w) δ c b : ℝ) *
          ∑ a, (IETDatum₂.Path.Q P w a c : ℝ) := by
    rw [colsum_append P w δ b]
    push_cast
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  push_cast at h3 ⊢
  exact h3

/-- **Heights are non-decreasing** along a continuation. -/
theorem state_mono (P : IETDatum₂ α n) (w δ : List Bool) (b : α) :
    colSum P w b ≤ colSum P (w ++ δ) b := by
  have h := colsum_le_colsum_append P w δ b
  have h2 : ((∑ a, IETDatum₂.Path.Q P w a b : ℤ) : ℝ)
      ≤ ((∑ a, IETDatum₂.Path.Q P (w ++ δ) a b : ℤ) : ℝ) := by exact_mod_cast h
  push_cast at h2
  simpa [colSum] using h2

/-- The relative cylinder masses are positive. -/
theorem cond_pos (P : IETDatum₂ α n) (w δ : List Bool) : 0 < cond P w δ :=
  div_pos (Finset.prod_pos fun b _ => colSum_pos P w b)
    (Finset.prod_pos fun b _ => colSum_pos P (w ++ δ) b)

theorem cond_nonneg (P : IETDatum₂ α n) (w δ : List Bool) : 0 ≤ cond P w δ :=
  le_of_lt (cond_pos P w δ)

/-! ## 3. The link with the exact cylinder mass `volume_append_mul` -/

/-- The column sums used by the mass formula and by `colSum` agree. -/
theorem coe_colsumNN_cs (P : IETDatum₂ α n) (γ : List Bool) (b : α) :
    ((colsumNN (IETDatum₂.Path.Q P γ) b : ℝ≥0) : ℝ) = colSum P γ b := by
  rw [coe_colsumNN (N := IETDatum₂.Path.Q P γ) (b := b)
    (IETDatum₂.Path.Q_colsum_pos P γ b)]
  simp only [colSum]
  push_cast
  ring

/-- `cond` is the `ℝ≥0` factor of the mass formula. -/
theorem toNNReal_cond (P : IETDatum₂ α n) (γ δ : List Bool) :
    Real.toNNReal (cond P γ δ) = ∏ b, (colsumNN (IETDatum₂.Path.Q P γ) b *
      (colsumNN (IETDatum₂.Path.Q P (γ ++ δ)) b)⁻¹) := by
  apply NNReal.coe_injective
  have h1 : ((∏ b, (colsumNN (IETDatum₂.Path.Q P γ) b *
      (colsumNN (IETDatum₂.Path.Q P (γ ++ δ)) b)⁻¹) : ℝ≥0) : ℝ)
      = (∏ b, colSum P γ b) * (∏ b, colSum P (γ ++ δ) b)⁻¹ := by
    rw [NNReal.coe_prod]
    simp only [NNReal.coe_mul, NNReal.coe_inv]
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    congr 1
    · exact Finset.prod_congr rfl fun b _ => coe_colsumNN_cs P γ b
    · exact congrArg Inv.inv (Finset.prod_congr rfl fun b _ => coe_colsumNN_cs P (γ ++ δ) b)
  rw [h1, Real.coe_toNNReal (cond P γ δ) (le_of_lt (cond_pos P γ δ)), cond, div_eq_mul_inv]

/-- **`cond` is the mass of the child cylinder relative to its parent.**  This is the exact mass
formula `volume_append_mul`, rewritten with `cond`. -/
theorem volume_append_eq_cond (P : IETDatum₂ α n) (γ δ : List Bool) :
    simplexVolumeOn α (IETDatum₂.simplexCyl P (γ ++ δ))
      = ENNReal.ofReal (cond P γ δ) * simplexVolumeOn α (IETDatum₂.simplexCyl P γ) := by
  rw [volume_append_mul, ← toNNReal_cond]
  rfl

end IntervalExchange.RauzyVeech.RichPath

end
