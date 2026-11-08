/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.BoundedSimplex
public import IETFree.RauzyVeech.Nesting
public import IETFree.RauzyVeech.Ray.Criterion

/-!
# The closed cylinder: nonnegative `Q`-images of nonnegative vectors

`cone Q` is *strictly* positive: `x ∈ cone Q ↔ ∃ y, (∀ a, 0 < y a) ∧ x = Q y`.  The tower
formula of the Masur–Veech argument only produces a **nonnegative** renormalised vector `λ̂` (the
masses of the level-`n` cells can vanish), so the length vector of an invariant measure is only
known to lie in the *closure* of a path cylinder.  This file closes that gap for the ray criterion
of `Ray/Criterion.lean`:

* `mem_closure_simplexCyl_of_nonneg`: if `Sig : α → ℝ` is nonnegative, of total mass
  `1`, and `Sig = Q y` for a nonnegative `y`, then `Sig` (as a vector of `ℝ≥0`) lies in
  `closure (simplexCyl P w)`.

The proof is the usual `ε`-argument.  For `t > 0` the vector `y + t` is strictly positive, so
`z t = (y + t)/(1 + t W)`, with `W` the sum of all entries of `Q`, is a strictly positive
renormalised vector whose image `Q (z t)` still has total mass `1`: by Fubini (`sum_qApply_cast`)
its mass is `(∑_b Z_b (y_b + t))/(1 + t W)`, and `∑_b Z_b y_b = ∑_a (Q y)_a = 1`, `∑_b Z_b = W`;
and `Q (z t) → Q y` as `t → 0⁺`, with the explicit bound
`|Q(z t)_a - (Q y)_a| ≤ 2 t W`.  Only `0 ≤ W` is needed, never `0 < W`: if `W = 0` the hypotheses
are contradictory (`∑_a (Q y)_a = 1`), and the estimate is uniform anyway.

Auxiliary identities, stated separately:
* `sum_qApply_cast` — Fubini for the action, `∑_a (Q y)_a = ∑_b (∑_a Q_{ab}) y_b` (this is
  `IETDatum₂.sum_qApply` of `Nesting.lean`, restated with the column sums `colR`);
* `totSum_eq_sum_colR` — the sum of the row sums is the sum of the column sums;
* `qApply_add_div` — the coordinates of `Q ((y + t)/(1 + t W))`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology

-- the auxiliary sums keep the project's variable context (`[DecidableEq α]` is part of it)

namespace IntervalExchange.RauzyVeech

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Row sums, and the two sum identities -/

/-- The row sums of an integer matrix, as real numbers: `R_a = ∑_b Q_{ab}`. -/
noncomputable def rowSum (Q : Matrix α α ℤ) (a : α) : ℝ := ∑ b, (Q a b : ℝ)

/-- The total mass of an integer matrix: `W = ∑_a ∑_b Q_{ab}`, the sum of the row sums. -/
noncomputable def totSum (Q : Matrix α α ℤ) : ℝ := ∑ a, rowSum Q a

omit [DecidableEq α] in
theorem rowSum_nonneg (Q : Matrix α α ℤ) (hQ : ∀ a b, (0 : ℝ) ≤ (Q a b : ℝ)) (a : α) :
    0 ≤ rowSum Q a :=
  Finset.sum_nonneg fun b _ => hQ a b

omit [DecidableEq α] in
theorem totSum_nonneg (Q : Matrix α α ℤ) (hQ : ∀ a b, (0 : ℝ) ≤ (Q a b : ℝ)) :
    0 ≤ totSum Q :=
  Finset.sum_nonneg fun a _ => rowSum_nonneg Q hQ a

omit [DecidableEq α] in
/-- Each row sum is at most the total mass (all entries are nonnegative). -/
theorem rowSum_le_totSum (Q : Matrix α α ℤ) (hQ : ∀ a b, (0 : ℝ) ≤ (Q a b : ℝ)) (a : α) :
    rowSum Q a ≤ totSum Q :=
  Finset.single_le_sum (f := rowSum Q) (fun a _ => rowSum_nonneg Q hQ a) (Finset.mem_univ a)

omit [DecidableEq α] in
/-- **The sum of the row sums is the sum of the column sums** (finite Fubini). -/
theorem totSum_eq_sum_colR (Q : Matrix α α ℤ) :
    totSum Q = ∑ b, colR Q b := by
  simp only [totSum, rowSum, colR_eq_sum]
  exact Finset.sum_comm

omit [DecidableEq α] in
/-- **Fubini for the action of `Q`**: the total mass of `Q y` is the `W`-weighted sum
`∑_b (∑_a Q_{ab}) y_b`.  This is `IETDatum₂.sum_qApply` (`Nesting.lean`), with the column sums
written as `colR`. -/
theorem sum_qApply_cast (Q : Matrix α α ℤ) (y : α → ℝ) :
    ∑ a, qApply Q y a = ∑ b, colR Q b * y b :=
  IETDatum₂.sum_qApply Q y

omit [DecidableEq α] in
/-- **The renormalised vector `(y + t)/(1 + tW)` and its image.**  The identity is a ring identity
and holds for every `t` (the denominator is never used invertibly). -/
theorem qApply_add_div (Q : Matrix α α ℤ) (y : α → ℝ) (t : ℝ) (a : α) :
    qApply Q (fun b => (y b + t) / (1 + t * totSum Q)) a =
      (qApply Q y a + t * rowSum Q a) / (1 + t * totSum Q) := by
  rw [qApply_apply]
  have hstep (b : α) :
    (Q a b : ℝ) * ((y b + t) / (1 + t * totSum Q)) =
      ((Q a b : ℝ) * y b + t * (Q a b : ℝ)) / (1 + t * totSum Q) := by
    ring
  rw [Finset.sum_congr rfl (fun b _ => hstep b), ← Finset.sum_div, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  rfl

/-! ## 2. The closure lemma -/

/-- **Nonnegative `Q`-images of nonnegative vectors lie in the closure of the cylinder.**  This is
the closure form of `mem_simplexCyl_of_cone` needed by the ray criterion: the tower formula gives a
renormalised vector that is only nonnegative, and the level-`n` cell masses may vanish. -/
theorem mem_closure_simplexCyl_of_nonneg (P : IETDatum₂ α n) {w : List Bool} {Sig : α → ℝ}
    (hSig0 : ∀ a, 0 ≤ Sig a) (hsum : ∑ a, Sig a = 1)
    (hSig : ∃ y : α → ℝ, (∀ a, 0 ≤ y a) ∧ Sig = qApply (IETDatum₂.Path.Q P w) y) :
    (fun a => (⟨Sig a, hSig0 a⟩ : ℝ≥0)) ∈ closure (IETDatum₂.simplexCyl P w) := by
  obtain ⟨y, hy, rfl⟩ := hSig
  set Q := IETDatum₂.Path.Q P w with hQdef
  have hQnn (a) (b) : (0 : ℝ) ≤ (Q a b : ℝ) := by
    have h := IETDatum₂.Path.Q_nonneg P w a b
    exact_mod_cast h
  have hWnn : 0 ≤ totSum Q := totSum_nonneg Q hQnn
  have hxnn (a) : 0 ≤ qApply Q y a := by
    rw [qApply_apply]
    exact Finset.sum_nonneg fun b _ => mul_nonneg (hQnn a b) (hy b)
  have hx1 (a) : qApply Q y a ≤ 1 := by
    have h := Finset.single_le_sum (f := fun a => qApply Q y a)
      (fun a _ => hxnn a) (Finset.mem_univ a)
    linarith
  refine Metric.mem_closure_iff.mpr fun ε hε => ?_
  set t : ℝ := ε / (2 * (totSum Q + 1)) with ht
  have hW1 : (0 : ℝ) < totSum Q + 1 := by linarith
  have htpos : 0 < t := by
    rw [ht]
    exact div_pos hε (by linarith)
  have hdenpos : 0 < 1 + t * totSum Q := by
    have h := mul_nonneg htpos.le hWnn
    linarith
  have hden1 : (1 : ℝ) ≤ 1 + t * totSum Q := by
    have h := mul_nonneg htpos.le hWnn
    linarith
  set z : α → ℝ := fun a => (y a + t) / (1 + t * totSum Q) with hz
  have hzpos (a) : 0 < z a := div_pos (by linarith [hy a]) hdenpos
  set xt : α → ℝ := qApply Q z with hxt
  have hxtpt (a) : xt a =
      (qApply Q y a + t * rowSum Q a) / (1 + t * totSum Q) := qApply_add_div Q y t a
  have hxtnn (a) : 0 ≤ xt a := by
    rw [hxtpt a]
    refine div_nonneg ?_ hdenpos.le
    have h1 := rowSum_nonneg Q hQnn a
    have h2 := mul_nonneg htpos.le h1
    linarith [hxnn a]
  -- the mass of `Q y`, from Fubini (`sum_qApply_cast`)
  have hfub : ∑ b, colR Q b * y b = 1 := by
    rw [← sum_qApply_cast Q y]
    exact hsum
  have hmass : ∑ a, xt a = 1 := by
    have hstep (b : α) :
      colR Q b * ((y b + t) / (1 + t * totSum Q)) =
        (colR Q b * y b + t * colR Q b) / (1 + t * totSum Q) := by
      ring
    have h1 : ∑ b, colR Q b * ((y b + t) / (1 + t * totSum Q)) =
        ((∑ b, colR Q b * y b) + t * totSum Q) / (1 + t * totSum Q) := by
      rw [Finset.sum_congr rfl (fun b _ => hstep b), ← Finset.sum_div, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← totSum_eq_sum_colR]
    have h2 : ∑ a, xt a = ∑ b, colR Q b * ((y b + t) / (1 + t * totSum Q)) :=
      sum_qApply_cast Q z
    rw [h2, h1, hfub]
    exact div_self (ne_of_gt hdenpos)
  have hcone : xt ∈ cone Q := by
    rw [cone_eq]
    exact ⟨z, hzpos, hxt.symm⟩
  have hmem : (fun a => (⟨xt a, hxtnn a⟩ : ℝ≥0)) ∈ IETDatum₂.simplexCyl P w :=
    mem_simplexCyl_of_cone P hxtnn hmass hcone
  refine ⟨fun a => (⟨xt a, hxtnn a⟩ : ℝ≥0), hmem, ?_⟩
  -- the estimate `|xt a - (Q y) a| ≤ 2 t W`
  have hbound (a) : |xt a - qApply Q y a| ≤ 2 * t * totSum Q := by
    have hRnn : 0 ≤ rowSum Q a := rowSum_nonneg Q hQnn a
    have hRle : rowSum Q a ≤ totSum Q := rowSum_le_totSum Q hQnn a
    have hx1a : qApply Q y a ≤ 1 := hx1 a
    have hx0a : 0 ≤ qApply Q y a := hxnn a
    have hsub : xt a - qApply Q y a =
        t * (rowSum Q a - totSum Q * qApply Q y a) / (1 + t * totSum Q) := by
      rw [hxtpt a]
      field_simp
      ring
    have hnum : |rowSum Q a - totSum Q * qApply Q y a| ≤ 2 * totSum Q := by
      refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith
    have hAle : 0 ≤ t * |rowSum Q a - totSum Q * qApply Q y a| :=
      mul_nonneg htpos.le (abs_nonneg _)
    have hA : t * |rowSum Q a - totSum Q * qApply Q y a| ≤ t * (2 * totSum Q) :=
      mul_le_mul_of_nonneg_left hnum htpos.le
    rw [hsub, abs_div, abs_of_pos hdenpos, abs_mul, abs_of_pos htpos]
    calc t * |rowSum Q a - totSum Q * qApply Q y a| / (1 + t * totSum Q)
        ≤ t * |rowSum Q a - totSum Q * qApply Q y a| := div_le_self hAle hden1
      _ ≤ t * (2 * totSum Q) := hA
      _ = 2 * t * totSum Q := by ring
  have hdist' : dist (fun a => ((⟨qApply Q y a, hSig0 a⟩ : ℝ≥0) : ℝ))
      (fun a => ((⟨xt a, hxtnn a⟩ : ℝ≥0) : ℝ)) ≤ 2 * t * totSum Q := by
    rw [dist_pi_le_iff (by linarith : (0 : ℝ) ≤ 2 * t * totSum Q)]
    intro a
    rw [Real.dist_eq, abs_sub_comm]
    exact hbound a
  have hdist : dist (fun a => (⟨qApply Q y a, hSig0 a⟩ : ℝ≥0))
      (fun a => (⟨xt a, hxtnn a⟩ : ℝ≥0)) ≤ 2 * t * totSum Q :=
    (dist_co_co (x := fun a => (⟨qApply Q y a, hSig0 a⟩ : ℝ≥0))
      (y := fun a => (⟨xt a, hxtnn a⟩ : ℝ≥0))).symm.trans_le hdist'
  have hkey : 2 * t * totSum Q = ε * (totSum Q / (totSum Q + 1)) := by
    rw [ht]
    field_simp
  have hfrac : totSum Q / (totSum Q + 1) < 1 := by
    rw [div_lt_one hW1]
    linarith
  have hlt : 2 * t * totSum Q < ε := by
    rw [hkey]
    calc ε * (totSum Q / (totSum Q + 1)) < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
      _ = ε := mul_one ε
  exact lt_of_le_of_lt hdist hlt

/-! ## 3. Application: the ray criterion with a nonnegative preimage -/

/-- **The ray criterion with the hypothesis the tower formula actually gives.**  The ray criterion
(of `IETFree/RauzyVeech/Ray/Criterion.lean`) assumes `Sig ∈ cone (Q (w k))` for every `k`, i.e. a
*strictly* positive renormalised vector.  The
tower formula only produces nonnegative ones, which is what `mem_closure_simplexCyl_of_nonneg` is
for: `Sig` then lies in every `closure Δ(w k)`, and these closures meet in `lam` by
`iInter_closure_eq_singleton`. -/
theorem eq_of_nonneg_preimage_of_diam {w : ℕ → List Bool} {lam : α → ℝ≥0} {Sig : α → ℝ}
    {y : ℕ → α → ℝ} (P : IETDatum₂ α n)
    (hanti : Antitone fun k => IETDatum₂.simplexCyl P (w k))
    (hbdd : Bornology.IsBounded (IETDatum₂.simplexCyl P (w 0)))
    (hdiam : Tendsto (fun k => Metric.diam (IETDatum₂.simplexCyl P (w k))) atTop (𝓝 0))
    (hlam_mem : ∀ k, lam ∈ IETDatum₂.simplexCyl P (w k))
    (hsum : ∑ a, Sig a = 1) (hy : ∀ k a, 0 ≤ y k a)
    (hSig : ∀ k, Sig = qApply (IETDatum₂.Path.Q P (w k)) (y k)) :
    Sig = fun a => (lam a : ℝ) := by
  have hQnn (a) (b) : (0 : ℝ) ≤ (IETDatum₂.Path.Q P (w 0) a b : ℝ) := by
    have h := IETDatum₂.Path.Q_nonneg P (w 0) a b
    exact_mod_cast h
  have hSig0 (a) : 0 ≤ Sig a := by
    rw [hSig 0, qApply_apply]
    exact Finset.sum_nonneg fun b _ => mul_nonneg (hQnn a b) (hy 0 b)
  have hclos (k) : (fun a => (⟨Sig a, hSig0 a⟩ : ℝ≥0)) ∈
      closure (IETDatum₂.simplexCyl P (w k)) := mem_closure_simplexCyl_of_nonneg P hSig0 hsum ⟨y k,
          hy k, hSig k⟩
  have hsub : (fun a => (⟨Sig a, hSig0 a⟩ : ℝ≥0)) ∈
      ⋂ k, closure (IETDatum₂.simplexCyl P (w k)) := Set.mem_iInter.mpr hclos
  have hsingle : (fun a => (⟨Sig a, hSig0 a⟩ : ℝ≥0)) ∈ ({lam} : Set (α → ℝ≥0)) := by
    rw [← iInter_closure_eq_singleton hlam_mem hanti hbdd hdiam]
    exact hsub
  have hEq : (fun a => (⟨Sig a, hSig0 a⟩ : ℝ≥0)) = lam :=
    Set.mem_singleton_iff.mp hsingle
  funext a
  have h := congrArg (fun v : α → ℝ≥0 => ((v a : ℝ))) hEq
  exact h

end IntervalExchange.RauzyVeech

end
