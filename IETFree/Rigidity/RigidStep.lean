/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.Rigidity.RigidSet

/-!
# The rigid step

The abstract rigid step of the proof of Veech's rigidity: at a node `γ` of an `IterOK` word whose
`b`-cell is big (`BigCell`, relative precision
`deltaOf ε M`),
whose heights are dominated by the height of `b` (with constant `M`), and whose base is short
(`baseLen ≤ min ε (1/(2N₀))`), there are a time `q ≥ N₀`, a translation vector `t` with `|t| ≤ ε`,
and a measurable set `B ⊆ [0,1)` of measure `≥ 1 - ε` on which `T^[q]` is the translation
`x ↦ x + t`.

The proof runs as follows:

* the degenerate cases first: for `ε ≥ 1` the conclusion is trivial (`q := N₀`, `t := 0`, `B := ∅`),
  and `N₀ = 0` makes the hypotheses contradictory, since `hΛ` then gives `baseLen ≤ 0` while
  `0 < baseLen`;
* `0 < baseLen P γ lam` needs no positivity of `lam`: the total-mass identity `∑_c h_c · σ_c = 1`
  (Veech's (3.1) at the node) with every `σ_c ≥ 0` shows that some `σ_c` is positive;
* the tower dominates, `1 - (M+1)δ ≤ h_b · σ_b`, because the other terms of the total mass are at
  most `M h_b (Λ - σ_b) ≤ M h_b δ Λ` with `Λ ≤ σ_b/(1-δ)`;
* `exists_rigid_set` then gives a set `B` with `|t| ≤ δ Λ` and `|B| ≥ (1-2δ) h_b Λ`, and the
  arithmetic of Appendix A turns the two into `|t| ≤ ε` and `|B| ≥ 1 - ε`, and the domination into
  `q = h_b ≥ N₀`.

The hypothesis `hstop` is carried by the statement but is **not used** by the proof: the tower
statements at the node `γ` are those of `Rigidity/RigidSet.lean`, which needs `IterOK P lam γ` only.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

namespace IETFree.Rigidity
namespace Internal

/-! ## 1. The constants of `deltaOf` -/

/-- `deltaOf ε M` is positive. -/
private theorem deltaOf_pos {ε : ℝ} (hε : 0 < ε) (M : ℕ) : 0 < deltaOf ε M := by
  rw [deltaOf]
  exact lt_min (by norm_num) (div_pos hε (by positivity))

/-- `deltaOf ε M` is at most `1/4`. -/
private theorem deltaOf_le_quarter (ε : ℝ) (M : ℕ) : deltaOf ε M ≤ 1 / 4 :=
  min_le_left _ _

/-- `deltaOf ε M` is at most `ε / (8 (M + 2))`. -/
private theorem deltaOf_le_div (ε : ℝ) (M : ℕ) :
    deltaOf ε M ≤ ε / (8 * ((M : ℝ) + 2)) :=
  min_le_right _ _

/-- Cleared form of `deltaOf_le_div`: `deltaOf ε M · 8 (M + 2) ≤ ε`. -/
private theorem deltaOf_mul_le {ε : ℝ} {M : ℕ} :
    deltaOf ε M * (8 * ((M : ℝ) + 2)) ≤ ε := by
  have hC : (0 : ℝ) < 8 * ((M : ℝ) + 2) := by positivity
  calc deltaOf ε M * (8 * ((M : ℝ) + 2))
      ≤ (ε / (8 * ((M : ℝ) + 2))) * (8 * ((M : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_right (deltaOf_le_div ε M) hC.le
    _ = ε := by rw [div_mul_cancel₀ ε (ne_of_gt hC)]

/-- `(M + 1) · deltaOf ε M ≤ 1/8` for `ε ≤ 1`. -/
private theorem deltaOf_mul_succ_le {ε : ℝ} {M : ℕ} (hε1 : ε ≤ 1) :
    ((M : ℝ) + 1) * deltaOf ε M ≤ 1 / 8 := by
  have hB := deltaOf_mul_le (ε := ε) (M := M)
  have h1 : ((M : ℝ) + 1) * (deltaOf ε M * (8 * ((M : ℝ) + 2)))
      ≤ ((M : ℝ) + 1) * 1 := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have h3 : (((M : ℝ) + 1) * deltaOf ε M) * 8 * ((M : ℝ) + 2) ≤ ((M : ℝ) + 2) := by
    linarith [h1]
  have h4 : (((M : ℝ) + 1) * deltaOf ε M) * 8 ≤ 1 := by
    refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < (M : ℝ) + 2)
    linarith [h3]
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr h4

/-- `(M + 3) · deltaOf ε M ≤ ε` for `0 < ε`. -/
private theorem deltaOf_mul_add_three_le {ε : ℝ} {M : ℕ} (hε0 : 0 < ε) :
    ((M : ℝ) + 3) * deltaOf ε M ≤ ε := by
  have hB := deltaOf_mul_le (ε := ε) (M := M)
  have h1 : ((M : ℝ) + 3) * deltaOf ε M
      ≤ (8 * ((M : ℝ) + 2)) * deltaOf ε M := by
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (deltaOf_pos hε0 M))
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    nlinarith
  have h2 : (8 * ((M : ℝ) + 2)) * deltaOf ε M ≤ ε := by linarith
  linarith

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 2. The total mass at a node, and positivity of the base length -/

/-- **The total-mass identity at a node**: `∑_b h_b · σ_b = 1`, Veech's (3.1) at the node. -/
private theorem total_mass (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {lam : α → ℝ≥0} (hlam : lam ∈ simplexOn α) {γ : List Bool}
    (hOK : TowerTrue.IterOK P lam γ) :
    (∑ b, (height P γ b : ℝ) * (Tower.lamAfter P γ lam b : ℝ)) = 1 := by
  have hcoef (b : α) : (height P γ b : ℝ)
      = ∑ a, ((IETDatum₂.Path.Q P γ a b).toNat : ℝ) := by
    simp only [height]
    push_cast
    rfl
  calc (∑ b, (height P γ b : ℝ) * (Tower.lamAfter P γ lam b : ℝ))
      = ∑ b, (∑ a, ((IETDatum₂.Path.Q P γ a b).toNat : ℝ))
          * (Tower.lamAfter P γ lam b : ℝ) :=
        Finset.sum_congr rfl (fun b _ => by rw [hcoef b])
    _ = ∑ b, ∑ a, ((IETDatum₂.Path.Q P γ a b).toNat : ℝ)
          * (Tower.lamAfter P γ lam b : ℝ) :=
        Finset.sum_congr rfl (fun b _ => Finset.sum_mul _ _ _)
    _ = ∑ a, ∑ b, ((IETDatum₂.Path.Q P γ a b).toNat : ℝ)
          * (Tower.lamAfter P γ lam b : ℝ) := Finset.sum_comm
    _ = ∑ a, (lam a : ℝ) :=
        Finset.sum_congr rfl (fun a _ => TowerInjectivity.renorm_apply P hP hn hOK a)
    _ = 1 := by
        have h := congrArg (fun t : ℝ≥0 => (t : ℝ)) hlam
        push_cast at h
        exact h

/-- **The base length at a node is positive**, with no positivity hypothesis on `lam`: the
total-mass identity and the nonnegativity of the renormalised lengths force one of them to be
positive. -/
private theorem baseLen_pos (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {lam : α → ℝ≥0} (hlam : lam ∈ simplexOn α) {γ : List Bool}
    (hOK : TowerTrue.IterOK P lam γ) : 0 < baseLen P γ lam := by
  rcases lt_or_ge 0 (baseLen P γ lam) with h | h
  · exact h
  · exfalso
    have hbase : baseLen P γ lam = ∑ c, (Tower.lamAfter P γ lam c : ℝ) := rfl
    have hsum : (∑ c, (Tower.lamAfter P γ lam c : ℝ)) = 0 := by
      have h0 : (0 : ℝ) ≤ ∑ c, (Tower.lamAfter P γ lam c : ℝ) :=
        Finset.sum_nonneg (fun c _ => (Tower.lamAfter P γ lam c).coe_nonneg)
      linarith
    have hzero (c : α) : (Tower.lamAfter P γ lam c : ℝ) = 0 := by
      have h1 : (Tower.lamAfter P γ lam c : ℝ) ≤ ∑ i, (Tower.lamAfter P γ lam i : ℝ) :=
        Finset.single_le_sum (f := fun i => (Tower.lamAfter P γ lam i : ℝ))
          (fun i _ => (Tower.lamAfter P γ lam i).coe_nonneg) (Finset.mem_univ c)
      have h2 : (0 : ℝ) ≤ (Tower.lamAfter P γ lam c : ℝ) :=
        (Tower.lamAfter P γ lam c).coe_nonneg
      linarith
    have hmass := total_mass P hP hn hlam hOK
    have h0 : (∑ c, (height P γ c : ℝ) * (Tower.lamAfter P γ lam c : ℝ)) = 0 :=
      Finset.sum_eq_zero (fun c _ => by rw [hzero c, mul_zero])
    linarith

/-! ## 3. The tower dominates the base -/

/-- **The tower dominates**: if the `b`-th cell has measure `≥ 1 - δ` of the base and every other
tower height is at most `M · h_b`, the `b`-th tower alone carries `1 - (M+1)δ` of the total mass. -/
private theorem tower_bound {hb sb L d Mm R : ℝ} (hM : 1 ≤ Mm) (hd0 : 0 ≤ d)
    (hbd : d ≤ 1 / 4) (hb0 : 0 ≤ hb) (hbig : (1 - d) * L ≤ sb)
    (hR : R ≤ Mm * hb * (L - sb)) (hTL : hb * sb + R = 1) :
    1 - (Mm + 1) * d ≤ hb * sb := by
  have hd1 : (0 : ℝ) < 1 - d := by linarith
  have hMm0 : (0 : ℝ) ≤ Mm := by linarith
  -- the mass outside the `b`-th tower, after multiplying by `1 - d`
  have hA : (1 - d) * (L - sb) ≤ d * sb := by nlinarith
  have h1 : hb * ((1 - d) * (L - sb)) ≤ hb * (d * sb) := mul_le_mul_of_nonneg_left hA hb0
  have h2 : Mm * (hb * ((1 - d) * (L - sb))) ≤ Mm * (hb * (d * sb)) :=
    mul_le_mul_of_nonneg_left h1 hMm0
  have hB : Mm * hb * ((1 - d) * (L - sb)) ≤ Mm * d * (hb * sb) := by linarith
  have h3 : (1 - d) * R ≤ (1 - d) * (Mm * hb * (L - sb)) :=
    mul_le_mul_of_nonneg_left hR hd1.le
  have hC : (1 - d) * R ≤ Mm * hb * ((1 - d) * (L - sb)) := by linarith
  have hTL' : (1 - d) * (hb * sb) + (1 - d) * R = 1 - d := by nlinarith
  have hX : 1 - d ≤ hb * sb * (1 + (Mm - 1) * d) := by linarith
  have hpos : 0 < 1 + (Mm - 1) * d := by nlinarith
  by_contra hcon
  push Not at hcon
  have h4 : hb * sb * (1 + (Mm - 1) * d) < (1 - (Mm + 1) * d) * (1 + (Mm - 1) * d) :=
    mul_lt_mul_of_pos_right hcon hpos
  have h5 : (1 - (Mm + 1) * d) * (1 + (Mm - 1) * d) ≤ 1 - d := by
    have hMsq : (1 : ℝ) ≤ Mm * Mm := by nlinarith
    have hprod : (0 : ℝ) ≤ (Mm * Mm - 1) * (d * d) :=
      mul_nonneg (by linarith) (mul_nonneg hd0 hd0)
    nlinarith
  linarith

/-! ## 4. The arithmetic of the constants (Appendix A) -/

/-- **The final arithmetic**: a dominating tower of mass `≥ 1 - (M+1)δ` in a base of length
`L ≤ min (1/(2N₀)) ε` gives `h_b ≥ N₀`, a set of measure `≥ 1 - ε` and `|t| ≤ δ L ≤ ε`. -/
private theorem rigid_arith {L s hb ε : ℝ} {M N₀ : ℕ}
    (hM : 1 < M) (hε : 0 < ε) (hε1 : ε ≤ 1) (hN₀ : 1 ≤ N₀)
    (hL : 0 < L) (hs : 0 < s) (hsL : s ≤ L) (hLle : L ≤ 1 / (2 * (N₀ : ℝ)))
    (hLε : L ≤ ε)
    (htower : 1 - ((M : ℝ) + 1) * deltaOf ε M ≤ hb * s) :
    (N₀ : ℝ) ≤ hb ∧ 1 - ε ≤ (1 - 2 * deltaOf ε M) * (L * hb) ∧
      deltaOf ε M * L ≤ ε := by
  have hd0 : (0 : ℝ) ≤ deltaOf ε M := le_of_lt (deltaOf_pos hε M)
  have hd14 : deltaOf ε M ≤ 1 / 4 := deltaOf_le_quarter ε M
  have hδ8 : ((M : ℝ) + 1) * deltaOf ε M ≤ 1 / 8 := deltaOf_mul_succ_le hε1
  have hδ3 : ((M : ℝ) + 3) * deltaOf ε M ≤ ε := deltaOf_mul_add_three_le hε
  have hN1 : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀
  have hT : (0 : ℝ) < 2 * (N₀ : ℝ) := by linarith
  -- the dominating tower has mass at least `7/8`
  have h1 : 7 / 8 ≤ hb * s := by linarith
  have hb0 : 0 ≤ hb := by
    by_contra hc
    push Not at hc
    have hneg : hb * s < 0 := mul_neg_of_neg_of_pos hc hs
    linarith
  have h2 : 7 / 8 ≤ L * hb := by
    have hle : hb * s ≤ hb * L := mul_le_mul_of_nonneg_left hsL hb0
    linarith
  have h3 : hb * s ≤ hb * (1 / (2 * (N₀ : ℝ))) :=
    mul_le_mul_of_nonneg_left (le_trans hsL hLle) hb0
  have h4 : 7 / 8 ≤ hb * (1 / (2 * (N₀ : ℝ))) := le_trans h1 h3
  have h5 : hb * (1 / (2 * (N₀ : ℝ))) * (2 * (N₀ : ℝ)) = hb := by
    rw [one_div, mul_assoc, inv_mul_cancel₀ (ne_of_gt hT), mul_one]
  have h6 : (7 / 8) * (2 * (N₀ : ℝ)) ≤ hb := by
    have h := mul_le_mul_of_nonneg_right h4 hT.le
    rwa [h5] at h
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · have h7 : 1 - ((M : ℝ) + 1) * deltaOf ε M ≤ L * hb := by
      have hle : hb * s ≤ hb * L := mul_le_mul_of_nonneg_left hsL hb0
      linarith
    have h8 : (0 : ℝ) ≤ 1 - 2 * deltaOf ε M := by linarith
    have h9 : (1 - 2 * deltaOf ε M) * (1 - ((M : ℝ) + 1) * deltaOf ε M)
        ≤ (1 - 2 * deltaOf ε M) * (L * hb) := mul_le_mul_of_nonneg_left h7 h8
    have h10 : 1 - ε ≤ (1 - 2 * deltaOf ε M) * (1 - ((M : ℝ) + 1) * deltaOf ε M) := by
      have hsq : (0 : ℝ) ≤ deltaOf ε M * deltaOf ε M := mul_nonneg hd0 hd0
      have hM1 : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
      nlinarith [hδ3, mul_nonneg hM1 hsq]
    linarith
  · have h11 : deltaOf ε M * L ≤ (1 / 4) * ε :=
      mul_le_mul hd14 hLε (le_of_lt hL) (by norm_num)
    linarith

/-! ## 5. The rigid step -/

/-- **The rigid step.**  At a node `γ` of an `IterOK` word whose `b`-cell occupies at least
`1 - deltaOf ε M` of the base, whose tower heights are dominated by the height of `b` with constant
`M`, and whose base is shorter than both `ε` and `1/(2N₀)`, the exchange `T = P.toIET lam` is, after
`q = height P γ b ≥ N₀` steps, the exact translation `x ↦ x + t` with `|t| ≤ ε` on a measurable set
`B ⊆ [0,1)` of measure at least `1 - ε`.

The hypothesis `hstop` is carried by the statement but is not used by the proof: the tower
statements at a single node need `IterOK P lam γ` only (`Rigidity/RigidSet.lean`). -/
theorem rigid_step {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {ε : ℝ} (hε : 0 < ε) {N₀ : ℕ}
    {lam : α → ℝ≥0} (hlam : lam ∈ simplexOn α)
    (hstop : ∀ γ : List Bool, lam ∉ IETDatum₂.cylStop P γ)
    {γ : List Bool} {b : α} {M : ℕ} (hM : 1 < M)
    (hOK : TowerTrue.IterOK P lam γ)
    (hbig : BigCell P γ lam (deltaOf ε M) b)
    (hdom : ∀ c, height P γ c ≤ M * height P γ b)
    (hΛ : baseLen P γ lam ≤ min ε (1 / (2 * (N₀ : ℝ)))) :
    ∃ (q : ℕ) (t : ℝ) (B : Set ℝ),
      N₀ ≤ q ∧ |t| ≤ ε ∧ B ⊆ Set.Ico (0:ℝ) 1 ∧ MeasurableSet B ∧
      1 - ε ≤ (volume B).toReal ∧
      ∀ x ∈ B, (⇑(P.toIET lam))^[q] x = x + t := by
  classical
  -- `hstop` is part of the interface, but the proof does not need it
  have _hstop := hstop
  rcases lt_or_ge 1 ε with hε1 | hε1
  · refine ⟨N₀, 0, ∅, le_rfl, ?_, Set.empty_subset _, MeasurableSet.empty, ?_, ?_⟩
    · rw [abs_zero]
      linarith
    · rw [measure_empty, ENNReal.toReal_zero]
      linarith
    · intro x hx
      exact absurd hx (Set.notMem_empty x)
  · -- from now on `0 < ε < 1`
    have hLε : baseLen P γ lam ≤ ε := le_trans hΛ (min_le_left _ _)
    have hLle : baseLen P γ lam ≤ 1 / (2 * (N₀ : ℝ)) := le_trans hΛ (min_le_right _ _)
    have hLpos : 0 < baseLen P γ lam := baseLen_pos P hP hn hlam hOK
    rcases Nat.eq_zero_or_pos N₀ with hN0 | hN0
    · -- `N₀ = 0` contradicts the shortness of the base
      exfalso
      rw [hN0] at hLle
      simp only [Nat.cast_zero, mul_zero, div_zero] at hLle
      linarith
    -- the `b`-th cell has a positive length, and is at most the whole base
    have hbig' : (1 - deltaOf ε M) * baseLen P γ lam ≤ (Tower.lamAfter P γ lam b : ℝ) := hbig
    have hsb : 0 < (Tower.lamAfter P γ lam b : ℝ) := by
      have h1 : (0 : ℝ) < 1 - deltaOf ε M := by linarith [deltaOf_le_quarter ε M]
      have h2 : 0 < (1 - deltaOf ε M) * baseLen P γ lam := mul_pos h1 hLpos
      linarith
    have hsbL : (Tower.lamAfter P γ lam b : ℝ) ≤ baseLen P γ lam := by
      have h1 : (Tower.lamAfter P γ lam b : ℝ) ≤ ∑ c, (Tower.lamAfter P γ lam c : ℝ) :=
        Finset.single_le_sum (f := fun c => (Tower.lamAfter P γ lam c : ℝ))
          (fun c _ => (Tower.lamAfter P γ lam c).coe_nonneg) (Finset.mem_univ b)
      have h2 : baseLen P γ lam = ∑ c, (Tower.lamAfter P γ lam c : ℝ) := rfl
      linarith
    -- the total mass, split at `b`
    have hmass : (∑ c, (height P γ c : ℝ) * (Tower.lamAfter P γ lam c : ℝ)) = 1 :=
      total_mass P hP hn hlam hOK
    have hsplit : (height P γ b : ℝ) * (Tower.lamAfter P γ lam b : ℝ)
        + (∑ c ∈ Finset.univ.erase b,
          (height P γ c : ℝ) * (Tower.lamAfter P γ lam c : ℝ)) = 1 := by
      have h := Finset.sum_erase_add (Finset.univ : Finset α)
        (fun c => (height P γ c : ℝ) * (Tower.lamAfter P γ lam c : ℝ)) (Finset.mem_univ b)
      linarith [hmass]
    have hRle : (∑ c ∈ Finset.univ.erase b,
          (height P γ c : ℝ) * (Tower.lamAfter P γ lam c : ℝ))
        ≤ (M : ℝ) * (height P γ b : ℝ)
          * (baseLen P γ lam - (Tower.lamAfter P γ lam b : ℝ)) := by
      have hstep : ∀ c ∈ Finset.univ.erase b,
          (height P γ c : ℝ) * (Tower.lamAfter P γ lam c : ℝ)
            ≤ ((M : ℝ) * (height P γ b : ℝ)) * (Tower.lamAfter P γ lam c : ℝ) := by
        intro c _
        have hc : (height P γ c : ℝ) ≤ (M : ℝ) * (height P γ b : ℝ) := by
          exact_mod_cast hdom c
        exact mul_le_mul_of_nonneg_right hc (Tower.lamAfter P γ lam c).coe_nonneg
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.mul_sum]
      have hsum : (∑ c ∈ Finset.univ.erase b, (Tower.lamAfter P γ lam c : ℝ))
          = baseLen P γ lam - (Tower.lamAfter P γ lam b : ℝ) := by
        have h1 := Finset.sum_erase_add (Finset.univ : Finset α)
          (fun c => (Tower.lamAfter P γ lam c : ℝ)) (Finset.mem_univ b)
        have h2 : (∑ c, (Tower.lamAfter P γ lam c : ℝ)) = baseLen P γ lam := rfl
        linarith
      rw [hsum]
    -- the `b`-th tower dominates the mass
    have hb0 : (0 : ℝ) ≤ (height P γ b : ℝ) := Nat.cast_nonneg _
    have htower : 1 - ((M : ℝ) + 1) * deltaOf ε M
        ≤ (height P γ b : ℝ) * (Tower.lamAfter P γ lam b : ℝ) :=
      tower_bound (hb := (height P γ b : ℝ)) (sb := (Tower.lamAfter P γ lam b : ℝ))
        (L := baseLen P γ lam) (d := deltaOf ε M) (Mm := (M : ℝ))
        (R := ∑ c ∈ Finset.univ.erase b, (height P γ c : ℝ) * (Tower.lamAfter P γ lam c : ℝ))
        (by exact_mod_cast Nat.le_of_lt hM) (le_of_lt (deltaOf_pos hε M))
        (deltaOf_le_quarter ε M) hb0 hbig' hRle hsplit
    -- the rigid set of `RigidSet`, and the arithmetic of the constants
    obtain ⟨t, B, hBsub, hBmeas, hBvol, htle, hexact⟩ :=
      exists_rigid_set P hP hn hlam (deltaOf_pos hε M) (deltaOf_le_quarter ε M) hOK hbig
    obtain ⟨hq, hvol, ht⟩ := rigid_arith (L := baseLen P γ lam)
      (s := (Tower.lamAfter P γ lam b : ℝ)) (hb := (height P γ b : ℝ)) (ε := ε) (M := M)
      (N₀ := N₀) hM hε hε1 hN0 hLpos hsb hsbL hLle hLε htower
    refine ⟨height P γ b, t, B, ?_, ?_, hBsub, hBmeas, ?_, hexact⟩
    · exact_mod_cast hq
    · linarith
    · linarith

end Internal
end IETFree.Rigidity
