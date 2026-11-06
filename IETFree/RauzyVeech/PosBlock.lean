/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.ColDiam

/-!
# The algebra of the positive-block contraction

This file proves the two inequalities on the *spread* of the normalised columns of the
Rauzy–Veech path matrix that drive the "positive blocks imply unique ergodicity" argument
(`IETFree/RauzyVeech/PosBlocks.lean`):

* `PosBlock.spread_append_le` — appending letters never increases the spread;
* `PosBlock.spread_append_contract` — appending a *positive block* whose path matrix has
  entries in `[1, M]` multiplies the spread by at most `1 - 1/(d·M)`, `d = #α`.

Both rest on the mixing identity `PosBlock.ncol_append_apply`: every normalised column of
`Q(γδ)` is a convex combination of the normalised columns of `Q(γ)`, with weights
`θ_c = Q_γ(δ)_{cb} h_c / h'_b` (`h` the heights, i.e. the column sums).
The contraction also uses that, at a letter `a₀` of *maximal* height `h_{a₀}`, both weight
vectors put mass at least `1/(d·M)` on `a₀`; the total variation of the two weight vectors is
then at most `1 - 1/(d·M)`, and the spread bounds the range of `a ↦ ncol P γ · a`.  In
particular **no balanced-heights hypothesis is needed**: using the maximal height (not the
minimal one) is what removes it.

The dictionary to the geometry is `ColShrink.diam_le_of_cols_close`, read through `spread`: the
diameter of the cylinder is at most twice the spread of the normalised columns.

No measure theory is involved.  The peeling of the blocks along a greedy path is
`IETFree/RauzyVeech/Peel.lean`; the assembly is
 `IETFree/RauzyVeech/PosBlocks.lean`.
-/

@[expose] public section


open scoped BigOperators NNReal

namespace PosBlock

variable {α : Type*} [Fintype α] {n : ℕ} [NeZero n]

/-! ## 1. Total variation of two probability weights -/

/-- **Total variation bound under a shared atom.**  If two probability weights `θ`, `θ'` both
give mass at least `p` to the same letter `a`, their total variation
`∑_{θ' < θ} (θ - θ')` is at most `1 - p`. -/
theorem beta_le_of_mass {θ θ' : α → ℝ} (hθ0 : ∀ c, 0 ≤ θ c)
    (hθ'0 : ∀ c, 0 ≤ θ' c) (hθ : ∑ c, θ c = 1) {a : α} {p : ℝ}
    (ha : p ≤ θ a) (ha' : p ≤ θ' a) :
    ∑ c ∈ Finset.univ.filter (fun c => θ' c < θ c), (θ c - θ' c) ≤ 1 - p := by
  classical
  set S := Finset.univ.filter (fun c => θ' c < θ c) with hS
  have hSθ : ∑ c ∈ S, θ c ≤ 1 := by
    rw [← hθ]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun c _ _ => hθ0 c)
  have hSθ' : 0 ≤ ∑ c ∈ S, θ' c := Finset.sum_nonneg fun c _ => hθ'0 c
  rw [Finset.sum_sub_distrib]
  by_cases hmem : a ∈ S
  · have hle : θ' a ≤ ∑ c ∈ S, θ' c :=
      Finset.single_le_sum (f := θ') (fun c _ => hθ'0 c) hmem
    linarith
  · have hSa : θ a ≤ θ' a := by
      by_contra hcon
      push Not at hcon
      exact hmem (by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ a, hcon⟩)
    have hcompl : a ∈ Sᶜ := Finset.mem_compl.mpr hmem
    have hle : θ a ≤ ∑ c ∈ Sᶜ, θ c :=
      Finset.single_le_sum (f := θ) (fun c _ => hθ0 c) hcompl
    have hsplit : (∑ c ∈ S, θ c) + (∑ c ∈ Sᶜ, θ c) = 1 := by
      rw [Finset.sum_add_sum_compl, hθ]
    linarith

/-! ## 2. The mixing weights -/

section MixW

variable [DecidableEq α]

/-- The column sums of `Q(γ++δ)` are obtained from those of `Q(γ)` by the matrix `Q_γ(δ)`:
`h'_b = ∑_c Q_γ(δ)_{cb} h_c`. -/
theorem cs_append (P : IETDatum₂ α n) (γ δ : List Bool) (b : α) :
    ColShrink.cs P (γ ++ δ) b
      = ∑ c, (IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ c b : ℝ) * ColShrink.cs P γ c := by
  simp only [ColShrink.cs, IETDatum₂.Path.Q_append, Matrix.mul_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The weights expressing the `b`-th normalised column of `Q(γδ)` as a convex combination of those
of `Q(γ)`: `θ_c = Q_γ(δ)_{cb} · h_c / h'_b`, where `h` are the heights of `Q(γ)` and `h'`
those of `Q(γδ)`. -/
noncomputable def mixW (P : IETDatum₂ α n) (γ δ : List Bool) (b : α) : α → ℝ :=
  fun c => (IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ c b : ℝ) * ColShrink.cs P γ c
    / ColShrink.cs P (γ ++ δ) b

theorem mixW_nonneg (P : IETDatum₂ α n) (γ δ : List Bool) (b c : α) :
    0 ≤ mixW P γ δ b c :=
  div_nonneg
    (mul_nonneg (by exact_mod_cast IETDatum₂.Path.Q_nonneg _ _ c b)
      (le_of_lt (ColShrink.cs_pos P γ c)))
    (le_of_lt (ColShrink.cs_pos P (γ ++ δ) b))

/-- The mixing weights are a probability vector. -/
theorem mixW_sum (P : IETDatum₂ α n) (γ δ : List Bool) (b : α) :
    ∑ c, mixW P γ δ b c = 1 := by
  simp only [mixW]
  rw [← Finset.sum_div, ← cs_append, div_self (ColShrink.cs_ne_zero P (γ ++ δ) b)]

/-- **Mixing identity, pointwise form.**  The `b`-th normalised column of `Q(γ++δ)` is the convex
combination of the normalised columns of `Q(γ)` given by the weights `mixW`. -/
theorem ncol_append_apply (P : IETDatum₂ α n) (γ δ : List Bool) (b a : α) :
    ColShrink.ncol P (γ ++ δ) b a
      = ∑ c, mixW P γ δ b c * ColShrink.ncol P γ c a := by
  have hterm (c : α) :
    mixW P γ δ b c * ColShrink.ncol P γ c a
      = ((IETDatum₂.Path.Q P γ a c : ℝ)
          * (IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ c b : ℝ))
        / ColShrink.cs P (γ ++ δ) b := by
    have hc := ColShrink.cs_ne_zero P γ c
    simp only [mixW, ColShrink.ncol]
    field_simp
  rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.sum_div]
  rw [ColShrink.ncol, ColShrink.cs, IETDatum₂.Path.Q_append, Matrix.mul_apply]
  push_cast
  refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
  ring

end MixW

/-! ## 3. The weighted-sum bound -/

section Weighted

variable [Nonempty α]

/-- **Bound for a difference of two weighted sums.**  If `θ` and `θ'` have the same total mass
and the range of `v` is at most `s`, the difference of the weighted sums is at most `s` times the
total variation `∑_{θ' < θ} (θ - θ')` of the two weights. -/
theorem abs_sum_sub_mul_le {θ θ' : α → ℝ} (hsum : ∑ c, θ c = ∑ c, θ' c)
    {v : α → ℝ} {s : ℝ} (hs : ∀ c c', |v c - v c'| ≤ s) :
    |∑ c, θ c * v c - ∑ c, θ' c * v c|
      ≤ s * ∑ c ∈ Finset.univ.filter (fun c => θ' c < θ c), (θ c - θ' c) := by
  obtain ⟨c₀, -, hc₀⟩ :=
    Finset.exists_max_image (Finset.univ : Finset α) v Finset.univ_nonempty
  have hsum0 : ∑ c, (θ c - θ' c) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  have hw0 (c) : v c - v c₀ ≤ 0 := by
    have h := hc₀ c (Finset.mem_univ c); linarith
  have hws (c) : -s ≤ v c - v c₀ := by
    have h := hs c c₀; rw [abs_le] at h; linarith
  have hkey : ∑ c, θ c * v c - ∑ c, θ' c * v c
      = ∑ c, (θ c - θ' c) * (v c - v c₀) := by
    have hL : ∑ c, θ c * v c - ∑ c, θ' c * v c = ∑ c, (θ c - θ' c) * v c := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    have hR : ∑ c, (θ c - θ' c) * (v c - v c₀) = ∑ c, (θ c - θ' c) * v c := by
      have h1 : ∑ c, (θ c - θ' c) * (v c - v c₀)
          = ∑ c, (θ c - θ' c) * v c - ∑ c, (θ c - θ' c) * v c₀ := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun c _ => by ring
      have h2 : ∑ c, (θ c - θ' c) * v c₀ = 0 := by
        rw [← Finset.sum_mul, hsum0, zero_mul]
      rw [h1, h2, sub_zero]
    rw [hL, hR]
  set S := Finset.univ.filter (fun c => θ' c < θ c) with hS
  set T := Finset.univ.filter (fun c => ¬ (θ' c < θ c)) with hT
  have hbS (c) (hc : c ∈ S) : 0 < θ c - θ' c := by
    rw [hS, Finset.mem_filter] at hc
    linarith [hc.2]
  have hbT (c) (hc : c ∈ T) : θ c - θ' c ≤ 0 := by
    rw [hT, Finset.mem_filter] at hc
    linarith [hc.2]
  have hsplit : (∑ c ∈ S, (θ c - θ' c)) + (∑ c ∈ T, (θ c - θ' c)) = 0 := by
    rw [hS, hT, Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun c => θ' c < θ c) (f := fun c => θ c - θ' c), hsum0]
  have hwsplit : (∑ c ∈ S, (θ c - θ' c) * (v c - v c₀))
      + (∑ c ∈ T, (θ c - θ' c) * (v c - v c₀))
      = ∑ c, (θ c - θ' c) * (v c - v c₀) := by
    rw [hS, hT, Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun c => θ' c < θ c) (f := fun c => (θ c - θ' c) * (v c - v c₀))]
  have hSle : ∑ c ∈ S, (θ c - θ' c) * (v c - v c₀) ≤ 0 :=
    Finset.sum_nonpos fun c hc =>
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hbS c hc)) (hw0 c)
  have hSge : -s * (∑ c ∈ S, (θ c - θ' c))
      ≤ ∑ c ∈ S, (θ c - θ' c) * (v c - v c₀) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have h1 : 0 ≤ θ c - θ' c := le_of_lt (hbS c hc)
    have h2 : -s ≤ v c - v c₀ := hws c
    have h3 := mul_le_mul_of_nonneg_left h2 h1
    rw [mul_neg] at h3
    rw [show -s * (θ c - θ' c) = -((θ c - θ' c) * s) from by ring]
    exact h3
  have hTle : ∑ c ∈ T, (θ c - θ' c) * (v c - v c₀)
      ≤ -s * (∑ c ∈ T, (θ c - θ' c)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have h1 : θ c - θ' c ≤ 0 := hbT c hc
    have h2 : -s ≤ v c - v c₀ := hws c
    have h3 := mul_le_mul_of_nonpos_left h2 h1
    rw [mul_neg] at h3
    rw [show -s * (θ c - θ' c) = -((θ c - θ' c) * s) from by ring]
    exact h3
  have hTge : 0 ≤ ∑ c ∈ T, (θ c - θ' c) * (v c - v c₀) :=
    Finset.sum_nonneg fun c hc => mul_nonneg_of_nonpos_of_nonpos (hbT c hc) (hw0 c)
  set β := ∑ c ∈ S, (θ c - θ' c) with hβ
  have hTsum : ∑ c ∈ T, (θ c - θ' c) = -β := by rw [hβ]; linarith
  have hTle' : ∑ c ∈ T, (θ c - θ' c) * (v c - v c₀) ≤ s * β := by
    rw [hTsum, neg_mul_neg] at hTle
    exact hTle
  rw [hkey, ← hwsplit, abs_le]
  constructor <;> linarith

end Weighted

/-! ## 4. The spread and its behaviour under appending -/

section Spread

variable [DecidableEq α] [Nonempty α]

/-- The **spread** of the normalised columns of `Q(γ)`: the largest difference between two
entries of two normalised columns.  It bounds the diameter of the cylinder `Δ(γ)`
(`ColShrink.diam_le_of_cols_close`). -/
noncomputable def spread (P : IETDatum₂ α n) (γ : List Bool) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty (α := α × α × α))
    (fun p : α × α × α =>
      |ColShrink.ncol P γ p.1 p.2.2 - ColShrink.ncol P γ p.2.1 p.2.2|)

theorem le_spread (P : IETDatum₂ α n) (γ : List Bool) (b b' a : α) :
    |ColShrink.ncol P γ b a - ColShrink.ncol P γ b' a| ≤ spread P γ := by
  refine Finset.le_sup' (f := fun p : α × α × α =>
    |ColShrink.ncol P γ p.1 p.2.2 - ColShrink.ncol P γ p.2.1 p.2.2|)
    (Finset.mem_univ (b, b', a))

theorem spread_nonneg (P : IETDatum₂ α n) (γ : List Bool) : 0 ≤ spread P γ := by
  have h := le_spread P γ (Classical.arbitrary α) (Classical.arbitrary α)
    (Classical.arbitrary α)
  simpa using h

/-- **Pointwise contraction.** If both mixing weights of `b` and `b'` give mass at least `p` to the
letter `a₀`, the corresponding entries of the normalised columns of `Q(γδ)` are within `(1 - p) ·
spread P γ`. -/
theorem abs_ncol_append_le (P : IETDatum₂ α n) (γ δ : List Bool) (a₀ : α) {p : ℝ}
    (hmass : ∀ b, p ≤ mixW P γ δ b a₀) (b b' a : α) :
    |ColShrink.ncol P (γ ++ δ) b a - ColShrink.ncol P (γ ++ δ) b' a|
      ≤ (1 - p) * spread P γ := by
  have hb : ∑ c, mixW P γ δ b c = 1 := mixW_sum P γ δ b
  have hb' : ∑ c, mixW P γ δ b' c = 1 := mixW_sum P γ δ b'
  have h := abs_sum_sub_mul_le (θ := mixW P γ δ b) (θ' := mixW P γ δ b')
    (by rw [hb, hb']) (v := fun c => ColShrink.ncol P γ c a) (s := spread P γ)
    (fun c c' => le_spread P γ c c' a)
  have hβ : ∑ c ∈ Finset.univ.filter (fun c => mixW P γ δ b' c < mixW P γ δ b c),
      (mixW P γ δ b c - mixW P γ δ b' c) ≤ 1 - p :=
    beta_le_of_mass (fun c => mixW_nonneg P γ δ b c) (fun c => mixW_nonneg P γ δ b' c) hb
      (hmass b) (hmass b')
  rw [ncol_append_apply P γ δ b a, ncol_append_apply P γ δ b' a]
  refine h.trans ?_
  calc spread P γ * ∑ c ∈ Finset.univ.filter (fun c => mixW P γ δ b' c < mixW P γ δ b c),
        (mixW P γ δ b c - mixW P γ δ b' c)
      ≤ spread P γ * (1 - p) := mul_le_mul_of_nonneg_left hβ (spread_nonneg P γ)
    _ = (1 - p) * spread P γ := by ring

/-- **Monotonicity of the spread.**  Appending letters never increases the spread. -/
theorem spread_append_le (P : IETDatum₂ α n) (γ δ : List Bool) :
    spread P (γ ++ δ) ≤ spread P γ := by
  refine Finset.sup'_le _ _ fun q _ => ?_
  have h := abs_ncol_append_le P γ δ (Classical.arbitrary α) (p := 0)
    (fun b => mixW_nonneg P γ δ b _) q.1 q.2.1 q.2.2
  simpa using h

/-- **Contraction of the spread by a positive block.** If the path matrix `Q_γ(δ)` of `δ` at `vertex
P γ` has all entries in `[1, M]`, appending `δ` multiplies the spread by at most `1 - 1/(d·M)`, `d =
#α`. -/
theorem spread_append_contract (P : IETDatum₂ α n) (γ δ : List Bool) {M : ℕ} (hM : 1 ≤ M)
    (h1 : ∀ a b, 1 ≤ IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ a b)
    (h2 : ∀ a b, IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ a b ≤ (M : ℤ)) :
    spread P (γ ++ δ) ≤ (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) * spread P γ := by
  obtain ⟨a₀, -, ha₀⟩ := Finset.exists_max_image (Finset.univ : Finset α)
    (fun c => ColShrink.cs P γ c) Finset.univ_nonempty
  have ha₀le (c) : ColShrink.cs P γ c ≤ ColShrink.cs P γ a₀ := ha₀ c (Finset.mem_univ c)
  have hcardpos : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hden : (0 : ℝ) < (Fintype.card α : ℝ) * (M : ℝ) := mul_pos hcardpos hMpos
  have hha : (0 : ℝ) < ColShrink.cs P γ a₀ := ColShrink.cs_pos P γ a₀
  have hmass (b) : 1 / ((Fintype.card α : ℝ) * (M : ℝ)) ≤ mixW P γ δ b a₀ := by
    have hQ1 : (1 : ℝ) ≤ (IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ a₀ b : ℝ) := by
      exact_mod_cast h1 a₀ b
    have hcsle : ColShrink.cs P (γ ++ δ) b
        ≤ (Fintype.card α : ℝ) * (M : ℝ) * ColShrink.cs P γ a₀ := by
      rw [cs_append]
      calc ∑ c, (IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ c b : ℝ) * ColShrink.cs P γ c
          ≤ ∑ _c : α, (M : ℝ) * ColShrink.cs P γ a₀ := by
            refine Finset.sum_le_sum fun c _ => ?_
            have hQ : (IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ c b : ℝ) ≤ (M : ℝ) := by
              exact_mod_cast h2 c b
            exact mul_le_mul hQ (ha₀le c) (ColShrink.cs_nonneg P γ c) (le_of_lt hMpos)
        _ = (Fintype.card α : ℝ) * (M : ℝ) * ColShrink.cs P γ a₀ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
    simp only [mixW]
    rw [le_div_iff₀ (ColShrink.cs_pos P (γ ++ δ) b)]
    calc 1 / ((Fintype.card α : ℝ) * (M : ℝ)) * ColShrink.cs P (γ ++ δ) b
        ≤ 1 / ((Fintype.card α : ℝ) * (M : ℝ))
            * ((Fintype.card α : ℝ) * (M : ℝ) * ColShrink.cs P γ a₀) :=
          mul_le_mul_of_nonneg_left hcsle (le_of_lt (one_div_pos.mpr hden))
      _ = ColShrink.cs P γ a₀ := by field_simp
      _ ≤ (IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ a₀ b : ℝ) * ColShrink.cs P γ a₀ :=
          le_mul_of_one_le_left (le_of_lt hha) hQ1
  refine Finset.sup'_le _ _ fun q _ => ?_
  exact abs_ncol_append_le P γ δ a₀ hmass q.1 q.2.1 q.2.2

end Spread

end PosBlock

end
