/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.Path

/-!
# Every letter is a name infinitely often along a Rauzy–Veech path

Proposition 4.3 of the source (p. 13): along a path of the Rauzy–Veech algorithm — with an
irreducibility hypothesis, which is *necessary*: on non-irreducible data the pivot can equal the
second-to-last position, the step is then the identity, and the algorithm degenerates to the
subtractive Euclidean algorithm on two letters, in which a third letter is never a name — every
letter is a *main name* infinitely often. Proof strategy:
* the lengths are non-increasing, coordinate by coordinate, and the total length drops at step `k`
  by the secondary length `λ_k(sec_k)`; hence `∑_k λ_k(sec_k) ≤ ∑_a λ_0(a) < ∞`;
* consequently a letter that is a main name only finitely often is a secondary name only finitely
  often (its length is eventually a constant `δ > 0`, and each secondary occurrence drops the total
  by `δ`), so that letter is eventually never the last letter of either order, and its two positions
  are eventually constant;
* such a letter is `Frozen`; the letters that are main names infinitely often are *active* (not
  `Frozen`). An active letter can never sit *below* a frozen one, in either order: if `b` (active)
  sits below `x` (frozen) in the `ε`-order, the block of positions below `x` is fixed (insertions,
  which happen just after the last letter of the other order, are always above `x`), so `b` is never
  the last letter of that order; each of its infinitely many occurrences as the main name then moves
  the last letter of that order to just after `b`, whence shifts `x` — contradiction;
* so, eventually, all frozen letters sit below all active letters in both orders.  If there were a
  frozen letter, the frozen letters would therefore occupy the first `|F|` positions of *both*
  orders, and the set of letters sitting there has cardinal `|F|`: a proper invariant initial
  segment for `perm`, contradicting irreducibility.
-/

@[expose] public section

open Filter
open scoped BigOperators NNReal

namespace MeshShrink

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 0. The path of the algorithm -/

/-- The vertex of the Rauzy–Veech algorithm at time `k`, for the sequence of types `γ`. -/
noncomputable def Vs (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) : IETDatum₂ α n :=
  IETDatum₂.vertexNat P γ k

omit [DecidableEq α] in
@[simp] theorem Vs_succ (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) :
    Vs P γ (k + 1) = IETDatum₂.rvStep (Vs P γ k) (γ k) := rfl

/-- The **main name** at time `k`: the letter that is last in the order `γ k`. -/
noncomputable def mn (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) : α :=
  (Vs P γ k).last (γ k)

/-- The **secondary name** at time `k`: the letter that is last in the order `!γ k`. -/
noncomputable def sc (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) : α :=
  (Vs P γ k).last (!γ k)

/-- The real-valued right hand side of the length recursion at time `k`. -/
noncomputable def nextR (lam : ℕ → α → ℝ≥0) (k : ℕ) (m s : α) (a : α) : ℝ :=
  if a = m then ((lam k a : ℝ) - (lam k s : ℝ)) else (lam k a)

/-- The hypothesis `hnext` in the form used throughout this file. -/
def HNext (P : IETDatum₂ α n) (γ : ℕ → Bool) (lam : ℕ → α → ℝ≥0) : Prop :=
  ∀ k, lam (k + 1) = fun a => Real.toNNReal (nextR lam k (mn P γ k) (sc P γ k) a)

/-- The hypothesis `htype` (the type rule). -/
def HType (P : IETDatum₂ α n) (γ : ℕ → Bool) (lam : ℕ → α → ℝ≥0) : Prop :=
  ∀ k, lam k (sc P γ k) < lam k (mn P γ k)

omit [DecidableEq α] in
theorem Vs_irreducible (P : IETDatum₂ α n) (γ : ℕ → Bool) (hP : P.Irreducible) (k : ℕ) :
    (Vs P γ k).Irreducible :=
  IETDatum₂.vertexNat_irreducible P γ hP k

/-! ## 1. The two last letters of a step are distinct -/

omit [DecidableEq α] in
theorem mn_ne_sc (P : IETDatum₂ α n) (γ : ℕ → Bool) (lam : ℕ → α → ℝ≥0)
    (hty : HType P γ lam) (k : ℕ) : mn P γ k ≠ sc P γ k := by
  intro h
  have hk := hty k
  rw [h] at hk
  exact lt_irrefl _ hk

/-! ## 2. Pointwise recursion of the lengths -/

theorem next_apply (P : IETDatum₂ α n) (γ : ℕ → Bool) (lam : ℕ → α → ℝ≥0)
    (hnxt : HNext P γ lam) (k : ℕ) (a : α) :
    lam (k + 1) a = Real.toNNReal (nextR lam k (mn P γ k) (sc P γ k) a) :=
  congrFun (hnxt k) a

/-- The length of a letter that is not the main name is unchanged. -/
theorem coe_next_of_ne (P : IETDatum₂ α n) (γ : ℕ → Bool) (lam : ℕ → α → ℝ≥0) (k : ℕ)
    (hnxt : HNext P γ lam) {a : α} (hne : a ≠ mn P γ k) :
    ((lam (k + 1) a : ℝ)) = ((lam k a : ℝ)) := by
  rw [next_apply P γ lam hnxt k a]
  show ((Real.toNNReal (nextR lam k (mn P γ k) (sc P γ k) a) : ℝ)) = ((lam k a : ℝ))
  rw [nextR, if_neg hne, Real.coe_toNNReal _ (NNReal.coe_nonneg _)]

/-- The length of the main name is decreased by the length of the secondary name. -/
theorem coe_next_main (P : IETDatum₂ α n) (γ : ℕ → Bool) (lam : ℕ → α → ℝ≥0) (k : ℕ)
    (hty : HType P γ lam) (hnxt : HNext P γ lam) :
    ((lam (k + 1) (mn P γ k) : ℝ)) =
      ((lam k (mn P γ k) : ℝ)) - ((lam k (sc P γ k) : ℝ)) := by
  rw [next_apply P γ lam hnxt k (mn P γ k)]
  show ((Real.toNNReal (nextR lam k (mn P γ k) (sc P γ k) (mn P γ k)) : ℝ)) = _
  rw [nextR, if_pos rfl, Real.coe_toNNReal _ (by have := hty k; linarith)]

/-! ## 3. The total length and its telescoping -/

/-- The total length drops by the secondary length. -/
theorem sum_next (P : IETDatum₂ α n) (γ : ℕ → Bool) (lam : ℕ → α → ℝ≥0)
    (hty : HType P γ lam) (hnxt : HNext P γ lam) (k : ℕ) :
    (∑ a, ((lam (k + 1) a : ℝ))) = (∑ a, ((lam k a : ℝ))) - ((lam k (sc P γ k) : ℝ)) := by
  have hterm (a : α) :
    ((lam (k + 1) a : ℝ)) =
      ((lam k a : ℝ)) - (if a = mn P γ k then ((lam k (sc P γ k) : ℝ)) else 0) := by
    by_cases h : a = mn P γ k
    · subst h
      rw [coe_next_main P γ lam k hty hnxt, if_pos rfl]
    · rw [coe_next_of_ne P γ lam k hnxt h, if_neg h, sub_zero]
  calc (∑ a, ((lam (k + 1) a : ℝ)))
      = ∑ a, (((lam k a : ℝ)) - (if a = mn P γ k then ((lam k (sc P γ k) : ℝ)) else 0)) :=
        Finset.sum_congr rfl fun a _ => hterm a
    _ = (∑ a, ((lam k a : ℝ))) -
          ∑ a, (if a = mn P γ k then ((lam k (sc P γ k) : ℝ)) else 0) := by
        rw [Finset.sum_sub_distrib]
    _ = (∑ a, ((lam k a : ℝ))) - ((lam k (sc P γ k) : ℝ)) := by
        rw [Finset.sum_ite_eq' Finset.univ (mn P γ k) (fun _ => ((lam k (sc P γ k) : ℝ))),
          if_pos (Finset.mem_univ _)]

omit [DecidableEq α] in
/-- The total length is nonnegative. -/
theorem sum_nonneg' (lam : ℕ → α → ℝ≥0) (k : ℕ) : (0 : ℝ) ≤ ∑ a, ((lam k a : ℝ)) :=
  Finset.sum_nonneg fun _a _ => NNReal.coe_nonneg _

/-- Telescoping: the total length at time `N` is the initial one minus the partial sums of the
secondary lengths. -/
theorem sum_eq_sub_partial (P : IETDatum₂ α n) (γ : ℕ → Bool) (lam : ℕ → α → ℝ≥0)
    (hty : HType P γ lam) (hnxt : HNext P γ lam) (N : ℕ) :
    (∑ a, ((lam N a : ℝ))) =
      (∑ a, ((lam 0 a : ℝ))) - ∑ k ∈ Finset.range N, ((lam k (sc P γ k) : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_next P γ lam hty hnxt N, ih, Finset.sum_range_succ]
    ring

/-- The partial sums of the secondary lengths are bounded by the initial total length. -/
theorem partial_sum_le (P : IETDatum₂ α n) (γ : ℕ → Bool) (lam : ℕ → α → ℝ≥0)
    (hty : HType P γ lam) (hnxt : HNext P γ lam) (N : ℕ) :
    ∑ k ∈ Finset.range N, ((lam k (sc P γ k) : ℝ)) ≤ (∑ a, ((lam 0 a : ℝ))) := by
  have h := sum_eq_sub_partial P γ lam hty hnxt N
  have h2 := sum_nonneg' lam N
  linarith

/-! ## 4. A monotone bounded sequence of naturals is eventually constant -/

theorem eventually_eq_of_monotone_bdd : ∀ (b : ℕ) (f : ℕ → ℕ), Monotone f → (∀ k, f k ≤ b) →
    ∃ N, ∀ k ≥ N, f k = f N
  | 0, f, _, hb => ⟨0, fun k _ => by
      have h1 := hb 0; have h2 := hb k; omega⟩
  | b + 1, f, hf, hb => by
    by_cases hex : ∃ k, f k = b + 1
    · obtain ⟨k, hk⟩ := hex
      refine ⟨k, fun j hj => ?_⟩
      have h1 := hb j
      have h2 : f k ≤ f j := hf hj
      omega
    · push Not at hex
      exact eventually_eq_of_monotone_bdd b f hf fun k => by
        have h1 := hb k; have h2 := hex k; omega

/-! ## 5. A letter that is eventually never the main name is eventually never a secondary name -/

/-- If `a` is not a main name after time `N₀`, its length is constant after `N₀`. -/
theorem coe_eq_of_not_main (P : IETDatum₂ α n) (γ : ℕ → Bool) (lam : ℕ → α → ℝ≥0)
    (hnxt : HNext P γ lam) {a : α} {N₀ : ℕ} (hN₀ : ∀ k ≥ N₀, mn P γ k ≠ a) {k : ℕ}
    (hk : N₀ ≤ k) : ((lam k a : ℝ)) = ((lam N₀ a : ℝ)) := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [coe_next_of_ne P γ lam k hnxt (fun h => hN₀ k hk h.symm), ih]

/-- The set of times `k < N` at which `a` is the secondary name, among `k ≥ N₀`. -/
noncomputable def cntSet (P : IETDatum₂ α n) (γ : ℕ → Bool) (a : α) (N₀ N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun k => N₀ ≤ k ∧ sc P γ k = a

theorem cntSet_mono (P : IETDatum₂ α n) (γ : ℕ → Bool) (a : α) (N₀ : ℕ) :
    Monotone (cntSet P γ a N₀) :=
  fun _N _M hNM => Finset.filter_subset_filter _ (Finset.range_mono hNM)

theorem cntSet_subset_range (P : IETDatum₂ α n) (γ : ℕ → Bool) (a : α) (N₀ N : ℕ) :
    cntSet P γ a N₀ N ⊆ Finset.range N := Finset.filter_subset _ _

theorem mem_cntSet (P : IETDatum₂ α n) (γ : ℕ → Bool) (a : α) {N₀ N k : ℕ} :
    k ∈ cntSet P γ a N₀ N ↔ k < N ∧ N₀ ≤ k ∧ sc P γ k = a := by
  simp [cntSet]

theorem cntSet_succ_of_mem (P : IETDatum₂ α n) (γ : ℕ → Bool) (a : α) {N₀ k : ℕ}
    (hk : N₀ ≤ k) (h : sc P γ k = a) :
    (cntSet P γ a N₀ (k + 1)).card = (cntSet P γ a N₀ k).card + 1 := by
  have hnot : k ∉ cntSet P γ a N₀ k := by
    rw [mem_cntSet]; exact fun h' => absurd h'.1 (Nat.lt_irrefl k)
  have hins : cntSet P γ a N₀ (k + 1) = insert k (cntSet P γ a N₀ k) := by
    ext j
    rw [mem_cntSet, Finset.mem_insert, mem_cntSet]
    constructor
    · rintro ⟨hj, hj₀, hjs⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | h'
      · exact Or.inr ⟨h', hj₀, hjs⟩
      · exact Or.inl h'
    · rintro (h' | ⟨hj, hj₀, hjs⟩)
      · subst h'
        exact ⟨by omega, hk, h⟩
      · exact ⟨by omega, hj₀, hjs⟩
  rw [hins, Finset.card_insert_of_notMem hnot]

/-- **A letter that is a main name only finitely often is a secondary name only finitely often.**
Its length is then eventually a positive constant `δ`, and each occurrence as the secondary name
drops the total length by `δ`, while the total length is bounded below by `0` and the partial sums
of the drops are bounded by the initial total length. -/
theorem eventually_sc_ne_of_eventually_mn_ne (P : IETDatum₂ α n) (γ : ℕ → Bool) (lam : ℕ → α → ℝ≥0)
    (hpos : ∀ k a, 0 < lam k a) (hty : HType P γ lam) (hnxt : HNext P γ lam)
    {a : α} {N₀ : ℕ} (hN₀ : ∀ k ≥ N₀, mn P γ k ≠ a) :
    ∀ᶠ k in atTop, sc P γ k ≠ a := by
  have hconst (k) (hk : k ≥ N₀) : ((lam k a : ℝ)) = ((lam N₀ a :
      ℝ)) := coe_eq_of_not_main P γ lam hnxt hN₀ hk
  have hδ : (0 : ℝ) < ((lam N₀ a : ℝ)) := NNReal.coe_pos.mpr (hpos N₀ a)
  -- the counting function is bounded
  have hcardmono : Monotone fun N => (cntSet P γ a N₀ N).card :=
    fun N M hNM => Finset.card_le_card (cntSet_mono P γ a N₀ hNM)
  have hbound (N) : (cntSet P γ a N₀ N).card ≤
      Nat.floor ((∑ a, ((lam 0 a : ℝ))) / ((lam N₀ a : ℝ)) + 1) := by
    have hsum_eq : ∑ k ∈ cntSet P γ a N₀ N, ((lam k (sc P γ k) : ℝ)) =
        ((cntSet P γ a N₀ N).card : ℝ) * ((lam N₀ a : ℝ)) := by
      have h1 (k) (hk : k ∈ cntSet P γ a N₀ N) : ((lam k (sc P γ k) : ℝ)) = ((lam N₀ a : ℝ)) := by
        rw [mem_cntSet] at hk
        obtain ⟨-, hk₀, hksc⟩ := hk
        rw [hksc]
        exact hconst k hk₀
      rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    have hle : ∑ k ∈ cntSet P γ a N₀ N, ((lam k (sc P γ k) : ℝ)) ≤
        ∑ k ∈ Finset.range N, ((lam k (sc P γ k) : ℝ)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (cntSet_subset_range P γ a N₀ N) ?_
      intro k _ _; exact NNReal.coe_nonneg _
    have hpartial := partial_sum_le P γ lam hty hnxt N
    have hmain : ((cntSet P γ a N₀ N).card : ℝ) * ((lam N₀ a : ℝ)) ≤
        (∑ a, ((lam 0 a : ℝ))) := by
      rw [← hsum_eq]
      linarith
    have hg' : ((cntSet P γ a N₀ N).card : ℝ) ≤
        (∑ a, ((lam 0 a : ℝ))) / ((lam N₀ a : ℝ)) := (le_div_iff₀ hδ).mpr hmain
    refine Nat.le_floor ?_
    linarith
  obtain ⟨N₁, hN₁⟩ := eventually_eq_of_monotone_bdd _ (fun N => (cntSet P γ a N₀ N).card)
    hcardmono hbound
  refine eventually_atTop.mpr ⟨max N₀ N₁, fun k hk => ?_⟩
  intro hksc
  have hkN₀ : N₀ ≤ k := le_trans (le_max_left _ _) hk
  have hkN₁ : N₁ ≤ k := le_trans (le_max_right _ _) hk
  have hstep := cntSet_succ_of_mem P γ a hkN₀ hksc
  have heq := hN₁ k hkN₁
  have heq2 := hN₁ (k + 1) (by omega)
  omega

/-! ## 6. Positions of the letters in the two orders -/

/-- Position of `a` in the top order at time `k`. -/
noncomputable def posT (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) (a : α) : ℕ :=
  ((Vs P γ k).piTop a).val

/-- Position of `a` in the bottom order at time `k`. -/
noncomputable def posB (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) (a : α) : ℕ :=
  ((Vs P γ k).piBottom a).val

omit [DecidableEq α] in
theorem posT_lt (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) (a : α) : posT P γ k a < n :=
  ((Vs P γ k).piTop a).isLt

omit [DecidableEq α] in
theorem posB_lt (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) (a : α) : posB P γ k a < n :=
  ((Vs P γ k).piBottom a).isLt

omit [DecidableEq α] in
theorem posT_inj (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) {a b : α}
    (h : posT P γ k a = posT P γ k b) : a = b :=
  (Vs P γ k).piTop.injective (Fin.ext h)

omit [DecidableEq α] in
theorem posB_inj (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) {a b : α}
    (h : posB P γ k a = posB P γ k b) : a = b :=
  (Vs P γ k).piBottom.injective (Fin.ext h)

omit [DecidableEq α] in
/-- The top order is unchanged by a step of type `true`. -/
theorem posT_succ_true (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) (hγ : γ k = true) (a : α) :
    posT P γ (k + 1) a = posT P γ k a := by
  simp only [posT, Vs_succ, hγ, IETDatum₂.rvStep_piTop_true]

omit [DecidableEq α] in
/-- The bottom order is unchanged by a step of type `false`. -/
theorem posB_succ_false (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) (hγ : γ k = false) (a : α) :
    posB P γ (k + 1) a = posB P γ k a := by
  simp only [posB, Vs_succ, hγ, IETDatum₂.rvStep_piBottom_false]

omit [DecidableEq α] in
/-- After a step of type `false`, a letter at a top position not above the pivot does not move. -/
theorem posT_succ_false_of_le (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) (hγ : γ k = false)
    {a : α} (ha : ((Vs P γ k).piTop a).val ≤ ((Vs P γ k).piTop (mn P γ k)).val) :
    posT P γ (k + 1) a = posT P γ k a := by
      classical
  have hmn : (Vs P γ k).last false = mn P γ k := by simp [mn, hγ]
  have h := IETDatum₂.rvStep_piTop_false_apply_val (Vs P γ k) a
  rw [hmn] at h
  rw [posT, Vs_succ, hγ, h, if_pos ha]
  rfl

omit [DecidableEq α] in
/-- After a step of type `false`, a letter strictly above the pivot and not the last letter of the
top order moves up by one. -/
theorem posT_succ_false_of_gt (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) (hγ : γ k = false)
    {a : α} (ha : ((Vs P γ k).piTop (mn P γ k)).val < ((Vs P γ k).piTop a).val)
    (hne : a ≠ (Vs P γ k).last true) :
    posT P γ (k + 1) a = posT P γ k a + 1 := by
      classical
  have hmn : (Vs P γ k).last false = mn P γ k := by simp [mn, hγ]
  have h := IETDatum₂.rvStep_piTop_false_apply_val (Vs P γ k) a
  rw [hmn] at h
  rw [posT, Vs_succ, hγ, h, if_neg (by omega), if_neg hne]
  rfl

omit [DecidableEq α] in
/-- After a step of type `true`, a letter at a bottom position not above the pivot does not move. -/
theorem posB_succ_true_of_le (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) (hγ : γ k = true)
    {a : α} (ha : ((Vs P γ k).piBottom a).val ≤ ((Vs P γ k).piBottom (mn P γ k)).val) :
    posB P γ (k + 1) a = posB P γ k a := by
      classical
  have hmn : (Vs P γ k).last true = mn P γ k := by simp [mn, hγ]
  have h := IETDatum₂.rvStep_piBottom_true_apply_val (Vs P γ k) a
  rw [hmn] at h
  rw [posB, Vs_succ, hγ, h, if_pos ha]
  rfl

omit [DecidableEq α] in
/-- After a step of type `true`, a letter strictly above the pivot and not the last letter of the
bottom order moves up by one. -/
theorem posB_succ_true_of_gt (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) (hγ : γ k = true)
    {a : α} (ha : ((Vs P γ k).piBottom (mn P γ k)).val < ((Vs P γ k).piBottom a).val)
    (hne : a ≠ (Vs P γ k).last false) :
    posB P γ (k + 1) a = posB P γ k a + 1 := by
      classical
  have hmn : (Vs P γ k).last true = mn P γ k := by simp [mn, hγ]
  have h := IETDatum₂.rvStep_piBottom_true_apply_val (Vs P γ k) a
  rw [hmn] at h
  rw [posB, Vs_succ, hγ, h, if_neg (by omega), if_neg hne]
  rfl

omit [DecidableEq α] in
/-- A letter that is the main name at a step of type `false` is the last letter of the bottom order.
-/
theorem eq_last_false_of_mn (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) (hγ : γ k = false)
    {y : α} (hy : mn P γ k = y) : y = (Vs P γ k).last false := by
  rw [← hy]; simp [mn, hγ]

omit [DecidableEq α] in
/-- A letter that is the main name at a step of type `true` is the last letter of the top order. -/
theorem eq_last_true_of_mn (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) (hγ : γ k = true)
    {y : α} (hy : mn P γ k = y) : y = (Vs P γ k).last true := by
  rw [← hy]; simp [mn, hγ]

omit [DecidableEq α] in
/-- A letter that is neither the main nor the secondary name is not the last letter of either order.
-/
theorem ne_last_true (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) {a : α}
    (h1 : mn P γ k ≠ a) (h2 : sc P γ k ≠ a) : a ≠ (Vs P γ k).last true := by
  intro h
  cases hγ : γ k
  · refine h2 ?_
    rw [sc, hγ]
    simpa using h.symm
  · refine h1 ?_
    rw [mn, hγ]
    simpa using h.symm

omit [DecidableEq α] in
theorem ne_last_false (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) {a : α}
    (h1 : mn P γ k ≠ a) (h2 : sc P γ k ≠ a) : a ≠ (Vs P γ k).last false := by
  intro h
  cases hγ : γ k
  · refine h1 ?_
    rw [mn, hγ]
    simpa using h.symm
  · refine h2 ?_
    rw [sc, hγ]
    simpa using h.symm

omit [DecidableEq α] in
/-- If `a` is never the last letter of either order after time `N`, its position in the top order is
non-decreasing. -/
theorem posT_le_succ (P : IETDatum₂ α n) (γ : ℕ → Bool) {a : α} {N k : ℕ}
    (hk : N ≤ k) (hz : ∀ j ≥ N, mn P γ j ≠ a ∧ sc P γ j ≠ a) :
    posT P γ k a ≤ posT P γ (k + 1) a := by
  obtain ⟨h1, h2⟩ := hz k hk
  cases hγ : γ k
  · by_cases hc : ((Vs P γ k).piTop a).val ≤ ((Vs P γ k).piTop (mn P γ k)).val
    · exact le_of_eq (posT_succ_false_of_le P γ k hγ hc).symm
    · rw [posT_succ_false_of_gt P γ k hγ (by omega) (ne_last_true P γ k h1 h2)]
      omega
  · exact le_of_eq (posT_succ_true P γ k hγ a).symm

omit [DecidableEq α] in
/-- If `a` is never the last letter of either order after time `N`, its position in the bottom order
is non-decreasing. -/
theorem posB_le_succ (P : IETDatum₂ α n) (γ : ℕ → Bool) {a : α} {N k : ℕ}
    (hk : N ≤ k) (hz : ∀ j ≥ N, mn P γ j ≠ a ∧ sc P γ j ≠ a) :
    posB P γ k a ≤ posB P γ (k + 1) a := by
  obtain ⟨h1, h2⟩ := hz k hk
  cases hγ : γ k
  · exact le_of_eq (posB_succ_false P γ k hγ a).symm
  · by_cases hc : ((Vs P γ k).piBottom a).val ≤ ((Vs P γ k).piBottom (mn P γ k)).val
    · exact le_of_eq (posB_succ_true_of_le P γ k hγ hc).symm
    · rw [posB_succ_true_of_gt P γ k hγ (by omega) (ne_last_false P γ k h1 h2)]
      omega

omit [DecidableEq α] in
/-- If `a` is never the last letter of either order after time `N`, its top position is
eventually constant. -/
theorem posT_eventually_const (P : IETDatum₂ α n) (γ : ℕ → Bool) {a : α} {N : ℕ}
    (hz : ∀ j ≥ N, mn P γ j ≠ a ∧ sc P γ j ≠ a) :
    ∃ v : ℕ, ∀ᶠ k in atTop, posT P γ k a = v := by
  have hmono : Monotone fun m => posT P γ (N + m) a := by
    intro m m' hmm
    obtain ⟨d, rfl⟩ : ∃ d, m' = m + d := ⟨m' - m, by omega⟩
    have hstep (e) : posT P γ (N + m) a ≤ posT P γ (N + m + e) a := by
      induction e with
      | zero => exact le_rfl
      | succ e ih =>
        exact le_trans ih (posT_le_succ P γ (a := a) (k := N + m + e) (by omega) hz)
    simpa [Nat.add_assoc] using hstep d
  obtain ⟨M, hM⟩ := eventually_eq_of_monotone_bdd n (fun m => posT P γ (N + m) a) hmono
    (fun m => le_of_lt (posT_lt P γ (N + m) a))
  refine ⟨posT P γ (N + M) a, eventually_atTop.mpr ⟨N + M, fun k hk => ?_⟩⟩
  have hkN : N ≤ k := by omega
  have h1 : posT P γ (N + (k - N)) a = posT P γ (N + M) a := hM (k - N) (by omega)
  rwa [Nat.add_sub_cancel' hkN] at h1

omit [DecidableEq α] in
/-- If `a` is never the last letter of either order after time `N`, its bottom position is
eventually constant. -/
theorem posB_eventually_const (P : IETDatum₂ α n) (γ : ℕ → Bool) {a : α} {N : ℕ}
    (hz : ∀ j ≥ N, mn P γ j ≠ a ∧ sc P γ j ≠ a) :
    ∃ v : ℕ, ∀ᶠ k in atTop, posB P γ k a = v := by
  have hmono : Monotone fun m => posB P γ (N + m) a := by
    intro m m' hmm
    obtain ⟨d, rfl⟩ : ∃ d, m' = m + d := ⟨m' - m, by omega⟩
    have hstep (e) : posB P γ (N + m) a ≤ posB P γ (N + m + e) a := by
      induction e with
      | zero => exact le_rfl
      | succ e ih =>
        exact le_trans ih (posB_le_succ P γ (a := a) (k := N + m + e) (by omega) hz)
    simpa [Nat.add_assoc] using hstep d
  obtain ⟨M, hM⟩ := eventually_eq_of_monotone_bdd n (fun m => posB P γ (N + m) a) hmono
    (fun m => le_of_lt (posB_lt P γ (N + m) a))
  refine ⟨posB P γ (N + M) a, eventually_atTop.mpr ⟨N + M, fun k hk => ?_⟩⟩
  have hkN : N ≤ k := by omega
  have h1 : posB P γ (N + (k - N)) a = posB P γ (N + M) a := hM (k - N) (by omega)
  rwa [Nat.add_sub_cancel' hkN] at h1

/-! ## 7. Frozen and active letters -/

/-- A letter is **frozen** if it is a main name only finitely often, i.e. if its length is
eventually constant. -/
def Frozen (P : IETDatum₂ α n) (γ : ℕ → Bool) (a : α) : Prop := ∀ᶠ k in atTop, mn P γ k ≠ a

/-- A frozen letter is eventually never the last letter of either order. -/
theorem frozen_never_top (P : IETDatum₂ α n) (γ : ℕ → Bool) (lam : ℕ → α → ℝ≥0)
    (hpos : ∀ k a, 0 < lam k a) (hty : HType P γ lam) (hnxt : HNext P γ lam) {a : α}
    (h : Frozen P γ a) : ∀ᶠ k in atTop, mn P γ k ≠ a ∧ sc P γ k ≠ a := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
  filter_upwards [h, eventually_sc_ne_of_eventually_mn_ne P γ lam hpos hty hnxt hN₀]
    with k h1 h2 using ⟨h1, h2⟩

/-! ## 8. The block below a frozen letter is fixed -/

omit [DecidableEq α] in
/-- If `x` is never a last letter after `N` and its top position is `vT` from `N` on, then every
letter sitting at a top position `≤ vT` at a time `k ≥ N` keeps that position forever. -/
theorem posT_fixed_of_le (P : IETDatum₂ α n) (γ : ℕ → Bool) {x : α} {N vT : ℕ}
    (hx : ∀ j ≥ N, mn P γ j ≠ x ∧ sc P γ j ≠ x)
    (hconst : ∀ j ≥ N, posT P γ j x = vT) {k : ℕ} (hk : N ≤ k) {y : α}
    (hy : posT P γ k y ≤ vT) : ∀ j ≥ k, posT P γ j y = posT P γ k y := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    have hjN : N ≤ j := le_trans hk hj
    have hq : posT P γ j y ≤ vT := by rw [ih]; exact hy
    obtain ⟨h1, h2⟩ := hx j hjN
    have hxq : posT P γ j x = vT := hconst j hjN
    have hxtop : x ≠ (Vs P γ j).last true := ne_last_true P γ j h1 h2
    cases hγ : γ j
    · -- a step of type `false`: the pivot is at or above `vT`
      have hpiv : vT ≤ ((Vs P γ j).piTop (mn P γ j)).val := by
        by_contra hlt
        push Not at hlt
        have hcontr := posT_succ_false_of_gt P γ j hγ (a := x)
          (by rw [show ((Vs P γ j).piTop x).val = vT from hxq]; exact hlt) hxtop
        have h2 : posT P γ (j + 1) x = vT := hconst (j + 1) (le_trans hjN (Nat.le_succ j))
        omega
      rw [posT_succ_false_of_le P γ j hγ (a := y) (le_trans hq hpiv)]
      exact ih
    · rw [posT_succ_true P γ j hγ y]
      exact ih

omit [DecidableEq α] in
/-- **An active letter cannot sit below a frozen one** (in the top order). -/
theorem frozen_lt_posT (P : IETDatum₂ α n) (γ : ℕ → Bool) {x : α} {N vT : ℕ} (hn : 2 ≤ n)
    (hx : ∀ j ≥ N, mn P γ j ≠ x ∧ sc P γ j ≠ x)
    (hconst : ∀ j ≥ N, posT P γ j x = vT) {y : α}
    (hy : ∃ᶠ k in atTop, mn P γ k = y) :
    ∀ᶠ k in atTop, posT P γ k x < posT P γ k y := by
  have hxtopN : x ≠ (Vs P γ N).last true := ne_last_true P γ N (hx N le_rfl).1 (hx N le_rfl).2
  have hvT : vT ≤ n - 2 := by
    have h1 : vT < n := by rw [← hconst N le_rfl]; exact posT_lt P γ N x
    have h2 : vT ≠ n - 1 := by
      intro h
      have h' : (Vs P γ N).piTop x = IETDatum₂.lastPos n := by
        apply Fin.ext
        rw [IETDatum₂.lastPos_val]
        exact (show ((Vs P γ N).piTop x).val = vT from hconst N le_rfl).trans h
      have h2 : x = (Vs P γ N).last true := by
        rw [IETDatum₂.last]
        simp only [if_true]
        rw [← h', Equiv.symm_apply_apply]
      exact hxtopN h2
    omega
  refine eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
  by_contra hcon
  push Not at hcon
  -- `y` sits at or below `vT`
  have hq : posT P γ k y ≤ vT := hcon.trans_eq (hconst k hk)
  have hfix := posT_fixed_of_le P γ hx hconst hk hq
  -- `y` is the main name at some time `j ≥ k`
  obtain ⟨j, hjy, hjk⟩ := (hy.and_eventually (eventually_ge_atTop k)).exists
  have hqj : posT P γ j y = posT P γ k y := hfix j hjk
  have hqtop : posT P γ j y ≤ n - 2 := by rw [hqj]; exact le_trans hq hvT
  have hytop : y ≠ (Vs P γ j).last true := by
    intro h
    have h1 : posT P γ j y = n - 1 := by
      rw [posT, h]
      simp [IETDatum₂.last_top, IETDatum₂.lastPos_val]
    omega
  have hγj : γ j = false := by
    cases h : γ j
    · rfl
    · exact absurd (eq_last_true_of_mn P γ j h hjy) hytop
  have hxq : posT P γ j x = vT := hconst j (le_trans hk hjk)
  have hxtop : x ≠ (Vs P γ j).last true :=
    ne_last_true P γ j (hx j (le_trans hk hjk)).1 (hx j (le_trans hk hjk)).2
  have hqjv : posT P γ j y ≤ vT := by rw [hqj]; exact hq
  have hpiv : (posT P γ j y) < posT P γ j x := by
    rw [hxq]
    rcases lt_or_eq_of_le hqjv with h' | h'
    · exact h'
    · exfalso
      have hxy : x = y := posT_inj P γ j (by rw [hxq, h'])
      rw [← hjy] at hxy
      exact (hx j (le_trans hk hjk)).1 hxy.symm
  have hcontr := posT_succ_false_of_gt P γ j hγj (a := x) (by rw [hjy]; exact hpiv) hxtop
  have h2 : posT P γ (j + 1) x = vT :=
    hconst (j + 1) (le_trans (le_trans hk hjk) (Nat.le_succ j))
  omega

omit [DecidableEq α] in
/-- The same statement for the bottom order. -/
theorem posB_fixed_of_le (P : IETDatum₂ α n) (γ : ℕ → Bool) {x : α} {N vB : ℕ}
    (hx : ∀ j ≥ N, mn P γ j ≠ x ∧ sc P γ j ≠ x)
    (hconst : ∀ j ≥ N, posB P γ j x = vB) {k : ℕ} (hk : N ≤ k) {y : α}
    (hy : posB P γ k y ≤ vB) : ∀ j ≥ k, posB P γ j y = posB P γ k y := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    have hjN : N ≤ j := le_trans hk hj
    have hq : posB P γ j y ≤ vB := by rw [ih]; exact hy
    obtain ⟨h1, h2⟩ := hx j hjN
    have hxq : posB P γ j x = vB := hconst j hjN
    have hxbot : x ≠ (Vs P γ j).last false := ne_last_false P γ j h1 h2
    cases hγ : γ j
    · rw [posB_succ_false P γ j hγ y]
      exact ih
    · have hpiv : vB ≤ ((Vs P γ j).piBottom (mn P γ j)).val := by
        by_contra hlt
        push Not at hlt
        have hcontr := posB_succ_true_of_gt P γ j hγ (a := x)
          (by rw [show ((Vs P γ j).piBottom x).val = vB from hxq]; exact hlt) hxbot
        have h2 : posB P γ (j + 1) x = vB := hconst (j + 1) (le_trans hjN (Nat.le_succ j))
        omega
      rw [posB_succ_true_of_le P γ j hγ (a := y) (le_trans hq hpiv)]
      exact ih

omit [DecidableEq α] in
/-- **An active letter cannot sit below a frozen one** (in the bottom order). -/
theorem frozen_lt_posB (P : IETDatum₂ α n) (γ : ℕ → Bool) {x : α} {N vB : ℕ} (hn : 2 ≤ n)
    (hx : ∀ j ≥ N, mn P γ j ≠ x ∧ sc P γ j ≠ x)
    (hconst : ∀ j ≥ N, posB P γ j x = vB) {y : α}
    (hy : ∃ᶠ k in atTop, mn P γ k = y) :
    ∀ᶠ k in atTop, posB P γ k x < posB P γ k y := by
  have hxbotN : x ≠ (Vs P γ N).last false := ne_last_false P γ N (hx N le_rfl).1 (hx N le_rfl).2
  have hvB : vB ≤ n - 2 := by
    have h1 : vB < n := by rw [← hconst N le_rfl]; exact posB_lt P γ N x
    have h2 : vB ≠ n - 1 := by
      intro h
      have h' : (Vs P γ N).piBottom x = IETDatum₂.lastPos n := by
        apply Fin.ext
        rw [IETDatum₂.lastPos_val]
        exact (show ((Vs P γ N).piBottom x).val = vB from hconst N le_rfl).trans h
      have h2 : x = (Vs P γ N).last false := by
        rw [IETDatum₂.last]
        simp only [Bool.false_eq_true, if_false]
        rw [← h', Equiv.symm_apply_apply]
      exact hxbotN h2
    omega
  refine eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
  by_contra hcon
  push Not at hcon
  have hq : posB P γ k y ≤ vB := hcon.trans_eq (hconst k hk)
  have hfix := posB_fixed_of_le P γ hx hconst hk hq
  obtain ⟨j, hjy, hjk⟩ := (hy.and_eventually (eventually_ge_atTop k)).exists
  have hqj : posB P γ j y = posB P γ k y := hfix j hjk
  have hqbot : posB P γ j y ≤ n - 2 := by rw [hqj]; exact le_trans hq hvB
  have hybot : y ≠ (Vs P γ j).last false := by
    intro h
    have h1 : posB P γ j y = n - 1 := by
      rw [posB, h]
      simp [IETDatum₂.last_bottom, IETDatum₂.lastPos_val]
    omega
  have hγj : γ j = true := by
    cases h : γ j
    · exact absurd (eq_last_false_of_mn P γ j h hjy) hybot
    · rfl
  have hxq : posB P γ j x = vB := hconst j (le_trans hk hjk)
  have hxbot : x ≠ (Vs P γ j).last false :=
    ne_last_false P γ j (hx j (le_trans hk hjk)).1 (hx j (le_trans hk hjk)).2
  have hqjv : posB P γ j y ≤ vB := by rw [hqj]; exact hq
  have hpiv : (posB P γ j y) < posB P γ j x := by
    rw [hxq]
    rcases lt_or_eq_of_le hqjv with h' | h'
    · exact h'
    · exfalso
      have hxy : x = y := posB_inj P γ j (by rw [hxq, h'])
      rw [← hjy] at hxy
      exact (hx j (le_trans hk hjk)).1 hxy.symm
  have hcontr := posB_succ_true_of_gt P γ j hγj (a := x) (by rw [hjy]; exact hpiv) hxbot
  have h2 : posB P γ (j + 1) x = vB :=
    hconst (j + 1) (le_trans (le_trans hk hjk) (Nat.le_succ j))
  omega

/-! ## 9. There is at least one active letter, and there are at least two letters -/

omit [DecidableEq α] in
/-- If `n = 1` the type rule is contradictory, so `2 ≤ n` under `htype`. -/
theorem two_le_of_htype (P : IETDatum₂ α n) (γ : ℕ → Bool) (lam : ℕ → α → ℝ≥0)
    (hty : HType P γ lam) : 2 ≤ n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · exfalso
    have hn1 : n = 1 := by have := NeZero.ne n; omega
    have hcard : Fintype.card α = 1 := by
      rw [Fintype.card_congr P.piTop, Fintype.card_fin]; exact hn1
    have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact mn_ne_sc P γ lam hty 0 (Subsingleton.elim _ _)
  · exact h

omit [DecidableEq α] in
/-- There is always an active letter (a letter that is a main name infinitely often). -/
theorem exists_not_frozen (P : IETDatum₂ α n) (γ : ℕ → Bool) : ∃ b, ¬ Frozen P γ b := by
  by_contra h
  push Not at h
  have hall : ∀ᶠ k in atTop, ∀ z : α, mn P γ k ≠ z := by
    rw [Filter.eventually_all]
    exact h
  obtain ⟨k, hk⟩ := hall.exists
  exact hk (mn P γ k) rfl

/-- Frozen letters sit below active letters in the top order. -/
theorem frozen_lt_posT' (P : IETDatum₂ α n) (γ : ℕ → Bool) (lam : ℕ → α → ℝ≥0)
    (hpos : ∀ k a, 0 < lam k a) (hty : HType P γ lam) (hnxt : HNext P γ lam) (hn : 2 ≤ n)
    {x y : α} (hx : Frozen P γ x) (hy : ¬ Frozen P γ y) :
    ∀ᶠ k in atTop, posT P γ k x < posT P γ k y := by
  have hyf : ∃ᶠ k in atTop, mn P γ k = y := by
    have h1 : ¬ ∀ᶠ k in atTop, ¬ (mn P γ k = y) := by
      simpa only [ne_eq, Frozen] using hy
    simpa using Filter.not_eventually.mp h1
  obtain ⟨N, hN⟩ := eventually_atTop.mp (frozen_never_top P γ lam hpos hty hnxt hx)
  obtain ⟨vT, hvT⟩ := posT_eventually_const P γ hN
  obtain ⟨N', hN'⟩ := eventually_atTop.mp hvT
  exact frozen_lt_posT (P := P) (γ := γ) (x := x) (y := y) (N := max N N') (vT := vT) hn
    (fun j hj => hN j (le_trans (le_max_left N N') hj))
    (fun j hj => hN' j (le_trans (le_max_right N N') hj)) hyf

/-- Frozen letters sit below active letters in the bottom order. -/
theorem frozen_lt_posB' (P : IETDatum₂ α n) (γ : ℕ → Bool) (lam : ℕ → α → ℝ≥0)
    (hpos : ∀ k a, 0 < lam k a) (hty : HType P γ lam) (hnxt : HNext P γ lam) (hn : 2 ≤ n)
    {x y : α} (hx : Frozen P γ x) (hy : ¬ Frozen P γ y) :
    ∀ᶠ k in atTop, posB P γ k x < posB P γ k y := by
  have hyf : ∃ᶠ k in atTop, mn P γ k = y := by
    have h1 : ¬ ∀ᶠ k in atTop, ¬ (mn P γ k = y) := by
      simpa only [ne_eq, Frozen] using hy
    simpa using Filter.not_eventually.mp h1
  obtain ⟨N, hN⟩ := eventually_atTop.mp (frozen_never_top P γ lam hpos hty hnxt hx)
  obtain ⟨vB, hvB⟩ := posB_eventually_const P γ hN
  obtain ⟨N', hN'⟩ := eventually_atTop.mp hvB
  exact frozen_lt_posB (P := P) (γ := γ) (x := x) (y := y) (N := max N N') (vB := vB) hn
    (fun j hj => hN j (le_trans (le_max_left N N') hj))
    (fun j hj => hN' j (le_trans (le_max_right N N') hj)) hyf

/-! ## 10. No proper initial segment is invariant -/

omit [NeZero n] [DecidableEq α] in
/-- The letters whose position in the order `e` is at most the maximum position over `S` are exactly
`S`, when all of `S` sits below its complement. -/
theorem low_eq_of (e : α ≃ Fin n) (S : Finset α) (hSne : S.Nonempty)
    (h : ∀ a ∈ S, ∀ b, b ∉ S → (e a).val < (e b).val) :
    (Finset.univ.filter fun a => (e a).val ≤ S.sup (fun a => (e a).val)) = S := by
  apply Finset.Subset.antisymm
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    by_contra hcon
    obtain ⟨s, hs⟩ := hSne
    have h1 : (e s).val < (e a).val := h s hs a hcon
    have h3 : S.sup (fun a => (e a).val) < (e a).val :=
      Finset.sup_lt_iff (by omega : (0:ℕ) < (e a).val) |>.mpr (fun b hb => h b hb a hcon)
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.le_sup (f := fun a => (e a).val) ha

omit [DecidableEq α] [Fintype α] in
/-- Cardinality of the block below the maximal position of `S`: it is `max + 1`. -/
theorem card_low_of (e : α ≃ Fin n) (S : Finset α) (hSne : S.Nonempty)
    (h : ∀ a ∈ S, ∀ b, b ∉ S → (e a).val < (e b).val) :
    S.card = S.sup (fun a => (e a).val) + 1 := by
  have : Fintype α := Fintype.ofEquiv (Fin n) e.symm
  have hLow := low_eq_of e S hSne h
  have himg : (Finset.univ.filter fun a => (e a).val ≤ S.sup (fun a => (e a).val)).image
      (fun a => (e a).val) = Finset.range (S.sup (fun a => (e a).val) + 1) := by
    apply Finset.Subset.antisymm
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      simp only [Finset.mem_range]
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      have hMn : S.sup (fun a => (e a).val) < n :=
        Finset.sup_lt_iff (show (0:ℕ) < n from NeZero.pos n) |>.mpr
          (fun b _ => (e b).isLt)
      refine Finset.mem_image.mpr ⟨e.symm ⟨i, by omega⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
        omega
      · simp
  calc S.card = (Finset.univ.filter fun a => (e a).val ≤ S.sup (fun a => (e a).val)).card := by
        rw [hLow]
    _ = ((Finset.univ.filter fun a => (e a).val ≤ S.sup (fun a => (e a).val)).image
          (fun a => (e a).val)).card := by
        rw [Finset.card_image_of_injective]
        intro a b hab
        exact e.injective (Fin.ext hab)
    _ = (Finset.range (S.sup (fun a => (e a).val) + 1)).card := by rw [himg]
    _ = S.sup (fun a => (e a).val) + 1 := Finset.card_range _

omit [DecidableEq α] in
/-- **A proper nonempty initial block of both orders is impossible for irreducible data.** -/
theorem no_block (Q : IETDatum₂ α n) (hQ : Q.Irreducible) (S : Finset α)
    (hSne : S.Nonempty) (hSproper : S ≠ Finset.univ)
    (hT : ∀ a ∈ S, ∀ b, b ∉ S → (Q.piTop a).val < (Q.piTop b).val)
    (hB : ∀ a ∈ S, ∀ b, b ∉ S → (Q.piBottom a).val < (Q.piBottom b).val) : False := by
  have hcardT : S.card = S.sup (fun a => (Q.piTop a).val) + 1 := card_low_of Q.piTop S hSne hT
  have hcardB : S.card = S.sup (fun a => (Q.piBottom a).val) + 1 := card_low_of Q.piBottom S hSne hB
  have hcardα : Fintype.card α = n := by rw [Fintype.card_congr Q.piTop, Fintype.card_fin]
  have hlt : S.card < n := by
    have hsub : S ⊂ Finset.univ :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ S, hSproper⟩
    have := Finset.card_lt_card hsub
    rw [Finset.card_univ] at this
    omega
  set M := S.sup (fun a => (Q.piBottom a).val) with hM
  have hM1 : M + 1 < n := by
    have h1 : S.card = M + 1 := by rw [hcardB, hM]
    omega
  have hMn : M < n := by omega
  have hMT : S.sup (fun a => (Q.piTop a).val) = M := by omega
  have key (i : Fin n) (hi : i ≤ (⟨M, hMn⟩ : Fin n)) : Q.perm i ≤ (⟨M, hMn⟩ : Fin n) := by
    have hzB : (Q.piBottom (Q.piBottom.symm i)).val = i.val := by simp
    have hzS : Q.piBottom.symm i ∈ S := by
      have hlow := low_eq_of Q.piBottom S hSne hB
      rw [← hlow]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hzB]; exact hi
    have hzT : (Q.piTop (Q.piBottom.symm i)).val ≤ M := by
      have h1 : (Q.piTop (Q.piBottom.symm i)).val ≤ S.sup (fun a => (Q.piTop a).val) :=
        Finset.le_sup (f := fun a => (Q.piTop a).val) hzS
      rwa [hMT] at h1
    rwa [show Q.perm i = Q.piTop (Q.piBottom.symm i) from rfl]
  have hall := hQ ⟨M, hMn⟩ key
  have hlast : ((⟨n - 1, by omega⟩ : Fin n)) ≤ (⟨M, hMn⟩ : Fin n) := hall _
  have : n - 1 ≤ M := hlast
  omega

/-! ## 11. Proposition 4.3: every name is taken infinitely often -/

/-- **Proposition 4.3 of the source** (p. 13): along any infinite path of the Rauzy–Veech algorithm
on **irreducible** combinatorial data, every letter is a main name infinitely often. -/
theorem name_infinite (P : IETDatum₂ α n) (hP : P.Irreducible) (γ : ℕ → Bool)
    (lam : ℕ → α → ℝ≥0) (hpos : ∀ k a, 0 < lam k a) (hty : HType P γ lam)
    (hnxt : HNext P γ lam) (a : α) : ∃ᶠ k in atTop, mn P γ k = a := by
  classical
  have hn : 2 ≤ n := two_le_of_htype P γ lam hty
  by_contra hcon
  have hfr : Frozen P γ a := by
    have h1 : ∀ᶠ k in atTop, ¬ (mn P γ k = a) := Filter.not_frequently.mp hcon
    simpa [Frozen] using h1
  obtain ⟨b, hb⟩ := exists_not_frozen P γ
  -- all frozen letters sit below all active letters, in both orders, eventually
  have hsep : ∀ᶠ k in atTop, ∀ x : α, ∀ y : α, Frozen P γ x → ¬ Frozen P γ y →
      (posT P γ k x < posT P γ k y ∧ posB P γ k x < posB P γ k y) := by
    rw [Filter.eventually_all]
    intro x
    rw [Filter.eventually_all]
    intro y
    by_cases hx : Frozen P γ x
    · by_cases hy : Frozen P γ y
      · exact Filter.Eventually.of_forall fun _ _ hh => absurd hy hh
      · filter_upwards [frozen_lt_posT' P γ lam hpos hty hnxt hn hx hy,
          frozen_lt_posB' P γ lam hpos hty hnxt hn hx hy] with k h1 h2 _ _
        exact ⟨h1, h2⟩
    · exact Filter.Eventually.of_forall fun _ hh => absurd hh hx
  obtain ⟨k, hk⟩ := hsep.exists
  -- the set of frozen letters is a proper nonempty initial block of both orders
  set S : Finset α := Finset.univ.filter (Frozen P γ) with hSdef
  have hSne : S.Nonempty := ⟨a, by simp [hSdef, hfr]⟩
  have hSproper : S ≠ Finset.univ := by
    intro h
    have hmem : b ∈ S := by rw [h]; exact Finset.mem_univ b
    rw [hSdef, Finset.mem_filter] at hmem
    exact hb hmem.2
  refine no_block (Vs P γ k) (Vs_irreducible P γ hP k) S hSne hSproper ?_ ?_
  · intro x hx y hy
    have hx' : Frozen P γ x := by rw [hSdef, Finset.mem_filter] at hx; exact hx.2
    have hy' : ¬ Frozen P γ y := by
      intro h; exact hy (by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ y, h⟩)
    exact (hk x y hx' hy').1
  · intro x hx y hy
    have hx' : Frozen P γ x := by rw [hSdef, Finset.mem_filter] at hx; exact hx.2
    have hy' : ¬ Frozen P γ y := by
      intro h; exact hy (by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ y, h⟩)
    exact (hk x y hx' hy').2

end MeshShrink

end
