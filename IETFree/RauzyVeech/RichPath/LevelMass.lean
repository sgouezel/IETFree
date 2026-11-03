/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.RauzyVeech.RichPath.LargeLetter

/-!
# The mass calculus of `Γ₂`/`Γ₃`: level words, fibres, and the covering bound

The combinatorial mass machinery that the `Γ₃` argument of
`IETFree/RauzyVeech/RichPath/Potential.lean` runs on
(`CylinderMass.cond P w η` is the conditional mass of the cylinder `wη` over `w`):

* §1 a bound on the `A'`-heights at the end of `w ++ η` holds at every prefix (`st_take_le_end`,
  `heights_bound_of_end`);
* §2 at an irreducible node the two arrows carry total mass `1` (`cond_arrow_add_one`);
* §3 the level-`N` decomposition `∑_{|δ| = N} cond P w δ = 1` (`levelWords`, `sum_cond_levelWords`);
* §4 the fibre identity: the level-`N` extensions of `γ` sum to `cond P w γ` (`sum_cond_extends`),
  in the counting form `sum_cond_eq_sum_count`;
* §5 the covering bound: a prefix-free family all of whose members extend a member of `B` has mass
  at most that of `B` (`sum_cond_le_sum_of_covers`).
-/


open Finset NodeHeight
open scoped BigOperators

namespace LevelMass

open IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Heights only grow: the bound at the end of a word gives it at every prefix -/

/-- The `A'`-height at a prefix of `w ++ η` is at most the height at `w ++ η`. -/
theorem st_take_le_end (P : IETDatum₂ α n) (w η : List Bool) (i : ℕ) (b : α) :
    st P (w ++ η.take i) b ≤ st P (w ++ η) b := by
  have h := CylinderMass.state_mono P (w ++ η.take i) (η.drop i) b
  rwa [List.append_assoc, List.take_append_drop] at h

/-- A bound on the `A'`-heights valid at the end of `w ++ η` is valid at every prefix. -/
theorem heights_bound_of_end (P : IETDatum₂ α n) (w η : List Bool) (A' : Finset α) {R : ℝ}
    (h : ∀ b ∈ A', st P (w ++ η) b ≤ R) :
    ∀ i, i ≤ η.length → ∀ b ∈ A', st P (w ++ η.take i) b ≤ R :=
  fun i _ b hb => (st_take_le_end P w η i b).trans (h b hb)

/-! ## 2. The two arrows at a node carry total mass exactly `1` -/

theorem cond_arrow_add_one (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) :
    CylinderMass.cond P w [true] + CylinderMass.cond P w [false] = 1 := by
  rw [CylinderMass.cond_arrow P hP hn w true, CylinderMass.cond_arrow P hP hn w false]
  simp only [Bool.not_true, Bool.not_false]
  have h1 : (0 : ℝ) < ColShrink.cs P w ((P.vertex w).last false) := ColShrink.cs_pos P w _
  have h2 : (0 : ℝ) < ColShrink.cs P w ((P.vertex w).last true) := ColShrink.cs_pos P w _
  have h3 : ColShrink.cs P w ((P.vertex w).last false)
      + ColShrink.cs P w ((P.vertex w).last true) ≠ 0 := by positivity
  have h4 : ColShrink.cs P w ((P.vertex w).last true)
      + ColShrink.cs P w ((P.vertex w).last false) ≠ 0 := by positivity
  field_simp
  ring

/-! ## 3. The level-`N` decomposition `∑_{|δ| = N} cond P w δ = 1` -/

/-- The words of length `N`, built one letter at a time (no `Fintype (List Bool)` needed). -/
def levelWords : ℕ → Finset (List Bool)
  | 0 => {[]}
  | N + 1 => (levelWords N).image (fun δ => δ ++ [true]) ∪
      (levelWords N).image (fun δ => δ ++ [false])

theorem levelWords_zero : levelWords 0 = {[]} := rfl

theorem levelWords_succ (N : ℕ) :
    levelWords (N + 1) = (levelWords N).image (fun δ => δ ++ [true]) ∪
      (levelWords N).image (fun δ => δ ++ [false]) := rfl

theorem length_mem_levelWords {N : ℕ} {δ : List Bool} (h : δ ∈ levelWords N) :
    δ.length = N := by
  induction N generalizing δ with
  | zero =>
    simp only [levelWords_zero, Finset.mem_singleton] at h
    simp [h]
  | succ N ih =>
    rw [levelWords_succ, Finset.mem_union] at h
    rcases h with h | h
    · obtain ⟨δ', hδ', rfl⟩ := Finset.mem_image.mp h
      simp [ih hδ']
    · obtain ⟨δ', hδ', rfl⟩ := Finset.mem_image.mp h
      simp [ih hδ']

theorem append_true_ne_append_false {x y : List Bool} :
    x ++ [true] ≠ y ++ [false] := by
  intro h
  have h2 : (x ++ [true]).getLast? = (y ++ [false]).getLast? := by rw [h]
  rw [List.getLast?_append, List.getLast?_append] at h2
  simp at h2

/-- **The level-`N` decomposition**: the relative masses of the `2^N` child cylinders of a given
length sum to `1`.  Induction on `N`, with `cond_append` for the chain rule and
`cond_arrow_add_one` for the two-arrow partition. -/
theorem sum_cond_levelWords (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (N : ℕ) :
    ∑ δ ∈ levelWords N, CylinderMass.cond P w δ = 1 := by
  have hdisj (N : ℕ) :
    Disjoint ((levelWords N).image (fun δ => δ ++ [true]))
      ((levelWords N).image (fun δ => δ ++ [false])) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hb
    exact append_true_ne_append_false hy.symm
  induction N with
  | zero => simp [levelWords]
  | succ N ih =>
    have hstep : ∀ δ : List Bool, CylinderMass.cond P w (δ ++ [true])
        + CylinderMass.cond P w (δ ++ [false]) = CylinderMass.cond P w δ := by
      intro δ
      rw [CylinderMass.cond_append, CylinderMass.cond_append, ← mul_add,
        cond_arrow_add_one P hP hn (w ++ δ), mul_one]
    rw [levelWords_succ, Finset.sum_union (hdisj N),
      Finset.sum_image (fun a _ b _ h => List.append_cancel_right h),
      Finset.sum_image (fun a _ b _ h => List.append_cancel_right h),
      ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun δ _ => hstep δ)]
    exact ih

/-! ## 4. The fibre identity for level-`N` words -/

theorem mem_levelWords_iff {N : ℕ} {δ : List Bool} : δ ∈ levelWords N ↔ δ.length = N := by
  constructor
  · exact length_mem_levelWords
  · intro h
    induction N generalizing δ with
    | zero =>
      rw [List.length_eq_zero_iff] at h
      simp [levelWords_zero, h]
    | succ N ih =>
      obtain ⟨δ', e, rfl⟩ : ∃ (δ' : List Bool) (e : Bool), δ = δ' ++ [e] := by
        rcases List.eq_nil_or_concat δ with h0 | ⟨l, b, hlb⟩
        · rw [h0] at h; simp at h
        · exact ⟨l, b, hlb.trans List.concat_eq_append⟩
      have hlen : δ'.length = N := by simp at h; omega
      rw [levelWords_succ, Finset.mem_union]
      cases e with
      | false => exact Or.inr (Finset.mem_image.mpr ⟨δ', ih hlen, rfl⟩)
      | true => exact Or.inl (Finset.mem_image.mpr ⟨δ', ih hlen, rfl⟩)

/-- The level-`N` words extending `γ` are exactly the words `γ ++ u` with `|u| = N - |γ|`. -/
theorem filter_levelWords_prefix {N : ℕ} {γ : List Bool} (hγ : γ.length ≤ N) :
    (levelWords N).filter (fun δ => γ <+: δ) =
      (levelWords (N - γ.length)).image (fun u => γ ++ u) := by
  ext δ
  simp only [Finset.mem_filter, Finset.mem_image, mem_levelWords_iff]
  constructor
  · rintro ⟨hδ, hp⟩
    obtain ⟨u, rfl⟩ := hp
    exact ⟨u, by simp at hδ ⊢; omega, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨by simp [hu]; omega, List.prefix_append γ u⟩

/-- **The mass of a node is the mass of its level-`N` subtree.** -/
theorem sum_cond_extends (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w γ : List Bool) {N : ℕ} (hγ : γ.length ≤ N) :
    ∑ δ ∈ (levelWords N).filter (fun δ => γ <+: δ), CylinderMass.cond P w δ
      = CylinderMass.cond P w γ := by
  rw [filter_levelWords_prefix hγ,
    Finset.sum_image (fun a _ b _ h => List.append_cancel_left h),
    Finset.sum_congr rfl (fun u _ => CylinderMass.cond_append P w γ u),
    ← Finset.mul_sum, sum_cond_levelWords P hP hn (w ++ γ) (N - γ.length), mul_one]

/-! ## 5. The covering bound -/

/-- **Counting form of the mass**: the mass of a family is the sum over the level-`N` words of the
mass of the level-`N` word times the number of members of the family that prefix it. -/
theorem sum_cond_eq_sum_count (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) {N : ℕ} (G : Finset (List Bool)) (hG : ∀ γ ∈ G, γ.length ≤ N) :
    ∑ γ ∈ G, CylinderMass.cond P w γ =
      ∑ δ ∈ levelWords N, CylinderMass.cond P w δ *
        ((G.filter (fun γ => γ <+: δ)).card : ℝ) := by
  have h1 : ∀ γ ∈ G, CylinderMass.cond P w γ
      = ∑ δ ∈ levelWords N, (if γ <+: δ then CylinderMass.cond P w δ else 0) := by
    intro γ hγ
    rw [← sum_cond_extends P hP hn w γ (hG γ hγ), Finset.sum_filter]
  calc ∑ γ ∈ G, CylinderMass.cond P w γ
      = ∑ γ ∈ G, ∑ δ ∈ levelWords N,
          (if γ <+: δ then CylinderMass.cond P w δ else 0) := Finset.sum_congr rfl h1
    _ = ∑ δ ∈ levelWords N, ∑ γ ∈ G,
          (if γ <+: δ then CylinderMass.cond P w δ else 0) := Finset.sum_comm
    _ = ∑ δ ∈ levelWords N,
          ∑ γ ∈ G.filter (fun γ => γ <+: δ), CylinderMass.cond P w δ := by
        refine Finset.sum_congr rfl fun δ _ => ?_
        rw [Finset.sum_filter]
    _ = ∑ δ ∈ levelWords N, CylinderMass.cond P w δ *
          ((G.filter (fun γ => γ <+: δ)).card : ℝ) := by
        refine Finset.sum_congr rfl fun δ _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Covering bound.**  A prefix-free family all of whose members extend a member of `B` has
`cond`-mass at most the mass of `B`.  This is the mass bookkeeping the assembly needs: it is what
turns "the mass of the bad continuations" into a subtraction. -/
theorem sum_cond_le_sum_of_covers (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) {B S : Finset (List Bool)} (hS : PrefixFree S)
    (hcov : ∀ η ∈ S, ∃ β ∈ B, β <+: η) :
    ∑ η ∈ S, CylinderMass.cond P w η ≤ ∑ β ∈ B, CylinderMass.cond P w β := by
  classical
  have hSN : ∀ γ ∈ S, γ.length ≤ max (S.sup List.length) (B.sup List.length) :=
    fun γ hγ => le_trans (Finset.le_sup (s := S) (f := List.length) hγ) (le_max_left _ _)
  have hBN : ∀ γ ∈ B, γ.length ≤ max (S.sup List.length) (B.sup List.length) :=
    fun γ hγ => le_trans (Finset.le_sup (s := B) (f := List.length) hγ) (le_max_right _ _)
  rw [sum_cond_eq_sum_count P hP hn w (N := max (S.sup List.length) (B.sup List.length)) S hSN,
    sum_cond_eq_sum_count P hP hn w (N := max (S.sup List.length) (B.sup List.length)) B hBN]
  refine Finset.sum_le_sum fun δ _ => ?_
  have hcard : (S.filter (fun η => η <+: δ)).card ≤ (B.filter (fun β => β <+: δ)).card := by
    have hle1 : (S.filter (fun η => η <+: δ)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      have haS : a ∈ S := (Finset.mem_filter.mp ha).1
      have hbS : b ∈ S := (Finset.mem_filter.mp hb).1
      have hpa : a <+: δ := (Finset.mem_filter.mp ha).2
      have hpb : b <+: δ := (Finset.mem_filter.mp hb).2
      rcases List.prefix_or_prefix_of_prefix hpa hpb with h | h
      · exact h.eq_of_length_le (hS a haS b hbS h).length_le
      · exact (h.eq_of_length_le (hS b hbS a haS h).length_le).symm
    rcases Nat.eq_zero_or_pos (S.filter (fun η => η <+: δ)).card with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨η, hη⟩ := Finset.card_pos.mp hpos
      obtain ⟨β, hβB, hβη⟩ := hcov η (Finset.mem_filter.mp hη).1
      have hBpos : 0 < (B.filter (fun β => β <+: δ)).card := Finset.card_pos.mpr
        ⟨β, Finset.mem_filter.mpr ⟨hβB, hβη.trans (Finset.mem_filter.mp hη).2⟩⟩
      omega
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (CylinderMass.cond_nonneg P w δ)

end LevelMass

