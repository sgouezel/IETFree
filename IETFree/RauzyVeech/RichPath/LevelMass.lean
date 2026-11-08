/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.RichPath.LevelWords

/-!
# The mass calculus of `Γ₂`/`Γ₃`: fibres and the covering bound

The combinatorial mass machinery that the `Γ₃` argument of
`IETFree/RauzyVeech/RichPath/` runs on
(`cond P w η` is the conditional mass of the cylinder `wη` over `w`).  The level-`N`
words themselves, the identity `∑_{|δ| = N} cond P w δ = 1` and the two-arrow partition are in
`RauzyVeech/RichPath/`, below this file.

* §1 a bound on the `A'`-heights at the end of `w ++ η` holds at every prefix (`colSum_take_le_end`,
  `heights_bound_of_end`);
* §2 the fibre identity: the level-`N` extensions of `γ` sum to `cond P w γ` (`sum_cond_extends`),
  in the counting form `sum_cond_eq_sum_count`;
* §3 the covering bound: a prefix-free family all of whose members extend a member of `B` has mass
  at most that of `B` (`sum_cond_le_sum_of_covers`).
-/

open Finset IntervalExchange.IETDatum₂
open scoped BigOperators

@[expose] public section

namespace IntervalExchange.RauzyVeech.RichPath

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Heights only grow: the bound at the end of a word gives it at every prefix -/

/-- The `A'`-height at a prefix of `w ++ η` is at most the height at `w ++ η`. -/
theorem colSum_take_le_end (P : IETDatum₂ α n) (w η : List Bool) (i : ℕ) (b : α) :
    colSum P (w ++ η.take i) b ≤ colSum P (w ++ η) b := by
  have h := state_mono P (w ++ η.take i) (η.drop i) b
  rwa [List.append_assoc, List.take_append_drop] at h

/-- A bound on the `A'`-heights valid at the end of `w ++ η` is valid at every prefix. -/
theorem heights_bound_of_end (P : IETDatum₂ α n) (w η : List Bool) (A' : Finset α) {R : ℝ}
    (h : ∀ b ∈ A', colSum P (w ++ η) b ≤ R) (i : ℕ) (hi : i ≤ η.length) (b : α)
    (hb : b ∈ A') : colSum P (w ++ η.take i) b ≤ R := by
  have _hi := hi
  exact (colSum_take_le_end P w η i b).trans (h b hb)

/-! ## 2. The fibre identity for level-`N` words -/

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
    ∑ δ ∈ (levelWords N).filter (fun δ => γ <+: δ), cond P w δ
      = cond P w γ := by
  rw [filter_levelWords_prefix hγ,
    Finset.sum_image (fun a _ b _ h => List.append_cancel_left h),
    Finset.sum_congr rfl (fun u _ => cond_append P w γ u),
    ← Finset.mul_sum, sum_cond_levelWords P hP hn (w ++ γ) (N - γ.length), mul_one]

/-! ## 3. The covering bound -/

/-- **Counting form of the mass**: the mass of a family is the sum over the level-`N` words of the
mass of the level-`N` word times the number of members of the family that prefix it. -/
theorem sum_cond_eq_sum_count (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) {N : ℕ} (G : Finset (List Bool)) (hG : ∀ γ ∈ G, γ.length ≤ N) :
    ∑ γ ∈ G, cond P w γ =
      ∑ δ ∈ levelWords N, cond P w δ *
        ((G.filter (fun γ => γ <+: δ)).card : ℝ) := by
  have h1 (γ) (hγ : γ ∈ G) : cond P w γ
      = ∑ δ ∈ levelWords N, (if γ <+: δ then cond P w δ else 0) := by
    rw [← sum_cond_extends P hP hn w γ (hG γ hγ), Finset.sum_filter]
  calc ∑ γ ∈ G, cond P w γ
      = ∑ γ ∈ G, ∑ δ ∈ levelWords N,
          (if γ <+: δ then cond P w δ else 0) := Finset.sum_congr rfl h1
    _ = ∑ δ ∈ levelWords N, ∑ γ ∈ G,
          (if γ <+: δ then cond P w δ else 0) := Finset.sum_comm
    _ = ∑ δ ∈ levelWords N,
          ∑ γ ∈ G.filter (fun γ => γ <+: δ), cond P w δ := by
        refine Finset.sum_congr rfl fun δ _ => ?_
        rw [Finset.sum_filter]
    _ = ∑ δ ∈ levelWords N, cond P w δ *
          ((G.filter (fun γ => γ <+: δ)).card : ℝ) := by
        refine Finset.sum_congr rfl fun δ _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Covering bound.**  A prefix-free family all of whose members extend a member of `B` has
`cond`-mass at most the mass of `B`.  This is the mass bookkeeping the assembly needs: it is what
turns "the mass of the bad continuations" into a subtraction. -/
theorem sum_cond_le_sum_of_covers (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) {B S : Finset (List Bool)} (hS : PrefixFree S)
    (hcov : ∀ η ∈ S, ∃ β ∈ B, β <+: η) :
    ∑ η ∈ S, cond P w η ≤ ∑ β ∈ B, cond P w β := by
  have hSN (γ) (hγ : γ ∈ S) : γ.length ≤ max (S.sup List.length) (B.sup List.length) := le_trans
      (Finset.le_sup (s := S) (f := List.length) hγ) (le_max_left _ _)
  have hBN (γ) (hγ : γ ∈ B) : γ.length ≤ max (S.sup List.length) (B.sup List.length) := le_trans
      (Finset.le_sup (s := B) (f := List.length) hγ) (le_max_right _ _)
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
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (cond_nonneg P w δ)

end IntervalExchange.RauzyVeech.RichPath

end
