/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.RichPath.NodeHeight

/-!
# The words of length `N`

`levelWords N` is the finite set of words of length `N` over the alphabet `Bool`, built one letter
at a time from the empty word.  It is the index set of the level-`N` cylinders at a node of the
Rauzy diagram, and two developments of the `Γ₃` argument use it: the mass calculus
(`RauzyVeech/RichPath/`, where the masses of the members of `levelWords N` sum to `1`)
and the stopping bookkeeping (`RauzyVeech/RichPath/`, where the level-`N` words are the
candidates for the first crossing of a threshold).  The notion and its API therefore live here,
below both.

The construction is the `image` form (`levelWords (N + 1)` is the two images of `levelWords N`
under appending `true` and `false`), so that the mass computation can split the sum with
`Finset.sum_union` and rewrite the two images separately.

`Fintype (List Bool)` is not needed anywhere: `levelWords` is built by recursion on `N`.
-/

@[expose] public section

open Finset IntervalExchange.IETDatum₂
open scoped BigOperators

namespace IntervalExchange.RauzyVeech.RichPath

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. The definition and its elementary API -/

/-- The words of length `N`, built one letter at a time (no `Fintype (List Bool)` needed). -/
def levelWords : ℕ → Finset (List Bool)
  | 0 => {[]}
  | N + 1 => (levelWords N).image (fun δ => δ ++ [true]) ∪
      (levelWords N).image (fun δ => δ ++ [false])

theorem levelWords_zero : levelWords 0 = {[]} := (rfl)

theorem levelWords_succ (N : ℕ) :
    levelWords (N + 1) = (levelWords N).image (fun δ => δ ++ [true]) ∪
      (levelWords N).image (fun δ => δ ++ [false]) := (rfl)

/-- A word of `levelWords N` has length `N`. -/
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

/-- A word of length `N` is in `levelWords N`. -/
theorem mem_levelWords_of_length {N : ℕ} {δ : List Bool} (h : δ.length = N) :
    δ ∈ levelWords N := by
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

/-- **The members of `levelWords N` are the words of length `N`.** -/
theorem mem_levelWords_iff {N : ℕ} {δ : List Bool} : δ ∈ levelWords N ↔ δ.length = N :=
  ⟨length_mem_levelWords, mem_levelWords_of_length⟩

/-- A word ending in `true` is not a word ending in `false`. -/
theorem append_true_ne_append_false {x y : List Bool} : x ++ [true] ≠ y ++ [false] := by
  intro h
  have h2 : (x ++ [true]).getLast? = (y ++ [false]).getLast? := by rw [h]
  rw [List.getLast?_append, List.getLast?_append] at h2
  simp at h2

/-! ## 2. The mass of the level-`N` words -/

/-- **The level-`N` decomposition**: the relative masses of the `2^N` child cylinders of a given
length sum to `1`.  Induction on `N`, with `cond_append` for the chain rule and
`cond_arrow_sum` for the two-arrow partition. -/
theorem sum_cond_levelWords (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (N : ℕ) :
    ∑ δ ∈ levelWords N, cond P w δ = 1 := by
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
    have hstep (δ : List Bool) : cond P w (δ ++ [true])
        + cond P w (δ ++ [false]) = cond P w δ := by
      rw [cond_append, cond_append, ← mul_add,
        cond_arrow_sum P hP hn (w ++ δ), mul_one]
    rw [levelWords_succ, Finset.sum_union (hdisj N),
      Finset.sum_image (fun a _ b _ h => List.append_cancel_right h),
      Finset.sum_image (fun a _ b _ h => List.append_cancel_right h),
      ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun δ _ => hstep δ)]
    exact ih

end IntervalExchange.RauzyVeech.RichPath
