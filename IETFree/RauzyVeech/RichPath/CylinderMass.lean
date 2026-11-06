/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.BalancedSet
public import IETFree.RauzyVeech.ColDiam

/-!
# The cylinder mass, and Kerckhoff's lemma in cylinder-mass form

Everything here is about the Rauzy--Veech path matrices and the exact cylinder mass formula; no
measure theory on a projective space is used.

Write `h_b = cs P w b > 0` for the column sums of `Path.Q P w` (the heights of the tower) and

`cond P w δ = (∏ b, cs P w b) / (∏ b, cs P (w ++ δ) b) = σ(Δ_{wδ}) / σ(Δ_w)`

for the mass of the child cylinder relative to its parent
 (`BalancedCylinders.volume_append_mul`). Main results:

* `cond_arrow`: for one letter `e`, if `α` is the winner of `e` at `vertex P w` and `β` its loser,
  then `cond P w [e] = h_β / (h_α + h_β)` (the loser's height over the sum).
* `state_mono`: `cs P w b ≤ cs P (w ++ δ) b` (heights are non-decreasing).
* `kerckhoff`: for every `r > 0` and every finite *prefix-free* family `S` of continuations whose
  arrows all have winner `≠ α` and which satisfy `r < cs P (w ++ δ) α`, one has
  `∑_{δ ∈ S} cond P w δ < cs P w α / r`.  With `r = T * cs P w α`, this is `< 1/T`, the
  cylinder-mass form of Kerckhoff's lemma (the source's
  `P_q(Γ_α, (B_γ q)_α > T q_α) < T⁻¹`).
-/

open Finset IETDatum₂
open scoped BigOperators NNReal ENNReal

@[expose] public section

namespace CylinderMass

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 0. Definitions -/

/-- The mass of the child cylinder `Δ(w ++ δ)` relative to its parent `Δ(w)`, i.e. the ratio
of the products of the column sums. -/
noncomputable def cond (P : IETDatum₂ α n) (w δ : List Bool) : ℝ :=
  (∏ b, ColShrink.cs P w b) / ∏ b, ColShrink.cs P (w ++ δ) b

/-- `NoWin P w α δ`: the word `δ`, read from the vertex `P` at time `|w|`, has no arrow whose
winner is `α`.  (Recursive form, so that it unfolds along the first letter.) -/
def NoWin (P : IETDatum₂ α n) (w : List Bool) (α : α) : List Bool → Prop
  | [] => True
  | e :: δ => (P.vertex w).last e ≠ α ∧ NoWin P (w ++ [e]) α δ

/-! ## 1. The column sums and the conditional mass of one more letter -/

/-- The column sums in `ℝ`, one letter later: the loser's height grows by the winner's. -/
theorem cs_append_singleton (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (e : Bool) (b : α) :
    ColShrink.cs P (w ++ [e]) b =
      ColShrink.cs P w b +
        (if b = (P.vertex w).last (!e) then ColShrink.cs P w ((P.vertex w).last e) else 0) := by
  have h := BalancedCylinders.colsum_append_singleton P hP hn w e b
  have h2 := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at h2
  simpa [ColShrink.cs] using h2

/-- One factor of a product changed. -/
theorem prod_ite_eq_mul {M : Type*} [CommMonoid M] (f : α → M) (β : α) (y : M) :
    (∏ b, (if b = β then y else f b)) = (∏ b ∈ Finset.univ.erase β, f b) * y := by
  rw [← Finset.prod_erase_mul (s := Finset.univ) (f := fun b => if b = β then y else f b)
    (Finset.mem_univ β)]
  congr 1
  · exact Finset.prod_congr rfl fun b hb => by rw [if_neg (Finset.ne_of_mem_erase hb)]
  · rw [if_pos rfl]

/-- The product of the column sums one letter later. -/
theorem prod_cs_append_singleton (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (e : Bool) :
    (∏ b, ColShrink.cs P (w ++ [e]) b) =
      (∏ b ∈ Finset.univ.erase ((P.vertex w).last (!e)), ColShrink.cs P w b) *
        (ColShrink.cs P w ((P.vertex w).last (!e))
          + ColShrink.cs P w ((P.vertex w).last e)) := by
  have h1 : (∏ b, ColShrink.cs P (w ++ [e]) b) =
      ∏ b, (if b = (P.vertex w).last (!e) then ColShrink.cs P w ((P.vertex w).last (!e))
        + ColShrink.cs P w ((P.vertex w).last e) else ColShrink.cs P w b) := by
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [cs_append_singleton P hP hn w e b]
    by_cases hb : b = (P.vertex w).last (!e)
    · rw [if_pos hb, if_pos hb, hb]
    · rw [if_neg hb, if_neg hb, add_zero]
  rw [h1, prod_ite_eq_mul]

/-- **The conditional mass of one letter**: the loser's height over the sum of the two heights
(`P_q(γ | π) = q_β/(q_α + q_β)` in the source, `α` the winner and `β` the loser). -/
theorem cond_arrow (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (e : Bool) :
    cond P w [e] = ColShrink.cs P w ((P.vertex w).last (!e)) /
      (ColShrink.cs P w ((P.vertex w).last (!e)) + ColShrink.cs P w ((P.vertex w).last e)) := by
  have hprod := prod_cs_append_singleton P hP hn w e
  have herase : (∏ b ∈ Finset.univ.erase ((P.vertex w).last (!e)), ColShrink.cs P w b) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun b _ => ColShrink.cs_ne_zero P w b
  have hsplit : (∏ b, ColShrink.cs P w b) =
      (∏ b ∈ Finset.univ.erase ((P.vertex w).last (!e)), ColShrink.cs P w b) *
        ColShrink.cs P w ((P.vertex w).last (!e)) :=
    (Finset.prod_erase_mul (s := Finset.univ) (f := fun b => ColShrink.cs P w b)
      (Finset.mem_univ _)).symm
  rw [cond, hprod, hsplit]
  exact mul_div_mul_left _ _ herase

/-- The mass of the empty continuation is `1`. -/
@[simp]
theorem cond_nil (P : IETDatum₂ α n) (w : List Bool) : cond P w [] = 1 := by
  have h : (∏ b, ColShrink.cs P w b) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun b _ => ColShrink.cs_ne_zero P w b
  simpa [cond] using div_self h

/-- **The chain rule** for the conditional masses. -/
theorem cond_append (P : IETDatum₂ α n) (w δ δ' : List Bool) :
    cond P w (δ ++ δ') = cond P w δ * cond P (w ++ δ) δ' := by
  have h2 : (∏ b, ColShrink.cs P (w ++ δ) b) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun b _ => ColShrink.cs_ne_zero P (w ++ δ) b
  simp only [cond]
  rw [div_mul_div_comm, mul_comm (∏ b, ColShrink.cs P w b) (∏ b, ColShrink.cs P (w ++ δ) b),
    mul_div_mul_left _ _ h2, List.append_assoc]

/-- The height of the child in terms of the path matrix of the continuation — the direction's
`∑ c, (Path.Q (P.vertex P w) δ c α : ℝ) * cs P w c`. -/
theorem cs_append_eq_sum (P : IETDatum₂ α n) (w δ : List Bool) (b : α) :
    ColShrink.cs P (w ++ δ) b
      = ∑ c, (IETDatum₂.Path.Q (P.vertex w) δ c b : ℝ) * ColShrink.cs P w c := by
  simp only [ColShrink.cs]
  have h3 : ((∑ a, IETDatum₂.Path.Q P (w ++ δ) a b : ℤ) : ℝ)
      = ∑ c, (IETDatum₂.Path.Q (P.vertex w) δ c b : ℝ) *
          ∑ a, (IETDatum₂.Path.Q P w a c : ℝ) := by
    rw [BalancedCylinders.colsum_append P w δ b]
    push_cast
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  push_cast at h3 ⊢
  exact h3

/-- **Heights are non-decreasing** along a continuation. -/
theorem state_mono (P : IETDatum₂ α n) (w δ : List Bool) (b : α) :
    ColShrink.cs P w b ≤ ColShrink.cs P (w ++ δ) b := by
  have h := BalancedCylinders.colsum_le_colsum_append P w δ b
  have h2 : ((∑ a, IETDatum₂.Path.Q P w a b : ℤ) : ℝ)
      ≤ ((∑ a, IETDatum₂.Path.Q P (w ++ δ) a b : ℤ) : ℝ) := by exact_mod_cast h
  push_cast at h2
  simpa [ColShrink.cs] using h2

/-- **The key identity of the induction.**  Summing `cond · [e] · h'^α` over the two arrows whose
winner is not `α` gives exactly the current height `h_α`.  (If `α` is the winner of one arrow,
only the other one is allowed and there `α` is the loser, so its height grows by exactly the
right amount; if `α` is neither winner, both arrows keep `h_α` and their masses add up to `1`.) -/
theorem sum_cond_mul_cs (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (α : α) :
    (∑ e : Bool, (if (P.vertex w).last e ≠ α then
        cond P w [e] * ColShrink.cs P (w ++ [e]) α else 0)) = ColShrink.cs P w α := by
  have hTF : (P.vertex w).last true ≠ (P.vertex w).last false := by
    have h := vertex_last_ne_not P hP hn w true
    simpa using h
  have hFT : (P.vertex w).last false ≠ (P.vertex w).last true := Ne.symm hTF
  have hTF' : ColShrink.cs P w ((P.vertex w).last true)
      + ColShrink.cs P w ((P.vertex w).last false) ≠ 0 := by
    have h1 := ColShrink.cs_pos P w ((P.vertex w).last true)
    have h2 := ColShrink.cs_pos P w ((P.vertex w).last false)
    positivity
  have hFT' : ColShrink.cs P w ((P.vertex w).last false)
      + ColShrink.cs P w ((P.vertex w).last true) ≠ 0 := by
    have h1 := ColShrink.cs_pos P w ((P.vertex w).last true)
    have h2 := ColShrink.cs_pos P w ((P.vertex w).last false)
    positivity
  rw [show (∑ e : Bool, (if (P.vertex w).last e ≠ α then
      cond P w [e] * ColShrink.cs P (w ++ [e]) α else 0))
      = (if (P.vertex w).last true ≠ α then cond P w [true] *
          ColShrink.cs P (w ++ [true]) α else 0)
        + (if (P.vertex w).last false ≠ α then cond P w [false] *
          ColShrink.cs P (w ++ [false]) α else 0) from by simp]
  rw [cond_arrow P hP hn w true, cond_arrow P hP hn w false,
    cs_append_singleton P hP hn w true α, cs_append_singleton P hP hn w false α]
  simp only [Bool.not_true, Bool.not_false]
  rcases eq_or_ne α ((P.vertex w).last true) with hα | hα
  · subst hα
    rw [if_neg (by simp), if_pos hFT, if_pos rfl, zero_add, div_mul_cancel₀ _ hTF']
  · rcases eq_or_ne α ((P.vertex w).last false) with hβ | hβ
    · subst hβ
      rw [if_pos hTF, if_pos rfl, if_neg (by simp), add_zero, div_mul_cancel₀ _ hFT']
    · rw [if_pos (Ne.symm hα), if_neg hβ, add_zero, if_pos (Ne.symm hβ), if_neg hα, add_zero]
      field_simp
      ring

/-- A nonempty list is its head followed by its tail. -/
theorem eq_cons_tail_of_head? {l : List Bool} {e : Bool} (h : l.head? = some e) :
    l = e :: l.tail := by
  cases l with
  | nil => simp at h
  | cons a t => simp at h; simp [h]

/-- The relative cylinder masses are positive. -/
theorem cond_pos (P : IETDatum₂ α n) (w δ : List Bool) : 0 < cond P w δ :=
  div_pos (Finset.prod_pos fun b _ => ColShrink.cs_pos P w b)
    (Finset.prod_pos fun b _ => ColShrink.cs_pos P (w ++ δ) b)

theorem cond_nonneg (P : IETDatum₂ α n) (w δ : List Bool) : 0 ≤ cond P w δ :=
  le_of_lt (cond_pos P w δ)

/-! ## 2. Kerckhoff's lemma -/

/-- **The length induction behind Kerckhoff's lemma.**  For every `r > 0` and every finite
*prefix-free* family `S` of continuations of length at most `N`, all of whose arrows have winner `≠
α` and which all satisfy `r < h'^α`, the total relative mass is strictly less than `h_α / r`.
(Strict: at the bottom of the induction a crossing word of length `0` needs `r < h_α`, and every
step multiplies by a positive arrow mass, so no equality can arise.)  The induction is on the length
bound: the first letter of the continuations splits `S` into (at most) the two arrows whose winner
is not `α`, and the induction hypothesis at `w ++ [e]` bounds each part by `h'_α / r`;
`sum_cond_mul_cs` then converts the sum back to `h_α / r`. -/
theorem kerckhoff_aux (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) (N : ℕ) :
    ∀ (S : Finset (List Bool)) (w : List Bool) (α : α) (r : ℝ), 0 < r →
      (∀ δ ∈ S, δ.length ≤ N) →
      (∀ δ ∈ S, ∀ δ' ∈ S, δ <+: δ' → δ' <+: δ) →
      (∀ δ ∈ S, NoWin P w α δ) →
      (∀ δ ∈ S, r < ColShrink.cs P (w ++ δ) α) →
      (∑ δ ∈ S, cond P w δ) < ColShrink.cs P w α / r := by
  induction N with
  | zero =>
    intro S w α r hr hlen hpre hwin hcross
    rcases S.eq_empty_or_nonempty with rfl | ⟨δ₀, hδ₀⟩
    · rw [Finset.sum_empty]
      exact div_pos (ColShrink.cs_pos P w α) hr
    · have hsingle : S = {[]} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun δ hδ => ?_⟩
        · have h : δ₀ = [] :=
            List.eq_nil_of_length_eq_zero (by have := hlen δ₀ hδ₀; omega)
          rw [h] at hδ₀
          exact hδ₀
        · exact List.eq_nil_of_length_eq_zero (by have := hlen δ hδ; omega)
      rw [hsingle, Finset.sum_singleton, cond_nil, lt_div_iff₀ hr, one_mul]
      have hc := hcross [] (hsingle.symm ▸ Finset.mem_singleton_self ([] : List Bool))
      rw [List.append_nil] at hc
      exact hc
  | succ N ih =>
    intro S w α r hr hlen hpre hwin hcross
    rcases S.eq_empty_or_nonempty with rfl | ⟨δ₀, hδ₀⟩
    · rw [Finset.sum_empty]
      exact div_pos (ColShrink.cs_pos P w α) hr
    · by_cases hnil : ([] : List Bool) ∈ S
      · have hsingle : S = {[]} := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hnil, fun δ hδ => ?_⟩
          exact List.eq_nil_of_prefix_nil (hpre [] hnil δ hδ List.nil_prefix)
        rw [hsingle, Finset.sum_singleton, cond_nil, lt_div_iff₀ hr, one_mul]
        have hc := hcross [] (hsingle.symm ▸ Finset.mem_singleton_self ([] : List Bool))
        rw [List.append_nil] at hc
        exact hc
      · have hne (δ) (hδ : δ ∈ S) : δ ≠ [] := fun h =>
      hnil (h ▸ hδ)
        have hhead (δ) (hδ : δ ∈ S) : δ.head? = some true ∨ δ.head? = some false := by
          cases h : δ.head? with
          | none => exact absurd (List.head?_eq_none_iff.mp h) (hne δ hδ)
          | some e => cases e <;> simp
        have hfilt : S.filter (fun δ : List Bool => ¬ (δ.head? = some true))
            = S.filter (fun δ : List Bool => δ.head? = some false) := by
          refine Finset.filter_congr (p := fun δ : List Bool => ¬ (δ.head? = some true))
            (q := fun δ : List Bool => δ.head? = some false) (s := S) ?_
          intro δ hδ
          rcases hhead δ hδ with h | h <;> rw [h] <;> simp
        have hsplit : S.sum (fun δ => cond P w δ)
            = (S.filter (fun δ : List Bool => δ.head? = some true)).sum (fun δ => cond P w δ)
              + (S.filter (fun δ : List Bool => δ.head? = some false)).sum
                (fun δ => cond P w δ) := by
          rw [← Finset.sum_filter_add_sum_filter_not (s := S)
            (p := fun δ : List Bool => δ.head? = some true) (f := fun δ => cond P w δ), hfilt]
        have hterm (e : Bool) :
          (S.filter (fun δ : List Bool => δ.head? = some e)).sum (fun δ => cond P w δ)
              = cond P w [e] * ((S.filter (fun δ : List Bool => δ.head? = some e)).image
                  List.tail).sum (fun δ' => cond P (w ++ [e]) δ') := by
          have hinj : Set.InjOn (List.tail : List Bool → List Bool)
              ↑(S.filter (fun δ : List Bool => δ.head? = some e)) := by
            intro x hx y hy hxy
            simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
            rw [eq_cons_tail_of_head? hx.2, eq_cons_tail_of_head? hy.2, hxy]
          calc (S.filter (fun δ : List Bool => δ.head? = some e)).sum (fun δ => cond P w δ)
              = (S.filter (fun δ : List Bool => δ.head? = some e)).sum
                  (fun δ => cond P w (e :: δ.tail)) := by
                refine Finset.sum_congr rfl fun δ hδ => ?_
                exact congrArg (fun x => cond P w x)
                  (eq_cons_tail_of_head? (Finset.mem_filter.mp hδ).2)
            _ = (S.filter (fun δ : List Bool => δ.head? = some e)).sum
                  (fun δ => cond P w [e] * cond P (w ++ [e]) δ.tail) := by
                refine Finset.sum_congr rfl fun δ hδ => ?_
                rw [show e :: δ.tail = [e] ++ δ.tail from rfl, cond_append]
            _ = cond P w [e] * (S.filter (fun δ : List Bool => δ.head? = some e)).sum
                  (fun δ => cond P (w ++ [e]) δ.tail) := (Finset.mul_sum ..).symm
            _ = cond P w [e] * ((S.filter (fun δ : List Bool => δ.head? = some e)).image
                  List.tail).sum (fun δ' => cond P (w ++ [e]) δ') := by
                rw [Finset.sum_image hinj]
        have hb_empty (e : Bool) (hw : (P.vertex w).last e = α) :
          S.filter (fun δ : List Bool => δ.head? = some e) = ∅ := by
          refine Finset.filter_false_of_mem ?_
          intro δ hδ hhead
          have h1 : δ = e :: δ.tail := eq_cons_tail_of_head? hhead
          have h2 : NoWin P w α δ := hwin δ hδ
          rw [h1] at h2
          exact h2.1 hw
        have hb_lt (e : Bool) :
          (S.filter (fun δ : List Bool => δ.head? = some e)).sum (fun δ => cond P w δ)
              < cond P w [e] * ColShrink.cs P (w ++ [e]) α / r := by
          set Te := (S.filter (fun δ : List Bool => δ.head? = some e)).image List.tail
            with hTe
          have hlen' (δ') (hδ' : δ' ∈ Te) : δ'.length ≤ N := by
            obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hδ'
            have h1 : δ = e :: δ.tail := eq_cons_tail_of_head? (Finset.mem_filter.mp hδ).2
            have h2 : δ.length ≤ N + 1 := hlen δ (Finset.mem_filter.mp hδ).1
            have h3 : (e :: δ.tail).length ≤ N + 1 := h1 ▸ h2
            simp only [List.length_cons] at h3
            omega
          have hpre' (δ') (hx : δ' ∈ Te) : ∀ δ'' ∈ Te, δ' <+: δ'' → δ'' <+: δ' := by
            intro y hy hxy
            obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
            obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
            have hx1 : x' = e :: x'.tail := eq_cons_tail_of_head? (Finset.mem_filter.mp hx').2
            have hy1 : y' = e :: y'.tail := eq_cons_tail_of_head? (Finset.mem_filter.mp hy').2
            have h1 : x' <+: y' := by
              rw [hx1, hy1]
              exact List.cons_prefix_cons.mpr ⟨rfl, hxy⟩
            have h2 : y' <+: x' := hpre x' (Finset.mem_filter.mp hx').1
              y' (Finset.mem_filter.mp hy').1 h1
            rw [hy1, hx1] at h2
            obtain ⟨c, hc⟩ := h2
            exact ⟨c, by simpa using hc⟩
          have hwin' (δ') (hδ' : δ' ∈ Te) : NoWin P (w ++ [e]) α δ' := by
            obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hδ'
            have h1 : δ = e :: δ.tail := eq_cons_tail_of_head? (Finset.mem_filter.mp hδ).2
            have h2 : NoWin P w α δ := hwin δ (Finset.mem_filter.mp hδ).1
            rw [h1] at h2
            exact h2.2
          have hcross' (δ') (hδ' : δ' ∈ Te) : r < ColShrink.cs P ((w ++ [e]) ++ δ') α := by
            obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hδ'
            have h1 : δ = e :: δ.tail := eq_cons_tail_of_head? (Finset.mem_filter.mp hδ).2
            have h2 : r < ColShrink.cs P (w ++ δ) α := hcross δ (Finset.mem_filter.mp hδ).1
            rw [h1, List.append_cons] at h2
            exact h2
          have hIH : Te.sum (fun δ' => cond P (w ++ [e]) δ')
              < ColShrink.cs P (w ++ [e]) α / r :=
            ih Te (w ++ [e]) α r hr hlen' hpre' hwin' hcross'
          rw [hterm e]
          have hshape : cond P w [e] * ColShrink.cs P (w ++ [e]) α / r
              = cond P w [e] * (ColShrink.cs P (w ++ [e]) α / r) := by
            rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
          rw [hshape]
          exact mul_lt_mul_of_pos_left hIH (cond_pos P w [e])
        have hkey := sum_cond_mul_cs P hP hn w α
        rw [show (∑ e : Bool, (if (P.vertex w).last e ≠ α then
              cond P w [e] * ColShrink.cs P (w ++ [e]) α else 0))
            = (if (P.vertex w).last true ≠ α then
                cond P w [true] * ColShrink.cs P (w ++ [true]) α else 0)
              + (if (P.vertex w).last false ≠ α then
                cond P w [false] * ColShrink.cs P (w ++ [false]) α else 0)
            from by simp] at hkey
        rw [hsplit, ← hkey, add_div]
        rcases eq_or_ne ((P.vertex w).last true) α with ht | ht
        · rcases eq_or_ne ((P.vertex w).last false) α with hf | hf
          · exfalso
            rcases hhead δ₀ hδ₀ with hh | hh
            · have h2 : NoWin P w α δ₀ := hwin δ₀ hδ₀
              rw [eq_cons_tail_of_head? hh] at h2
              exact h2.1 ht
            · have h2 : NoWin P w α δ₀ := hwin δ₀ hδ₀
              rw [eq_cons_tail_of_head? hh] at h2
              exact h2.1 hf
          · rw [hb_empty true ht, Finset.sum_empty, if_neg (by rw [ht]; simp), if_pos hf]
            simp only [zero_add, zero_div]
            exact hb_lt false
        · rcases eq_or_ne ((P.vertex w).last false) α with hf | hf
          · rw [hb_empty false hf, Finset.sum_empty, if_pos ht, if_neg (by rw [hf]; simp)]
            simp only [add_zero, zero_div]
            exact hb_lt true
          · rw [if_pos ht, if_pos hf]
            exact add_lt_add (hb_lt true) (hb_lt false)

/-- **Kerckhoff's lemma in cylinder-mass form.**  Let `T > 0`, let `w` be a finite path, `α` a
letter, and let `S` be a finite *prefix-free* family of continuations of `w` along which no arrow
has winner `α` and after which the `α`-height has grown by a factor `> T`.  Then the total mass of
the corresponding child cylinders, relative to `Δ(w)`, is less than `1/T` — exactly the source's
statement (with the family of minimal crossings as the prefix-free `S`).  In the source's notation:
`P_q(γ ∈ Γ_α(π), (B_γ q)_α > T q_α | π) < T⁻¹`, with `q = cs P w`. -/
theorem kerckhoff (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (α : α) {T : ℝ} (hT : 0 < T) (S : Finset (List Bool))
    (hpre : ∀ δ ∈ S, ∀ δ' ∈ S, δ <+: δ' → δ' <+: δ)
    (hwin : ∀ δ ∈ S, NoWin P w α δ)
    (hcross : ∀ δ ∈ S, T * ColShrink.cs P w α < ColShrink.cs P (w ++ δ) α) :
    (∑ δ ∈ S, cond P w δ) < 1 / T := by
  have hr : 0 < T * ColShrink.cs P w α := by
    have h := ColShrink.cs_pos P w α
    positivity
  have hmain := kerckhoff_aux P hP hn (S.sup List.length) S w α (T * ColShrink.cs P w α) hr
    (fun δ hδ => Finset.le_sup (s := S) (f := List.length) hδ) hpre hwin hcross
  refine lt_of_lt_of_eq hmain ?_
  rw [mul_comm T (ColShrink.cs P w α), div_mul_eq_div_div,
    div_self (ColShrink.cs_ne_zero P w α), one_div]

/-! ## 3. The link with the exact cylinder mass `BalancedCylinders.volume_append_mul` -/

/-- The column sums used by the mass formula and by `ColShrink.cs` agree. -/
theorem coe_colsumNN_cs (P : IETDatum₂ α n) (γ : List Bool) (b : α) :
    ((colsumNN (IETDatum₂.Path.Q P γ) b : ℝ≥0) : ℝ) = ColShrink.cs P γ b := by
  rw [coe_colsumNN (N := IETDatum₂.Path.Q P γ) (b := b)
    (IETDatum₂.Path.Q_colsum_pos P γ b)]
  simp only [ColShrink.cs]
  push_cast
  ring

/-- `cond` is the `ℝ≥0` factor of the mass formula. -/
theorem toNNReal_cond (P : IETDatum₂ α n) (γ δ : List Bool) :
    Real.toNNReal (cond P γ δ) = ∏ b, (colsumNN (IETDatum₂.Path.Q P γ) b *
      (colsumNN (IETDatum₂.Path.Q P (γ ++ δ)) b)⁻¹) := by
  apply NNReal.coe_injective
  have h1 : ((∏ b, (colsumNN (IETDatum₂.Path.Q P γ) b *
      (colsumNN (IETDatum₂.Path.Q P (γ ++ δ)) b)⁻¹) : ℝ≥0) : ℝ)
      = (∏ b, ColShrink.cs P γ b) * (∏ b, ColShrink.cs P (γ ++ δ) b)⁻¹ := by
    rw [NNReal.coe_prod]
    simp only [NNReal.coe_mul, NNReal.coe_inv]
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    congr 1
    · exact Finset.prod_congr rfl fun b _ => coe_colsumNN_cs P γ b
    · exact congrArg Inv.inv (Finset.prod_congr rfl fun b _ => coe_colsumNN_cs P (γ ++ δ) b)
  rw [h1, Real.coe_toNNReal (cond P γ δ) (le_of_lt (cond_pos P γ δ)), cond, div_eq_mul_inv]

/-- **`cond` is the mass of the child cylinder relative to its parent.**  This is the exact mass
formula `BalancedCylinders.volume_append_mul`, rewritten with `cond`. -/
theorem volume_append_eq_cond (P : IETDatum₂ α n) (γ δ : List Bool) :
    simplexVolumeOn α (IETDatum₂.simplexCyl P (γ ++ δ))
      = ENNReal.ofReal (cond P γ δ) * simplexVolumeOn α (IETDatum₂.simplexCyl P γ) := by
  rw [BalancedCylinders.volume_append_mul, ← toNNReal_cond]
  rfl

end CylinderMass

end
