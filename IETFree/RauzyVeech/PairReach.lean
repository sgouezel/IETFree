/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.CylinderGrowth
public import IETFree.RauzyVeech.NameInfinite

/-!
# `PairReach`: the combinatorial core of Cor. 4

Descent on `pos_T(last false)`. -/

@[expose] public section

open scoped BigOperators

namespace IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Counting letters by position -/

omit [DecidableEq α] [NeZero n] in
/-- The letters whose position in the order `e` is `< k` are `k` in number. -/
theorem card_filter_lt (e : α ≃ Fin n) {k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter (fun a => (e a).val < k)).card = k := by
  classical
  have himg : ((Finset.univ.filter (fun a => (e a).val < k)).image (fun a => (e a).val))
      = Finset.range k := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hi
      exact ⟨e.symm ⟨i, by omega⟩, by simpa using hi, by simp⟩
  rw [← Finset.card_image_of_injective _ (f := fun a => (e a).val)
    (fun a b h => e.injective (Fin.ext h)), himg, Finset.card_range]

omit [DecidableEq α] [NeZero n] in
/-- The letters whose position in the order `e` is `≤ k` are `k + 1` in number. -/
theorem card_filter_le (e : α ≃ Fin n) {k : ℕ} (hk : k < n) :
    (Finset.univ.filter (fun a => (e a).val ≤ k)).card = k + 1 := by
  classical
  have himg : ((Finset.univ.filter (fun a => (e a).val ≤ k)).image (fun a => (e a).val))
      = Finset.range (k + 1) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      omega
    · intro hi
      exact ⟨e.symm ⟨i, by omega⟩, by simpa using (show i ≤ k by omega), by simp⟩
  rw [← Finset.card_image_of_injective _ (f := fun a => (e a).val)
    (fun a b h => e.injective (Fin.ext h)), himg, Finset.card_range]

omit [DecidableEq α] [NeZero n] in
/-- The letters whose position in the order `e` is `> k` are `n - k - 1` in number. -/
theorem card_filter_gt (e : α ≃ Fin n) {k : ℕ} (_hk : k < n) :
    (Finset.univ.filter (fun a => k < (e a).val)).card = n - k - 1 := by
  classical
  have himg : ((Finset.univ.filter (fun a => k < (e a).val)).image (fun a => (e a).val))
      = Finset.Ico (k + 1) n := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ha, (e a).isLt⟩
    · rintro ⟨hi1, hi2⟩
      exact ⟨e.symm ⟨i, hi2⟩, by simpa using hi1, by simp⟩
  rw [← Finset.card_image_of_injective _ (f := fun a => (e a).val)
    (fun a b h => e.injective (Fin.ext h)), himg, Nat.card_Ico]
  omega

/-! ## 2. `true` blocks do not change the top order, `false` blocks the bottom order -/

omit [DecidableEq α] in
theorem true_block_piTop (P : IETDatum₂ α n) (j : ℕ) :
    (vertex P (List.replicate j true)).piTop = P.piTop := by
  induction j with
  | zero => simp
  | succ j ih => rw [vertex_replicate_succ, IETDatum₂.rvStep_piTop_true]; exact ih

omit [DecidableEq α] in
theorem false_block_piBottom (P : IETDatum₂ α n) (j : ℕ) :
    (vertex P (List.replicate j false)).piBottom = P.piBottom := by
  induction j with
  | zero => simp
  | succ j ih => rw [vertex_replicate_succ, IETDatum₂.rvStep_piBottom_false]; exact ih

omit [DecidableEq α] in
/-- `false` blocks preserve the letters at top positions `≤ pivot`. -/
theorem false_block_prefix (P : IETDatum₂ α n) (j : ℕ) (a : α)
    (ha : (P.piTop a).val ≤ (P.piTop (P.last false)).val) :
    (vertex P (List.replicate j false)).piTop a = P.piTop a := by
  have h := true_block_prefix P.inv j a (by simpa using ha)
  rw [vertex_replicate_false_eq]
  simpa using h

/-! ## 3. The sub-claim: in Case B a suitable `c'` exists -/

omit [DecidableEq α] in
/-- **Sub-claim of the descent** (Case B): if every letter before `d = last false` in the top order
sits at a bottom position `≤ pos_L(last true)`, then there is a letter after `d` in the top order
whose bottom position is strictly less than the maximal bottom position of those letters. -/
theorem descent_subclaim (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (hm : 0 < (P.piTop (P.last false)).val)
    (_hA : ∀ u, (P.piTop u).val < (P.piTop (P.last false)).val →
      (P.piBottom u).val ≤ (P.piBottom (P.last true)).val) :
    ∃ c', (P.piTop (P.last false)).val < (P.piTop c').val ∧
      (P.piBottom c').val < (Finset.univ.filter (fun a =>
        (P.piTop a).val < (P.piTop (P.last false)).val)).sup (fun a => (P.piBottom a).val) := by
  classical
  set m : ℕ := (P.piTop (P.last false)).val with hm_def
  set S : Finset α := Finset.univ.filter (fun a => (P.piTop a).val < m) with hS_def
  set ML : ℕ := S.sup (fun a => (P.piBottom a).val) with hML_def
  by_contra hcon
  push Not at hcon
  -- basic facts
  have hmn : m < n := (P.piTop (P.last false)).isLt
  have hmn2 : m ≤ n - 2 := by
    have hne : P.last false ≠ P.last true := (last_true_ne_last_false P hP hn).symm
    have hlt : m ≠ n - 1 := by
      intro h
      have h1 : P.piTop (P.last false) = IETDatum₂.lastPos n :=
        Fin.ext (by rw [lastPos_val]; exact h)
      have h2 : P.piTop (P.last false) = P.piTop (P.last true) := by rw [h1, IETDatum₂.last_top]
      exact hne (P.piTop.injective h2)
    have := (P.piTop (P.last false)).isLt
    omega
  have hS_card : S.card = m := by
    rw [hS_def]
    exact card_filter_lt P.piTop (by omega)
  have hd_not : P.last false ∉ S := by
    rw [hS_def, Finset.mem_filter]
    intro h
    exact absurd h.2 (by omega)
  have hy_mem : P.piTop.symm (0 : Fin n) ∈ S := by
    rw [hS_def, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Equiv.apply_symm_apply, Fin.val_zero]
    omega
  have hSne : S.Nonempty := ⟨_, hy_mem⟩
  have hS_sub : ∀ u ∈ S, (P.piBottom u).val ≤ ML := by
    intro u hu
    rw [hML_def]
    exact Finset.le_sup (f := fun a => (P.piBottom a).val) hu
  obtain ⟨u₀, hu₀, hu₀sup⟩ :=
    Finset.exists_mem_eq_sup S hSne (fun a => (P.piBottom a).val)
  have hML_eq : (P.piBottom u₀).val = ML := by rw [hML_def, ← hu₀sup]
  have hML_lt : ML < n := by rw [← hML_eq]; exact (P.piBottom u₀).isLt
  -- letters after `d` in the top order sit strictly after `ML` in the bottom order
  have hstrict : ∀ a, m < (P.piTop a).val → ML < (P.piBottom a).val := by
    intro a ha
    rcases Nat.lt_trichotomy (P.piBottom a).val ML with h | h | h
    · exact absurd (hcon a ha) (by omega)
    · exfalso
      have hPa : P.piBottom a = P.piBottom u₀ := Fin.ext (by rw [h, hML_eq])
      have hSa : a ∈ S := by rw [P.piBottom.injective hPa]; exact hu₀
      rw [hS_def, Finset.mem_filter] at hSa
      omega
    · exact h
  -- counting
  have hstep1 : m ≤ ML + 1 := by
    have hsub : S ⊆ Finset.univ.filter (fun a => (P.piBottom a).val ≤ ML) := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS_sub a ha⟩
    have h1 := Finset.card_le_card hsub
    rw [hS_card, card_filter_le P.piBottom hML_lt] at h1
    exact h1
  have hstep2 : ML ≤ m := by
    set R : Finset α := Finset.univ.filter (fun a => m < (P.piTop a).val) with hR_def
    have hRcard : R.card = n - m - 1 := by
      rw [hR_def]
      exact card_filter_gt P.piTop hmn
    have hRsub : R ⊆ Finset.univ.filter (fun a => ML < (P.piBottom a).val) := by
      intro a ha
      rw [hR_def, Finset.mem_filter] at ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstrict a ha.2⟩
    have h2 := Finset.card_le_card hRsub
    rw [hRcard, card_filter_gt P.piBottom hML_lt] at h2
    omega
  have hdich : ML = m - 1 ∨ ML = m := by omega
  rcases hdich with hcase | hcase
  · -- `ML = m - 1`: `S` is an initial segment of both orders
    have hSproper : S ≠ Finset.univ := by
      intro h
      rw [h] at hd_not
      exact hd_not (Finset.mem_univ _)
    have heq : S = Finset.univ.filter (fun a => (P.piBottom a).val ≤ ML) := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro a ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS_sub a ha⟩
      · rw [hS_card, card_filter_le P.piBottom hML_lt]
        omega
    refine MeshShrink.no_block P hP S hSne hSproper ?_ ?_
    · intro a ha b hb
      rw [hS_def, Finset.mem_filter] at ha
      have hbm : ¬ ((P.piTop b).val < m) := fun h =>
        hb (by rw [hS_def, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩)
      omega
    · intro a ha b hb
      rw [heq, Finset.mem_filter] at ha
      have hbm : ¬ ((P.piBottom b).val ≤ ML) := fun h =>
        hb (by rw [heq, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩)
      omega
  · -- `ML = m`: `S ∪ {d}` is an initial segment of both orders
    set R : Finset α := Finset.univ.filter (fun a => m < (P.piTop a).val) with hR_def
    have hRcard : R.card = n - m - 1 := by
      rw [hR_def]
      exact card_filter_gt P.piTop hmn
    have hReq : R = Finset.univ.filter (fun a => ML < (P.piBottom a).val) := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro a ha
        rw [hR_def, Finset.mem_filter] at ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstrict a ha.2⟩
      · rw [hRcard, card_filter_gt P.piBottom hML_lt]
        omega
    have hd_not_R : P.last false ∉ R := by
      rw [hR_def, Finset.mem_filter]
      intro h
      exact absurd h.2 (by omega)
    have hd_le : (P.piBottom (P.last false)).val ≤ m := by
      rw [hReq, Finset.mem_filter] at hd_not_R
      push Not at hd_not_R
      have h := hd_not_R (Finset.mem_univ _)
      omega
    set S' : Finset α := insert (P.last false) S with hS'_def
    have hS'_card : S'.card = m + 1 := by
      rw [hS'_def, Finset.card_insert_of_notMem hd_not, hS_card]
    have hS'_eq : S' = Finset.univ.filter (fun a => (P.piBottom a).val ≤ m) := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro a ha
        rw [hS'_def, Finset.mem_insert] at ha
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rcases ha with rfl | haS
        · exact hd_le
        · have := hS_sub a haS
          omega
      · rw [hS'_card, card_filter_le P.piBottom hmn]
    have hcardα : Fintype.card α = n := by
      rw [Fintype.card_congr P.piTop, Fintype.card_fin]
    refine MeshShrink.no_block P hP S' (by rw [hS'_def]; exact Finset.insert_nonempty _ _) ?_ ?_ ?_
    · intro h
      rw [h, Finset.card_univ, hcardα] at hS'_card
      omega
    · intro a ha b hb
      rw [hS'_def, Finset.mem_insert] at ha hb
      push Not at hb
      obtain ⟨hbd, hbS⟩ := hb
      have hatop : (P.piTop a).val ≤ m := by
        rcases ha with rfl | haS
        · simp [hm_def]
        · rw [hS_def, Finset.mem_filter] at haS
          omega
      have hbtop : m < (P.piTop b).val := by
        have hbm : ¬ ((P.piTop b).val < m) := fun h =>
          hbS (by rw [hS_def, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩)
        have hne : (P.piTop b).val ≠ m := by
          intro h
          exact hbd (P.piTop.injective (Fin.ext h))
        omega
      omega
    · intro a ha b hb
      rw [hS'_eq, Finset.mem_filter] at ha
      have hbm : ¬ ((P.piBottom b).val ≤ m) := fun h =>
        hb (by rw [hS'_eq, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩)
      omega

/-! ## 4. The descent step -/

omit [DecidableEq α] in
/-- **The descent step**: if the bottom-last letter is not first in the top
order, some nonempty word strictly decreases its top position. -/
theorem descent_step (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (hm : 0 < (P.piTop (P.last false)).val) :
    ∃ w : List Bool, ((vertex P w).piTop ((vertex P w).last false)).val
      < (P.piTop (P.last false)).val := by
  classical
  by_cases hcaseA : ∃ u, (P.piTop u).val < (P.piTop (P.last false)).val ∧
      (P.piBottom (P.last true)).val < (P.piBottom u).val
  · -- Case A: a block of `true` steps brings `u` to the last bottom position
    obtain ⟨u, huS, hupos⟩ := hcaseA
    refine ⟨List.replicate (n - 1 - (P.piBottom u).val) true, ?_⟩
    have hlast : (vertex P (List.replicate (n - 1 - (P.piBottom u).val) true)).last false = u := by
      have h := exists_true_block P (P.piBottom u) hupos
      rw [Equiv.symm_apply_apply] at h
      change (vertex P (List.replicate (n - 1 - (P.piBottom u).val) true)).piBottom.symm
        (IETDatum₂.lastPos n) = u
      rw [← h, Equiv.symm_apply_apply]
    rw [hlast, true_block_piTop]
    exact huS
  · -- Case B: a `false` block followed by a `true` block
    push Not at hcaseA
    have hA' : ∀ u, (P.piTop u).val < (P.piTop (P.last false)).val →
        (P.piBottom u).val ≤ (P.piBottom (P.last true)).val := by
      intro u hu
      have h := hcaseA u hu
      omega
    obtain ⟨c', hc'1, hc'2⟩ := descent_subclaim P hP hn hm hA'
    -- the `false` block puts `c'` last in the top order
    set j₁ : ℕ := n - 1 - (P.piTop c').val with hj₁
    set Q₁ : IETDatum₂ α n := vertex P (List.replicate j₁ false) with hQ₁
    have hQ₁_top : Q₁.piTop c' = IETDatum₂.lastPos n := by
      rw [hQ₁, hj₁]
      simpa using exists_false_block P (P.piTop c') hc'1
    have hQ₁_last : Q₁.last true = c' := by
      change Q₁.piTop.symm (IETDatum₂.lastPos n) = c'
      rw [← hQ₁_top, Equiv.symm_apply_apply]
    -- the letter of `S` with maximal bottom position
    set S : Finset α :=
      Finset.univ.filter (fun a => (P.piTop a).val < (P.piTop (P.last false)).val) with hS
    have hy_mem : P.piTop.symm (0 : Fin n) ∈ S := by
      rw [hS, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Equiv.apply_symm_apply, Fin.val_zero]
      omega
    obtain ⟨u₀, hu₀, hu₀sup⟩ := Finset.exists_mem_eq_sup S ⟨_, hy_mem⟩
      (fun a => (P.piBottom a).val)
    have hu₀S : (P.piTop u₀).val < (P.piTop (P.last false)).val := by
      rw [hS, Finset.mem_filter] at hu₀
      exact hu₀.2
    have hu₀pos : (P.piBottom c').val < (P.piBottom u₀).val := by
      rw [← hu₀sup]
      exact hc'2
    -- the `true` block brings `u₀` to the last bottom position
    have hpivot : (Q₁.piBottom (Q₁.last true)).val < (Q₁.piBottom u₀).val := by
      rw [hQ₁_last, hQ₁, false_block_piBottom]
      exact hu₀pos
    set j₂ : ℕ := n - 1 - (Q₁.piBottom u₀).val with hj₂
    set Q₂ : IETDatum₂ α n := vertex Q₁ (List.replicate j₂ true) with hQ₂
    have hQ₂_last : Q₂.last false = u₀ := by
      have h := exists_true_block Q₁ (Q₁.piBottom u₀) hpivot
      rw [Equiv.symm_apply_apply] at h
      change Q₂.piBottom.symm (IETDatum₂.lastPos n) = u₀
      rw [hQ₂, hj₂, ← h, Equiv.symm_apply_apply]
    have hQ₂_top : Q₂.piTop u₀ = P.piTop u₀ := by
      rw [hQ₂, true_block_piTop, hQ₁]
      exact false_block_prefix P j₁ u₀ (by omega)
    refine ⟨List.replicate j₁ false ++ List.replicate j₂ true, ?_⟩
    have hgoal : vertex P (List.replicate j₁ false ++ List.replicate j₂ true) = Q₂ := by
      rw [vertex_append, hQ₂]
    rw [hgoal, hQ₂_last, hQ₂_top]
    exact hu₀S

/-! ## 5. Iterating the descent: reaching a state whose last-true letter is the bottom-first one -/

omit [DecidableEq α] in
theorem true_block_last_true (P : IETDatum₂ α n) (j : ℕ) :
    (vertex P (List.replicate j true)).last true = P.last true := by
  induction j with
  | zero => simp
  | succ j ih => rw [vertex_replicate_succ, IETDatum₂.rvStep_last_self]; exact ih

omit [DecidableEq α] in
theorem false_block_last_false (P : IETDatum₂ α n) (j : ℕ) :
    (vertex P (List.replicate j false)).last false = P.last false := by
  induction j with
  | zero => simp
  | succ j ih => rw [vertex_replicate_succ, IETDatum₂.rvStep_last_self]; exact ih

omit [DecidableEq α] in
/-- From every irreducible vertex, some word ends with the top-first letter last in the
bottom order. -/
theorem exists_last_false_first (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∃ w : List Bool, (vertex P w).last false = P.piTop.symm 0 := by
  have key : ∀ m, ∀ (Q : IETDatum₂ α n), Q.Irreducible → (Q.piTop (Q.last false)).val = m →
      ∃ w, (vertex Q w).last false = Q.piTop.symm 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro Q hQ hm
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · refine ⟨[], ?_⟩
        simp only [vertex_nil]
        have h0' : Q.piTop (Q.last false) = (0 : Fin n) :=
          Fin.ext (by rw [hm, h0, Fin.val_zero])
        rw [← h0', Equiv.symm_apply_apply]
      · obtain ⟨w, hw⟩ := descent_step Q hQ hn (by omega)
        obtain ⟨w', hw'⟩ := ih _ (by omega) (vertex Q w) (vertex_irreducible Q w hQ) rfl
        exact ⟨w ++ w', by rw [vertex_append, hw', piTop_zero_letter]⟩
  exact key _ P hP rfl

omit [DecidableEq α] in
/-- From every irreducible vertex, some word ends with the bottom-first letter last in
the top order. -/
theorem exists_last_true_first (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∃ w : List Bool, (vertex P w).last true = P.piBottom.symm 0 := by
  obtain ⟨w₁, hw₁⟩ := exists_last_false_first P hP hn
  set Q : IETDatum₂ α n := vertex P w₁ with hQ
  have hQy : Q.last false = Q.piTop.symm 0 := by
    rw [hQ, piTop_zero_letter]
    exact hw₁
  have hQx : Q.piBottom.symm (0 : Fin n) = P.piBottom.symm 0 := by
    rw [hQ]; exact piBottom_zero_letter P w₁
  have hxne : P.piBottom.symm (0 : Fin n) ≠ Q.piTop.symm 0 := by
    rw [← hQx]
    exact first_ne Q (by rw [hQ]; exact vertex_irreducible P w₁ hP) hn
  have hlast_lf : Q.piTop (Q.last false) = (0 : Fin n) := by rw [hQy, Equiv.apply_symm_apply]
  have hx_ne : Q.piTop (P.piBottom.symm (0 : Fin n)) ≠ (0 : Fin n) := by
    intro h
    have h4 : Q.piTop.symm (Q.piTop (P.piBottom.symm (0 : Fin n))) = P.piBottom.symm 0 :=
      Equiv.symm_apply_apply _ _
    rw [h] at h4
    exact hxne h4.symm
  have hi : (Q.piTop (Q.last false)).val < (Q.piTop (P.piBottom.symm 0)).val := by
    rw [hlast_lf, Fin.val_zero]
    exact Fin.pos_iff_ne_zero.mpr hx_ne
  have h := exists_false_block Q (Q.piTop (P.piBottom.symm 0)) hi
  rw [Equiv.symm_apply_apply] at h
  refine ⟨w₁ ++ List.replicate (n - 1 - (Q.piTop (P.piBottom.symm 0)).val) false, ?_⟩
  rw [vertex_append]
  change (vertex Q (List.replicate (n - 1 - (Q.piTop (P.piBottom.symm 0)).val) false)).piTop.symm
    (IETDatum₂.lastPos n) = P.piBottom.symm 0
  rw [← h, Equiv.symm_apply_apply]

/-! ## 6. The pair manoeuvres and `PairReach` -/

omit [DecidableEq α] in
/-- In a state whose last-true letter is `x = piBottom.symm 0`, a `true` block puts any other
letter last in the bottom order. -/
theorem exists_true_block_last_of_first (Q : IETDatum₂ α n) (hx : Q.last true = Q.piBottom.symm 0)
    (u : α) (hu : u ≠ Q.piBottom.symm 0) :
    ∃ j, (vertex Q (List.replicate j true)).last false = u ∧
      (vertex Q (List.replicate j true)).last true = Q.piBottom.symm 0 := by
  have hpos : (Q.piBottom (Q.last true)).val < (Q.piBottom u).val := by
    have h1 : Q.piBottom (Q.last true) = (0 : Fin n) := by rw [hx, Equiv.apply_symm_apply]
    have h2 : Q.piBottom u ≠ (0 : Fin n) := by
      intro h
      have h3 : u = Q.piBottom.symm (0 : Fin n) := by
        rw [← Equiv.symm_apply_apply Q.piBottom u, h]
      exact hu h3
    rw [h1, Fin.val_zero]
    exact Fin.pos_iff_ne_zero.mpr h2
  have h := exists_true_block Q (Q.piBottom u) hpos
  rw [Equiv.symm_apply_apply] at h
  refine ⟨n - 1 - (Q.piBottom u).val, ?_, ?_⟩
  · change (vertex Q (List.replicate (n - 1 - (Q.piBottom u).val) true)).piBottom.symm
      (IETDatum₂.lastPos n) = u
    rw [← h, Equiv.symm_apply_apply]
  · rw [true_block_last_true]
    exact hx

omit [DecidableEq α] in
/-- A `false` block puts any letter after the bottom-last one last in the top order. -/
theorem exists_false_block_last_of_pivot (Q : IETDatum₂ α n) (u : α)
    (hu : (Q.piTop (Q.last false)).val < (Q.piTop u).val) :
    ∃ j, (vertex Q (List.replicate j false)).last true = u ∧
      (vertex Q (List.replicate j false)).last false = Q.last false := by
  have h := exists_false_block Q (Q.piTop u) hu
  rw [Equiv.symm_apply_apply] at h
  refine ⟨n - 1 - (Q.piTop u).val, ?_, ?_⟩
  · change (vertex Q (List.replicate (n - 1 - (Q.piTop u).val) false)).piTop.symm
      (IETDatum₂.lastPos n) = u
    rw [← h, Equiv.symm_apply_apply]
  · rw [false_block_last_false]

omit [DecidableEq α] in
/-- **The last step of Cor. 4**: in a state whose last-true letter is the
bottom-first letter `x`, every ordered pair of distinct letters occurs as `(last e, last !e)`. -/
theorem pair_of_last_true_first (Q : IETDatum₂ α n) (hx : Q.last true = Q.piBottom.symm 0)
    {a b : α} (hne : a ≠ b) :
    ∃ w : List Bool, ∃ e : Bool, (vertex Q w).last e = a ∧ (vertex Q w).last (!e) = b := by
  classical
  have hbot := exists_true_block_last_of_first Q hx
  by_cases ha : a = Q.piBottom.symm 0
  · -- `a` is the bottom-first letter: bring `b` to the bottom-last position
    obtain ⟨j, hj1, hj2⟩ := hbot b (by rw [← ha]; exact hne.symm)
    refine ⟨List.replicate j true, true, ?_, ?_⟩
    · rw [hj2, ha]
    · change (vertex Q (List.replicate j true)).last false = b
      exact hj1
  · by_cases hb : b = Q.piBottom.symm 0
    · -- `b` is the bottom-first letter: bring `a` to the bottom-last position
      obtain ⟨j, hj1, hj2⟩ := hbot a ha
      refine ⟨List.replicate j true, false, ?_, ?_⟩
      · show (vertex Q (List.replicate j true)).last false = a
        exact hj1
      · change (vertex Q (List.replicate j true)).last true = b
        rw [hj2, hb]
    · -- both differ from the bottom-first letter
      obtain ⟨j₁, hj₁1, hj₁2⟩ := hbot b hb
      set Q₁ : IETDatum₂ α n := vertex Q (List.replicate j₁ true) with hQ₁
      have hQ₁false : Q₁.last false = b := hj₁1
      have hQ₁top : Q₁.piTop = Q.piTop := by rw [hQ₁]; exact true_block_piTop Q j₁
      by_cases hcmp : (Q.piTop b).val < (Q.piTop a).val
      · -- then bring `a` to the top-last position from `Q₁`
        obtain ⟨j₂, hj₂1, hj₂2⟩ :=
          exists_false_block_last_of_pivot Q₁ a (by rw [hQ₁false, hQ₁top]; exact hcmp)
        refine ⟨List.replicate j₁ true ++ List.replicate j₂ false, true, ?_, ?_⟩
        · rw [vertex_append]
          change (vertex Q₁ (List.replicate j₂ false)).last true = a
          exact hj₂1
        · rw [vertex_append]
          change (vertex Q₁ (List.replicate j₂ false)).last false = b
          rw [hj₂2, hQ₁false]
      · -- otherwise bring `a` to the bottom-last position and then `b` to the top-last one
        have hlt : (Q.piTop a).val < (Q.piTop b).val := by
          have hne' : (Q.piTop a).val ≠ (Q.piTop b).val := fun h =>
            hne (Q.piTop.injective (Fin.ext h))
          omega
        obtain ⟨j₂, hj₂1, hj₂2⟩ := hbot (u := a) ha
        set Q' : IETDatum₂ α n := vertex Q (List.replicate j₂ true) with hQ'
        have hQ'false : Q'.last false = a := by rw [hQ']; exact hj₂1
        have hQ'top : Q'.piTop = Q.piTop := by rw [hQ']; exact true_block_piTop Q j₂
        obtain ⟨j₃, hj₃1, hj₃2⟩ :=
          exists_false_block_last_of_pivot Q' b (by rw [hQ'false, hQ'top]; exact hlt)
        refine ⟨List.replicate j₂ true ++ List.replicate j₃ false, false, ?_, ?_⟩
        · rw [vertex_append]
          change (vertex Q' (List.replicate j₃ false)).last false = a
          rw [hj₃2, hQ'false]
        · rw [vertex_append]
          change (vertex Q' (List.replicate j₃ false)).last true = b
          exact hj₃1

omit [DecidableEq α] in
/-- **`PairReach`**: from every irreducible vertex, every ordered pair of distinct letters occurs,
at some reachable vertex, as the pair `(last e, last !e)` of one of the two arrows. -/
theorem pairReach (P : IETDatum₂ α n) (_hP : P.Irreducible) (hn : 2 ≤ n) : Path.PairReach P := by
  intro v hv a b hne
  obtain ⟨w₁, hw₁⟩ := exists_last_true_first v hv hn
  have hlast : (vertex v w₁).last true = (vertex v w₁).piBottom.symm (0 : Fin n) := by
    rw [piBottom_zero_letter]
    exact hw₁
  obtain ⟨w₂, e, h2a, h2b⟩ := pair_of_last_true_first (vertex v w₁) hlast hne
  exact ⟨w₁ ++ w₂, e, by rw [vertex_append]; exact h2a, by rw [vertex_append]; exact h2b⟩

omit [DecidableEq α] in
/-- **`PairReach` with no hypothesis on `n`**: `PairReach` is vacuous for a single letter, and
`pairReach` covers `n ≥ 2`. -/
theorem pairReach_all (P : IETDatum₂ α n) (hP : P.Irreducible) : Path.PairReach P := by
  by_cases hn : 2 ≤ n
  · exact pairReach P hP hn
  · intro v hv a b hne
    exfalso
    have hcard : Fintype.card α = n := by rw [Fintype.card_congr P.piTop, Fintype.card_fin]
    have h1 : Fintype.card α ≤ 1 := by omega
    exact hne (Fintype.card_le_one_iff.mp h1 a b)

/-- **The uniform constant `C₁` of Lemma 2, unconditional.** -/
theorem exists_uniform_bound' (hn : 2 ≤ n) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ (P : IETDatum₂ α n), P.Irreducible →
      ∃ w : List Bool, ∀ a b, 1 ≤ Path.Q P w a b ∧ (Path.Q P w a b : ℝ) ≤ C₁ :=
  Path.exists_uniform_bound (fun Q hQ => pairReach Q hQ hn)

end IETDatum₂

end
