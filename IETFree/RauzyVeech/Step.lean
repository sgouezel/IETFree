/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.Basic

/-!
# The Rauzy–Veech step: statements

The step and the path combinatorics: the last letters `last`, the elementary matrix `rvMat`, the
product `IETDatum₂.Path.Q` along a word, and the inverse of an irreducible permutation. -/

open MeasureTheory
open scoped BigOperators ENNReal NNReal


namespace IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- The last position of `Fin n`, as a `Fin n` (needs `n ≠ 0`). -/
def lastPos (n : ℕ) [NeZero n] : Fin n := ⟨n - 1, by have := NeZero.ne n; omega⟩

/-- The letter at the last position in the order `ε` (`true` = top, `false` = bottom): the source's
`α_ε`, the *name* of an arrow of type `ε`. -/
def last (P : IETDatum₂ α n) (ε : Bool) : α :=
  if ε then P.piTop.symm (lastPos n) else P.piBottom.symm (lastPos n)

omit [DecidableEq α] in
@[simp] theorem last_top (P : IETDatum₂ α n) : P.piTop (P.last true) = lastPos n := by
  simp [last]

omit [DecidableEq α] in
@[simp] theorem last_bottom (P : IETDatum₂ α n) : P.piBottom (P.last false) = lastPos n := by
  simp [last]

/-! ## 0. The inverse of an irreducible permutation -/

theorem IsIrreduciblePerm.symm {n : ℕ} {π : Equiv.Perm (Fin n)} (h : IsIrreduciblePerm π) :
    IsIrreduciblePerm π.symm := by
  intro k hk i
  have key (j : Fin n) (hj : j ≤ k) : π j ≤ k := by
    have hsurj : Function.Surjective
        (fun a : {a : Fin n // a ≤ k} => (⟨π.symm a.1, hk a.1 a.2⟩ : {a : Fin n // a ≤ k})) := by
      apply Finite.surjective_of_injective
      intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext (π.symm.injective hab)
    obtain ⟨a, ha⟩ := hsurj ⟨j, hj⟩
    simp only [Subtype.mk.injEq] at ha
    rw [← ha, Equiv.apply_symm_apply]
    exact a.2
  exact h k key i

/-! ## 1. Inserting the last position just after `p` -/

section Insert

variable {n : ℕ} [NeZero n]

/-- The last position of `Fin n`. -/
lemma lastPos_val : (IETDatum₂.lastPos n).val = n - 1 := rfl

/-- Move the element at the last position to the position just after `p`, shifting the letters
strictly in between up by one. -/
def insertFun (p : Fin n) (h : p.val + 1 < n) (k : Fin n) : Fin n :=
  if k.val ≤ p.val then k
  else if k = IETDatum₂.lastPos n then ⟨p.val + 1, h⟩
  else ⟨min (k.val + 1) (n - 1), by have := k.isLt; omega⟩

/-- The inverse of `insertFun`: move the element at position `p + 1` to the last position. -/
def removeFun (p : Fin n) (_h : p.val + 1 < n) (k : Fin n) : Fin n :=
  if k.val ≤ p.val then k
  else if k.val = p.val + 1 then IETDatum₂.lastPos n
  else ⟨k.val - 1, by have := k.isLt; omega⟩

lemma insertFun_of_le {p : Fin n} (h : p.val + 1 < n) {k : Fin n} (hk : k.val ≤ p.val) :
    insertFun p h k = k := by
  rw [insertFun, if_pos hk]

lemma insertFun_lastPos {p : Fin n} (h : p.val + 1 < n) :
    insertFun p h (IETDatum₂.lastPos n) = ⟨p.val + 1, h⟩ := by
  rw [insertFun, if_neg (by rw [lastPos_val]; omega), if_pos rfl]

lemma insertFun_of_gt {p : Fin n} (h : p.val + 1 < n) {k : Fin n} (hk : p.val < k.val)
    (hk' : k ≠ IETDatum₂.lastPos n) :
    (insertFun p h k).val = k.val + 1 := by
  have hk2 : k.val + 1 ≤ n - 1 := by
    have hlt := k.isLt
    have hne : k.val ≠ n - 1 := fun hh => hk' (Fin.ext (by rw [lastPos_val, hh]))
    omega
  rw [insertFun, if_neg (by omega), if_neg hk', Fin.val_mk, Nat.min_eq_left hk2]

lemma removeFun_of_le {p : Fin n} (h : p.val + 1 < n) {k : Fin n} (hk : k.val ≤ p.val) :
    removeFun p h k = k := by
  rw [removeFun, if_pos hk]

lemma removeFun_insertFun {p : Fin n} (h : p.val + 1 < n) (k : Fin n) :
    removeFun p h (insertFun p h k) = k := by
  by_cases h1 : k.val ≤ p.val
  · rw [insertFun_of_le h h1, removeFun_of_le h h1]
  · by_cases h2 : k = IETDatum₂.lastPos n
    · rw [h2, insertFun_lastPos h, removeFun, if_neg (by simp), if_pos (by simp)]
    · have hk : p.val < k.val := by
        have := k.isLt
        omega
      have hval := insertFun_of_gt h hk h2
      rw [removeFun, if_neg (by rw [hval]; omega), if_neg (by rw [hval]; omega)]
      exact Fin.ext (by rw [Fin.val_mk, hval]; omega)

lemma insertFun_removeFun {p : Fin n} (h : p.val + 1 < n) (k : Fin n) :
    insertFun p h (removeFun p h k) = k := by
  by_cases h1 : k.val ≤ p.val
  · rw [removeFun, if_pos h1, insertFun_of_le h h1]
  · rw [removeFun, if_neg h1]
    by_cases h2 : k.val = p.val + 1
    · rw [if_pos h2, insertFun_lastPos h, Fin.ext_iff, h2]
    · rw [if_neg h2]
      have hk : p.val + 1 < k.val := by
        have := k.isLt
        omega
      have hk' : (⟨k.val - 1, by have := k.isLt; omega⟩ : Fin n) ≠ IETDatum₂.lastPos n := by
        intro hh
        have hh' : k.val - 1 = n - 1 := by
          have := congrArg Fin.val hh
          simpa [lastPos_val] using this
        omega
      have hk2 : p.val < (⟨k.val - 1, by have := k.isLt; omega⟩ : Fin n).val := by
        change p.val < k.val - 1
        omega
      apply Fin.ext
      rw [insertFun_of_gt h hk2 hk']
      change k.val - 1 + 1 = k.val
      omega

/-- The insertion as a permutation of the positions.  It is the identity (junk value) when `p` is
already the last position, which cannot happen for irreducible data with `n ≥ 2`. -/
noncomputable def insertEquiv (p : Fin n) : Equiv.Perm (Fin n) :=
  if h : p.val + 1 < n then
    { toFun := insertFun p h
      invFun := removeFun p h
      left_inv := removeFun_insertFun h
      right_inv := insertFun_removeFun h }
  else 1

lemma insertEquiv_apply_le {p : Fin n} {k : Fin n} (hk : k.val ≤ p.val) :
    insertEquiv p k = k := by
  by_cases h : p.val + 1 < n
  · rw [insertEquiv, dif_pos h]
    exact insertFun_of_le h hk
  · rw [insertEquiv, dif_neg h]
    rfl

lemma insertEquiv_lastPos {p : Fin n} (h : p.val + 1 < n) :
    insertEquiv p (IETDatum₂.lastPos n) = ⟨p.val + 1, h⟩ := by
  rw [insertEquiv, dif_pos h]
  exact insertFun_lastPos h

lemma insertEquiv_apply_gt {p : Fin n} {k : Fin n} (h : p.val + 1 < n) (hk : p.val < k.val)
    (hk' : k ≠ IETDatum₂.lastPos n) : (insertEquiv p k).val = k.val + 1 := by
  rw [insertEquiv, dif_pos h]
  exact insertFun_of_gt h hk hk'

omit [Fintype α] in
/-- The insertion formula along a bijection `e : α ≃ Fin n` whose last letter is `c`. -/
theorem trans_insertEquiv_apply_val {α : Type*} [DecidableEq α] {n : ℕ} [NeZero n]
    (e : α ≃ Fin n) (p : Fin n) {c : α} (hc : e c = IETDatum₂.lastPos n) (a : α) :
    ((e.trans (insertEquiv p)) a).val =
      if (e a).val ≤ p.val then (e a).val else if a = c then p.val + 1 else (e a).val + 1 := by
  rw [Equiv.trans_apply]
  by_cases h1 : (e a).val ≤ p.val
  · rw [if_pos h1, insertEquiv_apply_le h1]
  · rw [if_neg h1]
    have hp : p.val + 1 < n := by
      have := (e a).isLt
      omega
    by_cases h2 : a = c
    · subst h2
      rw [if_pos rfl, hc, insertEquiv_lastPos (p := p) hp]
    · rw [if_neg h2]
      have hne : e a ≠ IETDatum₂.lastPos n := by
        intro hh
        exact h2 (e.injective (by rw [hh, hc]))
      rw [insertEquiv_apply_gt (p := p) (k := e a) hp (by omega) hne]

end Insert

/-! ## 2. The Rauzy–Veech step -/

section Step

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- The pivot of the step of type `ε`: the position, in the order that is modified, of the letter
that is last in the order that is kept. -/
noncomputable def pivot (P : IETDatum₂ α n) (ε : Bool) : Fin n :=
  if ε then P.piBottom (P.last true) else P.piTop (P.last false)

omit [DecidableEq α] in
@[simp] theorem pivot_true (P : IETDatum₂ α n) : pivot P true = P.piBottom (P.last true) := rfl

omit [DecidableEq α] in
@[simp] theorem pivot_false (P : IETDatum₂ α n) : pivot P false = P.piTop (P.last false) := rfl

/-- **The Rauzy–Veech step** (source 4.1).  The `ε`-order is unchanged; in the `1-ε` order the
letter `last (1-ε)` is moved from the last position to the position just after `last ε`, the
letters strictly in between shifting up by one. -/
noncomputable def rvStep (P : IETDatum₂ α n) (ε : Bool) : IETDatum₂ α n where
  piTop := if ε then P.piTop else P.piTop.trans (insertEquiv (pivot P ε))
  piBottom := if ε then P.piBottom.trans (insertEquiv (pivot P ε)) else P.piBottom

omit [DecidableEq α] in
@[simp] theorem rvStep_piTop_true (P : IETDatum₂ α n) :
    (rvStep P true).piTop = P.piTop := rfl

omit [DecidableEq α] in
@[simp] theorem rvStep_piBottom_false (P : IETDatum₂ α n) :
    (rvStep P false).piBottom = P.piBottom := rfl

omit [DecidableEq α] in
theorem rvStep_piBottom_true (P : IETDatum₂ α n) :
    (rvStep P true).piBottom =
      P.piBottom.trans (insertEquiv (P.piBottom (P.last true))) := rfl

omit [DecidableEq α] in
theorem rvStep_piTop_false (P : IETDatum₂ α n) :
    (rvStep P false).piTop =
      P.piTop.trans (insertEquiv (P.piTop (P.last false))) := rfl

omit [DecidableEq α] in
theorem rvStep_apply_true (P : IETDatum₂ α n) (a : α) :
    (rvStep P true).piBottom a =
      insertEquiv (P.piBottom (P.last true)) (P.piBottom a) := rfl

omit [DecidableEq α] in
theorem rvStep_apply_false (P : IETDatum₂ α n) (a : α) :
    (rvStep P false).piTop a =
      insertEquiv (P.piTop (P.last false)) (P.piTop a) := rfl

omit [DecidableEq α] in
/-- Exchanging the two orders exchanges the two types of step. -/
theorem rvStep_inv (P : IETDatum₂ α n) (ε : Bool) :
    (rvStep P ε).inv = rvStep P.inv (!ε) := by
  cases ε <;> rfl

/-- **Defining equation of the step, `ε = true`, in coordinates**: the new bottom position of a
letter is its old bottom position if it is not after the pivot, `pivot + 1` for the letter `last
false`, and its old position plus one for the letters strictly between.  (`Fin` addition is modular,
so the value form is the unconditional form of the equation; see `rvStep_piBottom_true_apply_le` and
`rvStep_piBottom_true_apply_last` for the two non-trivial branches.) -/
theorem rvStep_piBottom_true_apply_val (P : IETDatum₂ α n) (a : α) :
    ((rvStep P true).piBottom a).val =
      if (P.piBottom a).val ≤ (P.piBottom (P.last true)).val then (P.piBottom a).val
      else if a = P.last false then (P.piBottom (P.last true)).val + 1
      else (P.piBottom a).val + 1 := by
  rw [rvStep_apply_true]
  exact trans_insertEquiv_apply_val P.piBottom (P.piBottom (P.last true))
    (IETDatum₂.last_bottom P) a

/-- **Defining equation of the step, `ε = false`, in coordinates**. -/
theorem rvStep_piTop_false_apply_val (P : IETDatum₂ α n) (a : α) :
    ((rvStep P false).piTop a).val =
      if (P.piTop a).val ≤ (P.piTop (P.last false)).val then (P.piTop a).val
      else if a = P.last true then (P.piTop (P.last false)).val + 1
      else (P.piTop a).val + 1 := by
  rw [rvStep_apply_false]
  exact trans_insertEquiv_apply_val P.piTop (P.piTop (P.last false))
    (IETDatum₂.last_top P) a

omit [DecidableEq α] in
/-- The letters that are not after the pivot do not move (`ε = true`). -/
theorem rvStep_piBottom_true_apply_le (P : IETDatum₂ α n) {a : α}
    (ha : P.piBottom a ≤ P.piBottom (P.last true)) :
    (rvStep P true).piBottom a = P.piBottom a := by
  rw [rvStep_apply_true]
  exact insertEquiv_apply_le ha

omit [DecidableEq α] in
/-- The letter `last false` moves to the position just after the pivot (`ε = true`), when the
pivot is not the last position (always the case for irreducible data with `n ≥ 2`). -/
theorem rvStep_piBottom_true_apply_last (P : IETDatum₂ α n)
    (hp : (P.piBottom (P.last true)).val + 1 < n) :
    (rvStep P true).piBottom (P.last false) =
      ⟨(P.piBottom (P.last true)).val + 1, hp⟩ := by
  rw [rvStep_apply_true, IETDatum₂.last_bottom]
  exact insertEquiv_lastPos hp

omit [DecidableEq α] in
/-- The letters that are not after the pivot do not move (`ε = false`). -/
theorem rvStep_piTop_false_apply_le (P : IETDatum₂ α n) {a : α}
    (ha : P.piTop a ≤ P.piTop (P.last false)) :
    (rvStep P false).piTop a = P.piTop a := by
  rw [rvStep_apply_false]
  exact insertEquiv_apply_le ha

/-- `Fin` addition by `1` in coordinates, when there is no wrap-around. -/
lemma fin_add_one_val {p : Fin n} (h : p.val + 1 < n) : (p + 1).val = p.val + 1 := by
  rw [Fin.val_add_eq_of_add_lt]
  · rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  · rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    omega

/-- **Defining equation of the step, `ε = true`**: the top order is unchanged and the new bottom
position of a letter is its old bottom position if it is not after the pivot, `pivot + 1` for the
letter `last false`, and its old position plus one for the letters strictly between. -/
theorem rvStep_piBottom_true_apply (P : IETDatum₂ α n) (a : α) :
    (rvStep P true).piBottom a =
      if P.piBottom a ≤ P.piBottom (P.last true) then P.piBottom a
      else if a = P.last false then P.piBottom (P.last true) + 1
      else P.piBottom a + 1 := by
  apply Fin.ext
  by_cases h1 : P.piBottom a ≤ P.piBottom (P.last true)
  · rw [if_pos h1,
      rvStep_piBottom_true_apply_val,
      if_pos (show (P.piBottom a).val ≤ (P.piBottom (P.last true)).val from h1)]
  · have hpv : (P.piBottom (P.last true)).val < (P.piBottom a).val := by
      have h' : ¬ (P.piBottom a).val ≤ (P.piBottom (P.last true)).val := h1
      omega
    have hp : (P.piBottom (P.last true)).val + 1 < n := by
      have := (P.piBottom a).isLt
      omega
    rw [if_neg h1]
    by_cases h2 : a = P.last false
    · rw [if_pos h2, h2, rvStep_piBottom_true_apply_last P hp, Fin.val_mk, fin_add_one_val hp]
    · have hp' : (P.piBottom a).val + 1 < n := by
        have hne : (P.piBottom a).val ≠ n - 1 := by
          intro hh
          exact h2 (P.piBottom.injective (by
            rw [IETDatum₂.last_bottom]
            exact Fin.ext (by rw [lastPos_val, hh])))
        have := (P.piBottom a).isLt
        omega
      rw [if_neg h2,
        rvStep_piBottom_true_apply_val,
        if_neg (show ¬ ((P.piBottom a).val ≤ (P.piBottom (P.last true)).val) from h1),
        if_neg h2]
      exact (fin_add_one_val hp').symm

end Step
/-! ## 3. Irreducibility is preserved by the step -/

section Irreducible

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

omit [DecidableEq α] in
/-- **Irreducibility is preserved by a step of type `true`** (source p. 10).  If an initial segment
of the new bottom order is invariant, then so is the
same initial segment of the old bottom order (when it lies before the pivot), or else it contains
the pivot letter, whose top position is the last one. -/
theorem rvStep_irreducible_true (P : IETDatum₂ α n) (hP : P.Irreducible) :
    (rvStep P true).Irreducible := by
  intro k hk i
  set p : Fin n := P.piBottom (P.last true) with hp
  by_cases hle : k ≤ p
  · refine hP k ?_ i
    intro j hj
    have hj' : j.val ≤ p.val := by
      have h1 : j.val ≤ k.val := hj
      have h2 : k.val ≤ p.val := hle
      omega
    have hQ : (rvStep P true).piBottom (P.piBottom.symm j) = j := by
      rw [rvStep_apply_true, Equiv.apply_symm_apply]
      exact insertEquiv_apply_le hj'
    have hsymm : (rvStep P true).piBottom.symm j = P.piBottom.symm j := by
      have := congrArg (rvStep P true).piBottom.symm hQ.symm
      simpa using this
    have hperm : (rvStep P true).perm j = P.perm j := by
      change (rvStep P true).piTop ((rvStep P true).piBottom.symm j) = P.piTop (P.piBottom.symm j)
      rw [hsymm]
      rfl
    simpa only [hperm] using hk j hj
  · have hp_lt : p.val < k.val := by
      have h' : ¬ k.val ≤ p.val := hle
      omega
    have hQb : (rvStep P true).piBottom (P.last true) = p := by
      rw [rvStep_apply_true, ← hp]
      exact insertEquiv_apply_le (le_refl _)
    have h1 : (rvStep P true).perm ((rvStep P true).piBottom (P.last true)) ≤ k :=
      hk _ (by rw [hQb]; exact hp_lt.le)
    have h2 : (rvStep P true).perm ((rvStep P true).piBottom (P.last true)) =
        IETDatum₂.lastPos n := by
      change (rvStep P true).piTop
          ((rvStep P true).piBottom.symm ((rvStep P true).piBottom (P.last true)))
        = IETDatum₂.lastPos n
      rw [Equiv.symm_apply_apply]
      exact IETDatum₂.last_top P
    rw [h2] at h1
    have hk_last : k = IETDatum₂.lastPos n := by
      apply Fin.ext
      have h1' : (IETDatum₂.lastPos n).val ≤ k.val := h1
      rw [lastPos_val] at h1'
      change k.val = (IETDatum₂.lastPos n).val
      rw [lastPos_val]
      have := k.isLt
      omega
    rw [hk_last]
    change i.val ≤ (IETDatum₂.lastPos n).val
    rw [lastPos_val]
    have := i.isLt
    omega

omit [DecidableEq α] in
/-- **Irreducibility is preserved by a step of type `false`** (by symmetry with
`rvStep_irreducible_true`: exchanging the two orders exchanges the two types of step). -/
theorem rvStep_irreducible_false (P : IETDatum₂ α n) (hP : P.Irreducible) :
    (rvStep P false).Irreducible := by
  have h1 : P.inv.Irreducible := by
    change IsIrreduciblePerm P.inv.perm
    rw [IETDatum₂.perm_inv]
    exact IsIrreduciblePerm.symm hP
  have h2 : (rvStep P.inv true).Irreducible := rvStep_irreducible_true P.inv h1
  have heq : rvStep P false = (rvStep P.inv true).inv := rfl
  change IsIrreduciblePerm (rvStep P false).perm
  rw [heq, IETDatum₂.perm_inv]
  exact IsIrreduciblePerm.symm h2

omit [DecidableEq α] in
/-- **Irreducibility is preserved by the Rauzy–Veech step** (source 4.1, p. 10). -/
theorem rvStep_irreducible (P : IETDatum₂ α n) (hP : P.Irreducible) (ε : Bool) :
    (rvStep P ε).Irreducible := by
  cases ε with
  | false => exact rvStep_irreducible_false P hP
  | true => exact rvStep_irreducible_true P hP

omit [DecidableEq α] in
/-- For irreducible data with `n ≥ 2`, the letter last in the top order is not last in the bottom
order: otherwise the permutation would fix its last point, contradicting irreducibility. -/
theorem pivot_true_ne_lastPos (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    P.piBottom (P.last true) ≠ IETDatum₂.lastPos n := by
  intro h
  have hk : ∀ i : Fin n, i ≤ (⟨n - 2, by omega⟩ : Fin n) := by
    refine hP _ ?_
    intro j hj
    have hjv : j.val ≤ n - 2 := hj
    have hjne : j ≠ IETDatum₂.lastPos n := by
      intro hh
      rw [hh] at hjv
      rw [lastPos_val] at hjv
      omega
    have hnp : P.perm j ≠ IETDatum₂.lastPos n := by
      intro hh
      have h1 : P.piTop (P.piBottom.symm j) = P.piTop (P.last true) := by
        rw [IETDatum₂.last_top P]
        exact hh
      have h2 : P.piBottom.symm j = P.last true := P.piTop.injective h1
      have h3 : j = P.piBottom (P.last true) := by
        have := congrArg P.piBottom h2
        simpa using this
      exact hjne (by rw [h3, h])
    change (P.perm j).val ≤ n - 2
    have hjlt := (P.perm j).isLt
    have hnv : (IETDatum₂.lastPos n).val = n - 1 := lastPos_val
    have hne : (P.perm j).val ≠ n - 1 := by
      intro hh
      exact hnp (Fin.ext (by rw [hnv]; exact hh))
    omega
  have h1 : (IETDatum₂.lastPos n).val ≤ n - 2 := hk (IETDatum₂.lastPos n)
  have hnv : (IETDatum₂.lastPos n).val = n - 1 := lastPos_val
  omega

end Irreducible

/-- The elementary matrix `V = 1 + E_{α_ε α_{1-ε}}` of source 4.1. -/
def rvMat (P : IETDatum₂ α n) (ε : Bool) : Matrix α α ℤ :=
  fun i j => if i = j then 1 else if i = P.last ε ∧ j = P.last (!ε) then 1 else 0

/-- The open cone `C(γ) = Q(γ)(ℝ^*_+)^A` over a finite path. -/
def cone (Q : Matrix α α ℤ) : Set (α → ℝ) :=
  {x | ∃ y : α → ℝ, (∀ a, 0 < y a) ∧ x = fun a => ∑ b, (Q a b : ℝ) * y b}

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. The elementary-matrix identity -/

/-- The `(a,b)` entry of `rvMat ε`, as a sum of two `ite`'s in `ℝ`.  The hypothesis
`P.last ε ≠ P.last (!ε)` is what rules out the double counting when `a = b`. -/
theorem rvMat_cast (P : IETDatum₂ α n) (ε : Bool) (a b : α)
    (hne : P.last ε ≠ P.last (!ε)) :
    (P.rvMat ε a b : ℝ) = (if b = a then (1 : ℝ) else 0) +
      (if a = P.last ε ∧ b = P.last (!ε) then (1 : ℝ) else 0) := by
  have key : P.rvMat ε a b = (if b = a then (1 : ℤ) else 0) +
      (if a = P.last ε ∧ b = P.last (!ε) then (1 : ℤ) else 0) := by
    by_cases hb : b = a
    · rw [hb]
      have h1 : ¬ (a = P.last ε ∧ a = P.last (!ε)) := fun h => hne (h.1.symm.trans h.2)
      simp [IETDatum₂.rvMat, h1]
    · have h1 : ¬ (a = b) := Ne.symm hb
      simp [IETDatum₂.rvMat, h1, hb]
  rw [key]
  push_cast
  ring

/-- Summing the elementary matrix `1 + E_{c,c'}` against a vector `y`: the result at `a` is
`y a` plus (if `a` is the "main" letter `c`) `y c'`. -/
theorem sum_rvMat_mul (c c' : α) (y : α → ℝ) (a : α) :
    ∑ b, ((if b = a then (1 : ℝ) else 0) + (if a = c ∧ b = c' then (1 : ℝ) else 0)) * y b
      = y a + (if a = c then y c' else 0) := by
  have hexp : ∀ b, ((if b = a then (1 : ℝ) else 0) +
        (if a = c ∧ b = c' then (1 : ℝ) else 0)) * y b
      = (if b = a then y b else 0) + (if a = c ∧ b = c' then y b else 0) := by
    intro b
    rw [add_mul, ite_mul, ite_mul, one_mul, zero_mul]
  have hsplit : ∑ b, ((if b = a then (1 : ℝ) else 0) +
        (if a = c ∧ b = c' then (1 : ℝ) else 0)) * y b
      = (∑ b, (if b = a then y b else 0)) +
        (∑ b, (if a = c ∧ b = c' then y b else 0)) := by
    rw [Finset.sum_congr rfl (fun b _ => hexp b), Finset.sum_add_distrib]
  rw [hsplit, Finset.sum_ite_eq' Finset.univ a (fun b => y b)]
  simp only [Finset.mem_univ, if_true]
  by_cases ha : a = c
  · have h2 : ∀ b, (if a = c ∧ b = c' then y b else 0) = (if b = c' then y b else 0) := by
      intro b
      rw [ha]
      simp
    rw [Finset.sum_congr rfl (fun b _ => h2 b), Finset.sum_ite_eq' Finset.univ c' (fun b => y b)]
    simp [ha]
  · have h2 : ∀ b, (if a = c ∧ b = c' then y b else 0) = (0 : ℝ) := by
      intro b
      rw [if_neg (fun h => ha h.1)]
    rw [Finset.sum_congr rfl (fun b _ => h2 b), Finset.sum_const_zero, add_zero]
    simp [ha]

variable (P : IETDatum₂ α n)

/-! ## 3. The rows of `rvMat` and the converse of the length relation -/

/-- The matrix `Q(γ) = V⁽¹⁾⋯V⁽ⁿ⁾` of a finite path, i.e. the matrix taking the renormalised
lengths `λ⁽ⁿ⁾` to the original ones (Lemma 1 of the source). -/
noncomputable def Path.Q (P : IETDatum₂ α n) : List Bool → Matrix α α ℤ
  | [] => 1
  | e :: es => P.rvMat e * Path.Q (P.rvStep e) es

/-- The path cylinder `Δ(γ) = C(γ) ∩ Δ`. -/
def simplexCyl (P : IETDatum₂ α n) (γ : List Bool) : Set (α → ℝ≥0) :=
  {x | (fun a => (x a : ℝ)) ∈ cone (Path.Q P γ) ∧ x ∈ simplexOn α}

end IETDatum₂
