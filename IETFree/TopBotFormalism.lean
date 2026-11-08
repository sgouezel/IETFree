/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.IET

/-!
# Interval exchanges in the Marmi–Moussa–Yoccoz framework

This module defines interval exchange transformations as they are used in the Marmi–Moussa–Yoccoz
framework for the Rauzy induction: over a **fixed alphabet** `α`, an exchange is described by a
**top** permutation `piTop : α ≃ Fin n` and a **bottom** permutation `piBottom : α ≃ Fin n` — the
two orders in which the letters are read above and below the exchange — plus a length vector
`α → ℝ≥0`.  The main object is the combinatorial datum `IETDatum₂ α n`, Yoccoz's
$(A,\pi_0,\pi_1)$, carrying both permutations.

This file also translates between that point of view and the one with a **single permutation of
`Fin n`**: `perm` is Yoccoz's permutation `π₁ ∘ π₀⁻¹` (`piBottom.symm.trans piTop`), `toIET` is
the exchange obtained from the single-permutation API (`mkIETFun`, `mkIET1'`) applied to it, and
`ofPerm` turns a `π : Equiv.Perm (Fin n)` into the datum whose top permutation is `π` and whose
bottom permutation is the identity.  So `IETDatum₂.ofPerm π` *is* the library's `mkIET1 π` — the two
viewpoints agree (`ofPerm_perm`, `ofPerm_toIET`) — and the Rauzy induction can be carried out on the
two-permutation datum while the statements of the paper are read on the single permutation.

The rest of the contents:

* `Irreducible` — irreducibility of the datum (Yoccoz's admissibility, 2.5), stated through
  `perm` (`ofPerm_irreducible_iff` reads it on a single permutation);
* `toIET` — the exchange; it is total, with the identity as junk value off the simplex (the same
  convention as `mkIETFun`);
* `simplex`, `simplexVolumeOn` — the simplex of `α`-indexed length vectors and its
  `(card α - 1)`-dimensional Lebesgue measure, which depends on the alphabet only.

The single-exchange API (`IsCutSet`, `IsIET`, `mkIETFun`, `mkIET1'`, `simplexVolume`, …) is the
library's own, from `IETFree.CutSet.Basic`, `IETFree.CutSet.Measure` and `IETFree.IET`; this module
adds the two-bijection datum on top of it. -/

@[expose] public section

open MeasureTheory
open scoped BigOperators NNReal

namespace IntervalExchange

/-! ## The simplex -/

/-- The simplex of `α`-indexed length vectors: total mass `1`.  It does not involve the
combinatorial data, and it does not require the coordinates to be positive.

This is not Mathlib's simplex: `stdSimplex` is deprecated in this Mathlib in favour of
`Convexity.StdSimplex`, a finitely supported `Finsupp`-valued structure, whereas the length vectors
here are functions `α → ℝ≥0` on a finite type and their total mass is a `Finset.sum`.  The carrier
is the one the rest of the library computes with, so the set is defined here. -/
def simplex (α : Type*) [Fintype α] : Set (α → ℝ≥0) := {lam | ∑ a, lam a = 1}

/-- **A point of the simplex has total length `1`**, as a real number: the form of the defining
equation that the measure-theoretic proofs use. -/
theorem sum_coe_eq_one {α : Type*} [Fintype α] {lam : α → ℝ≥0} (hlam : lam ∈ simplex α) :
    ∑ a, (lam a : ℝ) = 1 := by
  have h := congrArg (fun t : ℝ≥0 => (t : ℝ)) hlam
  push_cast at h
  exact h

@[simp] theorem mem_simplex {α : Type*} [Fintype α] {lam : α → ℝ≥0} :
    lam ∈ simplex α ↔ ∑ a, lam a = 1 := Iff.rfl

/-- The simplex `{lam | ∑ lam = 1}` is measurable: a level set of a continuous function on the
product space. -/
theorem measurableSet_simplex (α : Type*) [Fintype α] : MeasurableSet (simplex α) := by
  have h : Measurable fun lam : α → ℝ≥0 => ∑ a, lam a :=
    Finset.measurable_sum _ fun a _ => measurable_pi_apply a
  simpa [simplex] using measurableSet_eq_fun h measurable_const

/-- The `(card α - 1)`-dimensional Lebesgue measure on `simplex α`: the pushforward of the copied
`simplexVolume` along one equivalence `α ≃ Fin (card α)`. It depends on the alphabet only; the
independence of the chosen equivalence is `simplexVolume_map_perm` (its invariance under a
permutation of the coordinates), and its consequence `simplexVolumeOn_eq_map` for the particular
`piBottom` at hand. -/
noncomputable def simplexVolumeOn (α : Type*) [Fintype α] : Measure (α → ℝ≥0) :=
  (simplexVolume (Fintype.card α)).map (fun l a => l (Fintype.equivFin α a))

-- `ae_mem_simplex_of_nonempty` lives in `IETFree/RauzyVeech/SimplexAe.lean` and needs
-- `[Nonempty α]`: without it the statement is false (`simplex α = ∅` for the empty alphabet
-- while `simplexVolumeOn α` is a
-- probability measure).  Every use in the project has `α ≃ Fin n` with `n ≠ 0`.

/-! ## Combinatorial data: two bijections -/

/-- The source's combinatorial data $(A,\pi_0,\pi_1)$: **two** orderings of the same finite
alphabet, `piBottom` $=\pi_0$ and `piTop` $=\pi_1$. Keeping both (rather than the single permutation
`piTop * piBottom.symm`) is what makes the Rauzy–Veech step an operation on a fixed alphabet.  The
subscript counts the two orderings; there is no `IETDatum₁` — the one-permutation datum of the
`Pair` development is `Pair.IETDatum`, whose permutation is its field `perm`. -/
structure IETDatum₂ (α : Type*) [Fintype α] (n : ℕ) where
  /-- the order of the images (`π₁` of Yoccoz) -/
  piTop : α ≃ Fin n
  /-- the order of the lengths (`π₀` of Yoccoz) -/
  piBottom : α ≃ Fin n

namespace IETDatum₂

variable {α : Type*} [Fintype α] {n : ℕ}

/-- Two data with the same pair of bijections are equal. -/
@[ext] theorem ext {P Q : IETDatum₂ α n} (h1 : P.piTop = Q.piTop) (h2 : P.piBottom = Q.piBottom) :
    P = Q := by
  cases P; cases Q
  simp only at h1 h2
  subst h1 h2
  rfl

/-- **The alphabet has `n` letters**, through the top permutation of the datum. -/
theorem card_eq_n (P : IETDatum₂ α n) : Fintype.card α = n :=
  (Fintype.card_congr P.piTop).trans (Fintype.card_fin n)

/-- The alphabet is nonempty, from the combinatorial data: a datum has `n ≥ 1` letters. -/
theorem card_pos (P : IETDatum₂ α n) [NeZero n] : 1 ≤ Fintype.card α := by
  rw [card_eq_n P]
  exact Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)

/-- **The cardinality of the alphabet, as a positive real.** -/
theorem card_pos_cast (P : IETDatum₂ α n) [NeZero n] : (0 : ℝ) < (Fintype.card α : ℝ) := by
  have h := P.card_pos
  exact_mod_cast h

/-- The source's permutation `π₁ ∘ π₀⁻¹` of `{1,…,d}`: the exchange only depends on it (and on the
lengths in bottom order). -/
def perm (P : IETDatum₂ α n) : Equiv.Perm (Fin n) := P.piBottom.symm.trans P.piTop

/-- **The permutation of a datum, as a function**: `π₁ ∘ π₀⁻¹`, in the computation form proofs
unfolding `perm` need. -/
theorem perm_apply (P : IETDatum₂ α n) (i : Fin n) : P.perm i = P.piTop (P.piBottom.symm i) := (rfl)

/-- Irreducibility of the datum: no proper initial segment of the permutation is invariant (the
source's admissibility, 2.5). -/
def Irreducible (P : IETDatum₂ α n) : Prop := IsIrreduciblePerm P.perm

/-- The definition of `Irreducible`, as an equation: the form in which proofs rewrite it. -/
theorem Irreducible_def (P : IETDatum₂ α n) : P.Irreducible ↔ IsIrreduciblePerm P.perm :=
  Iff.rfl

/-- The length vector in bottom-order coordinates, i.e. `λ ∘ π_bottom⁻¹`. -/
def lengthsInBottom (P : IETDatum₂ α n) (lam : α → ℝ≥0) : Fin n → ℝ≥0 :=
  fun i => lam (P.piBottom.symm i)

theorem sum_lengthsInBottom (P : IETDatum₂ α n) {lam : α → ℝ≥0} (h : lam ∈ simplex α) :
    (∑ i, P.lengthsInBottom lam i) = 1 := by
  have h2 : (∑ i, P.lengthsInBottom lam i) = ∑ a, lam a := Equiv.sum_comp P.piBottom.symm lam
  rw [h2, h]

/-- The exchange as an element of `IET 0 1`.  It is **total**: off the simplex it is the identity,
the same junk-value convention as `mkIETFun`.  On the simplex it is `mkIET1'` of the reindexed
length
vector and of `π_top ∘ π_bottom⁻¹`. -/
noncomputable def toIET (P : IETDatum₂ α n) [NeZero n] (lam : α → ℝ≥0) : IET 0 1 := by
  classical
  exact if h : lam ∈ simplex α then
    mkIET1' (P.lengthsInBottom lam) P.perm (P.sum_lengthsInBottom h)
  else 1

/-- **The exit criterion**: on the simplex, the exchange of two-bijection data is the copied
single-permutation construction applied to `π_top ∘ π_bottom⁻¹`. -/
theorem toIET_eq_mkIET1 (P : IETDatum₂ α n) [NeZero n] {lam : α → ℝ≥0}
    (h : lam ∈ simplex α) :
    P.toIET lam = mkIET1' (P.lengthsInBottom lam) P.perm (P.sum_lengthsInBottom h) := by
  rw [toIET, dite_eq_left h]

/-- Off the simplex, `toIET` is the identity. -/
theorem toIET_of_notMem (P : IETDatum₂ α n) [NeZero n] {lam : α → ℝ≥0}
    (h : lam ∉ simplex α) : P.toIET lam = 1 := by
  rw [toIET, dite_eq_right h]

/-- The involution `π_top ↔ π_bottom`; by source 2.4 it sends the exchange to its inverse. -/
def inv (P : IETDatum₂ α n) : IETDatum₂ α n := ⟨P.piBottom, P.piTop⟩

@[simp] theorem inv_piTop (P : IETDatum₂ α n) : P.inv.piTop = P.piBottom := (rfl)

@[simp] theorem inv_piBottom (P : IETDatum₂ α n) : P.inv.piBottom = P.piTop := (rfl)

@[simp] theorem inv_inv (P : IETDatum₂ α n) : P.inv.inv = P := (rfl)

theorem perm_inv (P : IETDatum₂ α n) : P.inv.perm = P.perm.symm := by
  ext i
  simp [perm, inv]

/-- **The coercion of `mkIET1'`, read on `toEquiv`**:
`(mkIET1' lam π h).toEquiv = mkIETFun lam π 0`.  The same identity as
`IntervalExchange.coe_mkIET1'`, stated so that it rewrites when the coercion has already been
unfolded. -/
theorem toEquiv_mkIET1 {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (h : (∑ i, lam i) = 1) : (mkIET1' lam π h).toEquiv = mkIETFun lam π 0 := (rfl)

/-- The position of `k` in the bottom order, read off the inverse permutation: the key point is
`(π₁ ∘ π₀⁻¹)⁻¹ = π₀ ∘ π₁⁻¹`, i.e. `perm P` has inverse `π₀` after `π₁⁻¹`. -/
theorem perm_symm_apply (P : IETDatum₂ α n) (k : Fin n) :
    P.perm.symm k = P.piBottom (P.piTop.symm k) := by
  rw [Equiv.symm_apply_eq]
  simp [perm]

/-! ## The datum of a single permutation  The copied single-permutation API `mkIET1'` takes a
permutation of `Fin n` and a length vector in `Fin n` coordinates, while the induction works with
the two-bijection datum on a fixed alphabet. `ofPerm π` is the datum with `piBottom = id`: its
permutation is `π`, its lengths in bottom order are those of `Fin n`, and its exchange is `mkIET1'`
(`ofPerm_toIET`).  This is the whole translation needed to state the main theorem for a single
irreducible permutation; the converse translation is `toIET_eq_mkIET1`. -/

/-- The two-bijection datum of a single permutation, with `piBottom = id`. -/
def ofPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : IETDatum₂ (Fin n) n := ⟨π, Equiv.refl (Fin n)⟩

@[simp] theorem ofPerm_piTop {n : ℕ} (π : Equiv.Perm (Fin n)) : (ofPerm π).piTop = π := (rfl)

@[simp] theorem ofPerm_piBottom {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (ofPerm π).piBottom = Equiv.refl (Fin n) := (rfl)

@[simp] theorem ofPerm_perm {n : ℕ} (π : Equiv.Perm (Fin n)) : (ofPerm π).perm = π := by
  ext i
  rfl

@[simp] theorem ofPerm_lengthsInBottom {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    (ofPerm π).lengthsInBottom lam = lam := (rfl)

/-- `ofPerm` is irreducible exactly when the permutation is irreducible. -/
theorem ofPerm_irreducible_iff {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (ofPerm π).Irreducible ↔ IsIrreduciblePerm π := by
  rw [Irreducible, ofPerm_perm]

/-- On the simplex, the exchange of `ofPerm π` is `mkIET1' lam π h`. -/
theorem ofPerm_toIET {n : ℕ} [NeZero n] (π : Equiv.Perm (Fin n)) {lam : Fin n → ℝ≥0}
    (h : lam ∈ simplex (Fin n)) : (ofPerm π).toIET lam = mkIET1' lam π h := by
  ext x
  rw [toIET_eq_mkIET1 (ofPerm π) h, toEquiv_mkIET1, ofPerm_perm, ofPerm_lengthsInBottom]
  rfl

end IETDatum₂

/-! ## The `Fin n` insert-remove API

The position `n - 1`, the permutation that moves the element there just after a given position,
and its inverse.  None of these mentions a datum: they are `Fin n` combinatorics, not the step.
-/

/-- The last position of `Fin n`, as a `Fin n` (needs `n ≠ 0`). -/
def lastPos (n : ℕ) [NeZero n] : Fin n := ⟨n - 1, by have := NeZero.ne n; omega⟩

section Insert

variable {n : ℕ} [NeZero n]

/-- The last position of `Fin n`. -/
@[simp] lemma lastPos_val : (lastPos n).val = n - 1 := (rfl)

/-- `lastPos` at `m + 1` is the last index. -/
lemma lastPos_eq_last {m : ℕ} : lastPos (m + 1) = Fin.last m := Fin.ext rfl

/-- Move the element at the last position to the position just after `p`, shifting the letters
strictly in between up by one. -/
def insertFun (p : Fin n) (h : p.val + 1 < n) (k : Fin n) : Fin n :=
  if k.val ≤ p.val then k
  else if k = lastPos n then ⟨p.val + 1, h⟩
  else ⟨min (k.val + 1) (n - 1), by have := k.isLt; omega⟩

/-- The inverse of `insertFun`: move the element at position `p + 1` to the last position. -/
def removeFun (p : Fin n) (k : Fin n) : Fin n :=
  if k.val ≤ p.val then k
  else if k.val = p.val + 1 then lastPos n
  else ⟨k.val - 1, by have := k.isLt; omega⟩

lemma insertFun_of_le {p : Fin n} (h : p.val + 1 < n) {k : Fin n} (hk : k.val ≤ p.val) :
    insertFun p h k = k := by
  rw [insertFun, ite_eq_left hk]

lemma insertFun_lastPos {p : Fin n} (h : p.val + 1 < n) :
    insertFun p h (lastPos n) = ⟨p.val + 1, h⟩ := by
  rw [insertFun, ite_eq_right (by rw [lastPos_val]; omega), ite_eq_left rfl]

lemma insertFun_of_gt {p : Fin n} (h : p.val + 1 < n) {k : Fin n} (hk : p.val < k.val)
    (hk' : k ≠ lastPos n) :
    (insertFun p h k).val = k.val + 1 := by
  have hk2 : k.val + 1 ≤ n - 1 := by
    have hne : k.val ≠ n - 1 := fun hh => hk' (Fin.ext (by rw [lastPos_val, hh]))
    omega
  rw [insertFun, ite_eq_right (by omega), ite_eq_right hk', Fin.val_mk, Nat.min_eq_left hk2]

lemma removeFun_of_le {p : Fin n} {k : Fin n} (hk : k.val ≤ p.val) :
    removeFun p k = k := by
  rw [removeFun, ite_eq_left hk]

lemma removeFun_insertFun {p : Fin n} (h : p.val + 1 < n) (k : Fin n) :
    removeFun p (insertFun p h k) = k := by
  by_cases h1 : k.val ≤ p.val
  · rw [insertFun_of_le h h1, removeFun_of_le h1]
  · by_cases h2 : k = lastPos n
    · rw [h2, insertFun_lastPos h, removeFun, ite_eq_right (by simp), ite_eq_left (by simp)]
    · have hk : p.val < k.val := by
        have := k.isLt
        omega
      have hval := insertFun_of_gt h hk h2
      rw [removeFun, ite_eq_right (by rw [hval]; omega), ite_eq_right (by rw [hval]; omega)]
      exact Fin.ext (by rw [Fin.val_mk, hval]; omega)

lemma insertFun_removeFun {p : Fin n} (h : p.val + 1 < n) (k : Fin n) :
    insertFun p h (removeFun p k) = k := by
  by_cases h1 : k.val ≤ p.val
  · rw [removeFun, ite_eq_left h1, insertFun_of_le h h1]
  · rw [removeFun, ite_eq_right h1]
    by_cases h2 : k.val = p.val + 1
    · rw [ite_eq_left h2, insertFun_lastPos h, Fin.ext_iff, h2]
    · rw [ite_eq_right h2]
      have hk : p.val + 1 < k.val := by
        have := k.isLt
        omega
      have hk' : (⟨k.val - 1, by have := k.isLt; omega⟩ : Fin n) ≠ lastPos n := by
        intro hh
        have hh' : k.val - 1 = n - 1 := by
          have := congrArg Fin.val hh
          simpa [lastPos_val] using this
        omega
      have hk2 : p.val < (⟨k.val - 1, by have := k.isLt; omega⟩ : Fin n).val := by
        simp only []
        omega
      apply Fin.ext
      rw [insertFun_of_gt h hk2 hk']
      rw [Fin.val_mk]
      omega

/-- The insertion as a permutation of the positions.  It is the identity (junk value) when `p` is
already the last position, which cannot happen for irreducible data with `n ≥ 2`. -/
noncomputable def insertEquiv (p : Fin n) : Equiv.Perm (Fin n) :=
  if h : p.val + 1 < n then
    { toFun := insertFun p h
      invFun := removeFun p
      left_inv := removeFun_insertFun h
      right_inv := insertFun_removeFun h }
  else 1

lemma insertEquiv_apply_le {p : Fin n} {k : Fin n} (hk : k.val ≤ p.val) :
    insertEquiv p k = k := by
  by_cases h : p.val + 1 < n
  · rw [insertEquiv, dite_eq_left h]
    exact insertFun_of_le h hk
  · rw [insertEquiv, dite_eq_right h]
    rfl

lemma insertEquiv_lastPos {p : Fin n} (h : p.val + 1 < n) :
    insertEquiv p (lastPos n) = ⟨p.val + 1, h⟩ := by
  rw [insertEquiv, dite_eq_left h]
  exact insertFun_lastPos h

lemma insertEquiv_apply_gt {p : Fin n} {k : Fin n} (h : p.val + 1 < n) (hk : p.val < k.val)
    (hk' : k ≠ lastPos n) : (insertEquiv p k).val = k.val + 1 := by
  rw [insertEquiv, dite_eq_left h]
  exact insertFun_of_gt h hk hk'

/-- The insertion formula along a bijection `e : α ≃ Fin n` whose last letter is `c`. -/
theorem trans_insertEquiv_apply_val {α : Type*} [DecidableEq α] {n : ℕ} [NeZero n]
    (e : α ≃ Fin n) (p : Fin n) {c : α} (hc : e c = lastPos n) (a : α) :
    ((e.trans (insertEquiv p)) a).val =
      if (e a).val ≤ p.val then (e a).val else if a = c then p.val + 1 else (e a).val + 1 := by
  rw [Equiv.trans_apply]
  by_cases h1 : (e a).val ≤ p.val
  · rw [ite_eq_left h1, insertEquiv_apply_le h1]
  · rw [ite_eq_right h1]
    have hp : p.val + 1 < n := by
      have := (e a).isLt
      omega
    by_cases h2 : a = c
    · subst h2
      rw [ite_eq_left rfl, hc, insertEquiv_lastPos (p := p) hp]
    · rw [ite_eq_right h2]
      have hne : e a ≠ lastPos n := by
        intro hh
        exact h2 (e.injective (by rw [hh, hc]))
      rw [insertEquiv_apply_gt (p := p) (k := e a) hp (by omega) hne]

end Insert

end IntervalExchange

end
