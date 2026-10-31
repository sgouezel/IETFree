/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib

/-!
# Commensurable elements of a free group commute

Word-form target: if `a ^ m = b ^ n` in a free group with `m, n ≠ 0`, then `a` and `b` commute.
This is the "root uniqueness" step behind Lyndon–Schupp Prop. 2.19 (the centralizer of a nontrivial
element of a free group is cyclic).

Route (verified on paper; the ingredients below are supplied):

1. Reduce to `0 < m`, `0 < n` (replace `a` by `a⁻¹` and use `(-m).natAbs = m.natAbs` style
   bookkeeping).
2. Let `La := a.toWord` (reduced), `Wa := FreeGroup.reduceCyclically La` (cyclically reduced),
   `ca := FreeGroup.reduceCyclically.conjugator La`.  Mathlib's
   `FreeGroup.reduceCyclically.reduce_flatten_replicate` and `FreeGroup.toWord_pow` give
   `(a ^ m).toWord = ca ++ (List.replicate m Wa).flatten ++ FreeGroup.invRev ca`, and similarly for
   `b` and `n`; both sides compute `g.toWord` for `g := a ^ m = b ^ n`.
3. Compare norms: for every `k ≥ 1`, `(g ^ k).norm = 2 * ca.length + (m * k) * Wa.length` and the
   same with `cb`, `n`.  Hence `ca.length = cb.length` and `m * Wa.length = n * Wb.length`.  (The
   lemmas `norm_pow_eq` and `norm_zpow_eq` below are exactly this computation; use them with
   `q := a` and exponent `m * k`, noting `(a ^ m) ^ k = a ^ (m * k)`.)
4. Since `ca`, `cb` are prefixes of the same word `g.toWord` and have equal length, `ca = cb`; then
   the middles agree: `(List.replicate m Wa).flatten = (List.replicate n Wb).flatten`.
5. From that word equation deduce that `Wa` and `Wb` are powers of a common word `W` (handle
   `m = 1` or `n = 1` directly; otherwise both `Wa` and `Wb` are periods of the same word of length
   `m * Wa.length = n * Wb.length`, which is long enough for
   `List.HasPeriod.gcd` (Fine–Wilf, `Mathlib/Data/List/PeriodicityLemma.lean`) to give the common
   period `Nat.gcd Wa.length Wb.length`; the common prefix of that length is `W`).
6. Finally `a = mk (ca ++ Wa ++ FreeGroup.invRev ca)` by
   `FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically` and `FreeGroup.mk_toWord`, and
   likewise for `b` with the same `ca`; so both are conjugate (by `mk ca`) of powers of `W`, hence
   they commute.

If `a = 1` or `b = 1`, torsion-freeness (`FreeGroup.zpow_eq_one_iff` below) makes the conclusion
immediate.
-/

open FreeGroup

namespace FreeGroup

variable {α : Type*}

/-- The flattened `n`-fold repetition of `W` has length `n * W.length`. -/
theorem length_flatten_replicate (W : List (α × Bool)) (n : ℕ) :
    ((List.replicate n W).flatten).length = n * W.length := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ', List.flatten_concat, List.length_append, ih]
    ring

/-- `q ^ j = 1` only when `j = 0` or `q = 1` (free groups are torsion-free). -/
theorem zpow_eq_one_iff [DecidableEq α] {q : FreeGroup α} {j : ℤ} :
    q ^ j = 1 ↔ j = 0 ∨ q = 1 := by
  refine ⟨fun h => ?_, by rintro (rfl | rfl) <;> simp⟩
  rcases lt_trichotomy j 0 with hlt | heq | hgt
  · right
    have h3 : q ^ (-j) = 1 := by rw [zpow_neg, h, inv_one]
    have hj : (((-j).toNat : ℤ)) = -j := Int.toNat_of_nonneg (by omega)
    have h4 : (-j).toNat ≠ 0 := by omega
    have h5 : q ^ (-j).toNat = (1 : FreeGroup α) ^ (-j).toNat := by
      rw [one_pow, ← zpow_natCast, hj]
      exact h3
    exact IsMulTorsionFree.pow_left_injective h4 h5
  · exact Or.inl heq
  · right
    have hj : (((j.toNat : ℤ)) = j) := Int.toNat_of_nonneg (le_of_lt hgt)
    have h4 : j.toNat ≠ 0 := by omega
    have h5 : q ^ j.toNat = (1 : FreeGroup α) ^ j.toNat := by
      rw [one_pow, ← zpow_natCast, hj]
      exact h
    exact IsMulTorsionFree.pow_left_injective h4 h5

/-- **The norm of a nontrivial power**: `q ^ k` has length `2 |conjugator| + k |cyclic reduction|`
for `k ≥ 1`. -/
theorem norm_pow_eq [DecidableEq α] {q : FreeGroup α} {k : ℕ} (hk : 0 < k) :
    FreeGroup.norm (q ^ k) = 2 * (reduceCyclically.conjugator q.toWord).length
      + k * (reduceCyclically q.toWord).length := by
  have hL : IsReduced q.toWord := isReduced_toWord
  rw [show FreeGroup.norm (q ^ k) = (q ^ k).toWord.length from rfl, toWord_pow,
    FreeGroup.reduceCyclically.reduce_flatten_replicate hL k, if_neg (by omega),
    List.length_append, List.length_append, FreeGroup.invRev_length, length_flatten_replicate]
  ring

/-- **The norm of a nontrivial integral power.** -/
theorem norm_zpow_eq [DecidableEq α] {q : FreeGroup α} {m : ℤ} (hm : m ≠ 0) :
    FreeGroup.norm (q ^ m) = 2 * (reduceCyclically.conjugator q.toWord).length
      + m.natAbs * (reduceCyclically q.toWord).length := by
  have hnat : ∀ k : ℕ, 0 < k → FreeGroup.norm (q ^ k) = 2 * (reduceCyclically.conjugator q.toWord).length
      + k * (reduceCyclically q.toWord).length := fun k hk => norm_pow_eq hk
  rcases lt_trichotomy m 0 with hlt | heq | hgt
  · have hm' : m = -((m.natAbs : ℤ)) := by
      have h1 : ((m.natAbs : ℤ)) = -m := by
        rw [← Int.natAbs_neg m]
        exact Int.natAbs_of_nonneg (by omega)
      omega
    rw [hm', zpow_neg, FreeGroup.norm_inv_eq, zpow_natCast, hnat m.natAbs (by omega),
      Int.natAbs_neg, Int.natAbs_natCast]
  · exact absurd heq hm
  · have hm' : m = ((m.natAbs : ℤ)) := by
      have h1 : ((m.natAbs : ℤ)) = m := Int.natAbs_of_nonneg (by omega)
      omega
    rw [hm', zpow_natCast, hnat m.natAbs (by omega), Int.natAbs_natCast]

end FreeGroup

/-- **Commensurable elements of a free group commute**: `a ^ m = b ^ n` with `m, n ≠ 0` forces
`a * b = b * a`. -/
theorem commute_of_zpow_eq {α : Type*} [DecidableEq α] {a b : FreeGroup α} {m n : ℤ}
    (hm : m ≠ 0) (hn : n ≠ 0) (h : a ^ m = b ^ n) : a * b = b * a := by
  sorry
