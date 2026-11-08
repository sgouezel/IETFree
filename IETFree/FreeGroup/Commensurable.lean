/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.ListPeriodicity
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# Commensurable elements of a free group commute

`z ^ m = s ^ q` with `m, n ≠ 0` forces `z * s = s * z`.  This is the "root uniqueness" input behind
Lyndon–Schupp Prop. 2.19, and the last missing ingredient of `FreeGroup.exists_zpow_eq_of_mul_comm`
(`Centralizer.lean`, LS 2.19) and hence of Lemma 2.7 (`Irreducible.lean`).

The proof is by reduction to word combinatorics:

* `FreeGroup.reduceCyclically.reduce_flatten_replicate` and `FreeGroup.toWord_pow` write the reduced
  word of `a ^ M` as `c ++ (replicate M W).flatten ++ invRev c`, where `W` is cyclically reduced;
* comparing lengths for both `a`, `M` and `b`, `N` gives `|c_a| = |c_b|` and `M |W_a| = N |W_b|`;
* both `c`'s are prefixes of the single reduced word of the common value, so `c_a = c_b`, and the
  middles coincide: `(replicate M W_a).flatten = (replicate N W_b).flatten`;
* two words with a common positive power commute as words
  (`List.append_comm_of_flatten_replicate_eq`, in `ListPeriodicity.lean`), via the Fine–Wilf lemma
  `List.HasPeriod.gcd` on `W_a^{2M} = W_b^{2N}` and `List.take_eq_flatten_replicate_of_hasPeriod`;
* so `a` and `b` are conjugates (by the *same* element `mk c`) of powers of a common word.

Nothing here is specific to two generators; `FreeGroup.norm_conj_le`, the general bound on the norm
of a conjugate, is here for the same reason and is used by `MeasureTools` and `Centralizer`.
-/

@[expose] public section

open List

namespace FreeGroup

variable {α : Type*}

section Group

variable [DecidableEq α]

/-- The length of the reduced word of a positive power: the cyclically reduced word of `a`
repeated `k` times, with the conjugator at both ends.  Mathlib's `FreeGroup.toWord_pow` states the
reduction only, and this length form is what the commutativity argument below computes with; the
word form itself is the four rewrites of `FreeGroup.toWord_pow` done inline at the two use sites. -/
lemma toWord_pow_length (a : FreeGroup α) {k : ℕ} (hk : k ≠ 0) :
    (a ^ k).toWord.length = 2 * (FreeGroup.reduceCyclically.conjugator a.toWord).length +
      k * (FreeGroup.reduceCyclically a.toWord).length := by
  rw [FreeGroup.toWord_pow,
    FreeGroup.reduceCyclically.reduce_flatten_replicate FreeGroup.isReduced_toWord, ite_eq_right hk,
    List.append_assoc]
  simp [List.length_append, List.length_flatten]
  ring

end Group

/-- Commensurable elements of a free group commute (natural number exponents). -/
lemma commute_of_pow_eq {a b : FreeGroup α} {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0)
    (h : a ^ M = b ^ N) : a * b = b * a := by
  -- Cyclically reduce both words: `a` is a conjugate `c w c⁻¹` and `b` a conjugate `d v d⁻¹` of
  -- cyclically reduced words.  From `a ^ M = b ^ N` the two lengths are comparable, the periodicity
  -- lemma gives `w ++ v = v ++ w`, and conjugating back gives `a * b = b * a`.
  classical
  set c := FreeGroup.reduceCyclically.conjugator a.toWord with hc
  set w := FreeGroup.reduceCyclically a.toWord with hw
  set d := FreeGroup.reduceCyclically.conjugator b.toWord with hd
  set v := FreeGroup.reduceCyclically b.toWord with hv
  have hca : c ++ w ++ FreeGroup.invRev c = a.toWord :=
    FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically a.toWord
  have hdb : d ++ v ++ FreeGroup.invRev d = b.toWord :=
    FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically b.toWord
  have hpa : (a ^ M).toWord = c ++ ((List.replicate M w).flatten ++ FreeGroup.invRev c) := by
    rw [FreeGroup.toWord_pow,
      FreeGroup.reduceCyclically.reduce_flatten_replicate FreeGroup.isReduced_toWord,
      ite_eq_right hM, List.append_assoc]
  have hpb : (b ^ N).toWord = d ++ ((List.replicate N v).flatten ++ FreeGroup.invRev d) := by
    rw [FreeGroup.toWord_pow,
      FreeGroup.reduceCyclically.reduce_flatten_replicate FreeGroup.isReduced_toWord,
      ite_eq_right hN, List.append_assoc]
  have hlen1 : 2 * c.length + M * w.length = 2 * d.length + N * v.length := by
    have ha := toWord_pow_length a hM
    have hb := toWord_pow_length b hN
    rw [h] at ha
    rw [hb] at ha
    exact ha.symm
  have h2MN : a ^ (2 * M) = b ^ (2 * N) := by
    rw [Nat.mul_comm 2 M, Nat.mul_comm 2 N, pow_mul, pow_mul, h]
  have hlen2 : 2 * c.length + (2 * M) * w.length = 2 * d.length + (2 * N) * v.length := by
    have ha := toWord_pow_length a (by omega : 2 * M ≠ 0)
    have hb := toWord_pow_length b (by omega : 2 * N ≠ 0)
    rw [h2MN] at ha
    rw [hb] at ha
    exact ha.symm
  have hlen2' : 2 * c.length + 2 * (M * w.length) = 2 * d.length + 2 * (N * v.length) := by
    rw [Nat.mul_assoc, Nat.mul_assoc] at hlen2
    exact hlen2
  have hcd_len : c.length = d.length := by omega
  have hword : c ++ ((List.replicate M w).flatten ++ FreeGroup.invRev c)
      = d ++ ((List.replicate N v).flatten ++ FreeGroup.invRev d) := by
    rw [← hpa, ← hpb, h]
  have hcd : c = d := by
    have ht : (c ++ ((List.replicate M w).flatten ++ FreeGroup.invRev c)).take c.length
        = (d ++ ((List.replicate N v).flatten ++ FreeGroup.invRev d)).take c.length := by
      rw [hword]
    rw [List.take_left, List.take_left' hcd_len.symm] at ht
    exact ht
  have hUV : (List.replicate M w).flatten = (List.replicate N v).flatten := by
    have h1 : (List.replicate M w).flatten ++ FreeGroup.invRev c
        = (List.replicate N v).flatten ++ FreeGroup.invRev c := by
      rw [← hcd] at hword
      exact List.append_cancel_left hword
    exact List.append_cancel_right h1
  have hwv : w ++ v = v ++ w := append_comm_of_flatten_replicate_eq hM hN hUV
  have ha_eq : a = FreeGroup.mk c * FreeGroup.mk w * (FreeGroup.mk c)⁻¹ := by
    rw [← FreeGroup.mk_toWord (x := a), ← hca]
    rw [FreeGroup.inv_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
  have hb_eq : b = FreeGroup.mk c * FreeGroup.mk v * (FreeGroup.mk c)⁻¹ := by
    rw [← FreeGroup.mk_toWord (x := b), ← hdb, ← hcd]
    rw [FreeGroup.inv_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
  have hmk : FreeGroup.mk w * FreeGroup.mk v = FreeGroup.mk v * FreeGroup.mk w := by
    rw [FreeGroup.mul_mk, FreeGroup.mul_mk, hwv]
  rw [ha_eq, hb_eq]
  calc FreeGroup.mk c * FreeGroup.mk w * (FreeGroup.mk c)⁻¹ *
        (FreeGroup.mk c * FreeGroup.mk v * (FreeGroup.mk c)⁻¹)
      = FreeGroup.mk c * (FreeGroup.mk w * FreeGroup.mk v) * (FreeGroup.mk c)⁻¹ := by group
    _ = FreeGroup.mk c * (FreeGroup.mk v * FreeGroup.mk w) * (FreeGroup.mk c)⁻¹ := by rw [hmk]
    _ = FreeGroup.mk c * FreeGroup.mk v * (FreeGroup.mk c)⁻¹ *
        (FreeGroup.mk c * FreeGroup.mk w * (FreeGroup.mk c)⁻¹) := by group

theorem commute_of_zpow_eq {α : Type*} {a b : FreeGroup α} {m n : ℤ}
    (hm : m ≠ 0) (hn : n ≠ 0) (h : a ^ m = b ^ n) : a * b = b * a := by
  obtain ⟨M, hM | hM⟩ := Int.eq_nat_or_neg m
  · obtain ⟨N, hN | hN⟩ := Int.eq_nat_or_neg n
    · subst hM; subst hN
      rw [zpow_natCast, zpow_natCast] at h
      have hM0 : M ≠ 0 := by rintro rfl; simp at hm
      have hN0 : N ≠ 0 := by rintro rfl; simp at hn
      exact commute_of_pow_eq hM0 hN0 h
    · subst hM; subst hN
      rw [zpow_natCast, zpow_neg, zpow_natCast] at h
      have hM0 : M ≠ 0 := by rintro rfl; simp at hm
      have hN0 : N ≠ 0 := by rintro rfl; simp at hn
      have h' : (a⁻¹) ^ M = b ^ N := by rw [inv_pow, h, inv_inv]
      have hc : Commute a⁻¹ b := commute_of_pow_eq hM0 hN0 h'
      simpa only [inv_inv, Commute, SemiconjBy] using hc.inv_left
  · obtain ⟨N, hN | hN⟩ := Int.eq_nat_or_neg n
    · subst hM; subst hN
      rw [zpow_neg, zpow_natCast, zpow_natCast] at h
      have hM0 : M ≠ 0 := by rintro rfl; simp at hm
      have hN0 : N ≠ 0 := by rintro rfl; simp at hn
      have h' : (b⁻¹) ^ N = a ^ M := by rw [inv_pow, ← h, inv_inv]
      have hc : Commute b⁻¹ a := commute_of_pow_eq hN0 hM0 h'
      have hc2 : Commute b a := by
        simpa only [inv_inv, Commute, SemiconjBy] using hc.inv_left
      exact hc2.symm
    · subst hM; subst hN
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast] at h
      have hM0 : M ≠ 0 := by rintro rfl; simp at hm
      have hN0 : N ≠ 0 := by rintro rfl; simp at hn
      have h' : a ^ M = b ^ N := by rw [← inv_inj]; exact h
      exact commute_of_pow_eq hM0 hN0 h'

/-- Conjugation changes the norm by at most `2 * norm g`. -/
theorem norm_conj_le [DecidableEq α] (g s : FreeGroup α) :
    FreeGroup.norm (g * s * g⁻¹) ≤ FreeGroup.norm s + 2 * FreeGroup.norm g := by
  have h1 : FreeGroup.norm (g * s * g⁻¹) ≤ FreeGroup.norm (g * s) + FreeGroup.norm g⁻¹ :=
    norm_mul_le _ _
  have h2 : FreeGroup.norm (g * s) ≤ FreeGroup.norm g + FreeGroup.norm s := norm_mul_le _ _
  rw [FreeGroup.norm_inv_eq] at h1
  omega

end FreeGroup

end
