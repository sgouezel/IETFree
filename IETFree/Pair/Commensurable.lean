/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib

/-!
**Commensurable elements of a free group commute** (run `commensurable-commute`, ported).

`z ^ m = s ^ q` with `m, n ≠ 0` forces `z * s = s * z`.  This is the "root uniqueness" input behind
Lyndon–Schupp Prop. 2.19, and the last missing ingredient of `FreeGroup.exists_zpow_eq_of_mul_comm`
(`Centralizer.lean`, LS 2.19) and hence of Lemma 2.7 (`Irreducible.lean`).

The proof is by reduction to word combinatorics:

* `FreeGroup.reduceCyclically.reduce_flatten_replicate` and `FreeGroup.toWord_pow` write the reduced
  word of `a ^ M` as `c ++ (replicate M W).flatten ++ invRev c`, where `W` is cyclically reduced;
* comparing lengths for both `a`, `M` and `b`, `N` gives `|c_a| = |c_b|` and `M |W_a| = N |W_b|`;
* both `c`'s are prefixes of the single reduced word of the common value, so `c_a = c_b`, and the
  middles coincide: `(replicate M W_a).flatten = (replicate N W_b).flatten`;
* two words with a common positive power commute as words (`append_comm_of_flatten_replicate_eq`,
  via the Fine–Wilf lemma `List.HasPeriod.gcd` on `W_a^{2M} = W_b^{2N}` and
  `take_eq_flatten_replicate_of_hasPeriod`);
* so `a` and `b` are conjugates (by the *same* element `mk c`) of powers of a common word.

Nothing here is specific to two generators.
-/

open List

namespace List

variable {α : Type*}

/-- The flattening of `k ≥ 1` copies of `w` has period `|w|`. -/
lemma hasPeriod_flatten_replicate {w : List α} {k : ℕ} (hk : k ≠ 0) :
    (List.replicate k w).flatten.HasPeriod w.length := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [List.HasPeriod]
  have h1 : (List.replicate (k' + 1) w).flatten = w ++ (List.replicate k' w).flatten := by
    rw [List.replicate_succ, List.flatten_cons]
  have h2 : w ++ (List.replicate k' w).flatten = (List.replicate k' w).flatten ++ w := by
    rw [← h1, List.replicate_succ', List.flatten_concat]
  have hgoal : w ++ (w ++ (List.replicate k' w).flatten) =
      (w ++ (List.replicate k' w).flatten) ++ w := by
    rw [h2, ← List.append_assoc, h2]
  rw [h1, List.take_left, hgoal]
  exact List.prefix_append _ _

lemma drop_mul_prefix {U : List α} {d : ℕ} (hper : U.HasPeriod d) (m : ℕ) :
    U.drop (m * d) <+: U := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep : U.drop ((m + 1) * d) = (U.drop (m * d)).drop d := by
        rw [List.drop_drop]
        congr 1
        ring
      rw [hstep]
      refine (List.HasPeriod.drop_prefix d ?_).trans ih
      exact hper.infix ⟨U.take (m * d), [], by rw [List.take_append_drop, List.append_nil]⟩

lemma take_drop_mul_eq_take {U : List α} {d : ℕ} (hd : 0 < d) (hper : U.HasPeriod d)
    {m : ℕ} (hlen : (m + 1) * d ≤ U.length) : (U.drop (m * d)).take d = U.take d := by
  have hX : U.drop (m * d) <+: U := drop_mul_prefix hper m
  have hXd : U.drop (m * d) = U.take (U.drop (m * d)).length := by
    rw [List.prefix_iff_eq_take] at hX
    exact hX
  have hlen2 : m * d + d ≤ U.length := by rwa [Nat.succ_mul] at hlen
  have hdX : d ≤ (U.drop (m * d)).length := by
    rw [List.length_drop]; omega
  rw [hXd, List.take_take, Nat.min_eq_left hdX]

lemma take_eq_flatten_replicate_of_hasPeriod {U : List α} {d : ℕ} (hd : 0 < d)
    (hper : U.HasPeriod d) (m : ℕ) (hlen : m * d ≤ U.length) :
    U.take (m * d) = (List.replicate m (U.take d)).flatten := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hlen2 : m * d + d ≤ U.length := by rwa [Nat.succ_mul] at hlen
      have hlen' : m * d ≤ U.length := by omega
      have hstep : (U.drop (m * d)).take d = U.take d := take_drop_mul_eq_take hd hper hlen
      calc U.take ((m + 1) * d) = U.take (m * d + d) := by rw [Nat.succ_mul]
        _ = U.take (m * d) ++ (U.drop (m * d)).take d := List.take_add
        _ = (List.replicate m (U.take d)).flatten ++ U.take d := by rw [ih hlen', hstep]
        _ = (List.replicate (m + 1) (U.take d)).flatten := by
              rw [List.replicate_succ', List.flatten_concat]

/-- Two words with a common positive power commute. -/
lemma append_comm_of_flatten_replicate_eq {w v : List α} {M N : ℕ}
    (hM : M ≠ 0) (hN : N ≠ 0)
    (h : (List.replicate M w).flatten = (List.replicate N v).flatten) :
    w ++ v = v ++ w := by
  by_cases hw : w = []
  · simp [hw]
  by_cases hv : v = []
  · simp [hv]
  have hp : 0 < w.length := List.length_pos_of_ne_nil hw
  have hq : 0 < v.length := List.length_pos_of_ne_nil hv
  set d := Nat.gcd w.length v.length with hd
  have hd0 : 0 < d := by rw [hd]; exact Nat.gcd_pos_of_pos_left _ hp
  have hdp : d ∣ w.length := by rw [hd]; exact Nat.gcd_dvd_left _ _
  have hdq : d ∣ v.length := by rw [hd]; exact Nat.gcd_dvd_right _ _
  set U := (List.replicate (2 * M) w).flatten with hU
  have hW : (List.replicate M w).flatten = w ++ (List.replicate (M - 1) w).flatten := by
    conv_lhs => rw [show M = M - 1 + 1 by omega]
    rw [List.replicate_succ, List.flatten_cons]
  have hV : (List.replicate N v).flatten = v ++ (List.replicate (N - 1) v).flatten := by
    conv_lhs => rw [show N = N - 1 + 1 by omega]
    rw [List.replicate_succ, List.flatten_cons]
  have hU2orig : (List.replicate (2 * M) w).flatten = (List.replicate (2 * N) v).flatten := by
    rw [show 2 * M = M + M by ring, List.replicate_add, List.flatten_append, h,
      show 2 * N = N + N by ring, List.replicate_add, List.flatten_append]
  have hU_eq : U = (List.replicate M w).flatten ++ (List.replicate M w).flatten := by
    rw [hU, show 2 * M = M + M by ring, List.replicate_add, List.flatten_append]
  have hU2 : U = (List.replicate N v).flatten ++ (List.replicate N v).flatten := by
    rw [hU, hU2orig, show 2 * N = N + N by ring, List.replicate_add, List.flatten_append]
  have hper_p : U.HasPeriod w.length := by
    rw [hU]; exact hasPeriod_flatten_replicate (by omega)
  have hper_q : U.HasPeriod v.length := by
    rw [hU, hU2orig]; exact hasPeriod_flatten_replicate (by omega)
  have hlenU : U.length = 2 * (List.replicate M w).flatten.length := by
    rw [hU_eq, List.length_append]; ring
  have hlenU2 : U.length = 2 * (List.replicate N v).flatten.length := by
    rw [hU2, List.length_append]; ring
  have hWlen : w.length ≤ (List.replicate M w).flatten.length := by
    rw [hW, List.length_append]; omega
  have hVlen : v.length ≤ (List.replicate N v).flatten.length := by
    rw [hV, List.length_append]; omega
  have hpU : 2 * w.length ≤ U.length := by rw [hlenU]; omega
  have hqU : 2 * v.length ≤ U.length := by rw [hlenU2]; omega
  have hfine : w.length + v.length - d ≤ U.length := by omega
  have hper_d : U.HasPeriod d := HasPeriod.gcd hper_p hper_q hfine
  have hUp : w.length ≤ U.length := by omega
  have hUq : v.length ≤ U.length := by omega
  have hwU : U.take w.length = w := by
    rw [hU_eq, hW, List.append_assoc, List.take_left]
  have hvU : U.take v.length = v := by
    rw [hU2, hV, List.append_assoc, List.take_left]
  have hpd : w.length / d * d = w.length := Nat.div_mul_cancel hdp
  have hqd : v.length / d * d = v.length := Nat.div_mul_cancel hdq
  have hwz' : U.take w.length = (List.replicate (w.length / d) (U.take d)).flatten := by
    have h1 := take_eq_flatten_replicate_of_hasPeriod hd0 hper_d (w.length / d)
      (by rw [hpd]; exact hUp)
    rwa [hpd] at h1
  have hvz' : U.take v.length = (List.replicate (v.length / d) (U.take d)).flatten := by
    have h1 := take_eq_flatten_replicate_of_hasPeriod hd0 hper_d (v.length / d)
      (by rw [hqd]; exact hUq)
    rwa [hqd] at h1
  have hwz : w = (List.replicate (w.length / d) (U.take d)).flatten := hwU.symm.trans hwz'
  have hvz : v = (List.replicate (v.length / d) (U.take d)).flatten := hvU.symm.trans hvz'
  rw [hwz, hvz, ← List.flatten_append, ← List.flatten_append, ← List.replicate_add,
    ← List.replicate_add, Nat.add_comm (w.length / d) (v.length / d)]

end List

namespace FreeGroup

variable {α : Type*}

section Group

variable [DecidableEq α]

/-- Reduced word of a positive power. -/
lemma toWord_pow_eq_append (a : FreeGroup α) {k : ℕ} (hk : k ≠ 0) :
    (a ^ k).toWord = FreeGroup.reduceCyclically.conjugator a.toWord ++
      ((List.replicate k (FreeGroup.reduceCyclically a.toWord)).flatten ++
        FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator a.toWord)) := by
  rw [FreeGroup.toWord_pow,
    FreeGroup.reduceCyclically.reduce_flatten_replicate FreeGroup.isReduced_toWord, if_neg hk,
    List.append_assoc]

lemma toWord_pow_length (a : FreeGroup α) {k : ℕ} (hk : k ≠ 0) :
    (a ^ k).toWord.length = 2 * (FreeGroup.reduceCyclically.conjugator a.toWord).length +
      k * (FreeGroup.reduceCyclically a.toWord).length := by
  rw [toWord_pow_eq_append a hk]
  simp [List.length_append, List.length_flatten]
  ring

end Group

/-- Commensurable elements of a free group commute (natural number exponents). -/
lemma commute_of_pow_eq {a b : FreeGroup α} {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0)
    (h : a ^ M = b ^ N) : a * b = b * a := by
  classical
  set c := FreeGroup.reduceCyclically.conjugator a.toWord with hc
  set w := FreeGroup.reduceCyclically a.toWord with hw
  set d := FreeGroup.reduceCyclically.conjugator b.toWord with hd
  set v := FreeGroup.reduceCyclically b.toWord with hv
  have hca : c ++ w ++ FreeGroup.invRev c = a.toWord :=
    FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically a.toWord
  have hdb : d ++ v ++ FreeGroup.invRev d = b.toWord :=
    FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically b.toWord
  have hpa : (a ^ M).toWord = c ++ ((List.replicate M w).flatten ++ FreeGroup.invRev c) :=
    toWord_pow_eq_append a hM
  have hpb : (b ^ N).toWord = d ++ ((List.replicate N v).flatten ++ FreeGroup.invRev d) :=
    toWord_pow_eq_append b hN
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
    have h' := hlen2
    rw [Nat.mul_assoc, Nat.mul_assoc] at h'
    exact h'
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
      have h2 := hword
      rw [← hcd] at h2
      exact List.append_cancel_left h2
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
  classical
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
      have h2 := hc.inv_left
      rw [inv_inv] at h2
      exact h2
  · obtain ⟨N, hN | hN⟩ := Int.eq_nat_or_neg n
    · subst hM; subst hN
      rw [zpow_neg, zpow_natCast, zpow_natCast] at h
      have hM0 : M ≠ 0 := by rintro rfl; simp at hm
      have hN0 : N ≠ 0 := by rintro rfl; simp at hn
      have h' : (b⁻¹) ^ N = a ^ M := by rw [inv_pow, ← h, inv_inv]
      have hc : Commute b⁻¹ a := commute_of_pow_eq hN0 hM0 h'
      have hc2 : Commute b a := by
        have h := hc.inv_left
        rw [inv_inv] at h
        exact h
      exact hc2.symm
    · subst hM; subst hN
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast] at h
      have hM0 : M ≠ 0 := by rintro rfl; simp at hm
      have hN0 : N ≠ 0 := by rintro rfl; simp at hn
      have h' : a ^ M = b ^ N := by rw [← inv_inj]; exact h
      exact commute_of_pow_eq hM0 hN0 h'

end FreeGroup
