/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.RichPath.MassFunction
public import IETFree.RauzyVeech.RichPath.MinimalExit

/-!
# The mass bound of `Γ₂` along a blocked run

The per-step estimates of the `Γ₂` step (`colSum P w` is `B_w·1`, `mkMass 1` is the
maximum `𝔐`, `cond` the conditional mass of a continuation):

* `colSum_le_two_pow_mul_Mk`: every height after `δ` is at most `2^{|δ|}·𝔐(q_w)`;
* `rowEnds_mem_of_blocked`: at a blocked node of a nonempty `A'`, both row ends lie in `A'`;
* `cond_arrow_ge_blocked`, `cond_arrow_ge_blocked'`: at a blocked node the conditional mass of an
  arrow is at least `1/(1 + Cb)`, where `Cb` is the balance constant of the node;
* `cond_blocked_ge`, `cond_blocked_prefix_ge`: hence a blocked run of length at most `L` whose
  proper prefixes are all blocked has conditional mass at least `(1/(1 + 2^L·Cb))^L`;
* `exists_uniform_minimal_exit`: there is `L` such that for every nonempty proper `A'` and every
  node there is an exit word of length at most `L` all of whose proper prefixes are blocked;
* `cond_minimal_exit_ge`: the conditional mass of such a minimal exit word is bounded below by the
  corresponding product over `Cb`.

These are the inputs of `exists_extMassGen_sharp`. -/

open Finset IntervalExchange.IETDatum₂
open scoped BigOperators

@[expose] public section

namespace IntervalExchange.RauzyVeech.RichPath

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Toolbox -/

/-- **Per-coordinate growth**: every height after `δ` is at most `2^{|δ|}·𝔐(q_w)`. -/
theorem colSum_le_two_pow_mul_Mk (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (δ : List Bool) (b : α) :
    colSum P (w ++ δ) b ≤ 2 ^ δ.length * mkMass 1 (colSum P w) := by
  induction δ generalizing w b with
  | nil => simpa using le_mkMass_one (q := colSum P w) b
  | cons e δ' ih =>
    have h2 : colSum P ((w ++ [e]) ++ δ') b ≤
        2 ^ δ'.length * mkMass 1 (colSum P (w ++ [e])) := ih (w ++ [e]) b
    have h3 : mkMass 1 (colSum P (w ++ [e]))
        ≤ 2 * mkMass 1 (colSum P w) :=
      Mk_one_step_le P hP hn w e
    have h4 : (0 : ℝ) ≤ 2 ^ δ'.length := by positivity
    have h5 : 2 ^ δ'.length * mkMass 1 (colSum P (w ++ [e])) ≤
        2 ^ δ'.length * (2 * mkMass 1 (colSum P w)) :=
      mul_le_mul_of_nonneg_left h3 h4
    have h6 : w ++ (e :: δ') = (w ++ [e]) ++ δ' := by
      rw [List.append_assoc, List.singleton_append]
    have h7 : (2 : ℝ) ^ (e :: δ').length * mkMass 1 (colSum P w) =
        2 ^ δ'.length * (2 * mkMass 1 (colSum P w)) := by
      rw [List.length_cons, pow_succ]
      ring
    rw [h6, h7]
    exact le_trans h2 h5

/-! ## 2. One blocked step degrades the balance by a factor at most `2` -/

omit [DecidableEq α] in
/-- At a blocked node, **both** row ends are `A'`-heights — for either choice of arrow. -/
theorem rowEnds_mem_of_blocked (P : IETDatum₂ α n) (v : List Bool) (A' : Finset α)
    (h : Blocked P v A') (e : Bool) :
    (P.vertex v).last e ∈ A' ∧ (P.vertex v).last (!e) ∈ A' := by
  rcases e with _ | _
  · exact ⟨h.2, h.1⟩
  · exact ⟨h.1, h.2⟩

/-! ## 3. Every blocked step has definite mass -/

/-- **One blocked arrow has mass at least `m/(m+M)`**: at a blocked node the loser `last (!e)` and
the winner `last e` are *both* `A'`-heights (`rowEnds_mem_of_blocked`), so the loser is at least `m`
and the winner at most `M` (`cond_arrow`). -/
theorem cond_arrow_ge_blocked (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (A' : Finset α) (v : List Bool) (e : Bool) {m M : ℝ}
    (hbl : Blocked P v A')
    (hm0 : 0 < m) (hm : ∀ b ∈ A', m ≤ colSum P v b)
    (hMm : mkMass 1 (colSum P v) ≤ M) :
    m / (m + M) ≤ cond P v [e] := by
  obtain ⟨hwin, hlos⟩ := rowEnds_mem_of_blocked P v A' hbl e
  have h1 : m ≤ colSum P v ((P.vertex v).last (!e)) := hm _ hlos
  have h2 : colSum P v ((P.vertex v).last e) ≤ M :=
    le_trans (le_mkMass_one (q := colSum P v) _) hMm
  have h3 : (0 : ℝ) < colSum P v ((P.vertex v).last (!e)) := colSum_pos P v _
  have h4 : (0 : ℝ) < colSum P v ((P.vertex v).last e) := colSum_pos P v _
  have hMpos : (0 : ℝ) < M :=
    lt_of_lt_of_le (mkMass_colSum_pos P v le_rfl (P.card_pos)) hMm
  have hden : (0 : ℝ) < colSum P v ((P.vertex v).last (!e))
      + colSum P v ((P.vertex v).last e) := by linarith
  rw [cond_arrow P hP hn v e, le_div_iff₀ hden]
  have hsum : (0 : ℝ) < m + M := by linarith
  have hfac : (0 : ℝ) < m / (m + M) := by positivity
  have hstep : m / (m + M) * (colSum P v ((P.vertex v).last (!e))
        + colSum P v ((P.vertex v).last e))
      ≤ m / (m + M) * (colSum P v ((P.vertex v).last (!e)) + M) := by
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hfac)
    linarith
  have hstep2 : m / (m + M) * (colSum P v ((P.vertex v).last (!e)) + M)
      ≤ colSum P v ((P.vertex v).last (!e)) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hsum]
    nlinarith [h1, hMpos]
  linarith

/-- **The arrow bound at a blocked node**, in the form used along a blocked run: with
`m = 𝔐(q_v)/Cb` and `M = 2^j·𝔐(q_v)`, the arrow has mass at least `1/(1 + 2^j·Cb)`. -/
theorem cond_arrow_ge_blocked' (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (A' : Finset α) (v : List Bool) (e : Bool) {Cb M₀ : ℝ} {j : ℕ}
    (hCb : 1 ≤ Cb) (hbl : Blocked P v A')
    (hm : ∀ b ∈ A', (1 / Cb) * M₀ ≤ colSum P v b)
    (hM : mkMass 1 (colSum P v) ≤ 2 ^ j * M₀) (hM0 : 0 < M₀) :
    1 / (1 + 2 ^ j * Cb) ≤ cond P v [e] := by
  have hCb0 : (0 : ℝ) < Cb := by linarith
  have hpos : (0 : ℝ) < (1 / Cb) * M₀ := by positivity
  have hMj : (0 : ℝ) < 2 ^ j * M₀ := by positivity
  have h := cond_arrow_ge_blocked P hP hn A' v e hbl hpos hm hM
  have heq : (1 / Cb) * M₀ / ((1 / Cb) * M₀ + 2 ^ j * M₀) = 1 / (1 + 2 ^ j * Cb) := by
    field_simp
  rwa [heq] at h

/-- **The induction behind item 3**: with `j` steps already taken (`𝔐 ≤ 2^j·M₀`) and
  the `A'`-heights
still at least `M₀/Cb`, `|δ|` blocked steps multiply the mass by at least
`(1/(1 + 2^L·Cb))^{|δ|}` as soon as `j + |δ| ≤ L`. -/
theorem cond_blocked_ge (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (A' : Finset α) {Cb : ℝ} (hCb : 1 ≤ Cb) (δ v : List Bool) (j L : ℕ) (M : ℝ)
    (hM0 : 0 < M) (hjL : j + δ.length ≤ L) (hbal : ∀ b ∈ A', (1 / Cb) * M ≤ colSum P v b)
    (hMk : mkMass 1 (colSum P v) ≤ 2 ^ j * M)
    (hbl : ∀ i, i < δ.length → Blocked P (v ++ δ.take i) A') :
    (1 / (1 + 2 ^ L * Cb)) ^ δ.length ≤ cond P v δ := by
  induction δ generalizing v j with
  | nil =>
    rw [cond_nil, List.length_nil, pow_zero]
  | cons e δ' ih =>
    have h0 : Blocked P v A' := by
      have h := hbl 0 (by simp)
      rwa [List.take_zero, List.append_nil] at h
    have hstep : 1 / (1 + 2 ^ L * Cb) ≤ cond P v [e] := by
      have h1 : 1 / (1 + 2 ^ j * Cb) ≤ cond P v [e] :=
        cond_arrow_ge_blocked' P hP hn A' v e hCb h0 hbal hMk hM0
      have hjL' : j ≤ L := by
        simp only [List.length_cons] at hjL
        omega
      have h2 : (2 : ℝ) ^ j ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hjL'
      have hc : (0 : ℝ) ≤ Cb := by linarith
      have h3 : 1 + 2 ^ j * Cb ≤ 1 + 2 ^ L * Cb := by nlinarith
      have h4 : 1 / (1 + 2 ^ L * Cb) ≤ 1 / (1 + 2 ^ j * Cb) :=
        one_div_le_one_div_of_le (by positivity) h3
      linarith
    have hbal' (b) (hb : b ∈ A') : (1 / Cb) * M ≤ colSum P (v ++ [e]) b := le_trans (hbal b
        hb) (state_mono P v [e] b)
    have hMk' : mkMass 1 (colSum P (v ++ [e])) ≤ 2 ^ (j + 1) * M := by
      have h1 : mkMass 1 (colSum P (v ++ [e]))
          ≤ 2 * mkMass 1 (colSum P v) :=
        Mk_one_step_le P hP hn v e
      have h2 : (2 : ℝ) ^ (j + 1) * M = 2 * (2 ^ j * M) := by
        rw [pow_succ]
        ring
      rw [h2]
      linarith
    have hbl' (i) (hi : i < δ'.length) : Blocked P ((v ++ [e]) ++ δ'.take i) A' := by
      have h1 := hbl (i + 1) (by simp only [List.length_cons]; omega)
      rw [List.take_succ_cons] at h1
      have hconv : v ++ (e :: δ'.take i) = (v ++ [e]) ++ δ'.take i := by
        rw [List.append_assoc, List.singleton_append]
      rwa [hconv] at h1
    have hjL2 : j + 1 + δ'.length ≤ L := by
      simp only [List.length_cons] at hjL
      omega
    have hih := ih (v ++ [e]) (j + 1) hjL2 hbal' hMk' hbl'
    have hcond : cond P v (e :: δ')
        = cond P v [e] * cond P (v ++ [e]) δ' := by
      have h := cond_append P v [e] δ'
      rwa [List.singleton_append] at h
    have hpow : (1 / (1 + 2 ^ L * Cb)) ^ (e :: δ').length
        = (1 / (1 + 2 ^ L * Cb)) * (1 / (1 + 2 ^ L * Cb)) ^ δ'.length := by
      rw [List.length_cons, pow_succ']
    rw [hcond, hpow]
    exact mul_le_mul hstep hih (by positivity) (cond_nonneg P v [e])

/-- **Item 3.** If all proper prefixes of `δ` are blocked and `|δ| ≤ L`, then the mass of `δ` from
a `Cb`-balanced node is at least `(1/(1 + 2^L·Cb))^L` — uniformly in the configuration, in `Cb`
and in the length of the run. -/
theorem cond_blocked_prefix_ge (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (A' : Finset α) (v : List Bool) {Cb : ℝ} (hCb : 1 ≤ Cb)
    (hbal : ∀ b ∈ A', (1 / Cb) * mkMass 1 (colSum P v) ≤ colSum P v b)
    {L : ℕ} (δ : List Bool) (hlen : δ.length ≤ L)
    (hbl : ∀ i, i < δ.length → Blocked P (v ++ δ.take i) A') :
    (1 / (1 + 2 ^ L * Cb)) ^ L ≤ cond P v δ := by
  have hM0 := mkMass_colSum_pos P v le_rfl (P.card_pos)
  have h := cond_blocked_ge P hP hn A' hCb δ v 0 L (mkMass 1 (colSum P v)) hM0
    (by omega) hbal (by simp) hbl
  refine le_trans ?_ h
  have hr0 : (0 : ℝ) ≤ 1 / (1 + 2 ^ L * Cb) := by positivity
  have hr1 : 1 / (1 + 2 ^ L * Cb) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h2 : (0 : ℝ) ≤ 2 ^ L * Cb := by positivity
    linarith
  exact pow_le_pow_of_le_one hr0 hr1 hlen

/-! ## 4. The minimal exit word: a uniform length bound -/

omit [DecidableEq α] in
/-- **The exit word of a minimal exit is short**: there is a bound on the length of a minimal exit
word, uniformly in `A'` and in the node. -/
theorem exists_uniform_minimal_exit (P : IETDatum₂ α n) (hP : P.Irreducible) :
    ∃ L : ℕ, ∀ (A' : Finset α) (w : List Bool), A'.Nonempty → A' ≠ Finset.univ →
      ∃ u : List Bool, Exit P (w ++ u) A' ∧
        (∀ i, i < u.length → Blocked P (w ++ u.take i) A') ∧
        u.length ≤ L := by
  obtain ⟨L, hL⟩ := exists_path_between P
  refine ⟨L, fun A' w hne hprop => ?_⟩
  obtain ⟨u, hu, hmin, hblk⟩ := exists_minimal_exit P hP w hne hprop
  obtain ⟨θ, hθ⟩ : ∃ θ : α, θ ∉ A' := by
    by_contra h
    exact hprop (Finset.eq_univ_iff_forall.mpr (by simpa using h))
  obtain ⟨b, hb⟩ := hne
  have hbθ : b ≠ θ := fun h => hθ (h ▸ hb)
  obtain ⟨u₀, e, -, h2⟩ := IETDatum₂.pairReach_all P hP b θ hbθ
  have hex (v : List Bool) : ∃ u : List Bool,
      u.length ≤ L ∧ Exit P (v ++ u) A' := by
    obtain ⟨u, hulen, hu⟩ := hL (P.vertex v) (P.vertex u₀) ⟨v, rfl⟩ ⟨u₀, rfl⟩
    refine ⟨u, hulen, ?_⟩
    have hvu : P.vertex (v ++ u) = (P.vertex v).vertex u := IETDatum₂.vertex_append P v u
    have hEq : P.vertex (v ++ u) = P.vertex u₀ := by rw [hvu, hu]
    cases e with
    | false => exact Or.inl (by rw [hEq]; simp only [Bool.not_false] at h2; rw [h2]; exact hθ)
    | true => exact Or.inr (by rw [hEq]; simp only [Bool.not_true] at h2; rw [h2]; exact hθ)
  obtain ⟨v, hv1, hv2⟩ := hex w
  exact ⟨u, hu, hblk, le_trans (hmin v hv2) hv1⟩

/-! ## 5. The last arrow

The author's list flags the exit arrow as uncovered: its probability is `h_out/(h_out + h_clean)`
with `h_out` the outsider's height, which is frozen along the blocked phase and is not controlled by
the `A'`-balance.  The point of this section is that **for the minimal exit word the last arrow is
covered by the same estimate**, because of a structural fact of `exists_minimal_exit`: all proper
prefixes of the minimal exit word are `Blocked`, so the *parent* of the last arrow is
  a blocked node,
and at a blocked node the arrow's loser `last (!e)` and winner `last e` are **both** `A'`-heights.
The outsider is not a row end at that node at all — it becomes one only *after* the arrow fires —
so its frozen height never enters the arrow's mass (`cond_arrow_ge_blocked` of §3 is the estimate).

What *is* true is the author's concern in the other case of the argument: at a node with exactly one
row end inside `A'`, the arrow whose **loser** is the outside row end (the `Γ₄` straddling arrow)
has mass `h_out/(h_out + h_{A'})` (`cond_arrow`), and there `h_out` is
not controlled by
the `A'`-balance at all.  That case belongs to `Γ₃`/`Γ₄`, not to `Γ₂`.
  -/

/-- **Item 5, resolved.**  Item 3 applies verbatim to the *whole* minimal exit word `u`: the
hypothesis `hmin` is exactly the third component of `exists_minimal_exit`, and it
covers the parent of the last arrow like any other prefix.  Hence the exit step needs no separate
estimate and no hypothesis on the outsider's height. -/
theorem cond_minimal_exit_ge (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (A' : Finset α) (v : List Bool) {Cb : ℝ} (hCb : 1 ≤ Cb)
    (hbal : ∀ b ∈ A', (1 / Cb) * mkMass 1 (colSum P v) ≤ colSum P v b)
    {L : ℕ} (u : List Bool)
    (hmin : ∀ i, i < u.length → Blocked P (v ++ u.take i) A')
    (hlen : u.length ≤ L) :
    (1 / (1 + 2 ^ L * Cb)) ^ L ≤ cond P v u :=
  cond_blocked_prefix_ge P hP hn A' v hCb hbal u hlen hmin

end IntervalExchange.RauzyVeech.RichPath

end
