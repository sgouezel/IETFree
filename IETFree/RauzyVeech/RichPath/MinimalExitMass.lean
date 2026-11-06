/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.RichPath.GradedInduction
public import IETFree.RauzyVeech.RichPath.MassFunction

/-!
# The mass bound of `Γ₂` along a blocked run

The per-step estimates of the `Γ₂` step (`NodeHeight.st P w` is `B_w·1`, `NodeHeight.Mk 1` is the
maximum `𝔐`, `CylinderMass.cond` the conditional mass of a continuation):

* `st_le_two_pow_mul_Mk`: every height after `δ` is at most `2^{|δ|}·𝔐(q_w)`;
* `rowEnds_mem_of_blocked`: at a blocked node of a nonempty `A'`, both row ends lie in `A'`;
* `cond_arrow_ge_blocked`, `cond_arrow_ge_blocked'`: at a blocked node the conditional mass of an
  arrow is at least `1/(1 + Cb)`, where `Cb` is the balance constant of the node;
* `cond_blocked_ge_aux`, `cond_blocked_prefix_ge`: hence a blocked run of length at most `L` whose
  proper prefixes are all blocked has conditional mass at least `(1/(1 + 2^L·Cb))^L`;
* `exists_uniform_minimal_exit`: there is `L` such that for every nonempty proper `A'` and every
  node there is an exit word of length at most `L` all of whose proper prefixes are blocked;
* `cond_minimal_exit_ge`: the conditional mass of such a minimal exit word is bounded below by the
  corresponding product over `Cb`.

These are the inputs of `MassGrowth.exists_extMassGen_sharp`. -/

open Finset IETDatum₂
open scoped BigOperators

@[expose] public section

namespace MinimalExitMass

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 0. Toolbox -/

/-- **Per-coordinate growth**: every height after `δ` is at most `2^{|δ|}·𝔐(q_w)`. -/
theorem st_le_two_pow_mul_Mk (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) : ∀ (δ : List Bool) (b : α),
    NodeHeight.st P (w ++ δ) b ≤ 2 ^ δ.length * NodeHeight.Mk 1 (NodeHeight.st P w) := by
  intro δ
  induction δ generalizing w with
  | nil => intro b; simpa using NodeHeight.le_Mk_one (q := NodeHeight.st P w) b
  | cons e δ' ih =>
    intro b
    have h2 : NodeHeight.st P ((w ++ [e]) ++ δ') b ≤
        2 ^ δ'.length * NodeHeight.Mk 1 (NodeHeight.st P (w ++ [e])) := ih (w ++ [e]) b
    have h3 : NodeHeight.Mk 1 (NodeHeight.st P (w ++ [e]))
        ≤ 2 * NodeHeight.Mk 1 (NodeHeight.st P w) :=
      LargeLetter.Mk_one_step_le P hP hn w e
    have h4 : (0 : ℝ) ≤ 2 ^ δ'.length := by positivity
    have h5 : 2 ^ δ'.length * NodeHeight.Mk 1 (NodeHeight.st P (w ++ [e])) ≤
        2 ^ δ'.length * (2 * NodeHeight.Mk 1 (NodeHeight.st P w)) :=
      mul_le_mul_of_nonneg_left h3 h4
    have h6 : w ++ (e :: δ') = (w ++ [e]) ++ δ' := by
      rw [List.append_assoc, List.singleton_append]
    have h7 : (2 : ℝ) ^ (e :: δ').length * NodeHeight.Mk 1 (NodeHeight.st P w) =
        2 ^ δ'.length * (2 * NodeHeight.Mk 1 (NodeHeight.st P w)) := by
      rw [List.length_cons, pow_succ]
      ring
    rw [h6, h7]
    exact le_trans h2 h5

/-! ## 1. One blocked step degrades the balance by a factor at most `2` -/

omit [DecidableEq α] in
/-- At a blocked node, **both** row ends are `A'`-heights — for either choice of arrow. -/
theorem rowEnds_mem_of_blocked (P : IETDatum₂ α n) (v : List Bool) (A' : Finset α)
    (h : MinimalExit.Blocked P v A') (e : Bool) :
    (P.vertex v).last e ∈ A' ∧ (P.vertex v).last (!e) ∈ A' := by
  rcases e with _ | _
  · exact ⟨h.2, h.1⟩
  · exact ⟨h.1, h.2⟩

/-! ## 2. Every blocked step has definite mass -/

/-- Powers *decrease* with the exponent when the base lies in `[0,1]`. -/
theorem pow_le_pow_of_le_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {j L : ℕ} (hjL : j ≤ L) :
    r ^ L ≤ r ^ j := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hjL
  rw [hk, pow_add]
  calc r ^ j * r ^ k ≤ r ^ j * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hr0 hr1) (pow_nonneg hr0 j)
    _ = r ^ j := by ring

/-- **One blocked arrow has mass at least `m/(m+M)`**: at a blocked node the loser `last (!e)` and
the winner `last e` are *both* `A'`-heights (`rowEnds_mem_of_blocked`), so the loser is at least `m`
and the winner at most `M` (`CylinderMass.cond_arrow`). -/
theorem cond_arrow_ge_blocked (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (A' : Finset α) (v : List Bool) (e : Bool) {m M : ℝ}
    (hbl : MinimalExit.Blocked P v A')
    (hm0 : 0 < m) (hm : ∀ b ∈ A', m ≤ NodeHeight.st P v b)
    (hMm : NodeHeight.Mk 1 (NodeHeight.st P v) ≤ M) :
    m / (m + M) ≤ CylinderMass.cond P v [e] := by
  obtain ⟨hwin, hlos⟩ := rowEnds_mem_of_blocked P v A' hbl e
  have h1 : m ≤ NodeHeight.st P v ((P.vertex v).last (!e)) := hm _ hlos
  have h2 : NodeHeight.st P v ((P.vertex v).last e) ≤ M :=
    le_trans (NodeHeight.le_Mk_one (q := NodeHeight.st P v) _) hMm
  have h3 : (0 : ℝ) < NodeHeight.st P v ((P.vertex v).last (!e)) := NodeHeight.st_pos P v _
  have h4 : (0 : ℝ) < NodeHeight.st P v ((P.vertex v).last e) := NodeHeight.st_pos P v _
  have hMpos : (0 : ℝ) < M :=
    lt_of_lt_of_le (NodeHeight.Mk_st_pos P v le_rfl (NodeHeight.card_pos P)) hMm
  have hden : (0 : ℝ) < NodeHeight.st P v ((P.vertex v).last (!e))
      + NodeHeight.st P v ((P.vertex v).last e) := by linarith
  simp only [NodeHeight.st] at h1 h2 h3 h4 hden ⊢
  rw [CylinderMass.cond_arrow P hP hn v e, le_div_iff₀ hden]
  have hsum : (0 : ℝ) < m + M := by linarith
  have hfac : (0 : ℝ) < m / (m + M) := by positivity
  have hstep : m / (m + M) * (ColShrink.cs P v ((P.vertex v).last (!e))
        + ColShrink.cs P v ((P.vertex v).last e))
      ≤ m / (m + M) * (ColShrink.cs P v ((P.vertex v).last (!e)) + M) := by
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hfac)
    linarith
  have hstep2 : m / (m + M) * (ColShrink.cs P v ((P.vertex v).last (!e)) + M)
      ≤ ColShrink.cs P v ((P.vertex v).last (!e)) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hsum]
    nlinarith [h1, hMpos]
  linarith

/-- The same bound in the form used along a blocked run: with `m = 𝔐(q_v)/Cb` and
`M = 2^j·𝔐(q_v)`, the arrow has mass at least `1/(1 + 2^j·Cb)`. -/
theorem cond_arrow_ge_blocked' (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (A' : Finset α) (v : List Bool) (e : Bool) {Cb M₀ : ℝ} {j : ℕ}
    (hCb : 1 ≤ Cb) (hbl : MinimalExit.Blocked P v A')
    (hm : ∀ b ∈ A', (1 / Cb) * M₀ ≤ NodeHeight.st P v b)
    (hM : NodeHeight.Mk 1 (NodeHeight.st P v) ≤ 2 ^ j * M₀) (hM0 : 0 < M₀) :
    1 / (1 + 2 ^ j * Cb) ≤ CylinderMass.cond P v [e] := by
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
theorem cond_blocked_ge_aux (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (A' : Finset α) {Cb : ℝ} (hCb : 1 ≤ Cb) :
    ∀ (δ : List Bool) (v : List Bool) (j L : ℕ) (M : ℝ), 0 < M → j + δ.length ≤ L →
      (∀ b ∈ A', (1 / Cb) * M ≤ NodeHeight.st P v b) →
      NodeHeight.Mk 1 (NodeHeight.st P v) ≤ 2 ^ j * M →
      (∀ i, i < δ.length → MinimalExit.Blocked P (v ++ δ.take i) A') →
      (1 / (1 + 2 ^ L * Cb)) ^ δ.length ≤ CylinderMass.cond P v δ := by
  intro δ
  induction δ with
  | nil =>
    intro v j L M hM0 hjL hbal hMk hbl
    rw [CylinderMass.cond_nil, List.length_nil, pow_zero]
  | cons e δ' ih =>
    intro v j L M hM0 hjL hbal hMk hbl
    have h0 : MinimalExit.Blocked P v A' := by
      have h := hbl 0 (by simp)
      rwa [List.take_zero, List.append_nil] at h
    have hstep : 1 / (1 + 2 ^ L * Cb) ≤ CylinderMass.cond P v [e] := by
      have h1 : 1 / (1 + 2 ^ j * Cb) ≤ CylinderMass.cond P v [e] :=
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
    have hbal' (b) (hb : b ∈ A') : (1 / Cb) * M ≤ NodeHeight.st P (v ++ [e]) b := le_trans (hbal b
        hb) (CylinderMass.state_mono P v [e] b)
    have hMk' : NodeHeight.Mk 1 (NodeHeight.st P (v ++ [e])) ≤ 2 ^ (j + 1) * M := by
      have h1 : NodeHeight.Mk 1 (NodeHeight.st P (v ++ [e]))
          ≤ 2 * NodeHeight.Mk 1 (NodeHeight.st P v) :=
        LargeLetter.Mk_one_step_le P hP hn v e
      have h2 : (2 : ℝ) ^ (j + 1) * M = 2 * (2 ^ j * M) := by
        rw [pow_succ]
        ring
      rw [h2]
      linarith
    have hbl' (i) (hi : i < δ'.length) : MinimalExit.Blocked P ((v ++ [e]) ++ δ'.take i) A' := by
      have h1 := hbl (i + 1) (by simp only [List.length_cons]; omega)
      rw [List.take_succ_cons] at h1
      have hconv : v ++ (e :: δ'.take i) = (v ++ [e]) ++ δ'.take i := by
        rw [List.append_assoc, List.singleton_append]
      rwa [hconv] at h1
    have hjL2 : j + 1 + δ'.length ≤ L := by
      simp only [List.length_cons] at hjL
      omega
    have hih := ih (v ++ [e]) (j + 1) L M hM0 hjL2 hbal' hMk' hbl'
    have hcond : CylinderMass.cond P v (e :: δ')
        = CylinderMass.cond P v [e] * CylinderMass.cond P (v ++ [e]) δ' := by
      have h := CylinderMass.cond_append P v [e] δ'
      rwa [List.singleton_append] at h
    have hpow : (1 / (1 + 2 ^ L * Cb)) ^ (e :: δ').length
        = (1 / (1 + 2 ^ L * Cb)) * (1 / (1 + 2 ^ L * Cb)) ^ δ'.length := by
      rw [List.length_cons, pow_succ']
    rw [hcond, hpow]
    exact mul_le_mul hstep hih (by positivity) (CylinderMass.cond_nonneg P v [e])

/-- **Item 3.** If all proper prefixes of `δ` are blocked and `|δ| ≤ L`, then the mass of `δ` from
a `Cb`-balanced node is at least `(1/(1 + 2^L·Cb))^L` — uniformly in the configuration, in `Cb`
and in the length of the run. -/
theorem cond_blocked_prefix_ge (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (A' : Finset α) (v : List Bool) {Cb : ℝ} (hCb : 1 ≤ Cb)
    (hbal : ∀ b ∈ A', (1 / Cb) * NodeHeight.Mk 1 (NodeHeight.st P v) ≤ NodeHeight.st P v b)
    {L : ℕ} (δ : List Bool) (hlen : δ.length ≤ L)
    (hbl : ∀ i, i < δ.length → MinimalExit.Blocked P (v ++ δ.take i) A') :
    (1 / (1 + 2 ^ L * Cb)) ^ L ≤ CylinderMass.cond P v δ := by
  have hM0 := NodeHeight.Mk_st_pos P v le_rfl (NodeHeight.card_pos P)
  have h := cond_blocked_ge_aux P hP hn A' hCb δ v 0 L (NodeHeight.Mk 1 (NodeHeight.st P v)) hM0
    (by omega) hbal (by simp) hbl
  refine le_trans ?_ h
  have hr0 : (0 : ℝ) ≤ 1 / (1 + 2 ^ L * Cb) := by positivity
  have hr1 : 1 / (1 + 2 ^ L * Cb) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h2 : (0 : ℝ) ≤ 2 ^ L * Cb := by positivity
    linarith
  exact pow_le_pow_of_le_one hr0 hr1 hlen

/-! ## 3. The minimal exit word: a uniform length bound -/

omit [DecidableEq α] in
/-- **The exit word of a minimal exit is short**: there is a bound on the length of a minimal exit
word, uniformly in `A'` and in the node. -/
theorem exists_uniform_minimal_exit (P : IETDatum₂ α n) (hP : P.Irreducible) (_hn : 2 ≤ n) :
    ∃ L : ℕ, ∀ (A' : Finset α) (w : List Bool), A'.Nonempty → A' ≠ Finset.univ →
      ∃ u : List Bool, MinimalExit.Exit P (w ++ u) A' ∧
        (∀ i, i < u.length → MinimalExit.Blocked P (w ++ u.take i) A') ∧
        u.length ≤ L := by
  obtain ⟨L, hL⟩ := RauzyReach.exists_path_between P
  refine ⟨L, fun A' w hne hprop => ?_⟩
  obtain ⟨u, hu, hmin, hblk⟩ := MinimalExit.exists_minimal_exit P hP w hne hprop
  obtain ⟨θ, hθ⟩ : ∃ θ : α, θ ∉ A' := by
    by_contra h
    exact hprop (Finset.eq_univ_iff_forall.mpr (by simpa using h))
  obtain ⟨b, hb⟩ := hne
  have hbθ : b ≠ θ := fun h => hθ (h ▸ hb)
  obtain ⟨u₀, e, -, h2⟩ := IETDatum₂.pairReach_all P hP P hP b θ hbθ
  have hex (v : List Bool) : ∃ u : List Bool,
      u.length ≤ L ∧ MinimalExit.Exit P (v ++ u) A' := by
    obtain ⟨u, hulen, hu⟩ := hL (P.vertex v) (P.vertex u₀) ⟨v, rfl⟩ ⟨u₀, rfl⟩
    refine ⟨u, hulen, ?_⟩
    have hvu : P.vertex (v ++ u) = (P.vertex v).vertex u := IETDatum₂.vertex_append P v u
    have hEq : P.vertex (v ++ u) = P.vertex u₀ := by rw [hvu, hu]
    cases e with
    | false => exact Or.inl (by rw [hEq]; simp only [Bool.not_false] at h2; rw [h2]; exact hθ)
    | true => exact Or.inr (by rw [hEq]; simp only [Bool.not_true] at h2; rw [h2]; exact hθ)
  obtain ⟨v, hv1, hv2⟩ := hex w
  exact ⟨u, hu, hblk, le_trans (hmin v hv2) hv1⟩

/-! ## 4. The last arrow

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
has mass `h_out/(h_out + h_{A'})` (`CylinderMass.cond_arrow`), and there `h_out` is
not controlled by
the `A'`-balance at all.  That case belongs to `Γ₃`/`Γ₄`, not to `Γ₂`.
  -/

/-- **Item 5, resolved.**  Item 3 applies verbatim to the *whole* minimal exit word `u`: the
hypothesis `hmin` is exactly the third component of `MinimalExit.exists_minimal_exit`, and it
covers the parent of the last arrow like any other prefix.  Hence the exit step needs no separate
estimate and no hypothesis on the outsider's height. -/
theorem cond_minimal_exit_ge (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (A' : Finset α) (v : List Bool) {Cb : ℝ} (hCb : 1 ≤ Cb)
    (hbal : ∀ b ∈ A', (1 / Cb) * NodeHeight.Mk 1 (NodeHeight.st P v) ≤ NodeHeight.st P v b)
    {L : ℕ} (u : List Bool)
    (hmin : ∀ i, i < u.length → MinimalExit.Blocked P (v ++ u.take i) A')
    (hlen : u.length ≤ L) :
    (1 / (1 + 2 ^ L * Cb)) ^ L ≤ CylinderMass.cond P v u :=
  cond_blocked_prefix_ge P hP hn A' v hCb hbal u hlen hmin

/-! ## 5. What remains: the growth constant of the input family

Everything above is unconditional.  What `Induction.ExtMassGen` also asks for is a growth bound by a
*constant* `C₂` on the composite word `γ_s ++ γ_e`; the pigeonhole `Γ₁` of the repository supplies
the mass `1/C₁` and the `Cb`-balance of its endpoints, but its growth clause is `Cb`, not a
constant. With the mass bound recorded here the balance constant of the assembly becomes `KeeGen
(fun Cb => K·Cb^(L+1)) (2^L·C₂')`, i.e. `4·#α·(2^L C₂')²·Cb + 2·K·Cb^(L+1) + 1`
(`Induction.balanceStep_of_extMassGen`), so the mass side of `Γ₂` is settled by §3–§5 and only the
growth constant remains. -/

end MinimalExitMass

end
