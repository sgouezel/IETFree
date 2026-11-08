/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.RichPath.LevelMass
public import IETFree.RauzyVeech.RichPath.MinimalExit
public import IETFree.RauzyVeech.RichPath.Stopping

/-!
# The unclean mass at a straddling node is at most `k/(2d)` — the `A'`-sum supermartingale

The second half of the `Γ₃` estimate (`k ≥ 2`).  The statement asks, at a node `w`
with a row outside `A'`, for a prefix-free family of `cond`-mass `> 1/2` whose members stop at a
*clean* exit (exit arrow, or the maximum has crossed `2d·M(q_w)`) with all `A'`-heights below
`2d·M(q_w)`.

The reduction `straddleMassCard_of_goodMass_straddle` turns this into a single
numerical statement: the level-`N` words whose **first stop event is unclean** (`Bad`)
carry mass `≤ 1/2`.  This file proves the bound in the shape the node hypothesis allows:

  `∑_{δ ∈ Bad at level N} cond P w δ ≤ #A' / (2·#α)`

for every node `w` at which some row end lies outside `A'` (i.e. `¬ Blocked`),
with **no** hypothesis on the heights (in particular `Cb`-balancedness is not used).  Since `#A' <
#α` this is `< 1/2`, which is exactly what the target needs; the constant is `#A'/(2·#α)`, to be
compared with the sharp `1/(2·#α)` measured on the extremal configurations.

## The argument

Write `S(u) = ∑_{b ∈ A'} colSum P u b` for the `A'`-sum (the potential).

* **Locality.** A step of type `e` moves only the loser `last !e`, by the winner's height
  (`colSum_append_singleton`), and `cond P u [e] = h_loser/(h_loser + h_winner)`
  (`cond_arrow`).  Hence
  * at a **blocked** node (both row ends in `A'`) both letters grow `A'`, and `∑ cond·S = S+…`;
  * at a **straddling** node (one row end `a ∈ A'`, the other `c ∉ A'`) the letter with winner
    is an *exit arrow*, and the other letter carries `h_a/(h_a+h_c)` and sends `S ↦ S + h_c`;
  * at an **outside** node (both row ends outside `A'`) both letters carry together `1` and
    leave `S` alone.
  Therefore at every **non-blocked** node, restricted to the letters that are not exit arrows,
  `∑ cond(u,[e])·S(u ++ [e]) ≤ S(u)` (the case `h_a ≤ S` is all that is used).

* **The blocked region is unreachable.** A step of type `e` keeps the row end of type `e`
  (`IETDatum₂.rvStep_last_self`), so a child is blocked only if the parent's row end of that type is
  in `A'`; if the parent is not blocked, the other row end is outside, and the letter is then an
  *exit arrow* — a stop event.  Hence along a word in which no exit arrow has been read, no node
  blocked.  (So blocked nodes are irrelevant at the nodes the estimate talks about.)

* **The frontier bound.** Let `S_N` be the sum of `cond·S` over the level-`N` words that have read
  no exit arrow and crossed nothing, plus the same over all *first crossing* words of level `≤ N`.
  The locality inequality makes this invariant non-increasing in `N`, and its value at `N = 0` is
  `S(w)`.  Since a crossing word has `S > thr = 2d·M(q_w)`, while `S(w) ≤ #A'·M(q_w)`,

  `∑_{first crossing, level ≤ N} cond ≤ S(w)/thr ≤ #A'/(2·#α)`.

* **Unclean stops are crossings.** If the first stop event of `δ` is unclean, then some `A'`-height
  already exceeds the threshold there, hence so does the maximum: the first stop event is a
  `Huge` event.  And no `A'`-height crossed before (that would have been a `Huge` stop event
  earlier), so `δ` extends a first crossing word.  Covering the bad words by the crossing words
  (`sum_cond_le_sum_of_covers`) finishes.

No assumptions beyond `P.Irreducible` and `2 ≤ n` are used.
-/

open Finset IntervalExchange.IETDatum₂
open scoped BigOperators

@[expose] public section

namespace IntervalExchange.RauzyVeech.RichPath

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Row ends, blocked nodes, and the potential -/

omit [DecidableEq α] in
/-- A step of type `e` keeps the row end of type `e`. -/
theorem vertex_last_append_singleton (P : IETDatum₂ α n) (u : List Bool) (e : Bool) :
    (P.vertex (u ++ [e])).last e = (P.vertex u).last e := by
  rw [IETDatum₂.vertex_append_singleton, IETDatum₂.rvStep_last_self]

/-- The `A'`-potential: the sum of the `A'`-heights. -/
noncomputable def pot (P : IETDatum₂ α n) (u : List Bool) (A' : Finset α) : ℝ :=
  ∑ b ∈ A', colSum P u b

theorem pot_nonneg (P : IETDatum₂ α n) (u : List Bool) (A' : Finset α) :
    0 ≤ pot P u A' :=
  Finset.sum_nonneg fun b _ => (colSum_pos P u b).le

theorem colSum_le_pot (P : IETDatum₂ α n) (u : List Bool) {A' : Finset α} {b : α} (hb : b ∈ A') :
    colSum P u b ≤ pot P u A' :=
  Finset.single_le_sum (f := fun b => colSum P u b)
    (fun b _ => (colSum_pos P u b).le) hb

theorem pot_le_card_mul_Mx (P : IETDatum₂ α n) (u : List Bool) (A' : Finset α) :
    pot P u A' ≤ (A'.card : ℝ) * Mx P u := by
  calc pot P u A' ≤ ∑ _b ∈ A', Mx P u :=
        Finset.sum_le_sum fun b _ => colSum_le_Mx P u b
    _ = (A'.card : ℝ) * Mx P u := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **The `A'`-potential one step later**: only the loser moves, by the winner's height, so `pot`
grows by the winner's height exactly when the loser lies in `A'`. -/
theorem pot_append_singleton (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (u : List Bool) (e : Bool) (A' : Finset α) :
    pot P (u ++ [e]) A' = pot P u A' +
      (if (P.vertex u).last (!e) ∈ A' then colSum P u ((P.vertex u).last e) else 0) := by
  have hstep (b : α) : colSum P (u ++ [e]) b =
      colSum P u b + (if b = (P.vertex u).last (!e) then
        colSum P u ((P.vertex u).last e) else 0) := colSum_append_singleton P hP hn
            u e b
  rw [pot, pot, Finset.sum_congr rfl fun b _ => hstep b, Finset.sum_add_distrib,
    Finset.sum_ite_eq']

/-! ## 2. The local supermartingale inequality  At a node `u` that is not blocked, summing
`cond·pot` over the letters that are **not** exit arrows never increases the potential.  The three
cases are: both row ends in `A'` (excluded), exactly one row end in `A'` (only the *other* letter
survives — the one with the outside winner, adding the outside height to the `A'`-sum), and both row
ends outside (both letters survive and leave the `A'`-sum alone, and their masses add up to `1`). -/

/-- The potential-weighted mass of the letter `e` at `u`, killed when `e` is an exit arrow. -/
noncomputable def nw (P : IETDatum₂ α n) (A' : Finset α) (u : List Bool) (e : Bool) : ℝ := by
  classical
  exact if ExitArrow P A' u [] e then 0
    else cond P u [e] * pot P (u ++ [e]) A'

theorem nw_of_exitArrow (P : IETDatum₂ α n) {A' : Finset α} {u : List Bool} {e : Bool}
    (h : ExitArrow P A' u [] e) : nw P A' u e = 0 := by
  rw [nw, ite_eq_left h]

theorem nw_of_not_exitArrow (P : IETDatum₂ α n) {A' : Finset α} {u : List Bool} {e : Bool}
    (h : ¬ ExitArrow P A' u [] e) :
    nw P A' u e = cond P u [e] * pot P (u ++ [e]) A' := by
  rw [nw, ite_eq_right h]

/-- **Straddling step**: the letter whose winner is the `A'`-row end is an exit arrow, and the other
letter carries `h_a/(h_a + h_c)` and adds the outside height `h_c` to the `A'`-sum. -/
theorem step_le_of_exitArrow (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {A' : Finset α}
    {u : List Bool} {e : Bool} (he : ExitArrow P A' u [] e) :
    cond P u [!e] * pot P (u ++ [!e]) A' ≤ pot P u A' := by
  have hwin : (P.vertex u).last e ∈ A' := by simpa using he.1
  have hlos : (P.vertex u).last (!e) ∉ A' := by simpa using he.2
  have hnn : (!(!e)) = e := by cases e <;> rfl
  set a := colSum P u ((P.vertex u).last e) with ha
  set c := colSum P u ((P.vertex u).last (!e)) with hc
  have hapos : 0 < a := colSum_pos P u _
  have hcpos : 0 < c := colSum_pos P u _
  have hcond : cond P u [!e] = a / (a + c) := by
    have h := cond_arrow P hP hn u (!e)
    rw [hnn] at h
    simpa [ha, hc] using h
  have hpot : pot P (u ++ [!e]) A' = pot P u A' + c := by
    have h := pot_append_singleton P hP hn u (!e) A'
    rw [hnn, ite_eq_left hwin] at h
    simpa [hc] using h
  have hle : a ≤ pot P u A' := colSum_le_pot P u hwin
  rw [hcond, hpot, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- **Outside step**: if both row ends are outside `A'`, both letters are non-exit, the potential
does not move, and the two masses add up to `1`. -/
theorem step_eq_of_outside (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {A' : Finset α}
    {u : List Bool} (h1 : (P.vertex u).last true ∉ A') (h2 : (P.vertex u).last false ∉ A') :
    ∑ e : Bool, nw P A' u e = pot P u A' := by
  have hne (e : Bool) : ¬ ExitArrow P A' u [] e := by
    cases e with
    | false => exact fun h => h2 (by simpa using h.1)
    | true => exact fun h => h1 (by simpa using h.1)
  have hpot (e : Bool) : pot P (u ++ [e]) A' = pot P u A' := by
    have h := pot_append_singleton P hP hn u e A'
    have hlos : (P.vertex u).last (!e) ∉ A' := by
      cases e with
      | false => simpa using h1
      | true => simpa using h2
    rw [ite_eq_right hlos, add_zero] at h
    exact h
  have hsum : (∑ e : Bool, nw P A' u e)
      = nw P A' u true + nw P A' u false := Fintype.sum_bool _
  rw [hsum, nw_of_not_exitArrow P (hne true), nw_of_not_exitArrow P (hne false), hpot, hpot,
    ← add_mul, cond_arrow_sum P hP hn u, one_mul]

/-- **The local supermartingale inequality.**  At a node that is not blocked, the potential-weighted
mass of the non-exit letters never exceeds the potential. -/
theorem step_sum_le (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {A' : Finset α}
    {u : List Bool} (hbl : ¬ Blocked P u A') :
    ∑ e : Bool, nw P A' u e ≤ pot P u A' := by
  have hsum : (∑ e : Bool, nw P A' u e) = nw P A' u true + nw P A' u false :=
    Fintype.sum_bool _
  simp only [Blocked, not_and_or] at hbl
  rcases hbl with h1 | h2
  · -- `last true ∉ A'`
    by_cases hq : (P.vertex u).last false ∈ A'
    · -- straddling, the exit arrow is `false`
      have he : ExitArrow P A' u [] false :=
        ⟨by simpa using hq, by simpa using h1⟩
      have ht : ¬ ExitArrow P A' u [] true :=
        fun h => h1 (by simpa using h.1)
      have h := step_le_of_exitArrow P hP hn (A' := A') (u := u) (e := false) he
      simp only [Bool.not_false] at h
      rw [hsum, nw_of_exitArrow P he, nw_of_not_exitArrow P ht]
      simpa using h
    · rw [step_eq_of_outside P hP hn (A' := A') h1 hq]
  · -- `last false ∉ A'`
    by_cases hp : (P.vertex u).last true ∈ A'
    · -- straddling, the exit arrow is `true`
      have he : ExitArrow P A' u [] true :=
        ⟨by simpa using hp, by simpa using h2⟩
      have hf : ¬ ExitArrow P A' u [] false :=
        fun h => h2 (by simpa using h.1)
      have h := step_le_of_exitArrow P hP hn (A' := A') (u := u) (e := true) he
      simp only [Bool.not_true] at h
      rw [hsum, nw_of_exitArrow P he, nw_of_not_exitArrow P hf]
      simpa using h
    · rw [step_eq_of_outside P hP hn (A' := A') hp h2]

/-! ## 3. The blocked region is unreachable from a node with a row end outside `A'`  A step of type
`e` keeps the row end of type `e`, so a blocked child forces the parent's row end of that type into
`A'`; if the parent is not blocked the other row end is outside, and the letter is then an exit
arrow — a stop event.  Hence along a word in which no exit arrow is read, no node is ever blocked.
This removes the blocked phase from the `Γ₃` analysis at a straddling node. -/

omit [DecidableEq α] in
/-- The child of a non-blocked node along a non-exit arrow is not blocked. -/
theorem blocked_append_of_not_exitArrow (P : IETDatum₂ α n) {A' : Finset α} {u : List Bool}
    {e : Bool} (hbl : ¬ Blocked P u A')
    (hne : ¬ ExitArrow P A' u [] e) :
    ¬ Blocked P (u ++ [e]) A' := by
  intro hb
  simp only [Blocked] at hbl hb
  simp only [ExitArrow, List.append_nil] at hne
  cases e with
  | true =>
    have hpar : (P.vertex u).last true ∈ A' := by
      simpa only [vertex_last_append_singleton P u true] using hb.1
    exact hne ⟨hpar, fun hc => hbl ⟨hpar, hc⟩⟩
  | false =>
    have hpar : (P.vertex u).last false ∈ A' := by
      simpa only [vertex_last_append_singleton P u false] using hb.2
    exact hne ⟨hpar, fun hc => hbl ⟨hc, hpar⟩⟩

/-- A word none of whose letters is an exit arrow, read successively from `w`. -/
def NoExit (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) (δ : List Bool) : Prop :=
  ∀ g, g < δ.length → ¬ ExitArrow P A' w (δ.take g) (δ.getD g false)

omit [DecidableEq α] in
/-- The recursive unfolding of `NoExit` at the first letter. -/
theorem noExit_cons_iff (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) (e : Bool)
    (t : List Bool) :
    NoExit P A' w (e :: t) ↔
      ¬ ExitArrow P A' w [] e ∧ NoExit P A' (w ++ [e]) t := by
  simp only [NoExit, ExitArrow]
  constructor
  · rintro h
    refine ⟨?_, ?_⟩
    · simpa using h 0 (by simp)
    · intro g hg
      have h1 := h (g + 1) (by simpa using hg)
      rw [List.take_succ_cons] at h1
      rw [← List.singleton_append, ← List.append_assoc] at h1
      simpa using h1
  · rintro ⟨h0, ht⟩ g hg
    rcases Nat.eq_zero_or_pos g with hg0 | hpos
    · subst hg0
      simpa using h0
    · obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      have h1 := ht g' (by simpa using hg)
      rw [List.take_succ_cons]
      rw [← List.singleton_append, ← List.append_assoc]
      simpa using h1

omit [DecidableEq α] in
/-- **The blocked region is unreachable along a word with no exit arrow**, when the root is
not blocked. -/
theorem not_blocked_of_noExit (P : IETDatum₂ α n) {A' : Finset α} {w : List Bool}
    (h0 : ¬ Blocked P w A') {δ : List Bool} (hδ : NoExit P A' w δ) :
    ¬ Blocked P (w ++ δ) A' := by
  induction δ generalizing w with
  | nil => simpa using h0
  | cons e t ih =>
    rw [noExit_cons_iff] at hδ
    obtain ⟨hne, ht⟩ := hδ
    have h1 : ¬ Blocked P (w ++ [e]) A' :=
      blocked_append_of_not_exitArrow P h0 hne
    have h2 := ih (w := w ++ [e]) h1 ht
    rwa [← List.singleton_append, ← List.append_assoc]

/-! ## 4. The frontier of the no-exit / no-crossing tree  The tree generated by the letters that are
not exit arrows, stopped at the first `A'`-crossing. The potential-weighted mass of its frontier
never exceeds the potential at the root. -/

/-- The `A'`-crossing at `w ++ μ`: some `A'`-height exceeds the threshold. -/
def Cr (P : IETDatum₂ α n) (A' : Finset α) (w μ : List Bool) : Prop :=
  ∃ b ∈ A', thr P w < colSum P (w ++ μ) b

theorem cr_nil_false (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) :
    ¬ Cr P A' w [] := by
  rintro ⟨b, -, hb⟩
  rw [List.append_nil] at hb
  exact absurd hb (not_lt.mpr (colSum_le_thr P w b))

/-- Alive at `δ`: no exit arrow read, and no crossing at any prefix up to `δ`. -/
def Alive (P : IETDatum₂ α n) (A' : Finset α) (w δ : List Bool) : Prop :=
  NoExit P A' w δ ∧ ∀ i, i ≤ δ.length → ¬ Cr P A' w (δ.take i)

/-- First crossing at `δ`: no exit arrow read, the crossing happens at `δ`, nowhere earlier. -/
def FirstCr (P : IETDatum₂ α n) (A' : Finset α) (w δ : List Bool) : Prop :=
  NoExit P A' w δ ∧ Cr P A' w δ ∧ ∀ i, i < δ.length → ¬ Cr P A' w (δ.take i)

/-- Decidability of `Alive`, classically: the file filters words by it.  `local`, so that
nothing outside it inherits a classical instance that a computable one would have to shadow. -/
noncomputable local instance aliveDecidable (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) :
    DecidablePred (Alive P A' w) := fun _ => Classical.propDecidable _

/-- Decidability of `FirstCr`, classically (`local`, as for `aliveDecidable`). -/
noncomputable local instance firstCrDecidable (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) :
    DecidablePred (FirstCr P A' w) := fun _ => Classical.propDecidable _

/-- Decidability of `Bad`, classically (`local`, as for `aliveDecidable`). -/
noncomputable local instance badDecidable' (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) :
    DecidablePred (Bad P A' w) := fun _ => Classical.propDecidable _

/-- Decidability of `StopEv`, classically (`local`, as for `aliveDecidable`). -/
noncomputable local instance stopEvDecidable' (P : IETDatum₂ α n) (A' : Finset α)
    (w δ : List Bool) :
    DecidablePred (StopEv P A' w δ) := fun _ => Classical.propDecidable _

/-- The potential-weighted mass of the word `δ`. -/
noncomputable def wt (P : IETDatum₂ α n) (A' : Finset α) (w δ : List Bool) : ℝ :=
  cond P w δ * pot P (w ++ δ) A'

theorem wt_nil (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) :
    wt P A' w [] = pot P w A' := by
  simp [wt]

/-- The value of `getD` at the appended last letter. -/
theorem getD_append_singleton_len (γ : List Bool) (e : Bool) :
    (γ ++ [e]).getD γ.length false = e := by
  induction γ with
  | nil => simp
  | cons a t ih => simp

/-- The value of `getD` before the appended last letter. -/
theorem getD_append_singleton_of_lt (γ : List Bool) (e : Bool) {g : ℕ} (hg : g < γ.length) :
    (γ ++ [e]).getD g false = γ.getD g false := by
  induction γ generalizing g with
  | nil => simp at hg
  | cons a t ih =>
    cases g with
    | zero => simp
    | succ g' => simpa [List.getD_cons_succ] using ih (by simpa using hg)

omit [DecidableEq α] in
/-- `NoExit` of `γ ++ [e]` splits as `NoExit γ` plus the last letter not being an exit arrow. -/
theorem noExit_append_singleton (P : IETDatum₂ α n) (A' : Finset α) (w γ : List Bool) (e : Bool) :
    NoExit P A' w (γ ++ [e]) ↔ NoExit P A' w γ ∧ ¬ ExitArrow P A' w γ e := by
  simp only [NoExit, ExitArrow]
  constructor
  · intro h
    refine ⟨fun g hg => ?_, ?_⟩
    · have h1 := h g (by simp only [List.length_append, List.length_singleton]; omega)
      rw [List.take_append_of_le_length (le_of_lt hg), getD_append_singleton_of_lt γ e hg] at h1
      exact h1
    · have h1 := h γ.length (by simp)
      rw [List.take_left, getD_append_singleton_len] at h1
      exact h1
  · rintro ⟨h1, h2⟩ g hg
    have hgl : g ≤ γ.length := by
      simp only [List.length_append, List.length_singleton] at hg; omega
    rw [List.take_append_of_le_length hgl]
    rcases Nat.lt_or_eq_of_le hgl with hlt | heq
    · rw [getD_append_singleton_of_lt γ e hlt]
      exact h1 g hlt
    · subst heq
      have ht : List.take γ.length γ = γ := by simp
      have hd : (γ ++ [e]).getD γ.length false = e := getD_append_singleton_len γ e
      rw [ht, hd]
      exact h2

/-- Alive passes to the child unless the letter is an exit arrow or the crossing happens. -/
theorem alive_append_singleton (P : IETDatum₂ α n) {A' : Finset α} {w γ : List Bool}
    (h : Alive P A' w γ) (e : Bool)
    (hne : ¬ ExitArrow P A' w γ e) (hcr : ¬ Cr P A' w (γ ++ [e])) :
    Alive P A' w (γ ++ [e]) := by
  obtain ⟨hno, hnc⟩ := h
  refine ⟨(noExit_append_singleton P A' w γ e).mpr ⟨hno, hne⟩, ?_⟩
  intro i hi
  have hi' : i ≤ γ.length + 1 := by simpa using hi
  rcases Nat.lt_or_eq_of_le hi' with hlt | heq
  · have hil : i ≤ γ.length := by omega
    rw [List.take_append_of_le_length hil]
    rcases Nat.lt_or_eq_of_le hil with hlt2 | heq2
    · exact hnc i (le_of_lt hlt2)
    · subst heq2
      exact hnc γ.length le_rfl
  · subst heq
    have hL : (γ ++ [e]).take (γ.length + 1) = γ ++ [e] := by
      simp
    rw [hL]
    exact hcr

/-- First crossings pass to the child when the crossing happens there and the parent is alive. -/
theorem firstCr_append_singleton (P : IETDatum₂ α n) {A' : Finset α} {w γ : List Bool}
    (h : Alive P A' w γ) (e : Bool)
    (hne : ¬ ExitArrow P A' w γ e) (hcr : Cr P A' w (γ ++ [e])) :
    FirstCr P A' w (γ ++ [e]) := by
  obtain ⟨hno, hnc⟩ := h
  refine ⟨(noExit_append_singleton P A' w γ e).mpr ⟨hno, hne⟩, hcr, ?_⟩
  intro i hi
  have hil : i ≤ γ.length := by
    simp only [List.length_append, List.length_singleton] at hi; omega
  rw [List.take_append_of_le_length hil]
  exact hnc i hil

/-- Neither alive nor a first crossing, when the letter is an exit arrow. -/
theorem not_alive_not_firstCr_of_exitArrow (P : IETDatum₂ α n) {A' : Finset α} {w γ : List Bool}
    (e : Bool) (hne : ExitArrow P A' w γ e) :
    ¬ Alive P A' w (γ ++ [e]) ∧ ¬ FirstCr P A' w (γ ++ [e]) := by
  have h : ¬ NoExit P A' w (γ ++ [e]) := by
    rw [noExit_append_singleton]
    exact fun h => h.2 hne
  exact ⟨fun h1 => h h1.1, fun h1 => h h1.1⟩

/-! ## 5. The level decomposition and the frontier bound -/

omit [DecidableEq α] in
theorem exitArrow_append_iff (P : IETDatum₂ α n) (A' : Finset α) (w γ : List Bool) (e : Bool) :
    ExitArrow P A' w γ e ↔ ExitArrow P A' (w ++ γ) [] e := by
  simp [ExitArrow]

/-- Alive words have an alive prefix. -/
theorem alive_take_of_alive_append (P : IETDatum₂ α n) {A' : Finset α} {w γ : List Bool}
    {e : Bool} (h : Alive P A' w (γ ++ [e])) : Alive P A' w γ := by
  refine ⟨(noExit_append_singleton P A' w γ e).mp h.1 |>.1, fun i hi => ?_⟩
  have h1 := h.2 i (by simp only [List.length_append, List.length_singleton]; omega)
  rwa [List.take_append_of_le_length hi] at h1

/-- A first crossing word has an alive prefix. -/
theorem alive_take_of_firstCr_append (P : IETDatum₂ α n) {A' : Finset α} {w γ : List Bool}
    {e : Bool} (h : FirstCr P A' w (γ ++ [e])) : Alive P A' w γ := by
  refine ⟨(noExit_append_singleton P A' w γ e).mp h.1 |>.1, fun i hi => ?_⟩
  rcases Nat.lt_or_eq_of_le hi with hlt | heq
  · have h1 := h.2.2 i (by simp only [List.length_append, List.length_singleton]; omega)
    rwa [List.take_append_of_le_length (le_of_lt hlt)] at h1
  · subst heq
    have h1 := h.2.2 γ.length (by simp)
    rwa [List.take_append_of_le_length (le_refl γ.length)] at h1

/-- The weight of one step in the tree, in terms of `cond` at the parent and the local step
functional `nw`. -/
theorem wt_append_singleton (P : IETDatum₂ α n) (A' : Finset α) (w γ : List Bool) (e : Bool) :
    wt P A' w (γ ++ [e]) =
      cond P w γ *
        (cond P (w ++ γ) [e] * pot P ((w ++ γ) ++ [e]) A') := by
  rw [wt, cond_append]
  rw [← List.append_assoc, mul_assoc]

/-- **The two children of an alive word**: either the crossing happens at the child (a first
crossing) or it does not (the child is alive); the two contributions add up to the local step
functional at the parent. -/
theorem child_weight (P : IETDatum₂ α n) (A' : Finset α) (w γ : List Bool) (e : Bool)
    (hγ : Alive P A' w γ) :
    (if Alive P A' w (γ ++ [e]) then wt P A' w (γ ++ [e]) else 0)
        + (if FirstCr P A' w (γ ++ [e]) then wt P A' w (γ ++ [e]) else 0)
      = cond P w γ * nw P A' (w ++ γ) e := by
  by_cases hex : ExitArrow P A' w γ e
  · obtain ⟨h1, h2⟩ := not_alive_not_firstCr_of_exitArrow P e hex
    rw [ite_eq_right h1, ite_eq_right h2, zero_add, nw_of_exitArrow P (e := e)
      ((exitArrow_append_iff P A' w γ e).mp hex)]
    ring
  · have hwt : wt P A' w (γ ++ [e])
        = cond P w γ * nw P A' (w ++ γ) e := by
      rw [wt_append_singleton, nw_of_not_exitArrow P (e := e)
        ((exitArrow_append_iff P A' w γ e).not.mp hex)]
    by_cases hcr : Cr P A' w (γ ++ [e])
    · have hnotAlive : ¬ Alive P A' w (γ ++ [e]) := by
        intro h
        have h3 := h.2 (γ.length + 1) (by simp)
        rw [List.take_append, Nat.add_sub_cancel_left, List.take_of_length_le (by simp),
          List.take_one, List.head?_cons, Option.toList_some] at h3
        exact h3 hcr
      rw [ite_eq_right hnotAlive, ite_eq_left (firstCr_append_singleton P hγ e hex hcr),
          zero_add, hwt]
    · have hfirst : ¬ FirstCr P A' w (γ ++ [e]) := fun h => hcr h.2.1
      rw [ite_eq_left (alive_append_singleton P hγ e hex hcr), ite_eq_right hfirst, add_zero, hwt]

/-- **The children of an alive word carry at most its weight.** -/
theorem child_sum (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {A' : Finset α}
    {w : List Bool} (hbl0 : ¬ Blocked P w A') {γ : List Bool}
    (hγ : Alive P A' w γ) :
    ∑ e : Bool, ((if Alive P A' w (γ ++ [e]) then wt P A' w (γ ++ [e]) else 0)
        + (if FirstCr P A' w (γ ++ [e]) then wt P A' w (γ ++ [e]) else 0))
      ≤ wt P A' w γ := by
  have hbl : ¬ Blocked P (w ++ γ) A' :=
    not_blocked_of_noExit P hbl0 hγ.1
  calc ∑ e : Bool, ((if Alive P A' w (γ ++ [e]) then wt P A' w (γ ++ [e]) else 0)
        + (if FirstCr P A' w (γ ++ [e]) then wt P A' w (γ ++ [e]) else 0))
      = ∑ e : Bool, cond P w γ * nw P A' (w ++ γ) e :=
        Finset.sum_congr rfl fun e _ => child_weight P A' w γ e hγ
    _ = cond P w γ * ∑ e : Bool, nw P A' (w ++ γ) e := by
        rw [Finset.mul_sum]
    _ ≤ cond P w γ * pot P (w ++ γ) A' :=
        mul_le_mul_of_nonneg_left (step_sum_le P hP hn hbl) (cond_pos P w γ).le
    _ = wt P A' w γ := (rfl)

/-- The level-`N+1` words are the children of the level-`N` words. -/
theorem sum_levelWords_succ (f : List Bool → ℝ) (N : ℕ) :
    ∑ δ ∈ levelWords (N + 1), f δ
      = ∑ γ ∈ levelWords N, (f (γ ++ [true]) + f (γ ++ [false])) := by
  have hdisj : Disjoint ((levelWords N).image (fun δ => δ ++ [true]))
      ((levelWords N).image (fun δ => δ ++ [false])) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hb
    exact append_true_ne_append_false hy.symm
  rw [levelWords_succ, Finset.sum_union hdisj,
    Finset.sum_image (fun a _ b _ h => List.append_cancel_right h),
    Finset.sum_image (fun a _ b _ h => List.append_cancel_right h),
    ← Finset.sum_add_distrib]

/-- **The children of an alive word carry at most its weight**, letter by letter. -/
theorem child_sum2 (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {A' : Finset α}
    {w : List Bool} (hbl0 : ¬ Blocked P w A') {γ : List Bool}
    (hγ : Alive P A' w γ) :
    ((if Alive P A' w (γ ++ [true]) then wt P A' w (γ ++ [true]) else 0)
        + (if FirstCr P A' w (γ ++ [true]) then wt P A' w (γ ++ [true]) else 0))
      + ((if Alive P A' w (γ ++ [false]) then wt P A' w (γ ++ [false]) else 0)
        + (if FirstCr P A' w (γ ++ [false]) then wt P A' w (γ ++ [false]) else 0))
      ≤ wt P A' w γ := by
  have h := child_sum P hP hn hbl0 hγ
  rw [Fintype.sum_bool (fun e => ((if Alive P A' w (γ ++ [e]) then wt P A' w (γ ++ [e]) else 0)
    + (if FirstCr P A' w (γ ++ [e]) then wt P A' w (γ ++ [e]) else 0)))] at h
  linarith [h]

/-- **The frontier bound.**  The potential-weighted mass of the level-`N` alive words plus that of
all first-crossing words of level at most `N` never exceeds the potential at the root. -/
theorem frontier_bound (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {A' : Finset α}
    {w : List Bool} (hbl0 : ¬ Blocked P w A') (N : ℕ) :
    (∑ δ ∈ (levelWords N).filter (Alive P A' w), wt P A' w δ)
      + (∑ m ∈ Finset.range (N + 1),
          ∑ δ ∈ (levelWords m).filter (FirstCr P A' w), wt P A' w δ)
      ≤ pot P w A' := by
  induction N with
  | zero =>
    have halive : Alive P A' w [] := by
      refine ⟨fun g hg => by simp at hg, fun i hi => ?_⟩
      have hi0 : i = 0 := by simpa using hi
      subst hi0
      simpa using cr_nil_false P A' w
    have hfirst : ¬ FirstCr P A' w [] := fun h => cr_nil_false P A' w h.2.1
    have hlev : levelWords 0 = {[]} := (rfl)
    have h1 : (∑ δ ∈ (levelWords 0).filter (Alive P A' w), wt P A' w δ)
        = pot P w A' := by
      rw [hlev, Finset.filter_singleton, ite_eq_left halive, Finset.sum_singleton, wt_nil]
    have h2 : (∑ m ∈ Finset.range (0 + 1),
        ∑ δ ∈ (levelWords m).filter (FirstCr P A' w), wt P A' w δ) = 0 := by
      rw [Finset.range_one, Finset.sum_singleton, hlev, Finset.filter_singleton,
          ite_eq_right hfirst,
        Finset.sum_empty]
    rw [h1, h2, add_zero]
  | succ N ih =>
    have hsplit : (∑ m ∈ Finset.range (N + 1 + 1),
        ∑ δ ∈ (levelWords m).filter (FirstCr P A' w), wt P A' w δ)
        = (∑ m ∈ Finset.range (N + 1),
            ∑ δ ∈ (levelWords m).filter (FirstCr P A' w), wt P A' w δ)
          + ∑ δ ∈ (levelWords (N + 1)).filter (FirstCr P A' w), wt P A' w δ := by
      rw [Finset.sum_range_succ]
    have hkey : (∑ δ ∈ (levelWords (N + 1)).filter (Alive P A' w), wt P A' w δ)
        + (∑ δ ∈ (levelWords (N + 1)).filter (FirstCr P A' w), wt P A' w δ)
        ≤ ∑ δ ∈ (levelWords N).filter (Alive P A' w), wt P A' w δ := by
      rw [Finset.sum_filter (p := Alive P A' w),
        Finset.sum_filter (p := FirstCr P A' w), ← Finset.sum_add_distrib,
        sum_levelWords_succ]
      rw [Finset.sum_filter (p := Alive P A' w)]
      refine Finset.sum_le_sum fun γ _ => ?_
      by_cases hal : Alive P A' w γ
      · rw [ite_eq_left hal]
        exact child_sum2 P hP hn hbl0 hal
      · have hz (e : Bool) : (if Alive P A' w (γ ++ [e]) then wt P A' w (γ ++ [e]) else 0)
            + (if FirstCr P A' w (γ ++ [e]) then wt P A' w (γ ++ [e]) else 0) = 0 := by
          rw [ite_eq_right (fun h => hal (alive_take_of_alive_append P h)),
            ite_eq_right (fun h => hal (alive_take_of_firstCr_append P h)), add_zero]
        rw [ite_eq_right hal, hz true, hz false]
        simp
    rw [hsplit]
    linarith [hkey, ih]

/-! ## 6. From the frontier bound to the crossing mass -/

theorem pot_gt_thr_of_firstCr (P : IETDatum₂ α n) {A' : Finset α} {w δ : List Bool}
    (h : FirstCr P A' w δ) : thr P w < pot P (w ++ δ) A' := by
  obtain ⟨-, ⟨b, hb, hgt⟩, -⟩ := h
  exact lt_of_lt_of_le hgt (colSum_le_pot P (w ++ δ) hb)

/-- **The crossing words of level at most `N` carry `cond`-mass at most `pot/thr`.** -/
theorem sum_firstCr_le (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {A' : Finset α}
    {w : List Bool} (hbl0 : ¬ Blocked P w A') (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1),
        ∑ δ ∈ (levelWords m).filter (FirstCr P A' w), cond P w δ)
      ≤ pot P w A' / thr P w := by
  have hthr : 0 < thr P w := thr_pos P w
  have hterm (m) (_ : m ∈ Finset.range (N + 1)) : ∀ δ ∈ (levelWords m).filter
      (FirstCr P A' w),
      cond P w δ ≤ wt P A' w δ / thr P w := by
    intro δ hδ
    obtain ⟨-, hfc⟩ := Finset.mem_filter.mp hδ
    have hgt := pot_gt_thr_of_firstCr P hfc
    rw [wt, le_div_iff₀ hthr]
    exact mul_le_mul_of_nonneg_left hgt.le (cond_pos P w δ).le
  calc (∑ m ∈ Finset.range (N + 1),
        ∑ δ ∈ (levelWords m).filter (FirstCr P A' w), cond P w δ)
      ≤ ∑ m ∈ Finset.range (N + 1),
          ∑ δ ∈ (levelWords m).filter (FirstCr P A' w),
            wt P A' w δ / thr P w :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun δ hδ => hterm m hm δ hδ
    _ = (∑ m ∈ Finset.range (N + 1),
          ∑ δ ∈ (levelWords m).filter (FirstCr P A' w), wt P A' w δ)
          / thr P w := by
        simp only [Finset.sum_div]
    _ ≤ pot P w A' / thr P w := by
        refine div_le_div_of_nonneg_right ?_ hthr.le
        have h := frontier_bound P hP hn hbl0 N
        have hnn : 0 ≤ ∑ δ ∈ (levelWords N).filter (Alive P A' w), wt P A' w δ :=
          Finset.sum_nonneg fun δ _ =>
            mul_nonneg (cond_nonneg P w δ) (pot_nonneg P (w ++ δ) A')
        linarith

/-- **The first-crossing mass is at most `#A'/(2·#α)`**, with the constants evaluated. -/
theorem sum_firstCr_le_card (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {A' : Finset α}
    {w : List Bool} (hbl0 : ¬ Blocked P w A') (N : ℕ) (k : ℕ)
    (hcard : A'.card = k) :
    (∑ m ∈ Finset.range (N + 1),
        ∑ δ ∈ (levelWords m).filter (FirstCr P A' w), cond P w δ)
      ≤ (k : ℝ) / (2 * (Fintype.card α : ℝ)) := by
  refine le_trans (sum_firstCr_le P hP hn hbl0 N) ?_
  have hMx : 0 < Mx P w := Mx_pos P w
  have hd : (0 : ℝ) < (Fintype.card α : ℝ) := P.card_pos_cast
  have hden : (0 : ℝ) < 2 * (Fintype.card α : ℝ) * Mx P w := by positivity
  rw [thr, div_le_iff₀ hden]
  have hkm : (k / (2 * (Fintype.card α : ℝ)))
      * (2 * (Fintype.card α : ℝ) * Mx P w) = (k : ℝ) * Mx P w := by
    field_simp
  rw [hkm, ← hcard]
  exact pot_le_card_mul_Mx P w A'

/-! ## 7. Unclean stops are crossings: the cover -/

theorem getD_take_eq_of_lt {δ : List Bool} {g j : ℕ} (h : g < j) :
    (δ.take j).getD g false = δ.getD g false := by
  induction δ generalizing g j with
  | nil => simp
  | cons a t ih =>
    cases g with
    | zero =>
      cases j with
      | zero => omega
      | succ j' => simp
    | succ g' =>
      cases j with
      | zero => omega
      | succ j' => simpa [List.getD_cons_succ] using ih (g := g') (j := j') (by omega)

/-- **The first stop event of a bad word is unclean**: it occurs at a node where some `A'`-height
already exceeds the threshold. -/
theorem exists_bad_stop (P : IETDatum₂ α n) {A' : Finset α} {w δ : List Bool}
    (hbad : Bad P A' w δ) :
    ∃ j, j ≤ δ.length ∧ (∀ g < j, ¬ StopEv P A' w δ g) ∧
      ¬ Clean P A' w (δ.take j) := by
  have hex : ∃ g, g ∈ Finset.range (δ.length + 1) ∧ StopEv P A' w δ g := by
    by_contra h
    refine hbad (Or.inl ?_)
    intro g hg hge
    exact h ⟨g, hg, hge⟩
  obtain ⟨hfind, hfind2⟩ := Nat.find_spec hex
  have hjle : Nat.find hex ≤ δ.length := by
    rw [Finset.mem_range] at hfind
    omega
  refine ⟨Nat.find hex, hjle, ?_, ?_⟩
  · intro g hg hstop
    exact Nat.find_min hex hg ⟨by rw [Finset.mem_range]; omega, hstop⟩
  · intro hclean
    refine hbad (Or.inr ⟨Nat.find hex, ?_, ?_, ?_⟩)
    · rw [Finset.mem_range]; omega
    · intro g hg hstop
      rw [Finset.mem_range] at hg
      exact (Nat.find_min hex hg) ⟨by
        rw [Finset.mem_range]; omega, hstop⟩
    · rcases hfind2 with hH | ⟨hlt, hexit⟩
      · exact Or.inl ⟨hH, hclean⟩
      · exact Or.inr ⟨by omega, hexit, hclean⟩

/-- The family of first-crossing words of level at most `N`. -/
noncomputable def FC (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) (N : ℕ) :
    Finset (List Bool) :=
  (Finset.range (N + 1)).biUnion (fun m => (levelWords m).filter (FirstCr P A' w))

theorem mem_FC {P : IETDatum₂ α n} {A' : Finset α} {w : List Bool} {N : ℕ} {γ : List Bool} :
    γ ∈ FC P A' w N ↔ γ.length ≤ N ∧ FirstCr P A' w γ := by
  constructor
  · intro h
    rw [FC, Finset.mem_biUnion] at h
    obtain ⟨m, hm, hγ⟩ := h
    rw [Finset.mem_filter] at hγ
    rw [Finset.mem_range] at hm
    exact ⟨by rw [length_mem_levelWords hγ.1]; omega, hγ.2⟩
  · intro ⟨hlen, hfc⟩
    rw [FC, Finset.mem_biUnion]
    refine ⟨γ.length, by rw [Finset.mem_range]; omega, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨mem_levelWords_iff.mpr rfl, hfc⟩

/-- **A bad word extends a first crossing word.** -/
theorem bad_extends_firstCr (P : IETDatum₂ α n) {A' : Finset α} {w δ : List Bool} {N : ℕ}
    (hlev : δ ∈ levelWords N) (hbad : Bad P A' w δ) :
    ∃ γ ∈ FC P A' w N, γ <+: δ := by
  obtain ⟨j, hjle, hmin, hclean⟩ := exists_bad_stop P hbad
  have hlen : δ.length = N := length_mem_levelWords hlev
  have hnotclean : ∃ b ∈ A', thr P w < colSum P (w ++ δ.take j) b := by
    by_contra h
    exact hclean (fun b hb => by
      by_contra hlt
      exact h ⟨b, hb, not_le.mp hlt⟩)
  have hCr : Cr P A' w (δ.take j) := hnotclean
  have hnoCr (i) (hi : i < j) : ¬ Cr P A' w (δ.take i) := by
    intro hcr
    obtain ⟨b, hb, hgt⟩ := hcr
    have hH : Huge P w (δ.take i) :=
      lt_of_lt_of_le hgt (colSum_le_Mx P (w ++ δ.take i) b)
    exact hmin i hi (Or.inl hH)
  have hnoexit : NoExit P A' w (δ.take j) := by
    intro g hg
    rw [List.length_take] at hg
    have hgj : g < j := by omega
    intro hexit
    refine hmin g hgj (Or.inr ⟨?_, ?_⟩)
    · rw [hlen]; omega
    · rwa [List.take_take, Nat.min_eq_left (le_of_lt hgj), getD_take_eq_of_lt hgj] at hexit
  refine ⟨δ.take j, ?_, List.take_prefix j δ⟩
  rw [mem_FC]
  refine ⟨by rw [List.length_take]; omega, hnoexit, hCr, fun i hi => ?_⟩
  have hi' : i < j := by rw [List.length_take] at hi; omega
  rw [List.take_take, Nat.min_eq_left (le_of_lt hi')]
  exact hnoCr i hi'

theorem pairwiseDisjoint_firstCr (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) (N : ℕ) :
    (↑(Finset.range (N + 1)) : Set ℕ).PairwiseDisjoint
      (fun m => (levelWords m).filter (FirstCr P A' w)) := by
  intro m _ m' _ hne
  refine Finset.disjoint_left.mpr fun x hx hx' => ?_
  rw [Finset.mem_filter] at hx hx'
  have h1 : x.length = m := length_mem_levelWords hx.1
  have h2 : x.length = m' := length_mem_levelWords hx'.1
  exact hne (by omega)

theorem sum_FC_eq (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) (N : ℕ) :
    ∑ γ ∈ FC P A' w N, cond P w γ
      = ∑ m ∈ Finset.range (N + 1),
          ∑ γ ∈ (levelWords m).filter (FirstCr P A' w), cond P w γ := by
  rw [FC, Finset.sum_biUnion (pairwiseDisjoint_firstCr P A' w N)]

/-- **The unclean mass at a non-blocked node is at most `#A'/(2·#α)`.** -/
theorem bad_mass_le (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {A' : Finset α}
    {w : List Bool} (hbl0 : ¬ Blocked P w A') (N k : ℕ)
    (hcard : A'.card = k) :
    ∑ δ ∈ (levelWords N).filter (fun δ => Bad P A' w δ),
        cond P w δ
      ≤ (k : ℝ) / (2 * (Fintype.card α : ℝ)) := by
  set S : Finset (List Bool) :=
    (levelWords N).filter (fun δ => Bad P A' w δ) with hS
  have hSpf : PrefixFree S := by
    refine prefixFree_of_length (N := N) ?_
    intro δ hδ
    rw [hS, Finset.mem_filter] at hδ
    exact length_mem_levelWords hδ.1
  have hcov (δ) (hδ : δ ∈ S) : ∃ γ ∈ FC P A' w N, γ <+: δ := by
    rw [hS, Finset.mem_filter] at hδ
    exact bad_extends_firstCr P hδ.1 hδ.2
  calc ∑ δ ∈ S, cond P w δ
      ≤ ∑ γ ∈ FC P A' w N, cond P w γ :=
        sum_cond_le_sum_of_covers P hP hn w hSpf hcov
    _ = ∑ m ∈ Finset.range (N + 1),
          ∑ γ ∈ (levelWords m).filter (FirstCr P A' w), cond P w γ :=
        sum_FC_eq P A' w N
    _ ≤ (k : ℝ) / (2 * (Fintype.card α : ℝ)) :=
        sum_firstCr_le_card P hP hn hbl0 N k hcard

/-! ## 8. The good (clean-stop) mass, and the `Γ₃` estimate -/

omit [DecidableEq α] in
/-- The node hypothesis `∃ e, last e ∉ A'` forbids a blocked node. -/
theorem not_blocked_of_exists_outside (P : IETDatum₂ α n) {A' : Finset α} {w : List Bool}
    (h : ∃ e : Bool, (P.vertex w).last e ∉ A') :
    ¬ Blocked P w A' := by
  intro hb
  obtain ⟨e, he⟩ := h
  simp only [Blocked] at hb
  cases e with
  | false => exact he hb.2
  | true => exact he hb.1

/-- **The clean-stop words carry more than half of the mass** at a node with a row end outside `A'`.
-/
theorem good_mass_gt_half (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {A' : Finset α}
    {w : List Bool} (hbl0 : ¬ Blocked P w A') (N k : ℕ)
    (hcard : A'.card = k) (hk : k < Fintype.card α) :
    (1 / 2 : ℝ) <
      ∑ δ ∈ (levelWords N).filter (fun δ => ¬ Bad P A' w δ),
        cond P w δ := by
  have hsplit : (∑ δ ∈ levelWords N, cond P w δ)
      = (∑ δ ∈ (levelWords N).filter (fun δ => Bad P A' w δ),
          cond P w δ)
        + (∑ δ ∈ (levelWords N).filter (fun δ => ¬ Bad P A' w δ),
            cond P w δ) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hall := sum_cond_levelWords P hP hn w N
  have hbad := bad_mass_le P hP hn hbl0 N k hcard
  have hd : (0 : ℝ) < (Fintype.card α : ℝ) := P.card_pos_cast
  have hkk : (k : ℝ) / (2 * (Fintype.card α : ℝ)) < 1 / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    have h1 : (k : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hk
    nlinarith
  linarith

/-- **The `Γ₃` mass estimate from a clean-stop mass bound at the straddling nodes.**  This is the
`Γ₃` estimate of AGY, in the form the `k → k+1` step consumes: at every `Cb`-balanced
straddling node `w` and every nonempty `A'` of `k` letters, there is a prefix-free family of
continuations of mass `> 1/2` whose members end in an exit arrow — or after the maximum has crossed
`2·d·𝔐(q_w)` — with all `A'`-heights at the end at most `2·d·𝔐(q_w)`.  The hypothesis is that mass
bound at the nodes where the node hypothesis `∃ e, last e ∉ A'` holds (it fails at the blocked
nodes). -/
theorem straddleMassCard_of_goodMass_straddle (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {k : ℕ}
    (hgood : ∀ (w : List Bool) (A' : Finset α), A'.card = k → k < Fintype.card α →
      A'.Nonempty → (∃ e : Bool, (P.vertex w).last e ∉ A') →
      ∃ N : ℕ, (∀ δ : List Bool, δ.length = N →
          ∃ i ∈ Finset.range (δ.length + 1), Huge P w (δ.take i)) ∧
        1 / 2 < ∑ δ ∈ (levelWords N).filter
          (fun δ => ¬ Bad P A' w δ), cond P w δ)
    (Cb : ℝ) (_ : 1 ≤ Cb) (A' : Finset α) (w : List Bool)
    (hcard : A'.card = k) (hklt : k < Fintype.card α) (hne : A'.Nonempty)
    (_ : ∀ b ∈ A', (1 / Cb) * mkMass 1 (colSum P w) ≤ colSum P w b)
    (hex : ∃ e : Bool, (P.vertex w).last e ∉ A') :
    ∃ T : Finset (List Bool), PrefixFree T ∧
      1 / 2 < ∑ η ∈ T, cond P w η ∧
      ∀ η ∈ T, ∃ (ν : List Bool) (e : Bool), η = ν ++ [e] ∧
        (((P.vertex (w ++ ν)).last e ∈ A' ∧ (P.vertex (w ++ ν)).last (!e) ∉ A')
          ∨ 2 * (Fintype.card α : ℝ) * mkMass 1 (colSum P w)
              < mkMass 1 (colSum P (w ++ η))) ∧
        (∀ b ∈ A', colSum P (w ++ η) b
          ≤ 2 * (Fintype.card α : ℝ) * mkMass 1 (colSum P w)) := by
  have hα : Nonempty α := Fintype.card_pos_iff.mp (by
    have := P.card_pos
    omega)
  obtain ⟨N, hN, hmass⟩ := hgood w A' hcard hklt hne hex
  set G : Finset (List Bool) :=
    (levelWords N).filter (fun δ => ¬ Bad P A' w δ) with hG
  have hGpf : PrefixFree G := by
    refine prefixFree_of_length (N := N) ?_
    intro δ hδ
    rw [hG, Finset.mem_filter] at hδ
    exact length_mem_levelWords hδ.1
  have hcov (δ) (hδ : δ ∈ G) : ∃ η ∈ StopFam P A' w N, η <+: δ := by
    rw [hG, Finset.mem_filter] at hδ
    have hlen : δ.length = N := length_mem_levelWords hδ.1
    have hstop : ∃ g ∈ Finset.range (δ.length + 1), StopEv P A' w δ g := by
      obtain ⟨i, hi, hH⟩ := hN δ hlen
      exact ⟨i, hi, Or.inl hH⟩
    exact exists_stopfam_of_good P hP hn w A' N hlen
      (goodFirst_of_good (by by_contra hg; exact hδ.2 hg) hstop)
  have hmassle : ∑ δ ∈ G, cond P w δ ≤
      ∑ η ∈ StopFam P A' w N, cond P w η :=
    sum_cond_le_sum_of_covers P hP hn w hGpf hcov
  refine ⟨StopFam P A' w N, prefixFree_stopFam P A' w N, ?_, ?_⟩
  · linarith
  · intro η hη
    obtain ⟨hW, hAb, -, -⟩ := mem_stopFam hη
    have hbnd (b) (hb : b ∈ A') :
        colSum P (w ++ η) b ≤
          2 * (Fintype.card α : ℝ) * mkMass 1 (colSum P w) := by
      have h1 := hAb η.length (by rw [Finset.mem_range]; omega) b hb
      rw [List.take_length] at h1
      simpa [thr, Mx] using h1
    rcases hW with ⟨e, heq, hEA⟩ | hH
    · exact ⟨η.dropLast, e, heq, Or.inl ⟨hEA.1, hEA.2⟩, hbnd⟩
    · have hpos : 0 < η.length := by
        rcases Nat.eq_zero_or_pos η.length with h0 | h1
        · exfalso
          have hnil : η = [] := List.eq_nil_of_length_eq_zero h0
          exact not_huge_nil P w (hnil ▸ hH)
        · exact h1
      have hne : η ≠ [] := List.ne_nil_of_length_pos hpos
      exact ⟨η.dropLast, η.getLast hne, (List.dropLast_append_getLast hne).symm,
        Or.inr (by simpa [Huge, thr, Mx] using hH), hbnd⟩

/-- **The `Γ₃` mass estimate, unconditionally, for every `k`** — the last step towards richness of
the greedy path. -/
theorem straddleMassCard_of_unclean (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (k : ℕ) (Cb : ℝ) (_hCb : 1 ≤ Cb) (A' : Finset α) (w : List Bool)
    (hcard : A'.card = k) (hklt : k < Fintype.card α) (hne : A'.Nonempty)
    (_hbal : ∀ b ∈ A', (1 / Cb) * mkMass 1 (colSum P w) ≤ colSum P w b)
    (hex : ∃ e : Bool, (P.vertex w).last e ∉ A') :
    ∃ T : Finset (List Bool), PrefixFree T ∧
      1 / 2 < ∑ η ∈ T, cond P w η ∧
      ∀ η ∈ T, ∃ (ν : List Bool) (e : Bool), η = ν ++ [e] ∧
        (((P.vertex (w ++ ν)).last e ∈ A' ∧ (P.vertex (w ++ ν)).last (!e) ∉ A')
          ∨ 2 * (Fintype.card α : ℝ) * mkMass 1 (colSum P w)
              < mkMass 1 (colSum P (w ++ η))) ∧
        (∀ b ∈ A', colSum P (w ++ η) b
          ≤ 2 * (Fintype.card α : ℝ) * mkMass 1 (colSum P w)) := by
  refine straddleMassCard_of_goodMass_straddle P hP hn (k := k) ?_
    Cb _hCb A' w hcard hklt hne _hbal hex
  intro w A' hcard hklt hne hex
  have hα : Nonempty α := Fintype.card_pos_iff.mp (by
    have := P.card_pos
    omega)
  obtain ⟨N, hN⟩ := exists_stop_length P hP hn w
  exact ⟨N, hN, good_mass_gt_half P hP hn (not_blocked_of_exists_outside P hex) N k hcard hklt⟩

end IntervalExchange.RauzyVeech.RichPath

end
