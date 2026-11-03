/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.RauzyVeech.RichPath.LargeLetter

/-!
# The `Γ₃` bookkeeping: level words, thresholds, stop events, and the minimal stopping family

The vocabulary that the `Γ₃` argument of `IETFree.Potential` runs on (`NodeHeight.st = cs` is
`B_w·1`, `NodeHeight.Mk 1` is the maximum `𝔐 = 𝔐(q_w)`):

* §1 the level-`N` words: `levelWords` is the set of words of length `N` (`mem_levelWords_iff`,
  `pairwiseDisjoint_levelWords`, `prefixFree_of_length`), and the conditional masses of its members
  add up to `1` (`sum_cond_levelWords`);
* §2 the threshold `thr = 2·d·𝔐` (`Mx`, `thr`, `qmin`, with `Mx_pos`, `Mx_lt_thr`, `st_le_thr`), the
  predicate `Huge` (the maximum has crossed at some prefix, `not_huge_nil`), and the explicit
  stopping length `exists_stop_length`: every word of length `⌈2d²M/min⌉ + 1` is huge;
* §3 the sum of the `A'`-heights along a continuation: `sum_st_append_singleton` (one step),
  `sum_st_ge` (growth) and `sum_st_le` (boundedness by `Mx`), hence `length_le_of_not_huge`;
* §4 exit arrows `ExitArrow`, stop events `StopEv`, the cleanness predicate `Clean`, the good/bad
  predicates `GoodFirst`, `Good`, `Bad` with their `Decidable` instances, and the minimal stopping
  family `StopW`, `StopFam` (`prefixFree_stopFam`, `st_eq_of_exitArrow`).

-/


open MeasureTheory IETDatum₂ Finset NodeHeight
open scoped BigOperators


/-! ## Three conventions in the definitions, and why

* **The empty word has no stop event**, so `Good` (a *first* stop which is clean) cannot be the
  whole story: `Good` carries the extra alternative "no stop yet", i.e. `Good = (no stop yet) ∨
  GoodFirst`, and a word on which the threshold has not been crossed and no exit arrow has been read
  is good.
* **`StopEv` is guarded on the index**: its exit clause reads `δ.getD j false`, which at
  `j = δ.length` is the default `false`; the guard `j < δ.length` is part of the definition.
* **`A'` is a nonempty proper subset of the alphabet** wherever a stopping family is used: with
  `A' = univ` there is no exit arrow and no clean crossing, so every word would be bad.
-/

namespace Stopping

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. The level-`N` cylinders -/

/-- The words of length `N`. -/
def levelWords : ℕ → Finset (List Bool)
  | 0 => {[]}
  | (N + 1) => (levelWords N).biUnion fun γ =>
      ({γ ++ [true], γ ++ [false]} : Finset (List Bool))

theorem length_of_mem_levelWords :
    ∀ {N : ℕ} {δ : List Bool}, δ ∈ levelWords N → δ.length = N := by
  intro N
  induction N with
  | zero =>
    intro δ h
    simp only [levelWords, Finset.mem_singleton] at h
    subst h
    rfl
  | succ N ih =>
    intro δ h
    simp only [levelWords, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at h
    obtain ⟨γ, hγ, rfl | rfl⟩ := h <;> simp [ih hγ]

theorem mem_levelWords_of_length :
    ∀ {N : ℕ} {δ : List Bool}, δ.length = N → δ ∈ levelWords N := by
  intro N
  induction N with
  | zero =>
    intro δ h
    have hnil : δ = [] := List.eq_nil_of_length_eq_zero h
    subst hnil
    exact Finset.mem_singleton_self []
  | succ N ih =>
    intro δ h
    rcases List.eq_nil_or_concat δ with rfl | ⟨L, b, rfl⟩
    · simp at h
    · simp only [levelWords, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
      rcases b with _ | _ <;> refine ⟨L, ih (by simpa using h), ?_⟩ <;> simp

theorem mem_levelWords_iff {N : ℕ} {δ : List Bool} : δ ∈ levelWords N ↔ δ.length = N :=
  ⟨length_of_mem_levelWords, mem_levelWords_of_length⟩

theorem eq_of_append_singleton_eq {γ γ' : List Bool} {e e' : Bool}
    (hlen : γ.length = γ'.length) (h : γ ++ [e] = γ' ++ [e']) : γ = γ' := by
  have h1 : (γ ++ [e]).take γ.length = γ := List.take_left
  have h2 : (γ' ++ [e']).take γ.length = γ' := by
    rw [hlen]
    exact List.take_left
  rw [h, h2] at h1
  exact h1.symm

theorem pairwiseDisjoint_levelWords (N : ℕ) :
    (↑(levelWords N) : Set (List Bool)).PairwiseDisjoint
      (fun γ => ({γ ++ [true], γ ++ [false]} : Finset (List Bool))) := by
  intro γ hγ γ' hγ' hne
  refine Finset.disjoint_left.mpr ?_
  intro x hx hx'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
  have hlen : γ.length = γ'.length := by
    rw [length_of_mem_levelWords hγ, length_of_mem_levelWords hγ']
  rcases hx with rfl | rfl <;> rcases hx' with h | h
  · exact hne (eq_of_append_singleton_eq hlen h)
  · have hg : γ = γ' := eq_of_append_singleton_eq hlen h
    rw [hg] at h
    exact absurd h (by simp)
  · have hg : γ = γ' := eq_of_append_singleton_eq hlen h
    rw [hg] at h
    exact absurd h (by simp)
  · exact hne (eq_of_append_singleton_eq hlen h)

/-- **The masses of the level-`N` cylinders sum to `1`.** -/
theorem sum_cond_levelWords (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) : ∀ N : ℕ, ∑ δ ∈ levelWords N, CylinderMass.cond P w δ = 1 := by
  intro N
  induction N with
  | zero => simp [levelWords]
  | succ N ih =>
    have hdisj := pairwiseDisjoint_levelWords N
    rw [levelWords, Finset.sum_biUnion hdisj]
    have hstep : ∀ γ ∈ levelWords N,
        ∑ e ∈ ({γ ++ [true], γ ++ [false]} : Finset (List Bool)), CylinderMass.cond P w e
          = CylinderMass.cond P w γ := by
      intro γ _
      rw [Finset.sum_pair (by simp)]
      rw [CylinderMass.cond_append, CylinderMass.cond_append,
        ← mul_add, NodeHeight.cond_arrow_sum P hP hn (w ++ γ)]
      ring
    rw [Finset.sum_congr rfl hstep, ih]

/-- Words of the same length form a prefix-free family. -/
theorem prefixFree_of_length {N : ℕ} {G : Finset (List Bool)}
    (hG : ∀ δ ∈ G, δ.length = N) : NodeHeight.PrefixFree G := by
  intro u hu v hv hpre
  have hlen : u.length = v.length := by rw [hG u hu, hG v hv]
  have huv : u = v := List.IsPrefix.eq_of_length hpre hlen
  subst huv
  exact List.prefix_rfl

/-! ## 2. The threshold, the minimum height, and the stopping rule -/

omit [DecidableEq α] [NeZero n] in
theorem card_eq_n (P : IETDatum₂ α n) : Fintype.card α = n :=
  (Fintype.card_congr P.piTop).trans (Fintype.card_fin n)

omit [DecidableEq α] in
theorem card_ge_one (P : IETDatum₂ α n) : 1 ≤ Fintype.card α := by
  rw [card_eq_n P]
  exact Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)

omit [DecidableEq α] in
theorem card_ge_oneR (P : IETDatum₂ α n) : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by
  have := card_ge_one P
  exact_mod_cast this

omit [DecidableEq α] [NeZero n] in
theorem card_ge_two (P : IETDatum₂ α n) (hn : 2 ≤ n) : 2 ≤ Fintype.card α := by
  rw [card_eq_n P]; exact hn

/-- The maximum of the state at the node `w`. -/
noncomputable def Mx (P : IETDatum₂ α n) (w : List Bool) : ℝ := NodeHeight.Mk 1 (NodeHeight.st P w)

/-- The threshold `2·#α·M(q_w)` of the dichotomy. -/
noncomputable def thr (P : IETDatum₂ α n) (w : List Bool) : ℝ :=
  2 * (Fintype.card α : ℝ) * Mx P w

/-- The minimal height of the state at the node `w`, as `Mk #α`. -/
noncomputable def qmin (P : IETDatum₂ α n) (w : List Bool) : ℝ :=
  NodeHeight.Mk (Fintype.card α) (NodeHeight.st P w)

omit [DecidableEq α] in
/-- `Mk #α` is the minimum over the alphabet. -/
theorem Mk_card_eq_mmin (q : α → ℝ) :
    NodeHeight.Mk (Fintype.card α) q = NodeHeight.mmin Finset.univ q := by
  have hne : ((Finset.univ : Finset α).powersetCard (Fintype.card α)).Nonempty :=
    ⟨Finset.univ, by simp⟩
  refine le_antisymm ?_ (NodeHeight.mmin_le_Mk (s := Finset.univ) (k := Fintype.card α)
    Finset.card_univ)
  rw [NodeHeight.Mk_eq hne, Finset.sup'_le_iff]
  intro s hs
  have hsu : s = Finset.univ :=
    Finset.eq_univ_of_card s (by rw [(Finset.mem_powersetCard.mp hs).2])
  rw [hsu]

theorem qmin_le (P : IETDatum₂ α n) (w : List Bool) (b : α) :
    qmin P w ≤ NodeHeight.st P w b := by
  rw [qmin, Mk_card_eq_mmin]
  exact NodeHeight.mmin_le (Finset.mem_univ b)

theorem qmin_pos [Nonempty α] (P : IETDatum₂ α n) (w : List Bool) : 0 < qmin P w := by
  rw [qmin, Mk_card_eq_mmin]
  exact NodeHeight.mmin_pos (Finset.univ_nonempty) (fun b => NodeHeight.st_pos P w b)

omit [Fintype α] [DecidableEq α] in
/-- `mmin` is monotone in the state. -/
theorem mmin_le_mmin {q q' : α → ℝ} (h : ∀ b, q b ≤ q' b) (s : Finset α)
    (hs : s.Nonempty) :
    NodeHeight.mmin s q ≤ NodeHeight.mmin s q' := by
  obtain ⟨b, hb, hbe⟩ := Finset.exists_mem_eq_inf' hs q'
  have h2 : NodeHeight.mmin s q' = q' b := (NodeHeight.mmin_eq hs q').trans hbe
  rw [h2]
  exact (NodeHeight.mmin_le hb).trans (h b)

/-- The minimal height only grows. -/
theorem qmin_mono [Nonempty α] (P : IETDatum₂ α n) (w δ : List Bool) :
    qmin P w ≤ qmin P (w ++ δ) := by
  rw [qmin, qmin, Mk_card_eq_mmin, Mk_card_eq_mmin]
  refine mmin_le_mmin (fun b => ?_) Finset.univ Finset.univ_nonempty
  exact CylinderMass.state_mono P w δ b

theorem Mx_pos (P : IETDatum₂ α n) (w : List Bool) : 0 < Mx P w :=
  NodeHeight.Mk_st_pos (k := 1) P w le_rfl (card_ge_one P)

/-- `Mx` dominates every height. -/
theorem st_le_Mx (P : IETDatum₂ α n) (w : List Bool) (b : α) : NodeHeight.st P w b ≤ Mx P w :=
  (LargeLetter.Mk_one_le_iff (card_ge_one P) (q := NodeHeight.st P w)
    (R := Mx P w)).mp le_rfl b

/-- The threshold dominates every height. -/
theorem st_le_thr (P : IETDatum₂ α n) (w : List Bool) (b : α) :
    NodeHeight.st P w b ≤ thr P w := by
  have h1 := st_le_Mx P w b
  have h2 := Mx_pos P w
  have h3 := card_ge_oneR P
  rw [thr]
  nlinarith [h1, h2, h3]

/-- The maximum is below the threshold. -/
theorem Mx_lt_thr (P : IETDatum₂ α n) (w : List Bool) : Mx P w < thr P w := by
  have h1 := Mx_pos P w
  have h2 := card_ge_oneR P
  rw [thr]
  nlinarith

/-- The maximum at the node `w ++ μ` exceeds the threshold. -/
noncomputable def Huge (P : IETDatum₂ α n) (w μ : List Bool) : Prop :=
  thr P w < Mx P (w ++ μ)

/-- The root is not a crossing. -/
theorem not_huge_nil (P : IETDatum₂ α n) (w : List Bool) : ¬ Huge P w [] := by
  rw [Huge, List.append_nil]
  exact not_lt.mpr (le_of_lt (Mx_lt_thr P w))

/-- The `A'`-heights stay below the threshold along `μ`. -/
def ABound (P : IETDatum₂ α n) (A' : Finset α) (w μ : List Bool) : Prop :=
  ∀ i ∈ Finset.range (μ.length + 1), ∀ b ∈ A', NodeHeight.st P (w ++ μ.take i) b ≤ thr P w

/-! ## 3. The sum of the heights along a continuation -/

/-- The sum of the heights after one more letter: the loser grows by the winner. -/
theorem sum_st_append_singleton (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (v : List Bool) (e : Bool) :
    ∑ b, NodeHeight.st P (v ++ [e]) b
      = ∑ b, NodeHeight.st P v b + NodeHeight.st P v ((IETDatum₂.vertex P v).last e) := by
  have hterm : ∀ b, NodeHeight.st P (v ++ [e]) b
      = NodeHeight.st P v b + (if b = (IETDatum₂.vertex P v).last (!e)
          then NodeHeight.st P v ((IETDatum₂.vertex P v).last e) else 0) := by
    intro b
    have h := CylinderMass.cs_append_singleton P hP hn v e b
    simpa [NodeHeight.st] using h
  calc ∑ b, NodeHeight.st P (v ++ [e]) b
      = ∑ b, (NodeHeight.st P v b + (if b = (IETDatum₂.vertex P v).last (!e)
          then NodeHeight.st P v ((IETDatum₂.vertex P v).last e) else 0)) :=
        Finset.sum_congr rfl fun b _ => hterm b
    _ = ∑ b, NodeHeight.st P v b + ∑ b, (if b = (IETDatum₂.vertex P v).last (!e)
          then NodeHeight.st P v ((IETDatum₂.vertex P v).last e) else 0) := Finset.sum_add_distrib
    _ = ∑ b, NodeHeight.st P v b + NodeHeight.st P v ((IETDatum₂.vertex P v).last e) := by
        rw [Finset.sum_ite_eq']
        simp

/-- **The total height grows at least by the minimal initial height at each step.** -/
theorem sum_st_ge [Nonempty α] (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) :
    ∀ μ : List Bool, ∑ b, NodeHeight.st P w b + μ.length * qmin P w
      ≤ ∑ b, NodeHeight.st P (w ++ μ) b := by
  intro μ
  induction μ generalizing w with
  | nil => simp
  | cons e μ ih =>
    have h3 := sum_st_append_singleton P hP hn w e
    have h4 : qmin P w ≤ NodeHeight.st P w ((IETDatum₂.vertex P w).last e) := qmin_le P w _
    have h2 := ih (w ++ [e])
    have hmono : qmin P w ≤ qmin P (w ++ [e]) := qmin_mono P w [e]
    have hmlen : (0 : ℝ) ≤ (μ.length : ℝ) := Nat.cast_nonneg _
    have heq : w ++ (e :: μ) = (w ++ [e]) ++ μ := by rw [List.append_assoc]; rfl
    have hlen : ((e :: μ).length : ℝ) = (μ.length : ℝ) + 1 := by simp
    have hq : (0 : ℝ) < qmin P w := qmin_pos P w
    rw [heq, hlen]
    nlinarith [h2, h3, h4, hq, hmono, hmlen]

/-- The sum of the heights is at most `#α` times the maximum. -/
theorem sum_st_le (P : IETDatum₂ α n) (v : List Bool) {R : ℝ} (hR : Mx P v ≤ R) :
    ∑ b, NodeHeight.st P v b ≤ (Fintype.card α : ℝ) * R := by
  have hb : ∀ b, NodeHeight.st P v b ≤ R := fun b =>
    (st_le_Mx P v b).trans hR
  calc ∑ b, NodeHeight.st P v b ≤ ∑ _b : α, R := Finset.sum_le_sum fun b _ => hb b
    _ = (Fintype.card α : ℝ) * R := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **A word along which the maximum has not crossed the threshold is short.** -/
theorem length_le_of_not_huge [Nonempty α] (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w δ : List Bool) (hδ : ¬ Huge P w δ) :
    (δ.length : ℝ) * qmin P w ≤ (Fintype.card α : ℝ) * thr P w := by
  have h1 := sum_st_ge P hP hn w δ
  have h2 := sum_st_le P (w ++ δ) (show Mx P (w ++ δ) ≤ thr P w from not_lt.mp hδ)
  have h3 : (0 : ℝ) ≤ ∑ b, NodeHeight.st P w b :=
    Finset.sum_nonneg fun b _ => NodeHeight.st_nonneg P w b
  linarith [h1, h2, h3]

/-- **The stopping length**: at this length, every word has already crossed the threshold. -/
theorem exists_stop_length [Nonempty α] (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) :
    ∃ N : ℕ, ∀ δ : List Bool, δ.length = N →
      ∃ i ∈ Finset.range (δ.length + 1), Huge P w (δ.take i) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((Fintype.card α : ℝ) * thr P w / qmin P w)
  refine ⟨N, fun δ hδ => ?_⟩
  by_contra hcon
  push Not at hcon
  have hmem : δ.length ∈ Finset.range (δ.length + 1) := by simp
  have hnh : ¬ Huge P w (δ.take δ.length) := hcon δ.length hmem
  rw [List.take_length] at hnh
  have h2 := length_le_of_not_huge P hP hn w δ hnh
  have hq := qmin_pos P w
  have h3 : (δ.length : ℝ) ≤ (Fintype.card α : ℝ) * thr P w / qmin P w := by
    rw [le_div_iff₀ hq]
    linarith
  rw [hδ] at h3
  linarith

/-! ## 4. Exit arrows, stop events, and the minimal stopping family -/

/-- `e` is an **exit arrow** at the node `μ` (read from `w`): its winner is in `A'`, its
loser is not. -/
def ExitArrow (P : IETDatum₂ α n) (A' : Finset α) (w μ : List Bool) (e : Bool) : Prop :=
  (IETDatum₂.vertex P (w ++ μ)).last e ∈ A' ∧
    (IETDatum₂.vertex P (w ++ μ)).last (!e) ∉ A'

/-- A **stop event** at index `j` of the word `δ`: either the maximum has crossed the threshold at
`δ.take j`, or the letter `j` of `δ` is an exit arrow at the node `δ.take j`. -/
noncomputable def StopEv (P : IETDatum₂ α n) (A' : Finset α) (w δ : List Bool) (j : ℕ) : Prop :=
  Huge P w (δ.take j) ∨ (j < δ.length ∧ ExitArrow P A' w (δ.take j) (δ.getD j false))

/-- The `A'`-heights are below the threshold at the node `μ`. -/
def Clean (P : IETDatum₂ α n) (A' : Finset α) (w μ : List Bool) : Prop :=
  ∀ b ∈ A', NodeHeight.st P (w ++ μ) b ≤ thr P w

/-- **A clean stop for `δ`**: at the first stop event the `A'`-heights are still below the threshold
(so the corresponding word of `StopFam` keeps the `A'`-bound and is usable). Only meaningful when
`δ` *has* a stop event: on the empty word it is false, which is why `Good` adds a "no stop yet"
alternative. -/
noncomputable def GoodFirst (P : IETDatum₂ α n) (A' : Finset α) (w δ : List Bool) : Prop :=
  ∃ j ∈ Finset.range (δ.length + 1), (∀ g ∈ Finset.range j, ¬ StopEv P A' w δ g) ∧
    ((Huge P w (δ.take j) ∧ Clean P A' w (δ.take j)) ∨
      (j + 1 ≤ δ.length ∧ ExitArrow P A' w (δ.take j) (δ.getD j false) ∧
        Clean P A' w (δ.take j)))

/-- **The good words**: no stop event at all within the word (no `δ.take j` crosses the threshold
and no read letter is an exit arrow), or a first stop event which is clean. The first alternative is
not redundant: `GoodFirst` is false on the empty word, so without it every word would be bad at
level `N = 0`. -/
noncomputable def Good (P : IETDatum₂ α n) (A' : Finset α) (w δ : List Bool) : Prop :=
  (∀ g ∈ Finset.range (δ.length + 1), ¬ StopEv P A' w δ g) ∨ GoodFirst P A' w δ

/-- **The bad words**: a stop event has been read and the first one is not clean.  This is the
family whose mass the race estimate bounds. -/
noncomputable def Bad (P : IETDatum₂ α n) (A' : Finset α) (w δ : List Bool) : Prop :=
  ¬ Good P A' w δ

noncomputable instance stopEvDecidable (P : IETDatum₂ α n) (A' : Finset α) (w δ : List Bool) :
    DecidablePred (StopEv P A' w δ) := fun _ => Classical.propDecidable _

noncomputable instance goodDecidable (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) :
    DecidablePred (Good P A' w) := fun _ => Classical.propDecidable _

noncomputable instance badDecidable (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) :
    DecidablePred (Bad P A' w) := fun _ => Classical.propDecidable _

/-- The stop *words*: `η` ends with an exit arrow at its parent node, or the maximum has already
crossed the threshold at `η`. -/
noncomputable def StopW (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool)
    (η : List Bool) : Prop :=
  (∃ e : Bool, η = η.dropLast ++ [e] ∧ ExitArrow P A' w η.dropLast e) ∨ Huge P w η

/-- The predicate defining the minimal stopping family. -/
noncomputable def stopPred (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool)
    (η : List Bool) : Prop :=
  StopW P A' w η ∧ ABound P A' w η ∧
    ∀ j ∈ Finset.range η.length, ¬ StopW P A' w (η.take j)

noncomputable instance stopPredDecidable (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) :
    DecidablePred (stopPred P A' w) := fun _ => Classical.propDecidable _

/-- **The minimal stopping family**: the words of length `≤ N` which are a stop word and such that
no shorter stop word is a prefix, with the `A'`-heights below the threshold throughout. -/
noncomputable def StopFam (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) (N : ℕ) :
    Finset (List Bool) :=
  (Finset.range (N + 1)).biUnion (fun m => (levelWords m).filter (stopPred P A' w))

theorem mem_stopFam {P : IETDatum₂ α n} {A' : Finset α} {w : List Bool} {N : ℕ}
    {η : List Bool} (h : η ∈ StopFam P A' w N) :
    StopW P A' w η ∧ ABound P A' w η ∧ η.length ≤ N ∧
      (∀ j ∈ Finset.range η.length, ¬ StopW P A' w (η.take j)) := by
  rw [StopFam, Finset.mem_biUnion] at h
  obtain ⟨m, hm, hμ⟩ := h
  rw [Finset.mem_filter] at hμ
  obtain ⟨hlev, hW, hA, hmin⟩ := hμ
  rw [Finset.mem_range] at hm
  refine ⟨hW, hA, ?_, hmin⟩
  rw [length_of_mem_levelWords hlev]
  omega

/-- The minimal stopping family is prefix-free. -/
theorem prefixFree_stopFam (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) (N : ℕ) :
    NodeHeight.PrefixFree (StopFam P A' w N) := by
  intro u hu v hv hpre
  obtain ⟨huW, -, -, humin⟩ := mem_stopFam hu
  obtain ⟨-, -, -, hvmin⟩ := mem_stopFam hv
  obtain ⟨t, rfl⟩ := hpre
  rcases lt_or_ge u.length (u ++ t).length with hlt | hge
  · exfalso
    have hj : u.length ∈ Finset.range ((u ++ t).length) := by
      rw [Finset.mem_range]; exact hlt
    have h := hvmin u.length hj
    have h2 : (u ++ t).take u.length = u := by
      rw [List.take_append_of_le_length le_rfl]
      exact List.take_length
    rw [h2] at h
    exact h huW
  · have ht : t = [] := by
      rw [List.length_append] at hge
      exact List.eq_nil_of_length_eq_zero (by omega)
    rw [ht, List.append_nil]

/-- A word of length `n + 1` is its prefix of length `n` followed by its `n`-th letter. -/
theorem take_succ_getD (l : List Bool) {n : ℕ} (h : n < l.length) :
    l.take (n + 1) = l.take n ++ [l.getD n false] := by
  rw [List.take_add_one]
  have hsome : l[n]? = some (l.getD n false) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rfl
  rw [hsome]
  rfl

/-- **The `A'`-heights do not move across an exit arrow.** -/
theorem st_eq_of_exitArrow (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {A' : Finset α} {w μ : List Bool} {e : Bool}
    (hE : ExitArrow P A' w μ e) {b : α} (hb : b ∈ A') :
    NodeHeight.st P (w ++ μ ++ [e]) b = NodeHeight.st P (w ++ μ) b := by
  obtain ⟨-, hlose⟩ := hE
  have h := CylinderMass.cs_append_singleton P hP hn (w ++ μ) e b
  have hne : b ≠ (IETDatum₂.vertex P (w ++ μ)).last (!e) := fun hb' => hlose (hb' ▸ hb)
  simp only [NodeHeight.st]
  rw [h, if_neg hne, add_zero]

omit [DecidableEq α] in
/-- The exit part of `StopW`, read back on a `take` of a long word: the exit arrow is the letter
that the word actually took. -/
theorem exitArrow_of_stopW_take {P : IETDatum₂ α n} {A' : Finset α} {w : List Bool}
    {δ : List Bool} {g : ℕ} {e : Bool} (hg : g < δ.length) (hne : 1 ≤ g)
    (heq : δ.take g = (δ.take g).dropLast ++ [e])
    (hEA : ExitArrow P A' w (δ.take g).dropLast e) :
    ExitArrow P A' w (δ.take (g - 1)) (δ.getD (g - 1) false) := by
  have hgl : g - 1 < δ.length := by omega
  have h1 : δ.take g = δ.take (g - 1) ++ [δ.getD (g - 1) false] := by
    rw [show g = g - 1 + 1 by omega]
    exact take_succ_getD δ hgl
  have h2 : (δ.take g).dropLast = δ.take (g - 1) := by
    rw [h1, List.dropLast_concat]
  have h5 : (δ.take g).dropLast ++ [e] = δ.take (g - 1) ++ [δ.getD (g - 1) false] := by
    rw [← heq, h1]
  rw [h2] at h5
  have h3 : e = δ.getD (g - 1) false := by
    simpa using List.append_cancel_left h5
  rw [← h2, ← h3]
  exact hEA

/-- A stop word read at a prefix is a stop event at the parent node (exit arrow) or at
itself (crossing). -/
theorem stopEv_of_stopW_take {P : IETDatum₂ α n} {A' : Finset α} {w : List Bool} {δ : List Bool}
    {g : ℕ} (hW : StopW P A' w (δ.take g)) (hg : g < δ.length) :
    StopEv P A' w δ (g - 1) ∨ StopEv P A' w δ g := by
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · right
    rcases hW with ⟨e, heq, -⟩ | hH
    · have hz : δ.take g = ([] : List Bool) := by rw [h0]; rfl
      rw [hz] at heq
      simp at heq
    · exact Or.inl hH
  · rcases hW with ⟨e, heq, hEA⟩ | hH
    · exact Or.inl (Or.inr ⟨by omega, exitArrow_of_stopW_take hg hpos heq hEA⟩)
    · exact Or.inr (Or.inl hH)

/-! ## 4.b From a good word which has stopped to a clean stop -/

/-- A word with a stop event whose first one is clean. This is the form the covering lemma consumes:
at the stopping length of `exists_stop_length` every word has stopped, so `Good` gives `GoodFirst`.
-/
theorem goodFirst_of_good {P : IETDatum₂ α n} {A' : Finset α} {w δ : List Bool}
    (h : Good P A' w δ) (hstop : ∃ g ∈ Finset.range (δ.length + 1), StopEv P A' w δ g) :
    GoodFirst P A' w δ := by
  rcases h with h | h
  · obtain ⟨g, hg, hse⟩ := hstop
    exact absurd hse (h g hg)
  · exact h

/-- **Covering.**  A word with a clean stop has a prefix in the minimal stopping family. -/
theorem exists_stopfam_of_good (P : IETDatum₂ α n) (hP : P.Irreducible)
    (hn : 2 ≤ n) (w : List Bool) (A' : Finset α) (N : ℕ)
    (_hN : ∀ δ : List Bool, δ.length = N →
      ∃ i ∈ Finset.range (δ.length + 1), Huge P w (δ.take i))
    {δ : List Bool} (hlen : δ.length = N) (hgood : GoodFirst P A' w δ) :
    ∃ η ∈ StopFam P A' w N, η <+: δ := by
  classical
  obtain ⟨j, hjmem, hjfirst, hcase⟩ := hgood
  have hjle : j ≤ δ.length := by rw [Finset.mem_range] at hjmem; omega
  have hlenj : (δ.take j).length = j := by rw [List.length_take, Nat.min_eq_left hjle]
  have hbelow : ∀ g, g < j → ∀ b : α, NodeHeight.st P (w ++ δ.take g) b ≤ thr P w := by
    intro g hg b
    have hns := hjfirst g (by rw [Finset.mem_range]; exact hg)
    exact (st_le_Mx P (w ++ δ.take g) b).trans
      (not_lt.mp fun hc => hns (Or.inl hc))
  have hcleanJ : Clean P A' w (δ.take j) := by
    rcases hcase with ⟨-, hc⟩ | ⟨-, -, hc⟩
    · exact hc
    · exact hc
  have hminAt : ∀ g, g < j → ¬ StopW P A' w (δ.take g) := by
    intro g hg hW
    have hgl : g < δ.length := lt_of_lt_of_le hg hjle
    rcases stopEv_of_stopW_take hW hgl with hSE | hSE
    · exact hjfirst (g - 1) (by rw [Finset.mem_range]; omega) hSE
    · exact hjfirst g (by rw [Finset.mem_range]; exact hg) hSE
  by_cases hH : Huge P w (δ.take j)
  · -- case 1: the maximum has crossed at `j`
    have hAb : ABound P A' w (δ.take j) := by
      intro i hi b hb
      have hle : i ≤ j := by rw [Finset.mem_range] at hi; omega
      have htake : (δ.take j).take i = δ.take i := by
        rw [List.take_take, Nat.min_eq_left hle]
      rw [htake]
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hbelow i hlt b
      · subst heq
        exact hcleanJ b hb
    have hmin : ∀ g ∈ Finset.range (δ.take j).length,
        ¬ StopW P A' w ((δ.take j).take g) := by
      intro g hg hW
      rw [Finset.mem_range, hlenj] at hg
      have htake : (δ.take j).take g = δ.take g := by
        rw [List.take_take, Nat.min_eq_left (le_of_lt hg)]
      exact hminAt g hg (by rw [← htake]; exact hW)
    refine ⟨δ.take j, ?_, List.take_prefix j δ⟩
    rw [StopFam, Finset.mem_biUnion]
    exact ⟨j, by rw [Finset.mem_range]; omega,
      Finset.mem_filter.mpr ⟨mem_levelWords_iff.mpr hlenj, Or.inr hH, hAb, hmin⟩⟩
  · -- case 2: the letter taken at `j` is an exit arrow and the maximum has not crossed
    rcases hcase with ⟨hH', -⟩ | ⟨hsucc, hEA, -⟩
    · exact absurd hH' hH
    have hjlt : j < δ.length := by omega
    have hsplitj : δ.take (j + 1) = δ.take j ++ [δ.getD j false] := take_succ_getD δ hjlt
    have hlenS : (δ.take (j + 1)).length = j + 1 := by
      rw [List.length_take, Nat.min_eq_left (by omega)]
    have hdropS : (δ.take (j + 1)).dropLast = δ.take j := by
      rw [hsplitj, List.dropLast_concat]
    have hAb : ABound P A' w (δ.take (j + 1)) := by
      intro i hi b hb
      have hle : i ≤ j + 1 := by rw [Finset.mem_range] at hi; omega
      have htake : (δ.take (j + 1)).take i = δ.take i := by
        rw [List.take_take, Nat.min_eq_left hle]
      rw [htake]
      rcases lt_or_eq_of_le hle with hlt | heq
      · rcases lt_or_eq_of_le (show i ≤ j by omega) with hlt2 | heq2
        · exact hbelow i hlt2 b
        · subst heq2
          exact hcleanJ b hb
      · subst heq
        rw [hsplitj, ← List.append_assoc, st_eq_of_exitArrow P hP hn hEA hb]
        exact hcleanJ b hb
    have hminAtJ : ¬ StopW P A' w (δ.take j) := by
      intro hW
      rcases hW with ⟨e, heq, hEA'⟩ | hHj
      · rcases Nat.eq_zero_or_pos j with h0 | hpos
        · have hz : δ.take j = ([] : List Bool) := by rw [h0]; rfl
          rw [hz] at heq
          simp at heq
        · exact hjfirst (j - 1) (by rw [Finset.mem_range]; omega)
            (Or.inr ⟨by omega, exitArrow_of_stopW_take hjlt hpos heq hEA'⟩)
      · exact hH hHj
    have hmin : ∀ g ∈ Finset.range (δ.take (j + 1)).length,
        ¬ StopW P A' w ((δ.take (j + 1)).take g) := by
      intro g hg hW
      rw [Finset.mem_range, hlenS] at hg
      have htake : (δ.take (j + 1)).take g = δ.take g := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
      rw [htake] at hW
      rcases lt_or_eq_of_le (show g ≤ j by omega) with hlt | heq
      · exact hminAt g hlt hW
      · rw [heq] at hW
        exact hminAtJ hW
    refine ⟨δ.take (j + 1), ?_, List.take_prefix (j + 1) δ⟩
    rw [StopFam, Finset.mem_biUnion]
    refine ⟨j + 1, by rw [Finset.mem_range]; omega, ?_⟩
    refine Finset.mem_filter.mpr ⟨mem_levelWords_iff.mpr hlenS, ?_, hAb, hmin⟩
    exact Or.inl ⟨δ.getD j false, by rw [hsplitj, List.dropLast_concat],
      by rw [hdropS]; exact hEA⟩

/-! ## 6. The race estimate and the assembly -/

end Stopping

