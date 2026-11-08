/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.RichPath.LargeLetter
public import IETFree.RauzyVeech.RichPath.LevelWords

/-!
# The `Γ₃` bookkeeping: thresholds, stop events, and the minimal stopping family

The vocabulary that the `Γ₃` argument of `IETFree.RauzyVeech.RichPath.Potential` runs on (`colSum =
colSum` is
`B_w·1`, `mkMass 1` is the maximum `𝔐 = 𝔐(q_w)`):

* §1 words of equal length are prefix-free (`prefixFree_of_length`); the level-`N` words themselves,
  with `mem_levelWords_iff` and the mass identity `sum_cond_levelWords`, are in
  `RauzyVeech/RichPath/LevelWords.lean`, below this file;
* §2 the threshold `thr = 2·d·𝔐` (`Mx`, `thr`, `qmin`, with `Mx_pos`, `Mx_lt_thr`,
  `colSum_le_thr`), the
  predicate `Huge` (the maximum has crossed at some prefix, `not_huge_nil`), and the explicit
  stopping length `exists_stop_length`: every word of length `⌈2d²M/min⌉ + 1` is huge;
* §3 the sum of the `A'`-heights along a continuation: `sum_colSum_append_singleton` (one step),
  `sum_colSum_ge` (growth) and `sum_colSum_le` (boundedness by `Mx`), hence `length_le_of_not_huge`;
* §4 exit arrows `ExitArrow`, stop events `StopEv`, the cleanness predicate `Clean`, the good/bad
  predicates `GoodFirst`, `Good`, `Bad` with their `Decidable` instances, and the minimal stopping
  family `StopW`, `StopFam` (`prefixFree_stopFam`, `colSum_eq_of_exitArrow`).

-/

@[expose] public section

open MeasureTheory IntervalExchange.IETDatum₂ Finset
open scoped BigOperators

namespace IntervalExchange.RauzyVeech.RichPath

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Prefix-free families of words of equal length -/

/-- Words of the same length form a prefix-free family. -/
theorem prefixFree_of_length {N : ℕ} {G : Finset (List Bool)}
    (hG : ∀ δ ∈ G, δ.length = N) : PrefixFree G := by
  intro u hu v hv hpre
  have hlen : u.length = v.length := by rw [hG u hu, hG v hv]
  have huv : u = v := List.IsPrefix.eq_of_length hpre hlen
  subst huv
  exact List.prefix_rfl

/-! ## 2. The threshold, the minimum height, and the stopping rule -/

omit [DecidableEq α] in
theorem one_le_card_cast (P : IETDatum₂ α n) : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by
  have := P.card_pos
  exact_mod_cast this

/-- The maximum of the state at the node `w`. -/
noncomputable def Mx (P : IETDatum₂ α n) (w : List Bool) : ℝ := mkMass 1 (colSum P w)

/-- The threshold `2·#α·M(q_w)` of the dichotomy. -/
noncomputable def thr (P : IETDatum₂ α n) (w : List Bool) : ℝ :=
  2 * (Fintype.card α : ℝ) * Mx P w

/-- The minimal height of the state at the node `w`, as `mkMass #α`. -/
noncomputable def qmin (P : IETDatum₂ α n) (w : List Bool) : ℝ :=
  mkMass (Fintype.card α) (colSum P w)

omit [DecidableEq α] in
/-- `mkMass #α` is the minimum over the alphabet. -/
theorem Mk_card_eq_mmin (q : α → ℝ) :
    mkMass (Fintype.card α) q = mmin Finset.univ q := by
  have hne : ((Finset.univ : Finset α).powersetCard (Fintype.card α)).Nonempty :=
    ⟨Finset.univ, by simp⟩
  refine le_antisymm ?_ (mmin_le_mkMass (s := Finset.univ) (k := Fintype.card α)
    Finset.card_univ)
  rw [mkMass_eq hne, Finset.sup'_le_iff]
  intro s hs
  have hsu : s = Finset.univ :=
    Finset.eq_univ_of_card s (by rw [(Finset.mem_powersetCard.mp hs).2])
  rw [hsu]

theorem qmin_le (P : IETDatum₂ α n) (w : List Bool) (b : α) :
    qmin P w ≤ colSum P w b := by
  rw [qmin, Mk_card_eq_mmin]
  exact mmin_le (Finset.mem_univ b)

theorem qmin_pos [Nonempty α] (P : IETDatum₂ α n) (w : List Bool) : 0 < qmin P w := by
  rw [qmin, Mk_card_eq_mmin]
  exact mmin_pos (Finset.univ_nonempty) (fun b => colSum_pos P w b)

omit [Fintype α] [DecidableEq α] in
/-- `mmin` is monotone in the state. -/
theorem mmin_le_mmin {q q' : α → ℝ} (h : ∀ b, q b ≤ q' b) (s : Finset α)
    (hs : s.Nonempty) :
    mmin s q ≤ mmin s q' := by
  obtain ⟨b, hb, hbe⟩ := Finset.exists_mem_eq_inf' hs q'
  have h2 : mmin s q' = q' b := (mmin_eq hs q').trans hbe
  rw [h2]
  exact (mmin_le hb).trans (h b)

/-- The minimal height only grows. -/
theorem qmin_mono [Nonempty α] (P : IETDatum₂ α n) (w δ : List Bool) :
    qmin P w ≤ qmin P (w ++ δ) := by
  rw [qmin, qmin, Mk_card_eq_mmin, Mk_card_eq_mmin]
  refine mmin_le_mmin (fun b => ?_) Finset.univ Finset.univ_nonempty
  exact state_mono P w δ b

theorem Mx_pos (P : IETDatum₂ α n) (w : List Bool) : 0 < Mx P w :=
  mkMass_colSum_pos (k := 1) P w le_rfl (P.card_pos)

/-- `Mx` dominates every height. -/
theorem colSum_le_Mx (P : IETDatum₂ α n) (w : List Bool) (b : α) : colSum P w b ≤ Mx P w :=
  (Mk_one_le_iff (P.card_pos) (q := colSum P w)
    (R := Mx P w)).mp le_rfl b

/-- The threshold dominates every height. -/
theorem colSum_le_thr (P : IETDatum₂ α n) (w : List Bool) (b : α) :
    colSum P w b ≤ thr P w := by
  have h1 := colSum_le_Mx P w b
  have h2 := Mx_pos P w
  have h3 := one_le_card_cast P
  rw [thr]
  nlinarith [h1, h2, h3]

/-- The maximum is below the threshold. -/
theorem Mx_lt_thr (P : IETDatum₂ α n) (w : List Bool) : Mx P w < thr P w := by
  have h1 := Mx_pos P w
  have h2 := one_le_card_cast P
  rw [thr]
  nlinarith

/-- The threshold `2·#α·M(q_w)` is positive. -/
theorem thr_pos (P : IETDatum₂ α n) (w : List Bool) : 0 < thr P w :=
  lt_trans (Mx_pos P w) (Mx_lt_thr P w)

/-- The maximum at the node `w ++ μ` exceeds the threshold. -/
noncomputable def Huge (P : IETDatum₂ α n) (w μ : List Bool) : Prop :=
  thr P w < Mx P (w ++ μ)

/-- The root is not a crossing. -/
theorem not_huge_nil (P : IETDatum₂ α n) (w : List Bool) : ¬ Huge P w [] := by
  rw [Huge, List.append_nil]
  exact not_lt.mpr (le_of_lt (Mx_lt_thr P w))

/-- The `A'`-heights stay below the threshold along `μ`. -/
def ABound (P : IETDatum₂ α n) (A' : Finset α) (w μ : List Bool) : Prop :=
  ∀ i ∈ Finset.range (μ.length + 1), ∀ b ∈ A', colSum P (w ++ μ.take i) b ≤ thr P w

/-! ## 3. The sum of the heights along a continuation -/

/-- The sum of the heights after one more letter: the loser grows by the winner. -/
theorem sum_colSum_append_singleton (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (v : List Bool) (e : Bool) :
    ∑ b, colSum P (v ++ [e]) b
      = ∑ b, colSum P v b + colSum P v ((IETDatum₂.vertex P v).last e) := by
  have hterm (b) : colSum P (v ++ [e]) b
      = colSum P v b + (if b = (IETDatum₂.vertex P v).last (!e)
          then colSum P v ((IETDatum₂.vertex P v).last e) else 0) := by
    have h := colSum_append_singleton P hP hn v e b
    simpa [colSum] using h
  calc ∑ b, colSum P (v ++ [e]) b
      = ∑ b, (colSum P v b + (if b = (IETDatum₂.vertex P v).last (!e)
          then colSum P v ((IETDatum₂.vertex P v).last e) else 0)) :=
        Finset.sum_congr rfl fun b _ => hterm b
    _ = ∑ b, colSum P v b + ∑ b, (if b = (IETDatum₂.vertex P v).last (!e)
          then colSum P v ((IETDatum₂.vertex P v).last e) else 0) := Finset.sum_add_distrib
    _ = ∑ b, colSum P v b + colSum P v ((IETDatum₂.vertex P v).last e) := by
        rw [Finset.sum_ite_eq']
        simp

/-- **The total height grows at least by the minimal initial height at each step.** -/
theorem sum_colSum_ge [Nonempty α] (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (μ : List Bool) : ∑ b, colSum P w b + μ.length * qmin P w
      ≤ ∑ b, colSum P (w ++ μ) b := by
  induction μ generalizing w with
  | nil => simp
  | cons e μ ih =>
    have h3 := sum_colSum_append_singleton P hP hn w e
    have h4 : qmin P w ≤ colSum P w ((IETDatum₂.vertex P w).last e) := qmin_le P w _
    have h2 := ih (w ++ [e])
    have hmono : qmin P w ≤ qmin P (w ++ [e]) := qmin_mono P w [e]
    have hmlen : (0 : ℝ) ≤ (μ.length : ℝ) := Nat.cast_nonneg _
    have heq : w ++ (e :: μ) = (w ++ [e]) ++ μ := by rw [List.append_assoc]; rfl
    have hlen : ((e :: μ).length : ℝ) = (μ.length : ℝ) + 1 := by simp
    have hq : (0 : ℝ) < qmin P w := qmin_pos P w
    rw [heq, hlen]
    nlinarith [h2, h3, h4, hq, hmono, hmlen]

/-- The sum of the heights is at most `#α` times the maximum. -/
theorem sum_colSum_le (P : IETDatum₂ α n) (v : List Bool) {R : ℝ} (hR : Mx P v ≤ R) :
    ∑ b, colSum P v b ≤ (Fintype.card α : ℝ) * R := by
  have hb (b) : colSum P v b ≤ R := (colSum_le_Mx P v b).trans hR
  calc ∑ b, colSum P v b ≤ ∑ _b : α, R := Finset.sum_le_sum fun b _ => hb b
    _ = (Fintype.card α : ℝ) * R := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **A word along which the maximum has not crossed the threshold is short.** -/
theorem length_le_of_not_huge [Nonempty α] (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w δ : List Bool) (hδ : ¬ Huge P w δ) :
    (δ.length : ℝ) * qmin P w ≤ (Fintype.card α : ℝ) * thr P w := by
  have h1 := sum_colSum_ge P hP hn w δ
  have h2 := sum_colSum_le P (w ++ δ) (not_lt.mp hδ)
  have h3 : (0 : ℝ) ≤ ∑ b, colSum P w b :=
    Finset.sum_nonneg fun b _ => colSum_nonneg P w b
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
  ∀ b ∈ A', colSum P (w ++ μ) b ≤ thr P w

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

/-- Decidability of `StopEv`, classically: the file filters words by it.  `local`, so that
nothing outside it inherits a classical instance that a computable one would have to shadow. -/
noncomputable local instance stopEvDecidable (P : IETDatum₂ α n) (A' : Finset α) (w δ : List Bool) :
    DecidablePred (StopEv P A' w δ) := fun _ => Classical.propDecidable _

/-- Decidability of `Good`, classically (`local`, as for `stopEvDecidable`). -/
noncomputable local instance goodDecidable (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) :
    DecidablePred (Good P A' w) := fun _ => Classical.propDecidable _

/-- Decidability of `Bad`, classically (`local`, as for `stopEvDecidable`). -/
noncomputable local instance badDecidable (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) :
    DecidablePred (Bad P A' w) := fun _ => Classical.propDecidable _

/-- The stop *words*: `η` ends with an exit arrow at its parent node, or the maximum has already
crossed the threshold at `η`. -/
noncomputable def StopW (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool)
    (η : List Bool) : Prop :=
  (∃ e : Bool, η = η.dropLast ++ [e] ∧ ExitArrow P A' w η.dropLast e) ∨ Huge P w η

/-- The predicate defining the minimal stopping family. -/
noncomputable def StopPred (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool)
    (η : List Bool) : Prop :=
  StopW P A' w η ∧ ABound P A' w η ∧
    ∀ j ∈ Finset.range η.length, ¬ StopW P A' w (η.take j)

/-- Decidability of `StopPred`, classically (`local`, as for `stopEvDecidable`). -/
noncomputable local instance stopPredDecidable (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) :
    DecidablePred (StopPred P A' w) := fun _ => Classical.propDecidable _

/-- **The minimal stopping family**: the words of length `≤ N` which are a stop word and such that
no shorter stop word is a prefix, with the `A'`-heights below the threshold throughout. -/
noncomputable def StopFam (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) (N : ℕ) :
    Finset (List Bool) :=
  (Finset.range (N + 1)).biUnion (fun m => (levelWords m).filter (StopPred P A' w))

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
  rw [length_mem_levelWords hlev]
  omega

/-- The minimal stopping family is prefix-free. -/
theorem prefixFree_stopFam (P : IETDatum₂ α n) (A' : Finset α) (w : List Bool) (N : ℕ) :
    PrefixFree (StopFam P A' w N) := by
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
theorem colSum_eq_of_exitArrow (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {A' : Finset α} {w μ : List Bool} {e : Bool}
    (hE : ExitArrow P A' w μ e) {b : α} (hb : b ∈ A') :
    colSum P (w ++ μ ++ [e]) b = colSum P (w ++ μ) b := by
  obtain ⟨-, hlose⟩ := hE
  have h := colSum_append_singleton P hP hn (w ++ μ) e b
  have hne : b ≠ (IETDatum₂.vertex P (w ++ μ)).last (!e) := fun hb' => hlose (hb' ▸ hb)
  rw [h, ite_eq_right hne, add_zero]

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
    {δ : List Bool} (hlen : δ.length = N) (hgood : GoodFirst P A' w δ) :
    ∃ η ∈ StopFam P A' w N, η <+: δ := by
  obtain ⟨j, hjmem, hjfirst, hcase⟩ := hgood
  have hjle : j ≤ δ.length := by rw [Finset.mem_range] at hjmem; omega
  have hlenj : (δ.take j).length = j := by rw [List.length_take, Nat.min_eq_left hjle]
  have hbelow (g) (hg : g < j) : ∀ b : α, colSum P (w ++ δ.take g) b ≤ thr P w := by
    intro b
    have hns := hjfirst g (by rw [Finset.mem_range]; exact hg)
    exact (colSum_le_Mx P (w ++ δ.take g) b).trans
      (not_lt.mp fun hc => hns (Or.inl hc))
  have hcleanJ : Clean P A' w (δ.take j) := by
    rcases hcase with ⟨-, hc⟩ | ⟨-, -, hc⟩
    · exact hc
    · exact hc
  have hminAt (g) (hg : g < j) : ¬ StopW P A' w (δ.take g) := by
    intro hW
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
    have hmin (g) (hg : g ∈ Finset.range (δ.take j).length) : ¬ StopW P A' w ((δ.take
        j).take g) := by
      intro hW
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
        rw [hsplitj, ← List.append_assoc, colSum_eq_of_exitArrow P hP hn hEA hb]
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
    have hmin (g) (hg : g ∈ Finset.range (δ.take (j + 1)).length) : ¬ StopW P A' w
        ((δ.take (j + 1)).take g) := by
      intro hW
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

end IntervalExchange.RauzyVeech.RichPath

end
