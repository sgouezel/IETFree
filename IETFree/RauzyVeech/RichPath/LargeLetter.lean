/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.RauzyVeech.RichPath.NodeHeight

/-!
# The new-large-letter step `Γ₄`

The graded induction of the source has three steps at level `k`: `Γ₂` (extend to a vertex where a
row end is outside `A'`), `Γ₃` (Kerckhoff bounds the `A'`-coordinates) and `Γ₄` (a new large letter
appears).  This file proves **`Γ₄`**, in the form the `k → k+1` step consumes:

* `Mk_one_le_iff`, `exists_eq_Mk_one`, `le_mmin_insert`, `Mk_one_step_le`, `cs_step_le_two`: the
  bookkeeping of the maximum `Mk 1`, in particular that one arrow at most doubles a height;
* `abs` / `words`: `Γ₄` in its two branches, with constant `4·#α·Cb` — a new large
  letter appears, under the dichotomy of the `A'`-heights;
* `sum_cond_le_one`, `sum_cond_fibre_le`, **`exists_prefixFree_mass`**: the minimal prefixes of a
  covering family carry at least its mass (replacing the paper's non-injective, non-prefix-free
  truncation in "`P(Γ₄ | π) ≥ P(Γ₃ | π)`"), together with `take_succ_eq_of_head`,
  `exists_head_drop`.
-/


open MeasureTheory Finset NodeHeight
open scoped BigOperators

namespace LargeLetter

open IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. `Mk 1` is the maximum, and `mmin` on an insertion -/

omit [DecidableEq α] in
/-- `Mk 1 q` is exactly the maximum of `q` over the alphabet. -/
theorem Mk_one_le_iff {q : α → ℝ} {R : ℝ} (hcard : 1 ≤ Fintype.card α) :
    Mk 1 q ≤ R ↔ ∀ b, q b ≤ R := by
  constructor
  · intro h b
    calc q b = mmin {b} q := (mmin_singleton b q).symm
      _ ≤ Mk 1 q := mmin_le_Mk (Finset.card_singleton b)
      _ ≤ R := h
  · intro h
    have hne : ((Finset.univ : Finset α).powersetCard 1).Nonempty := by
      rw [Finset.powersetCard_nonempty]
      simpa using hcard
    rw [Mk_eq hne, Finset.sup'_le_iff]
    intro s hs
    obtain ⟨-, hscard⟩ := Finset.mem_powersetCard.mp hs
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hscard
    rw [mmin_singleton]
    exact h b

omit [DecidableEq α] in
/-- The maximum `Mk 1 q` is attained (as soon as the alphabet is nonempty). -/
theorem exists_eq_Mk_one (q : α → ℝ) (hcard : 1 ≤ Fintype.card α) :
    ∃ b, q b = Mk 1 q := by
  have hne : ((Finset.univ : Finset α).powersetCard 1).Nonempty := by
    rw [Finset.powersetCard_nonempty]
    simpa using hcard
  rw [Mk_eq hne]
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup' hne (fun s => mmin s q)
  obtain ⟨-, hscard⟩ := Finset.mem_powersetCard.mp hs
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hscard
  exact ⟨b, by rw [mmin_singleton] at hsup; exact hsup.symm⟩

omit [Fintype α] in
/-- A lower bound for `mmin` on `insert θ A'`. -/
theorem le_mmin_insert {A' : Finset α} {q : α → ℝ} {θ : α} {c : ℝ} :
    c ≤ mmin (insert θ A') q ↔ c ≤ q θ ∧ ∀ b ∈ A', c ≤ q b := by
  constructor
  · intro h
    exact ⟨le_trans h (mmin_le (Finset.mem_insert_self θ A')),
      fun b hb => le_trans h (mmin_le (Finset.mem_insert_of_mem hb))⟩
  · rintro ⟨h1, h2⟩
    exact le_mmin ⟨θ, Finset.mem_insert_self θ A'⟩ fun b hb => by
      rcases Finset.mem_insert.mp hb with rfl | hb'
      · exact h1
      · exact h2 b hb'

/-! ## 2. One Rauzy--Veech step at most doubles the maximum -/

/-- A single arrow changes each height by adding a height of the parent node. -/
theorem cs_step_le_two (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (e : Bool) (b : α) :
    ColShrink.cs P (w ++ [e]) b ≤ 2 * Mk 1 (st P w) := by
  rw [CylinderMass.cs_append_singleton P hP hn w e b]
  have h1 : ColShrink.cs P w b ≤ Mk 1 (st P w) := le_Mk_one b
  have h2 : ColShrink.cs P w ((P.vertex w).last e) ≤ Mk 1 (st P w) := le_Mk_one _
  have h0 : 0 < Mk 1 (st P w) := Mk_st_pos P w le_rfl (card_pos P)
  split_ifs with h
  · linarith
  · linarith

/-- The maximum at most doubles in one step. -/
theorem Mk_one_step_le (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (e : Bool) :
    Mk 1 (st P (w ++ [e])) ≤ 2 * Mk 1 (st P w) := by
  rw [Mk_one_le_iff (card_pos P)]
  exact cs_step_le_two P hP hn w e

/-! ## 3. `Γ₄` in abstract form: the dichotomy with constant `4·d·κ`  The paper's `Γ₄`: given a path
along which no `A'`-height exceeds `2d·M(q_w)` (the output of `Γ₃`), either the maximum has crossed
`2d·M(q_w)` — then the *first crossing letter* is a new letter of size `≥ (4d·κ)⁻¹ · M`, where `κ`
relates `M(q_w)` to the `A'`-heights — or it has not, and then the *loser of the last arrow* is such
a letter (because the last arrow's winner lies in `A'` and the `A'`-heights are all `≥
(1/Cb)·M(q_w)`).  In both cases one gets a node of the path and a letter outside `A'` with `M ≤ 4dκε
· min{m_{A'∪{θ}}, M(q_w)}`. -/

/-- **`Γ₄`, abstract form**: a node of the path and a letter outside `A'` with
`M ≤ 4dκε · min{m_{A'∪{θ}}, M(q_w)}`. -/
theorem newLetter_bound
    (h : ℕ → α → ℝ) (win lose : ℕ → α) (N : ℕ) (A' : Finset α) {R mA κ : ℝ}
    (hcard : 1 ≤ Fintype.card α)
    (hpos : ∀ i ≤ N, ∀ b, 0 < h i b)
    (hstep : ∀ i < N, ∀ b, h (i + 1) b = h i b + (if b = lose i then h i (win i) else 0))
    (hR : ∀ b, h 0 b ≤ R) (hRpos : 0 < R)
    (hA'ne : A'.Nonempty)
    (hmA : ∀ i ≤ N, ∀ b ∈ A', mA ≤ h i b)
    (hκ : R ≤ κ * mA) (hκ1 : 1 ≤ κ)
    (hAN : ∀ i ≤ N, ∀ b ∈ A', h i b ≤ 2 * (Fintype.card α : ℝ) * R)
    (hN1 : 1 ≤ N)
    (hlast : Mk 1 (h N) ≤ 2 * (Fintype.card α : ℝ) * R →
      win (N - 1) ∈ A' ∧ lose (N - 1) ∉ A') :
    ∃ i, i ≤ N ∧ ∃ θ, θ ∉ A' ∧
      Mk 1 (h i) ≤ 4 * (Fintype.card α : ℝ) * κ *
        min (mmin (insert θ A') (h i)) R := by
  classical
  set d : ℝ := (Fintype.card α : ℝ) with hd
  have hd1 : (1 : ℝ) ≤ d := by rw [hd]; exact_mod_cast hcard
  have hR0 : Mk 1 (h 0) ≤ R := (Mk_one_le_iff hcard).mpr hR
  have hRnn : (0 : ℝ) ≤ R := le_of_lt hRpos
  have hd0 : (0 : ℝ) ≤ d := by linarith
  have hκ0 : (0 : ℝ) ≤ κ := by linarith
  have hdκ : (0 : ℝ) ≤ 4 * d * κ := by positivity
  have h2dR : (0 : ℝ) ≤ 2 * d * R := by positivity
  by_cases hcase : Mk 1 (h N) ≤ 2 * d * R
  · -- case 2: the maximum did not cross `2dR`; the last loser is a new large letter
    obtain ⟨hwinN, hloseN⟩ := hlast (by rw [hd]; exact hcase)
    have hNsub : N - 1 < N := by omega
    have hNm : N - 1 + 1 = N := Nat.sub_add_cancel hN1
    have hθ : mA ≤ h N (lose (N - 1)) := by
      have h1 := hmA (N - 1) (by omega) (win (N - 1)) hwinN
      have h2 := hstep (N - 1) hNsub (lose (N - 1))
      rw [hNm] at h2
      rw [h2]
      have hp := hpos (N - 1) (by omega) (lose (N - 1))
      split_ifs with hh
      · linarith
      · exact absurd rfl hh
    have hmin : mA ≤ mmin (insert (lose (N - 1)) A') (h N) :=
      le_mmin_insert.mpr ⟨hθ, hmA N le_rfl⟩
    have hminR : min mA R ≤ min (mmin (insert (lose (N - 1)) A') (h N)) R :=
      min_le_min hmin le_rfl
    have hkey : 2 * d * R ≤ 4 * d * κ * min mA R := by
      rcases le_total R mA with hr | hr
      · rw [min_eq_right hr]
        nlinarith
      · rw [min_eq_left hr]
        nlinarith
    refine ⟨N, le_rfl, lose (N - 1), hloseN, ?_⟩
    calc Mk 1 (h N) ≤ 2 * d * R := hcase
      _ ≤ 4 * d * κ * min mA R := hkey
      _ ≤ 4 * d * κ * min (mmin (insert (lose (N - 1)) A') (h N)) R :=
          mul_le_mul_of_nonneg_left hminR hdκ
  · -- case 1: the maximum crossed `2dR`; the first crossing letter is a new large letter
    simp only [not_le] at hcase
    have hex : ∃ j : ℕ, 2 * d * R < Mk 1 (h j) := ⟨N, hcase⟩
    set j := Nat.find hex with hjdef
    have hjgt : 2 * d * R < Mk 1 (h j) := Nat.find_spec hex
    have hjmin : ∀ m, m < j → ¬ (2 * d * R < Mk 1 (h m)) := fun m hm => Nat.find_min hex hm
    have hjle : j ≤ N := Nat.find_min' hex hcase
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · exfalso
        have hgt := hjgt
        rw [h0] at hgt
        have := hR0
        nlinarith
      · exact h0
    have hprev : Mk 1 (h (j - 1)) ≤ 2 * d * R := not_lt.mp (hjmin (j - 1) (by omega))
    have hjN : j - 1 < N := by omega
    have hbound : ∀ b, h j b ≤ 2 * (2 * d * R) := by
      intro b
      have hstepj := hstep (j - 1) hjN b
      have hjm : j - 1 + 1 = j := Nat.sub_add_cancel hj1
      rw [hjm] at hstepj
      rw [hstepj]
      have h1 : h (j - 1) b ≤ 2 * d * R := (Mk_one_le_iff hcard).mp hprev b
      have h2 : h (j - 1) (win (j - 1)) ≤ 2 * d * R := (Mk_one_le_iff hcard).mp hprev _
      split_ifs with hh
      · linarith
      · linarith
    obtain ⟨θ, hθeq⟩ := exists_eq_Mk_one (h j) hcard
    have hθgt : 2 * d * R < h j θ := by rw [hθeq]; exact hjgt
    have hθnot : θ ∉ A' := by
      intro hθA
      have h1 := hAN j hjle θ hθA
      linarith
    have hmaxj : Mk 1 (h j) ≤ 4 * d * R := by
      rw [Mk_one_le_iff hcard]
      intro b
      have := hbound b
      linarith
    have hmAj : mA ≤ h j θ := by
      obtain ⟨b₀, hb₀⟩ := hA'ne
      have h1 := hmA j hjle b₀ hb₀
      have h2 := hAN j hjle b₀ hb₀
      linarith
    have hmin : mA ≤ mmin (insert θ A') (h j) := le_mmin_insert.mpr ⟨hmAj, hmA j hjle⟩
    have hminR : min mA R ≤ min (mmin (insert θ A') (h j)) R := min_le_min hmin le_rfl
    have hkey : 4 * d * R ≤ 4 * d * κ * min mA R := by
      rcases le_total R mA with hr | hr
      · rw [min_eq_right hr]
        nlinarith
      · rw [min_eq_left hr]
        nlinarith
    refine ⟨j, hjle, θ, hθnot, ?_⟩
    calc Mk 1 (h j) ≤ 4 * d * R := hmaxj
      _ ≤ 4 * d * κ * min mA R := hkey
      _ ≤ 4 * d * κ * min (mmin (insert θ A') (h j)) R :=
          mul_le_mul_of_nonneg_left hminR hdκ

/-! ## 4. The word-level form of `Γ₄` -/

/-- Splitting off the last letter of a prefix, in a form that avoids dependent indices. -/
theorem take_succ_eq_of_head (l : List Bool) (i : ℕ) (e : Bool)
    (h : (l.drop i).head? = some e) : l.take (i + 1) = l.take i ++ [e] := by
  induction l generalizing i with
  | nil => simp at h
  | cons a t ih =>
    cases i with
    | zero =>
      simp only [List.drop_zero, List.head?_cons, Option.some.injEq] at h
      subst h
      rfl
    | succ j =>
      have h' : (t.drop j).head? = some e := by simpa using h
      simp only [List.take_succ_cons, List.cons_append]
      rw [ih j h']

/-- The letter dropped at a position below the length exists. -/
theorem exists_head_drop (l : List Bool) (i : ℕ) (h : i < l.length) :
    ∃ e : Bool, (l.drop i).head? = some e := by
  cases hh : (l.drop i).head? with
  | none =>
    rw [List.head?_eq_none_iff, List.drop_eq_nil_iff] at hh
    omega
  | some e => exact ⟨e, rfl⟩

/-- **`Γ₄` in the cylinder vocabulary.**  Let `w` be a node, `A'` a nonempty set of letters whose
heights at `w` are all `≥ (1/Cb)·Mk 1 (st P w)`, and let `δ = ν ++ [e]` be a continuation along
which no `A'`-height ever exceeds `2d·Mk 1 (st P w)` (the output of the paper's `Γ₃`), the last
arrow of which has its winner in `A'` and its loser outside `A'`.  Then some node of the path and
some letter outside `A'` satisfy

`Mk 1 (st P (w ++ δ.take i)) ≤ 4dCb · min (mmin (insert θ A') (st P (w ++ δ.take i)))
  (Mk 1 (st P w))`.

This is the paper's `Γ₄` dichotomy: either the maximum crossed `2d·Mk 1 (st P w)`, and the first
crossing letter is a new letter with `Mk 1 ≤ 4d·Mk 1 (st P w)`; or it did not, and the loser of the
last arrow is a new letter above the `A'`-level. -/
theorem newLetter_words
    (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w ν : List Bool) (e : Bool) (A' : Finset α) {Cb : ℝ}
    (hA'ne : A'.Nonempty) (hCb : 1 ≤ Cb)
    (hbal : ∀ b ∈ A', (1 / Cb) * Mk 1 (st P w) ≤ st P w b)
    (hAN : ∀ i, i ≤ (ν ++ [e]).length → ∀ b ∈ A',
      st P (w ++ (ν ++ [e]).take i) b ≤ 2 * (Fintype.card α : ℝ) * Mk 1 (st P w))
    (hlast : (IETDatum₂.vertex P (w ++ ν)).last e ∈ A' ∧
        (IETDatum₂.vertex P (w ++ ν)).last (!e) ∉ A'
      ∨ 2 * (Fintype.card α : ℝ) * Mk 1 (st P w) < Mk 1 (st P (w ++ (ν ++ [e])))) :
    ∃ i, i ≤ (ν ++ [e]).length ∧ ∃ θ, θ ∉ A' ∧
      Mk 1 (st P (w ++ (ν ++ [e]).take i)) ≤
        4 * (Fintype.card α : ℝ) * Cb *
          min (mmin (insert θ A') (st P (w ++ (ν ++ [e]).take i))) (Mk 1 (st P w)) := by
  classical
  set δ : List Bool := ν ++ [e] with hδdef
  have hex : ∀ i, i < δ.length → ∃ e' : Bool, (δ.drop i).head? = some e' :=
    fun i h => exists_head_drop δ i h
  set ee : ℕ → Bool := fun i => if h : i < δ.length then Classical.choose (hex i h) else true
    with hee_def
  have hee : ∀ i (h : i < δ.length), (δ.drop i).head? = some (ee i) := by
    intro i h
    rw [hee_def]
    simp only [dif_pos h]
    exact Classical.choose_spec (hex i h)
  have htake : ∀ i (h : i < δ.length), δ.take (i + 1) = δ.take i ++ [ee i] :=
    fun i h => take_succ_eq_of_head δ i (ee i) (hee i h)
  have hstep : ∀ i < δ.length, ∀ b, st P (w ++ δ.take (i + 1)) b
      = st P (w ++ δ.take i) b
        + (if b = (P.vertex (w ++ δ.take i)).last (!(ee i))
           then st P (w ++ δ.take i) ((P.vertex (w ++ δ.take i)).last (ee i)) else 0) := by
    intro i h b
    change ColShrink.cs P (w ++ δ.take (i + 1)) b
      = ColShrink.cs P (w ++ δ.take i) b
        + (if b = (P.vertex (w ++ δ.take i)).last (!(ee i))
           then ColShrink.cs P (w ++ δ.take i) ((P.vertex (w ++ δ.take i)).last (ee i))
           else 0)
    rw [htake i h, ← List.append_assoc,
      CylinderMass.cs_append_singleton P hP hn (w ++ δ.take i) (ee i) b]
  have hδlen : δ.length = ν.length + 1 := by simp [hδdef]
  have htakeν : δ.take ν.length = ν := by simp [hδdef]
  have hdropν : (δ.drop ν.length).head? = some e := by simp [hδdef]
  have heeLast : ee (δ.length - 1) = e := by
    have h1 : δ.length - 1 = ν.length := by omega
    rw [h1]
    have h2 := hee ν.length (by omega)
    rw [hdropν] at h2
    exact (Option.some.inj h2).symm
  have htakeLast : δ.take (δ.length - 1) = ν := by
    have h1 : δ.length - 1 = ν.length := by omega
    rw [h1, htakeν]
  have hlast' (hM : Mk 1 (st P (w ++ δ.take δ.length)) ≤ 2 * (Fintype.card α : ℝ) * Mk 1 (st P w)) :
    (P.vertex (w ++ δ.take (δ.length - 1))).last (ee (δ.length - 1)) ∈ A' ∧
      (P.vertex (w ++ δ.take (δ.length - 1))).last (!(ee (δ.length - 1))) ∉ A' := by
    have h1 : δ.take δ.length = ν ++ [e] := by rw [List.take_length, hδdef]
    rw [h1] at hM
    have h2 : (P.vertex (w ++ δ.take (δ.length - 1))).last (ee (δ.length - 1))
        = (P.vertex (w ++ ν)).last e := by rw [htakeLast, heeLast]
    have h3 : (P.vertex (w ++ δ.take (δ.length - 1))).last (!(ee (δ.length - 1)))
        = (P.vertex (w ++ ν)).last (!e) := by rw [htakeLast, heeLast]
    rw [h2, h3]
    rcases hlast with hh | hh
    · exact hh
    · exact absurd hh (not_lt.mpr hM)
  obtain ⟨i, hi, θ, hθ, hbound⟩ :=
    newLetter_bound (fun i => st P (w ++ δ.take i))
      (fun i => (P.vertex (w ++ δ.take i)).last (ee i))
      (fun i => (P.vertex (w ++ δ.take i)).last (!(ee i))) δ.length A'
      (card_pos P)
      (fun i _ b => st_pos P _ b)
      hstep
      (fun b => by simpa using le_Mk_one (q := st P w) b)
      (Mk_st_pos P w le_rfl (card_pos P))
      hA'ne
      (fun i _ b hb => le_trans (hbal b hb) (CylinderMass.state_mono P w (δ.take i) b))
      (by
        have hCb0 : Cb ≠ 0 := by linarith
        have hEq : Cb * (1 / Cb * Mk 1 (st P w)) = Mk 1 (st P w) := by
          field_simp
        rw [hEq])
      hCb
      (fun i hi b hb => hAN i hi b hb)
      (by omega)
      hlast'
  exact ⟨i, hi, θ, hθ, hbound⟩

/-! ## 5. The mass of an antichain is at most `1`  This is the step the paper uses silently when it
replaces `Γ₃` by `Γ₄` ("`P_q(Γ₄|π) ≥ P_q(Γ₃|π)`"): a finite antichain of continuations has total
relative mass at most `1`, so replacing a prefix-free family by a family of *prefixes* of its
members does not decrease the mass.  It is what makes `Γ₄`'s intermediate nodes usable inside the
mass argument. -/

theorem sum_cond_le_one (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (S : Finset (List Bool)) (hS : PrefixFree S) :
    ∑ δ ∈ S, CylinderMass.cond P w δ ≤ 1 := by
  set V := simplexVolumeOn α (IETDatum₂.simplexCyl P w) with hV
  have hVpos : 0 < V := RegionVolume.volume_simplexCyl_pos P w
  have hVtop : V ≠ ⊤ := ne_of_lt (BalancedCylinders.volume_simplexCyl_lt_top P w)
  have hsub : (⋃ δ ∈ S, IETDatum₂.simplexCyl P (w ++ δ)) ⊆ IETDatum₂.simplexCyl P w := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨δ, -, hx⟩ := hx
    exact BalancedCylinders.simplexCyl_append_prefix P hP hn w δ hx
  have hle : simplexVolumeOn α (⋃ δ ∈ S, IETDatum₂.simplexCyl P (w ++ δ)) ≤ V :=
    measure_mono hsub
  rw [BalancedCylinders.volume_iUnion_antichain P hP hn w S hS.antichain] at hle
  have hterm : ∀ δ ∈ S, simplexVolumeOn α (IETDatum₂.simplexCyl P (w ++ δ))
      = ENNReal.ofReal (CylinderMass.cond P w δ) * V :=
    fun δ _ => CylinderMass.volume_append_eq_cond P w δ
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul] at hle
  have h1 : (∑ δ ∈ S, ENNReal.ofReal (CylinderMass.cond P w δ)) ≤ 1 := by
    have h2 : V * (∑ δ ∈ S, ENNReal.ofReal (CylinderMass.cond P w δ)) ≤ V * 1 := by
      rw [mul_one, mul_comm V]
      exact hle
    exact (ENNReal.mul_le_mul_iff_right hVpos.ne' hVtop).mp h2
  have h3 : ENNReal.ofReal (∑ δ ∈ S, CylinderMass.cond P w δ) ≤ 1 := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun δ _ => (CylinderMass.cond_pos P w δ).le)]
    exact h1
  exact ENNReal.ofReal_le_one.mp h3

/-- **A prefix-free family all of whose members extend `t` has total mass at most `cond P w t`.**
The members are `t ++ u_δ` with the `u_δ` an antichain, so the mass factors through `cond P w t` and
`sum_cond_le_one` at the node `w ++ t`. -/
theorem sum_cond_fibre_le (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w t : List Bool) (S : Finset (List Bool)) (hS : PrefixFree S)
    (hext : ∀ δ ∈ S, t <+: δ) :
    ∑ δ ∈ S, CylinderMass.cond P w δ ≤ CylinderMass.cond P w t := by
  classical
  have hex : ∀ δ, δ ∈ S → ∃ u, δ = t ++ u := by
    intro δ hδ
    obtain ⟨u, hu⟩ := hext δ hδ
    exact ⟨u, hu.symm⟩
  set uu : List Bool → List Bool :=
    fun δ => if h : δ ∈ S then Classical.choose (hex δ h) else [] with huu
  have huu_eq : ∀ δ (h : δ ∈ S), uu δ = Classical.choose (hex δ h) := by
    intro δ h
    simp only [huu, dif_pos h]
  have hgoal : ∀ δ (h : δ ∈ S), δ = t ++ uu δ := by
    intro δ h
    rw [huu_eq δ h]
    exact Classical.choose_spec (hex δ h)
  have hsum : ∑ δ ∈ S, CylinderMass.cond P w δ
      = CylinderMass.cond P w t * ∑ δ ∈ S, CylinderMass.cond P (w ++ t) (uu δ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun δ hδ => ?_
    conv_lhs => rw [hgoal δ hδ]
    rw [CylinderMass.cond_append]
  rw [hsum]
  refine mul_le_of_le_one_right (le_of_lt (CylinderMass.cond_pos P w t)) ?_
  have hinj : ∀ x ∈ S, ∀ y ∈ S, uu x = uu y → x = y := by
    intro x hx y hy hxy
    rw [hgoal x hx, hgoal y hy, hxy]
  have himg : ∑ η ∈ S.image uu, CylinderMass.cond P (w ++ t) η
      = ∑ δ ∈ S, CylinderMass.cond P (w ++ t) (uu δ) := by
    rw [Finset.sum_image (f := fun η => CylinderMass.cond P (w ++ t) η) (g := uu)]
    exact hinj
  rw [← himg]
  refine sum_cond_le_one P hP hn (w ++ t) _ ?_
  refine (prefixFree_iff_one_sided _).mpr ?_
  intro a ha b hb hab habs
  rw [Finset.mem_image] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  have hxy : x <+: y := by
    rw [hgoal x hx, hgoal y hy]
    exact append_prefix_append t habs
  have hyx : y <+: x := hS x hx y hy hxy
  exact hab (congrArg uu (eq_of_prefix_of_prefix hxy hyx))

/-- **The family of minimal prefixes of a finite family carries at least its mass.**  Given a
prefix-free family `S` and a finite set `U` of words such that every member of `S` extends a member
of `U`, the *minimal* elements of `U` (for the prefix order) form a prefix-free family whose total
mass is at least that of `S`.  This is the correct substitute for the false statement "truncating a
prefix-free family to prefixes preserves the mass": the truncation is not injective and not
prefix-free, but its minimal elements carry at least as much mass.  (This is the paper's `P_q(Γ₄ |
π) ≥ P_q(Γ₃ | π)`.) -/
theorem exists_prefixFree_mass (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (w : List Bool) (S U : Finset (List Bool)) (hS : PrefixFree S)
    (hcov : ∀ δ ∈ S, ∃ t ∈ U, t <+: δ) :
    ∃ T ⊆ U, PrefixFree T ∧
      ∑ δ ∈ S, CylinderMass.cond P w δ ≤ ∑ t ∈ T, CylinderMass.cond P w t := by
  classical
  set T : Finset (List Bool) := U.filter (fun t => ∀ u ∈ U, u <+: t → u = t) with hT
  have hTU : T ⊆ U := Finset.filter_subset _ _
  have hmin : ∀ t ∈ U, ∃ a ∈ T, a <+: t := by
    intro t ht
    have hne : (U.filter (fun u => u <+: t)).Nonempty := by
      rw [Finset.filter_nonempty_iff]
      exact ⟨t, ht, List.prefix_rfl⟩
    obtain ⟨a, ha, hamin⟩ := Finset.exists_min_image (U.filter (fun u => u <+: t))
      List.length hne
    rw [Finset.mem_filter] at ha
    refine ⟨a, ?_, ha.2⟩
    rw [hT, Finset.mem_filter]
    refine ⟨ha.1, fun u hu hua => ?_⟩
    have hu' : u ∈ U.filter (fun u => u <+: t) :=
      Finset.mem_filter.mpr ⟨hu, hua.trans ha.2⟩
    have hle := hamin u hu'
    exact List.IsPrefix.eq_of_length hua (le_antisymm (List.IsPrefix.length_le hua) hle)
  have hTpf : PrefixFree T := by
    refine (prefixFree_iff_one_sided _).mpr ?_
    intro a ha b hb hab habs
    rw [hT, Finset.mem_filter] at hb
    exact hab (hb.2 a (hTU ha) habs)
  have hcov2 : ∀ δ, δ ∈ S → ∃ a, a ∈ T ∧ a <+: δ := by
    intro δ hδ
    obtain ⟨t, ht, hpre⟩ := hcov δ hδ
    obtain ⟨a, ha, hapre⟩ := hmin t ht
    exact ⟨a, ha, hapre.trans hpre⟩
  set g : List Bool → List Bool :=
    fun δ => if h : δ ∈ S then Classical.choose (hcov2 δ h) else [] with hg
  have hg_eq : ∀ δ (h : δ ∈ S), g δ = Classical.choose (hcov2 δ h) := by
    intro δ h
    simp only [hg, dif_pos h]
  have hgT : ∀ δ (h : δ ∈ S), g δ ∈ T := by
    intro δ h
    rw [hg_eq δ h]
    exact (Classical.choose_spec (hcov2 δ h)).1
  have hgpre : ∀ δ (h : δ ∈ S), g δ <+: δ := by
    intro δ h
    rw [hg_eq δ h]
    exact (Classical.choose_spec (hcov2 δ h)).2
  have hdisj : (↑T : Set (List Bool)).PairwiseDisjoint
      (fun a => S.filter (fun δ => g δ = a)) := by
    intro a _ a' _ hne
    refine Finset.disjoint_left.mpr ?_
    intro δ hδ hδ'
    exact hne ((Finset.mem_filter.mp hδ).2.symm.trans (Finset.mem_filter.mp hδ').2)
  have hunion : T.biUnion (fun a => S.filter (fun δ => g δ = a)) = S := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro δ hδ
      obtain ⟨a, -, hδ'⟩ := Finset.mem_biUnion.mp hδ
      exact (Finset.mem_filter.mp hδ').1
    · intro δ hδ
      exact Finset.mem_biUnion.mpr ⟨g δ, hgT δ hδ, Finset.mem_filter.mpr ⟨hδ, rfl⟩⟩
  have hfib : ∑ a ∈ T, ∑ δ ∈ S.filter (fun δ => g δ = a), CylinderMass.cond P w δ
      = ∑ δ ∈ S, CylinderMass.cond P w δ := by
    rw [← Finset.sum_biUnion hdisj, hunion]
  refine ⟨T, hTU, hTpf, ?_⟩
  rw [← hfib]
  refine Finset.sum_le_sum fun a _ => ?_
  exact sum_cond_fibre_le P hP hn w a _ (hS.subset (Finset.filter_subset _ _)) fun δ hδ => by
    rw [← (Finset.mem_filter.mp hδ).2]
    exact hgpre δ (Finset.mem_filter.mp hδ).1

open scoped MeasureTheory

end LargeLetter

