/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.RauzyVeech.RichPath.CylinderMass

/-!
# The height functionals of a node, and the graded induction

The graded induction of the source in the cylinder-mass language of
`IETFree/RauzyVeech/RichPath/CylinderMass.lean`: `st P w = cs P w` is the height vector,
`CylinderMass.cond P w δ` the
conditional mass of `Δ(wδ)` over `Δ(w)`.

Proved here:

* the functionals `mmin s q = min_{b ∈ s} q b` and `Mk k q = max_{#s = k} mmin s q`, with
  `Mk_card` (`Mk (#α) = min`) and `le_Mk_one` (`Mk 1 = max`);
* `GradedStep P k Cb Cm` / `GradedStepMin P k Cb Cm` — the `k`-statement of the induction
  (a prefix-free family of definite mass, after which the state is `Cb`-balanced on `k` letters and
  the maximum has grown by at most `Cm`);
* `gradedStep_min` (the paper's `Γ₁`: pass to the subfamily where the minimum is attained on one
  fixed `A'`, losing the factor `1/#{k-subsets}`), `prefixFree_comp` and `sum_comp` (gluing composed
  families: the masses multiply), and `gradedStep_succ` (the `k → k+1` step, given `BalanceStep`).

`NodeHeight.BalanceStep P K` (the source's `Γ₂`–`Γ₄`: extend each path to a vertex whose row ends
outside `A'`, bound the `A'`-coordinates with Kerckhoff's lemma, and the final case analysis) is the
notion that `gradedStep_succ` takes as input; it is proved, for a suitable `K`, in
`IETFree/RauzyVeech/RichPath/InductionAssembly.lean`.


-/

-- section instances used in the proofs but not in every statement

open MeasureTheory Finset
open scoped BigOperators NNReal ENNReal

namespace NodeHeight

open IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. The functionals -/

/-- The minimum of a state over a finite set of letters (junk value `0` on the empty set). -/
noncomputable def mmin (s : Finset α) (q : α → ℝ) : ℝ :=
  if h : s.Nonempty then s.inf' h q else 0

omit [Fintype α] [DecidableEq α] in
theorem mmin_eq {s : Finset α} (h : s.Nonempty) (q : α → ℝ) : mmin s q = s.inf' h q :=
  dif_pos h

omit [Fintype α] [DecidableEq α] in
theorem mmin_le {s : Finset α} {q : α → ℝ} {b : α} (hb : b ∈ s) : mmin s q ≤ q b := by
  have h : s.Nonempty := ⟨b, hb⟩
  rw [mmin_eq h]
  exact Finset.inf'_le q hb

omit [Fintype α] [DecidableEq α] in
theorem le_mmin {s : Finset α} (hs : s.Nonempty) {q : α → ℝ} {c : ℝ}
    (h : ∀ b ∈ s, c ≤ q b) : c ≤ mmin s q := by
  rw [mmin_eq hs]
  exact Finset.le_inf' (f := q) hs h

omit [Fintype α] [DecidableEq α] in
theorem mmin_pos {s : Finset α} (hs : s.Nonempty) {q : α → ℝ} (hq : ∀ _b, 0 < q _b) :
    0 < mmin s q := by
  obtain ⟨b, hb, hb'⟩ := Finset.exists_mem_eq_inf' hs q
  rw [mmin_eq hs, hb']
  exact hq b

/-- `Mk k q` = `max_{#s = k} min_{b ∈ s} q b`: the source's `m_k(q)`.  For `k = 1` this is
`M(q) = max_b q b`; for `k = #α` it is `m(q) = min_b q b`.  Junk value `0` if `k > #α`. -/
noncomputable def Mk (k : ℕ) (q : α → ℝ) : ℝ :=
  if h : (Finset.univ.powersetCard k).Nonempty then
    (Finset.univ.powersetCard k).sup' h (fun s => mmin s q) else 0

omit [DecidableEq α] in
theorem Mk_eq {k : ℕ} (h : (Finset.univ.powersetCard k).Nonempty) (q : α → ℝ) :
    Mk k q = (Finset.univ.powersetCard k).sup' h (fun s => mmin s q) :=
  dif_pos h

omit [DecidableEq α] in
theorem mmin_le_Mk {s : Finset α} {k : ℕ} {q : α → ℝ} (hs : s.card = k) :
    mmin s q ≤ Mk k q := by
  have hmem : s ∈ Finset.univ.powersetCard k := by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ s, hs⟩
  have h : (Finset.univ.powersetCard k).Nonempty := ⟨s, hmem⟩
  rw [Mk_eq h]
  exact Finset.le_sup' (fun s => mmin s q) hmem

omit [DecidableEq α] in
theorem Mk_pos {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ Fintype.card α) {q : α → ℝ}
    (hq : ∀ b, 0 < q b) : 0 < Mk k q := by
  have hne : ((Finset.univ : Finset α).powersetCard k).Nonempty := by
    rw [Finset.powersetCard_nonempty]
    simpa using hk
  rw [Mk_eq hne]
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup' hne (fun s => mmin s q)
  have hscard : s.card = k := (Finset.mem_powersetCard.mp hs).2
  have hspos : 0 < mmin s q :=
    mmin_pos (Finset.card_pos.mp (by rw [hscard]; omega)) hq
  rw [hsup]
  exact hspos

omit [Fintype α] [DecidableEq α] in
theorem mmin_singleton (b : α) (q : α → ℝ) : mmin {b} q = q b := by
  have h : ({b} : Finset α).Nonempty := ⟨b, Finset.mem_singleton_self b⟩
  rw [mmin_eq h, Finset.inf'_singleton]

/-! ## 2. Prefix-free families and the induction statement -/

/-- A finite family of words is *prefix-free*: no two distinct elements are comparable for the
prefix order. -/
def PrefixFree (S : Finset (List Bool)) : Prop :=
  ∀ δ ∈ S, ∀ δ' ∈ S, δ <+: δ' → δ' <+: δ

theorem PrefixFree.subset {S T : Finset (List Bool)} (h : PrefixFree S) (hTS : T ⊆ S) :
    PrefixFree T :=
  fun δ hδ δ' hδ' hp => h δ (hTS hδ) δ' (hTS hδ') hp

theorem prefixFree_singleton (δ : List Bool) : PrefixFree {δ} := by
  intro u hu v hv _
  rw [Finset.mem_singleton] at hu hv
  rw [hu, hv]

/-- The state of the tower at the node `w`: the source's `q = B_w·1`, here the column sums. -/
noncomputable def st (P : IETDatum₂ α n) (w : List Bool) : α → ℝ :=
  fun b => ColShrink.cs P w b

theorem st_pos (P : IETDatum₂ α n) (w : List Bool) (b : α) : 0 < st P w b :=
  ColShrink.cs_pos P w b

theorem st_nonneg (P : IETDatum₂ α n) (w : List Bool) (b : α) : 0 ≤ st P w b :=
  le_of_lt (st_pos P w b)

omit [DecidableEq α] in
/-- The number of letters of the alphabet is positive, from the combinatorial data. -/
theorem card_pos (P : IETDatum₂ α n) : 1 ≤ Fintype.card α := by
  rw [Fintype.card_congr P.piTop, Fintype.card_fin]
  exact Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)

theorem Mk_st_pos (P : IETDatum₂ α n) (w : List Bool) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ Fintype.card α) : 0 < Mk k (st P w) :=
  Mk_pos hk1 hk (fun b => st_pos P w b)

/-- **The induction statement at level `k`**, in the cylinder-mass language: for every node `w`
there is a prefix-free family of continuations whose total relative mass is `> 1/Cm`, at the end of
each of which the state is `Cb`-balanced and its maximum is at most `Cb` times `min{m_k(q_w),
M(q_w)}`.  This is `P_q(M(B_γ·q) < C min{m_k(B_γ q), M(q)} | π) > C^{-1}` of the source, with the
probability replaced by the mass of a prefix-free family. -/
def GradedStep (P : IETDatum₂ α n) (k : ℕ) (Cb Cm : ℝ) : Prop :=
  ∀ w : List Bool, ∃ S : Finset (List Bool), PrefixFree S ∧
    (∀ δ ∈ S, Mk 1 (st P (w ++ δ)) <
      Cb * min (Mk k (st P (w ++ δ))) (Mk 1 (st P w))) ∧
    1 / Cm < ∑ δ ∈ S, CylinderMass.cond P w δ

/-- The same statement with the `k`-subset `A'` on which the minimum `m_k` is attained fixed
explicitly (the source's `Γ₁`: `m_{A'}(B_γ q) = m_k(B_γ q)` for all paths of the family). -/
def GradedStepMin (P : IETDatum₂ α n) (k : ℕ) (Cb Cm : ℝ) : Prop :=
  ∀ w : List Bool, ∃ A' : Finset α, A'.card = k ∧
    ∃ S : Finset (List Bool), PrefixFree S ∧
    (∀ δ ∈ S, Mk 1 (st P (w ++ δ)) <
      Cb * min (mmin A' (st P (w ++ δ))) (Mk 1 (st P w))) ∧
    1 / Cm < ∑ δ ∈ S, CylinderMass.cond P w δ

omit [DecidableEq α] in
/-- Every `k`-subset of the alphabet, seen in the finite type of all `k`-subsets. -/
theorem mem_powersetCard_univ {A' : Finset α} {k : ℕ} (h : A'.card = k) :
    A' ∈ (Finset.univ : Finset α).powersetCard k := by
  rw [Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ A', h⟩

omit [DecidableEq α] in
theorem powersetCard_univ_nonempty {k : ℕ} (hk : k ≤ Fintype.card α) :
    ((Finset.univ : Finset α).powersetCard k).Nonempty := by
  rw [Finset.powersetCard_nonempty]
  simpa using hk

omit [DecidableEq α] in
theorem powersetCard_univ_card_pos {k : ℕ} (hk : k ≤ Fintype.card α) :
    0 < (((Finset.univ : Finset α).powersetCard k).card : ℝ) := by
  have h := Finset.card_pos.mpr (powersetCard_univ_nonempty hk)
  exact_mod_cast h

/-- **The source's step `Γ₁`**: split the family of the `k`-statement according to which
`k`-subset `A'` attains `m_k = m_{A'}`; one piece keeps a fraction `1/#{k-subsets}` of the total
mass, and on that piece `m_k` *is* `m_{A'}`. -/
theorem gradedStep_min {P : IETDatum₂ α n} {k : ℕ} {Cb Cm : ℝ} (hst : GradedStep P k Cb Cm)
    (hk : k ≤ Fintype.card α) (hCm : 0 < Cm) :
    GradedStepMin P k Cb (Cm * (((Finset.univ : Finset α).powersetCard k).card : ℝ)) := by
  intro w
  obtain ⟨S, hpf, hb, hm⟩ := hst w
  have hchoice : ∀ δ ∈ S, ∃ A' : Finset α,
      A'.card = k ∧ Mk k (st P (w ++ δ)) = mmin A' (st P (w ++ δ)) := by
    intro δ _
    have hne : ((Finset.univ : Finset α).powersetCard k).Nonempty :=
      powersetCard_univ_nonempty hk
    obtain ⟨A', hA', hsup⟩ := Finset.exists_mem_eq_sup' hne (fun s => mmin s (st P (w ++ δ)))
    exact ⟨A', (Finset.mem_powersetCard.mp hA').2, by rw [Mk_eq hne, hsup]⟩
  set g : List Bool → Finset α :=
    fun δ => if hδ : δ ∈ S then Classical.choose (hchoice δ hδ) else ∅ with hg
  have hg_card : ∀ δ ∈ S, (g δ).card = k := by
    intro δ hδ
    simp only [hg, dif_pos hδ]
    exact (Classical.choose_spec (hchoice δ hδ)).1
  have hg_Mk : ∀ δ ∈ S, Mk k (st P (w ++ δ)) = mmin (g δ) (st P (w ++ δ)) := by
    intro δ hδ
    simp only [hg, dif_pos hδ]
    exact (Classical.choose_spec (hchoice δ hδ)).2
  have hg_mem : ∀ δ ∈ S, g δ ∈ (Finset.univ : Finset α).powersetCard k :=
    fun δ hδ => mem_powersetCard_univ (hg_card δ hδ)
  set Nk : ℝ := (((Finset.univ : Finset α).powersetCard k).card : ℝ) with hNk
  have hNk_pos : 0 < Nk := by
    rw [hNk]
    exact powersetCard_univ_card_pos hk
  set m : Finset α → ℝ := fun A' => ∑ δ ∈ S with g δ = A', CylinderMass.cond P w δ
    with hm_def
  have hsplit : ∑ A' ∈ (Finset.univ : Finset α).powersetCard k, m A'
      = ∑ δ ∈ S, CylinderMass.cond P w δ := by
    have hall : ∑ A' : Finset α, m A' = ∑ δ ∈ S, CylinderMass.cond P w δ :=
      Finset.sum_fiberwise S g (fun δ => CylinderMass.cond P w δ)
    refine (Finset.sum_subset (fun A' _ => Finset.mem_univ A') ?_).trans hall
    intro A' _ hA'
    have hempty : (S.filter fun δ => g δ = A') = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro δ hδ hEq
      exact hA' (hEq ▸ hg_mem δ hδ)
    simp only [hm_def, hempty, Finset.sum_empty]
  obtain ⟨A'₀, hA'₀, hmax⟩ :=
    Finset.exists_max_image ((Finset.univ : Finset α).powersetCard k) m
      (powersetCard_univ_nonempty hk)
  have hA'₀_card : A'₀.card = k := (Finset.mem_powersetCard.mp hA'₀).2
  have haverage : ∑ A' ∈ (Finset.univ : Finset α).powersetCard k, m A' ≤ Nk * m A'₀ := by
    have h1 : ∑ A' ∈ (Finset.univ : Finset α).powersetCard k, m A'
        ≤ ∑ A' ∈ (Finset.univ : Finset α).powersetCard k, m A'₀ :=
      Finset.sum_le_sum fun A' hA' => hmax A' hA'
    have h2 : ∑ _A' ∈ (Finset.univ : Finset α).powersetCard k, m A'₀ = Nk * m A'₀ := by
      rw [Finset.sum_const, hNk, nsmul_eq_mul]
    linarith
  have hmass : 1 / (Cm * Nk) < m A'₀ := by
    have h1 : 1 / Cm < Nk * m A'₀ := lt_of_lt_of_le hm (by rw [← hsplit]; exact haverage)
    have h2 : 1 / Cm * Cm < (Nk * m A'₀) * Cm := mul_lt_mul_of_pos_right h1 hCm
    have h3 : 1 / Cm * Cm = (1 : ℝ) := by field_simp
    rw [h3] at h2
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < Cm * Nk)]
    nlinarith [h2]
  refine ⟨A'₀, hA'₀_card, S.filter (fun δ => g δ = A'₀),
    hpf.subset (Finset.filter_subset _ _), ?_, ?_⟩
  · intro δ hδ
    obtain ⟨hδS, hgA⟩ := Finset.mem_filter.mp hδ
    have hMk : Mk k (st P (w ++ δ)) = mmin A'₀ (st P (w ++ δ)) := by
      rw [hg_Mk δ hδS, hgA]
    have hbnd := hb δ hδS
    rw [hMk] at hbnd
    exact hbnd
  · exact hmass

/-! ## 3. Composing prefix-free families (the gluing lemma) -/

theorem prefix_or_prefix_of_append {β : Type*} {a b c d : List β}
    (h : a ++ b <+: c ++ d) : a <+: c ∨ c <+: a := by
  induction a generalizing c with
  | nil => exact Or.inl List.nil_prefix
  | cons x a' ih =>
    cases c with
    | nil => exact Or.inr List.nil_prefix
    | cons y c' =>
      rw [List.cons_append, List.cons_append, List.cons_prefix_cons] at h
      obtain ⟨rfl, h'⟩ := h
      rcases ih h' with h2 | h2
      · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h2⟩)
      · exact Or.inr (List.cons_prefix_cons.mpr ⟨rfl, h2⟩)

theorem prefixFree_empty : PrefixFree (∅ : Finset (List Bool)) := by
  intro δ hδ
  exact absurd hδ (Finset.notMem_empty δ)

theorem eq_of_prefix_of_prefix {u v : List Bool} (h1 : u <+: v) (h2 : v <+: u) : u = v :=
  List.IsPrefix.eq_of_length h1 (le_antisymm (List.IsPrefix.length_le h1)
    (List.IsPrefix.length_le h2))

/-- The one-sided form of prefix-freeness used below. -/
theorem prefixFree_iff_one_sided (S : Finset (List Bool)) :
    PrefixFree S ↔ ∀ δ ∈ S, ∀ δ' ∈ S, δ ≠ δ' → ¬ δ <+: δ' := by
  constructor
  · intro h δ hδ δ' hδ' hne hp
    exact hne (eq_of_prefix_of_prefix hp (h δ hδ δ' hδ' hp))
  · intro h δ hδ δ' hδ' hp
    by_contra hcon
    exact h δ hδ δ' hδ' (fun hh => hcon (hh ▸ List.prefix_rfl)) hp

/-- Injectivity of `fun η => δ ++ η`. -/
theorem append_left_inj {δ : List Bool} : Function.Injective (fun η => δ ++ η) :=
  fun _ _ h => List.append_cancel_left h

/-- The word `δ ++ η` (with `δ ∈ S`, `η ∈ T δ`) determines `δ`. -/
theorem prefix_append_left_cancel {a b c : List Bool} (h : a ++ b <+: a ++ c) : b <+: c := by
  obtain ⟨t, ht⟩ := h
  rw [List.append_assoc] at ht
  exact ⟨t, List.append_cancel_left ht⟩

theorem append_prefix_append (a : List Bool) {b c : List Bool} (h : b <+: c) :
    a ++ b <+: a ++ c := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by rw [List.append_assoc, ht]⟩

/-- The word `δ ++ η` (with `δ ∈ S`, `η ∈ T δ`) determines `δ`. -/
theorem eq_of_append_eq_append {S : Finset (List Bool)} (hS : PrefixFree S) {δ δ' : List Bool}
    (hδ : δ ∈ S) (hδ' : δ' ∈ S) {η η' : List Bool} (h : δ ++ η = δ' ++ η') :
    δ = δ' := by
  have hpre0 : δ ++ η <+: δ' ++ η' := h ▸ List.prefix_rfl
  rcases prefix_or_prefix_of_append hpre0 with h2 | h2
  · exact eq_of_prefix_of_prefix h2 (hS δ hδ δ' hδ' h2)
  · exact (eq_of_prefix_of_prefix h2 (hS δ' hδ' δ hδ h2)).symm

/-- **Gluing of prefix-free families** is prefix-free. -/
theorem prefixFree_comp {S : Finset (List Bool)} {T : List Bool → Finset (List Bool)}
    (hS : PrefixFree S) (hT : ∀ δ, PrefixFree (T δ)) :
    PrefixFree (S.biUnion fun δ => (T δ).image (fun η => δ ++ η)) := by
  intro x hx y hy hxy
  rw [Finset.mem_biUnion] at hx hy
  obtain ⟨δ, hδ, hxδ⟩ := hx
  obtain ⟨δ', hδ', hyδ⟩ := hy
  rw [Finset.mem_image] at hxδ hyδ
  obtain ⟨η, hη, rfl⟩ := hxδ
  obtain ⟨η', hη', rfl⟩ := hyδ
  rcases prefix_or_prefix_of_append hxy with h2 | h2
  · have hEq : δ = δ' := eq_of_prefix_of_prefix h2 (hS δ hδ δ' hδ' h2)
    subst hEq
    have hηη' : η <+: η' := prefix_append_left_cancel hxy
    exact append_prefix_append δ (hT δ η hη η' hη' hηη')
  · have hEq : δ' = δ := eq_of_prefix_of_prefix h2 (hS δ' hδ' δ hδ h2)
    subst hEq
    have hηη' : η <+: η' := prefix_append_left_cancel hxy
    exact append_prefix_append δ' (hT δ' η hη η' hη' hηη')

/-- The mass of a glued family: the product of the masses (`cond_append` + disjointness). -/
theorem sum_comp {S : Finset (List Bool)} {T : List Bool → Finset (List Bool)}
    (hS : PrefixFree S) (P : IETDatum₂ α n) (w : List Bool) :
    ∑ x ∈ (S.biUnion fun δ => (T δ).image (fun η => δ ++ η)), CylinderMass.cond P w x
      = ∑ δ ∈ S, CylinderMass.cond P w δ * ∑ η ∈ T δ, CylinderMass.cond P (w ++ δ) η := by
  have hdisj : (↑S : Set (List Bool)).PairwiseDisjoint
      (fun δ => (T δ).image (fun η => δ ++ η)) := by
    intro δ hδ δ' hδ' hne
    refine Finset.disjoint_left.mpr ?_
    intro x hx hx'
    rw [Finset.mem_image] at hx hx'
    obtain ⟨η, -, rfl⟩ := hx
    obtain ⟨η', -, hEq⟩ := hx'
    exact hne (eq_of_append_eq_append hS hδ hδ' hEq.symm)
  rw [Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [Finset.sum_image (f := fun x => CylinderMass.cond P w x) (g := fun η => δ ++ η)
    (fun η _ η' _ h => append_left_inj h), Finset.mul_sum]
  exact Finset.sum_congr rfl fun η _ => CylinderMass.cond_append P w δ η

/-- The two arrows at a node carry total mass `1` (their relative masses add up). -/
theorem cond_arrow_sum (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) (w : List Bool) :
    CylinderMass.cond P w [true] + CylinderMass.cond P w [false] = 1 := by
  have hTF : (P.vertex w).last true ≠ (P.vertex w).last false :=
    vertex_last_ne P hP hn w
  have hF : CylinderMass.cond P w [false]
      = ColShrink.cs P w ((P.vertex w).last true) /
        (ColShrink.cs P w ((P.vertex w).last true) + ColShrink.cs P w ((P.vertex w).last false)) :=
    CylinderMass.cond_arrow P hP hn w false
  have ht : CylinderMass.cond P w [true]
      = ColShrink.cs P w ((P.vertex w).last false) /
        (ColShrink.cs P w ((P.vertex w).last false) + ColShrink.cs P w ((P.vertex w).last true)) :=
    CylinderMass.cond_arrow P hP hn w true
  have h1 : ColShrink.cs P w ((P.vertex w).last true) ≠ 0 := ColShrink.cs_ne_zero P w _
  have h2 : ColShrink.cs P w ((P.vertex w).last false) ≠ 0 := ColShrink.cs_ne_zero P w _
  have h3 : ColShrink.cs P w ((P.vertex w).last false)
      + ColShrink.cs P w ((P.vertex w).last true) ≠ 0 :=
    ne_of_gt (add_pos (ColShrink.cs_pos P w _) (ColShrink.cs_pos P w _))
  have h4 : ColShrink.cs P w ((P.vertex w).last true)
      + ColShrink.cs P w ((P.vertex w).last false) ≠ 0 :=
    ne_of_gt (add_pos (ColShrink.cs_pos P w _) (ColShrink.cs_pos P w _))
  rw [ht, hF, div_add_div _ _ h3 h4, add_comm (ColShrink.cs P w ((P.vertex w).last true))]
  field_simp

/-! ## 4. The balance step (`Γ₂`--`Γ₄` of the source) and the induction step -/

/-- **The balance step of the source (`Γ₂`--`Γ₄`), as a hypothesis.**  **NOTE**: the conclusion
below used to be the *conjunctive* form (all of `insert θ A'` at height `≥ (1/K Cb)·M(q_η)`, and
`M(q_η) ≤ K Cb·M(q_w)`), which is FALSE: a machine-checked counterexample shows that along the
periodic path `(false,true,true)` at `(top (0,1,2,3), bottom (1,3,0,2))` with `A' = {0,2,3}` both
rows end inside `A'` for ever, so a letter outside `A'` can stay frozen while the others grow.  The
paper absorbs that case in the `min{…, 𝔐(q)}` clause, and the definition below now has exactly that
shape (the shape of `GradedStep`).  Let `A'` be a set of `k < #α` letters whose heights `q_α` at the
node `w` are all at least `(1/Cb)·M(q)` (the conclusion of the `k`-statement at the end of a path of
the family `Γ₁`). Then there is a prefix-free family of continuations of total mass `> 1/C` at the
end of each of which there is a *new* letter `θ ∉ A'` with `M(q_η) ≤ K Cb · min{m_{A'∪{θ}}(q_η),
M(q_w)}` — i.e. **both** the maximum is at most `K Cb` times the `(k+1)`-minimum on `A' ∪ {θ}`
**and** it has not grown by more than `K Cb` (the `min` is compact notation for the conjunction; it
is *not* a disjunction).  This is the paper's chain `Γ₂` (extend to a vertex with a row ending
outside `A'`), `Γ₃` (Kerckhoff bounds the `A'`-coordinates) and `Γ₄` (a new large letter appears).
It is **not proved here**: it is discharged, for a suitable `K`, in `InductionAssembly.lean`
(`Assemble.balanceStep_of_straddleMass`).  Everything after it — the induction from `k` to `k+1`,
the gluing of the families, and the base case — is proved in this file. -/
def BalanceStep (P : IETDatum₂ α n) (K : ℝ → ℝ) : Prop :=
  ∀ (Cb : ℝ), 1 ≤ Cb → ∀ (k : ℕ) (A' : Finset α) (w : List Bool),
    A'.card = k → k < Fintype.card α →
    (∀ b ∈ A', (1 / Cb) * Mk 1 (st P w) ≤ st P w b) →
    ∃ T : Finset (List Bool), PrefixFree T ∧
      1 / K Cb < ∑ η ∈ T, CylinderMass.cond P w η ∧
      ∀ η ∈ T, ∃ θ : α, θ ∉ A' ∧
        Mk 1 (st P (w ++ η)) ≤
          K Cb * min (mmin (insert θ A') (st P (w ++ η))) (Mk 1 (st P w))

/-- **The induction step `k → k+1`**, given the balance step: the `k`-statement with the minimum
attained on a fixed `A'` (`GradedStepMin`, the source's `Γ₁`) and `BalanceStep` give the
`(k+1)`-statement. The mass loses the factor `K Cb` of the balance step; the balance constant
becomes `2·(K Cb)·Cb` — the `K Cb` of the balance step, the `Cb` left over when the `min` clause is
*not* the binding one (`M(q_η) < Cb·M(q_w)`), and the `2` the slack turning the resulting `≤` into
the `<` of `GradedStep`. -/
theorem gradedStep_succ {P : IETDatum₂ α n} {K : ℝ → ℝ} {Cb Cm : ℝ} (hbal : BalanceStep P K) {k : ℕ}
    (hst : GradedStepMin P k Cb Cm) (hk : k < Fintype.card α) (hCb : 1 ≤ Cb) (hCm : 0 < Cm)
    (hC : 1 ≤ K Cb) : GradedStep P (k + 1) (2 * K Cb * Cb) (Cm * K Cb) := by
  intro w
  obtain ⟨A', hA'card, S, hpf, hb, hm⟩ := hst w
  have hCpos : 0 < K Cb := by linarith
  have hprem : ∀ δ ∈ S, ∀ b ∈ A',
      (1 / Cb) * Mk 1 (st P (w ++ δ)) ≤ st P (w ++ δ) b := by
    intro δ hδ b hbA
    have h1 := hb δ hδ
    have h2 : min (mmin A' (st P (w ++ δ))) (Mk 1 (st P w)) ≤ st P (w ++ δ) b :=
      le_trans (min_le_left _ _) (mmin_le hbA)
    have h3 : Mk 1 (st P (w ++ δ)) ≤ Cb * st P (w ++ δ) b :=
      le_of_lt (lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_left h2 (by linarith)))
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith : (0 : ℝ) < Cb)]
    linarith
  have hex : ∀ δ ∈ S, ∃ T : Finset (List Bool), PrefixFree T ∧
      1 / K Cb < ∑ η ∈ T, CylinderMass.cond P (w ++ δ) η ∧
      ∀ η ∈ T, ∃ θ : α, θ ∉ A' ∧
        Mk 1 (st P ((w ++ δ) ++ η)) ≤
          K Cb * min (mmin (insert θ A') (st P ((w ++ δ) ++ η))) (Mk 1 (st P (w ++ δ))) :=
    fun δ hδ => hbal Cb hCb k A' (w ++ δ) hA'card hk (hprem δ hδ)
  set T : List Bool → Finset (List Bool) :=
    fun δ => if hδ : δ ∈ S then Classical.choose (hex δ hδ) else ∅ with hT
  have hT_pf : ∀ δ, PrefixFree (T δ) := by
    intro δ
    by_cases hδ : δ ∈ S
    · rw [hT]; simp only [dif_pos hδ]
      exact (Classical.choose_spec (hex δ hδ)).1
    · rw [hT]; simp only [dif_neg hδ]
      exact prefixFree_empty
  have hT_mass : ∀ δ ∈ S, 1 / K Cb < ∑ η ∈ T δ, CylinderMass.cond P (w ++ δ) η := by
    intro δ hδ
    rw [hT]; simp only [dif_pos hδ]
    exact (Classical.choose_spec (hex δ hδ)).2.1
  have hT_wit : ∀ δ ∈ S, ∀ η ∈ T δ, ∃ θ : α, θ ∉ A' ∧
      Mk 1 (st P ((w ++ δ) ++ η)) ≤
        K Cb * min (mmin (insert θ A') (st P ((w ++ δ) ++ η))) (Mk 1 (st P (w ++ δ))) := by
    intro δ hδ η hη
    rw [hT] at hη
    simp only [dif_pos hδ] at hη
    exact (Classical.choose_spec (hex δ hδ)).2.2 η hη
  refine ⟨S.biUnion fun δ => (T δ).image (fun η => δ ++ η),
    prefixFree_comp hpf hT_pf, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨δ, hδ, hxδ⟩ := hx
    rw [Finset.mem_image] at hxδ
    obtain ⟨η, hη, rfl⟩ := hxδ
    obtain ⟨θ, hθA, hθM⟩ := hT_wit δ hδ η hη
    rw [← List.append_assoc]
    set Mx := Mk 1 (st P ((w ++ δ) ++ η)) with hMx
    have hMx_pos : 0 < Mx := Mk_st_pos P _ le_rfl (card_pos P)
    have hcard : (insert θ A').card = k + 1 := by
      rw [Finset.card_insert_of_notMem hθA, hA'card]
    have hmk : mmin (insert θ A') (st P ((w ++ δ) ++ η))
        ≤ Mk (k + 1) (st P ((w ++ δ) ++ η)) := mmin_le_Mk hcard
    have hMk_nn : (0 : ℝ) ≤ Mk (k + 1) (st P ((w ++ δ) ++ η)) :=
      le_of_lt (Mk_st_pos P _ (by omega) (by omega))
    have hCb_inv : (1 : ℝ) / Cb ≤ 1 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < Cb)]
      linarith
    have hMδ : Mk 1 (st P (w ++ δ)) < Cb * Mk 1 (st P w) := by
      have hbnd := hb δ hδ
      have hle : Cb * min (mmin A' (st P (w ++ δ))) (Mk 1 (st P w))
          ≤ Cb * Mk 1 (st P w) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
      linarith
    have hM : Mx ≤ K Cb * Cb * Mk 1 (st P w) := by
      have h3 : K Cb * Mk 1 (st P (w ++ δ)) ≤ K Cb * (Cb * Mk 1 (st P w)) :=
        mul_le_mul_of_nonneg_left (le_of_lt hMδ) (le_of_lt hCpos)
      calc Mx ≤ K Cb * min (mmin (insert θ A') (st P ((w ++ δ) ++ η)))
            (Mk 1 (st P (w ++ δ))) := hθM
        _ ≤ K Cb * Mk 1 (st P (w ++ δ)) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (le_of_lt hCpos)
        _ ≤ K Cb * (Cb * Mk 1 (st P w)) := h3
        _ = K Cb * Cb * Mk 1 (st P w) := by ring
    have hbnd : (1 / ((K Cb) * Cb)) * Mx ≤ Mk 1 (st P w) := by
      have h1 : (1 / ((K Cb) * Cb)) * Mx
          ≤ (1 / ((K Cb) * Cb)) * ((K Cb) * Cb * Mk 1 (st P w)) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      have h2 : (1 / ((K Cb) * Cb)) * ((K Cb) * Cb * Mk 1 (st P w)) = Mk 1 (st P w) := by
        field_simp
      linarith
    have hmin_lb : (1 / ((K Cb) * Cb)) * Mx
        ≤ min (Mk (k + 1) (st P ((w ++ δ) ++ η))) (Mk 1 (st P w)) := by
      refine le_min ?_ hbnd
      by_cases hcase : mmin (insert θ A') (st P ((w ++ δ) ++ η)) ≤ Mk 1 (st P (w ++ δ))
      · have h1 : Mx ≤ K Cb * Mk (k + 1) (st P ((w ++ δ) ++ η)) := by
          calc Mx ≤ K Cb * min (mmin (insert θ A') (st P ((w ++ δ) ++ η)))
                (Mk 1 (st P (w ++ δ))) := hθM
            _ = K Cb * mmin (insert θ A') (st P ((w ++ δ) ++ η)) := by rw [min_eq_left hcase]
            _ ≤ K Cb * Mk (k + 1) (st P ((w ++ δ) ++ η)) :=
                mul_le_mul_of_nonneg_left hmk (le_of_lt hCpos)
        have h2 : (1 / ((K Cb) * Cb)) * (K Cb * Mk (k + 1) (st P ((w ++ δ) ++ η)))
            = (1 / Cb) * Mk (k + 1) (st P ((w ++ δ) ++ η)) := by
          field_simp
        have h3 : (1 / Cb) * Mk (k + 1) (st P ((w ++ δ) ++ η))
            ≤ Mk (k + 1) (st P ((w ++ δ) ++ η)) :=
          mul_le_of_le_one_left hMk_nn hCb_inv
        calc (1 / ((K Cb) * Cb)) * Mx
            ≤ (1 / ((K Cb) * Cb)) * (K Cb * Mk (k + 1) (st P ((w ++ δ) ++ η))) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = (1 / Cb) * Mk (k + 1) (st P ((w ++ δ) ++ η)) := h2
          _ ≤ Mk (k + 1) (st P ((w ++ δ) ++ η)) := h3
      · have hlt : Mk 1 (st P (w ++ δ)) < mmin (insert θ A') (st P ((w ++ δ) ++ η)) :=
          lt_of_not_ge hcase
        have h1 : Mx ≤ K Cb * Mk 1 (st P (w ++ δ)) := by
          calc Mx ≤ K Cb * min (mmin (insert θ A') (st P ((w ++ δ) ++ η)))
                (Mk 1 (st P (w ++ δ))) := hθM
            _ = K Cb * Mk 1 (st P (w ++ δ)) := by rw [min_eq_right (le_of_lt hlt)]
        have h2 : (1 / ((K Cb) * Cb)) * (K Cb * Mk 1 (st P (w ++ δ)))
            = (1 / Cb) * Mk 1 (st P (w ++ δ)) := by
          field_simp
        have h3 : (1 / Cb) * Mk 1 (st P (w ++ δ)) ≤ Mk 1 (st P (w ++ δ)) :=
          mul_le_of_le_one_left (le_of_lt (Mk_st_pos P _ le_rfl (card_pos P))) hCb_inv
        have h4 : (1 / ((K Cb) * Cb)) * Mx ≤ Mk 1 (st P (w ++ δ)) := by
          calc (1 / ((K Cb) * Cb)) * Mx
              ≤ (1 / ((K Cb) * Cb)) * (K Cb * Mk 1 (st P (w ++ δ))) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = (1 / Cb) * Mk 1 (st P (w ++ δ)) := h2
            _ ≤ Mk 1 (st P (w ++ δ)) := h3
        linarith
    have hmain : (2 * (K Cb) * Cb) * ((1 / ((K Cb) * Cb)) * Mx) = 2 * Mx := by
      field_simp
    have hstep : (2 * (K Cb) * Cb) * ((1 / ((K Cb) * Cb)) * Mx)
        ≤ (2 * (K Cb) * Cb) * min (Mk (k + 1) (st P ((w ++ δ) ++ η))) (Mk 1 (st P w)) :=
      mul_le_mul_of_nonneg_left hmin_lb (by positivity)
    rw [hmain] at hstep
    linarith
  · have hSne : S.Nonempty := by
      rcases Finset.eq_empty_or_nonempty S with rfl | h
      · rw [Finset.sum_empty] at hm
        have : (0 : ℝ) < 1 / Cm := by positivity
        linarith
      · exact h
    rw [sum_comp hpf P w]
    have h1 : ∀ δ ∈ S, CylinderMass.cond P w δ * (1 / (K Cb))
        ≤ CylinderMass.cond P w δ * ∑ η ∈ T δ, CylinderMass.cond P (w ++ δ) η :=
      fun δ hδ => mul_le_mul_of_nonneg_left (le_of_lt (hT_mass δ hδ))
        (le_of_lt (CylinderMass.cond_pos P w δ))
    obtain ⟨δ₀, hδ₀⟩ := hSne
    have h2 : CylinderMass.cond P w δ₀ * (1 / (K Cb))
        < CylinderMass.cond P w δ₀ * ∑ η ∈ T δ₀, CylinderMass.cond P (w ++ δ₀) η :=
      mul_lt_mul_of_pos_left (hT_mass δ₀ hδ₀) (CylinderMass.cond_pos P w δ₀)
    have hsum : ∑ δ ∈ S, CylinderMass.cond P w δ * (1 / (K Cb))
        < ∑ δ ∈ S, CylinderMass.cond P w δ * ∑ η ∈ T δ, CylinderMass.cond P (w ++ δ) η :=
      Finset.sum_lt_sum h1 ⟨δ₀, hδ₀, h2⟩
    have h3 : ∑ δ ∈ S, CylinderMass.cond P w δ * (1 / (K Cb))
        = (1 / (K Cb)) * ∑ δ ∈ S, CylinderMass.cond P w δ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun δ _ => by ring
    have h4 : (1 / (K Cb)) * (1 / Cm) < (1 / (K Cb)) * ∑ δ ∈ S, CylinderMass.cond P w δ :=
      mul_lt_mul_of_pos_left hm (by positivity)
    have h5 : 1 / (Cm * (K Cb)) = (1 / (K Cb)) * (1 / Cm) := by
      field_simp
    rw [h5]
    linarith [hsum, h3, h4]

omit [DecidableEq α] in
/-- `Mk 1` dominates every value of the state. -/
theorem le_Mk_one {q : α → ℝ} (b : α) : q b ≤ Mk 1 q := by
  have h : ({b} : Finset α).card = 1 := Finset.card_singleton b
  calc q b = mmin {b} q := (mmin_singleton b q).symm
    _ ≤ Mk 1 q := mmin_le_Mk h

omit [DecidableEq α] in
/-- For `k = #α`, `m_k` is the minimum over the whole alphabet. -/
theorem Mk_card (q : α → ℝ) :
    Mk (Fintype.card α) q = mmin (Finset.univ : Finset α) q := by
  have hne : ((Finset.univ : Finset α).powersetCard (Fintype.card α)).Nonempty := by
    rw [Finset.powersetCard_nonempty]
    simp
  have hle : Mk (Fintype.card α) q ≤ mmin (Finset.univ : Finset α) q := by
    rw [Mk_eq hne, Finset.sup'_le_iff]
    intro s hs
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hs
    have hsu : s = (Finset.univ : Finset α) :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_univ, ← hcard])
    rw [hsu]
  have hge : mmin (Finset.univ : Finset α) q ≤ Mk (Fintype.card α) q := by
    refine mmin_le_Mk (k := Fintype.card α) ?_
    simp
  linarith

/-- The statement is monotone in its two constants. -/
theorem gradedStep_const_mono {P : IETDatum₂ α n} {k : ℕ} {Cb Cb' Cm Cm' : ℝ}
    (h : GradedStep P k Cb Cm) (hk1 : 1 ≤ k) (hk : k ≤ Fintype.card α) (hCb : Cb ≤ Cb')
    (hCmpos : 0 < Cm) (hCm : Cm ≤ Cm') : GradedStep P k Cb' Cm' := by
  intro w
  obtain ⟨S, hpf, hb, hm⟩ := h w
  refine ⟨S, hpf, fun δ hδ => ?_, ?_⟩
  · have hpos : 0 < min (Mk k (st P (w ++ δ))) (Mk 1 (st P w)) :=
      lt_min (Mk_st_pos P _ hk1 hk) (Mk_st_pos P w le_rfl (card_pos P))
    calc Mk 1 (st P (w ++ δ)) < Cb * min (Mk k (st P (w ++ δ))) (Mk 1 (st P w)) := hb δ hδ
      _ ≤ Cb' * min (Mk k (st P (w ++ δ))) (Mk 1 (st P w)) :=
          mul_le_mul_of_nonneg_right hCb (le_of_lt hpos)
  · exact lt_of_le_of_lt (one_div_le_one_div_of_le hCmpos hCm) hm

/-! ## 5. From masses to volumes -/

/-- A prefix-free family satisfies the one-sided antichain condition of
`BalancedCylinders.volume_iUnion_antichain`. -/
theorem PrefixFree.antichain {S : Finset (List Bool)} (hS : PrefixFree S) :
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ u <+: v := by
  intro u hu v hv huv hpre
  exact huv (eq_of_prefix_of_prefix hpre (hS u hu v hv hpre))

/-- **Mass to volume**: if a prefix-free family of continuations of `w` has total relative mass `>
1/C`, then the union of the corresponding child cylinders carries at least a fraction `1/C` of the
mass of `Δ(w)`. (`BalancedCylinders.volume_iUnion_antichain` for additivity, `cond` for the
individual masses.) -/
theorem volume_union_ge (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {C : ℝ}
    {S : Finset (List Bool)} (hS : PrefixFree S) (w : List Bool)
    (hm : 1 / C < ∑ δ ∈ S, CylinderMass.cond P w δ) :
    ENNReal.ofReal (1 / C) * simplexVolumeOn α (IETDatum₂.simplexCyl P w)
      ≤ simplexVolumeOn α (⋃ δ ∈ S, IETDatum₂.simplexCyl P (w ++ δ)) := by
  rw [BalancedCylinders.volume_iUnion_antichain P hP hn w S hS.antichain]
  have hterm : ∀ δ ∈ S, simplexVolumeOn α (IETDatum₂.simplexCyl P (w ++ δ))
      = ENNReal.ofReal (CylinderMass.cond P w δ) * simplexVolumeOn α (IETDatum₂.simplexCyl P w) :=
    fun δ _ => CylinderMass.volume_append_eq_cond P w δ
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
    ← ENNReal.ofReal_sum_of_nonneg (fun δ _ => le_of_lt (CylinderMass.cond_pos P w δ))]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_of_lt hm))
    (simplexVolumeOn α (IETDatum₂.simplexCyl P w))

end NodeHeight

