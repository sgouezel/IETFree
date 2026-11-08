/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.RichPath.HeightDichotomy
public import IETFree.RauzyVeech.RichPath.LevelMass
public import IETFree.RauzyVeech.RichPath.StraddleMass

/-!
# `Γ₂`'s mass constant made dependent on the balance constant of the node

`ExtMassGen P M C₂` is the `Γ₂` step of the assembly with an arbitrary mass constant
`M : ℝ → ℝ`: the exit family `E` of the node satisfies `1/(M Cb) < ∑ η ∈ E, cond P w η`, where
`Cb = 𝔐(q_w)/𝔪_{A'}(q_w)` is the balance constant of the node (`M = fun _ => C₂` recovers the
constant form, which is false; the exit family's mass decays like `Cb⁻²`).

`balanceConstant M C₂ Cb = 4·#α·C₂²·Cb + (2·M Cb + 1)` is the resulting balance constant, positive
and large (`one_lt_balanceConstant`, `two_mul_lt_balanceConstant`, `le_balanceConstant`), and
`balanceStep_of_extMassGen` is the constant
chase of the balance step with `1/C₂` replaced by `1/(M Cb)` throughout: since
`BalanceStep` takes an arbitrary `K : ℝ → ℝ`, nothing else moves. `one_div_mul_two_eq` is
the elementary arithmetic used in the chase. -/

open Finset IntervalExchange.IETDatum₂
open scoped BigOperators

@[expose] public section

namespace IntervalExchange.RauzyVeech.RichPath

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Piece B with an arbitrary mass constant -/

/-- **Piece B (`Γ₂`) with the mass constant `M : ℝ → ℝ`.**  The mass bound is `1/(M Cb) < ∑ η ∈ T,
cond P w η`: the reciprocal of the mass is not a constant but an arbitrary function of the balance
constant `Cb` of the node (the constant case is `M = fun _ => C₂`).  The growth bound keeps a
*constant* `C₂` (the diagram constant `2^L + 1`, `L` the diameter of the Rauzy diagram): it is what
`dichotomy` consumes as `hC2bd`. -/
def ExtMassGen (P : IETDatum₂ α n) (M : ℝ → ℝ) (C2 : ℝ) : Prop :=
  ∀ (Cb : ℝ), 1 ≤ Cb → ∀ (k : ℕ) (A' : Finset α) (w : List Bool),
    A'.card = k → k < Fintype.card α → A'.Nonempty →
    (∀ b ∈ A', (1 / Cb) * mkMass 1 (colSum P w) ≤ colSum P w b) →
    ∃ T : Finset (List Bool), PrefixFree T ∧
      1 / (M Cb) < ∑ η ∈ T, cond P w η ∧
      ∀ η ∈ T, (∃ e : Bool, (P.vertex (w ++ η)).last e ∉ A') ∧
        mkMass 1 (colSum P (w ++ η)) ≤ C2 * mkMass 1 (colSum P w)

/-! ## 2. The balance constant -/

/-- The balance constant of the assembly, at mass constant `M`: the `Γ₄` constant `4·#α·C₀·C₂` (with
`C₀ = C₂·Cb` the `A'`-balance at the `Γ₂`-endpoint) plus the mass `1/(2·M Cb)` of `Γ₂·Γ₃`, plus `1`
of slack turning the two `≤` into the strict inequalities `BalanceStep` asks for. This is the
balance constant of the assembly with `C₂` replaced by `M Cb`. -/
def balanceConstant (M : ℝ → ℝ) (C2 : ℝ) : ℝ → ℝ :=
  fun Cb => 4 * (Fintype.card α : ℝ) * C2 * C2 * Cb + (2 * M Cb + 1)

omit [DecidableEq α] in
theorem one_lt_balanceConstant {M : ℝ → ℝ} {C2 Cb : ℝ} (hMpos : 0 < M Cb) (hC2 : 0 ≤ C2)
    (hCb : 1 ≤ Cb) : 1 < balanceConstant (α := α) M C2 Cb := by
  have h1 : (0 : ℝ) ≤ 4 * (Fintype.card α : ℝ) * C2 * C2 * Cb := by positivity
  simp only [balanceConstant]
  nlinarith

omit [DecidableEq α] in
theorem two_mul_lt_balanceConstant {M : ℝ → ℝ} {C2 Cb : ℝ} (hC2 : 0 ≤ C2) (hCb : 0 ≤ Cb) :
    M Cb * 2 < balanceConstant (α := α) M C2 Cb := by
  have h1 : (0 : ℝ) ≤ 4 * (Fintype.card α : ℝ) * C2 * C2 * Cb := by positivity
  simp only [balanceConstant]
  nlinarith

omit [DecidableEq α] in
theorem le_balanceConstant {M : ℝ → ℝ} {C2 Cb : ℝ} (hMpos : 0 < M Cb) :
    4 * (Fintype.card α : ℝ) * (C2 * Cb) * C2 ≤ balanceConstant (α := α) M C2 Cb := by
  have h1 : (0 : ℝ) ≤ 2 * M Cb + 1 := by linarith
  simp only [balanceConstant]
  nlinarith

/-- A numerical identity used in the mass bookkeeping. -/
theorem one_div_mul_two_eq {x : ℝ} (hx : x ≠ 0) : 1 / (x * 2) = 1 / 2 * (1 / x) := by
  field_simp

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 3. The balance step with the repaired mass constant -/

/-- **The assembly with an arbitrary mass constant.**  `BalanceStep` (AGY's
`Γ₂`--`Γ₄`) follows from the mass estimate `ExtMassGen` with constant `M` and the `Γ₃` mass estimate
(spelled out in the signature), with balance constant `balanceConstant M C₂`.  The proof is the
balance
step's, character for character, with `1/C₂` replaced by `1/(M Cb)` (hence `2·C₂` by `2·M Cb` in the
constant): `Γ₂` gives a family of mass `> 1/(M Cb)`; at each of its endpoints `w ++ η` the
`A'`-balance is `C₂·Cb` (`bal_of_growth`) and `Γ₃` gives a family of mass `> 1/2`; the composed
family has mass `>
1/(2·M Cb)` (`sum_comp`), each composed word has a prefix `γ₁` reaching a new large
letter (`dichotomy`), and `exists_prefixFree_mass` replaces the family
by its minimal elements, which loses no mass. -/
theorem balanceStep_of_extMassGen (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {M : ℝ → ℝ} {C2 : ℝ} (hC2 : 1 ≤ C2) (hM : ∀ Cb : ℝ, 1 ≤ Cb → 0 < M Cb)
    (hB : ExtMassGen P M C2)
    (hG :
    ∀ (Cb : ℝ), 1 ≤ Cb → ∀ (k : ℕ) (A' : Finset α) (w : List Bool),
      A'.card = k → k < Fintype.card α → A'.Nonempty →
      (∀ b ∈ A', (1 / Cb) * mkMass 1 (colSum P w) ≤ colSum P w b) →
      (∃ e : Bool, (P.vertex w).last e ∉ A') →
      ∃ T : Finset (List Bool), PrefixFree T ∧
        1 / 2 < ∑ η ∈ T, cond P w η ∧
        ∀ η ∈ T, ∃ (ν : List Bool) (e : Bool), η = ν ++ [e] ∧
          (((P.vertex (w ++ ν)).last e ∈ A' ∧ (P.vertex (w ++ ν)).last (!e) ∉ A')
            ∨ 2 * (Fintype.card α : ℝ) * mkMass 1 (colSum P w)
                < mkMass 1 (colSum P (w ++ η))) ∧
          (∀ b ∈ A', colSum P (w ++ η) b
            ≤ 2 * (Fintype.card α : ℝ) * mkMass 1 (colSum P w))) :
    BalanceStep P (balanceConstant (α := α) M C2) := by
  intro Cb hCb k A' w hk hklt hbal
  have hMpos : (0 : ℝ) < M Cb := hM Cb hCb
  have hCbpos : (0 : ℝ) < Cb := by linarith
  rcases Finset.eq_empty_or_nonempty A' with hemp | hne
  · -- `A' = ∅`: the node itself, with a letter of maximal height
    subst hemp
    obtain ⟨θ, hθ⟩ := exists_eq_Mk_one (colSum P w) (P.card_pos)
    have hlt := one_lt_balanceConstant (α := α) (M := M) (C2 := C2) (Cb := Cb) hMpos
      (by linarith : (0 : ℝ) ≤ C2) hCb
    refine ⟨{[]}, prefixFree_singleton [], ?_, ?_⟩
    · rw [Finset.sum_singleton, cond_nil,
        div_lt_one (by linarith : (0 : ℝ) < balanceConstant (α := α) M C2 Cb)]
      simpa using hlt
    · intro η hη
      rw [Finset.mem_singleton] at hη
      subst hη
      refine ⟨θ, Finset.notMem_empty θ, ?_⟩
      have hMk_pos : (0 : ℝ) < mkMass 1 (colSum P w) :=
        mkMass_colSum_pos P w le_rfl (P.card_pos)
      simp only [List.append_nil, Finset.insert_empty, mmin_singleton, hθ, min_self]
      exact le_mul_of_one_le_left (le_of_lt hMk_pos) (le_of_lt hlt)
  -- `Γ₂` at the node `w`
  obtain ⟨T2, hT2pf, hT2mass, hT2data⟩ := hB Cb hCb k A' w hk hklt hne hbal
  -- the `A'`-balance at the `Γ₂`-endpoints
  have hbal' (η) (hη : η ∈ T2) : ∀ b ∈ A',
      (1 / (C2 * Cb)) * mkMass 1 (colSum P (w ++ η)) ≤ colSum P (w ++ η) b :=
    bal_of_growth P hC2 hCb (w' := w ++ η) hbal
      (fun b => state_mono P w η b) (hT2data η hη).2
  -- the `Γ₃` family at each `Γ₂`-endpoint
  have hexG : ∀ η ∈ T2, ∃ F : Finset (List Bool), PrefixFree F ∧
      1 / 2 < ∑ δ ∈ F, cond P (w ++ η) δ ∧
      ∀ δ ∈ F, ∃ (ν : List Bool) (e : Bool), δ = ν ++ [e] ∧
        (((P.vertex ((w ++ η) ++ ν)).last e ∈ A'
            ∧ (P.vertex ((w ++ η) ++ ν)).last (!e) ∉ A')
          ∨ 2 * (Fintype.card α : ℝ) * mkMass 1 (colSum P (w ++ η))
              < mkMass 1 (colSum P ((w ++ η) ++ δ))) ∧
        (∀ b ∈ A', colSum P ((w ++ η) ++ δ) b
          ≤ 2 * (Fintype.card α : ℝ) * mkMass 1 (colSum P (w ++ η))) :=
    fun η hη => hG (C2 * Cb) (by nlinarith) k A' (w ++ η) hk hklt hne (hbal' η hη)
      (hT2data η hη).1
  set F : List Bool → Finset (List Bool) :=
    fun η => if h : η ∈ T2 then Classical.choose (hexG η h) else ∅ with hF
  have hF_spec (η) (h : η ∈ T2) : F η = Classical.choose (hexG η h) := by
    simp only [hF, dite_eq_left h]
  have hF_pf (η) : PrefixFree (F η) := by
    by_cases h : η ∈ T2
    · rw [hF_spec η h]
      exact (Classical.choose_spec (hexG η h)).1
    · simp only [hF, dite_eq_right h]
      exact prefixFree_empty
  have hF_mass (η) (h : η ∈ T2) :
      1 / 2 < ∑ δ ∈ F η, cond P (w ++ η) δ := by
    rw [hF_spec η h]
    exact (Classical.choose_spec (hexG η h)).2.1
  have hF_data (η) (h : η ∈ T2) (δ : List Bool) (hδ : δ ∈ F η) :
      ∃ (ν : List Bool) (e : Bool), δ = ν ++ [e] ∧
      (((P.vertex ((w ++ η) ++ ν)).last e ∈ A'
          ∧ (P.vertex ((w ++ η) ++ ν)).last (!e) ∉ A')
        ∨ 2 * (Fintype.card α : ℝ) * mkMass 1 (colSum P (w ++ η))
            < mkMass 1 (colSum P ((w ++ η) ++ δ))) ∧
      (∀ b ∈ A', colSum P ((w ++ η) ++ δ) b
        ≤ 2 * (Fintype.card α : ℝ) * mkMass 1 (colSum P (w ++ η))) := by
    rw [hF_spec η h] at hδ
    exact (Classical.choose_spec (hexG η h)).2.2 δ hδ
  -- the dichotomy (`Γ₄`) at every composed word
  have hdich (η) (hη : η ∈ T2) : ∀ δ ∈ F η, ∃ γ₁ : List Bool,
      η <+: γ₁ ∧ γ₁ <+: η ++ δ ∧
      ∃ θ : α, θ ∉ A' ∧ mkMass 1 (colSum P (w ++ γ₁)) ≤
        4 * (Fintype.card α : ℝ) * (C2 * Cb) * C2 *
          min (mmin (insert θ A') (colSum P (w ++ γ₁)))
            (mkMass 1 (colSum P w)) := by
    intro δ hδ
    obtain ⟨ν, e, hδeq, hlast, hbnd⟩ := hF_data η hη δ hδ
    subst hδeq
    obtain ⟨γ₁, hp1, hp2, θ, hθ, hbound⟩ :=
      dichotomy P hP hn w η ν e A' hne (by nlinarith) hC2 (hbal' η hη)
        (heights_bound_of_end P (w ++ η) (ν ++ [e]) A'
          (R := 2 * (Fintype.card α : ℝ) * mkMass 1 (colSum P (w ++ η))) hbnd)
        hlast (hT2data η hη).2
    exact ⟨γ₁, hp1, hp2, θ, hθ, hbound⟩
  set gam : List Bool → List Bool → List Bool :=
    fun η δ =>
      if h : η ∈ T2 ∧ δ ∈ F η then Classical.choose (hdich η h.1 δ h.2) else []
      with hgam
  have hgam_prop (η δ) (h : η ∈ T2 ∧ δ ∈ F η) :
      η <+: gam η δ ∧ gam η δ <+: η ++ δ ∧ ∃ θ : α, θ ∉ A' ∧
        mkMass 1 (colSum P (w ++ gam η δ)) ≤
          4 * (Fintype.card α : ℝ) * (C2 * Cb) * C2 *
            min (mmin (insert θ A') (colSum P (w ++ gam η δ)))
              (mkMass 1 (colSum P w)) := by
    simp only [hgam, dite_eq_left h]
    exact Classical.choose_spec (hdich η h.1 δ h.2)
  -- the composed family and its minimal elements
  set S : Finset (List Bool) := T2.biUnion (fun η => (F η).image (fun δ => η ++ δ)) with hS
  set U : Finset (List Bool) := T2.biUnion (fun η => (F η).image (fun δ => gam η δ)) with hU
  have hSpf : PrefixFree S := by
    rw [hS]
    exact prefixFree_comp hT2pf hF_pf
  have hSmass : ∑ x ∈ S, cond P w x =
      ∑ η ∈ T2, cond P w η * ∑ δ ∈ F η, cond P (w ++ η) δ := by
    rw [hS]
    exact sum_comp (T := F) hT2pf P w
  have hcov (x) (hx : x ∈ S) : ∃ t ∈ U, t <+: x := by
    rw [hS, Finset.mem_biUnion] at hx
    obtain ⟨η, hη, hx⟩ := hx
    rw [Finset.mem_image] at hx
    obtain ⟨δ, hδ, rfl⟩ := hx
    exact ⟨gam η δ, by
      rw [hU, Finset.mem_biUnion]
      exact ⟨η, hη, Finset.mem_image.mpr ⟨δ, hδ, rfl⟩⟩,
        (hgam_prop η δ ⟨hη, hδ⟩).2.1⟩
  obtain ⟨T, hTU, hTpf, hTmass⟩ := exists_prefixFree_mass P hP hn w S U hSpf hcov
  -- the mass of the composed family exceeds `1/(2·C₂)`
  have hT2ne : T2.Nonempty := by
    rcases Finset.eq_empty_or_nonempty T2 with h | h
    · rw [h, Finset.sum_empty] at hT2mass
      have : (0 : ℝ) < 1 / (M Cb) := by positivity
      linarith
    · exact h
  have hstep1 (η) (hη : η ∈ T2) : cond P w η * (1 / 2) ≤
      cond P w η * ∑ δ ∈ F η, cond P (w ++ η) δ :=
          mul_le_mul_of_nonneg_left (le_of_lt (hF_mass η hη))
      (le_of_lt (cond_pos P w η))
  obtain ⟨η₀, hη₀⟩ := hT2ne
  have hstep2 : cond P w η₀ * (1 / 2) <
      cond P w η₀ * ∑ δ ∈ F η₀, cond P (w ++ η₀) δ :=
    mul_lt_mul_of_pos_left (hF_mass η₀ hη₀) (cond_pos P w η₀)
  have hsum_lt : ∑ η ∈ T2, cond P w η * (1 / 2) <
      ∑ η ∈ T2, cond P w η * ∑ δ ∈ F η, cond P (w ++ η) δ :=
    Finset.sum_lt_sum hstep1 ⟨η₀, hη₀, hstep2⟩
  have hfac : ∑ η ∈ T2, cond P w η * (1 / 2)
      = (1 / 2) * ∑ η ∈ T2, cond P w η := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun η _ => by ring
  have hhalf : (1 / 2) * (1 / (M Cb)) < (1 / 2) * ∑ η ∈ T2, cond P w η :=
    mul_lt_mul_of_pos_left hT2mass (by norm_num)
  have hSgt : 1 / (M Cb * 2) < ∑ x ∈ S, cond P w x := by
    rw [hSmass, one_div_mul_two_eq (ne_of_gt hMpos)]
    linarith [hsum_lt, hfac, hhalf]
  refine ⟨T, hTpf, ?_, ?_⟩
  · -- the mass: `1/(K Cb) < 1/(2 C₂) ≤ mass(T)`
    have hTle : 1 / (M Cb * 2) ≤ ∑ t ∈ T, cond P w t :=
      le_of_lt (lt_of_lt_of_le hSgt hTmass)
    have hlt : 1 / balanceConstant (α := α) M C2 Cb < 1 / (M Cb * 2) := by
      refine one_div_lt_one_div_of_lt (by positivity) ?_
      have := two_mul_lt_balanceConstant (α := α) (M := M) (C2 := C2) (Cb := Cb)
        (by linarith : (0 : ℝ) ≤ C2) (by linarith : (0 : ℝ) ≤ Cb)
      linarith
    linarith
  · -- the conclusion, at every member of `U`
    intro t ht
    have htU : t ∈ U := hTU ht
    rw [hU, Finset.mem_biUnion] at htU
    obtain ⟨η, hη, ht⟩ := htU
    rw [Finset.mem_image] at ht
    obtain ⟨δ, hδ, rfl⟩ := ht
    obtain ⟨-, -, θ, hθ, hbound⟩ := hgam_prop η δ ⟨hη, hδ⟩
    refine ⟨θ, hθ, le_trans hbound ?_⟩
    have hmin0 : (0 : ℝ) ≤ min (mmin (insert θ A') (colSum P (w ++ gam η δ)))
        (mkMass 1 (colSum P w)) :=
      le_min (le_of_lt (mmin_pos ⟨θ, Finset.mem_insert_self θ A'⟩
        fun b => colSum_pos P _ b))
        (le_of_lt (mkMass_colSum_pos P w le_rfl (P.card_pos)))
    exact mul_le_mul_of_nonneg_right
      (le_balanceConstant (α := α) (M := M) (C2 := C2) (Cb := Cb) hMpos)
      hmin0

end IntervalExchange.RauzyVeech.RichPath

end
