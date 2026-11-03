/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.RichPath.MinimalExitMass
public import IETFree.RauzyVeech.RichPath.GradedInduction
public import IETFree.RauzyVeech.RichPath.MassFunction

/-!
# Closing `Γ₂`: an existential mass growth from the uniform minimal exit

`exists_extMassGen_sharp`: for every irreducible `P` there is `L` such that for every `ε > 0` the
interface `Induction.ExtMassGen P (fun Cb => (1+ε) * (1 + 2^L * Cb)^L) (2^L)` holds — the mass slot
of the induction is met by a family whose mass constant depends on the balance constant `Cb` of the
node, with the height constant `2^L` supplied by `MinimalExitMass.exists_uniform_minimal_exit`.

The family slot only has to be met on the single prefix-free family `S = {[]}`, which is why no
hypothesis on `P` beyond irreducibility is needed. -/

@[expose] public section

open Finset
open scoped BigOperators

namespace MassGrowth

open IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## `Γ₂` in the `ExtMassGen` form of the assembly -/

/-- **The sharp form of `Γ₂`'s mass bound**: a single *minimal exit word* of a `Cb`-balanced node
already has mass at least `(1/(1 + 2^L·Cb))^L` (`MinimalExitMass.cond_minimal_exit_ge`), so
`Induction.ExtMassGen` holds with `M Cb = (1 + ε)·(1 + 2^L·Cb)^L` for every `ε > 0`, and
`C₂ = 2^L`.  The input family is the single word `u`, of mass `≥ (1/(1 + 2^L·Cb))^L`, so neither a
factor `1/C₁` from `Γ₁` nor any reshaping of the constants is needed. -/
theorem exists_extMassGen_sharp (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∃ L : ℕ, ∀ ε : ℝ, 0 < ε → Induction.ExtMassGen P
      (fun Cb => (1 + ε) * (1 + 2 ^ L * Cb) ^ L) (2 ^ L) := by
  obtain ⟨L, hL⟩ := MinimalExitMass.exists_uniform_minimal_exit P hP hn
  refine ⟨L, fun ε hε => ?_⟩
  intro Cb hCb k A' w hk hklt hne hbal
  have hprop : A' ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ] at hk
    omega
  obtain ⟨u, hExit, hblk, hlen⟩ := hL A' w hne hprop
  refine ⟨{u}, NodeHeight.prefixFree_singleton u, ?_, ?_⟩
  · rw [Finset.sum_singleton]
    have hge := MinimalExitMass.cond_minimal_exit_ge P hP hn A' w hCb hbal u hblk hlen
    have hx : (0 : ℝ) < 1 + 2 ^ L * Cb := by positivity
    have hxL : (0 : ℝ) < (1 + 2 ^ L * Cb) ^ L := pow_pos hx L
    have hge' : 1 ≤ CylinderMass.cond P w u * (1 + 2 ^ L * Cb) ^ L := by
      have h := hge
      rw [div_pow, one_pow] at h
      rwa [div_le_iff₀ hxL] at h
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (1 + ε) * (1 + 2 ^ L * Cb) ^ L)]
    nlinarith [hge', hxL]
  · intro η hη
    obtain rfl : η = u := Finset.mem_singleton.mp hη
    refine ⟨?_, ?_⟩
    · rcases hExit with h | h
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
    · refine (LargeLetter.Mk_one_le_iff (NodeHeight.card_pos P)).mpr fun b => ?_
      have h1 : NodeHeight.st P (w ++ η) b ≤ 2 ^ η.length * NodeHeight.Mk 1 (NodeHeight.st P w) :=
        MinimalExitMass.st_le_two_pow_mul_Mk P hP hn w η b
      have h2 : (2 : ℝ) ^ η.length ≤ 2 ^ L :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen
      have h3 : (0 : ℝ) < NodeHeight.Mk 1 (NodeHeight.st P w) :=
        NodeHeight.Mk_st_pos P w le_rfl (NodeHeight.card_pos P)
      nlinarith

end MassGrowth

end
