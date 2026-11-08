/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.RichPath.MinimalExitMass

/-!
# Closing `Γ₂`: an existential mass growth from the uniform minimal exit

`exists_extMassGen_sharp`: for every irreducible `P` there is `L` such that for every `ε > 0` the
interface `ExtMassGen P (fun Cb => (1+ε) * (1 + 2^L * Cb)^L) (2^L)` holds — the mass slot
of the induction is met by a family whose mass constant depends on the balance constant `Cb` of the
node, with the height constant `2^L` supplied by `exists_uniform_minimal_exit`.

The family slot only has to be met on the single prefix-free family `S = {[]}`, which is why no
hypothesis on `P` beyond irreducibility is needed. -/

open Finset IntervalExchange.IETDatum₂
open scoped BigOperators

@[expose] public section

namespace IntervalExchange.RauzyVeech.RichPath

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## `Γ₂` in the `ExtMassGen` form of the assembly -/

/-- **The sharp form of `Γ₂`'s mass bound**: a single *minimal exit word* of a `Cb`-balanced node
already has mass at least `(1/(1 + 2^L·Cb))^L` (`cond_minimal_exit_ge`), so
`ExtMassGen` holds with `M Cb = (1 + ε)·(1 + 2^L·Cb)^L` for every `ε > 0`, and
`C₂ = 2^L`.  The input family is the single word `u`, of mass `≥ (1/(1 + 2^L·Cb))^L`, so neither a
factor `1/C₁` from `Γ₁` nor any reshaping of the constants is needed. -/
theorem exists_extMassGen_sharp (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∃ L : ℕ, ∀ ε : ℝ, 0 < ε → ExtMassGen P
      (fun Cb => (1 + ε) * (1 + 2 ^ L * Cb) ^ L) (2 ^ L) := by
  obtain ⟨L, hL⟩ := exists_uniform_minimal_exit P hP
  refine ⟨L, fun ε hε => ?_⟩
  intro Cb hCb k A' w hk hklt hne hbal
  have hprop : A' ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ] at hk
    omega
  obtain ⟨u, hExit, hblk, hlen⟩ := hL A' w hne hprop
  refine ⟨{u}, prefixFree_singleton u, ?_, ?_⟩
  · rw [Finset.sum_singleton]
    have hge := cond_minimal_exit_ge P hP hn A' w hCb hbal u hblk hlen
    have hx : (0 : ℝ) < 1 + 2 ^ L * Cb := by positivity
    have hxL : (0 : ℝ) < (1 + 2 ^ L * Cb) ^ L := pow_pos hx L
    have hge' : 1 ≤ cond P w u * (1 + 2 ^ L * Cb) ^ L := by
      rw [div_pow, one_pow] at hge
      rwa [div_le_iff₀ hxL] at hge
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (1 + ε) * (1 + 2 ^ L * Cb) ^ L)]
    nlinarith [hge', hxL]
  · intro η hη
    obtain rfl : η = u := Finset.mem_singleton.mp hη
    refine ⟨?_, ?_⟩
    · rcases hExit with hge | hge
      · exact ⟨true, hge⟩
      · exact ⟨false, hge⟩
    · refine (Mk_one_le_iff (P.card_pos)).mpr fun b => ?_
      have h1 : colSum P (w ++ η) b ≤ 2 ^ η.length * mkMass 1 (colSum P w) :=
        colSum_le_two_pow_mul_Mk P hP hn w η b
      have h2 : (2 : ℝ) ^ η.length ≤ 2 ^ L :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen
      have h3 : (0 : ℝ) < mkMass 1 (colSum P w) :=
        mkMass_colSum_pos P w le_rfl (P.card_pos)
      nlinarith

end IntervalExchange.RauzyVeech.RichPath

end
