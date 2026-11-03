/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.RauzyVeech.RichPath.Potential
import IETFree.RauzyVeech.RichPath.InductionAssembly
import IETFree.RauzyVeech.RichPath.GradedInduction
import IETFree.RauzyVeech.RichPath.RichPathAssembly
import IETFree.RauzyVeech.MainComponents

/-!
# Richness of the greedy path, unconditionally

Richness of the greedy path with the vertices pinned (`richGreedyPath`), for **every** irreducible
combinatorial data on at least two letters: for every vertex `π₀` of the diagram of `P`, every word
`γ₀` and a.e. length vector, the greedy path of `λ` passes through `π₀` at arbitrarily late times
and then follows `γ₀`.  This is the only statement of richness in the library; the reductions that
lead to it are separate theorems, and it is not restated anywhere.

The two inputs of the graded induction are both theorems:

* `Γ₃` — `Potential.straddleMassCard_of_unclean`, for every cardinality and with no hypothesis
  beyond irreducibility (`Potential.lean`: the `A'`-sum potential contracts on the non-exit branches
  at every *non-blocked* node, and `not_blocked_of_noExit` shows no blocked node is reached before
  the stop, so the only obstruction in the potential argument never occurs);
* `Γ₂` — `MassGrowth.exists_extMassGen_sharp`, unconditionally (`M Cb = (1+ε)(1 + 2^L·Cb)^L`,
  `C₂ = 2^L`, from the balance degradation along a minimal extension).

The route follows the source: base case and `Γ₁`/pigeonhole (`GradedInduction.lean`), `Γ₂`
(`MinimalExitMass.lean`, `MassGrowth.lean`), `Γ₃` (`HeightDichotomy.lean`, `StraddleMass.lean`,
`Potential.lean`), `Γ₄` (`LargeLetter.lean`), the `k → k+1` dichotomy (`HeightDichotomy.lean`), the
reduction to the graded estimate (`GradedInduction.lean`:
`exists_gradedStep_card_of_inductionStep`), and the analytic step from the estimate to richness,
which is the body of the theorem below (`step_pinned`, then the pinned Lévy recurrence
`levy_cylinder`). -/


open MeasureTheory Filter IETDatum₂

namespace RichPath

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- **Richness of the greedy path**: for every vertex `π₀` of the diagram, given by a word `u`
(`hu`), every finite word `γ₀`, and a.e. length vector, the greedy path passes through `π₀` at
arbitrarily late times and then follows `γ₀`.

`step_pinned` gives, from every node `w`, a definite fraction of `Δ(w)` consisting of points which
at a time `≥ |w|` are at `π₀` and follow `γ₀`; the Lévy recurrence (`levy_cylinder`) turns this into
"a.e. point, at every level, has such a later time". -/
theorem richGreedyPath (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (π₀ : IETDatum₂ α n) (u : List Bool) (hu : IETDatum₂.vertex P u = π₀) (γ₀ : List Bool) :
    ∀ᵐ lam ∂(simplexVolumeOn α),
      ∀ k : ℕ, ∃ m ≥ k, ∃ w : List Bool, w.length = m ∧ IETDatum₂.vertex P w = π₀ ∧
        lam ∈ IETDatum₂.simplexCyl P (w ++ γ₀) := by
  have h : ∃ C : ℝ, 1 < C ∧ NodeHeight.GradedStep P (Fintype.card α) C C :=
    Induction.exists_gradedStep_card_of_inductionStep P
      (Assemble.inductionStep_of_straddleMass P hP hn)
  obtain ⟨δ, hδ, hstep⟩ := step_pinned P hP hn ⟨u, hu⟩ h
  have key : ∀ N : ℕ, ∀ᵐ x ∂(simplexVolumeOn α), x ∈ IETDatum₂.simplexCyl P [] →
      ∃ m ≥ N, ∃ w : List Bool, w.length = m ∧ IETDatum₂.vertex P w = π₀ ∧
        x ∈ IETDatum₂.simplexCyl P (w ++ γ₀) := by
    intro N
    -- the per-atom hypothesis of the Lévy recurrence, for the pinned target
    have hZ : simplexVolumeOn α (ZpinLev P π₀ γ₀ N) = 0 := by
      refine levy_cylinder P hP hn (ZpinLev P π₀ γ₀ N)
        (measurableSet_ZpinLev P π₀ γ₀ N) N hδ (fun k hk w hw => ?_)
      obtain ⟨F, hFsub, hmass, hFx⟩ := hstep w
      refine ⟨F, hFsub, hmass, ?_⟩
      rw [Set.disjoint_left]
      intro x hxF hxZ
      simp only [ZpinLev, Set.mem_iInter, Set.mem_compl_iff] at hxZ
      obtain ⟨hxF', hxN⟩ := hxF
      obtain ⟨m, hm, hv, hmem⟩ := hFx x hxF'
      exact hxZ ⟨m, le_trans hk (le_trans (le_of_eq hw.symm) hm)⟩
        ((mem_GoodPin_iff P hP hn π₀ γ₀ m hxN).mpr ⟨hv, hmem⟩)
    -- the same for the point form of the target
    have hZt : simplexVolumeOn α (ZpinTgt P π₀ γ₀ N) = 0 := by
      have heq : ZpinTgt P π₀ γ₀ N \ CylRec.Nbad P = ZpinLev P π₀ γ₀ N \ CylRec.Nbad P := by
        rw [Set.sdiff_eq, Set.sdiff_eq, ZpinLev_inter_Nbad P hP hn π₀ γ₀ N]
      rw [CylRec.measure_eq_of_sdiff_Nbad_eq P hP hn heq]
      exact hZ
    rw [measure_eq_zero_iff_ae_notMem] at hZt
    filter_upwards [hZt] with x hx hx0
    by_contra hcon
    refine hx ⟨hx0, fun m hm hpin => hcon ?_⟩
    exact ⟨m, hm, IETDatum₂.pathWord P x m, IETDatum₂.pathWord_length P x m, hpin.1, hpin.2⟩
  filter_upwards [MeasureTheory.ae_all_iff.mpr key, IETDatum₂.ae_mem_simplexCyl_nil P]
    with x hx hx0
  exact fun k => hx k hx0

end RichPath

