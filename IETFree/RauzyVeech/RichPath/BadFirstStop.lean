/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.RichPath.Stopping

/-!
# The first stop of a bad word is unclean

`Stopping.bad_first_stop`: a word `δ` which is `Bad` at the node `w` — no clean stop and no clean
crossing — has a *first* stop event `j ≤ δ.length`, all of whose earlier indices are not stop
events, and whose prefix `δ.take j` is not `Clean`.  This is the elementary step of the `Γ₃`
bookkeeping of `IETFree/RauzyVeech/RichPath/Stopping.lean`. -/

@[expose] public section


open Finset IETDatum₂ MeasureTheory NodeHeight
open scoped BigOperators

namespace Stopping

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. General facts about clean stops -/

/-- A bad word has a first stop event, and that first stop event is unclean. -/
theorem bad_first_stop {P : IETDatum₂ α n} {A' : Finset α} {w δ : List Bool}
    (hb : Bad P A' w δ) :
    ∃ j, j ≤ δ.length ∧ StopEv P A' w δ j ∧ (∀ g < j, ¬ StopEv P A' w δ g) ∧
      ¬ Clean P A' w (δ.take j) := by
  classical
  rw [Bad, Good, not_or] at hb
  obtain ⟨hns, hgf⟩ := hb
  push Not at hns
  obtain ⟨g, hg, hge⟩ := hns
  rw [Finset.mem_range] at hg
  set S := (Finset.range (δ.length + 1)).filter (fun g => StopEv P A' w δ g) with hS
  have hSne : S.Nonempty :=
    ⟨g, Finset.mem_filter.mpr ⟨by rw [Finset.mem_range]; omega, hge⟩⟩
  set j := S.min' hSne with hjdef
  have hjS : j ∈ S := Finset.min'_mem S hSne
  have hjmin : ∀ g ∈ S, j ≤ g := fun g hg' => Finset.min'_le S g hg'
  obtain ⟨hjrange, hjstop⟩ := Finset.mem_filter.mp hjS
  rw [Finset.mem_range] at hjrange
  have hfirst : ∀ g < j, ¬ StopEv P A' w δ g := by
    intro g hg' hcon
    have hmem : g ∈ S := Finset.mem_filter.mpr ⟨by rw [Finset.mem_range]; omega, hcon⟩
    have hle := hjmin g hmem
    omega
  refine ⟨j, by omega, hjstop, hfirst, ?_⟩
  intro hclean
  apply hgf
  refine ⟨j, by rw [Finset.mem_range]; omega, ?_, ?_⟩
  · intro g hg'
    exact hfirst g (by rw [Finset.mem_range] at hg'; omega)
  · rcases hjstop with hH | ⟨hlt, hEA⟩
    · exact Or.inl ⟨hH, hclean⟩
    · exact Or.inr ⟨by omega, hEA, hclean⟩

end Stopping

end
