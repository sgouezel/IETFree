/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.PairReach

/-!
# The vocabulary of the extension step, and the minimal extension to a row end outside `A'`

The proof of AGY's distortion theorem extends each `γ_s ∈ Γ₁` *minimally* to a path ending at
a vertex one of whose row ends lies outside `A'`.  This file carries the vocabulary of that step and
its existence half (`colSum` is `B_w·1`, so `mkMass 1` is AGY's `𝔐 = max`):

* §1 (definitions): `Blocked` — both row ends at the node lie in `A'`; `Exit` — one lies outside;
  and `blocked_iff_not_exit`.  (The straddle criterion, the stop word and the cleanness predicate
  used by the later induction are in `Stopping`.)
* §2 (existence): `exists_exit` — from every node and every non-empty proper `A'` some
  continuation ends at a node with a row end outside `A'`.  The proof applies
  `IETDatum₂.pairReach_all` to a pair `(a, θ)` with `θ ∉ A'`, so it even prescribes *both* row ends.
  `exists_minimal_exit` gives the *minimal-length* such word, together with AGY's structural
  fact that all its proper prefixes are blocked.
-/

open Finset IntervalExchange.IETDatum₂
open scoped BigOperators

@[expose] public section

namespace IntervalExchange.RauzyVeech.RichPath

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Definitions -/

/-- Both row ends at the node `w` lie in `A'`: AGY's "cleanness" at `w`. -/
def Blocked (P : IETDatum₂ α n) (w : List Bool) (A' : Finset α) : Prop :=
  (P.vertex w).last true ∈ A' ∧ (P.vertex w).last false ∈ A'

/-- Some row end at the node `w` lies outside `A'`: AGY's stopping condition of `Γ₂`. -/
def Exit (P : IETDatum₂ α n) (w : List Bool) (A' : Finset α) : Prop :=
  (P.vertex w).last true ∉ A' ∨ (P.vertex w).last false ∉ A'

omit [DecidableEq α] in
theorem blocked_iff_not_exit (P : IETDatum₂ α n) (w : List Bool) (A' : Finset α) :
    Blocked P w A' ↔ ¬ Exit P w A' := by
  simp only [Blocked, Exit, not_or, not_not]

/-! ## 2. Existence of an exit, and the minimal exit word -/

omit [DecidableEq α] in
/-- **Existence of a minimal exit**: from every node, and for every non-empty proper `A'`, some
continuation ends at a node with a row end outside `A'`. (`PairReach` at the vertex of the node
prescribes *both* row ends, so we simply prescribe one of them outside `A'`.) -/
theorem exists_exit (P : IETDatum₂ α n) (hP : P.Irreducible) (w : List Bool) {A' : Finset α}
    (hne : A'.Nonempty) (hprop : A' ≠ Finset.univ) :
    ∃ u : List Bool, Exit P (w ++ u) A' := by
  obtain ⟨θ, hθ⟩ : ∃ θ : α, θ ∉ A' := by
    by_contra h
    exact hprop (Finset.eq_univ_iff_forall.mpr (by simpa using h))
  obtain ⟨b, hb⟩ := hne
  have hbθ : b ≠ θ := fun h => hθ (h ▸ hb)
  obtain ⟨u, e, h1, h2⟩ :=
    IETDatum₂.pairReach_all (P.vertex w) (IETDatum₂.vertex_irreducible P w hP) b θ hbθ
  have hu : P.vertex (w ++ u) = (P.vertex w).vertex u := IETDatum₂.vertex_append P w u
  refine ⟨u, ?_⟩
  cases e with
  | false => exact Or.inl (by rw [hu]; simp only [Bool.not_false] at h2; rw [h2]; exact hθ)
  | true => exact Or.inr (by rw [hu]; simp only [Bool.not_true] at h2; rw [h2]; exact hθ)

omit [DecidableEq α] in
/-- The minimal-length exit word exists, and is length-minimal among *all* exit words. -/
theorem exists_minimal_exit (P : IETDatum₂ α n) (hP : P.Irreducible) (w : List Bool)
    {A' : Finset α} (hne : A'.Nonempty) (hprop : A' ≠ Finset.univ) :
    ∃ u : List Bool, Exit P (w ++ u) A' ∧
      (∀ v : List Bool, Exit P (w ++ v) A' → u.length ≤ v.length) ∧
      (∀ i, i < u.length → Blocked P (w ++ u.take i) A') := by
  classical
  obtain ⟨u₀, hu₀⟩ := exists_exit P hP w hne hprop
  have hex : ∃ L : ℕ, ∃ u : List Bool, u.length = L ∧ Exit P (w ++ u) A' :=
    ⟨u₀.length, u₀, rfl, hu₀⟩
  obtain ⟨u, hulen, hu⟩ := Nat.find_spec hex
  have hmin (v : List Bool) (hv : Exit P (w ++ v) A') : u.length ≤ v.length := by
    rw [hulen]
    exact Nat.find_min' hex ⟨v, rfl, hv⟩
  refine ⟨u, hu, hmin, fun i hi => (blocked_iff_not_exit P _ A').mpr (fun hcon => ?_)⟩
  have h1 : u.length ≤ (u.take i).length := hmin (u.take i) hcon
  have h2 : (u.take i).length = i := by rw [List.length_take]; omega
  omega

end IntervalExchange.RauzyVeech.RichPath

end
