/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.RauzyVeech.Path

/-!
# Direction F: every vertex of a Rauzy class is reached from its base in bounded time,
and every vertex has a bounded return path to the base

The Rauzy diagram on `IETDatum₂ α n` has two arrows at every vertex, `fun Q => Q.rvStep e`
for `e : Bool`.  We prove:

* `rvStep_injective` : for each letter `e` the map `Q ↦ Q.rvStep e` is injective, i.e. the arrow is
  determined by its target together with its label (the *inverse Rauzy move* is a well defined
  operation).
* `Reach P Q` : `Q` is reachable from `P` in the diagram.
* `reach_back` : if `Q` is reachable from `P` then `Q` returns to `P`, with a bound on the
  length of the returning word, uniform in `Q`.
* `reach_of_reach` / `exists_path_between` : the reachable class of `P` is strongly
  connected, with a diameter bound.

The mathematical content is the *return*: reachability alone is a triviality, whereas `reach_back`
is what a bounded-lag/partition argument needs.

No irreducibility hypothesis appears below: the counting argument only uses the two
structural facts above, which hold for the total `rvStep`.

Proof sketch of the return statement.  Let `R` be the set of vertices reachable from `P`, a finite
set closed under both arrows.  If `C ⊆ R` is nonempty and closed under both arrows, then for each
`e` the image of `C` under `Q ↦ Q.rvStep e` has the same cardinality as `C` and is contained in `C`,
hence equals `C`; by injectivity no vertex outside `C` is sent into `C`.  Reading a word from `P` to
a point of `C` backwards, it cannot enter `C` at any step, so it starts in `C`: `P ∈ C`.  Applying
this to the set of vertices reachable *from* `Q` (which is contained in `R` when `Q ∈ R`) gives
`Reach Q P`. -/


-- `[Fintype α]`/`[DecidableEq α]`/`[NeZero n]` are section variables used in the proofs but not
-- in every statement below; the convention here silences the unused-hypothesis lints.

open IETDatum₂

namespace RauzyReach

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. The vertex type is finite -/

/-- The vertices of the Rauzy diagram, i.e. the combinatorial data, form a finite type. -/
noncomputable instance IETDatum₂.instFintype : Fintype (IETDatum₂ α n) :=
  Fintype.ofEquiv ((α ≃ Fin n) × (α ≃ Fin n))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun P => (P.piTop, P.piBottom)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Vertices are compared classically (they carry two bijections, so no computation is involved). -/
noncomputable instance IETDatum₂.instDecidableEq : DecidableEq (IETDatum₂ α n) :=
  Classical.decEq _

/-! ## 2. The inverse Rauzy moves -/

omit [DecidableEq α] in
/-- The pivot value of the step of type `true` is fixed by the step. -/
theorem pivot_fixed_true (P : IETDatum₂ α n) :
    (P.rvStep true).piBottom (P.last true) = P.piBottom (P.last true) := by
  rw [IETDatum₂.rvStep_piBottom_true]
  change IETDatum₂.insertEquiv (P.piBottom (P.last true)) (P.piBottom (P.last true)) =
    P.piBottom (P.last true)
  exact IETDatum₂.insertEquiv_apply_le (le_refl _)

omit [DecidableEq α] in
/-- The pivot value of the step of type `false` is fixed by the step. -/
theorem pivot_fixed_false (P : IETDatum₂ α n) :
    (P.rvStep false).piTop (P.last false) = P.piTop (P.last false) := by
  rw [IETDatum₂.rvStep_piTop_false]
  change IETDatum₂.insertEquiv (P.piTop (P.last false)) (P.piTop (P.last false)) =
    P.piTop (P.last false)
  exact IETDatum₂.insertEquiv_apply_le (le_refl _)

omit [Fintype α] [DecidableEq α] in
/-- A helper for the cancellation of the insertion in the two injectivity proofs. -/
theorem cancel_of_trans_insertEquiv {p : Fin n} {e₁ e₂ : α ≃ Fin n}
    (h : e₁.trans (IETDatum₂.insertEquiv p) = e₂.trans (IETDatum₂.insertEquiv p)) : e₁ = e₂ :=
  Equiv.ext (fun a => (IETDatum₂.insertEquiv p).injective (by
    have := congrArg (fun (u : α ≃ Fin n) => u a) h
    simpa [Equiv.trans_apply] using this))

omit [DecidableEq α] [NeZero n] in
/-- The equality of the two vertices, from the equality of their two orders. -/
theorem eq_of_orders {P Q : IETDatum₂ α n} (htop : P.piTop = Q.piTop)
    (hbot : P.piBottom = Q.piBottom) : P = Q := by
  cases P
  cases Q
  simp only [IETDatum₂.mk.injEq]
  exact ⟨htop, hbot⟩

omit [DecidableEq α] in
/-- **The inverse Rauzy move, type `true`**: the arrow `Q ↦ Q.rvStep true` is injective. -/
theorem rvStep_true_injective : Function.Injective (fun Q : IETDatum₂ α n => Q.rvStep true) := by
  intro P Q hPQ
  have hab : P.rvStep true = Q.rvStep true := hPQ
  have htop : P.piTop = Q.piTop := by
    change (P.rvStep true).piTop = (Q.rvStep true).piTop
    rw [hab]
  have hlast : P.last true = Q.last true := by
    change P.piTop.symm (IETDatum₂.lastPos n) = Q.piTop.symm (IETDatum₂.lastPos n)
    rw [htop]
  have hbot : P.piBottom (P.last true) = Q.piBottom (Q.last true) := by
    have h1 := pivot_fixed_true P
    have h2 := pivot_fixed_true Q
    rw [hab] at h1
    rw [← h1, hlast]
    exact h2
  have hmaineq : P.piBottom.trans (IETDatum₂.insertEquiv (P.piBottom (P.last true))) =
      Q.piBottom.trans (IETDatum₂.insertEquiv (Q.piBottom (Q.last true))) := by
    rw [← IETDatum₂.rvStep_piBottom_true, ← IETDatum₂.rvStep_piBottom_true, hab]
  rw [hbot] at hmaineq
  exact eq_of_orders htop (cancel_of_trans_insertEquiv hmaineq)

omit [DecidableEq α] in
/-- **The inverse Rauzy move, type `false`**: the arrow `Q ↦ Q.rvStep false` is injective. -/
theorem rvStep_false_injective : Function.Injective (fun Q : IETDatum₂ α n => Q.rvStep false) := by
  intro P Q hPQ
  have hab : P.rvStep false = Q.rvStep false := hPQ
  have hbot : P.piBottom = Q.piBottom := by
    change (P.rvStep false).piBottom = (Q.rvStep false).piBottom
    rw [hab]
  have hlast : P.last false = Q.last false := by
    change P.piBottom.symm (IETDatum₂.lastPos n) = Q.piBottom.symm (IETDatum₂.lastPos n)
    rw [hbot]
  have htop : P.piTop (P.last false) = Q.piTop (Q.last false) := by
    have h1 := pivot_fixed_false P
    have h2 := pivot_fixed_false Q
    rw [hab] at h1
    rw [← h1, hlast]
    exact h2
  have hmaineq : P.piTop.trans (IETDatum₂.insertEquiv (P.piTop (P.last false))) =
      Q.piTop.trans (IETDatum₂.insertEquiv (Q.piTop (Q.last false))) := by
    rw [← IETDatum₂.rvStep_piTop_false, ← IETDatum₂.rvStep_piTop_false, hab]
  rw [htop] at hmaineq
  exact eq_of_orders (cancel_of_trans_insertEquiv hmaineq) hbot

omit [DecidableEq α] in
/-- **The inverse Rauzy move**: for each of the two letters, the arrow is injective. -/
theorem rvStep_injective (e : Bool) :
    Function.Injective (fun Q : IETDatum₂ α n => Q.rvStep e) := by
  cases e
  · exact rvStep_false_injective
  · exact rvStep_true_injective

/-! ## 3. Reachability in the diagram -/

/-- `Reach P Q`: the vertex `Q` is reachable from the vertex `P`. -/
def Reach (P Q : IETDatum₂ α n) : Prop := ∃ u : List Bool, IETDatum₂.vertex P u = Q

omit [DecidableEq α] in
theorem reach_refl (P : IETDatum₂ α n) : Reach P P := ⟨[], rfl⟩

omit [DecidableEq α] in
theorem reach_step {P Q : IETDatum₂ α n} (h : Reach P Q) (e : Bool) :
    Reach P (Q.rvStep e) := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u ++ [e], by rw [IETDatum₂.vertex_append_singleton, hu]⟩

omit [DecidableEq α] in
theorem reach_trans {P Q R : IETDatum₂ α n} (h₁ : Reach P Q) (h₂ : Reach Q R) : Reach P R := by
  obtain ⟨u, hu⟩ := h₁
  obtain ⟨v, hv⟩ := h₂
  exact ⟨u ++ v, by rw [IETDatum₂.vertex_append, hu, hv]⟩

/-! ## 4. The counting argument -/

omit [DecidableEq α] in
/-- A finite set closed under both arrows is invariant under each of the two arrows. -/
theorem image_rvStep_eq (C : Finset (IETDatum₂ α n))
    (hC : ∀ Q ∈ C, ∀ e : Bool, Q.rvStep e ∈ C) (e : Bool) :
    C.image (fun Q => Q.rvStep e) = C := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · rw [Finset.image_subset_iff]
    exact fun x hx => hC x hx e
  · rw [Finset.card_image_of_injOn (fun x _ y _ hxy => rvStep_injective e hxy)]

omit [DecidableEq α] in
/-- **No arrow enters a closed set**: if `C` is closed under both arrows, then no vertex
outside `C` is sent into `C` by an arrow. -/
theorem mem_of_rvStep_mem (C : Finset (IETDatum₂ α n))
    (hC : ∀ Q ∈ C, ∀ e : Bool, Q.rvStep e ∈ C) (e : Bool) {Q : IETDatum₂ α n}
    (h : Q.rvStep e ∈ C) : Q ∈ C := by
  have himg := image_rvStep_eq C hC e
  have hmem : Q.rvStep e ∈ C.image (fun Q => Q.rvStep e) := by
    rw [himg]
    exact h
  obtain ⟨Q', hQ', hQ'e⟩ := Finset.mem_image.mp hmem
  have hQQ' : Q' = Q := rvStep_injective e hQ'e
  rwa [hQQ'] at hQ'

omit [DecidableEq α] in
/-- **The key counting lemma**: a nonempty finite set of vertices that is closed under both
arrows and consists of vertices reachable from `P` contains `P`. -/
theorem mem_of_closed_reachable (C : Finset (IETDatum₂ α n)) (hCne : C.Nonempty)
    (hC : ∀ Q ∈ C, ∀ e : Bool, Q.rvStep e ∈ C) {P : IETDatum₂ α n}
    (hreach : ∀ Q ∈ C, Reach P Q) : P ∈ C := by
  obtain ⟨Q₀, hQ₀⟩ := hCne
  obtain ⟨u, hu⟩ := hreach Q₀ hQ₀
  have key : ∀ u : List Bool, IETDatum₂.vertex P u ∈ C → P ∈ C := by
    intro u
    induction u using List.reverseRecOn with
    | nil =>
        intro h
        simpa using h
    | append_singleton v e ih =>
        intro h
        rw [IETDatum₂.vertex_append_singleton] at h
        exact ih (mem_of_rvStep_mem C hC e h)
  exact key u (by rw [hu]; exact hQ₀)

/-! ## 5. Every reachable vertex returns to the base -/

omit [DecidableEq α] in
/-- **Strong connectivity of the reachable class**: a vertex reachable from `P` has a path
back to `P`. -/
theorem reach_back {P Q : IETDatum₂ α n} (h : Reach P Q) : Reach Q P := by
  classical
  let C : Finset (IETDatum₂ α n) := Finset.univ.filter (fun R => Reach Q R)
  have hQ : Q ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    exact reach_refl Q
  have hCne : C.Nonempty := ⟨Q, hQ⟩
  have hC : ∀ R ∈ C, ∀ e : Bool, R.rvStep e ∈ C := by
    intro R hR e
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hR ⊢
    exact reach_step hR e
  have hreach : ∀ R ∈ C, Reach P R := by
    intro R hR
    have hQR : Reach Q R := by simpa [C] using hR
    exact reach_trans h hQR
  have hP : P ∈ C := mem_of_closed_reachable C hCne hC hreach
  simpa [C] using hP

omit [DecidableEq α] in
/-- Two vertices reachable from `P` are mutually reachable: the class of `P` is strongly connected.
-/
theorem reach_of_reach {P Q Q' : IETDatum₂ α n} (hQ : Reach P Q) (hQ' : Reach P Q') :
    Reach Q Q' :=
  reach_trans (reach_back hQ) hQ'

/-! ## 6. Length bounds -/

omit [DecidableEq α] in
/-- **Diameter bound**: any two vertices of the class of `P` are joined by a word of length at
most `L`, with `L` depending on `P` only. -/
theorem exists_path_between (P : IETDatum₂ α n) :
    ∃ L : ℕ, ∀ (Q Q' : IETDatum₂ α n), Reach P Q → Reach P Q' →
      ∃ u : List Bool, u.length ≤ L ∧ IETDatum₂.vertex Q u = Q' := by
  classical
  let f : IETDatum₂ α n → IETDatum₂ α n → List Bool :=
    fun Q Q' => if h : Reach Q Q' then Classical.choose h else []
  have hf (Q Q' : IETDatum₂ α n) (h : Reach Q Q') : IETDatum₂.vertex Q (f Q Q') = Q' := by
    have h1 : f Q Q' = Classical.choose h := by
      simp only [f]
      exact dif_pos h
    rw [h1]
    exact Classical.choose_spec h
  refine ⟨Finset.univ.sup (fun p : IETDatum₂ α n × IETDatum₂ α n => (f p.1 p.2).length),
    fun Q Q' hQ hQ' => ?_⟩
  refine ⟨f Q Q', ?_, hf Q Q' (reach_of_reach hQ hQ')⟩
  exact Finset.le_sup (s := Finset.univ)
    (f := fun p : IETDatum₂ α n × IETDatum₂ α n => (f p.1 p.2).length) (Finset.mem_univ (Q, Q'))

/-! ## 7. A concrete return word, for `BoundedLag.padWord`  The statements above are existential.
For the use in a bounded-lag/composition argument one needs an actual choice of returning word
together with a bound that holds for all vertices at once; that is `returnWord` below, with the
vertex `IETDatum₂.vertex P w` in place of `π_w`. -/

/-- A chosen word bringing a vertex of the class of `P` back to `P` (`[]` outside the class). -/
noncomputable def returnWord (P Q : IETDatum₂ α n) : List Bool := by
  classical
  exact if h : Reach P Q then Classical.choose (reach_back (P := P) h) else []

omit [DecidableEq α] in
/-- The chosen return word does return to the base vertex. -/
theorem returnWord_spec {P Q : IETDatum₂ α n} (h : Reach P Q) :
    IETDatum₂.vertex Q (returnWord P Q) = P := by
  have h1 : returnWord P Q = Classical.choose (reach_back (P := P) h) := by
    simp only [returnWord]
    exact dif_pos h
  rw [h1]
  exact Classical.choose_spec (reach_back (P := P) h)

end RauzyReach

