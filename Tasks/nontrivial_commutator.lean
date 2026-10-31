/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib

/-!
Statement file for the discovery run `nontrivial-commutator`: the library's
`exists_nontrivial_commutator` (Lemma 2.7 of the paper), with the definitions inlined so that the
file only imports `Mathlib`.  The statement is checked against the library in `Tasks/Match.lean`.

The paper's proof: if all three commutators vanish then `u`, `x⁻¹ux` and `y⁻¹uy` all lie in the
centralizer of `v`, which is cyclic (Lyndon–Schupp, Prop. 2.19).  Since `x⁻¹ux` and `u` are
conjugate they have the same cyclically reduced length, so `x⁻¹ux = u^{±1}`; `u` is not conjugate to
`u⁻¹`, so `x⁻¹ux = u`, i.e. `x` centralizes `u`.  The same for `y`, so `F₂` is abelian.  Mathlib has
no centralizer theorem for free groups (`GroupTheory/FreeGroup/{Reduce,CyclicallyReduced}.lean`
have the reduction API and `conjugator`), so the proof has to be built.
-/

/-- The commutator `[a,b] = a⁻¹ b⁻¹ a b`. -/
def commWord {G : Type*} [Group G] (a b : G) : G := a⁻¹ * b⁻¹ * a * b

/-- **Lemma 2.7**: for nontrivial words `u`, `v` in `F_2`, one of `[u,v]`, `[x⁻¹ux,v]`,
`[y⁻¹uy,v]` is nontrivial. -/
theorem exists_nontrivial_commutator (u v : FreeGroup (Fin 2)) (hu : u ≠ 1) (hv : v ≠ 1) :
    commWord u v ≠ 1 ∨ commWord ((FreeGroup.of 0)⁻¹ * u * (FreeGroup.of 0)) v ≠ 1 ∨
      commWord ((FreeGroup.of 1)⁻¹ * u * (FreeGroup.of 1)) v ≠ 1 := by
  sorry
