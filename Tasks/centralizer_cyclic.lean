/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib

/-!
**PROVED** — kept as a record and as a guard in `Tasks/Match.lean`.

**The centralizer of a nontrivial element of the free group on two generators is cyclic**
(Lyndon–Schupp, Proposition 2.19), the single deep input of Lemma 2.7 of the paper.  The library form
is `FreeGroup.exists_zpow_eq_of_mul_comm` (`IET2/Centralizer.lean`, §D8), stated for an arbitrary free
group; its inputs are `FreeGroup.exists_common_zpow` (§D5), `FreeGroup.commute_of_zpow_eq`
(`IET2/Commensurable.lean`) and the root bound `FreeGroup.le_norm_of_pow_eq` (§2).  The route
sketched below (CyclicallyReduced/reduce_flatten_replicate) is superseded: the "abelian free group is
cyclic" lemma `FreeGroup.exists_zpow_eq_of_forall_commute` replaces the cyclic-word comparison.

What Mathlib does have, and what a proof should build on:

* `IsMulTorsionFree (FreeGroup α)`, i.e. `pow_left_injective : a ^ n = b ^ n → a = b` for `n ≠ 0`
  (`GroupTheory/FreeGroup/CyclicallyReduced.lean`, section `IsMulTorsionFree`);
* `reduceCyclically`, `conjugator`, `conj_conjugator_reduceCyclically` (every element is a conjugate
  `g⁻¹ w g` of a cyclically reduced one, with `w = mk (reduceCyclically L)`);
* `reduce_flatten_replicate`: the reduced word of `w ^ n` for cyclically reduced `w` is `n` copies of
  its cyclic word (plus the conjugator at both ends);
* `subgroupIsFreeOfIsFree`: subgroups of free groups are free (Nielsen–Schreier), so once the
  centralizer is known to be abelian it is cyclic by `ℤᵏ` not being free for `k ≥ 2`.

Route (the paper's, LS 2.19): write `u = g⁻¹ u₀ g`, `v = h⁻¹ v₀ h` with `u₀`, `v₀` cyclically
reduced.  Commuting is preserved, so `u₀` commutes with a conjugate of `v₀`; comparing the reduced
words of the two powers via `reduce_flatten_replicate` shows that the two cyclic words agree, i.e.
`u₀` and `v₀` are powers of a common cyclically reduced word (equivalently: commuting *cyclically
reduced words* in the free monoid are powers of a common word — a `List` induction, with the caveat
that cyclic words are only determined up to rotation).  Then `u` and `v` are powers of the same
element.  Note `FreeGroup (Fin 2)` here, but nothing is specific to rank two.
-/

/-- **Lyndon–Schupp 2.19 for `F₂`**: the centralizer of a nontrivial element is cyclic. -/
theorem exists_centralizer_pow {v : FreeGroup (Fin 2)} (hv : v ≠ 1) :
    ∃ r : FreeGroup (Fin 2), ∀ z : FreeGroup (Fin 2), z * v = v * z → ∃ n : ℤ, z = r ^ n := by
  sorry
