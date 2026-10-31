/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/


/-!
**LANDED — this file is now empty of content.**

It used to hold the ready-to-port proof chain of `FreeGroup.exists_zpow_eq_of_mul_comm` (LS 2.19) and
of Lemma 2.7, with one `sorry` standing for the commensurability input.  That input was supplied by
the run `commensurable-commute` and everything is now in the library:

* `Commensurable.lean` — `FreeGroup.commute_of_zpow_eq` and its word-combinatorics lemmas
  (`List.append_comm_of_flatten_replicate_eq` via Fine–Wilf `List.HasPeriod.gcd`);
* `Centralizer.lean` §D6–§D8 — `FreeGroup.exists_nat_pow_or_inv_of_zpow`,
  `FreeGroup.exists_common_zpow_of_zpow_eq`, `FreeGroup.exists_zpow_eq_of_mul_comm`;
* `Irreducible.lean` — `exists_nontrivial_commutator` (**Lemma 2.7**, no `sorry`, axiom-clean),
  stated with Mathlib's commutator `⁅u, v⁆ = u v u⁻¹ v⁻¹`.

The file is kept only as a pointer; do not re-prove anything here.
-/
