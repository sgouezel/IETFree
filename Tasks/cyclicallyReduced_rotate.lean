/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib

/-!
Statement file for a discovery run: **a one-step rotation preserves cyclic reducedness** in a free
group.  This is the last ingredient of P5b of the blueprint in `Centralizer.lean` (Lyndon–Schupp
Prop. 2.14: cyclically reduced conjugates are cyclic permutations of each other); its induction moves
the middle word around the circle, so it needs that a cyclic rotation of a cyclically reduced word is
again cyclically reduced.

Nothing has to be inlined: `FreeGroup.IsCyclicallyReduced` is in Mathlib
(`Mathlib/GroupTheory/FreeGroup/CyclicallyReduced.lean`), defined by

```lean
def IsCyclicallyReduced (L : List (α × Bool)) : Prop :=
  IsReduced L ∧ ∀ a ∈ L.getLast?, ∀ b ∈ L.head?, a.1 = b.1 → a.2 = b.2
```

so both sides of the statement say "every cyclically adjacent pair of the cyclic word fails to
cancel".

Two observations that make this short if a clean route is found:

* `IsReduced (A ++ B) ↔ IsReduced A ∧ IsReduced B ∧ (no cancellation at the junction)` is
  `List.isChain_append` (`IsReduced` is `IsChain` with `fun a b => a.1 = b.1 → a.2 = b.2`);
* `IsCyclicallyReduced L ↔ IsReduced (L ++ L)` — the doubled word tests the ordinary reducedness and
  the wrap-around condition at once (this is
  `FreeGroup.isCyclicallyReduced_iff_isReduced_append_self` in `Centralizer.lean`, not needed here).

With the second form the claim becomes: `IsReduced ((a :: l) ++ (a :: l)) ↔
IsReduced ((l ++ [a]) ++ (l ++ [a]))`, i.e. that `IsReduced` is invariant under rotating a *periodic*
word by one letter.  A pedestrian route is induction on `l`, comparing the two lists of cyclically
adjacent pairs; a slicker one may be to phrase both sides as "for all `i`, the `i`-th and `i+1`-th
letters of the cyclic word do not cancel" and shuffle indices.

The result is checked against the library in `Tasks/Match.lean` once it is ported.
-/

open FreeGroup

/-- **A one-step rotation preserves cyclic reducedness**: `a :: l` is cyclically reduced iff
`l ++ [a]` is.  Equivalently, cyclic reducedness is a property of the cyclic word.
(The run's id has to be all lowercase; when ported this becomes
`FreeGroup.IsCyclicallyReduced.cons_concat_iff`.) -/
theorem rotate_cyclically_reduced {α : Type*} (l : List (α × Bool)) (a : α × Bool) :
    FreeGroup.IsCyclicallyReduced (a :: l) ↔ FreeGroup.IsCyclicallyReduced (l ++ [a]) := by
  sorry
