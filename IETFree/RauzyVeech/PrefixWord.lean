/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.List.OfFn

/-!
# The word read by an infinite type sequence

`pfx p n` is the word read by the infinite type sequence `p` during its first `n` steps: the prefix
of length `n` of the greedy path.  `pfx_succ` records the one-letter recursion, which is what the
cylinder arguments use (`simplexCyl P (pfx p k)` is antitone in `k`).
-/

@[expose] public section

namespace IntervalExchange.RauzyVeech

/-- The word read by the infinite type sequence `p` during the first `n` steps. -/
noncomputable def pfx (p : ℕ → Bool) (n : ℕ) : List Bool :=
  List.ofFn fun i : Fin n => p i

theorem pfx_succ (p : ℕ → Bool) (n : ℕ) : pfx p (n + 1) = pfx p n ++ [p n] := by
  rw [pfx, List.ofFn_succ', List.concat_eq_append]
  congr 1

end IntervalExchange.RauzyVeech

end
