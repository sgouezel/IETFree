/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.List.TakeDrop
public import Mathlib.Data.List.GetD

/-!
# `List` lemmas for Mathlib

Five facts about `List` that the interval-exchange development needs and that Mathlib does not have,
stated for an arbitrary element type so that they can be proposed upstream as they are.  Each
docstring names the file the lemma would go in: `Mathlib/Data/List/TakeDrop.lean` for the ones about
`take`, `getD` and `head?`, `Mathlib/Data/List/Sublist.lean` (where `IsPrefix` lives) for the two
about prefixes — while `List.prefix_self_append_iff`, `List.getD_append` and
`List.getD_append_right` of Mathlib and core already cover the cases those files would otherwise
need.
-/

public section

namespace List

/-- **Appending the letter that was dropped at the end of a prefix.**  If the letter of `l` at
position `i` is `e`, then `l.take (i + 1)` is `l.take i` followed by `e`.

Natural home: `Mathlib/Data/List/TakeDrop.lean`, beside `List.take_add_one`. -/
theorem take_succ_eq_of_head {α : Type*} (l : List α) (i : ℕ) (e : α)
    (h : (l.drop i).head? = some e) : l.take (i + 1) = l.take i ++ [e] := by
  induction l generalizing i with
  | nil => simp at h
  | cons a t ih =>
    cases i with
    | zero =>
      simp only [List.drop_zero, List.head?_cons, Option.some.injEq] at h
      subst h
      rfl
    | succ j =>
      have h' : (t.drop j).head? = some e := by simpa using h
      simp only [List.take_succ_cons, List.cons_append]
      rw [ih j h']

/-- **A position below the length is occupied.**  The element dropped at a position below the length
exists.

Natural home: `Mathlib/Data/List/TakeDrop.lean`, beside `List.take_add_one`. -/
theorem exists_head_drop {α : Type*} (l : List α) (i : ℕ) (h : i < l.length) :
    ∃ e : α, (l.drop i).head? = some e := by
  cases hh : (l.drop i).head? with
  | none =>
    rw [List.head?_eq_none_iff, List.drop_eq_nil_iff] at hh
    omega
  | some e => exact ⟨e, rfl⟩

/-- **A prefix of length `n + 1` is its prefix of length `n` and the `n`-th letter.**  Stated with
`getD` so that no inhabitedness of the element type is needed; `List.take_add_one` gives the same
with `l[n]?.toList`.

Natural home: `Mathlib/Data/List/TakeDrop.lean`, beside `List.take_add_one`. -/
theorem take_succ_getD {α : Type*} (l : List α) {n : ℕ} (h : n < l.length) (d : α) :
    l.take (n + 1) = l.take n ++ [l.getD n d] := by
  rw [List.take_add_one]
  have hsome : l[n]? = some (l.getD n d) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rfl
  rw [hsome]
  rfl

/-- **Prefixes are stable under appending a common suffix on the left.**

Natural home: `Mathlib/Data/List/Sublist.lean`, beside `List.prefix_self_append_iff`. -/
theorem append_prefix_append {α : Type*} (a : List α) {b c : List α} (h : b <+: c) :
    a ++ b <+: a ++ c := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by rw [List.append_assoc, ht]⟩

/-- **Antisymmetry of the prefix order.**

Natural home: `Mathlib/Data/List/Sublist.lean`, beside `List.IsPrefix.length_le`. -/
theorem eq_of_prefix_of_prefix {α : Type*} {u v : List α} (h1 : u <+: v) (h2 : v <+: u) :
    u = v :=
  List.IsPrefix.eq_of_length h1 (Nat.le_antisymm (List.IsPrefix.length_le h1)
    (List.IsPrefix.length_le h2))

end List
