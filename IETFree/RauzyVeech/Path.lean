/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.RauzyVeech.Step

/-!
# Paths of the Rauzy–Veech algorithm

The iteration of the step along a finite path (`vertex`), the name and secondary name of a step,
Corollary 1 of the source (p. 13: consecutive arrows with different names satisfy `secondary(γₙ₊₁) =
name(γₙ)`), the multiplicativity of `Path.Q`, and the fact that for irreducible data on at least two
letters the two last letters differ (so the two `last` values never coincide).  Also `vertexNat`,
the iteration along an infinite sequence of types, which is the shape needed for Proposition 4.3. -/

open scoped BigOperators

namespace IETDatum₂

open IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. The vertices of the algorithm -/

/-- The vertex reached from `P` after reading the word `γ`: the iterated Rauzy--Veech step. -/
noncomputable def vertex (P : IETDatum₂ α n) : List Bool → IETDatum₂ α n
  | [] => P
  | e :: es => vertex (P.rvStep e) es

omit [DecidableEq α] in
@[simp]
theorem vertex_nil (P : IETDatum₂ α n) : vertex P [] = P := rfl

omit [DecidableEq α] in
@[simp]
theorem vertex_cons (P : IETDatum₂ α n) (e : Bool) (es : List Bool) :
    vertex P (e :: es) = vertex (P.rvStep e) es := rfl

omit [DecidableEq α] in
@[simp]
theorem vertex_singleton (P : IETDatum₂ α n) (e : Bool) : vertex P [e] = P.rvStep e := rfl

omit [DecidableEq α] in
/-- **Bimodularity of `vertex`**: reading `γ` then `δ` is reading `γ ++ δ`
(this gives `vertex P (γ ++ [e]) = rvStep (vertex P γ) e` in the one-letter case). -/
theorem vertex_append (P : IETDatum₂ α n) (γ δ : List Bool) :
    vertex P (γ ++ δ) = vertex (vertex P γ) δ := by
  induction γ generalizing P with
  | nil => simp
  | cons e es ih => simpa using ih (P.rvStep e)

omit [DecidableEq α] in
/-- Reading one more letter at the end. -/
theorem vertex_append_singleton (P : IETDatum₂ α n) (γ : List Bool) (e : Bool) :
    vertex P (γ ++ [e]) = rvStep (vertex P γ) e := by
  rw [vertex_append]
  simp

omit [DecidableEq α] in
/-- **Irreducibility is preserved along a path.** -/
theorem vertex_irreducible (P : IETDatum₂ α n) (γ : List Bool) (hP : P.Irreducible) :
    (vertex P γ).Irreducible := by
  induction γ generalizing P with
  | nil => exact hP
  | cons e es ih => exact ih (P.rvStep e) (P.rvStep_irreducible hP e)

/-! ## 3. A step does not change the last letter of the order of its own type -/

omit [DecidableEq α] in
/-- **The name is preserved by the step**: a step of type `e` leaves the order `e` unchanged, so
the last letter in the order `e` is the same at the next vertex.  This is the reason why a next
arrow can only have a *different* name if it has the other type. -/
@[simp]
theorem rvStep_last_self (P : IETDatum₂ α n) (e : Bool) : (P.rvStep e).last e = P.last e := by
  cases e with
  | false => rfl
  | true => rfl

omit [DecidableEq α] in
/-- **Corollary 1 of the source (p. 13)**, in the form used by Corollary 4: consecutive arrows of
*different types* satisfy secondary$(γ_{n+1})$ = name$(γ_n)$. -/
theorem secondary_eq_of_type_ne (P : IETDatum₂ α n) (e e' : Bool) (h : e' ≠ e) :
    (P.rvStep e).last (!e') = P.last e := by
  cases e <;> cases e' <;> simp_all

/-! ## 4. The two last letters of an irreducible vertex are distinct -/

omit [DecidableEq α] in
/-- **For irreducible data with `2 ≤ n` the two last letters differ.** Otherwise the pivot of a step
of type `true` would be the last position, contradicting `pivot_true_ne_lastPos`. -/
theorem last_true_ne_last_false (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    P.last true ≠ P.last false := by
  intro h
  apply pivot_true_ne_lastPos P hP hn
  rw [h, last_bottom]

omit [DecidableEq α] in
/-- The same, at an arbitrary vertex of the path. -/
theorem vertex_last_ne (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) (γ : List Bool) :
    (vertex P γ).last true ≠ (vertex P γ).last false := by
  intro h
  apply pivot_true_ne_lastPos (vertex P γ) (vertex_irreducible P γ hP) hn
  rw [h, last_bottom]

/-! ## 5. Multiplicativity of `Q` -/

namespace Path

/-- `Q` of the empty word is the identity (definitional). -/
@[simp]
theorem Q_nil (P : IETDatum₂ α n) : Path.Q P [] = 1 := rfl

/-- The recursion of `Q` (definitional). -/
theorem Q_cons (P : IETDatum₂ α n) (e : Bool) (es : List Bool) :
    Path.Q P (e :: es) = P.rvMat e * Path.Q (P.rvStep e) es := rfl

/-- **Multiplicativity of `Q` along a path**: `Q(γ ++ δ) = Q(γ) · Q_γ(δ)`, where `Q_γ` is `Q`
read from the vertex reached after `γ`. -/
theorem Q_append (P : IETDatum₂ α n) (γ δ : List Bool) :
    Path.Q P (γ ++ δ) = Path.Q P γ * Path.Q (vertex P γ) δ := by
  induction γ generalizing P with
  | nil => simp
  | cons e es ih =>
    rw [List.cons_append, Q_cons, Q_cons, ih (P.rvStep e), vertex_cons, Matrix.mul_assoc]

/-- `Q` of a one-letter word is the elementary matrix. -/
@[simp]
theorem Q_singleton (P : IETDatum₂ α n) (e : Bool) : Path.Q P [e] = P.rvMat e := by
  rw [Q_cons]
  simp

end Path

/-! ## 6. Iterating the path along a sequence of types -/

/-- The vertex reached at time `k` along the infinite sequence of types `γ`. -/
noncomputable def vertexNat (P : IETDatum₂ α n) (γ : ℕ → Bool) : ℕ → IETDatum₂ α n
  | 0 => P
  | k + 1 => rvStep (vertexNat P γ k) (γ k)

omit [DecidableEq α] in
/-- The time-`k+1` vertex is the step of type `γ k` applied to the time-`k` vertex. -/
theorem vertexNat_succ (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) :
    vertexNat P γ (k + 1) = rvStep (vertexNat P γ k) (γ k) := rfl

omit [DecidableEq α] in
/-- The recursive vertex is the vertex of the word `γ 0 … γ (k-1)`. -/
theorem vertexNat_eq_vertex_ofFn (P : IETDatum₂ α n) (γ : ℕ → Bool) (k : ℕ) :
    vertexNat P γ k = vertex P (List.ofFn fun i : Fin k => γ i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [vertexNat_succ, ih, List.ofFn_succ', List.concat_eq_append, vertex_append_singleton]
    rfl

omit [DecidableEq α] in
theorem vertexNat_irreducible (P : IETDatum₂ α n) (γ : ℕ → Bool) (hP : P.Irreducible) (k : ℕ) :
    (vertexNat P γ k).Irreducible := by
  rw [vertexNat_eq_vertex_ofFn]
  exact vertex_irreducible P _ hP

end IETDatum₂
