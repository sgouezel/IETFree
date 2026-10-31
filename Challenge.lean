/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib

/-!
The challenge statement, in the shortest form that can be checked: the *unconditional* form of
Theorem 1.1, in Mathlib-only language.  The comparator challenge is `ChallengeWeak.lean`, next to
this file, which states the same theorem with its two external inputs as hypotheses.

`mkIETFun` is the function of the interval exchange with lengths `lam` and permutation `π` placed on
`[a, a + ∑ lam)`; `mkIETEquiv` packages it as a permutation of `ℝ`, and `coe_mkIETEquiv` records its
coercion.  As in `ChallengeWeak.lean`, the inverse is not *constructed*: `mkIETEquiv` is a
definition hole (`:= sorry`) and `coe_mkIETEquiv` a statement, so the file contains no proof about
`mkIETFun`'s inverse — only the statement of Theorem 1.1, with `sorry`, uses them.  `main` is the
theorem.

The declarations are at the root namespace, and their names are the library's, exactly as in
`ChallengeWeak.lean`.

**FROZEN.**  The statements in this file are frozen — they are the unconditional form of Theorem
1.1, displayed for the reader — and must not be changed.  The corresponding definitions in
`IET.lean` are frozen with them.  The comparator target is `ChallengeWeak.lean`, next to this file.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

/-- Left endpoint of the `i`-th interval of the arrangement with lengths `lam`. -/
noncomputable def leftEnd {n : ℕ} (lam : Fin n → ℝ≥0) (i : Fin n) : ℝ :=
  ∑ j with j < i, (lam j : ℝ)

/-- The left endpoint of the image of the `i`-th interval. -/
noncomputable def imageLeft {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0)
    (i : Fin n) : ℝ :=
  ∑ j with π j < π i, (lam j : ℝ)

/-- The translation vector on the `i`-th interval. -/
noncomputable def translationVector {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0)
    (i : Fin n) : ℝ := imageLeft π lam i - leftEnd lam i

/-- The lengths reordered into the order of the images. -/
def imageLengths {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) : Fin n → ℝ≥0 :=
  fun k => lam (π.symm k)

/-- The index of the interval containing `x`, for `x` above the left end. -/
noncomputable def idx {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (x : ℝ) (hx : 0 ≤ x) : Fin n :=
  (Finset.univ.filter (fun i : Fin n => leftEnd lam i ≤ x)).max'
    (by
      refine ⟨0, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [leftEnd] using hx)

/-- **The function of the interval exchange** with lengths `lam` and permutation `π`, placed on
`[a, a + ∑ lam)`. -/
noncomputable def mkIETFun {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a x : ℝ) : ℝ :=
  if hx : x ∈ Set.Ico a (a + ∑ i, (lam i : ℝ)) then
    x + translationVector π lam (idx lam (x - a) (by linarith [hx.1]))
  else x

/-- **The interval exchange** with lengths `lam` and permutation `π`, placed on `[a, a + ∑ lam)`,
as a permutation of `ℝ`.

It is not constructed here: this is a **definition hole**, as in `ChallengeWeak.lean`. -/
noncomputable def mkIETEquiv {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a : ℝ) : Equiv ℝ ℝ := sorry

/-- **The coercion of `mkIETEquiv`**: as a map, the exchange with lengths `lam` and permutation `π`
shifted by `a` is `mkIETFun lam π a`.  This is the one property of the hole that the statement of
`main` needs. -/
lemma coe_mkIETEquiv {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n)) (a : ℝ) :
    (mkIETEquiv lam π a : ℝ → ℝ) = mkIETFun lam π a := sorry

/-- The free region: the `d - 1` free coordinates are positive and have total mass less than `1`,
so that every coordinate of the image, including the last one `1 - ∑`, is positive. -/
def simplexRegion (d : ℕ) : Set (Fin (d - 1) → ℝ) :=
  {v | (∀ i, 0 < v i) ∧ ∑ i, v i < 1}

/-- The parametrisation of the simplex: the `d - 1` free coordinates, the last being `1 - ∑`. -/
noncomputable def simplexMap (d : ℕ) (v : Fin (d - 1) → ℝ) : Fin d → ℝ≥0 :=
  fun i =>
    if h : i.val + 1 = d then (1 - ∑ j, v j).toNNReal
    else (v ⟨i.val, by have := i.isLt; omega⟩).toNNReal

/-- **Lebesgue measure on the simplex**: Lebesgue measure on the `d - 1` free coordinates,
restricted to the region where their total mass is less than `1`, transported by the
parametrisation `λ_d = 1 - ∑_{i<d} λ_i`.  Almost every point of the image is in the simplex. -/
noncomputable def simplexVolume (d : ℕ) : Measure (Fin d → ℝ≥0) :=
  Measure.map (simplexMap d) (volume.restrict (simplexRegion d))

/-- Evaluation of a word in the two generators at a pair of permutations of `ℝ`. -/
noncomputable def evalWordEquiv (w : FreeGroup (Fin 2)) (f g : Equiv ℝ ℝ) : Equiv ℝ ℝ :=
  (FreeGroup.lift (fun i : Fin 2 => if i = 0 then f else g)) w

/-- **The main theorem.**  For almost every pair of length vectors of total mass `1`, the two
exchanges satisfy a nontrivial relation in the group of permutations of `ℝ`. -/
theorem main {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
      ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧
        evalWordEquiv w (mkIETEquiv p.1 π 0) (mkIETEquiv p.2 σ 0) = 1 := by
  sorry
