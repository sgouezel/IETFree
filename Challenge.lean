/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib

/-!
The challenge statement, in the shortest form that can be checked: the *unconditional* form of
Theorem 1.1 and the conclusion of the remark that follows it, in Mathlib-only language.  This file
*is* the comparator challenge (see `comparator.json`): `IETFree/ChallengeSolved.lean` proves both,
and `lake comparator` checks that the two modules agree declaration by declaration.

`mkIETFun` is the function of the interval exchange with lengths `lam` and permutation `π` placed on
`[a, a + ∑ lam)`; `mkIETEquiv` packages it as a permutation of `ℝ`, and `coe_mkIETEquiv` records its
coercion.  The inverse is not *constructed*: `mkIETEquiv` is a
definition hole (`:= sorry`) and `coe_mkIETEquiv` a statement, so the file contains no proof about
`mkIETFun`'s inverse — only the two theorems below, each with `sorry`, use them: `main` is
Theorem 1.1, and `Pair.exists_isOpen_ae_exists_nontrivial_evalWordEquiv_eq_one` is the conclusion of
the remark that follows it.

The declarations are in `namespace IntervalExchange`, the library's namespace, and their names are
the library's: `comparator.json` names them in full (`IntervalExchange.main`, …), and the comparator
compares the two modules constant by constant.

The declarations mirror the library's — all of them in `IETFree/IET.lean` — name for name and body
for body, so that the comparator can compare the statements declaration by declaration;
`IETFree/ChallengeSolved.lean` proves them.

The remark's conclusion is the second target,
`exists_isOpen_ae_exists_nontrivial_evalWordEquiv_eq_one`, in `namespace Pair` because the library
states it there: it names no notion of the library's (no
predicate on the relation set), only `mkIETEquiv`, `evalWordEquiv`, `simplexVolume` and the two
normalisation conditions as hypotheses, so that it reads as a statement on its own. -/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

namespace IntervalExchange

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

/-- The intervals whose left endpoint is at most `x`. -/
noncomputable def idxSet {n : ℕ} (lam : Fin n → ℝ≥0) (x : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => leftEnd lam i ≤ x)

/-- The set of intervals whose left endpoint is at most `x` is never empty.  Like every declaration
copied into `Challenge.lean`, its proof must generate no auxiliary declaration — `simp` here would,
and the comparator would then see two different constants.  `refine`/`exact` are safe. -/
theorem idxSet_nonempty {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (x : ℝ) (hx : 0 ≤ x) :
    (idxSet lam x).Nonempty := by
  refine ⟨0, Finset.mem_filter.2 ⟨Finset.mem_univ 0, ?_⟩⟩
  exact le_of_eq_of_le (Finset.sum_eq_zero fun j hj =>
    absurd (Finset.mem_filter.1 hj).2 (Fin.not_lt_zero j)) hx

/-- The index of the interval, in the arrangement with lengths `lam`, that contains `x`. -/
noncomputable def idx {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (x : ℝ) (hx : 0 ≤ x) : Fin n :=
  (idxSet lam x).max' (idxSet_nonempty lam x hx)

/-- **The interval exchange transformation**, as a bare function, with lengths `lam` and
permutation `π`, placed on `[a, a + ∑ lam)`. -/
noncomputable def mkIETFun {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a x : ℝ) : ℝ :=
  if hx : x ∈ Set.Ico a (a + ∑ i, (lam i : ℝ)) then
    x + translationVector π lam (idx lam (x - a) (by linarith [hx.1]))
  else x

/-- **The interval exchange transformation**, as an equiv, with lengths `lam` and permutation `π`,
placed on `[a, a + ∑ lam)`; this is a permutation of `ℝ`.

It is not constructed here: this is a **definition hole**, which the solution fills with the
library's `mkIETEquiv`. -/
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

/-- The `d - 1` free coordinates sit below `d - 1` in the `d`-th slot of the last coordinate.
`omega` would be shorter, but it generates an auxiliary declaration, and auxiliaries are private to
their module: this statement is copied verbatim into `Challenge.lean`, and the comparator compares
the two proof terms, so the copies would no longer be the same declaration. -/
theorem simplexMap_val_lt (d : ℕ) (i : Fin d) (h : ¬ i.val + 1 = d) : i.val < d - 1 :=
  Nat.lt_pred_iff.2 (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.isLt) h)

/-- The parametrisation of the simplex: the `d - 1` free coordinates, the last being `1 - ∑`. -/
noncomputable def simplexMap (d : ℕ) (v : Fin (d - 1) → ℝ) : Fin d → ℝ≥0 :=
  fun i =>
    if h : i.val + 1 = d then (1 - ∑ j, v j).toNNReal
    else (v ⟨i.val, simplexMap_val_lt d i h⟩).toNNReal

/-- **Lebesgue measure on the simplex**: Lebesgue measure on the `d - 1` free coordinates,
restricted to the region where their total mass is less than `1`, transported by the
parametrisation `λ_d = 1 - ∑_{i<d} λ_i`.  Almost every point of the image is in the simplex. -/
noncomputable def simplexVolume (d : ℕ) : Measure (Fin d → ℝ≥0) :=
  Measure.map (simplexMap d) (volume.restrict (simplexRegion d))

/-- Evaluation of a word in the two generators at a pair of permutations of `ℝ`.

The generator map is `Fin.cases f fun _ => g` rather than `if i = 0 then f else g`: the latter
carries a `DecidableEq (Fin 2)` instance whose proof is an auxiliary declaration of the module it
is written in, and the comparator compares these two copies of the definition term by term. -/
noncomputable def evalWordEquiv (w : FreeGroup (Fin 2)) (f g : Equiv ℝ ℝ) : Equiv ℝ ℝ :=
  FreeGroup.lift (Fin.cases f fun _ => g) w

/-- **The main theorem.**  For almost every pair of length vectors of total mass `1`, the two
exchanges satisfy a nontrivial relation in the group of permutations of `ℝ`. -/
theorem main {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
      ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧
        evalWordEquiv w (mkIETEquiv p.1 π 0) (mkIETEquiv p.2 σ 0) = 1 := by
  sorry

namespace Pair

/-- **The remark after the main theorem.**  The pairs of length vectors which do not generate a free
group contain an open set of full measure: some open set `O` of the ambient space — of null
complement for the product of the two simplex measures — is such that every `p ∈ O` whose two
vectors have total mass `1` carries a nontrivial word which is trivial for the two permutations
`mkIETEquiv p.1 π 0` and `mkIETEquiv p.2 σ 0`. -/
theorem exists_isOpen_ae_exists_nontrivial_evalWordEquiv_eq_one {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) :
    ∃ O : Set ((Fin d → ℝ≥0) × (Fin e → ℝ≥0)), IsOpen O ∧
      ((simplexVolume d).prod (simplexVolume e)) Oᶜ = 0 ∧
      ∀ p ∈ O, (∑ i, p.1 i = 1) → (∑ j, p.2 j = 1) →
        ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧
          evalWordEquiv w (mkIETEquiv p.1 π 0) (mkIETEquiv p.2 σ 0) = 1 := by
  sorry

end Pair

end IntervalExchange

end
