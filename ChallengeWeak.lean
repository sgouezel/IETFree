/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib

/-!
The **weak challenge**: Theorem 1.1 of the paper with its two external inputs as hypotheses.

This is the *challenge* half of the comparator setup (`comparator.json`): `main` is the statement
that `IETFree/ChallengeWeakSolved.lean` proves, in these very words.  The file imports only
`Mathlib` and nothing imports it.

## What the names have to be

Comparator compares the statements of the target theorems between the two environments, and every
declaration those statements reach, **declaration by declaration, by name** — the same type and the
same value, proofs of definition parts included.  So every declaration below that shares a name with
a library declaration is *the library's declaration*, copied verbatim: `leftEnd`, `imageLeft`,
`translationVector`, `imageLengths`, `leftEnd_zero`, `idxSet`, `idx`, `mkIETFun`, `simplexRegion`,
`simplexMap`, `simplexVolume`, `unitMeas`, `IsIrreduciblePerm`, `evalWordEquiv`.  They are
*not* rewritten here, even where a shorter form would be equivalent: a different body is a different
declaration.

Three things are not the library's, and cannot be:

* `UniqueErgodicFun` and `IsRigidByTranslationsFun` — the library's `UniqueErgodic` and
  `IsRigidByTranslations` are stated for an exchange `f : IET 0 1` and iterate it with the group
  power; the same conditions for a self-map `ℝ → ℝ`, iterated with `f^[·]`, are different
  statements, so they cannot carry the same name.  `MasurVeechFun` and `VeechRigidityFun` are the
  paper's two hypotheses in that form.
* `coe_mkIETEquiv` — the one property of `mkIETEquiv` the proof uses.
* `mkIETEquiv` itself is a **definition hole** (`definition_names` in `comparator.json`): it is
  *given* by the solution, not by the challenge.  Comparator checks its statement, its safety, the
  kernel's acceptance of the solution's version and its axioms, but not its body — a private core
  (`mkIETFunCore` in `IETFree/IET.lean`) is used in the library's two inverse laws, and a private
  name cannot leave its own module.  `coe_mkIETEquiv` is what pins the hole down: it is a theorem
  target, so the solution has to prove that its `mkIETEquiv` is the map of `mkIETFun`.

## The `sorry`s

They are the statements — `main`, `coe_mkIETEquiv`, and the definition hole.  This file is a
challenge; its whole point is that they are not proved here.  `IETFree/ChallengeWeakSolved.lean`
proves them.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

/-! ## The interval exchange, in the shortest form that can be checked

These definitions are those of `Challenge.lean`, copied verbatim. -/

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

/-- The left end of the `0`-th interval is `0`. -/
@[simp] theorem leftEnd_zero {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) : leftEnd lam 0 = 0 := by
  simp [leftEnd]

/-- The intervals whose left endpoint is at most `x`. -/
noncomputable def idxSet {n : ℕ} (lam : Fin n → ℝ≥0) (x : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => leftEnd lam i ≤ x)

/-- The index of the interval, in the arrangement with lengths `lam`, that contains `x`. -/
noncomputable def idx {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (x : ℝ) (hx : 0 ≤ x) : Fin n :=
  (idxSet lam x).max'
    (by
      refine ⟨0, ?_⟩
      simp only [idxSet, Finset.mem_filter, Finset.mem_univ, true_and, leftEnd_zero]
      exact hx)

/-- **The function of the interval exchange** with lengths `lam` and permutation `π`, placed on
`[a, a + ∑ lam)`. -/
noncomputable def mkIETFun {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a x : ℝ) : ℝ :=
  if hx : x ∈ Set.Ico a (a + ∑ i, (lam i : ℝ)) then
    x + translationVector π lam (idx lam (x - a) (by linarith [hx.1]))
  else x

/-- **The interval exchange** with lengths `lam` and permutation `π`, placed on `[a, a + ∑ lam)`,
as a permutation of `ℝ`. -/
noncomputable def mkIETEquiv {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a : ℝ) : Equiv ℝ ℝ := sorry

/-- **The coercion of `mkIETEquiv`**: as a map, the exchange with lengths `lam` and permutation `π`
shifted by `a` is `mkIETFun lam π a`.

This is the property of the definition hole `mkIETEquiv` that the proof of `main` uses: without it
the hole would be an arbitrary permutation of `ℝ` of the right type.  It is a theorem *target* of
the challenge, so the solution has to prove it about the `mkIETEquiv` it supplies. -/
lemma coe_mkIETEquiv {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n)) (a : ℝ) :
    (mkIETEquiv lam π a : ℝ → ℝ) = mkIETFun lam π a := sorry

/-! ## The parameter space of length vectors -/

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

/-! ## The two notions of Definitions 2.1 and 2.2, for a self-map of `ℝ` -/

/-- Lebesgue measure on `[0, 1)`, as a probability measure on `ℝ`. -/
noncomputable def unitMeas : Measure ℝ := volume.restrict (Set.Ico 0 1)

/-- **Definition 2.1** (unique ergodicity): the Birkhoff averages of every continuous test function
converge to their integral, uniformly. -/
def UniqueErgodicFun (f : ℝ → ℝ) : Prop :=
  ∀ ψ : ℝ → ℝ, Continuous ψ → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
    ∀ n ≥ N, ∀ x ∈ Set.Ico (0 : ℝ) 1,
      |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ψ (f^[i] x) - ∫ y, ψ y ∂unitMeas| ≤ ε

/-- **Definition 2.2**: rigid by translations. -/
def IsRigidByTranslationsFun (f : ℝ → ℝ) : Prop :=
  ∃ q : ℕ → ℕ, ∃ t : ℕ → ℝ, ∃ B : ℕ → Set ℝ,
    Tendsto q atTop atTop ∧ Tendsto t atTop (nhds 0) ∧
      (∀ n, B n ⊆ Set.Ico (0 : ℝ) 1) ∧ (∀ n, MeasurableSet (B n)) ∧
        Tendsto (fun n => unitMeas.real (B n)) atTop (nhds 1) ∧
          ∀ (n : ℕ) (x : ℝ), x ∈ B n → f^[q n] x = x + t n

/-! ## The two external hypotheses of the paper -/

/-- The paper's irreducibility of a permutation. -/
def IsIrreduciblePerm {d : ℕ} (π : Equiv.Perm (Fin d)) : Prop :=
  ∀ k : Fin d, (∀ i : Fin d, i ≤ k → π i ≤ k) → ∀ i : Fin d, i ≤ k

/-- **Masur–Veech**: for `d ≥ 2` and every irreducible permutation, almost every length vector
gives a uniquely ergodic exchange.  The hypothesis is stated for the *map* `mkIETFun lam π 0`, not
for an `Equiv` packaging of it: unique ergodicity is a property of the self-map of `ℝ`.  (The
restriction `2 ≤ d` is necessary: on one cell the exchange is the identity for every length
vector, and the identity is not uniquely ergodic.) -/
def MasurVeechFun : Prop :=
  ∀ (d : ℕ) (_ : 2 ≤ d) [NeZero d] (π : Equiv.Perm (Fin d)), IsIrreduciblePerm π →
    ∀ᵐ lam ∂(simplexVolume d), UniqueErgodicFun (mkIETFun lam π 0)

/-- **Veech rigidity**: for every irreducible permutation, almost every length vector gives an
exchange rigid by translations.  Like `MasurVeech`, it is stated for the map `mkIETFun lam π 0`. -/
def VeechRigidityFun : Prop :=
  ∀ (d : ℕ) [NeZero d] (π : Equiv.Perm (Fin d)), IsIrreduciblePerm π →
    ∀ᵐ lam ∂(simplexVolume d), IsRigidByTranslationsFun (mkIETFun lam π 0)

/-! ## Words in the two generators -/

/-- **The evaluation of a word in two equivs**: the `Equiv`-valued analogue of `evalWord`, for a
pair of permutations of `ℝ`. -/
noncomputable def evalWordEquiv (w : FreeGroup (Fin 2)) (f g : Equiv ℝ ℝ) : Equiv ℝ ℝ :=
  FreeGroup.lift (fun i : Fin 2 => if i = 0 then f else g) w

/-! ## The theorem -/

/-- **The main theorem, weak form.**  Granting Masur–Veech's theorem and Veech's rigidity for the
irreducible block permutations, for almost every pair of length vectors of total mass `1` the two
exchanges satisfy a nontrivial relation in the group of permutations of `ℝ`.

This is the `main` of `Challenge.lean`, next to this file, with the two external inputs of the paper
admitted as hypotheses; it is proved in `IETFree/ChallengeWeakSolved.lean`. -/
theorem main (hMV : MasurVeechFun) (hVR : VeechRigidityFun) {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
    ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧
      evalWordEquiv w (mkIETEquiv p.1 π 0) (mkIETEquiv p.2 σ 0) = 1 := by
  sorry
