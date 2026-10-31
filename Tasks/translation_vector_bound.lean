/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib

/-!
# The translation-vector bound: coefficients of a word's displacement are linear in the word length

Let `f` and `g` be permutations of `ℝ` whose displacements are **lattice vectors with coefficients in
`{-1, 0, 1}`**:

`f y = y + ∑ i, (Df y i : ℝ) * lam i` with `|Df y i| ≤ 1`, and similarly `g` with `mu`.

Then for every word `w` in two generators and every `x : ℝ`, the displacement of `w(f, g)` at `x` is a
lattice vector whose coefficients are bounded by the **word length** of `w`:

`w(f,g) x = x + ∑ i, (a i : ℝ) * lam i + ∑ j, (b j : ℝ) * mu j`,
with `|a i| ≤ |w|` and `|b j| ≤ |w|` for all `i`, `j`.

This is the arithmetic content of the passage, in the proof of the paper's Theorem 2.6, that "the
numbers `a_i` and `b_j` that show up in this formula are all bounded linearly in terms of the word
length `|w_n|`, as the translation vectors for one map involve coefficients bounded by `1` in absolute
value": for a single interval exchange with lengths `lam` and permutation `π`, the displacement on the
`i`-th interval is `∑_{π j < π i} lam j - ∑_{j < i} lam j`, i.e. a lattice vector with coefficients in
`{-1, 0, 1}`; composing words adds such vectors, so a word of length `n` gets coefficients in
`[-n, n]`.  The application is the Diophantine lower bound `C / max |a_i|^c ≤ ℓ` for the length `ℓ` of
a nontrivial translation interval of `w(f, g)`, which becomes `C' / |w|^c ≤ ℓ`.

## Route

1. Prove the statement for a **list** `L : List (Fin 2 × Bool)` spelling the word, with bound
   `L.length`, by induction on `L`:
   * the empty list has displacement `0`;
   * `(i, true)` : `eval (L ++ [(i,true)]) x = f_i (eval L x)` (or `g_i`), and the displacement is
     the displacement of `eval L` at `x` plus the displacement of `f_i` at `eval L x` — the
     **cocycle identity** `p (q x) - x = (p (q x) - q x) + (q x - x)`;
   * `(i, false)` : `f_i⁻¹ y - y = -(f_i z - z)` where `z = f_i⁻¹ y` (the displacement at the *other*
     point, with the sign reversed);
   * coefficient vectors add, and `[-m,m]^d + [-n,n]^d ⊆ [-(m+n), m+n]^d`.
   For the coefficient bookkeeping it is convenient to keep the *whole* coefficient vector
   (`a` and `b` together) as a function `Fin d ⊕ Fin e → ℤ`.
2. Transfer from lists to `w : FreeGroup (Fin 2)` by taking the spelling `w.toWord`, using
   `FreeGroup.mk_toWord : FreeGroup.mk w.toWord = w` and the fact that `FreeGroup.lift` of a word only
   depends on its reduced word (`FreeGroup.toWord` is a spelling of the same element).
-/

/-- **The translation-vector bound.** For generators whose displacements are lattice vectors with
coefficients in `{-1, 0, 1}`, the displacement of any word of length `n` is a lattice vector with
coefficients bounded by `n`. -/
theorem exists_lattice_displacement {d e : ℕ} (lam : Fin d → ℝ) (mu : Fin e → ℝ)
    (f g : Equiv.Perm ℝ)
    (Df : ℝ → Fin d → ℤ) (Dg : ℝ → Fin e → ℤ)
    (hf : ∀ y, f y = y + ∑ i, (Df y i : ℝ) * lam i) (hfb : ∀ y i, |Df y i| ≤ 1)
    (hg : ∀ y, g y = y + ∑ j, (Dg y j : ℝ) * mu j) (hgb : ∀ y j, |Dg y j| ≤ 1)
    (w : FreeGroup (Fin 2)) (x : ℝ) :
    ∃ a : Fin d → ℤ, ∃ b : Fin e → ℤ,
      (∀ i, |a i| ≤ ((FreeGroup.toWord w).length : ℤ)) ∧
        (∀ j, |b j| ≤ ((FreeGroup.toWord w).length : ℤ)) ∧
        FreeGroup.lift (fun i : Fin 2 => if i = 0 then f else g) w x
          = x + (∑ i, (a i : ℝ) * lam i) + (∑ j, (b j : ℝ) * mu j) := by
  sorry
