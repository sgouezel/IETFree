/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib

/-!
# The singularity bound: cuts of a word in two interval exchanges are lattice points

Let `f` and `g` be permutations of `ℝ` that are **piecewise translations**, with finite cut sets `Sf`
and `Sg`: on the pieces cut by `Sf` the displacement of `f` is constant and is an integer combination
of the real numbers `lam i` with coefficients in `{-1, 0, 1}` (and likewise `g` with `mu`).  Assume
moreover that the elements of `Sf`, `Sg` are themselves such lattice combinations.

Then for every word `w` in two generators there is a finite set `C` of reals which **cuts** the word
evaluation `w(f, g)` into pieces on which it is a translation, and every element of `C` is a lattice
combination of `lam` and `mu` whose coefficients are bounded by the **word length** plus one:

`c = ∑ i, (a i : ℝ) * lam i + ∑ j, (b j : ℝ) * mu j`,  `|a i| ≤ |w| + 1`, `|b j| ≤ |w| + 1`.

This is the paper's step (proof of Theorem 2.6) that "all singularities of `h_n` are of the form
`∑ a_i λ_i + ∑ b_j μ_j`, as a point which is a singularity has to be mapped by a sum of such
translation vectors to some singularity of the original maps", together with the bound "the numbers
`a_i` and `b_j` that show up in this formula are all bounded linearly in terms of the word length".
Combined with the translation-vector bound it gives: *the length of a nontrivial translation interval
of `w(f, g)` is a nonzero lattice combination with coefficients `≤ 2 |w| + 2`*, which the Diophantine
condition bounds below by `C / |w| ^ c`.

## Formulation

`S` cuts `ℝ` into the pieces determined by the equivalence relation `¬ CutSep S x y`, i.e. `x` and `y`
have the same elements of `S` in `(min x y, max x y]`; this is the `Ioc` convention of the
development (`[α, β)` pieces, a cut at `β` belongs to the next piece).

## Route

Work with a **list** `L : List (Fin 2 × Bool)` spelling the word, with `L.length + 1` as the bound,
and prove by induction on `L` that there is a finite `C` such that

* every `c ∈ C` is a lattice combination with coefficients `≤ L.length + 1`, and
* `(L.prod) x - x = (L.prod) y - y` whenever `¬ CutSep C x y` (`L.prod` being the product of the letters
  `f`, `g`, `f⁻¹`, `g⁻¹` in `Equiv.Perm ℝ`).

Step `L ↦ L ++ [p]` with letter `e` (i.e. `f`, `g`, `f⁻¹` or `g⁻¹`), writing `A = L.prod`:

* take `C' := Ce ∪ e⁻¹(C)`, where `Ce` is the cut set of the letter `e` (`Sf`, `Sg`, or their images
  `f '' Sf`, `g '' Sg` for the inverses);
* **preimages of cuts**: if `e y = c ∈ C`, then `y = c - (e y - y)`, and `e y - y` is a single-letter
  lattice combination with coefficients `≤ 1` (from the hypotheses on `Df`, `Dg`; for `e = f⁻¹` use
  the displacement of `f` at the *other* point).  Similarly `f '' Sf` consists of
  `c + (f c - c)`, and `hTV` handles preimages of deep cuts of `A` (needed because `C` may be the
  image of an already-composed set: use `hTV` with the word spelled by `L`);
* **translation**: on a piece of `Ce` the letter `e` is a translation, hence strictly monotone.
  Given `¬ CutSep C' x y`, both `x`, `y` lie in one piece of `Ce`, so `e x`, `e y` are ordered as `x`,
  `y`, and no element of `C` lies in `(min (e x) (e y), max (e x) (e y)]` — otherwise its preimage,
  which lies in `C'`, would lie in `(min x y, max x y]`.  Hence `A` translates between `e x` and
  `e y`, and `e` translates between `x` and `y`, which gives the cocycle identity
  `(A ∘ e) x - x = (A (e x) - e x) + (e x - x)`;
* coefficient bookkeeping: `|a + b| ≤ |a| + |b|`, and `Ce`'s elements have coefficients `≤ 1`, so the
  bound grows by exactly one per letter.
-/

/-- `S` separates `x` from `y`: some element of `S` lies in `(min x y, max x y]`.  With `[α, β)`
pieces, a cut at `β` is a boundary point and belongs to the next piece, hence separates. -/
def CutSep (S : Finset ℝ) (x y : ℝ) : Prop := ∃ c ∈ S, c ∈ Set.Ioc (min x y) (max x y)

/-- **The singularity bound.**  For two piecewise-translation permutations of `ℝ` whose cuts and
displacements are lattice combinations of `lam` and `mu` with coefficients in `{-1, 0, 1}`, and for
any word `w`, there is a finite set cutting `w(f, g)` into translation pieces, all of whose elements
are lattice combinations with coefficients bounded by `|w| + 1`. -/
theorem exists_lattice_cuts {d e : ℕ} (lam : Fin d → ℝ) (mu : Fin e → ℝ)
    (f g : Equiv.Perm ℝ) (Sf Sg : Finset ℝ)
    (Df : ℝ → Fin d → ℤ) (Dg : ℝ → Fin e → ℤ)
    (hf : ∀ y, f y = y + ∑ i, (Df y i : ℝ) * lam i) (hfb : ∀ y i, |Df y i| ≤ 1)
    (hg : ∀ y, g y = y + ∑ j, (Dg y j : ℝ) * mu j) (hgb : ∀ y j, |Dg y j| ≤ 1)
    (hSf : ∀ y y', ¬ CutSep Sf y y' → f y - y = f y' - y')
    (hSg : ∀ y y', ¬ CutSep Sg y y' → g y - y = g y' - y')
    (hSf_lat : ∀ c ∈ Sf, ∃ a : Fin d → ℤ, (∀ i, |a i| ≤ 1) ∧ c = ∑ i, (a i : ℝ) * lam i)
    (hSg_lat : ∀ c ∈ Sg, ∃ b : Fin e → ℤ, (∀ j, |b j| ≤ 1) ∧ c = ∑ j, (b j : ℝ) * mu j)
    (hTV : ∀ (u : FreeGroup (Fin 2)) (x : ℝ), ∃ a : Fin d → ℤ, ∃ b : Fin e → ℤ,
      (∀ i, |a i| ≤ ((FreeGroup.toWord u).length : ℤ)) ∧
        (∀ j, |b j| ≤ ((FreeGroup.toWord u).length : ℤ)) ∧
        FreeGroup.lift (fun i : Fin 2 => if i = 0 then f else g) u x
          = x + (∑ i, (a i : ℝ) * lam i) + (∑ j, (b j : ℝ) * mu j))
    (w : FreeGroup (Fin 2)) :
    ∃ C : Finset ℝ,
      (∀ c ∈ C, ∃ a : Fin d → ℤ, ∃ b : Fin e → ℤ,
        (∀ i, |a i| ≤ ((FreeGroup.toWord w).length : ℤ) + 1) ∧
          (∀ j, |b j| ≤ ((FreeGroup.toWord w).length : ℤ) + 1) ∧
          c = (∑ i, (a i : ℝ) * lam i) + (∑ j, (b j : ℝ) * mu j)) ∧
      (∀ y y', ¬ CutSep C y y' →
        FreeGroup.lift (fun i : Fin 2 => if i = 0 then f else g) w y - y
          = FreeGroup.lift (fun i : Fin 2 => if i = 0 then f else g) w y' - y') := by
  sorry
