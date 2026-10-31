/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.BlockEndpoints
import IETFree.IntegerAffine
import IETFree.InvariantInterval

/-!
The integer-affine data of a block, and the Diophantine transfer.

The paper's step inside `lem:nontrivial_comp` — "the `νᵢ` and the `μ'_j` are all integer linear
combinations of `(λ₁,…,λ_d, μ₁,…,μ_e)`" — is made explicit here: each entry of the marked list of a
good region agrees on the region with an integer-affine function of the free parameters, and a
family of integer-affine functions is Diophantine after rescaling by the block mass.

* `GoodRegion.exists_isIntAffine_s`, `GoodRegion.sAffine`, `GoodRegion.isIntAffine_sAffine`,
  `GoodRegion.sAffine_spec`: every entry of the marked list is integer affine on the region;
* `GoodRegion.compLenVec_coe_eq`: the cell lengths of the composition in real coordinates, against
  the integer-affine representative `G.sAffine`; and `cutAffine_eq_leftEnd`, `sum_sub_mul`, the two
  algebraic identities the assembly needs;
* the `g`-cell lengths in real coordinates (`gLenAffine`, `gUpperEnd`, with `isIntAffine_gUpperEnd`
  and their evaluation lemmas) and `GoodRegion.exists_isIntAffine_truncatedLengths`: the `μ'` family
  of a block — the `g`-cell pieces truncated to the block — is a family of integer-affine functions;
* `IsDiophantine.of_intAffine_family`: the transfer of the Diophantine condition to a family of
  integer-affine functions rescaled by a positive parameter, which is what the block needs (the
  block length vector and the rescaled `g`-cell pieces are such a family, see
  `isDiophantine_blockPair` in `IETFree.BlockLemma`).

The versions for a *globally* monotone list — the block lengths as integer-affine functions, and
the Diophantine transfer, both indexed by `hmono : ∀ q, StrictMono fun k => G.s k q` — are gone: a
`GoodRegion` does not supply such an `hmono`, and the block's length vector is `G.cellLen hq` at the
point `q`, which is what the assembly uses.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

variable {d e : ℕ} [NeZero d] [NeZero e]

namespace GoodRegion

theorem exists_isIntAffine_s {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
    {q₀ : PReal d e} (G : GoodRegion d e π σ q₀) (k : Fin (G.n + 1)) :
    ∃ g : ParamAffine d e, IsIntAffine g ∧ ∀ q ∈ G.O, G.s k q = g q := by
  classical
  -- the lengths of `f` and `g` are positive on the region, so the map is the free-coordinate map
  have hmem : ∀ q ∈ G.O, simplexMap d q.1 ∈ simplex d ∧ simplexMap e q.2 ∈ simplex e := by
    intro q hq
    have hq' := G.subset_region q hq
    exact ⟨simplexMap_mem_simplex_fin hq'.1.1 hq'.1.2,
      simplexMap_mem_simplex_fin hq'.2.1 hq'.2.2⟩
  rcases G.surj k with h0 | hlast | ⟨i, hi⟩ | ⟨j, hj⟩
  · -- `k = 0`: the entry is the constant `0`
    subst h0
    exact ⟨0, isIntAffine_zero (d := d) (e := e),
      fun q hq => by rw [G.s_zero (q := q) hq]; rfl⟩
  · -- `k = last`: the entry is the constant `1`
    subst hlast
    exact ⟨AffineMap.const ℝ (PReal d e) 1, isIntAffine_one (d := d) (e := e),
      fun q hq => by
        rw [G.s_last (q := q) hq]
        rfl⟩
  · -- `k = posF i`: the entry is the `i+1`-st cut of `f`
    subst hi
    refine ⟨cutAffine (e := e) ⟨i.val + 1, by have := i.isLt; omega⟩,
      isIntAffine_cutAffine _, fun q hq => ?_⟩
    exact G.shape.posF_spec q hq i
  · -- `k = posG j`: the entry is the preimage under `f` of the `j+1`-st cut of `g`
    subst hj
    refine ⟨preimageCutAffine π ⟨j.val + 1, by have := j.isLt; omega⟩ (G.shape.cellIdx j),
      isIntAffine_preimageCutAffine π _ _, fun q hq => ?_⟩
    exact G.shape.posG_spec q hq j

end GoodRegion

/-! ## A uniform integer-affine representative of the whole marked list

`exists_isIntAffine_s` is an existential for each `k`; the block construction needs the choices to
be made once and for all, so that the length of a cell is the difference of two *fixed* affine
maps. -/

namespace GoodRegion

section Uniform

variable {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)} {q₀ : PReal d e}

/-- A choice of integer-affine function agreeing with each entry of the marked list on the
region. -/
noncomputable def sAffine (G : GoodRegion d e π σ q₀) : Fin (G.n + 1) → ParamAffine d e :=
  fun k => (G.exists_isIntAffine_s k).choose

theorem isIntAffine_sAffine (G : GoodRegion d e π σ q₀) (k : Fin (G.n + 1)) :
    IsIntAffine (G.sAffine k) :=
  (G.exists_isIntAffine_s k).choose_spec.1

theorem sAffine_spec (G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O)
    (k : Fin (G.n + 1)) : G.s k q = G.sAffine k q :=
  (G.exists_isIntAffine_s k).choose_spec.2 q hq

/-- **The length of a cell of the composition is a difference of two integer-affine maps.** -/
theorem compLenVec_coe_eq (G : GoodRegion d e π σ q₀)
    {q : PReal d e} (hq : q ∈ G.O) (i : Fin G.n) :
    ((G.cellLen hq i : ℝ≥0) : ℝ) = G.sAffine i.succ q - G.sAffine i.castSucc q := by
  have h1 : ((G.cellLen hq i : ℝ≥0) : ℝ)
      = G.s i.succ q - G.s i.castSucc q := rfl
  rw [h1, ← G.sAffine_spec hq i.succ, ← G.sAffine_spec hq i.castSucc]
end Uniform

end GoodRegion

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
The truncation of the `g`-cells at the ends of a block.

The `g`-cell lengths inside a block `[u, v)` are
`max 0 (min v (upperEnd μ j) - max u (leftEnd μ j))`, and they are integer-linear in the lengths as
soon as the pattern of the two `min`/`max` is fixed on the region.  This file builds the mechanism:
every "cut" of `f` and `g` is a *small* integer combination of the two full length vectors (all
coefficients in `{-1, 0, 1}`), so two such functions that agree at one good parameter pair agree on
the whole region (`relation_of_good`), and hence the sign of their difference is constant there.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

variable {d e : ℕ} [NeZero d] [NeZero e]

namespace GoodRegion

/-- The cuts of `f` are left ends of `simplexMap`. -/
theorem cutAffine_eq_leftEnd {q : PReal d e} (hq : q.1 ∈ simplexRegion d) (k : Fin d) :
    cutAffine (e := e) k q = leftEnd (simplexMap d q.1) k := by
  rw [cutAffine_apply, leftEnd_simplexMap hq]

/-- **The difference of two integer combinations of a length vector**: subtracting the coefficient
families and then combining is the difference of the two combinations. -/
theorem sum_sub_mul {n : ℕ} (a a' : Fin n → ℤ) (lam : Fin n → ℝ) :
    (∑ i, (((a - a') i : ℤ) : ℝ) * lam i)
      = (∑ i, (a i : ℝ) * lam i) - ∑ i, (a' i : ℝ) * lam i := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.sub_apply, Int.cast_sub]
  ring

end GoodRegion

/-!
# The block's lengths as a Diophantine input

The Diophantine transfer inside Lemma 3.4 (paper `lem:nontrivial_comp`) says: if the *composition*
lengths `ν` and the `g`-cell lengths `μ'` inside the block `P` are integer linear combinations of
free parameters `(λ, μ)`, and `(λ, μ)` is Diophantine, then the rescaled pair `(ν/L, μ'/L)` (with
`L = v - u` the block mass) is again Diophantine.

The library has the two ends of that step:

* `IsDiophantine.of_int_combination` (`Diophantine.lean`) — the numerical inequality;
* `IsIntAffine` / `intAffineData` (`Presentation.lean`) — the integer-affine description of
  each marked length and the coefficient matrices extracted from it.

This file supplies the middle: the absorption of the *constant* term of an integer-affine function
into the coefficients of the integer form, via `sum_simplexMap_mul`, and the resulting packaging
lemma `IsDiophantine.of_intAffine_family`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

variable {d e : ℕ}

/-- **The packaging lemma of the Diophantine transfer.**  Let `(lam, mu)` be Diophantine and equal
to the simplex coordinates of a free parameter `q`.  Let `Fs`, `Hs` be two finite families of
integer-affine functions of the parameters — the block's composition lengths and the `g`-cell pieces
— and let `L ∈ (0, 1]` be the block mass.  If all their values at `q` are nonnegative, then the
rescaled pair `(Fs i q / L, Hs j q / L)` is Diophantine.

This is the paper's "multiply everything by `u`, and note that the `νᵢ` and the `μ'_j` are all
integer linear combinations of `(λ₁, …, λ_d, μ₁, …, μ_e)`".  The constant terms of the
integer-affine descriptions are absorbed into the last simplex coordinate by `sum_simplexMap_mul`,
and the coefficient matrices are those of `intAffineData`, enlarged by that constant. -/
theorem IsDiophantine.of_intAffine_family {d e : ℕ} [NeZero d] [NeZero e]
    {lam : Fin d → ℝ≥0} {mu : Fin e → ℝ≥0} (hdio : IsDiophantine lam mu)
    {r s : ℕ} {Fs : Fin r → ParamAffine d e} {Hs : Fin s → ParamAffine d e}
    (hFs : ∀ i, IsIntAffine (Fs i)) (hHs : ∀ j, IsIntAffine (Hs j))
    (hrs : 0 < r + s) {q : PReal d e}
    (hq : q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e)
    (hlam : lam = simplexMap d q.1) (hmu : mu = simplexMap e q.2)
    {L : ℝ} (hL0 : 0 < L) (hL1 : L ≤ 1)
    (hFnn : ∀ i, 0 ≤ Fs i q) (hHnn : ∀ j, 0 ≤ Hs j q) :
    IsDiophantine (fun i => ⟨Fs i q / L, div_nonneg (hFnn i) hL0.le⟩)
      (fun j => ⟨Hs j q / L, div_nonneg (hHnn j) hL0.le⟩) := by
  classical
  obtain ⟨p, rfl⟩ : ∃ p, d = p + 1 := ⟨d - 1, (Nat.sub_add_cancel (NeZero.pos d)).symm⟩
  obtain ⟨p', rfl⟩ : ∃ p', e = p' + 1 := ⟨e - 1, (Nat.sub_add_cancel (NeZero.pos e)).symm⟩
  -- the coefficient matrices and the constants of the two families
  obtain ⟨K1, hK1, c1, A1, B1, hA1, hB1, hspec1⟩ := intAffineData Fs hFs
  obtain ⟨K2, hK2, c2, A2, B2, hA2, hB2, hspec2⟩ := intAffineData Hs hHs
  -- a bound for the coefficients *and* the constants
  obtain ⟨M, hMpos, hMK1, hMK2, hMc1, hMc2⟩ : ∃ M : ℕ, 0 < M ∧ K1 ≤ M ∧ K2 ≤ M ∧
      (∀ i, (c1 i).natAbs ≤ M) ∧ (∀ j, (c2 j).natAbs ≤ M) := by
    refine ⟨max (max K1 K2) (max (Finset.univ.sup fun i => (c1 i).natAbs)
      (Finset.univ.sup fun j => (c2 j).natAbs)), ?_, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), ?_, ?_⟩
    · have : 0 < max K1 K2 := lt_of_lt_of_le hK1 (le_max_left _ _)
      exact lt_of_lt_of_le this (le_max_left _ _)
    · intro i
      exact le_trans (Finset.le_sup (f := fun i => (c1 i).natAbs) (Finset.mem_univ i))
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · intro j
      exact le_trans (Finset.le_sup (f := fun j => (c2 j).natAbs) (Finset.mem_univ j))
        (le_trans (le_max_right _ _) (le_max_right _ _))
  have hAM : ∀ (i : Fin r) (k : Fin p), (A1 i k).natAbs ≤ M := fun i k => le_trans (hA1 i k) hMK1
  have hBM : ∀ (i : Fin r) (l : Fin p'), (B1 i l).natAbs ≤ M := fun i l => le_trans (hB1 i l) hMK1
  have hAM' : ∀ (j : Fin s) (k : Fin p), (A2 j k).natAbs ≤ M := fun j k => le_trans (hA2 j k) hMK2
  have hBM' : ∀ (j : Fin s) (l : Fin p'), (B2 j l).natAbs ≤ M := fun j l => le_trans (hB2 j l) hMK2
  -- the coefficient matrices, with the constant term added to every entry of the `λ` part
  -- (equivalently: to all non-last coordinates, and `c` alone on the last one)
  set Ahat : Fin r → Fin (p + 1) → ℤ :=
    fun i => Fin.snoc (α := fun _ => ℤ) (fun k : Fin p => A1 i k + c1 i) (c1 i) with hAhat
  set Bhat : Fin r → Fin (p' + 1) → ℤ :=
    fun i => Fin.snoc (α := fun _ => ℤ) (fun l : Fin p' => B1 i l) 0 with hBhat
  set Ahat' : Fin s → Fin (p + 1) → ℤ :=
    fun j => Fin.snoc (α := fun _ => ℤ) (fun k : Fin p => A2 j k + c2 j) (c2 j) with hAhat'
  set Bhat' : Fin s → Fin (p' + 1) → ℤ :=
    fun j => Fin.snoc (α := fun _ => ℤ) (fun l : Fin p' => B2 j l) 0 with hBhat'
  have hAhatSucc : ∀ (i : Fin r) (k : Fin p), Ahat i k.castSucc = A1 i k + c1 i := by
    intro i k
    rw [hAhat]
    exact Fin.snoc_castSucc _ _ _
  have hAhatLast : ∀ i : Fin r, Ahat i (Fin.last p) = c1 i := by
    intro i
    rw [hAhat]
    exact Fin.snoc_last _ _
  have hBhatSucc : ∀ (i : Fin r) (l : Fin p'), Bhat i l.castSucc = B1 i l := by
    intro i l
    rw [hBhat]
    exact Fin.snoc_castSucc _ _ _
  have hBhatLast : ∀ i : Fin r, Bhat i (Fin.last p') = 0 := by
    intro i
    rw [hBhat]
    exact Fin.snoc_last _ _
  have hAhatSucc' : ∀ (j : Fin s) (k : Fin p), Ahat' j k.castSucc = A2 j k + c2 j := by
    intro j k
    rw [hAhat']
    exact Fin.snoc_castSucc _ _ _
  have hAhatLast' : ∀ j : Fin s, Ahat' j (Fin.last p) = c2 j := by
    intro j
    rw [hAhat']
    exact Fin.snoc_last _ _
  have hBhatSucc' : ∀ (j : Fin s) (l : Fin p'), Bhat' j l.castSucc = B2 j l := by
    intro j l
    rw [hBhat']
    exact Fin.snoc_castSucc _ _ _
  have hBhatLast' : ∀ j : Fin s, Bhat' j (Fin.last p') = 0 := by
    intro j
    rw [hBhat']
    exact Fin.snoc_last _ _
  -- the uniform bound
  set K : ℕ := 2 * M with hK
  have hKpos : 0 < K := by rw [hK]; omega
  have hAhatBound : ∀ (i : Fin r) (k : Fin (p + 1)), (Ahat i k).natAbs ≤ K := by
    intro i k
    refine Fin.lastCases ?_ ?_ k
    · rw [hAhatLast i, hK]
      have := hMc1 i
      omega
    · intro k
      rw [hAhatSucc i k, hK]
      have h1 := hAM i k
      have h2 := hMc1 i
      have := Int.natAbs_add_le (A1 i k) (c1 i)
      omega
  have hBhatBound : ∀ (i : Fin r) (l : Fin (p' + 1)), (Bhat i l).natAbs ≤ K := by
    intro i l
    refine Fin.lastCases ?_ ?_ l
    · rw [hBhatLast i]; simp
    · intro l
      rw [hBhatSucc i l, hK]
      have := hBM i l
      omega
  have hAhatBound' : ∀ (j : Fin s) (k : Fin (p + 1)), (Ahat' j k).natAbs ≤ K := by
    intro j k
    refine Fin.lastCases ?_ ?_ k
    · rw [hAhatLast' j, hK]
      have := hMc2 j
      omega
    · intro k
      rw [hAhatSucc' j k, hK]
      have h1 := hAM' j k
      have h2 := hMc2 j
      have := Int.natAbs_add_le (A2 j k) (c2 j)
      omega
  have hBhatBound' : ∀ (j : Fin s) (l : Fin (p' + 1)), (Bhat' j l).natAbs ≤ K := by
    intro j l
    refine Fin.lastCases ?_ ?_ l
    · rw [hBhatLast' j]; simp
    · intro l
      rw [hBhatSucc' j l, hK]
      have := hBM' j l
      omega
  -- the integer forms of the two families
  have hw : ∀ i : Fin r, (Fs i q : ℝ)
      = ∑ k : Fin (p + 1), (Ahat i k : ℝ) * (lam k : ℝ)
        + ∑ l : Fin (p' + 1), (Bhat i l : ℝ) * (mu l : ℝ) := by
    intro i
    have h1 : (∑ k : Fin (p + 1), (Ahat i k : ℝ) * (lam k : ℝ))
        = ∑ k : Fin p, (A1 i k : ℝ) * q.1 k + (c1 i : ℝ) := by
      have key : (∑ k : Fin (p + 1), (Ahat i k : ℝ) * (lam k : ℝ))
          = ∑ k : Fin p, ((Ahat i k.castSucc - Ahat i (Fin.last p) : ℤ) : ℝ) * q.1 k
            + (Ahat i (Fin.last p) : ℝ) := by
        rw [hlam]
        exact sum_simplexMap_mul hq.1.1 hq.1.2 (Ahat i)
      rw [key]
      have hsimp : ∀ k : Fin p,
          ((Ahat i k.castSucc - Ahat i (Fin.last p) : ℤ) : ℝ) = (A1 i k : ℝ) := by
        intro k
        rw [hAhatSucc i k, hAhatLast i]
        push_cast
        ring
      simp only [hsimp]
      rw [hAhatLast i]
    have h2 : (∑ l : Fin (p' + 1), (Bhat i l : ℝ) * (mu l : ℝ))
        = ∑ l : Fin p', (B1 i l : ℝ) * q.2 l + ((0 : ℤ) : ℝ) := by
      have key : (∑ l : Fin (p' + 1), (Bhat i l : ℝ) * (mu l : ℝ))
          = ∑ l : Fin p', ((Bhat i l.castSucc - Bhat i (Fin.last p') : ℤ) : ℝ) * q.2 l
            + (Bhat i (Fin.last p') : ℝ) := by
        rw [hmu]
        exact sum_simplexMap_mul hq.2.1 hq.2.2 (Bhat i)
      rw [key]
      have hsimp : ∀ l : Fin p',
          ((Bhat i l.castSucc - Bhat i (Fin.last p') : ℤ) : ℝ) = (B1 i l : ℝ) := by
        intro l
        rw [hBhatSucc i l, hBhatLast i]
        push_cast
        ring
      simp only [hsimp]
      rw [hBhatLast i]
    have hspec1' : (Fs i q : ℝ) = (c1 i : ℝ) + ∑ k : Fin p, (A1 i k : ℝ) * q.1 k
        + ∑ l : Fin p', (B1 i l : ℝ) * q.2 l := hspec1 i q
    rw [h1, h2, hspec1']
    ring
  have hw' : ∀ j : Fin s, (Hs j q : ℝ)
      = ∑ k : Fin (p + 1), (Ahat' j k : ℝ) * (lam k : ℝ)
        + ∑ l : Fin (p' + 1), (Bhat' j l : ℝ) * (mu l : ℝ) := by
    intro j
    have h1 : (∑ k : Fin (p + 1), (Ahat' j k : ℝ) * (lam k : ℝ))
        = ∑ k : Fin p, (A2 j k : ℝ) * q.1 k + (c2 j : ℝ) := by
      have key : (∑ k : Fin (p + 1), (Ahat' j k : ℝ) * (lam k : ℝ))
          = ∑ k : Fin p, ((Ahat' j k.castSucc - Ahat' j (Fin.last p) : ℤ) : ℝ) * q.1 k
            + (Ahat' j (Fin.last p) : ℝ) := by
        rw [hlam]
        exact sum_simplexMap_mul hq.1.1 hq.1.2 (Ahat' j)
      rw [key]
      have hsimp : ∀ k : Fin p,
          ((Ahat' j k.castSucc - Ahat' j (Fin.last p) : ℤ) : ℝ) = (A2 j k : ℝ) := by
        intro k
        rw [hAhatSucc' j k, hAhatLast' j]
        push_cast
        ring
      simp only [hsimp]
      rw [hAhatLast' j]
    have h2 : (∑ l : Fin (p' + 1), (Bhat' j l : ℝ) * (mu l : ℝ))
        = ∑ l : Fin p', (B2 j l : ℝ) * q.2 l + ((0 : ℤ) : ℝ) := by
      have key : (∑ l : Fin (p' + 1), (Bhat' j l : ℝ) * (mu l : ℝ))
          = ∑ l : Fin p', ((Bhat' j l.castSucc - Bhat' j (Fin.last p') : ℤ) : ℝ) * q.2 l
            + (Bhat' j (Fin.last p') : ℝ) := by
        rw [hmu]
        exact sum_simplexMap_mul hq.2.1 hq.2.2 (Bhat' j)
      rw [key]
      have hsimp : ∀ l : Fin p',
          ((Bhat' j l.castSucc - Bhat' j (Fin.last p') : ℤ) : ℝ) = (B2 j l : ℝ) := by
        intro l
        rw [hBhatSucc' j l, hBhatLast' j]
        push_cast
        ring
      simp only [hsimp]
      rw [hBhatLast' j]
    have hspec2' : (Hs j q : ℝ) = (c2 j : ℝ) + ∑ k : Fin p, (A2 j k : ℝ) * q.1 k
        + ∑ l : Fin p', (B2 j l : ℝ) * q.2 l := hspec2 j q
    rw [h1, h2, hspec2']
    ring
  exact hdio.of_int_combination hKpos (fun i => (⟨Fs i q, hFnn i⟩ : ℝ≥0))
    (fun j => (⟨Hs j q, hHnn j⟩ : ℝ≥0)) L hL0 hL1 Ahat Bhat Ahat' Bhat' hrs
    hAhatBound hBhatBound hAhatBound' hBhatBound' hw hw'

/-! ### The cell lengths of `g` in real coordinates

The block construction never needs the `NNReal` length vector: the real cell lengths of `g` are free
coordinates (and `1 - ∑ q.2` at the last cell), so they are integer affine on *all* of `PReal d e`,
and `leftEnd`/`upperEnd` are integer affine accordingly (`cutAffineRight` and `gUpperEnd`).  The
identifications with `leftEnd`/`upperEnd` of `(simplexMap e q.2 : Fin e → ℝ≥0)` hold on the open
simplex region (`cutAffineRight_eq_leftEnd`, `gLenAffine_eq`, `gUpperEnd_eq`), which is exactly
where they are used. -/

section GCells

variable {d e : ℕ} [NeZero d] [NeZero e]

/-- The real length of the `j`-th cell of `g` as an affine function of the free parameters: the
free coordinate `q.2 j` away from the last cell, and the remaining mass `1 - ∑ q.2` at the last one.
This is the `g`-analogue of `imageLenAffine`, and it is why no `NNReal` is needed in the block
construction: on the open simplex region it is `(simplexMap e q.2 j : ℝ)`, but as a free-coordinate
expression it is integer affine on *all* of `PReal d e`, not merely on a region. -/
noncomputable def gLenAffine (j : Fin e) : ParamAffine d e :=
  if h : j.val + 1 = e then (AffineMap.const ℝ (PReal d e) (1 : ℝ))
      - ∑ m : Fin (e - 1), rightCoordAffine (d := d) m
    else rightCoordAffine (d := d) ⟨j.val, by have h1 := j.isLt; omega⟩

omit [NeZero d] [NeZero e] in
theorem gLenAffine_eq {q : PReal d e} (hq : q.2 ∈ simplexRegion e) (j : Fin e) :
    gLenAffine (d := d) j q = (simplexMap e q.2 j : ℝ) := by
  by_cases h : j.val + 1 = e
  · rw [gLenAffine, dif_pos h, simplexMap, dif_pos h, AffineMap.coe_sub, Pi.sub_apply,
      AffineMap.const_apply, AffineMap.sum_apply, Real.coe_toNNReal _ (by linarith [hq.2])]
    simp only [rightCoordAffine_apply]
  · rw [gLenAffine, dif_neg h, simplexMap, dif_neg h, rightCoordAffine_apply,
      Real.coe_toNNReal _ (le_of_lt (hq.1 _))]

/-- The right end of the `j`-th cell of `g`, in real coordinates: the next cut, and `1` at the last
cell.  Integer affine on all of `PReal d e`. -/
noncomputable def gUpperEnd (j : Fin e) : ParamAffine d e :=
  if h : j.val + 1 < e then cutAffineRight (d := d) ⟨j.val + 1, h⟩
    else AffineMap.const ℝ (PReal d e) (1 : ℝ)

omit [NeZero d] [NeZero e] in
theorem isIntAffine_gUpperEnd (j : Fin e) : IsIntAffine (gUpperEnd (d := d) j) := by
  unfold gUpperEnd
  split_ifs with h
  · exact isIntAffine_cutAffineRight _
  · exact isIntAffine_one

omit [NeZero d] in
theorem gUpperEnd_eq {q : PReal d e} (hq : q.2 ∈ simplexRegion e) (j : Fin e) :
    gUpperEnd (d := d) j q = (upperEnd (simplexMap e q.2) j : ℝ) := by
  unfold gUpperEnd
  split_ifs with h
  · rw [cutAffineRight_eq_leftEnd hq, ← leftEnd_eq_upperEnd_of_succ (simplexMap e q.2) h]
  · have hlast : j.val + 1 = e := by have := j.isLt; omega
    have htot : (∑ i, (simplexMap e q.2 i : ℝ)) = 1 := by
      have hm := simplexMap_mem_simplex_fin hq.1 hq.2
      rw [← NNReal.coe_sum, hm, NNReal.coe_one]
    rw [AffineMap.const_apply,
      upperEnd_of_max (lam := simplexMap e q.2) (fun i => by
        rw [Fin.le_def]; have := i.isLt; omega), htot]

end GCells

/-! ### The `μ'` family of a block: the `g`-cell pieces as integer-affine functions

The pieces of `g` inside a block `[s i₀, s i₁)` are the truncated cell lengths
`max 0 (min v (upperEnd j) - max u (leftEnd j))`.  At a *point* `q` of the region the truncation
pattern is decided by the ordering of the real numbers at `q`, and each branch is a difference of
two of the globally integer-affine functions `G.sAffine i₀`, `G.sAffine i₁`, `cutAffineRight j`,
`gUpperEnd j`; so no rigidity argument is needed, only the pointwise reading. -/

namespace GoodRegion

variable {d e : ℕ} [NeZero d] [NeZero e] {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
  {q₀ : PReal d e}

/-- **The integer-affine family of the `g`-cell pieces of a block.**  At a point `q` of the region,
the length of the part of the `j`-th cell of `g` that lies in the block `[s i₀, s i₁)` agrees with a
*globally* integer-affine function of the free parameters.

No rigidity argument is needed: the truncation pattern (`min` with the right end of the block, `max`
with the left end, and `max 0`) is read off the ordering of the real numbers at `q` itself, and each
of the four possible branches is a difference of two of the globally integer-affine functions
`G.sAffine i₀`, `G.sAffine i₁`, `cutAffineRight j`, `gUpperEnd j`. -/
theorem exists_isIntAffine_truncatedLengths (G : GoodRegion d e π σ q₀)
    {q : PReal d e} (hq : q ∈ G.O)
    {i₀ i₁ : Fin (G.n + 1)} :
    ∃ (Hs : Fin e → ParamAffine d e), (∀ j, IsIntAffine (Hs j)) ∧
      ∀ j : Fin e, Hs j q = max 0 (min (G.s i₁ q) (upperEnd (simplexMap e q.2) j : ℝ)
        - max (G.s i₀ q) (leftEnd (simplexMap e q.2) j : ℝ)) := by
  classical
  obtain ⟨hp, hw⟩ := G.subset_region q hq
  have hex : ∀ j : Fin e, ∃ h : ParamAffine d e, IsIntAffine h ∧
      h q = max 0 (min (G.s i₁ q) (upperEnd (simplexMap e q.2) j : ℝ)
        - max (G.s i₀ q) (leftEnd (simplexMap e q.2) j : ℝ)) := by
    intro j
    rw [← gUpperEnd_eq hw j, ← cutAffineRight_eq_leftEnd hw j, G.sAffine_spec hq i₀,
      G.sAffine_spec hq i₁]
    set U := gUpperEnd (d := d) j with hUdef
    set L := cutAffineRight (d := d) j with hLdef
    set u := G.sAffine i₀ with hudef
    set v := G.sAffine i₁ with hvdef
    have hU : IsIntAffine U := isIntAffine_gUpperEnd j
    have hL : IsIntAffine L := isIntAffine_cutAffineRight j
    have hu : IsIntAffine u := G.isIntAffine_sAffine i₀
    have hv : IsIntAffine v := G.isIntAffine_sAffine i₁
    rcases le_total (L q) (u q) with h1 | h1 <;> rcases le_total (v q) (U q) with h2 | h2
    · -- `L ≤ u`, `v ≤ U`: the piece is `v - u` clamped at `0`
      refine ⟨if (0 : ℝ) ≤ v q - u q then v - u else 0,
        IsIntAffine.ite _ (hv.sub hu) isIntAffine_zero, ?_⟩
      rw [min_eq_left h2, max_eq_left h1]
      by_cases h3 : (0 : ℝ) ≤ v q - u q
      · rw [if_pos h3, AffineMap.coe_sub, Pi.sub_apply, max_eq_right h3]
      · rw [if_neg h3, max_eq_left (le_of_lt (not_le.mp h3))]
        simp
    · -- `L ≤ u`, `U ≤ v`: the piece is `U - u`
      refine ⟨if (0 : ℝ) ≤ U q - u q then U - u else 0,
        IsIntAffine.ite _ (hU.sub hu) isIntAffine_zero, ?_⟩
      rw [min_eq_right h2, max_eq_left h1]
      by_cases h3 : (0 : ℝ) ≤ U q - u q
      · rw [if_pos h3, AffineMap.coe_sub, Pi.sub_apply, max_eq_right h3]
      · rw [if_neg h3, max_eq_left (le_of_lt (not_le.mp h3))]
        simp
    · -- `u ≤ L`, `v ≤ U`: the piece is `v - L`
      refine ⟨if (0 : ℝ) ≤ v q - L q then v - L else 0,
        IsIntAffine.ite _ (hv.sub hL) isIntAffine_zero, ?_⟩
      rw [min_eq_left h2, max_eq_right h1]
      by_cases h3 : (0 : ℝ) ≤ v q - L q
      · rw [if_pos h3, AffineMap.coe_sub, Pi.sub_apply, max_eq_right h3]
      · rw [if_neg h3, max_eq_left (le_of_lt (not_le.mp h3))]
        simp
    · -- `u ≤ L`, `U ≤ v`: the piece is `U - L`
      refine ⟨if (0 : ℝ) ≤ U q - L q then U - L else 0,
        IsIntAffine.ite _ (hU.sub hL) isIntAffine_zero, ?_⟩
      rw [min_eq_right h2, max_eq_right h1]
      by_cases h3 : (0 : ℝ) ≤ U q - L q
      · rw [if_pos h3, AffineMap.coe_sub, Pi.sub_apply, max_eq_right h3]
      · rw [if_neg h3, max_eq_left (le_of_lt (not_le.mp h3))]
        simp
  choose Hs hHs hval using hex
  exact ⟨Hs, hHs, hval⟩

end GoodRegion
