/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.IET

/-!
# Interval exchanges from two bijections

This is the first module of the unique-ergodicity side of the library (`IETFree/RauzyVeech/`,
`IETFree/Rigidity/`, `IETFree/UniqueErgodicity/`).  It fixes the objects those developments work
with:

* `IETDatum₂ α n` — the source's combinatorial data $(A,\pi_0,\pi_1)$: **two** bijections between a
  finite alphabet `α` and `Fin n` (`piTop`, `piBottom`), not a single permutation;
* `Irreducible` — irreducibility of the datum (the source's admissibility, 2.5), stated through the
  permutation `piTop * piBottom.symm`;
* `toIET` — the exchange, obtained from the copied single-permutation API (`mkIETFun`, `mkIET1'`)
  applied to `piTop * piBottom.symm`; it is total, with the identity as junk value off the simplex
  (the same convention as `mkIETFun`);
* `simplexOn`, `simplexVolumeOn` — the simplex of `α`-indexed length vectors and its
  `(card α - 1)`-dimensional Lebesgue measure, which depends on the alphabet only;
* `IsRigidByTranslations` — Definition 2.2 of the paper (Veech's rigidity), the second notion the
  main theorem is stated with.  The first, `UniqueErgodic` (with `Invariant`), is in
  `IETFree/IET.lean`, below this module, so that `IETFree/Pair/` and
  `IETFree/UniqueErgodicity/` share it.

The single-exchange API (`IsCutSet`, `IsIET`, `mkIETFun`, `mkIET1'`, `simplexVolume`, …) is the
library's own, from `IETFree.CutSet`, `IETFree.CutSetMeasure` and `IETFree.IET`; this module adds
the two-bijection datum on top of it. -/

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

/-! ## The simplex -/

/-- The simplex of `α`-indexed length vectors.  It does not involve the combinatorial data. -/
def simplexOn (α : Type*) [Fintype α] : Set (α → ℝ≥0) := {lam | ∑ a, lam a = 1}

@[simp] theorem mem_simplexOn {α : Type*} [Fintype α] {lam : α → ℝ≥0} :
    lam ∈ simplexOn α ↔ ∑ a, lam a = 1 := Iff.rfl

/-- The simplex of length vectors of total mass `1`, on `Fin d`: the `α = Fin d` case of
`simplexOn`, kept under its own name because the single-permutation statements use it. -/
def simplex (d : ℕ) : Set (Fin d → ℝ≥0) := {lam | ∑ i, lam i = 1}

/-- The `(card α - 1)`-dimensional Lebesgue measure on `simplexOn α`: the pushforward of the copied
`simplexVolume` along one equivalence `α ≃ Fin (card α)`. It depends on the alphabet only; the
independence of the chosen equivalence is `simplexVolume_map_perm` (its invariance under a
permutation of the coordinates), and its consequence `simplexVolumeOn_eq_map` for the particular
`piBottom` at hand. -/
noncomputable def simplexVolumeOn (α : Type*) [Fintype α] : Measure (α → ℝ≥0) :=
  (simplexVolume (Fintype.card α)).map (fun l a => l (Fintype.equivFin α a))

-- `ae_mem_simplexOn_of_nonempty` lives in `IETFree/RauzyVeech/SimplexAe.lean` and needs
-- `[Nonempty α]`: without it the statement is false (`simplexOn α = ∅` for the empty alphabet
-- while `simplexVolumeOn α` is a
-- probability measure).  Every use in the project has `α ≃ Fin n` with `n ≠ 0`.

/-! ## Combinatorial data: two bijections -/

/-- The source's combinatorial data $(A,\pi_0,\pi_1)$: **two** orderings of the same finite
alphabet, `piBottom` $=\pi_0$ and `piTop` $=\pi_1$. Keeping both (rather than the single permutation
`piTop * piBottom.symm`) is what makes the Rauzy–Veech step an operation on a fixed alphabet. -/
structure IETDatum₂ (α : Type*) [Fintype α] (n : ℕ) where
  /-- the order of the images (`π₁` of the source) -/
  piTop : α ≃ Fin n
  /-- the order of the lengths (`π₀` of the source) -/
  piBottom : α ≃ Fin n

namespace IETDatum₂

variable {α : Type*} [Fintype α] {n : ℕ}

/-- The source's permutation `π₁ ∘ π₀⁻¹` of `{1,…,d}`: the exchange only depends on it (and on the
lengths in bottom order). -/
def perm (P : IETDatum₂ α n) : Equiv.Perm (Fin n) := P.piBottom.symm.trans P.piTop

/-- Irreducibility of the datum: no proper initial segment of the permutation is invariant (the
source's admissibility, 2.5). -/
def Irreducible (P : IETDatum₂ α n) : Prop := IsIrreduciblePerm P.perm

/-- The length vector in bottom-order coordinates, i.e. `λ ∘ π_bottom⁻¹`. -/
def lengthsInBottom (P : IETDatum₂ α n) (lam : α → ℝ≥0) : Fin n → ℝ≥0 :=
  fun i => lam (P.piBottom.symm i)

theorem sum_lengthsInBottom (P : IETDatum₂ α n) {lam : α → ℝ≥0} (h : lam ∈ simplexOn α) :
    (∑ i, P.lengthsInBottom lam i) = 1 := by
  have h' : (∑ a, lam a) = 1 := h
  have h2 : (∑ i, P.lengthsInBottom lam i) = ∑ a, lam a := Equiv.sum_comp P.piBottom.symm lam
  rw [h2, h']

/-- The exchange as an element of `IET 0 1`.  It is **total**: off the simplex it is the identity,
the same junk-value convention as `mkIETFun`.  On the simplex it is `mkIET1'` of the reindexed
length
vector and of `π_top ∘ π_bottom⁻¹`. -/
noncomputable def toIET (P : IETDatum₂ α n) [NeZero n] (lam : α → ℝ≥0) : IET 0 1 := by
  classical
  exact if h : lam ∈ simplexOn α then
    mkIET1' (P.lengthsInBottom lam) P.perm (P.sum_lengthsInBottom h)
  else 1

/-- **The exit criterion**: on the simplex, the exchange of two-bijection data is the copied
single-permutation construction applied to `π_top ∘ π_bottom⁻¹`. -/
theorem toIET_eq_mkIET1 (P : IETDatum₂ α n) [NeZero n] {lam : α → ℝ≥0}
    (h : lam ∈ simplexOn α) :
    P.toIET lam = mkIET1' (P.lengthsInBottom lam) P.perm (P.sum_lengthsInBottom h) := by
  rw [toIET, dif_pos h]

/-- The involution `π_top ↔ π_bottom`; by source 2.4 it sends the exchange to its inverse. -/
def inv (P : IETDatum₂ α n) : IETDatum₂ α n := ⟨P.piBottom, P.piTop⟩

@[simp] theorem inv_piTop (P : IETDatum₂ α n) : P.inv.piTop = P.piBottom := rfl

@[simp] theorem inv_piBottom (P : IETDatum₂ α n) : P.inv.piBottom = P.piTop := rfl

@[simp] theorem inv_inv (P : IETDatum₂ α n) : P.inv.inv = P := rfl

theorem perm_inv (P : IETDatum₂ α n) : P.inv.perm = P.perm.symm := by
  ext i
  simp [perm, inv]

/-- Definitional: the function of `mkIET1' lam π h` is `mkIETFun lam π 0`. -/
theorem coe_mkIET1' {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (h : (∑ i, lam i) = 1) : ⇑(mkIET1' lam π h) = mkIETFun lam π 0 := rfl

/-- The same identity as `coe_mkIET1'`, stated on `toEquiv` so that it rewrites when the coercion
has
already been unfolded. -/
theorem toEquiv_mkIET1 {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (h : (∑ i, lam i) = 1) : (mkIET1' lam π h).toEquiv = mkIETFun lam π 0 := rfl

/-- The position of `k` in the bottom order, read off the inverse permutation: the key point is
`(π₁ ∘ π₀⁻¹)⁻¹ = π₀ ∘ π₁⁻¹`, i.e. `perm P` has inverse `π₀` after `π₁⁻¹`. -/
theorem perm_symm_apply (P : IETDatum₂ α n) (k : Fin n) :
    P.perm.symm k = P.piBottom (P.piTop.symm k) := by
  rw [Equiv.symm_apply_eq]
  simp [perm]

/-! ## The datum of a single permutation  The copied single-permutation API `mkIET1'` takes a
permutation of `Fin n` and a length vector in `Fin n` coordinates, while the induction works with
the two-bijection datum on a fixed alphabet. `ofPerm π` is the datum with `piBottom = id`: its
permutation is `π`, its lengths in bottom order are those of `Fin n`, and its exchange is `mkIET1'`
(`ofPerm_toIET`).  This is the whole translation needed to state the main theorem for a single
irreducible permutation; the converse translation is `toIET_eq_mkIET1`. -/

/-- The two-bijection datum of a single permutation, with `piBottom = id`. -/
def ofPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : IETDatum₂ (Fin n) n := ⟨π, Equiv.refl (Fin n)⟩

@[simp] theorem ofPerm_piTop {n : ℕ} (π : Equiv.Perm (Fin n)) : (ofPerm π).piTop = π := rfl

@[simp] theorem ofPerm_piBottom {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (ofPerm π).piBottom = Equiv.refl (Fin n) := rfl

@[simp] theorem ofPerm_perm {n : ℕ} (π : Equiv.Perm (Fin n)) : (ofPerm π).perm = π := by
  ext i
  rfl

@[simp] theorem ofPerm_lengthsInBottom {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    (ofPerm π).lengthsInBottom lam = lam := rfl

/-- `ofPerm` is irreducible exactly when the permutation is irreducible. -/
theorem ofPerm_irreducible_iff {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (ofPerm π).Irreducible ↔ IsIrreduciblePerm π := by
  rw [Irreducible, ofPerm_perm]

/-- On the simplex, the exchange of `ofPerm π` is `mkIET1' lam π h`. -/
theorem ofPerm_toIET {n : ℕ} [NeZero n] (π : Equiv.Perm (Fin n)) {lam : Fin n → ℝ≥0}
    (h : lam ∈ simplexOn (Fin n)) : (ofPerm π).toIET lam = mkIET1' lam π h := by
  ext x
  rw [toIET_eq_mkIET1 (ofPerm π) h, toEquiv_mkIET1, ofPerm_perm, ofPerm_lengthsInBottom]
  rfl

end IETDatum₂

/-- **Definition 2.2 of the paper**: rigid by translations. -/
def IsRigidByTranslations (f : IET 0 1) : Prop :=
  ∃ q : ℕ → ℕ, ∃ t : ℕ → ℝ, ∃ B : ℕ → Set ℝ,
    Tendsto q atTop atTop ∧ Tendsto t atTop (nhds 0) ∧
      (∀ n, B n ⊆ Set.Ico (0 : ℝ) 1) ∧ (∀ n, MeasurableSet (B n)) ∧
        Tendsto (fun n => unitMeas.real (B n)) atTop (nhds 1) ∧
          ∀ (n : ℕ) (x : ℝ), x ∈ B n → ((f ^ q n) x) = x + t n
