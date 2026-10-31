/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.Presentation

/-!
Integer-affine functions of the free parameters.

A function of the free parameters is integer affine (`IsIntAffine`) when it is an integer constant
plus an integer combination of the coordinates.  The file proves that the class is closed under the
operations used in the reduction (`add`, `neg`, `sub`, `smul`, `sum`, `ite`), that the concrete
singularity functions of `IETFree.Presentation` are integer affine (`isIntAffine_cutAffine`,
`isIntAffine_imageLeftAffine`, …), and it extracts the data (`intAffineData`) that the Diophantine
transfer consumes.

The sign-constancy and truncation lemmas that used to close the file — `lt_or_gt_of_ne_of_convex`,
`lt_or_gt_of_ne_of_convex_intAffine`, `Convex.exists_isIntAffine_max`, `…_min`, `…_posPart`,
`…_truncatedLength`, together with the two lemmas only they used
(`lt_or_gt_of_ne_of_isPreconnected`, `IsIntAffine.continuous`) — are gone.  They wanted `Convex ℝ O`
for a region `O`, which no `GoodRegion` supplies; the assembly builds its integer-affine families
directly, and the live truncation lemma is `GoodRegion.exists_isIntAffine_truncatedLengths` in
`IETFree.BlockDiophantine`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
/-! ### Integer-affine functions of the free parameters -/

section IntAffine

variable {d e : ℕ}

/-- **An integer-affine function of the free parameters**: an integer constant plus an integer
combination of the coordinates of `q`. -/
def IsIntAffine (f : ParamAffine d e) : Prop :=
  ∃ (c : ℤ) (A : Fin (d - 1) → ℤ) (B : Fin (e - 1) → ℤ),
    ∀ q : PReal d e, f q = (c : ℝ) + ∑ i, (A i : ℝ) * q.1 i + ∑ j, (B j : ℝ) * q.2 j

theorem isIntAffine_zero : IsIntAffine (0 : ParamAffine d e) :=
  ⟨0, 0, 0, by intro q; simp⟩

theorem isIntAffine_const (c : ℤ) :
    IsIntAffine (AffineMap.const ℝ (PReal d e) (c : ℝ)) :=
  ⟨c, 0, 0, by intro q; simp⟩

theorem isIntAffine_one : IsIntAffine (AffineMap.const ℝ (PReal d e) 1) := by
  simpa using isIntAffine_const (d := d) (e := e) 1

theorem isIntAffine_leftCoordAffine (j : Fin (d - 1)) :
    IsIntAffine (leftCoordAffine (e := e) j) := by
  refine ⟨0, Pi.single j 1, 0, fun q => ?_⟩
  rw [leftCoordAffine_apply]
  have h0 : (∑ i, ((Pi.single j (1 : ℤ) : Fin (d - 1) → ℤ) i : ℝ) * q.1 i) = q.1 j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  simp only [Int.cast_zero, zero_add, h0]
  have hzero : (∑ j' : Fin (e - 1), ((0 : Fin (e - 1) → ℤ) j' : ℝ) * q.2 j') = 0 := by simp
  rw [hzero, add_zero]

theorem isIntAffine_rightCoordAffine (j : Fin (e - 1)) :
    IsIntAffine (rightCoordAffine (d := d) j) := by
  refine ⟨0, 0, Pi.single j 1, fun q => ?_⟩
  rw [rightCoordAffine_apply]
  have h0 : (∑ i, ((0 : Fin (d - 1) → ℤ) i : ℝ) * q.1 i) = 0 := by simp
  have h1 : (∑ j' : Fin (e - 1), ((Pi.single j (1 : ℤ) : Fin (e - 1) → ℤ) j' : ℝ) * q.2 j')
      = q.2 j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [h0, h1]
  ring

theorem IsIntAffine.add {f g : ParamAffine d e} (hf : IsIntAffine f) (hg : IsIntAffine g) :
    IsIntAffine (f + g) := by
  obtain ⟨c1, A1, B1, h1⟩ := hf
  obtain ⟨c2, A2, B2, h2⟩ := hg
  refine ⟨c1 + c2, A1 + A2, B1 + B2, fun q => ?_⟩
  have hfg : (f + g) q = f q + g q := rfl
  rw [hfg, h1 q, h2 q]
  have e1 : (∑ i, ((A1 + A2) i : ℝ) * q.1 i)
      = (∑ i, (A1 i : ℝ) * q.1 i) + ∑ i, (A2 i : ℝ) * q.1 i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by
      simp only [Pi.add_apply]
      push_cast
      ring)
  have e2 : (∑ j, ((B1 + B2) j : ℝ) * q.2 j)
      = (∑ j, (B1 j : ℝ) * q.2 j) + ∑ j, (B2 j : ℝ) * q.2 j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by
      simp only [Pi.add_apply]
      push_cast
      ring)
  rw [e1, e2]
  push_cast
  ring

theorem IsIntAffine.neg {f : ParamAffine d e} (hf : IsIntAffine f) : IsIntAffine (-f) := by
  obtain ⟨c, A, B, h⟩ := hf
  refine ⟨-c, -A, -B, fun q => ?_⟩
  have hneg : (-f) q = -(f q) := rfl
  rw [hneg, h q]
  have e1 : (∑ i, ((-A) i : ℝ) * q.1 i) = -(∑ i, (A i : ℝ) * q.1 i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by
      simp only [Pi.neg_apply]
      push_cast
      ring)
  have e2 : (∑ j, ((-B) j : ℝ) * q.2 j) = -(∑ j, (B j : ℝ) * q.2 j) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => by
      simp only [Pi.neg_apply]
      push_cast
      ring)
  rw [e1, e2]
  push_cast
  ring

theorem IsIntAffine.sub {f g : ParamAffine d e} (hf : IsIntAffine f) (hg : IsIntAffine g) :
    IsIntAffine (f - g) := by
  have h : f - g = f + (-g) := by
    ext q
    have h1 : (f - g) q = f q - g q := rfl
    have h2 : (f + (-g)) q = f q + (-g) q := rfl
    have h3 : (-g) q = -(g q) := rfl
    rw [h1, h2, h3]
    ring
  rw [h]
  exact hf.add hg.neg

end IntAffine

section Closure

variable {d e : ℕ}

theorem IsIntAffine.smul (k : ℤ) {f : ParamAffine d e} (hf : IsIntAffine f) :
    IsIntAffine ((k : ℝ) • f) := by
  obtain ⟨c, A, B, h⟩ := hf
  refine ⟨k * c, fun i => k * A i, fun j => k * B j, fun q => ?_⟩
  have hq : ((k : ℝ) • f) q = (k : ℝ) * f q := rfl
  rw [hq, h q]
  have e1 : (∑ i, ((k * A i : ℤ) : ℝ) * q.1 i)
      = (k : ℝ) * ∑ i, (A i : ℝ) * q.1 i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by push_cast; ring)
  have e2 : (∑ j, ((k * B j : ℤ) : ℝ) * q.2 j)
      = (k : ℝ) * ∑ j, (B j : ℝ) * q.2 j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by push_cast; ring)
  rw [e1, e2]
  push_cast
  ring

theorem IsIntAffine.sum {ι : Type*} (s : Finset ι) {F : ι → ParamAffine d e}
    (h : ∀ i ∈ s, IsIntAffine (F i)) : IsIntAffine (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isIntAffine_zero (d := d) (e := e)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Integer-affine maps are closed under `if` with a decidable (constant) condition. -/
theorem IsIntAffine.ite {f g : ParamAffine d e} (P : Prop) [Decidable P]
    (hf : IsIntAffine f) (hg : IsIntAffine g) :
    IsIntAffine (if P then f else g) := by
  by_cases hP : P
  · rw [if_pos hP]; exact hf
  · rw [if_neg hP]; exact hg

end Closure

section Concrete

variable {d e : ℕ}

theorem isIntAffine_imageLenAffine [NeZero d] (j : Fin d) :
    IsIntAffine (imageLenAffine (e := e) j) := by
  unfold imageLenAffine
  split_ifs with h
  · exact isIntAffine_one.sub (IsIntAffine.sum _ (fun m _ => isIntAffine_leftCoordAffine m))
  · exact isIntAffine_leftCoordAffine _

theorem isIntAffine_imageLeftAffine [NeZero d] (π : Equiv.Perm (Fin d)) (k : Fin d) :
    IsIntAffine (imageLeftAffine (e := e) π k) := by
  unfold imageLeftAffine
  refine IsIntAffine.sum _ (fun j _ => ?_)
  by_cases hj : π j < π k
  · rw [if_pos hj]
    exact isIntAffine_imageLenAffine j
  · rw [if_neg hj]
    exact isIntAffine_zero

theorem isIntAffine_cutAffine (i : Fin d) : IsIntAffine (cutAffine (e := e) i) := by
  unfold cutAffine
  refine IsIntAffine.sum _ (fun j _ => ?_)
  by_cases hj : j.val < i.val
  · rw [if_pos hj]; exact isIntAffine_leftCoordAffine j
  · rw [if_neg hj]; exact isIntAffine_zero

theorem isIntAffine_cutAffineRight (j : Fin e) : IsIntAffine (cutAffineRight (d := d) j) := by
  unfold cutAffineRight
  refine IsIntAffine.sum _ (fun m _ => ?_)
  by_cases hm : m.val < j.val
  · rw [if_pos hm]; exact isIntAffine_rightCoordAffine m
  · rw [if_neg hm]; exact isIntAffine_zero

theorem isIntAffine_preimageCutAffine [NeZero d] (π : Equiv.Perm (Fin d)) (j : Fin e)
    (k : Fin d) :
    IsIntAffine (preimageCutAffine (e := e) π j k) := by
  unfold preimageCutAffine
  exact ((isIntAffine_cutAffineRight j).sub (isIntAffine_imageLeftAffine π k)).add
    (isIntAffine_cutAffine k)

end Concrete

section Extract

variable {d e : ℕ}

/-- The constant term of an integer-affine function. -/
noncomputable def IsIntAffine.const {f : ParamAffine d e} (hf : IsIntAffine f) : ℤ :=
  Classical.choose hf

/-- The coefficients of the `q.1` coordinates. -/
noncomputable def IsIntAffine.coeffA {f : ParamAffine d e} (hf : IsIntAffine f) : Fin (d - 1) → ℤ :=
  Classical.choose (Classical.choose_spec hf)

/-- The coefficients of the `q.2` coordinates. -/
noncomputable def IsIntAffine.coeffB {f : ParamAffine d e} (hf : IsIntAffine f) : Fin (e - 1) → ℤ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec hf))

theorem IsIntAffine.coeff_spec {f : ParamAffine d e} (hf : IsIntAffine f) (q : PReal d e) :
    f q = (hf.const : ℝ) + ∑ i, (hf.coeffA i : ℝ) * q.1 i
      + ∑ j, (hf.coeffB j : ℝ) * q.2 j :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hf)) q

/-- **A uniform bound for a finite family of integer-affine functions**: the largest absolute value
of their coefficients, packaged with the matrices themselves. -/
noncomputable def intAffineData {ι : Type*} [Fintype ι] (F : ι → ParamAffine d e)
    (h : ∀ i, IsIntAffine (F i)) :
    { K : ℕ // 0 < K ∧ ∃ (c : ι → ℤ) (A : ι → Fin (d - 1) → ℤ) (B : ι → Fin (e - 1) → ℤ),
      (∀ i k, (A i k).natAbs ≤ K) ∧ (∀ i l, (B i l).natAbs ≤ K) ∧
        ∀ (i : ι) (q : PReal d e), F i q = (c i : ℝ) + ∑ k, (A i k : ℝ) * q.1 k
          + ∑ l, (B i l : ℝ) * q.2 l } := by
  classical
  refine ⟨(Finset.univ.sup (fun i => max (Finset.univ.sup (fun k => ((h i).coeffA k).natAbs))
    (Finset.univ.sup (fun l => ((h i).coeffB l).natAbs)))) + 1, ?_, ?_⟩
  · omega
  · refine ⟨fun i => (h i).const, fun i => (h i).coeffA, fun i => (h i).coeffB, ?_, ?_, ?_⟩
    · intro i k
      have h1 : ((h i).coeffA k).natAbs
          ≤ max (Finset.univ.sup (fun k => ((h i).coeffA k).natAbs))
            (Finset.univ.sup (fun l => ((h i).coeffB l).natAbs)) :=
        le_trans (Finset.le_sup (f := fun k => ((h i).coeffA k).natAbs) (Finset.mem_univ k))
          (le_max_left _ _)
      have h2 : max (Finset.univ.sup (fun k => ((h i).coeffA k).natAbs))
          (Finset.univ.sup (fun l => ((h i).coeffB l).natAbs))
          ≤ Finset.univ.sup (fun i => max (Finset.univ.sup (fun k => ((h i).coeffA k).natAbs))
            (Finset.univ.sup (fun l => ((h i).coeffB l).natAbs))) :=
        Finset.le_sup (f := fun i => max (Finset.univ.sup (fun k => ((h i).coeffA k).natAbs))
          (Finset.univ.sup (fun l => ((h i).coeffB l).natAbs))) (Finset.mem_univ i)
      exact le_trans (le_trans h1 h2) (Nat.le_succ _)
    · intro i l
      have h1 : ((h i).coeffB l).natAbs
          ≤ max (Finset.univ.sup (fun k => ((h i).coeffA k).natAbs))
            (Finset.univ.sup (fun l => ((h i).coeffB l).natAbs)) :=
        le_trans (Finset.le_sup (f := fun l => ((h i).coeffB l).natAbs) (Finset.mem_univ l))
          (le_max_right _ _)
      have h2 : max (Finset.univ.sup (fun k => ((h i).coeffA k).natAbs))
          (Finset.univ.sup (fun l => ((h i).coeffB l).natAbs))
          ≤ Finset.univ.sup (fun i => max (Finset.univ.sup (fun k => ((h i).coeffA k).natAbs))
            (Finset.univ.sup (fun l => ((h i).coeffB l).natAbs))) :=
        Finset.le_sup (f := fun i => max (Finset.univ.sup (fun k => ((h i).coeffA k).natAbs))
          (Finset.univ.sup (fun l => ((h i).coeffB l).natAbs))) (Finset.mem_univ i)
      exact le_trans (le_trans h1 h2) (Nat.le_succ _)
    · intro i q
      exact (h i).coeff_spec q

end Extract

/-! ### The truncation pattern is constant on a convex region

The block lengths of `g` inside a block are truncated cell lengths `max 0 (min V G - max U F)`.
On a convex region on which the strict inequalities of the truncation hold, such a length agrees
with a *single* integer-affine function: the pattern cannot change without the two lines meeting,
and a meeting point would be an interior zero of a continuous function (IVT).  This is what makes
the `μ'` of Lemma 3.4 integer combinations of the parameters, as the paper's
"integer combination" step needs. -/

section SignConstancy

variable {d e : ℕ}

end SignConstancy

section Truncation

variable {d e : ℕ}

end Truncation
