/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.UniqueErgodicity.Germ.Basic

/-!
# The iterate bridge for the left germs of the germ map

The germ map `T̃` of an interval exchange sends the left germ of a split point
`x` to the left germ of the left limit `L x` (the landed `Germ/Basic.lean` only records the dual
statement for right germs, `germMap_rightGerm`).  We prove this left-germ equivariance, deduce
from it the iterate bridge `T̃^[n] (leftGerm c) = leftGerm (L^[n] c)` together with its projection
form `proj (T̃^[n] (leftGerm c)) = L^[n] c`, and the dual projection form for right germs.

Everything is proved first for an arbitrary exchange `T` with cut set `s` on `[0, 1)`, as in
`Germ/Basic.lean`, and then specialised to `T = mkIETEquiv lam π 0` and `s = mkIETCuts lam 0 1`.
-/

@[expose] public section

open Set Function Filter Topology
open scoped BigOperators NNReal

/-! ## Invariance of the interval and of the split set along the iterates -/

namespace IntervalExchange.UniqueErgodicity

section Iterates

variable {T : ℝ ≃ ℝ} {s : Finset ℝ}

/-- The iterates of the left limit stay in `[0,1]`. -/
theorem leftLimit_iterate_mem_Icc (hT : IsCutSet (⇑T) 0 1 s) {c : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (i : ℕ) : (leftLimit hT)^[i] c ∈ Set.Icc (0 : ℝ) 1 := by
  induction i with
  | zero => simpa using hc
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact leftLimit_mem hT ih

/-- **Lemma 1.7 (iii), iterated**: the iterates of the left limit of a point of the split set stay
in the split set. -/
theorem leftLimit_iterate_mem_splitSet (hT : IsCutSet (⇑T) 0 1 s) {c : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (hcD : c ∈ splitSet T s) (i : ℕ) :
    (leftLimit hT)^[i] c ∈ splitSet T s := by
  induction i with
  | zero => simpa using hcD
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact leftLimit_mem_splitSet hT (leftLimit_iterate_mem_Icc hT hc i) ih

end Iterates

/-! ## The left germs of the germ map -/

section LeftGerm

variable {T : ℝ ≃ ℝ} {s : Finset ℝ}

/-- **Lemma 3.5 for left germs**: the germ map sends the left germ of a split point `x` to the left
germ of the left limit `L x`.  The hypothesis `x ∈ D` is what makes the statement true: it forces
`side (leftGerm x) = false`, so the first coordinate is `L x` and the `Bool` coordinates of the two
points are `d ↦ decide (L x > d)` and `d ↦ decide (d < L x)`. -/
theorem germMapOf_leftGerm (hT : IsCutSet (⇑T) 0 1 s) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hxD : x ∈ splitSet T s) :
    germMapOf hT (SplitI.leftGerm (D := splitSet T s) x hx) =
      SplitI.leftGerm (D := splitSet T s) (leftLimit hT x) (leftLimit_mem hT hx) := by
  set z := SplitI.leftGerm (D := splitSet T s) x hx with hz
  have hzside : SplitI.side z = false := by
    rw [hz]
    exact SplitI.side_leftGerm hx hxD
  have hzproj : SplitI.proj z = x := by
    rw [hz]
    exact SplitI.proj_leftGerm x hx
  refine SplitI.ext ?_ ?_
  · rw [proj_germMapOf, germProjOf_of_side_false hT hzside, hzproj, SplitI.proj_leftGerm]
  · funext d
    have hcoord : (germMapOf hT z).1.2 d = decide ((d : ℝ) < leftLimit hT x) := by
      rw [coord_germMapOf]
      rw [germCoordOf_def]
      rw [germProjOf_of_side_false hT hzside, hzproj, hzside]
      refine Bool.decide_congr ?_
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact h
        · exact absurd h (by simp)
      · intro h
        exact Or.inl h
    rw [hcoord, SplitI.coord_leftGerm]

/-- **The iterate bridge**: the `i`-th iterate of the germ map at the left germ of `c` is the left
germ of the `i`-th iterate of the left limit at `c`. -/
theorem iterate_germMapOf_leftGerm (hT : IsCutSet (⇑T) 0 1 s) {c : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (hcD : c ∈ splitSet T s) (i : ℕ) :
    (germMapOf hT)^[i] (SplitI.leftGerm (D := splitSet T s) c hc) =
      SplitI.leftGerm (D := splitSet T s) ((leftLimit hT)^[i] c)
        (leftLimit_iterate_mem_Icc hT hc i) := by
  induction i with
  | zero =>
      exact leftGerm_congr (D := splitSet T s) hc (leftLimit_iterate_mem_Icc hT hc 0) rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply' (f := germMapOf hT), ih,
        germMapOf_leftGerm hT (leftLimit_iterate_mem_Icc hT hc i)
          (leftLimit_iterate_mem_splitSet hT hc hcD i)]
      exact leftGerm_congr (D := splitSet T s) _ _
        (Function.iterate_succ_apply' (f := leftLimit hT) i c).symm

/-- **The iterate bridge, projection form**: the projection of the `i`-th iterate of the germ map at
the left germ of `c` is the `i`-th iterate of the left limit at `c`. -/
theorem proj_iterate_germMapOf_leftGerm (hT : IsCutSet (⇑T) 0 1 s) {c : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (hcD : c ∈ splitSet T s) (i : ℕ) :
    SplitI.proj ((germMapOf hT)^[i] (SplitI.leftGerm (D := splitSet T s) c hc)) =
      (leftLimit hT)^[i] c := by
  rw [iterate_germMapOf_leftGerm hT hc hcD i]
  exact SplitI.proj_leftGerm _ _

end LeftGerm

section RightGerm

variable {T : ℝ ≃ ℝ} {s : Finset ℝ}

end RightGerm

/-! ## The orbit of a left germ is infinite under (H2) -/

section Orbit

variable {T : ℝ ≃ ℝ} {s : Finset ℝ}

/-- The iterates of the left limit of a point of `(0,1]` are positive: `leftLimit` is injective
on `[0,1]` and fixes `0`, so an iterate can only vanish if the starting point does. -/
theorem leftLimit_iterate_pos (hT : IsCutSet (⇑T) 0 1 s) {c : ℝ}
    (hc : c ∈ Set.Ioc (0 : ℝ) 1) (i : ℕ) : 0 < (leftLimit hT)^[i] c := by
  induction i with
  | zero => simpa using hc.1
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      have hmem : (leftLimit hT)^[i] c ∈ Set.Icc (0 : ℝ) 1 :=
        leftLimit_iterate_mem_Icc hT ⟨hc.1.le, hc.2⟩ i
      have hne : leftLimit hT ((leftLimit hT)^[i] c) ≠ 0 := by
        intro h0
        have hzero : leftLimit hT (0 : ℝ) = 0 := leftLimit_of_le hT le_rfl
        have heq : leftLimit hT ((leftLimit hT)^[i] c) = leftLimit hT 0 := by
          rw [h0, hzero]
        have hy0 : (leftLimit hT)^[i] c = 0 :=
          leftLimit_injOn hT T.injective hmem ⟨le_rfl, zero_le_one⟩ heq
        rw [hy0] at ih
        exact absurd ih (lt_irrefl 0)
      exact lt_of_le_of_ne (leftLimit_mem hT hmem).1 (Ne.symm hne)

/-- **(H2) makes the orbit of a left germ infinite** (Lemma 4.5 (i), in the form needed by
`measure_singleton_eq_zero_of_injOn_orbit`): if the left limit has no periodic point in `(0,1]`,
then the iterates of `T̃` at the left germ of `c ∈ (0,1]` are pairwise distinct. -/
theorem germMapOf_orbit_infinite (hT : IsCutSet (⇑T) 0 1 s) (hH2 : NoPeriodicLeftLimit hT)
    {c : ℝ} (hc : c ∈ Set.Ioc (0 : ℝ) 1) (hcD : c ∈ splitSet T s) (i j : ℕ)
    (hij : (germMapOf hT)^[i] (SplitI.leftGerm (D := splitSet T s) c ⟨hc.1.le, hc.2⟩) =
        (germMapOf hT)^[j] (SplitI.leftGerm (D := splitSet T s) c ⟨hc.1.le, hc.2⟩)) :
    i = j := by
  have hIcc : c ∈ Set.Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
  have hL : (leftLimit hT)^[i] c = (leftLimit hT)^[j] c := by
    have h1 := congrArg SplitI.proj hij
    rwa [proj_iterate_germMapOf_leftGerm hT hIcc hcD i,
      proj_iterate_germMapOf_leftGerm hT hIcc hcD j] at h1
  have key (p q : ℕ) (hpq : p ≤ q) (hpqeq : (leftLimit hT)^[p] c = (leftLimit hT)^[q]
      c) : p = q := by
    rcases eq_or_lt_of_le hpq with heq | hlt
    · exact heq
    · exfalso
      obtain ⟨k, hkpos, hkq⟩ : ∃ k : ℕ, 0 < k ∧ k + p = q :=
        ⟨q - p, by omega, by omega⟩
      have hy : (leftLimit hT)^[p] c ∈ Set.Ioc (0 : ℝ) 1 :=
        ⟨leftLimit_iterate_pos hT hc p, (leftLimit_iterate_mem_Icc hT hIcc p).2⟩
      have hper : (leftLimit hT)^[k] ((leftLimit hT)^[p] c) = (leftLimit hT)^[p] c := by
        have h1 : (leftLimit hT)^[k] ((leftLimit hT)^[p] c) = (leftLimit hT)^[k + p] c :=
          (Function.iterate_add_apply (f := leftLimit hT) k p c).symm
        rw [h1, hkq]
        exact hpqeq.symm
      exact hH2 k hkpos _ hy hper
  rcases le_total i j with hle | hle
  · exact key i j hle hL
  · exact (key j i hle hL.symm).symm

end Orbit

section Concrete

variable {n : ℕ} [NeZero n]

end Concrete

end IntervalExchange.UniqueErgodicity

end
