/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.FirstReturn

/-!
# The tower formula at level one, in matrix form

Builds on `IETFree/RauzyVeech/FirstReturn.lean` (the Rauzy first return map, the level-one tower
decomposition and the level-one tower formula `tower_formula_one_step`) and proves the same
formula in **matrix form** (`tower_formula_one_step_mult`):

`μ (cell i) = ∑ j, (multOne π i j : ℝ≥0∞) * μ (cell j of the return map)`,

the multiplicity matrix `multOne` being the Rauzy–Veech matrix of the step, i.e. the identity
plus the floor over `topCell π` inside `lastPos n` (`multOne_cast_mul`).  Also here:
`image_Ico_totalLength`, the exchange maps `[0, Λ)` onto itself.

This is the `k = 1` case of the level-`n` formula: its iterates are set up in
`IETFree/RauzyVeech/RenormData.lean`, and the formula for an arbitrary word is
`tower_formula_level_pathQ_any` of `IETFree/RauzyVeech/TrueStep.lean`. -/

@[expose] public section

open MeasureTheory Finset
open scoped BigOperators ENNReal NNReal

namespace IntervalExchange.RauzyVeech

noncomputable section

variable {n : ℕ} [NeZero n]
variable {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}

/-! ## 1. The level-one formula in matrix form -/

/-- A purely propositional identity: an elementary multiplicity times a weight. -/
theorem ite_mul_eq_add_of_iff {P Q R S T : Prop} [Decidable P] [Decidable Q] [Decidable R]
    [Decidable S] [Decidable T] (h1 : P ↔ R) (h2 : Q ↔ (S ∧ T)) (h3 : ¬ (P ∧ Q))
    (f : ℝ≥0∞) :
    ((if P then (1 : ℝ≥0∞) else if Q then 1 else 0)) * f
      = (if R then f else 0) + (if S then (if T then f else 0) else 0) := by
  by_cases hP : P <;> by_cases hS : S <;> by_cases hT : T <;> simp_all

/-- The multiplicity of the level-one tower, as a `ℝ≥0∞` weight: the identity plus one
elementary term. -/
theorem multOne_cast_mul {f : Fin n → ℝ≥0∞} (hne : topCell π ≠ (lastPos n)) (i j : Fin n) :
    (multOne π i j : ℝ≥0∞) * f j
      = (if i = j then f j else 0)
        + (if i = (lastPos n) then (if j = topCell π then f j else 0) else 0) := by
  have hQ : (j = topCell π ∧ i = (lastPos n)) ↔ ((i = (lastPos n)) ∧ (j = topCell π)) :=
    ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have h3 : ¬ ((j = i) ∧ (j = topCell π ∧ i = (lastPos n))) := by
    rintro ⟨h1, h2, h3⟩
    exact hne (h2.symm.trans (h1.trans h3))
  have key := ite_mul_eq_add_of_iff (P := j = i) (Q := j = topCell π ∧ i = (lastPos n))
    (R := i = j) (S := i = (lastPos n)) (T := j = topCell π) eq_comm hQ h3 (f j)
  rw [multOne]
  push_cast
  simpa using key

/-- **Level-one tower formula, matrix form**: for a `T`-invariant measure `μ`,
`μ (cell i) = ∑ j, (rvMat false) i j * μ (cell j of the first return map)`. -/
theorem tower_formula_one_step_mult (hlt : lam (topCell π) < lam (lastPos n)) (μ : Measure ℝ)
    (hμ : μ.map (mkIETFun lam π 0) = μ) (i : Fin n) :
    μ (Set.Ico (leftEnd lam i) (upperEnd lam i))
      = ∑ j, (multOne π i j : ℝ≥0∞) * μ (cellHat π lam j) := by
  rw [tower_formula_one_step hlt μ hμ i]
  have hsum : (∑ j, (multOne π i j : ℝ≥0∞) * μ (cellHat π lam j))
      = ∑ j, ((if i = j then μ (cellHat π lam j) else 0)
          + (if i = (lastPos n) then (if j = topCell π then μ (cellHat π lam j) else 0)
            else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    exact multOne_cast_mul (f := fun j => μ (cellHat π lam j)) (topCell_ne_lastPos hlt) i j
  rw [hsum, Finset.sum_add_distrib,
    Finset.sum_ite_eq Finset.univ i (fun j => μ (cellHat π lam j))]
  simp only [Finset.mem_univ, ite_true]
  by_cases hi : i = (lastPos n)
  · simp only [hi, ite_true]
    rw [Finset.sum_ite_eq' Finset.univ (topCell π) (fun j => μ (cellHat π lam j))]
    simp
  · rw [ite_eq_right hi]
    simp [hi]

/-! ## 2. Auxiliary facts towards induced invariance  The following facts are independently useful
and are used in the proof of induced invariance: `T` maps `[0, Λ)` onto itself, and the points of
the cut interval whose cell is the rightmost-image cell are exactly the points that do not return
after one step. -/

/-- The exchange maps `[0, Λ)` onto itself. -/
theorem image_Ico_totalLength (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    mkIETFun lam π 0 '' Set.Ico 0 (totalLength lam) = Set.Ico 0 (totalLength lam) := by
  have hI : IsIET 0 (0 + ∑ i, (lam i : ℝ)) (mkIETFun lam π 0) :=
    isIET_mkIETFun lam π 0 le_rfl
  have hI' : IsIET 0 (0 + ∑ i, (imageLengths π lam i : ℝ))
      (mkIETFun (imageLengths π lam) π.symm 0) :=
    isIET_mkIETFun (imageLengths π lam) π.symm 0 le_rfl
  have htot : ∑ i, (imageLengths π lam i : ℝ) = totalLength lam := sum_imageLengths π lam
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := hI.mapsTo (x := y) (by rw [zero_add]; exact hy)
    rwa [zero_add, ← totalLength] at h
  · intro hz
    have hx : z ∈ Set.Ico 0 (0 + ∑ i, (imageLengths π lam i : ℝ)) := by
      rw [zero_add, htot]; exact hz
    have hy : ⇑(mkIETEquiv lam π 0).symm z ∈ Set.Ico 0 (totalLength lam) := by
      have h := hI'.mapsTo (x := z) hx
      rwa [zero_add, htot] at h
    refine ⟨⇑(mkIETEquiv lam π 0).symm z, hy, ?_⟩
    rw [← coe_mkIETEquiv, Equiv.apply_symm_apply]

end

end IntervalExchange.RauzyVeech

end
