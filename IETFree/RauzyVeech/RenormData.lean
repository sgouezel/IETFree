/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.Path
public import IETFree.RauzyVeech.Tower.Level

/-!
# Iterated permutations, path matrices over `ℕ`, and renormalised length vectors

The infrastructure behind the level-`n` tower formula, first in `Fin n` coordinates and then in the
`α`-indexed coordinates of `IETDatum₂`:

* §1 injectivity of the exchange and disjointness of the cells of an arrangement
  (`injective_mkIETFun`, `disjoint_cell`, `pairwiseDisjoint_cellHat`);
* §2 **induced invariance** (`restrict_cut_invariant`): for an invariant `μ`, the restriction
  `μ.restrict [0, cut)` is invariant under the first-return exchange — the analytic input of the
  tower formula;
* §3 the bridge to `IETDatum₂ α n`: `Path.Q` over `ℕ` (`Qnat`, `Qnat_cons`, `Qnat_cast`), the step
  in `Fin n` coordinates (`rvMat_ofPerm_false`, `rvMatNat_ofPerm_false`), the identification of the
  two permutations (`perm_rvStep_false`), the renormalised length vectors `hatLam`, `lamAfter` and
  the cells `cellAt`;
* §4 the renormalised length vectors in `α` coordinates, and the target statement.

Only the type-`false` case is treated here (`IETFree/RauzyVeech/FirstReturn.lean` proves the
first-return theorem only in that case); the level-`n` formula itself, for an arbitrary word, is
`tower_formula_level_pathQ_any` of `IETFree/RauzyVeech/TrueStep.lean`. -/

open MeasureTheory Finset IntervalExchange.IETDatum₂
open scoped BigOperators ENNReal NNReal
open IntervalExchange.RauzyVeech

@[expose] public section

namespace IntervalExchange.RauzyVeech

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## 1. Injectivity and disjointness -/

theorem injective_mkIETFun (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    Function.Injective (mkIETFun lam π 0) := by
  rw [← coe_mkIETEquiv lam π 0]
  exact (mkIETEquiv lam π 0).injective

omit [NeZero n] in
/-- Two distinct cells of an arrangement are disjoint. -/
theorem disjoint_cell (lam : Fin n → ℝ≥0) {i j : Fin n} (h : i ≠ j) :
    Disjoint (Set.Ico (leftEnd lam i) (upperEnd lam i))
      (Set.Ico (leftEnd lam j) (upperEnd lam j)) := by
  refine Set.disjoint_left.mpr fun x hx hy => ?_
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact absurd (lt_of_lt_of_le hx.2 (upperEnd_le_leftEnd _ hlt)) (not_lt.mpr hy.1)
  · exact absurd (lt_of_lt_of_le hy.2 (upperEnd_le_leftEnd _ hlt)) (not_lt.mpr hx.1)

/-- The cells of the first-return exchange are pairwise disjoint. -/
theorem pairwiseDisjoint_cellHat (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n))) (cellHat π lam) := by
  intro β _ β' _ hne
  exact disjoint_cell (lamHat π lam) hne

/-- Disjointness is preserved by an injective image. -/
theorem pairwiseDisjoint_image {ι : Type*} {f : ℝ → ℝ} (hf : Function.Injective f)
    {s : Finset ι} {g : ι → Set ℝ} (h : Set.PairwiseDisjoint (↑s) g) :
    Set.PairwiseDisjoint (↑s) fun i => f '' g i := by
  intro i hi j hj hij
  exact (h hi hj hij).image hf.injOn (Set.subset_univ _) (Set.subset_univ _)

/-! ## 2. Induced invariance: the restriction to the cut interval is invariant under the
first-return exchange -/

variable {π : Equiv.Perm (Fin n)} {lam : Fin n → ℝ≥0}

/-- The image of a measurable set under an exchange is measurable (the exchange is a measurable
bijection with measurable inverse, so the image is a preimage under the inverse). -/
theorem measurableSet_image_mkIETFun (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) {A : Set ℝ}
    (hA : MeasurableSet A) : MeasurableSet (mkIETFun lam π 0 '' A) := by
  have himg : mkIETFun lam π 0 '' A = ⇑(mkIETEquiv lam π 0).symm ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [Set.mem_preimage, ← coe_mkIETEquiv lam π 0, Equiv.symm_apply_apply]
      exact ha
    · intro hx
      exact ⟨⇑(mkIETEquiv lam π 0).symm x, hx, Equiv.apply_symm_apply (mkIETEquiv lam π 0) x⟩
  rw [himg]
  exact hA.preimage (measurable_mkIETEquiv_symm π lam)

/-- The exchange with the renormalised data maps the whole interval onto itself, so the
first-return exchange maps the cut interval onto itself. -/
theorem image_cut_self (hlt : lam (topCell π) < lam (lastPos n)) :
    mkIETFun (lamHat π lam) (piHat π) 0 '' Set.Ico 0 (cut π lam) = Set.Ico 0 (cut π lam) := by
  have h := image_Ico_totalLength (piHat π) (lamHat π lam)
  rw [totalLength, cut_eq_sum_lamHat hlt] at h
  exact h

/-- **Induced invariance.**  If `μ` is invariant under the exchange `T = mkIETFun lam π 0` and `lam
(topCell π) < lam lastPos n`, then the restriction of `μ` to the Rauzy subinterval `[0, cut)` is
invariant under the first-return exchange `T̂ = mkIETFun (lamHat π lam) (piHat π) 0`.  The proof
counts:
for `A ⊆ [0, cut)`, split `A` over the cells `cellHat β` of `T̂`; on `cellHat β` the return map is
`T^[returnB π β]`, and the floors `T^[j] '' cellHat β` all have the mass of `cellHat β` because `μ`
is `T`-invariant.  Hence `μ (T̂ '' A) = μ A`, and since `T̂` maps `[0, cut)` onto itself this is
the invariance. -/
theorem restrict_cut_invariant (hlt : lam (topCell π) < lam (lastPos n)) (μ : Measure ℝ)
    (hμ : μ.map (mkIETFun lam π 0) = μ) :
    (μ.restrict (Set.Ico 0 (cut π lam))).map (mkIETFun (lamHat π lam) (piHat π) 0)
      = μ.restrict (Set.Ico 0 (cut π lam)) := by
  -- the first-return exchange is measurable and maps the base `Ico 0 (cut π lam)` to itself
  have hmeasTH : Measurable (mkIETFun (lamHat π lam) (piHat π) 0) := measurable_mkIETFun _ _
  have hIm : mkIETFun (lamHat π lam) (piHat π) 0 '' Set.Ico 0 (cut π lam)
      = Set.Ico 0 (cut π lam) := image_cut_self hlt
  have hcell (β : Fin n) : MeasurableSet (cellHat π lam β) := measurableSet_cellHat π lam β
  -- the key counting identity
  have hmain (A : Set ℝ) (hAI : A ⊆ Set.Ico 0 (cut π lam)) (hA : MeasurableSet A) :
    μ (mkIETFun (lamHat π lam) (piHat π) 0 '' A) = μ A := by
    -- split `A` over the cells: there the exchange is an iterate of `T`, so `μ` is preserved
    have hcover : A = ⋃ β, A ∩ cellHat π lam β := by
      ext x
      constructor
      · intro hx
        have hxI : x ∈ ⋃ β : Fin n, cellHat π lam β := by
          rw [iUnion_cellHat hlt]
          exact hAI hx
        obtain ⟨β, hβ⟩ := Set.mem_iUnion.mp hxI
        exact Set.mem_iUnion.mpr ⟨β, hx, hβ⟩
      · intro hx
        obtain ⟨β, hβ⟩ := Set.mem_iUnion.mp hx
        exact hβ.1
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n)))
        (fun β => A ∩ cellHat π lam β) := by
      intro β _ β' _ hne
      exact (pairwiseDisjoint_cellHat π lam (Finset.mem_univ β) (Finset.mem_univ β')
        hne).mono Set.inter_subset_right Set.inter_subset_right
    have hmeasInt (β) (hβ : β ∈ (Finset.univ : Finset (Fin n))) :
        MeasurableSet (A ∩ cellHat π lam β) := hA.inter (hcell β)
    have hstep (β : Fin n) : μ (mkIETFun (lamHat π lam) (piHat π) 0 '' (A ∩ cellHat π lam β))
        = μ (A ∩ cellHat π lam β) := by
      have hfun (y) (hy0 : y ∈ A ∩ cellHat π lam β) :
          mkIETFun (lamHat π lam) (piHat π) 0 y = (mkIETFun lam π 0)^[returnB π β] y := by
        obtain ⟨-, hy⟩ := hy0
        have hyI : y ∈ Set.Ico 0 (cut π lam) := cellHat_subset_cut hlt β hy
        have h1 := firstReturn_eq hlt hyI
        have h2 := ret_eq_returnB hlt hy
        rw [h2] at h1
        exact h1.symm
      rw [Set.image_congr hfun]
      exact measure_image_iterate π lam μ hμ _ (hmeasInt β (Finset.mem_univ β)) _
    have hsum : μ A = ∑ β, μ (A ∩ cellHat π lam β) := by
      conv_lhs => rw [hcover]
      have hbi := measure_biUnion_finset (μ := μ) hdisj hmeasInt
      simpa using hbi
    -- the image splits the same way, so the two masses agree on `A`
    have hcov : mkIETFun (lamHat π lam) (piHat π) 0 '' A
        = ⋃ β, mkIETFun (lamHat π lam) (piHat π) 0 '' (A ∩ cellHat π lam β) := by
      conv_lhs => rw [hcover]
      rw [Set.image_iUnion]
    have hdisj' := pairwiseDisjoint_image (injective_mkIETFun (piHat π) (lamHat π lam)) hdisj
    have hmeas' (β) (hβ : β ∈ (Finset.univ : Finset (Fin n))) :
        MeasurableSet (mkIETFun (lamHat π lam) (piHat π) 0 '' (A ∩ cellHat π lam β)) :=
            measurableSet_image_mkIETFun _ _ (hmeasInt β (Finset.mem_univ β))
    have hsum' : μ (mkIETFun (lamHat π lam) (piHat π) 0 '' A)
        = ∑ β, μ (A ∩ cellHat π lam β) := by
      rw [hcov]
      have hbi := measure_biUnion_finset (μ := μ) hdisj' hmeas'
      rw [show μ (⋃ β, mkIETFun (lamHat π lam) (piHat π) 0 '' (A ∩ cellHat π lam β))
          = ∑ β, μ (mkIETFun (lamHat π lam) (piHat π) 0 '' (A ∩ cellHat π lam β)) from by
        simpa using hbi]
      exact Finset.sum_congr rfl fun β _ => hstep β
    rw [hsum', hsum]
  -- for a general `B`, apply that to the preimage of `B` in the base
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply hmeasTH hB, Measure.restrict_apply' measurableSet_Ico,
    Measure.restrict_apply' measurableSet_Ico]
  have hA : MeasurableSet (mkIETFun (lamHat π lam) (piHat π) 0 ⁻¹' B ∩ Set.Ico 0 (cut π lam)) :=
    (hB.preimage hmeasTH).inter measurableSet_Ico
  have hkey := hmain _ Set.inter_subset_right hA
  have himg1 : mkIETFun (lamHat π lam) (piHat π) 0
        '' (mkIETFun (lamHat π lam) (piHat π) 0 ⁻¹' B ∩ Set.Ico 0 (cut π lam))
      = B ∩ mkIETFun (lamHat π lam) (piHat π) 0 '' Set.Ico 0 (cut π lam) := by
    ext z
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨hy1, y, hy2, rfl⟩
    · rintro ⟨hzB, y, hyI, rfl⟩
      exact ⟨y, ⟨hzB, hyI⟩, rfl⟩
  rw [himg1, hIm] at hkey
  exact hkey.symm

end

end IntervalExchange.RauzyVeech

/-! ## 3. Bridge to `IETDatum₂ α n`: `Path.Q` over `ℕ`, renormalised lengths, cells -/

namespace IntervalExchange

namespace IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- The elementary Rauzy–Veech matrix `rvMat` as a matrix over `ℕ`. -/
def rvMatNat (P : IETDatum₂ α n) (ε : Bool) : Matrix α α ℕ := fun a b => (P.rvMat ε a b).toNat

theorem rvMatNat_cast (P : IETDatum₂ α n) (ε : Bool) (a b : α) :
    ((P.rvMatNat ε a b : ℕ) : ℤ) = P.rvMat ε a b :=
  Int.toNat_of_nonneg (P.rvMat_nonneg ε a b)

/-- **`Path.Q` read over `ℕ`** (all its entries are nonnegative). -/
noncomputable def Qnat (P : IETDatum₂ α n) : List Bool → Matrix α α ℕ
  | [] => 1
  | e :: es => P.rvMatNat e * Qnat (P.rvStep e) es

@[simp] theorem Qnat_nil (P : IETDatum₂ α n) : P.Qnat [] = 1 := (rfl)

theorem Qnat_cons (P : IETDatum₂ α n) (e : Bool) (es : List Bool) :
    P.Qnat (e :: es) = P.rvMatNat e * (P.rvStep e).Qnat es := (rfl)

/-- `Qnat` is `Path.Q` read over `ℕ`. -/
theorem Qnat_cast (P : IETDatum₂ α n) (γ : List Bool) (a b : α) :
    ((P.Qnat γ a b : ℕ) : ℤ) = IETDatum₂.Path.Q P γ a b := by
  induction γ generalizing P a b with
  | nil =>
    rw [Qnat_nil, IETDatum₂.Path.Q]
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  | cons e es ih =>
    rw [Qnat_cons, IETDatum₂.Path.Q, Matrix.mul_apply, Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ih (P.rvStep e) x b, P.rvMatNat_cast]

omit [DecidableEq α] in
/-- The bottom position of the letter last in the top order is the top cell. -/
theorem piBottom_last_true (P : IETDatum₂ α n) :
    P.piBottom (P.last true) = topCell P.perm := by
  rw [topCell, IETDatum₂.perm_symm_apply]
  rfl

omit [DecidableEq α] in
/-- The bottom position of the letter last in the bottom order is the bottom cell. -/
theorem piBottom_last_false (P : IETDatum₂ α n) : P.piBottom (P.last false) = (lastPos n) :=
  IETDatum₂.last_bottom P

omit [DecidableEq α] in
/-- The permutation of a IETDatum₂ step of type `false` is `piHat` of the permutation. -/
theorem perm_rvStep_false (P : IETDatum₂ α n) : (P.rvStep false).perm = piHat P.perm := by
  have hp : (IETDatum₂.pivot P false) = P.perm (lastPos n) := by
    rw [IETDatum₂.pivot_false, IETDatum₂.perm_apply (P := P),
      ← IETDatum₂.piBottom_last_false (P := P), Equiv.symm_apply_apply]
  rw [IETDatum₂.rvStep_perm_false, hp, ← Equiv.trans_assoc]
  rfl

/-- `rvMat` of a `IETDatum₂` step of type `false` is `rvMat` of the step of its permutation. -/
theorem rvMat_ofPerm_false (P : IETDatum₂ α n) (a b : α) :
    P.rvMat false a b = (ofPerm (P.perm)).rvMat false (P.piBottom a) (P.piBottom b) := by
  have e1 : (P.piBottom a = P.piBottom b) ↔ (a = b) := P.piBottom.injective.eq_iff
  have e2 : (P.piBottom a = (ofPerm (P.perm)).last false) ↔ (a = P.last false) := by
    rw [ofPerm_last_false (P.perm),
      ← IETDatum₂.piBottom_last_false P]
    exact P.piBottom.injective.eq_iff
  have e3 : (P.piBottom b = (ofPerm (P.perm)).last true) ↔ (b = P.last true) := by
    rw [ofPerm_last_true (P.perm),
      ← IETDatum₂.piBottom_last_true P]
    exact P.piBottom.injective.eq_iff
  simp only [IETDatum₂.rvMat, Bool.not_false, e1, e2, e3]

/-- The multiplicity matrix `multOne` is the `ℕ`-matrix of `rvMat` of the step, conjugated
by `piBottom`. -/
theorem rvMatNat_ofPerm_false (P : IETDatum₂ α n) (a b : α) :
    P.rvMatNat false a b = multOne P.perm (P.piBottom a) (P.piBottom b) := by
  have key (i) (j : Fin n) : (ofPerm (P.perm)).rvMat false i j
      = if j = i then 1 else if j = topCell P.perm ∧ i = (lastPos n) then 1 else 0 := by
    rw [rvMat_ofPerm_false_apply]
    by_cases h1 : i = j
    · subst h1
      simp
    · rw [ite_eq_right h1, ite_eq_right (Ne.symm h1)]
      by_cases h2 : i = (lastPos n) ∧ j = topCell P.perm
      · rw [ite_eq_left h2, ite_eq_left ⟨h2.2, h2.1⟩]
      · rw [ite_eq_right h2, ite_eq_right (fun hc => h2 ⟨hc.2, hc.1⟩)]
  rw [rvMatNat, IETDatum₂.rvMat_ofPerm_false P a b, key (P.piBottom a) (P.piBottom b), multOne]
  split_ifs <;> simp

end IETDatum₂

end IntervalExchange

/-! ## 4. The renormalised length vectors in `α` coordinates, and the target statement -/

namespace IntervalExchange.RauzyVeech

variable {n : ℕ} [NeZero n]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The length vector after a Rauzy step of type `ε`: the letter `last ε` loses the length of the
letter `last (!ε)` (this is `λ = V λ̂` solved for `λ̂`). -/
def hatLam (P : IETDatum₂ α n) (ε : Bool) (lam : α → ℝ≥0) : α → ℝ≥0 :=
  fun a => if a = P.last ε then lam a - lam (P.last (!ε)) else lam a

/-- The renormalised length vector at the end of the word `γ`. -/
noncomputable def lamAfter (P : IETDatum₂ α n) : List Bool → (α → ℝ≥0) → α → ℝ≥0
  | [], lam => lam
  | e :: es, lam => lamAfter (P.rvStep e) es (hatLam P e lam)

@[simp] theorem lamAfter_nil (P : IETDatum₂ α n) (lam : α → ℝ≥0) : lamAfter P [] lam = lam := (rfl)

theorem lamAfter_cons (P : IETDatum₂ α n) (e : Bool) (es : List Bool) (lam : α → ℝ≥0) :
    lamAfter P (e :: es) lam = lamAfter (P.rvStep e) es (hatLam P e lam) := (rfl)

/-- **One letter.**  `lamAfter_cons` with `es = []` followed by `lamAfter_nil`; it is therefore not
a `simp` lemma, `simp` reaching the same normal form through those two. -/
theorem lamAfter_singleton (P : IETDatum₂ α n) (e : Bool) (lam : α → ℝ≥0) :
    lamAfter P [e] lam = hatLam P e lam := (rfl)

/-- The renormalised length vector, read in bottom order, is `lamHat` of the permutation of
`Fin n`. -/
theorem lengthsInBottom_hatLam (P : IETDatum₂ α n) (lam : α → ℝ≥0) :
    (P.rvStep false).lengthsInBottom (hatLam P false lam)
      = lamHat P.perm (P.lengthsInBottom lam) := by
  have e2 (i : Fin n) : (P.piBottom.symm i = P.last false) ↔ (i = (lastPos n)) := by
    rw [Equiv.symm_apply_eq, IETDatum₂.piBottom_last_false]
  have hL : lam (P.piBottom.symm (topCell P.perm)) = lam (P.last true) := by
    rw [← IETDatum₂.piBottom_last_true P, Equiv.symm_apply_apply]
  funext i
  simp only [IETDatum₂.lengthsInBottom, hatLam, lamHat, IETDatum₂.rvStep_piBottom_false,
    Bool.not_false]
  by_cases hi : i = (lastPos n)
  · rw [ite_eq_left ((e2 i).mpr hi), ite_eq_left hi, hL]
  · rw [ite_eq_right (fun hc => hi ((e2 i).mp hc)), ite_eq_right hi]

/-- The cell of the letter `b` in the exchange renormalised at the end of `γ`: the cell of
`mkIETFun ((vertex P γ).lengthsInBottom (lamAfter P γ lam)) (vertex P γ).perm 0`. -/
def cellAt (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) (b : α) : Set ℝ :=
  Set.Ico (leftEnd ((IETDatum₂.vertex P γ).lengthsInBottom (lamAfter P γ lam))
      ((IETDatum₂.vertex P γ).piBottom b))
    (upperEnd ((IETDatum₂.vertex P γ).lengthsInBottom (lamAfter P γ lam))
      ((IETDatum₂.vertex P γ).piBottom b))

end IntervalExchange.RauzyVeech

end
