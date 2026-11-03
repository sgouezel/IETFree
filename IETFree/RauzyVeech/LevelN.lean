/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.RauzyVeech.FirstReturn
import IETFree.RauzyVeech.TowerLevel
import IETFree.RauzyVeech.InvariantMeasure

/-!
# Iterated permutations, path matrices over `ℕ`, and renormalised length vectors

The infrastructure behind the level-`n` tower formula, first in `Fin n` coordinates and then in the
`α`-indexed coordinates of `IETDatum₂`:

* §1 injectivity of the exchange and disjointness of the cells of an arrangement
  (`injective_exch`, `disjoint_cell`, `pairwiseDisjoint_cellHat`);
* §2 **induced invariance** (`restrict_cut_invariant`): for an invariant `μ`, the restriction
  `μ.restrict [0, cut)` is invariant under the first-return exchange — the analytic input of the
  tower formula;
* §3 the iterates `piN` and `lamN` of the permutation and of the lengths;
* §4 `Path.Q` over `ℕ` (`Qnat`, `Qnat_cons`, `Qnat_cast`), the step of `IETDatum₂` in `Fin n`
  coordinates (`rvMat_toComb_false`, `rvMatNat_toComb_false`) and the identification of the two
  permutations (`perm_rvStep_false`);
* §5 the renormalised length vectors `hatLam`, `lamAfter` and the cells `cellAt`.

Only the type-`false` case is treated here (`IETFree/RauzyVeech/FirstReturn.lean` proves the
first-return theorem only in that case); the level-`n` formula itself, for an arbitrary word, is
`TowerTrue.tower_formula_level_pathQ_any` of `IETFree/RauzyVeech/TrueStep.lean`. -/

open MeasureTheory Finset
open scoped BigOperators ENNReal NNReal

namespace Tower

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## 1. Injectivity and disjointness -/

theorem injective_exch (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    Function.Injective (exch π lam) := by
  rw [← coe_exchEquiv π lam]
  exact (exchEquiv π lam).injective

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
theorem measurableSet_image_exch (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) {A : Set ℝ}
    (hA : MeasurableSet A) : MeasurableSet (exch π lam '' A) := by
  have himg : exch π lam '' A = ⇑(exchEquiv π lam).symm ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      change ⇑(exchEquiv π lam).symm (⇑(exchEquiv π lam) a) ∈ A
      rw [Equiv.symm_apply_apply]
      exact ha
    · intro hx
      exact ⟨⇑(exchEquiv π lam).symm x, hx, Equiv.apply_symm_apply (exchEquiv π lam) x⟩
  rw [himg]
  exact hA.preimage (measurable_exchEquiv_symm π lam)

/-- The exchange with the renormalised data maps the whole interval onto itself, so the
first-return exchange maps the cut interval onto itself. -/
theorem image_cut_self (hlt : lam (topCell π) < lam botCell) :
    exch (piHat π) (lamHat π lam) '' Set.Ico 0 (cut π lam) = Set.Ico 0 (cut π lam) := by
  have h := image_Ico_tot (piHat π) (lamHat π lam)
  rw [show tot (lamHat π lam) = cut π lam from cut_eq_sum_lamHat hlt] at h
  exact h

/-- **All floors have the same mass for the original exchange**, in the shape used below. -/
theorem measure_image_iterate' (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (μ : Measure ℝ)
    (hμ : μ.map (exch π lam) = μ) (A : Set ℝ) (hA : MeasurableSet A) (j : ℕ) :
    μ ((exch π lam)^[j] '' A) = μ A := measure_image_iterate π lam μ hμ A hA j

/-- **Induced invariance.**  If `μ` is invariant under the exchange `T = exch π lam` and `lam
(topCell π) < lam botCell`, then the restriction of `μ` to the Rauzy subinterval `[0, cut)` is
invariant under the first-return exchange `T̂ = exch (piHat π) (lamHat π lam)`.  The proof counts:
for `A ⊆ [0, cut)`, split `A` over the cells `cellHat β` of `T̂`; on `cellHat β` the return map is
`T^[returnB π β]`, and the floors `T^[j] '' cellHat β` all have the mass of `cellHat β` because `μ`
is `T`-invariant.  Hence `μ (T̂ '' A) = μ A`, and since `T̂` maps `[0, cut)` onto itself this is
the invariance. -/
theorem restrict_cut_invariant (hlt : lam (topCell π) < lam botCell) (μ : Measure ℝ)
    (hμ : μ.map (exch π lam) = μ) :
    (μ.restrict (Set.Ico 0 (cut π lam))).map (exch (piHat π) (lamHat π lam))
      = μ.restrict (Set.Ico 0 (cut π lam)) := by
  have hmeasTH : Measurable (exch (piHat π) (lamHat π lam)) := measurable_exch _ _
  have hIm : exch (piHat π) (lamHat π lam) '' Set.Ico 0 (cut π lam)
      = Set.Ico 0 (cut π lam) := image_cut_self hlt
  have hcell : ∀ β : Fin n, MeasurableSet (cellHat π lam β) := measurableSet_cellHat π lam
  -- the key counting identity
  have hmain (A : Set ℝ) (hAI : A ⊆ Set.Ico 0 (cut π lam)) (hA : MeasurableSet A) :
    μ (exch (piHat π) (lamHat π lam) '' A) = μ A := by
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
    have hmeasInt : ∀ β ∈ (Finset.univ : Finset (Fin n)),
        MeasurableSet (A ∩ cellHat π lam β) := fun β _ => hA.inter (hcell β)
    have hstep : ∀ β : Fin n, μ (exch (piHat π) (lamHat π lam) '' (A ∩ cellHat π lam β))
        = μ (A ∩ cellHat π lam β) := by
      intro β
      have hfun : ∀ y ∈ A ∩ cellHat π lam β,
          exch (piHat π) (lamHat π lam) y = (exch π lam)^[returnB π β] y := by
        rintro y ⟨-, hy⟩
        have hyI : y ∈ Set.Ico 0 (cut π lam) := cellHat_subset_cut hlt β hy
        have h1 := firstReturn_eq hlt hyI
        have h2 := ret_eq_returnB hlt hy
        rw [h2] at h1
        exact h1.symm
      rw [Set.image_congr hfun]
      exact measure_image_iterate' π lam μ hμ _ (hmeasInt β (Finset.mem_univ β)) _
    have hsum : μ A = ∑ β, μ (A ∩ cellHat π lam β) := by
      conv_lhs => rw [hcover]
      have hbi := measure_biUnion_finset (μ := μ) hdisj hmeasInt
      simpa using hbi
    have hcov : exch (piHat π) (lamHat π lam) '' A
        = ⋃ β, exch (piHat π) (lamHat π lam) '' (A ∩ cellHat π lam β) := by
      conv_lhs => rw [hcover]
      rw [Set.image_iUnion]
    have hdisj' := pairwiseDisjoint_image (injective_exch (piHat π) (lamHat π lam)) hdisj
    have hmeas' : ∀ β ∈ (Finset.univ : Finset (Fin n)),
        MeasurableSet (exch (piHat π) (lamHat π lam) '' (A ∩ cellHat π lam β)) :=
      fun β _ => measurableSet_image_exch _ _ (hmeasInt β (Finset.mem_univ β))
    have hsum' : μ (exch (piHat π) (lamHat π lam) '' A)
        = ∑ β, μ (A ∩ cellHat π lam β) := by
      rw [hcov]
      have hbi := measure_biUnion_finset (μ := μ) hdisj' hmeas'
      rw [show μ (⋃ β, exch (piHat π) (lamHat π lam) '' (A ∩ cellHat π lam β))
          = ∑ β, μ (exch (piHat π) (lamHat π lam) '' (A ∩ cellHat π lam β)) from by
        simpa using hbi]
      exact Finset.sum_congr rfl fun β _ => hstep β
    rw [hsum', hsum]
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply hmeasTH hB, Measure.restrict_apply' measurableSet_Ico,
    Measure.restrict_apply' measurableSet_Ico]
  have hA : MeasurableSet (exch (piHat π) (lamHat π lam) ⁻¹' B ∩ Set.Ico 0 (cut π lam)) :=
    (hB.preimage hmeasTH).inter measurableSet_Ico
  have hkey := hmain _ Set.inter_subset_right hA
  have himg1 : exch (piHat π) (lamHat π lam)
        '' (exch (piHat π) (lamHat π lam) ⁻¹' B ∩ Set.Ico 0 (cut π lam))
      = B ∩ exch (piHat π) (lamHat π lam) '' Set.Ico 0 (cut π lam) := by
    ext z
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨hy1, y, hy2, rfl⟩
    · rintro ⟨hzB, y, hyI, rfl⟩
      exact ⟨y, ⟨hzB, hyI⟩, rfl⟩
  rw [himg1, hIm] at hkey
  exact hkey.symm

/-! ## 3. The iterated tower formula  The Rauzy–Veech step is iterated: `piN π k` is the `k`-th
renormalised permutation, `lamN π lam k` the `k`-th renormalised length vector, and the **level-`k`
cell** of `β` is the cell of the renormalised exchange `mkIETFun (lamN π lam k) (piN π k) 0` at `β`,
i.e. `Set.Ico (leftEnd (lamN π lam k) β) (upperEnd (lamN π lam k) β)`.  For `k = 0` this is the
original cell; for `k ≥ 1` it is the cell `cellHat` of the return exchange of level `k-1`.  The
multiplicities are the products `multN π k = multOne π · multOne (piHat π) · ⋯ · multOne (piN π
(k-1))`, i.e. `Path.Q` of the word `false, …, false`. -/

end

end Tower

/-! ## 4. Bridge to `IETDatum₂ α n`: `Path.Q` over `ℕ`, renormalised lengths, cells -/

namespace IETDatum₂

open Tower

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- The elementary Rauzy–Veech matrix `rvMat` as a matrix over `ℕ`. -/
def rvMatNat (P : IETDatum₂ α n) (ε : Bool) : Matrix α α ℕ := fun a b => (P.rvMat ε a b).toNat

theorem rvMat_nonneg (P : IETDatum₂ α n) (ε : Bool) (a b : α) : 0 ≤ P.rvMat ε a b := by
  simp only [IETDatum₂.rvMat]
  split_ifs <;> norm_num

theorem rvMatNat_cast (P : IETDatum₂ α n) (ε : Bool) (a b : α) :
    ((P.rvMatNat ε a b : ℕ) : ℤ) = P.rvMat ε a b :=
  Int.toNat_of_nonneg (P.rvMat_nonneg ε a b)

/-- **`Path.Q` read over `ℕ`** (all its entries are nonnegative). -/
noncomputable def Qnat (P : IETDatum₂ α n) : List Bool → Matrix α α ℕ
  | [] => 1
  | e :: es => P.rvMatNat e * Qnat (P.rvStep e) es

@[simp] theorem Qnat_nil (P : IETDatum₂ α n) : P.Qnat [] = 1 := rfl

theorem Qnat_cons (P : IETDatum₂ α n) (e : Bool) (es : List Bool) :
    P.Qnat (e :: es) = P.rvMatNat e * (P.rvStep e).Qnat es := rfl

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
theorem piBottom_last_false (P : IETDatum₂ α n) : P.piBottom (P.last false) = botCell :=
  IETDatum₂.last_bottom P

omit [DecidableEq α] in
/-- The permutation of a IETDatum₂ step of type `false` is `piHat` of the permutation. -/
theorem perm_rvStep_false (P : IETDatum₂ α n) : (P.rvStep false).perm = piHat P.perm := by
  have hp : (IETDatum₂.pivot P false) = P.perm botCell := by
    have h : P.perm botCell = P.piTop (P.piBottom.symm botCell) := rfl
    change P.piTop (P.last false) = P.perm botCell
    rw [h, ← IETDatum₂.piBottom_last_false P, Equiv.symm_apply_apply]
  change P.piBottom.symm.trans (P.piTop.trans (IETDatum₂.insertEquiv (IETDatum₂.pivot P false)))
      = P.perm.trans (IETDatum₂.insertEquiv (P.perm botCell))
  rw [hp, ← Equiv.trans_assoc]
  rfl

/-- `rvMat` of a `IETDatum₂` step of type `false` is `rvMat` of the step of its permutation. -/
theorem rvMat_toComb_false (P : IETDatum₂ α n) (a b : α) :
    P.rvMat false a b = (toComb P.perm).rvMat false (P.piBottom a) (P.piBottom b) := by
  have e1 : (P.piBottom a = P.piBottom b) ↔ (a = b) := P.piBottom.injective.eq_iff
  have e2 : (P.piBottom a = (toComb P.perm).last false) ↔ (a = P.last false) := by
    rw [show (toComb P.perm).last false = botCell from rfl,
      ← IETDatum₂.piBottom_last_false P]
    exact P.piBottom.injective.eq_iff
  have e3 : (P.piBottom b = (toComb P.perm).last true) ↔ (b = P.last true) := by
    rw [show (toComb P.perm).last true = topCell P.perm from rfl,
      ← IETDatum₂.piBottom_last_true P]
    exact P.piBottom.injective.eq_iff
  simp only [IETDatum₂.rvMat, Bool.not_false, e1, e2, e3]

/-- The multiplicity matrix `multOne` is the `ℕ`-matrix of `rvMat` of the step, conjugated
by `piBottom`. -/
theorem rvMatNat_toComb_false (P : IETDatum₂ α n) (a b : α) :
    P.rvMatNat false a b = multOne P.perm (P.piBottom a) (P.piBottom b) := by
  have key : ∀ i j : Fin n, (toComb P.perm).rvMat false i j
      = if j = i then 1 else if j = topCell P.perm ∧ i = botCell then 1 else 0 := by
    intro i j
    rw [rvMat_toComb_false_apply]
    by_cases h1 : i = j
    · subst h1
      simp
    · rw [if_neg h1, if_neg (Ne.symm h1)]
      by_cases h2 : i = botCell ∧ j = topCell P.perm
      · rw [if_pos h2, if_pos ⟨h2.2, h2.1⟩]
      · rw [if_neg h2, if_neg (fun hc => h2 ⟨hc.2, hc.1⟩)]
  rw [rvMatNat, IETDatum₂.rvMat_toComb_false P a b, key (P.piBottom a) (P.piBottom b), multOne]
  split_ifs <;> simp

end IETDatum₂

/-! ## 5. The renormalised length vectors in `α` coordinates, and the target statement -/

namespace Tower

open IETDatum₂

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

@[simp] theorem lamAfter_nil (P : IETDatum₂ α n) (lam : α → ℝ≥0) : lamAfter P [] lam = lam := rfl

theorem lamAfter_cons (P : IETDatum₂ α n) (e : Bool) (es : List Bool) (lam : α → ℝ≥0) :
    lamAfter P (e :: es) lam = lamAfter (P.rvStep e) es (hatLam P e lam) := rfl

/-- The renormalised length vector, read in bottom order, is the `Fin n` iterate `lamN`. -/
theorem lengthsInBottom_hatLam (P : IETDatum₂ α n) (lam : α → ℝ≥0) :
    (P.rvStep false).lengthsInBottom (hatLam P false lam)
      = lamHat P.perm (P.lengthsInBottom lam) := by
  have e2 (i : Fin n) : (P.piBottom.symm i = P.last false) ↔ (i = botCell) := by
    rw [Equiv.symm_apply_eq, IETDatum₂.piBottom_last_false]
  have hL : lam (P.piBottom.symm (topCell P.perm)) = lam (P.last true) := by
    rw [← IETDatum₂.piBottom_last_true P, Equiv.symm_apply_apply]
  funext i
  simp only [IETDatum₂.lengthsInBottom]
  change (if P.piBottom.symm i = P.last false then lam (P.piBottom.symm i) - lam (P.last true)
      else lam (P.piBottom.symm i))
    = if i = botCell then lam (P.piBottom.symm i) - lam (P.piBottom.symm (topCell P.perm))
      else lam (P.piBottom.symm i)
  by_cases hi : i = botCell
  · rw [if_pos ((e2 i).mpr hi), if_pos hi, hL]
  · rw [if_neg (fun hc => hi ((e2 i).mp hc)), if_neg hi]

/-- The cell of the letter `b` in the exchange renormalised at the end of `γ`: the cell of
`mkIETFun ((vertex P γ).lengthsInBottom (lamAfter P γ lam)) (vertex P γ).perm 0`. -/
def cellAt (P : IETDatum₂ α n) (γ : List Bool) (lam : α → ℝ≥0) (b : α) : Set ℝ :=
  Set.Ico (leftEnd ((IETDatum₂.vertex P γ).lengthsInBottom (lamAfter P γ lam))
      ((IETDatum₂.vertex P γ).piBottom b))
    (upperEnd ((IETDatum₂.vertex P γ).lengthsInBottom (lamAfter P γ lam))
      ((IETDatum₂.vertex P γ).piBottom b))

end Tower

