/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.Pair.RobustRelation.WordData
public import IETFree.Pair.TranslationVector
import Mathlib.Tactic.Linarith.NNRealPreprocessor

/-!
# The cuts and displacements of a single letter

The induction of `WordData.lean` starts from the four letters `f`, `g`, `f⁻¹`, `g⁻¹`.  A letter
is an exchange `mkIET1 (λ ∘ σ₀) ρ` on the open region — a reindexing of the lengths and a
permutation,
which is what each of the four becomes once the parameter is substituted: its cuts are
`withTop (revCut σ₀)` and its displacement on the `i`-th piece is `revTv σ₀ ρ i`, both affine in the
parameter and lattice combinations of the lengths (`isFullLat_revCut`, `isFullLat_revTv`).
`mkIETFun_rev_piece` is the piece statement, and `exists_wordData_singleton` assembles the four
instances of the certificate `WordData`.
-/


@[expose] public section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace IntervalExchange.Pair

/-! ## 9. The cut list of a single letter -/

/-- **Adding the top cut `1`** to a list of `n` cell starts: the `i`-th cut for `i < n` is the
`i`-th cell start and the last cut is `1`. -/
noncomputable def withTop {d e n : ℕ} (u : Fin n → ParamAffine d e) :
    Fin (n + 1) → ParamAffine d e :=
  fun j => if h : j.val < n then u ⟨j.val, h⟩ else AffineMap.const ℝ (PReal d e) 1

theorem withTop_castSucc {d e n : ℕ} (u : Fin n → ParamAffine d e) (i : Fin n) :
    withTop u i.castSucc = u i := by
  rw [withTop, dite_eq_left (by simp)]
  exact congrArg u (Fin.ext rfl)

theorem withTop_last {d e n : ℕ} (u : Fin n → ParamAffine d e) :
    withTop u (Fin.last n) = AffineMap.const ℝ (PReal d e) 1 := by
  rw [withTop, dite_eq_right (by simp)]

theorem withTop_succ {d e n : ℕ} (u : Fin n → ParamAffine d e) (i : Fin n) {q : PReal d e} :
    withTop u i.succ q = if h : i.val + 1 < n then u ⟨i.val + 1, h⟩ q else 1 := by
  rw [withTop]
  by_cases h : i.val + 1 < n
  · rw [dite_eq_left (by simpa using h), dite_eq_left h]
    exact congrArg (fun v => v q) (congrArg u (Fin.ext rfl))
  · rw [dite_eq_right (by simpa using h), dite_eq_right h]
    simp

/-- **The lengths of the simplex are positive on the open region.** -/
theorem positive_simplexMap {d : ℕ} {v : Fin (d - 1) → ℝ} (hv : v ∈ simplexRegion d) :
    Positive (simplexMap d v) := by
  intro i
  by_cases h : i.val + 1 = d
  · rw [simplexMap, dite_eq_left h, ← NNReal.coe_pos,
      Real.coe_toNNReal _ (by linarith [hv.2])]
    linarith [hv.2]
  · have hi : i.val < d - 1 := by have := i.isLt; omega
    rw [simplexMap, dite_eq_right h, ← NNReal.coe_pos, Real.coe_toNNReal _ (le_of_lt (hv.1 _))]
    exact hv.1 _

/-- **The cell starts of the exchange with lengths `λ ∘ σ₀`**: `∑_{j<i} λ_{σ₀ j}`, in the
coefficient form adapted to `IsFullLat`. -/
noncomputable def revCut {d e : ℕ} [NeZero d] (σ₀ : Equiv.Perm (Fin d)) (i : Fin d) :
    ParamAffine d e :=
  ∑ k : Fin d,
    ((if (σ₀.symm k).val < i.val then (1 : ℤ) else 0 : ℤ) : ℝ) • imageLenAffine (e := e) k

/-- **The upper ends of the cells**: `∑_{j≤i} λ_{σ₀ j}`. -/
noncomputable def revUpper {d e : ℕ} [NeZero d] (σ₀ : Equiv.Perm (Fin d)) (i : Fin d) :
    ParamAffine d e :=
  ∑ k : Fin d,
    ((if (σ₀.symm k).val ≤ i.val then (1 : ℤ) else 0 : ℤ) : ℝ) • imageLenAffine (e := e) k

/-- **The translation vector of the exchange** with lengths `λ ∘ σ₀` and permutation `ρ`. -/
noncomputable def revTv {d e : ℕ} [NeZero d] (σ₀ ρ : Equiv.Perm (Fin d)) (i : Fin d) :
    ParamAffine d e :=
  ∑ k : Fin d,
    ((translationCoeff ρ i (σ₀.symm k) : ℤ) : ℝ) • imageLenAffine (e := e) k

theorem revCut_eq {d e : ℕ} [NeZero d] (σ₀ : Equiv.Perm (Fin d)) (i : Fin d) {q : PReal d e}
    (hq : q.1 ∈ simplexRegion d) :
    revCut (e := e) σ₀ i q = leftEnd (fun j => simplexMap d q.1 (σ₀ j)) i := by
  have h1 : revCut (e := e) σ₀ i q
      = ∑ k : Fin d, ((if (σ₀.symm k).val < i.val then (1 : ℤ) else 0 : ℤ) : ℝ)
          * (imageLenAffine (e := e) k q) := by
    rw [revCut, AffineMap.sum_apply]
    exact Finset.sum_congr rfl (fun k _ => smul_eq_mul _ _)
  rw [h1, leftEnd, Finset.sum_filter]
  rw [← Equiv.sum_comp σ₀]
  simp only [Equiv.symm_apply_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : k.val < i.val
  · rw [ite_eq_left (show k < i from h), imageLenAffine_eq hq (σ₀ k), ite_eq_left h]
    norm_num
  · rw [ite_eq_right (show ¬ (k < i) from h), ite_eq_right h]
    simp

theorem revUpper_eq {d e : ℕ} [NeZero d] (σ₀ : Equiv.Perm (Fin d)) (i : Fin d) {q : PReal d e}
    (hq : q.1 ∈ simplexRegion d) :
    revUpper (e := e) σ₀ i q = upperEnd (fun j => simplexMap d q.1 (σ₀ j)) i := by
  have h1 : revUpper (e := e) σ₀ i q
      = ∑ k : Fin d, ((if (σ₀.symm k).val ≤ i.val then (1 : ℤ) else 0 : ℤ) : ℝ)
          * (imageLenAffine (e := e) k q) := by
    rw [revUpper, AffineMap.sum_apply]
    exact Finset.sum_congr rfl (fun k _ => smul_eq_mul _ _)
  rw [h1, upperEnd, Finset.sum_filter]
  rw [← Equiv.sum_comp σ₀]
  simp only [Equiv.symm_apply_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : k.val ≤ i.val
  · rw [ite_eq_left (show k ≤ i from h), imageLenAffine_eq hq (σ₀ k), ite_eq_left h]
    norm_num
  · rw [ite_eq_right (show ¬ (k ≤ i) from h), ite_eq_right h]
    simp

theorem revTv_eq {d e : ℕ} [NeZero d] (σ₀ ρ : Equiv.Perm (Fin d)) (i : Fin d) {q : PReal d e}
    (hq : q.1 ∈ simplexRegion d) :
    revTv (e := e) σ₀ ρ i q = translationVector ρ (fun j => simplexMap d q.1 (σ₀ j)) i := by
  have h1 : revTv (e := e) σ₀ ρ i q
      = ∑ k : Fin d, ((translationCoeff ρ i (σ₀.symm k) : ℤ) : ℝ)
          * (imageLenAffine (e := e) k q) := by
    rw [revTv, AffineMap.sum_apply]
    exact Finset.sum_congr rfl (fun k _ => smul_eq_mul _ _)
  rw [h1, translationVector_eq_sum_coeff]
  rw [← Equiv.sum_comp σ₀]
  simp only [Equiv.symm_apply_apply]
  exact Finset.sum_congr rfl (fun k _ => by rw [imageLenAffine_eq hq (σ₀ k)])

/-- The linear combination `∑ cₖ • λₖ` applied at a point: the coefficients act as multipliers. -/
theorem sum_smul_imageLenAffine_apply {d e : ℕ} [NeZero d] (c : Fin d → ℤ) (q : PReal d e) :
    (∑ k : Fin d, ((c k : ℤ) : ℝ) • imageLenAffine (e := e) k) q
      = ∑ k : Fin d, ((c k : ℤ) : ℝ) * (imageLenAffine (e := e) k q) := by
  rw [AffineMap.sum_apply]
  exact Finset.sum_congr rfl (fun k _ => smul_eq_mul _ _)

theorem isFullLat_revCut {d e : ℕ} [NeZero d] [NeZero e] (σ₀ : Equiv.Perm (Fin d)) (i : Fin d) :
    IsFullLat (d := d) (e := e) 1 (revCut (e := e) σ₀ i) := by
  refine ⟨fun k => if (σ₀.symm k).val < i.val then 1 else 0, 0, fun k => ?_, fun k => by simp, ?_⟩
  · by_cases h : (σ₀.symm k).val < i.val <;> simp [h]
  · have hL := sum_smul_imageLenAffine_apply (d := d) (e := e)
      (fun k => if (σ₀.symm k).val < i.val then 1 else 0)
    intro q
    rw [revCut, hL q]
    simp

theorem isFullLat_revTv {d e : ℕ} [NeZero d] [NeZero e] (σ₀ ρ : Equiv.Perm (Fin d)) (i : Fin d) :
    IsFullLat (d := d) (e := e) 1 (revTv (e := e) σ₀ ρ i) := by
  refine ⟨fun k => translationCoeff ρ i (σ₀.symm k), 0, fun k => abs_translationCoeff_le_one ρ i _,
    fun k => by simp, ?_⟩
  have hL := sum_smul_imageLenAffine_apply (d := d) (e := e)
    (fun k => translationCoeff ρ i (σ₀.symm k))
  intro q
  rw [revTv, hL q]
  simp

/-- **`mkIETFun` translates on the cells of the exchange with lengths `λ ∘ σ₀`**: this is the
one-letter piece statement, for an arbitrary reindexing `σ₀` of the lengths and permutation `ρ`. -/
theorem mkIETFun_rev_piece {d e : ℕ} [NeZero d] (σ₀ ρ : Equiv.Perm (Fin d)) {q : PReal d e}
    (hq : q.1 ∈ simplexRegion d) (k : Fin d) {x : ℝ}
    (h1 : revCut (e := e) σ₀ k q ≤ x) (h2 : x < revUpper (e := e) σ₀ k q) :
    mkIETFun (fun i => simplexMap d q.1 (σ₀ i)) ρ 0 x = x + revTv (e := e) σ₀ ρ k q := by
  set lam : Fin d → ℝ≥0 := fun i => simplexMap d q.1 (σ₀ i) with hlam
  have hpos : Positive lam := fun i => positive_simplexMap hq (σ₀ i)
  have hsum : (∑ i, (lam i : ℝ)) = 1 := by
    have h := sum_coe_eq_one (simplexMap_mem_simplex_fin hq.1 hq.2)
    rw [← h]
    exact Equiv.sum_comp σ₀ (fun i => (simplexMap d q.1 i : ℝ))
  have hx1 : (0 : ℝ) ≤ x := by
    refine le_trans ?_ h1
    rw [revCut_eq σ₀ k hq, leftEnd]
    exact Finset.sum_nonneg (fun j _ => (lam j).coe_nonneg)
  have hx2 : x < 1 := by
    refine lt_of_lt_of_le h2 ?_
    rw [revUpper_eq σ₀ k hq]
    calc upperEnd lam k ≤ ∑ j, (lam j : ℝ) := upperEnd_le_total lam k
      _ = 1 := hsum
  have hxT : x ∈ Set.Ico (0 : ℝ) (0 + ∑ i, (lam i : ℝ)) := by
    rw [hsum]
    exact ⟨hx1, by simpa using hx2⟩
  rw [mkIETFun_of_mem lam ρ 0 hxT]
  have hidx : idx lam (x - 0) (by linarith [hxT.1]) = k := by
    refine idx_eq lam ⟨by simpa using hx1, ?_⟩ ?_ ?_
    · simpa [hsum] using hx2
    · rw [← revCut_eq σ₀ k hq]; simpa using h1
    · rw [← revUpper_eq σ₀ k hq]; simpa using h2
  rw [hidx, ← revTv_eq σ₀ ρ k hq]

theorem revCut_zero {d e : ℕ} [NeZero d] (σ₀ : Equiv.Perm (Fin d)) :
    revCut (e := e) σ₀ 0 = 0 := by
  rw [revCut]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [ite_eq_right (by simp), Int.cast_zero, zero_smul]

theorem withTop_revCut_mono {d e : ℕ} [NeZero d] (σ₀ : Equiv.Perm (Fin d)) {q : PReal d e}
    (hq : q.1 ∈ simplexRegion d) :
    StrictMono fun j => withTop (revCut (e := e) σ₀) j q := by
  have hpos : Positive (fun j => simplexMap d q.1 (σ₀ j)) :=
    fun j => positive_simplexMap hq (σ₀ j)
  have hsum : (∑ j, ((simplexMap d q.1 (σ₀ j) : ℝ≥0) : ℝ)) = 1 := by
    rw [Equiv.sum_comp σ₀ (fun i => (simplexMap d q.1 i : ℝ))]
    exact sum_coe_eq_one (simplexMap_mem_simplex_fin hq.1 hq.2)
  intro a b hab
  change (withTop (revCut (e := e) σ₀) a) q < (withTop (revCut (e := e) σ₀) b) q
  rw [Fin.lt_def] at hab
  have hmem : ∀ i : Fin d, withTop (revCut (e := e) σ₀) i.castSucc q
      = leftEnd (fun j => simplexMap d q.1 (σ₀ j)) i := by
    intro i
    rw [withTop_castSucc, revCut_eq σ₀ i hq]
  have hlast : withTop (revCut (e := e) σ₀) (Fin.last d) q = 1 := by
    rw [withTop_last]; rfl
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
    · rw [hmem a', hmem b']
      refine leftEnd_lt_leftEnd hpos ?_
      simpa using hab
    · rw [hmem a', hlast]
      have h2 := leftEnd_add_le_total (fun j => simplexMap d q.1 (σ₀ j)) a'
      have h3 := hpos a'
      rw [hsum] at h2
      linarith
  · have := b.isLt
    simp only [Fin.val_last] at hab
    omega

theorem withTop_revCut_succ {d e : ℕ} [NeZero d] (σ₀ : Equiv.Perm (Fin d)) (k : Fin d)
    {q : PReal d e} (hq : q.1 ∈ simplexRegion d) :
    withTop (revCut (e := e) σ₀) k.succ q = revUpper (e := e) σ₀ k q := by
  have hsum : (∑ j, ((simplexMap d q.1 (σ₀ j) : ℝ≥0) : ℝ)) = 1 := by
    rw [Equiv.sum_comp σ₀ (fun i => (simplexMap d q.1 i : ℝ))]
    exact sum_coe_eq_one (simplexMap_mem_simplex_fin hq.1 hq.2)
  rw [withTop_succ]
  by_cases h : k.val + 1 < d
  · rw [dite_eq_left h]
    rw [revUpper, revCut, AffineMap.sum_apply, AffineMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hj : (σ₀.symm j).val ≤ k.val
    · have hj' : (σ₀.symm j).val < k.val + 1 := by omega
      rw [ite_eq_left hj, ite_eq_left hj']
    · have hj' : ¬ (σ₀.symm j).val < k.val + 1 := by omega
      rw [ite_eq_right hj, ite_eq_right hj']
  · rw [dite_eq_right h]
    have hmax : ∀ j : Fin d, j ≤ k := by
      intro j
      rw [Fin.le_def]
      have := k.isLt
      omega
    rw [revUpper_eq σ₀ k hq, upperEnd_of_max (fun j => simplexMap d q.1 (σ₀ j)) hmax]
    exact hsum.symm

/-- The constant `1` is a bounded integer-affine function as soon as `1 ≤ K`. -/
theorem isFreeLat_const_one {d e : ℕ} {K : ℤ} (hK : 1 ≤ K) :
    IsFreeLat (d := d) (e := e) K (AffineMap.const ℝ (PReal d e) 1) := by
  refine ⟨1, 0, 0, ?_, fun i => ?_, fun j => ?_, fun q => ?_⟩
  · simpa using hK
  · simp only [Pi.zero_apply, abs_zero]; linarith
  · simp only [Pi.zero_apply, abs_zero]; linarith
  · simp

/-- The first coordinate of a point of a ball is in the corresponding ball. -/
theorem mem_ball_fst {d e : ℕ} {q₀ : PReal d e} {ε : ℝ} {q : PReal d e}
    (hq : q ∈ Metric.ball q₀ ε) : q.1 ∈ Metric.ball q₀.1 ε := by
  rw [Metric.mem_ball, Prod.dist_eq] at hq
  rw [Metric.mem_ball]
  exact lt_of_le_of_lt (le_max_left _ _) hq

/-- The second coordinate of a point of a ball is in the corresponding ball. -/
theorem mem_ball_snd {d e : ℕ} {q₀ : PReal d e} {ε : ℝ} {q : PReal d e}
    (hq : q ∈ Metric.ball q₀ ε) : q.2 ∈ Metric.ball q₀.2 ε := by
  rw [Metric.mem_ball, Prod.dist_eq] at hq
  rw [Metric.mem_ball]
  exact lt_of_le_of_lt (le_max_right _ _) hq

/-- **The symbolic data of a single letter**, for an arbitrary reindexing `σ₀` of the lengths and an
arbitrary permutation `ρ`: if the letter is `mkIET1 (λ ∘ σ₀) ρ` on the open region, its cuts are
`withTop (revCut σ₀)` and its displacements on the pieces are `revTv σ₀ ρ`. -/
theorem exists_wordData_singleton_of_rev {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) (b : Fin 2 × Bool)
    (σ₀ ρ : Equiv.Perm (Fin d)) {q₀ : PReal d e}
    (hq₀ : q₀.1 ∈ simplexRegion d ∧ q₀.2 ∈ simplexRegion e)
    (hA : ∀ q : PReal d e, q.1 ∈ simplexRegion d →
      ltrQ π σ b q = mkIET1 (fun i => simplexMap d q.1 (σ₀ i)) ρ) :
    Nonempty (WordData π σ [b] q₀) := by
  classical
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.isOpen_iff.mp (isOpen_simplexRegion d) q₀.1 hq₀.1
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.isOpen_iff.mp (isOpen_simplexRegion e) q₀.2 hq₀.2
  obtain ⟨ε₃, hε₃, hball₃⟩ :=
    exists_ball_strictMono (withTop (revCut (e := e) σ₀)) (withTop_revCut_mono σ₀ hq₀.1)
  refine ⟨?_⟩
  refine
    { ε := min ε₁ (min ε₂ ε₃)
      hε := lt_min hε₁ (lt_min hε₂ hε₃)
      m := d
      hm := NeZero.pos d
      s := withTop (revCut (e := e) σ₀)
      D := revTv (e := e) σ₀ ρ
      lz := 0
      lo := Fin.last d
      hlz := ?_
      hlo := ?_
      hstrict := ?_
      hmono := ?_
      hregion := ?_
      hpiece := ?_
      hsLat := ?_
      hD := ?_ }
  · rw [show (0 : Fin (d + 1)) = (0 : Fin d).castSucc from Fin.ext rfl, withTop_castSucc,
      revCut_zero]
  · rw [withTop_last]
  · exact withTop_revCut_mono σ₀ hq₀.1
  · intro q hq
    have hsub : Metric.ball q₀ (min ε₁ (min ε₂ ε₃)) ⊆ Metric.ball q₀ ε₃ :=
      Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _))
    exact (hball₃ q (hsub hq)).monotone
  · intro q hq
    refine ⟨hball₁ (mem_ball_fst (Metric.ball_subset_ball (min_le_left _ _) hq)), ?_⟩
    exact hball₂ (mem_ball_snd
      (Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _)) hq))
  · intro q hq k x hx h1 h2
    have hq1 : q.1 ∈ simplexRegion d :=
      hball₁ (mem_ball_fst (Metric.ball_subset_ball (min_le_left _ _) hq))
    have hc1 : revCut (e := e) σ₀ k q ≤ x := by
      have h := h1
      rwa [withTop_castSucc] at h
    have hc2 : x < revUpper (e := e) σ₀ k q := by
      have h := h2
      rw [withTop_revCut_succ σ₀ k hq1] at h
      exact h
    have hpiece := mkIETFun_rev_piece σ₀ ρ hq1 k hc1 hc2
    have hl : (∑ i, simplexMap d q.1 (σ₀ i)) = 1 := by
      rw [Equiv.sum_comp σ₀]
      exact simplexMap_mem_simplex_fin hq1.1 hq1.2
    simp only [List.map_singleton, List.prod_singleton]
    rw [hA q hq1, mkIET1_of_mem hl,
      mkIET1_eq_mkIETFun (fun i => simplexMap d q.1 (σ₀ i)) ρ hl x]
    exact hpiece
  · intro k
    rw [withTop]
    by_cases hk : k.val < d
    · rw [dite_eq_left hk]
      have h := (isFullLat_revCut (d := d) (e := e) σ₀ ⟨k.val, hk⟩).isFreeLat
      refine h.mono ?_
      simp
    · rw [dite_eq_right hk]
      refine isFreeLat_const_one ?_
      simp
  · intro k
    have h := (isFullLat_revTv (d := d) (e := e) σ₀ ρ k).isFreeLat
    refine h.mono ?_
    simp

/-- **The inverse of `mkIET1'`**: as a function it is the exchange with the reordered lengths
`imageLengths π λ` and the inverse permutation (this is the `invFun` of `mkIETEquiv`). -/
theorem inv_mkIET1'_apply {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (hl : (∑ i, lam i) = 1) (x : ℝ) :
    ((mkIET1' lam π hl)⁻¹ : IET 0 1) x = mkIETFun (imageLengths π lam) π.symm 0 x := rfl

/-- **The symbolic data of the letter `f`** (not inverted). -/
theorem exists_wordData_singleton_fst {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) {q₀ : PReal d e}
    (hq₀ : q₀.1 ∈ simplexRegion d ∧ q₀.2 ∈ simplexRegion e) :
    Nonempty (WordData π σ [(0, true)] q₀) := by
  refine exists_wordData_singleton_of_rev π σ (0, true) (Equiv.refl (Fin d)) π hq₀ ?_
  intro q hq
  have hl := simplexMap_mem_simplex_fin hq.1 hq.2
  have hfun : (fun i => simplexMap d q.1 ((Equiv.refl (Fin d)) i)) = simplexMap d q.1 := rfl
  rw [ltrQ, Bool.cond_true, ite_eq_left rfl, fOf_eq_mkIET1' π hq, hfun, mkIET1_of_mem hl]

/-- **The symbolic data of the letter `f⁻¹`**: the exchange with the reordered lengths and the
inverse permutation. -/
theorem exists_wordData_singleton_fst_inv {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) {q₀ : PReal d e}
    (hq₀ : q₀.1 ∈ simplexRegion d ∧ q₀.2 ∈ simplexRegion e) :
    Nonempty (WordData π σ [(0, false)] q₀) := by
  refine exists_wordData_singleton_of_rev π σ (0, false) π.symm π.symm hq₀ ?_
  intro q hq
  have hl := simplexMap_mem_simplex_fin hq.1 hq.2
  have hl2 : (∑ i, simplexMap d q.1 ((Equiv.symm π) i)) = 1 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sum]
    push_cast
    rw [Equiv.sum_comp (Equiv.symm π) (fun i => (simplexMap d q.1 i : ℝ))]
    exact sum_coe_eq_one hl
  rw [ltrQ, Bool.cond_false, ite_eq_left rfl, fOf_eq_mkIET1' π hq]
  refine IET.ext (fun x => ?_)
  rw [inv_mkIET1'_apply (simplexMap d q.1) π hl x, mkIET1_of_mem hl2,
    mkIET1_eq_mkIETFun (fun i => simplexMap d q.1 ((Equiv.symm π) i)) (Equiv.symm π) hl2 x]
  rfl

/-- **The cell starts of the exchange with lengths `λ ∘ σ₀`**: `∑_{j<i} λ_{σ₀ j}`, in the
coefficient form adapted to `IsFullLat`. -/
noncomputable def revCutR {d e : ℕ} [NeZero e] (σ₀ : Equiv.Perm (Fin e)) (i : Fin e) :
    ParamAffine d e :=
  ∑ k : Fin e,
    ((if (σ₀.symm k).val < i.val then (1 : ℤ) else 0 : ℤ) : ℝ) • imageLenAffineRight (d := d) k

/-- **The upper ends of the cells**: `∑_{j≤i} λ_{σ₀ j}`. -/
noncomputable def revUpperR {d e : ℕ} [NeZero e] (σ₀ : Equiv.Perm (Fin e)) (i : Fin e) :
    ParamAffine d e :=
  ∑ k : Fin e,
    ((if (σ₀.symm k).val ≤ i.val then (1 : ℤ) else 0 : ℤ) : ℝ) • imageLenAffineRight (d := d) k

/-- **The translation vector of the exchange** with lengths `λ ∘ σ₀` and permutation `ρ`. -/
noncomputable def revTvR {d e : ℕ} [NeZero e] (σ₀ ρ : Equiv.Perm (Fin e)) (i : Fin e) :
    ParamAffine d e :=
  ∑ k : Fin e,
    ((translationCoeff ρ i (σ₀.symm k) : ℤ) : ℝ) • imageLenAffineRight (d := d) k

theorem revCutR_eq {d e : ℕ} [NeZero e] (σ₀ : Equiv.Perm (Fin e)) (i : Fin e) {q : PReal d e}
    (hq : q.2 ∈ simplexRegion e) :
    revCutR (d := d) (e := e) σ₀ i q = leftEnd (fun j => simplexMap e q.2 (σ₀ j)) i := by
  have h1 : revCutR (d := d) (e := e) σ₀ i q
      = ∑ k : Fin e, ((if (σ₀.symm k).val < i.val then (1 : ℤ) else 0 : ℤ) : ℝ)
          * (imageLenAffineRight (d := d) k q) := by
    rw [revCutR, AffineMap.sum_apply]
    exact Finset.sum_congr rfl (fun k _ => smul_eq_mul _ _)
  rw [h1, leftEnd, Finset.sum_filter]
  rw [← Equiv.sum_comp σ₀]
  simp only [Equiv.symm_apply_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : k.val < i.val
  · rw [ite_eq_left (show k < i from h), imageLenAffineRight_eq hq (σ₀ k), ite_eq_left h]
    norm_num
  · rw [ite_eq_right (show ¬ (k < i) from h), ite_eq_right h]
    simp

theorem revUpperR_eq {d e : ℕ} [NeZero e] (σ₀ : Equiv.Perm (Fin e)) (i : Fin e) {q : PReal d e}
    (hq : q.2 ∈ simplexRegion e) :
    revUpperR (d := d) (e := e) σ₀ i q = upperEnd (fun j => simplexMap e q.2 (σ₀ j)) i := by
  have h1 : revUpperR (d := d) (e := e) σ₀ i q
      = ∑ k : Fin e, ((if (σ₀.symm k).val ≤ i.val then (1 : ℤ) else 0 : ℤ) : ℝ)
          * (imageLenAffineRight (d := d) k q) := by
    rw [revUpperR, AffineMap.sum_apply]
    exact Finset.sum_congr rfl (fun k _ => smul_eq_mul _ _)
  rw [h1, upperEnd, Finset.sum_filter]
  rw [← Equiv.sum_comp σ₀]
  simp only [Equiv.symm_apply_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : k.val ≤ i.val
  · rw [ite_eq_left (show k ≤ i from h), imageLenAffineRight_eq hq (σ₀ k), ite_eq_left h]
    norm_num
  · rw [ite_eq_right (show ¬ (k ≤ i) from h), ite_eq_right h]
    simp

theorem revTvR_eq {d e : ℕ} [NeZero e] (σ₀ ρ : Equiv.Perm (Fin e)) (i : Fin e) {q : PReal d e}
    (hq : q.2 ∈ simplexRegion e) :
    revTvR (d := d) (e := e) σ₀ ρ i q
      = translationVector ρ (fun j => simplexMap e q.2 (σ₀ j)) i := by
  have h1 : revTvR (d := d) (e := e) σ₀ ρ i q
      = ∑ k : Fin e, ((translationCoeff ρ i (σ₀.symm k) : ℤ) : ℝ)
          * (imageLenAffineRight (d := d) k q) := by
    rw [revTvR, AffineMap.sum_apply]
    exact Finset.sum_congr rfl (fun k _ => smul_eq_mul _ _)
  rw [h1, translationVector_eq_sum_coeff]
  rw [← Equiv.sum_comp σ₀]
  simp only [Equiv.symm_apply_apply]
  exact Finset.sum_congr rfl (fun k _ => by rw [imageLenAffineRight_eq hq (σ₀ k)])

/-- The linear combination `∑ cₖ • λₖ` applied at a point: the coefficients act as multipliers. -/
theorem sum_smul_imageLenAffineRight_apply {d e : ℕ} [NeZero e] (c : Fin e → ℤ) (q : PReal d e) :
    (∑ k : Fin e, ((c k : ℤ) : ℝ) • imageLenAffineRight (d := d) k) q
      = ∑ k : Fin e, ((c k : ℤ) : ℝ) * (imageLenAffineRight (d := d) k q) := by
  rw [AffineMap.sum_apply]
  exact Finset.sum_congr rfl (fun k _ => smul_eq_mul _ _)

theorem isFullLat_revCutR {d e : ℕ} [NeZero d] [NeZero e] (σ₀ : Equiv.Perm (Fin e)) (i : Fin e) :
    IsFullLat (d := d) (e := e) 1 (revCutR (d := d) (e := e) σ₀ i) := by
  refine ⟨0, fun k => if (σ₀.symm k).val < i.val then 1 else 0, fun k => by simp, fun k => ?_, ?_⟩
  · by_cases h : (σ₀.symm k).val < i.val <;> simp [h]
  · have hL := sum_smul_imageLenAffineRight_apply (d := d) (e := e)
      (fun k => if (σ₀.symm k).val < i.val then 1 else 0)
    intro q
    rw [revCutR, hL q]
    simp

theorem isFullLat_revTvR {d e : ℕ} [NeZero d] [NeZero e] (σ₀ ρ : Equiv.Perm (Fin e)) (i : Fin e) :
    IsFullLat (d := d) (e := e) 1 (revTvR (d := d) (e := e) σ₀ ρ i) := by
  refine ⟨0, fun k => translationCoeff ρ i (σ₀.symm k), fun k => by simp,
    fun k => abs_translationCoeff_le_one ρ i _, ?_⟩
  have hL := sum_smul_imageLenAffineRight_apply (d := d) (e := e)
    (fun k => translationCoeff ρ i (σ₀.symm k))
  intro q
  rw [revTvR, hL q]
  simp

/-- **`mkIETFun` translates on the cells of the exchange with lengths `λ ∘ σ₀`**: this is the
one-letter piece statement, for an arbitrary reindexing `σ₀` of the lengths and permutation `ρ`. -/
theorem mkIETFun_rev_pieceR {d e : ℕ} [NeZero e] (σ₀ ρ : Equiv.Perm (Fin e)) {q : PReal d e}
    (hq : q.2 ∈ simplexRegion e) (k : Fin e) {x : ℝ}
    (h1 : revCutR (d := d) (e := e) σ₀ k q ≤ x) (h2 : x < revUpperR (d := d) (e := e) σ₀ k q) :
    mkIETFun (fun i => simplexMap e q.2 (σ₀ i)) ρ 0 x = x + revTvR (d := d) (e := e) σ₀ ρ k q := by
  set lam : Fin e → ℝ≥0 := fun i => simplexMap e q.2 (σ₀ i) with hlam
  have hpos : Positive lam := fun i => positive_simplexMap hq (σ₀ i)
  have hsum : (∑ i, (lam i : ℝ)) = 1 := by
    have h := sum_coe_eq_one (simplexMap_mem_simplex_fin hq.1 hq.2)
    rw [← h]
    exact Equiv.sum_comp σ₀ (fun i => (simplexMap e q.2 i : ℝ))
  have hx1 : (0 : ℝ) ≤ x := by
    refine le_trans ?_ h1
    rw [revCutR_eq σ₀ k hq, leftEnd]
    exact Finset.sum_nonneg (fun j _ => (lam j).coe_nonneg)
  have hx2 : x < 1 := by
    refine lt_of_lt_of_le h2 ?_
    rw [revUpperR_eq σ₀ k hq]
    calc upperEnd lam k ≤ ∑ j, (lam j : ℝ) := upperEnd_le_total lam k
      _ = 1 := hsum
  have hxT : x ∈ Set.Ico (0 : ℝ) (0 + ∑ i, (lam i : ℝ)) := by
    rw [hsum]
    exact ⟨hx1, by simpa using hx2⟩
  rw [mkIETFun_of_mem lam ρ 0 hxT]
  have hidx : idx lam (x - 0) (by linarith [hxT.1]) = k := by
    refine idx_eq lam ⟨by simpa using hx1, ?_⟩ ?_ ?_
    · simpa [hsum] using hx2
    · rw [← revCutR_eq σ₀ k hq]; simpa using h1
    · rw [← revUpperR_eq σ₀ k hq]; simpa using h2
  rw [hidx, ← revTvR_eq σ₀ ρ k hq]

theorem revCutR_zero {d e : ℕ} [NeZero e] (σ₀ : Equiv.Perm (Fin e)) :
    revCutR (d := d) (e := e) σ₀ 0 = 0 := by
  rw [revCutR]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [ite_eq_right (by simp), Int.cast_zero, zero_smul]

theorem withTop_revCutR_mono {d e : ℕ} [NeZero e] (σ₀ : Equiv.Perm (Fin e)) {q : PReal d e}
    (hq : q.2 ∈ simplexRegion e) :
    StrictMono fun j => withTop (revCutR (d := d) (e := e) σ₀) j q := by
  have hpos : Positive (fun j => simplexMap e q.2 (σ₀ j)) :=
    fun j => positive_simplexMap hq (σ₀ j)
  have hsum : (∑ j, ((simplexMap e q.2 (σ₀ j) : ℝ≥0) : ℝ)) = 1 := by
    rw [Equiv.sum_comp σ₀ (fun i => (simplexMap e q.2 i : ℝ))]
    exact sum_coe_eq_one (simplexMap_mem_simplex_fin hq.1 hq.2)
  intro a b hab
  change (withTop (revCutR (d := d) (e := e) σ₀) a) q < (withTop (revCutR (d := d) (e := e) σ₀) b) q
  rw [Fin.lt_def] at hab
  have hmem : ∀ i : Fin e, withTop (revCutR (d := d) (e := e) σ₀) i.castSucc q
      = leftEnd (fun j => simplexMap e q.2 (σ₀ j)) i := by
    intro i
    rw [withTop_castSucc, revCutR_eq σ₀ i hq]
  have hlast : withTop (revCutR (d := d) (e := e) σ₀) (Fin.last e) q = 1 := by
    rw [withTop_last]; rfl
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
    · rw [hmem a', hmem b']
      refine leftEnd_lt_leftEnd hpos ?_
      simpa using hab
    · rw [hmem a', hlast]
      have h2 := leftEnd_add_le_total (fun j => simplexMap e q.2 (σ₀ j)) a'
      have h3 := hpos a'
      rw [hsum] at h2
      linarith
  · have := b.isLt
    simp only [Fin.val_last] at hab
    omega

theorem withTop_revCutR_succ {d e : ℕ} [NeZero e] (σ₀ : Equiv.Perm (Fin e)) (k : Fin e)
    {q : PReal d e} (hq : q.2 ∈ simplexRegion e) :
    withTop (revCutR (d := d) (e := e) σ₀) k.succ q = revUpperR (d := d) (e := e) σ₀ k q := by
  have hsum : (∑ j, ((simplexMap e q.2 (σ₀ j) : ℝ≥0) : ℝ)) = 1 := by
    rw [Equiv.sum_comp σ₀ (fun i => (simplexMap e q.2 i : ℝ))]
    exact sum_coe_eq_one (simplexMap_mem_simplex_fin hq.1 hq.2)
  rw [withTop_succ]
  by_cases h : k.val + 1 < e
  · rw [dite_eq_left h]
    rw [revUpperR, revCutR, AffineMap.sum_apply, AffineMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hj : (σ₀.symm j).val ≤ k.val
    · have hj' : (σ₀.symm j).val < k.val + 1 := by omega
      rw [ite_eq_left hj, ite_eq_left hj']
    · have hj' : ¬ (σ₀.symm j).val < k.val + 1 := by omega
      rw [ite_eq_right hj, ite_eq_right hj']
  · rw [dite_eq_right h]
    have hmax : ∀ j : Fin e, j ≤ k := by
      intro j
      rw [Fin.le_def]
      have := k.isLt
      omega
    rw [revUpperR_eq σ₀ k hq, upperEnd_of_max (fun j => simplexMap e q.2 (σ₀ j)) hmax]
    exact hsum.symm

theorem exists_wordData_singleton_of_revR {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) (b : Fin 2 × Bool)
    (σ₀ ρ : Equiv.Perm (Fin e)) {q₀ : PReal d e}
    (hq₀ : q₀.1 ∈ simplexRegion d ∧ q₀.2 ∈ simplexRegion e)
    (hA : ∀ q : PReal d e, q.2 ∈ simplexRegion e →
      ltrQ π σ b q = mkIET1 (fun i => simplexMap e q.2 (σ₀ i)) ρ) :
    Nonempty (WordData π σ [b] q₀) := by
  classical
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.isOpen_iff.mp (isOpen_simplexRegion d) q₀.1 hq₀.1
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.isOpen_iff.mp (isOpen_simplexRegion e) q₀.2 hq₀.2
  obtain ⟨ε₃, hε₃, hball₃⟩ :=
    exists_ball_strictMono (withTop (revCutR (d := d) (e := e) σ₀)) (withTop_revCutR_mono σ₀ hq₀.2)
  refine ⟨?_⟩
  refine
    { ε := min ε₁ (min ε₂ ε₃)
      hε := lt_min hε₁ (lt_min hε₂ hε₃)
      m := e
      hm := NeZero.pos e
      s := withTop (revCutR (d := d) (e := e) σ₀)
      D := revTvR (d := d) (e := e) σ₀ ρ
      lz := 0
      lo := Fin.last e
      hlz := ?_
      hlo := ?_
      hstrict := ?_
      hmono := ?_
      hregion := ?_
      hpiece := ?_
      hsLat := ?_
      hD := ?_ }
  · rw [show (0 : Fin (e + 1)) = (0 : Fin e).castSucc from Fin.ext rfl, withTop_castSucc,
      revCutR_zero]
  · rw [withTop_last]
  · exact withTop_revCutR_mono σ₀ hq₀.2
  · intro q hq
    have hsub : Metric.ball q₀ (min ε₁ (min ε₂ ε₃)) ⊆ Metric.ball q₀ ε₃ :=
      Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _))
    exact (hball₃ q (hsub hq)).monotone
  · intro q hq
    refine ⟨hball₁ (mem_ball_fst (Metric.ball_subset_ball (min_le_left _ _) hq)), ?_⟩
    exact hball₂ (mem_ball_snd
      (Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _)) hq))
  · intro q hq k x hx h1 h2
    have hq1 : q.2 ∈ simplexRegion e :=
      hball₂ (mem_ball_snd
        (Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _)) hq))
    have hc1 : revCutR (d := d) (e := e) σ₀ k q ≤ x := by
      have h := h1
      rwa [withTop_castSucc] at h
    have hc2 : x < revUpperR (d := d) (e := e) σ₀ k q := by
      have h := h2
      rw [withTop_revCutR_succ σ₀ k hq1] at h
      exact h
    have hpiece := mkIETFun_rev_pieceR σ₀ ρ hq1 k hc1 hc2
    have hl : (∑ i, simplexMap e q.2 (σ₀ i)) = 1 := by
      rw [Equiv.sum_comp σ₀]
      exact simplexMap_mem_simplex_fin hq1.1 hq1.2
    simp only [List.map_singleton, List.prod_singleton]
    rw [hA q hq1, mkIET1_of_mem hl,
      mkIET1_eq_mkIETFun (fun i => simplexMap e q.2 (σ₀ i)) ρ hl x]
    exact hpiece
  · intro k
    rw [withTop]
    by_cases hk : k.val < e
    · rw [dite_eq_left hk]
      have h := (isFullLat_revCutR (d := d) (e := e) σ₀ ⟨k.val, hk⟩).isFreeLat
      refine h.mono ?_
      simp
    · rw [dite_eq_right hk]
      refine isFreeLat_const_one ?_
      simp
  · intro k
    have h := (isFullLat_revTvR (d := d) (e := e) σ₀ ρ k).isFreeLat
    refine h.mono ?_
    simp

/-- **The symbolic data of the letter `g`** (not inverted). -/
theorem exists_wordData_singleton_snd {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) {q₀ : PReal d e}
    (hq₀ : q₀.1 ∈ simplexRegion d ∧ q₀.2 ∈ simplexRegion e) :
    Nonempty (WordData π σ [(1, true)] q₀) := by
  refine exists_wordData_singleton_of_revR π σ (1, true) (Equiv.refl (Fin e)) σ hq₀ ?_
  intro q hq
  have hl := simplexMap_mem_simplex_fin hq.1 hq.2
  have hfun : (fun i => simplexMap e q.2 ((Equiv.refl (Fin e)) i)) = simplexMap e q.2 := rfl
  rw [ltrQ, Bool.cond_true, ite_eq_right (by decide : ¬ (1 : Fin 2) = 0), gOf_eq_mkIET1' σ hq, hfun,
    mkIET1_of_mem hl]

/-- **The symbolic data of the letter `g⁻¹`**: the exchange with the reordered lengths and the
inverse permutation. -/
theorem exists_wordData_singleton_snd_inv {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) {q₀ : PReal d e}
    (hq₀ : q₀.1 ∈ simplexRegion d ∧ q₀.2 ∈ simplexRegion e) :
    Nonempty (WordData π σ [(1, false)] q₀) := by
  refine exists_wordData_singleton_of_revR π σ (1, false) σ.symm σ.symm hq₀ ?_
  intro q hq
  have hl := simplexMap_mem_simplex_fin hq.1 hq.2
  have hl2 : (∑ i, simplexMap e q.2 ((Equiv.symm σ) i)) = 1 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sum]
    push_cast
    rw [Equiv.sum_comp (Equiv.symm σ) (fun i => (simplexMap e q.2 i : ℝ))]
    exact sum_coe_eq_one hl
  rw [ltrQ, Bool.cond_false, ite_eq_right (by decide : ¬ (1 : Fin 2) = 0), gOf_eq_mkIET1' σ hq]
  refine IET.ext (fun x => ?_)
  rw [inv_mkIET1'_apply (simplexMap e q.2) σ hl x, mkIET1_of_mem hl2,
    mkIET1_eq_mkIETFun (fun i => simplexMap e q.2 ((Equiv.symm σ) i)) (Equiv.symm σ) hl2 x]
  rfl

/-- **All four one-letter instances** of the symbolic data. -/
theorem exists_wordData_singleton {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) {q₀ : PReal d e}
    (hq₀ : q₀.1 ∈ simplexRegion d ∧ q₀.2 ∈ simplexRegion e) :
    ∀ b : Fin 2 × Bool, Nonempty (WordData π σ [b] q₀) := by
  intro b
  obtain ⟨i, bit⟩ := b
  fin_cases i
  · cases bit
    · exact exists_wordData_singleton_fst_inv π σ hq₀
    · exact exists_wordData_singleton_fst π σ hq₀
  · cases bit
    · exact exists_wordData_singleton_snd_inv π σ hq₀
    · exact exists_wordData_singleton_snd π σ hq₀

end IntervalExchange.Pair
