/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.IET
public import IETFree.Pair.MeasureTools

/-!
**Translation vectors are lattice vectors with coefficients in `{-1, 0, 1}`.**

For the exchange with lengths `lam` and permutation `π`, the displacement of a point `x` of the
`i`-th interval is

`translationVector π lam i = ∑_{π j < π i} lam j - ∑_{j < i} lam j`,

an integer combination of the lengths whose coefficients all lie in `{-1, 0, 1}`.  This is the base
case of the "translation-vector bound" used in the proof of the paper's Theorem 2.6: after composing
words, coefficients grow at most like the word length, which turns the Diophantine lower bound into
`C / |w| ^ c ≤ ℓ` for the length `ℓ` of a nontrivial translation interval of `w(f, g)`.

The statement proved here, in the abstract form, is: *if every displacement of `f` and of `g` is a
lattice vector with coefficients in `{-1, 0, 1}`, then every displacement of a word of length `n` is
a lattice vector with coefficients in `[-n, n]`*.  The lemmas here supply that hypothesis for
`f = g = mkIETFun lam π 0` (`mkIETFun_sub_eq_sum_dispCoeff`), together with the bookkeeping that
identifies the coercion of `evalWord w f g` with the corresponding permutation lift
(`evalWord_apply_coe`).
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

/-! ## The displacement of a single exchange -/

/-- **The translation vector is a lattice vector with coefficients in `{-1, 0, 1}`.** -/
theorem translationVector_eq_sum {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (i : Fin n) :
    translationVector π lam i
      = ∑ j, (((if π j < π i then (1 : ℤ) else 0) - (if j < i then (1 : ℤ) else 0) : ℤ) : ℝ)
          * (lam j : ℝ) := by
  have himg : imageLeft π lam i = ∑ j, (if π j < π i then (lam j : ℝ) else 0) := by
    rw [imageLeft, Finset.sum_filter]
  have hleft : leftEnd lam i = ∑ j, (if j < i then (lam j : ℝ) else 0) := by
    rw [leftEnd, Finset.sum_filter]
  rw [translationVector, himg, hleft, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> ring

/-- The coefficient of `lam j` in the translation vector of the `i`-th interval. -/
def translationCoeff {n : ℕ} (π : Equiv.Perm (Fin n)) (i j : Fin n) : ℤ :=
  (if π j < π i then 1 else 0) - (if j < i then 1 else 0)

/-- Every coefficient of a translation vector is `-1`, `0` or `1`. -/
theorem abs_translationCoeff_le_one {n : ℕ} (π : Equiv.Perm (Fin n)) (i j : Fin n) :
    |translationCoeff π i j| ≤ 1 := by
  unfold translationCoeff
  split_ifs <;> simp

/-- The translation vector as a lattice combination, with the coefficient function
`translationCoeff`. -/
theorem translationVector_eq_sum_coeff {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0)
    (i : Fin n) :
    translationVector π lam i = ∑ j, (translationCoeff π i j : ℝ) * (lam j : ℝ) :=
  translationVector_eq_sum π lam i

/-! ## The lift of a word, as a permutation -/

/-- The coercion of an exchange to the underlying permutation, as a monoid homomorphism. -/
def IET.coeHom {a b : ℝ} : IET a b →* Equiv.Perm ℝ where
  toFun e := e.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem IET.coeHom_apply {a b : ℝ} (e : IET a b) : IET.coeHom e = e.toEquiv := rfl

/-- **`evalWord` is the lift of the two exchanges as permutations**: the coercion of the group
element
`evalWord w f g` to a function is the image of `w` under the homomorphism into `Equiv.Perm ℝ`. -/
theorem evalWord_apply_coe (w : FreeGroup Gen) (f g : IET 0 1) :
    ⇑(evalWord w f g)
      = FreeGroup.lift (fun i : Gen => if i = 0 then f.toEquiv else g.toEquiv) w := by
  have h2 : IET.coeHom.comp (FreeGroup.lift (fun i : Gen => if i = 0 then f else g))
      = FreeGroup.lift (fun i : Gen => if i = 0 then f.toEquiv else g.toEquiv) := by
    refine FreeGroup.ext_hom _ _ (fun i => ?_)
    by_cases h : i = 0 <;> simp [h]
  exact congrArg (fun (φ : FreeGroup Gen →* Equiv.Perm ℝ) => ⇑(φ w)) h2

/-! ## Instantiation for the exchanges `mkIET1' lam π` and `mkIET1' mu σ` -/

/-- The coefficient vector of the displacement of `mkIETFun lam π a` at `y`, extended by `0` off the
interval. -/
noncomputable def dispCoeff {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n)) (a y :
  ℝ) :
    Fin n → ℤ :=
  if hy : y ∈ Set.Ico a (a + ∑ i, (lam i : ℝ)) then translationCoeff π (idx lam (y - a) (by linarith
    [hy.1])) else 0

theorem dispCoeff_abs_le_one {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a y : ℝ) (i : Fin n) : |dispCoeff lam π a y i| ≤ 1 := by
  unfold dispCoeff
  split_ifs
  · exact abs_translationCoeff_le_one π _ i
  · simp

theorem mkIETFun_sub_eq_sum_dispCoeff {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin n)) (a y : ℝ) :
    mkIETFun lam π a y - y = ∑ i, (dispCoeff lam π a y i : ℝ) * (lam i : ℝ) := by
  unfold dispCoeff
  split_ifs with hy
  · rw [mkIETFun_of_mem lam π a hy, translationVector_eq_sum_coeff]
    ring
  · rw [mkIETFun_of_notMem lam π a hy]; simp

/-! ## Cell starts are lattice vectors with coefficients in `{0, 1}` -/

/-- **A cell start is a lattice vector with coefficients in `{0, 1}`**:
`leftEnd lam i = ∑_{j < i} lam j`. -/
theorem leftEnd_eq_sum {n : ℕ} (lam : Fin n → ℝ≥0) (i : Fin n) :
    leftEnd lam i = ∑ j, (((if j < i then (1 : ℤ) else 0) : ℤ) : ℝ) * (lam j : ℝ) := by
  rw [leftEnd, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> ring

/-- The cell starts of the exchange, as a finite subset of `[0, 1)`. -/
noncomputable def cellCuts {n : ℕ} (lam : Fin n → ℝ≥0) : Finset ℝ :=
  (Finset.univ.image (fun i => leftEnd lam i)).filter (fun c => c ∈ Set.Ico (0 : ℝ) 1)

theorem mem_cellCuts {n : ℕ} (lam : Fin n → ℝ≥0) {c : ℝ} :
    c ∈ cellCuts lam ↔ ∃ i, leftEnd lam i = c ∧ 0 ≤ c ∧ c < 1 := by
  constructor
  · intro hc
    obtain ⟨himg, hmem⟩ := Finset.mem_filter.mp hc
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp himg
    exact ⟨i, rfl, hmem.1, hmem.2⟩
  · rintro ⟨i, rfl, h0, h1⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), ⟨h0, h1⟩⟩

/-- Every cell start of the exchange is a lattice combination of the lengths with coefficients
`0` or `1`. -/
theorem cellCuts_lattice {n : ℕ} (lam : Fin n → ℝ≥0) {c : ℝ} (hc : c ∈ cellCuts lam) :
    ∃ a : Fin n → ℤ, (∀ i, |a i| ≤ 1) ∧ c = ∑ i, (a i : ℝ) * (lam i : ℝ) := by
  obtain ⟨i, rfl, -, -⟩ := mem_cellCuts lam |>.mp hc
  refine ⟨fun j => if j < i then 1 else 0, fun j => ?_, leftEnd_eq_sum lam i⟩
  simp only []
  split_ifs <;> simp

end
