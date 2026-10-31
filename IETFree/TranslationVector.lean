/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.IET
import IETFree.MeasureTools

/-!
**Translation vectors are lattice vectors with coefficients in `{-1, 0, 1}`.**

For the exchange with lengths `lam` and permutation `π`, the displacement of a point `x` of the
  `i`-th
interval is

`translationVector π lam i = ∑_{π j < π i} lam j - ∑_{j < i} lam j`,

an integer combination of the lengths whose coefficients all lie in `{-1, 0, 1}`.  This is the base
case of the "translation-vector bound" used in the proof of the paper's Theorem 2.6: after composing
words, coefficients grow at most like the word length (`Tasks/translation_vector_bound.lean`, run
`translation-vector-bound`), which turns the Diophantine lower bound into `C / |w| ^ c ≤ ℓ` for the
length `ℓ` of a nontrivial translation interval of `w(f, g)`.

The generator-level statement handed to the discovery run is the abstract form: *if every
  displacement
of `f` and of `g` is a lattice vector with coefficients in `{-1, 0, 1}`, then every displacement of
  a
word of length `n` is a lattice vector with coefficients in `[-n, n]`*.  The lemmas here supply that
hypothesis for `f = g = mkIETFun lam π 0` (`mkIETFun_sub_eq_sum`), together with the bookkeeping
  that
identifies the coercion of `evalWord w f g` with the corresponding permutation lift
(`evalWord_apply_coe`).
-/

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

/-- **The displacement of `mkIETFun` is a lattice vector with coefficients in `{-1, 0, 1}`.** -/
theorem mkIETFun_sub_eq_sum {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a : ℝ) {x : ℝ} (hx : x ∈ Set.Ico a (a + ∑ i, (lam i : ℝ))) :
    ∃ D : Fin n → ℤ, (∀ i, |D i| ≤ 1) ∧
      mkIETFun lam π a x - x = ∑ i, (D i : ℝ) * (lam i : ℝ) := by
  refine ⟨translationCoeff π (idx lam (x - a) (by linarith [hx.1])), fun i => ?_, ?_⟩
  · exact abs_translationCoeff_le_one π _ i
  · rw [mkIETFun_of_mem lam π a hx, translationVector_eq_sum_coeff]
    ring

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

section aux

variable {d e : ℕ} {lam : Fin d → ℝ} {mu : Fin e → ℝ}
  {f g : Equiv.Perm ℝ} {Df : ℝ → Fin d → ℤ} {Dg : ℝ → Fin e → ℤ}

/-- Displacement of a single generator at a point, as a lattice vector with coefficients `≤ 1`. -/
lemma latticeDisp_gen (hfb : ∀ y i, |Df y i| ≤ 1) (hgb : ∀ y j, |Dg y j| ≤ 1)
    (hf : ∀ y, f y = y + ∑ i, (Df y i : ℝ) * lam i)
    (hg : ∀ y, g y = y + ∑ j, (Dg y j : ℝ) * mu j)
    (i : Fin 2) (y : ℝ) :
    ∃ s : Fin d ⊕ Fin e → ℤ, (∀ k, |s k| ≤ 1) ∧
      (if i = 0 then f else g) y = y + ∑ k, (s k : ℝ) * Sum.elim lam mu k := by
  fin_cases i
  · refine ⟨Sum.elim (Df y) (0 : Fin e → ℤ), ?_, ?_⟩
    · intro k
      cases k with
      | inl a => simpa using hfb y a
      | inr b => simp
    · change f y = _
      rw [hf y, Fintype.sum_sum_type]
      simp
  · refine ⟨Sum.elim (0 : Fin d → ℤ) (Dg y), ?_, ?_⟩
    · intro k
      cases k with
      | inl a => simp
      | inr b => simpa using hgb y b
    · change g y = _
      rw [hg y, Fintype.sum_sum_type]
      simp

/-- Displacement of one generator or its inverse, at a point. -/
lemma latticeDisp_gen_inv (hfb : ∀ y i, |Df y i| ≤ 1) (hgb : ∀ y j, |Dg y j| ≤ 1)
    (hf : ∀ y, f y = y + ∑ i, (Df y i : ℝ) * lam i)
    (hg : ∀ y, g y = y + ∑ j, (Dg y j : ℝ) * mu j)
    (i : Fin 2) (y : ℝ) :
    ∃ s : Fin d ⊕ Fin e → ℤ, (∀ k, |s k| ≤ 1) ∧
      (if i = 0 then f else g)⁻¹ y = y + ∑ k, (s k : ℝ) * Sum.elim lam mu k := by
  obtain ⟨s, hs, h⟩ := latticeDisp_gen hfb hgb hf hg i ((if i = 0 then f else g)⁻¹ y)
  refine ⟨fun k => -s k, fun k => by simpa using hs k, ?_⟩
  have hz : (if i = 0 then f else g) ((if i = 0 then f else g)⁻¹ y) = y :=
    Equiv.apply_symm_apply _ _
  rw [hz] at h
  have hS : (∑ k, ((-s k : ℤ) : ℝ) * Sum.elim lam mu k)
      = -(∑ k, (s k : ℝ) * Sum.elim lam mu k) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by push_cast; ring
  rw [hS]
  linarith

/-- The displacement of a list-word at any point is a lattice vector with coefficients bounded by
the word length. -/
lemma latticeDisp_list (hfb : ∀ y i, |Df y i| ≤ 1) (hgb : ∀ y j, |Dg y j| ≤ 1)
    (hf : ∀ y, f y = y + ∑ i, (Df y i : ℝ) * lam i)
    (hg : ∀ y, g y = y + ∑ j, (Dg y j : ℝ) * mu j)
    (L : List (Fin 2 × Bool)) (x : ℝ) :
    ∃ c : Fin d ⊕ Fin e → ℤ, (∀ k, |c k| ≤ (L.length : ℤ)) ∧
      (List.prod (L.map fun p : Fin 2 × Bool =>
        cond p.2 (if p.1 = 0 then f else g) ((if p.1 = 0 then f else g)⁻¹))) x
        = x + ∑ k, (c k : ℝ) * Sum.elim lam mu k := by
  revert x
  induction L using List.reverseRecOn with
  | nil =>
    intro x
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro k; simp
    · simp
  | append_singleton L p ih =>
    intro x
    obtain ⟨e, he, hee⟩ : ∃ e : Fin d ⊕ Fin e → ℤ, (∀ k, |e k| ≤ 1) ∧
        cond p.2 (if p.1 = 0 then f else g) ((if p.1 = 0 then f else g)⁻¹) x
          = x + ∑ k, (e k : ℝ) * Sum.elim lam mu k := by
      obtain ⟨i, b⟩ := p
      cases b
      · simpa using latticeDisp_gen_inv hfb hgb hf hg i x
      · simpa using latticeDisp_gen hfb hgb hf hg i x
    obtain ⟨c, hc, hcx⟩ := ih (cond p.2 (if p.1 = 0 then f else g) ((if p.1 = 0 then f else g)⁻¹) x)
    refine ⟨fun k => c k + e k, ?_, ?_⟩
    · intro k
      have h1 := hc k
      have h2 := he k
      have h3 : |c k + e k| ≤ |c k| + |e k| := abs_add_le _ _
      have hL : (L.length : ℤ) + 1 = ((L ++ [p]).length : ℤ) := by simp
      linarith
    · have hsum : (∑ k, ((c k + e k : ℤ) : ℝ) * Sum.elim lam mu k)
          = (∑ k, (c k : ℝ) * Sum.elim lam mu k)
            + ∑ k, (e k : ℝ) * Sum.elim lam mu k := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by push_cast; ring
      have hstep : (List.prod ((L ++ [p]).map fun q : Fin 2 × Bool =>
            cond q.2 (if q.1 = 0 then f else g) ((if q.1 = 0 then f else g)⁻¹)) x)
          = List.prod (L.map fun q : Fin 2 × Bool =>
              cond q.2 (if q.1 = 0 then f else g) ((if q.1 = 0 then f else g)⁻¹))
            (cond p.2 (if p.1 = 0 then f else g) ((if p.1 = 0 then f else g)⁻¹) x) := by
        simp [List.map_append, Equiv.Perm.mul_apply]
      rw [hstep, hcx, hee, hsum]
      ring

end aux

/-- **The translation-vector bound.** For generators whose displacements are lattice vectors with
coefficients in `{-1, 0, 1}`, the displacement of any word of length `n` is a lattice vector with
coefficients bounded by `n`. -/
theorem exists_lattice_displacement {d e : ℕ} (lam : Fin d → ℝ) (mu : Fin e → ℝ)
    (f g : Equiv.Perm ℝ)
    (Df : ℝ → Fin d → ℤ) (Dg : ℝ → Fin e → ℤ)
    (hf : ∀ y, f y = y + ∑ i, (Df y i : ℝ) * lam i) (hfb : ∀ y i, |Df y i| ≤ 1)
    (hg : ∀ y, g y = y + ∑ j, (Dg y j : ℝ) * mu j) (hgb : ∀ y j, |Dg y j| ≤ 1)
    (w : FreeGroup (Fin 2)) (x : ℝ) :
    ∃ a : Fin d → ℤ, ∃ b : Fin e → ℤ,
      (∀ i, |a i| ≤ ((FreeGroup.toWord w).length : ℤ)) ∧
        (∀ j, |b j| ≤ ((FreeGroup.toWord w).length : ℤ)) ∧
        FreeGroup.lift (fun i : Fin 2 => if i = 0 then f else g) w x
          = x + (∑ i, (a i : ℝ) * lam i) + (∑ j, (b j : ℝ) * mu j) := by
  classical
  obtain ⟨c, hc, hcx⟩ := latticeDisp_list hfb hgb hf hg w.toWord x
  refine ⟨fun i => c (Sum.inl i), fun j => c (Sum.inr j), ?_, ?_, ?_⟩
  · intro i; exact hc (Sum.inl i)
  · intro j; exact hc (Sum.inr j)
  · have hlift : FreeGroup.lift (fun i : Fin 2 => if i = 0 then f else g) w
        = List.prod (w.toWord.map fun p : Fin 2 × Bool =>
            cond p.2 (if p.1 = 0 then f else g) ((if p.1 = 0 then f else g)⁻¹)) := by
      conv_lhs => rw [← FreeGroup.mk_toWord (x := w)]
      rfl
    rw [hlift, hcx, Fintype.sum_sum_type]
    simp
    ring
/-! ## Instantiation for the exchanges `mkIET1 lam π` and `mkIET1 mu σ` -/

/-- The coefficient vector of the displacement of `mkIETFun lam π a` at `y`, extended by `0` off the
interval. -/
noncomputable def dispCoeff {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n)) (a y :
  ℝ) :
    Fin n → ℤ :=
  if hy : y ∈ Set.Ico a (a + ∑ i, (lam i : ℝ)) then translationCoeff π (idx lam (y - a) (by linarith
    [hy.1])) else 0

theorem dispCoeff_abs_le_one {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a y : ℝ) (i : Fin n) : |dispCoeff lam π a y i| ≤ 1 := by
  classical
  unfold dispCoeff
  split_ifs
  · exact abs_translationCoeff_le_one π _ i
  · simp

theorem mkIETFun_sub_eq_sum_dispCoeff {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin n)) (a y : ℝ) :
    mkIETFun lam π a y - y = ∑ i, (dispCoeff lam π a y i : ℝ) * (lam i : ℝ) := by
  classical
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
  change |(if j < i then (1 : ℤ) else 0)| ≤ 1
  split_ifs <;> simp
