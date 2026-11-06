/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.CylinderVolume
public import IETFree.RauzyVeech.Nesting

/-!
# Column sums and volumes of path cylinders

Column sums of a matrix multiplied by an elementary matrix (`colsum_mul_single`,
`colsum_append_singleton`, `colsum_append`), monotonicity of the column sums along an extension
(`colsum_le_colsum_append`), and the volume identities for path cylinders: disjointness of two
sibling cylinders and of incomparable prefixes (`disjoint_simplexCyl_cons_cons`,
`disjoint_simplexCyl_of_not_isPrefix`), the antichain formula `volume_iUnion_antichain`, and
multiplicativity of the volume along extensions (`volume_append_mul`, `volume_simplexCyl_lt_top`).
These are the `BalancedCylinders` facts of the volume computation. -/

open MeasureTheory Matrix IETDatum₂
open scoped BigOperators ENNReal NNReal

@[expose] public section

namespace BalancedCylinders

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Column sums of `Path.Q`  Write `cs γ b = ∑ a, Path.Q P γ a b` for the `b`-th column sum of
the path matrix.  The step `Path.Q P (γ ++ [e]) = Path.Q P γ * V` with `V = 1 + E_{a,b'}` (`a = last
e`, `b' = last !e`) multiplies the column sums on the right by `V`, hence adds the `a`-th column sum
to the `b'`-th one and leaves the others alone.  In particular they are non-decreasing, which is
what makes the balance inequalities of Lemma 5 monotone in the path. -/

/-- Column sums on the right by an elementary matrix `single i j c`: only the `j`-th column
sum changes, and it is multiplied by `c`. -/
theorem colsum_mul_single {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    (i j : ι) (c : ℤ) (b : ι) :
    (∑ a, (M * Matrix.single i j c) a b) = if b = j then (∑ a, M a i) * c else 0 := by
  have h1 (a) : (M * Matrix.single i j c) a b = if b = j then M a i * c else 0 := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · by_cases hb : b = j
      · rw [ite_eq_left hb, Matrix.single_apply, ite_eq_left ⟨rfl, hb.symm⟩]
      · rw [ite_eq_right hb, Matrix.single_apply,
          ite_eq_right (fun h : i = i ∧ j = b => hb h.2.symm), mul_zero]
    · intro k _ hk
      rw [Matrix.single_apply, ite_eq_right, mul_zero]
      rintro ⟨rfl, -⟩
      exact hk rfl
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  by_cases hb : b = j
  · rw [ite_eq_left hb]
    simp only [ite_eq_left hb, Finset.sum_mul]
  · simp only [ite_eq_right hb, Finset.sum_const_zero]

/-- **The one-step formula for the column sums.**  A step of type `e` adds the column sum of the
name `last e` to the column sum of the secondary name `last !e`, at the current vertex. -/
theorem colsum_append_singleton (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) (e : Bool) (b : α) :
    (∑ a, Path.Q P (γ ++ [e]) a b) =
      (∑ a, Path.Q P γ a b) +
        (if b = (vertex P γ).last (!e) then (∑ a, Path.Q P γ a ((vertex P γ).last e))
          else 0) := by
  have hne : (vertex P γ).last e ≠ (vertex P γ).last (!e) := vertex_last_ne_not P hP hn γ e
  rw [Path.Q_append, Path.Q_singleton, rvMat_eq_one_add_single _ e hne,
    Matrix.mul_add, Matrix.mul_one]
  simp only [Matrix.add_apply, Finset.sum_add_distrib]
  congr 1
  simpa using colsum_mul_single (Path.Q P γ) ((vertex P γ).last e) ((vertex P γ).last (!e)) 1 b

/-- **The column-sum recursion along a path**: the column sums of `γ ++ δ` are the column sums of
`γ` applied to `Q(δ)` read at the vertex reached after `γ`. -/
theorem colsum_append (P : IETDatum₂ α n) (γ δ : List Bool) (b : α) :
    (∑ a, Path.Q P (γ ++ δ) a b) =
      ∑ c, (∑ a, Path.Q P γ a c) * Path.Q (vertex P γ) δ c b := by
  rw [Path.Q_append]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => (Finset.sum_mul _ _ _).symm

/-- The diagonal entries of a path matrix are at least `1`. -/
theorem one_le_diag_Path.Q (P : IETDatum₂ α n) (γ : List Bool) (a : α) :
    1 ≤ Path.Q P γ a a := by
  induction γ generalizing P with
  | nil =>
    rw [Path.Q_nil, Matrix.one_apply, ite_eq_left rfl]
  | cons e es ih =>
    rw [Path.Q_cons, Matrix.mul_apply]
    refine le_trans ?_
      (Finset.single_le_sum
        (f := fun k => P.rvMat e a k * Path.Q (P.rvStep e) es k a)
        (fun k _ => mul_nonneg (rvMat_nonneg P e a k) (Path.Q_nonneg (P.rvStep e) es k a))
        (Finset.mem_univ a))
    have h1 : P.rvMat e a a = 1 := by
      rw [rvMat, ite_eq_left rfl]
    rw [h1, one_mul]
    exact ih (P.rvStep e)

/-- Column sums are non-decreasing along an arbitrary extension. -/
theorem colsum_le_colsum_append (P : IETDatum₂ α n) (γ δ : List Bool) (b : α) :
    (∑ a, Path.Q P γ a b) ≤ (∑ a, Path.Q P (γ ++ δ) a b) := by
  rw [colsum_append]
  refine le_trans ?_
    (Finset.single_le_sum
      (f := fun c => (∑ a, Path.Q P γ a c) * Path.Q (vertex P γ) δ c b)
      (fun c _ => mul_nonneg (le_of_lt (Path.Q_colsum_pos P γ c))
        (Path.Q_nonneg (vertex P γ) δ c b))
      (Finset.mem_univ b))
  have h1 : (1 : ℤ) ≤ Path.Q (vertex P γ) δ b b := one_le_diag_Path.Q (vertex P γ) δ b
  calc (∑ a, Path.Q P γ a b) = (∑ a, Path.Q P γ a b) * 1 := (mul_one _).symm
    _ ≤ (∑ a, Path.Q P γ a b) * Path.Q (vertex P γ) δ b b :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt (Path.Q_colsum_pos P γ b))

/-! ## 2. The laminar structure of the path cylinders  Every `Δ(γ ++ δ)` is contained in `Δ(γ)`.
Two extensions either are comparable (hence nested) or give disjoint cylinders; so a finite set of
words no one of which is a strict prefix of another ("antichain") gives pairwise disjoint cylinders,
and the volume of their union is the sum of the volumes. -/

/-- Nesting for an arbitrary extension. -/
theorem simplexCyl_append_prefix (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ δ : List Bool) : simplexCyl P (γ ++ δ) ⊆ simplexCyl P γ := by
  induction δ generalizing γ with
  | nil => simp
  | cons e es ih =>
    have h1 : γ ++ e :: es = (γ ++ [e]) ++ es := by simp
    rw [h1]
    exact Set.Subset.trans (ih (γ ++ [e])) (simplexCyl_append_subset P hP hn γ e)

/-- Two extensions whose first letters differ give disjoint cylinders. -/
theorem disjoint_simplexCyl_cons_cons (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {γ : List Bool} {a a' : Bool} (h : a ≠ a') (δ δ' : List Bool) :
    Disjoint (simplexCyl P (γ ++ a :: δ)) (simplexCyl P (γ ++ a' :: δ')) := by
  have ha' : a' = !a := by cases a <;> cases a' <;> simp_all
  have h1 : simplexCyl P (γ ++ a :: δ) ⊆ simplexCyl P (γ ++ [a]) := by
    have h2 : γ ++ a :: δ = (γ ++ [a]) ++ δ := by simp
    rw [h2]
    exact simplexCyl_append_prefix P hP hn (γ ++ [a]) δ
  have h2 : simplexCyl P (γ ++ a' :: δ') ⊆ simplexCyl P (γ ++ [!a]) := by
    have h3 : γ ++ a' :: δ' = (γ ++ [a']) ++ δ' := by simp
    rw [h3, ha']
    exact simplexCyl_append_prefix P hP hn (γ ++ [!a]) δ'
  refine Disjoint.mono h1 h2 ?_
  cases a with
  | true => simpa using disjoint_simplexCyl_true_false P hP hn γ
  | false => simpa using (disjoint_simplexCyl_true_false P hP hn γ).symm

/-- **Laminarity**: two extensions of a common word whose cylinders meet are prefix-comparable. -/
theorem isPrefix_or_isPrefix_of_mem_inter (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∀ (δ : List Bool) (γ δ' : List Bool) (x : α → ℝ≥0),
      x ∈ simplexCyl P (γ ++ δ) → x ∈ simplexCyl P (γ ++ δ') → δ <+: δ' ∨ δ' <+: δ := by
  intro δ
  induction δ with
  | nil => intro γ δ' x _ _; exact Or.inl List.nil_prefix
  | cons a δ₁ ih =>
    intro γ δ' x hx hy
    cases δ' with
    | nil => exact Or.inr List.nil_prefix
    | cons a' δ₁' =>
      by_cases ha : a = a'
      · subst ha
        have hx' : x ∈ simplexCyl P ((γ ++ [a]) ++ δ₁) := by
          rw [List.append_assoc, List.singleton_append]; exact hx
        have hy' : x ∈ simplexCyl P ((γ ++ [a]) ++ δ₁') := by
          rw [List.append_assoc, List.singleton_append]; exact hy
        rcases ih (γ ++ [a]) δ₁' x hx' hy' with h | h
        · exact Or.inl (by obtain ⟨t, ht⟩ := h; exact ⟨t, by rw [List.cons_append, ht]⟩)
        · exact Or.inr (by obtain ⟨t, ht⟩ := h; exact ⟨t, by rw [List.cons_append, ht]⟩)
      · exfalso
        exact Set.disjoint_left.mp (disjoint_simplexCyl_cons_cons P hP hn ha δ₁ δ₁') hx hy

/-- An antichain for the prefix order gives pairwise disjoint cylinders. -/
theorem disjoint_simplexCyl_of_not_isPrefix (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {γ δ δ' : List Bool} (h : ¬ δ <+: δ') (h' : ¬ δ' <+: δ) :
    Disjoint (simplexCyl P (γ ++ δ)) (simplexCyl P (γ ++ δ')) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases isPrefix_or_isPrefix_of_mem_inter P hP hn δ γ δ' x hx hy with h1 | h1
  exacts [h h1, h' h1]

/-- **Additivity over a finite antichain**. -/
theorem volume_iUnion_antichain (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) (s : Finset (List Bool))
    (hanti : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬ u <+: v) :
    simplexVolumeOn α (⋃ u ∈ s, simplexCyl P (γ ++ u))
      = ∑ u ∈ s, simplexVolumeOn α (simplexCyl P (γ ++ u)) := by
  rw [measure_biUnion_finset]
  · intro u hu v hv huv
    exact disjoint_simplexCyl_of_not_isPrefix P hP hn (hanti u hu v hv huv)
      (hanti v hv u hu (Ne.symm huv))
  · intro u _; exact measurableSet_simplexCyl P hP hn _

/-! ## 3. The volume of a child cylinder relative to a parent  `volume_simplexCyl` (Lemma 1 of the
source) computes both volumes up to the same constant `vol Δ`; the ratio is therefore the ratio of
the products of the inverse column sums.  Since the column sums do not decrease along an extension
(§1), the ratio is at most `1`. -/

/-- **The volume ratio of an extension.** -/
theorem volume_append_mul (P : IETDatum₂ α n) (γ δ : List Bool) :
    simplexVolumeOn α (simplexCyl P (γ ++ δ)) =
      (∏ b, (colsumNN (Path.Q P γ) b) * (colsumNN (Path.Q P (γ ++ δ)) b)⁻¹) *
        simplexVolumeOn α (simplexCyl P γ) := by
  have ha0 (b) : colsumNN (Path.Q P γ) b ≠ 0 := ne_of_gt (colsumNN_pos P γ b)
  have hkey : (∏ b, (colsumNN (Path.Q P γ) b) * (colsumNN (Path.Q P (γ ++ δ)) b)⁻¹) *
      (∏ b, (colsumNN (Path.Q P γ) b)⁻¹) = ∏ b, (colsumNN (Path.Q P (γ ++ δ)) b)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [mul_assoc, mul_comm ((colsumNN (Path.Q P (γ ++ δ)) b)⁻¹), ← mul_assoc,
      mul_inv_cancel₀ (ha0 b), one_mul]
  rw [volume_simplexCyl (P := P) (γ := γ ++ δ), volume_simplexCyl (P := P) (γ := γ),
    ← mul_assoc, ← ENNReal.coe_mul, hkey]

/-! ## 4. The mass of the simplex, and finite selection from a laminar family -/

/-- The open region of free coordinates is bounded, hence of finite Lebesgue measure. -/
theorem volume_region_lt_top (m : ℕ) : volume (region m) < ⊤ := by
  have hsub : region m ⊆ Set.pi Set.univ (fun _ : Fin m => Set.Icc (0 : ℝ) 1) := by
    intro v hv
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc]
    intro i
    refine ⟨le_of_lt (hv.1 i), ?_⟩
    have h1 : v i ≤ ∑ j, v j :=
      Finset.single_le_sum (f := v) (fun j _ => le_of_lt (hv.1 j)) (Finset.mem_univ i)
    linarith [h1, hv.2]
  refine lt_of_le_of_lt (measure_mono hsub) ?_
  exact IsCompact.measure_lt_top (isCompact_univ_pi fun _ => isCompact_Icc)

omit [DecidableEq α] in
/-- The `simplexVolumeOn`-mass of the whole simplex, as a Lebesgue volume. -/
theorem simplexVolumeOn_simplexOn (P : IETDatum₂ α n) :
    simplexVolumeOn α (simplexOn α) = volume (region (n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
  have hpre : (fun l : Fin (m + 1) → ℝ≥0 => fun a => l (P.piBottom a)) ⁻¹' (simplexOn α)
      = simplexOn (Fin (m + 1)) := by
    ext l
    simp only [Set.mem_preimage, mem_simplexOn]
    rw [Equiv.sum_comp P.piBottom l]
  have hmeas : MeasurableSet (simplexOn α) := by
    have h3 : simplexOn α = {x : α → ℝ≥0 | ∑ a, x a = 1} := rfl
    rw [h3]
    exact (isClosed_eq (continuous_finsetSum _ fun a _ => continuous_apply a)
      continuous_const).measurableSet
  rw [simplexVolumeOn_eq_map P,
    Measure.map_apply (measurable_pi_iff.mpr fun a => measurable_pi_apply (P.piBottom a)) hmeas,
    hpre, simplexVolume_simplexOn m]
  simp

/-- Every path cylinder has finite volume. -/
theorem volume_simplexCyl_lt_top (P : IETDatum₂ α n) (γ : List Bool) :
    simplexVolumeOn α (simplexCyl P γ) < ⊤ := by
  have hsub : simplexCyl P γ ⊆ simplexOn α := fun x hx => hx.2
  refine lt_of_le_of_lt (measure_mono hsub) ?_
  rw [simplexVolumeOn_simplexOn P]
  exact volume_region_lt_top _

end BalancedCylinders

end
