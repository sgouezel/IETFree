/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.Affine
public import IETFree.RauzyVeech.Path

/-!
# Nesting and partition of the path cylinders

For irreducible combinatorial data with `2 ≤ n` (the hypothesis is necessary, see below) and a
finite word `γ`, writing `Δ(γ) = simplexCyl P γ`:

* **Section 1–2 (algebra).** `cone (A * B) = qApply A '' cone B` for *every* pair of integer
  matrices, and `cone (rvMat ε) = {w | w > 0, w (last !ε) < w (last ε)}` (with
  `last ε ≠ last (!ε)`): the step cone is exactly the open half-space where the `α_ε` length
  exceeds the `α_{1-ε}` one, with the positivity included.
* **Section 3 (nesting, exact as sets).**
  `mem_simplexCyl_append_iff`: `x ∈ Δ(γ ++ [e]) ↔ x ∈ Δ(γ)` and the renormalised vector `w` of `x`
  at the vertex `vertex P γ` satisfies `w (last !e) < w (last e)`.  In particular
  `Δ(γ ++ [e]) ⊆ Δ(γ)`; no a.e. is involved.
* **Section 4 (uniqueness).** `Path.Q P γ` acts injectively on real vectors (`Path.Qinv` is an
  explicit left and right inverse), so `w` above is *unique* (`IsRenorm.unique`); this is what makes
  "the type of `x`" well defined.
* **Sections 5–6 (disjointness, partition, type).** `Δ(γ0) ∩ Δ(γ1) = ∅`,
  `Δ(γ) = Δ(γ0) ∪ Δ(γ1) ∪ cylStop` (exact, `simplexCyl_eq_union`), where `cylStop` is the set
  where `w (last true) = w (last false)` — the stopping set of the algorithm; and on `Δ(γ)` the
  child `Δ(γ ++ [true])` is exactly the set where the step is of type `true`.
* **Sections 7–9 (nullity).** `simplexVolumeOn α (cylStop P γ) = 0`: the stopping set lies in the
  trace on the simplex of a linear hyperplane (`Qinv`-image of the functional `w ↦ w (last true) - w
  (last false)`), whose chart equation has a nonzero linear part, or else is empty.
* **Section 10 (measurability, additivity).** `Δ(γ)` is Borel (`isOpen_cone`: a path cone is open)
  and `simplexVolumeOn α Δ(γ) = simplexVolumeOn α Δ(γ0) + simplexVolumeOn α Δ(γ1)`.
* **Section 11.** Capstone: the literal form
  `simplexVolumeOn α (Δ(γ) \ (Δ(γ0) ∪ Δ(γ1))) = 0` of hypothesis (H1).

`2 ≤ n` is required and not a convenience: for `n = 1` (one letter) `rvMat` is the identity, every
`Δ(γ)` is the whole open simplex, the two children coincide, and `cylStop` is the whole simplex, so
both disjointness and nullity fail. -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal
open IntervalExchange.RauzyVeech

namespace IntervalExchange

namespace IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

end IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. The real vector space action of an integer matrix -/

/-- The real matrix associated with an integer matrix. -/
noncomputable def qMat (Q : Matrix α α ℤ) : Matrix α α ℝ := Q.map (Int.castRingHom ℝ)

/-- `Q` acting on real vectors: `y ↦ Q y`.  This is the action appearing in `cone Q`. -/
noncomputable def qApply (Q : Matrix α α ℤ) (y : α → ℝ) : α → ℝ := (qMat Q).mulVec y

omit [DecidableEq α] in
theorem qApply_apply (Q : Matrix α α ℤ) (y : α → ℝ) (a : α) :
    qApply Q y a = ∑ b, (Q a b : ℝ) * y b := by
  simp only [qApply, qMat, Matrix.mulVec_apply_eq_sum, Matrix.map_apply, Int.coe_castRingHom]

omit [DecidableEq α] in
theorem qApply_eq (Q : Matrix α α ℤ) (y : α → ℝ) :
    qApply Q y = fun a => ∑ b, (Q a b : ℝ) * y b := by
  funext a
  exact qApply_apply Q y a

omit [DecidableEq α] in
/-- The action of a product is the composition of the actions. -/
theorem qApply_mul (A B : Matrix α α ℤ) (y : α → ℝ) :
    qApply (A * B) y = qApply A (qApply B y) := by
  simp only [qApply, qMat, Matrix.map_mul, Matrix.mulVec_mulVec]

omit [DecidableEq α] in
/-- The formal definition of `cone Q`, with the action written as `qApply`. -/
theorem cone_eq (Q : Matrix α α ℤ) :
    cone Q = {x : α → ℝ | ∃ y : α → ℝ, (∀ a, 0 < y a) ∧ x = qApply Q y} := by
  ext x
  simp only [cone, qApply_eq]

omit [DecidableEq α] in
/-- **The cone of a product is the image of the cone of the second factor.**  Nothing is
assumed on the matrices: this is the associativity of matrix-vector multiplication. -/
theorem cone_mul (A B : Matrix α α ℤ) :
    cone (A * B) = qApply A '' cone B := by
  rw [cone_eq (A * B), cone_eq B]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨qApply B y, ⟨y, hy, rfl⟩, (qApply_mul A B y).symm⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, (qApply_mul A B y).symm⟩

namespace IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 2. The cone of a single step -/

/-- The action of `rvMat ε`: it adds the `α_{1-ε}` coordinate to the `α_ε` coordinate. -/
theorem qApply_rvMat (P : IETDatum₂ α n) (ε : Bool) (hne : P.last ε ≠ P.last (!ε))
    (y : α → ℝ) :
    qApply (P.rvMat ε) y = fun a => y a + (if a = P.last ε then y (P.last (!ε)) else 0) := by
  funext a
  rw [qApply_apply]
  have hstep (b) : (P.rvMat ε a b : ℝ) * y b =
  ((if b = a then (1 : ℝ) else 0) +
    (if a = P.last ε ∧ b = P.last (!ε) then (1 : ℝ) else 0)) * y b := by
    rw [rvMat_cast P ε a b hne]
  rw [Finset.sum_congr rfl (fun b _ => hstep b),
    sum_add_single_mul (P.last ε) (P.last (!ε)) 1 y a, one_mul]

/-- Pointwise form of `qApply_rvMat`. -/
theorem qApply_rvMat_apply (P : IETDatum₂ α n) (ε : Bool) (hne : P.last ε ≠ P.last (!ε))
    (y : α → ℝ) (a : α) :
    qApply (P.rvMat ε) y a = y a + (if a = P.last ε then y (P.last (!ε)) else 0) :=
  congrFun (qApply_rvMat P ε hne y) a

/-- **The cone of a step**: `C(ε) = V_ε (ℝ^*_+)^A` is the open half-space where the
`α_ε` length exceeds the `α_{1-ε}` one, with the positivity included. -/
theorem cone_rvMat (P : IETDatum₂ α n) (ε : Bool) (hne : P.last ε ≠ P.last (!ε)) :
    cone (P.rvMat ε) =
      {w : α → ℝ | (∀ a, 0 < w a) ∧ w (P.last (!ε)) < w (P.last ε)} := by
  rw [cone_eq]
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 : qApply (P.rvMat ε) y (P.last (!ε)) = y (P.last (!ε)) := by
      rw [qApply_rvMat_apply P ε hne]
      simp [Ne.symm hne]
    have h2 : qApply (P.rvMat ε) y (P.last ε) =
        y (P.last ε) + y (P.last (!ε)) := by
      rw [qApply_rvMat_apply P ε hne]
      simp
    refine ⟨fun a => ?_, ?_⟩
    · rw [qApply_rvMat_apply P ε hne]
      by_cases ha : a = P.last ε
      · rw [ha, ite_eq_left rfl]
        have h1' := hy (P.last ε)
        have h2' := hy (P.last (!ε))
        linarith
      · rw [ite_eq_right ha]
        have h1' := hy a
        linarith
    · rw [h1, h2]
      have := hy (P.last ε)
      linarith
  · rintro ⟨hw, hlt⟩
    have hne' : P.last (!ε) ≠ P.last ε := Ne.symm hne
    refine ⟨fun a => if a = P.last ε then w a - w (P.last (!ε)) else w a, ?_, ?_⟩
    · intro a
      simp only []
      by_cases ha : a = P.last ε
      · rw [ha, ite_eq_left rfl]
        have h1' := hw (P.last ε)
        linarith
      · rw [ite_eq_right ha]
        exact hw a
    · funext a
      rw [qApply_rvMat_apply P ε hne]
      by_cases ha : a = P.last ε
      · rw [ha]
        simp only [hne', ite_eq_right, not_false_eq_true, ite_true]
        ring
      · rw [ite_eq_right ha]
        simp only [ite_eq_right ha, add_zero]

/-! ## 3. Renormalised length vectors and the two descriptions of `simplexCyl` -/

/-- `w` is a renormalised length vector of `x` along the path `γ`: it is positive and
`x = Q(γ) w` (as real vectors).  This is Yoccoz's `λ^{(n)}`. -/
def IsRenorm (P : IETDatum₂ α n) (γ : List Bool) (x : α → ℝ≥0) (w : α → ℝ) : Prop :=
  (∀ a, 0 < w a) ∧ (fun a => (x a : ℝ)) = qApply (Path.Q P γ) w

theorem isRenorm_iff (P : IETDatum₂ α n) (γ : List Bool) (x : α → ℝ≥0) (w : α → ℝ) :
    IsRenorm P γ x w ↔ (∀ a, 0 < w a) ∧ (fun a => (x a : ℝ)) = qApply (Path.Q P γ) w :=
  Iff.rfl

/-- Membership in a path cylinder: a point of the simplex whose real length vector lies in the
cone `C(γ)`, i.e. which has a positive renormalised vector. -/
theorem mem_simplexCyl_iff (P : IETDatum₂ α n) (γ : List Bool) (x : α → ℝ≥0) :
    x ∈ simplexCyl P γ ↔ x ∈ simplex α ∧ ∃ w : α → ℝ, IsRenorm P γ x w := by
  rw [simplexCyl]
  constructor
  · rintro ⟨h1, h2⟩
    rw [cone_eq] at h1
    exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩
    rw [cone_eq]
    exact ⟨h1, h2⟩

/-- The cone of `Q(γ ++ [e])` is the image under `Q(γ)` of the cone of the step. -/
theorem cone_Q_append (P : IETDatum₂ α n) (γ : List Bool) (e : Bool) :
    cone (Path.Q P (γ ++ [e])) = qApply (Path.Q P γ) '' cone ((vertex P γ).rvMat e) := by
  rw [Path.Q_append, Path.Q_singleton]
  exact cone_mul (Path.Q P γ) ((vertex P γ).rvMat e)

omit [DecidableEq α] in
/-- The two last letters of an irreducible alphabet of size `≥ 2` differ, at any vertex. -/
theorem last_ne_last_not (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) (e : Bool) :
    P.last e ≠ P.last (!e) := by
  cases e
  · exact fun h => last_true_ne_last_false P hP hn h.symm
  · exact last_true_ne_last_false P hP hn

omit [DecidableEq α] in
theorem vertex_last_ne_not (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) (e : Bool) :
    (vertex P γ).last e ≠ (vertex P γ).last (!e) :=
  last_ne_last_not (vertex P γ) (vertex_irreducible P γ hP) hn e

/-- **The step cuts out one side of the vertex**: the cylinder of `γ ++ [e]` is the set of points
of the cylinder of `γ` whose renormalised length vector `w` at the vertex `vertex P γ` satisfies
`w (last (!e)) < w (last e)`.  Both inclusions are exact set identities (no a.e. here). -/
theorem mem_simplexCyl_append_iff (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) (e : Bool) (x : α → ℝ≥0) :
    x ∈ simplexCyl P (γ ++ [e]) ↔ x ∈ simplexCyl P γ ∧ ∃ w : α → ℝ,
      IsRenorm P γ x w ∧ w ((vertex P γ).last (!e)) < w ((vertex P γ).last e) := by
  have hne := vertex_last_ne_not P hP hn γ e
  have hcone := cone_Q_append P γ e
  have hV := cone_rvMat (vertex P γ) e hne
  have hxin : (fun a => (x a : ℝ)) ∈ cone (Path.Q P (γ ++ [e])) ↔
      ∃ w : α → ℝ, w ∈ cone ((vertex P γ).rvMat e) ∧
        qApply (Path.Q P γ) w = fun a => (x a : ℝ) := by
    rw [hcone, Set.mem_image]
  rw [mem_simplexCyl_iff (P := P) (γ := γ ++ [e]) x, mem_simplexCyl_iff (P := P) (γ := γ) x]
  simp only [IsRenorm, and_assoc]
  constructor
  · rintro ⟨hsim, w, hw, hwx⟩
    have hmem : (fun a => (x a : ℝ)) ∈ cone (Path.Q P (γ ++ [e])) := ⟨w, hw, hwx⟩
    rw [hxin] at hmem
    obtain ⟨v, hv, hvx⟩ := hmem
    rw [hV] at hv
    exact ⟨hsim, ⟨v, hv.1, hvx.symm⟩, v, hv.1, hvx.symm, hv.2⟩
  · rintro ⟨hsim, ⟨v, hv, hvx⟩, w, hw, hwx, hlt⟩
    refine ⟨hsim, ?_⟩
    have hmem : (fun a => (x a : ℝ)) ∈ cone (Path.Q P (γ ++ [e])) := by
      rw [hxin]
      exact ⟨w, by rw [hV]; exact ⟨hw, hlt⟩, hwx.symm⟩
    rw [cone_eq] at hmem
    exact hmem

/-- Nesting: a child cylinder is contained in its parent. -/
theorem simplexCyl_append_subset (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) (e : Bool) :
    simplexCyl P (γ ++ [e]) ⊆ simplexCyl P γ := by
  intro x hx
  exact ((mem_simplexCyl_append_iff P hP hn γ e x).mp hx).1

/-- Nesting for an arbitrary extension: a cylinder is contained in the cylinder of any prefix of
its word. -/
theorem simplexCyl_append_prefix (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ δ : List Bool) : simplexCyl P (γ ++ δ) ⊆ simplexCyl P γ := by
  induction δ generalizing γ with
  | nil => simp
  | cons e es ih =>
    have h1 : γ ++ e :: es = (γ ++ [e]) ++ es := by simp
    rw [h1]
    exact Set.Subset.trans (ih (γ ++ [e])) (simplexCyl_append_subset P hP hn γ e)

/-! ## 4. Injectivity of the renormalisation map -/

/-- The action of an elementary matrix `V_ε` is injective (its inverse subtracts the
`α_{1-ε}` coordinate from the `α_ε` one). -/
theorem injective_qApply_rvMat (P : IETDatum₂ α n) (ε : Bool) (hne : P.last ε ≠ P.last (!ε)) :
    Function.Injective (qApply (P.rvMat ε)) := by
  intro y₁ y₂ h
  have hsec : y₁ (P.last (!ε)) = y₂ (P.last (!ε)) := by
    have h1 := congrFun h (P.last (!ε))
    rw [qApply_rvMat_apply P ε hne, qApply_rvMat_apply P ε hne] at h1
    simpa [Ne.symm hne] using h1
  funext a
  have h1 := congrFun h a
  rw [qApply_rvMat_apply P ε hne, qApply_rvMat_apply P ε hne] at h1
  by_cases ha : a = P.last ε
  · have h1' : y₁ a + y₁ (P.last (!ε)) = y₂ a + y₂ (P.last (!ε)) := by simpa [ha] using h1
    linarith
  · have h1' : y₁ a = y₂ a := by simpa [ha] using h1
    exact h1'

/-- **`Q(γ)` acts injectively on real vectors**, for irreducible data of size `≥ 2`. -/
theorem injective_qApply_Q (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) : Function.Injective (qApply (Path.Q P γ)) := by
  induction γ generalizing P with
  | nil =>
    intro y₁ y₂ h
    simpa [Path.Q_nil, qApply, qMat, Matrix.map_one, Matrix.one_mulVec] using h
  | cons e es ih =>
    have hinj1 : Function.Injective (qApply (P.rvMat e)) :=
      injective_qApply_rvMat P e (last_ne_last_not P hP hn e)
    have hinj2 : Function.Injective (qApply (Path.Q (P.rvStep e) es)) :=
      ih (P.rvStep e) (rvStep_irreducible P hP e)
    intro y₁ y₂ h
    rw [Path.Q_cons, qApply_mul, qApply_mul] at h
    exact hinj2 (hinj1 h)

/-- The renormalised vector of a point of a cylinder is unique. -/
theorem IsRenorm.unique {P : IETDatum₂ α n} {γ : List Bool} {x : α → ℝ≥0} {w w' : α → ℝ}
    (hP : P.Irreducible) (hn : 2 ≤ n) (hw : IsRenorm P γ x w) (hw' : IsRenorm P γ x w') :
    w = w' := by
  have hinj := injective_qApply_Q P hP hn γ
  exact hinj (hw.2.symm.trans hw'.2)

/-! ## 5. The partition: two disjoint children and the stopping set -/

/-- The stopping set at the vertex `vertex P γ`: the renormalised length vector gives the same
length to the two last letters, so the type of the next step is not defined and the algorithm stops.
-/
def cylStop (P : IETDatum₂ α n) (γ : List Bool) : Set (α → ℝ≥0) :=
  {x | x ∈ simplexCyl P γ ∧ ∃ w : α → ℝ, IsRenorm P γ x w ∧
    w ((vertex P γ).last true) = w ((vertex P γ).last false)}

theorem mem_cylStop_iff (P : IETDatum₂ α n) (γ : List Bool) (x : α → ℝ≥0) :
    x ∈ cylStop P γ ↔ x ∈ simplexCyl P γ ∧ ∃ w : α → ℝ, IsRenorm P γ x w ∧
      w ((vertex P γ).last true) = w ((vertex P γ).last false) :=
  Iff.rfl

/-- **The two children are disjoint.** -/
theorem disjoint_simplexCyl_true_false (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) :
    Disjoint (simplexCyl P (γ ++ [true])) (simplexCyl P (γ ++ [false])) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rw [mem_simplexCyl_append_iff P hP hn γ true x] at hx
  rw [mem_simplexCyl_append_iff P hP hn γ false x] at hy
  obtain ⟨-, w, hw, hlt⟩ := hx
  obtain ⟨-, w', hw', hlt'⟩ := hy
  have hww : w = w' := hw.unique hP hn hw'
  simp only [Bool.not_true, Bool.not_false] at hlt hlt'
  rw [hww] at hlt
  linarith

/-- **Hypothesis (H1) of the nested-cylinder lemma, as an exact partition**: the parent cylinder
is the union of the two children and the stopping set. -/
theorem simplexCyl_eq_union (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) :
    simplexCyl P γ = simplexCyl P (γ ++ [true]) ∪ simplexCyl P (γ ++ [false]) ∪ cylStop P γ := by
  have hne := vertex_last_ne P hP hn γ
  ext x
  constructor
  · intro hx
    rw [mem_simplexCyl_iff] at hx
    obtain ⟨hsim, w, hw, hwx⟩ := hx
    have hpar : x ∈ simplexCyl P γ := by rw [mem_simplexCyl_iff]; exact ⟨hsim, w, hw, hwx⟩
    rcases lt_trichotomy (w ((vertex P γ).last false)) (w ((vertex P γ).last true)) with h | h | h
    · left; left
      rw [mem_simplexCyl_append_iff P hP hn γ true x]
      refine ⟨hpar, w, ⟨hw, hwx⟩, ?_⟩
      simpa using h
    · right
      rw [mem_cylStop_iff]
      exact ⟨hpar, w, ⟨hw, hwx⟩, h.symm⟩
    · left; right
      rw [mem_simplexCyl_append_iff P hP hn γ false x]
      refine ⟨hpar, w, ⟨hw, hwx⟩, ?_⟩
      simpa using h
  · rintro ((h | h) | h)
    · exact simplexCyl_append_subset P hP hn γ true h
    · exact simplexCyl_append_subset P hP hn γ false h
    · exact h.1

/-! ## 6. The inverse of `Q(γ)` and the stopping set as a hyperplane section -/

/-- The inverse of the elementary matrix `V_ε = 1 + E`: `1 - E`. -/
def rvMatInv (P : IETDatum₂ α n) (ε : Bool) : Matrix α α ℤ :=
  fun i j => if i = j then 1 else if i = P.last ε ∧ j = P.last (!ε) then -1 else 0

end IETDatum₂

namespace IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- The action of `rvMatInv ε`: it subtracts the `α_{1-ε}` coordinate from the `α_ε` one. -/
theorem qApply_rvMatInv (P : IETDatum₂ α n) (ε : Bool) (hne : P.last ε ≠ P.last (!ε))
    (y : α → ℝ) :
    qApply (P.rvMatInv ε) y = fun a => y a - (if a = P.last ε then y (P.last (!ε)) else 0) := by
  funext a
  rw [qApply_apply]
  have hentry (b) : (P.rvMatInv ε a b : ℝ) =
          ((if b = a then (1 : ℝ) else 0) +
            (if a = P.last ε ∧ b = P.last (!ε) then (-1 : ℝ) else 0)) := by
    have hne' : P.last (!ε) ≠ P.last ε := Ne.symm hne
    by_cases hba : b = a
    · rw [hba]
      have hC : ¬ (a = P.last ε ∧ a = P.last (!ε)) := fun h => hne (h.1.symm.trans h.2)
      simp [IETDatum₂.rvMatInv, hC]
    · have h1 : ¬ (a = b) := Ne.symm hba
      by_cases hC : a = P.last ε ∧ b = P.last (!ε)
      · simp [IETDatum₂.rvMatInv, hC, hne, hne']
      · simp [IETDatum₂.rvMatInv, h1, hC, hba]
  rw [Finset.sum_congr rfl (fun b _ => by rw [hentry b]),
    sum_add_single_mul (P.last ε) (P.last (!ε)) (-1) y a]
  ring

/-- Pointwise form of `qApply_rvMatInv`. -/
theorem qApply_rvMatInv_apply (P : IETDatum₂ α n) (ε : Bool) (hne : P.last ε ≠ P.last (!ε))
    (y : α → ℝ) (a : α) :
    qApply (P.rvMatInv ε) y a = y a - (if a = P.last ε then y (P.last (!ε)) else 0) :=
  congrFun (qApply_rvMatInv P ε hne y) a

/-- The elementary matrix inverse is a left inverse for the vector action. -/
theorem qApply_rvMatInv_qApply_rvMat (P : IETDatum₂ α n) (ε : Bool)
    (hne : P.last ε ≠ P.last (!ε)) (y : α → ℝ) :
    qApply (P.rvMatInv ε) (qApply (P.rvMat ε) y) = y := by
  funext a
  rw [qApply_rvMatInv_apply P ε hne]
  by_cases ha : a = P.last ε
  · rw [ha, ite_eq_left rfl]
    have hq : qApply (P.rvMat ε) y (P.last (!ε)) = y (P.last (!ε)) := by
      rw [qApply_rvMat_apply P ε hne]
      simp [Ne.symm hne]
    have hq' : qApply (P.rvMat ε) y (P.last ε) = y (P.last ε) + y (P.last (!ε)) := by
      rw [qApply_rvMat_apply P ε hne]
      simp
    rw [hq, hq']
    ring
  · rw [ite_eq_right ha]
    have hq' : qApply (P.rvMat ε) y a = y a := by
      rw [qApply_rvMat_apply P ε hne]
      simp [ha]
    rw [hq', sub_zero]

namespace Path

/-- The inverse matrix `Q(γ)⁻¹` of a path, as the product of the inverses of the steps. -/
noncomputable def Qinv (P : IETDatum₂ α n) : List Bool → Matrix α α ℤ
  | [] => 1
  | e :: es => Qinv (P.rvStep e) es * P.rvMatInv e

/-- **`Q(γ)⁻¹` is a left inverse of `Q(γ)` on real vectors.** -/
theorem qApply_Qinv_Q (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) (γ : List Bool)
    (y : α → ℝ) : qApply (Qinv P γ) (qApply (Q P γ) y) = y := by
  induction γ generalizing P with
  | nil =>
    simp [Qinv, Q_nil, qApply, qMat, Matrix.map_one, Matrix.one_mulVec]
  | cons e es ih =>
    have hne := last_ne_last_not P hP hn e
    rw [Q_cons, Qinv, qApply_mul, qApply_mul,
      qApply_rvMatInv_qApply_rvMat P e hne]
    exact ih (P.rvStep e) (rvStep_irreducible P hP e)

end Path

end IETDatum₂

variable {k : ℕ}

/-- **A level set of a nonzero linear functional on `Fin k → ℝ` is Lebesgue-null.** -/
theorem volume_linear_eq_zero (f : (Fin k → ℝ) →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) :
    volume {v : Fin k → ℝ | f v = c} = 0 := by
  have hzero : volume {v : Fin k → ℝ | f v = 0} = 0 := by
    have h : {v : Fin k → ℝ | f v = 0} = (LinearMap.ker f : Set _) := by
      ext v
      simp
    rw [h]
    exact Measure.addHaar_submodule volume _ (by rwa [Ne, LinearMap.ker_eq_top])
  rcases eq_or_ne c 0 with rfl | hc
  · exact hzero
  · obtain ⟨v0, hv0⟩ : ∃ v0, f v0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hf (LinearMap.ext h)
    set a : Fin k → ℝ := (c / f v0) • v0 with ha
    have hset : {v : Fin k → ℝ | f v = c} =
        (fun w => w + a) '' {w : Fin k → ℝ | f w = 0} := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · intro hv
        refine ⟨v - a, ?_, by abel⟩
        simp only [map_sub, map_smul, hv, ha, smul_eq_mul]
        field_simp
        ring
      · rintro ⟨w, hw, rfl⟩
        simp only [map_add, hw, zero_add, ha, map_smul, smul_eq_mul]
        field_simp
    have himg : (fun h : Fin k → ℝ => h + a) ⁻¹'
        ((fun w => w + a) '' {w : Fin k → ℝ | f w = 0}) = {w : Fin k → ℝ | f w = 0} := by
      ext h
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨w, hw, hwe⟩
        have hwh : h = w := by simpa using hwe.symm
        rwa [hwh]
      · intro hh
        exact ⟨h, hh, rfl⟩
    have h1 : volume ((fun w : Fin k → ℝ => w + a) '' {w : Fin k → ℝ | f w = 0})
        = volume ((fun h : Fin k → ℝ => h + a) ⁻¹'
            ((fun w => w + a) '' {w : Fin k → ℝ | f w = 0})) :=
      (measure_preimage_add_right volume a _).symm
    rw [hset, h1, himg, hzero]

namespace IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 7. The stopping set is null: the hyperplane computation -/

section Null

variable {m : ℕ}

/-- The coefficient vector of the functional `x ↦ (Qinv x) (last true) - (Qinv x) (last false)`,
in the bottom order (`Fin (m+1)` indices). -/
noncomputable def Acoef (P : IETDatum₂ α (m + 1)) (γ : List Bool) : Fin (m + 1) → ℝ :=
  fun i => (Path.Qinv P γ ((P.vertex γ).last true) (P.piBottom.symm i) : ℝ) -
    (Path.Qinv P γ ((P.vertex γ).last false) (P.piBottom.symm i) : ℝ)

/-- The linear functional with coefficient vector `A`. -/
noncomputable def hallLin (A : Fin (m + 1) → ℝ) : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun w := ∑ i, A i * w i
  map_add' v w := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [RingHom.id_apply]; ring

theorem hallLin_apply (A : Fin (m + 1) → ℝ) (w : Fin (m + 1) → ℝ) :
    hallLin A w = ∑ i, A i * w i := (rfl)

/-- The linear part of `v ↦ hallLin A (chart m v)`. -/
noncomputable def glin (A : Fin (m + 1) → ℝ) : (Fin m → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ i, A i * linChart m v i
  map_add' v w := by
    simp only [linChart_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [linChart_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [RingHom.id_apply]; ring

theorem hallLin_linChart (A : Fin (m + 1) → ℝ) (v : Fin m → ℝ) :
    hallLin A (linChart m v) = glin A v := (rfl)

/-- The last coordinate vector. -/
def delta (m : ℕ) : Fin (m + 1) → ℝ := fun i => if i = Fin.last m then 1 else 0

theorem delta_apply_last : delta m (Fin.last m) = 1 := by
  simp [delta]

theorem delta_apply_castSucc (i : Fin m) : delta m i.castSucc = 0 := by
  have h : (i.castSucc : Fin (m + 1)) ≠ Fin.last m := Fin.ne_of_lt i.castSucc_lt_last
  simp [delta, h]

theorem chart_eq_linChart_add_delta (v : Fin m → ℝ) :
    chart m v = linChart m v + delta m := by
  rw [chart_eq_linChart_add]
  funext i
  simp only [Pi.add_apply]
  by_cases h : i = Fin.last m
  · subst h
    simp [delta]
  · simp [delta, h]

/-- The value of `hallLin A` on the last coordinate vector. -/
theorem hallLin_last (A : Fin (m + 1) → ℝ) : hallLin A (delta m) = A (Fin.last m) := by
  rw [hallLin_apply, Finset.sum_eq_single (Fin.last m)]
  · simp [delta]
  · intro b _ hb
    simp [delta, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The chart is affine with linear part `linChart` and constant term the last coordinate vector. -/
theorem hallLin_chart (A : Fin (m + 1) → ℝ) (v : Fin m → ℝ) :
    hallLin A (chart m v) = glin A v + A (Fin.last m) := by
  rw [chart_eq_linChart_add_delta, map_add, hallLin_last, hallLin_linChart]

/-- **Every vector is a linear-chart vector plus a multiple of the last coordinate vector.** -/
theorem eq_linChart_add_last (w : Fin (m + 1) → ℝ) :
    w = linChart m (fun j : Fin m => w j.castSucc) + (∑ i, w i) • delta m := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · rw [Pi.add_apply, Pi.smul_apply, linChart_last, delta_apply_last, smul_eq_mul, mul_one]
    have hsum := Fin.sum_univ_castSucc w
    linarith
  · intro i
    rw [Pi.add_apply, Pi.smul_apply, linChart_castSucc, delta_apply_castSucc, smul_eq_mul,
      mul_zero, add_zero]

/-- A nonzero coefficient vector gives a nonzero functional. -/
theorem hallLin_ne_zero {A : Fin (m + 1) → ℝ} (hA : A ≠ 0) : hallLin A ≠ 0 := by
  intro h
  apply hA
  funext i
  have h1 : hallLin A (fun j => if j = i then (1 : ℝ) else 0) = 0 := by rw [h]; rfl
  rw [hallLin_apply] at h1
  have h2 : ∑ j, A j * (if j = i then (1 : ℝ) else 0) = A i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hp
      exact absurd (Finset.mem_univ _) hp
  rw [h2] at h1
  exact h1

/-- **If the linear part of `v ↦ hallLin A (chart m v)` vanishes, then its constant term does not**
(for `A ≠ 0`). -/
theorem last_ne_zero_of_glin_eq_zero {A : Fin (m + 1) → ℝ} (hA : A ≠ 0)
    (hG : glin A = 0) : A (Fin.last m) ≠ 0 := by
  intro hlast
  apply hallLin_ne_zero hA
  refine LinearMap.ext fun w => ?_
  rw [eq_linChart_add_last w, map_add, map_smul, hallLin_linChart, hG, hallLin_last, hlast,
    LinearMap.zero_apply]
  simp

/-- **The set of `v` where `hallLin A (chart m v)` vanishes is Lebesgue-null**, for `A ≠ 0`. -/
theorem volume_hallLin_chart_eq_zero {A : Fin (m + 1) → ℝ} (hA : A ≠ 0) :
    volume {v : Fin m → ℝ | hallLin A (chart m v) = 0} = 0 := by
  rcases eq_or_ne (glin A) 0 with hG | hG
  · have hlast := last_ne_zero_of_glin_eq_zero hA hG
    have hempty : {v : Fin m → ℝ | hallLin A (chart m v) = 0} = ∅ := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rw [hallLin_chart, hG]
      simpa using hlast
    rw [hempty, measure_empty]
  · have hset : {v : Fin m → ℝ | hallLin A (chart m v) = 0} =
        {v : Fin m → ℝ | glin A v = -A (Fin.last m)} := by
      ext v
      simp only [Set.mem_ofPred_eq, hallLin_chart]
      constructor <;> intro h <;> linarith
    rw [hset]
    exact volume_linear_eq_zero (glin A) hG _

end Null

/-! ## 8. The stopping set is null for `simplexVolumeOn` -/

section NullVolume

variable {m : ℕ}

/-- The functional defining the stopping set, in `Fin (m+1)` coordinates, is the `Qinv`-image. -/
theorem hallLin_Acoef_eq (P : IETDatum₂ α (m + 1)) (γ : List Bool) (x : α → ℝ) :
    hallLin (Acoef P γ) (fun i => x (P.piBottom.symm i)) =
      qApply (Path.Qinv P γ) x ((P.vertex γ).last true) -
        qApply (Path.Qinv P γ) x ((P.vertex γ).last false) := by
  have h1 : hallLin (Acoef P γ) (fun i => x (P.piBottom.symm i))
      = (∑ i, ((Path.Qinv P γ ((P.vertex γ).last true) (P.piBottom.symm i) : ℝ) *
          x (P.piBottom.symm i))) -
        ∑ i, ((Path.Qinv P γ ((P.vertex γ).last false) (P.piBottom.symm i) : ℝ) *
          x (P.piBottom.symm i)) := by
    rw [hallLin_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Acoef]
      ring
  rw [h1, qApply_apply, qApply_apply,
    Equiv.sum_comp P.piBottom.symm
      (fun b => (Path.Qinv P γ ((P.vertex γ).last true) b : ℝ) * x b),
    Equiv.sum_comp P.piBottom.symm
      (fun b => (Path.Qinv P γ ((P.vertex γ).last false) b : ℝ) * x b)]

/-- The coefficient vector is nonzero (this is where `last true ≠ last false` is used). -/
theorem Acoef_ne_zero (P : IETDatum₂ α (m + 1)) (hP : P.Irreducible) (hn : 2 ≤ m + 1)
    (γ : List Bool) : Acoef P γ ≠ 0 := by
  intro hA
  have hcc : (P.vertex γ).last true ≠ (P.vertex γ).last false := vertex_last_ne P hP hn γ
  have hrow (b) : Path.Qinv P γ ((P.vertex γ).last true) b =
      Path.Qinv P γ ((P.vertex γ).last false) b := by
    have h1 := congrFun hA (P.piBottom b)
    simp only [Acoef, Pi.zero_apply, Equiv.symm_apply_apply] at h1
    have h2 : (Path.Qinv P γ ((P.vertex γ).last true) b : ℝ) =
        (Path.Qinv P γ ((P.vertex γ).last false) b : ℝ) := by linarith
    exact_mod_cast h2
  have h3 (w : α → ℝ) : w ((P.vertex γ).last true) = w ((P.vertex γ).last false) := by
    have hL := Path.qApply_Qinv_Q P hP hn γ w
    have h2 : qApply (Path.Qinv P γ) (qApply (Path.Q P γ) w) ((P.vertex γ).last true) =
        qApply (Path.Qinv P γ) (qApply (Path.Q P γ) w) ((P.vertex γ).last false) := by
      rw [qApply_apply, qApply_apply]
      exact Finset.sum_congr rfl fun b _ => by rw [hrow b]
    rwa [hL] at h2
  have h4 := h3 (fun b => if b = (P.vertex γ).last true then (1 : ℝ) else 0)
  simp [Ne.symm hcc] at h4

/-- **The stopping set is contained in the zero set of a fixed linear functional.** -/
theorem cylStop_subset_hyperplane (P : IETDatum₂ α (m + 1)) (hP : P.Irreducible)
    (hn : 2 ≤ m + 1) (γ : List Bool) :
    cylStop P γ ⊆ {x : α → ℝ≥0 |
      hallLin (Acoef P γ) (fun i => ((x (P.piBottom.symm i) : ℝ≥0) : ℝ)) = 0} := by
  rintro x ⟨-, w, ⟨hw, hwx⟩, heq⟩
  simp only [Set.mem_ofPred_eq]
  have hmain : hallLin (Acoef P γ) (fun i => ((x (P.piBottom.symm i) : ℝ≥0) : ℝ)) =
      qApply (Path.Qinv P γ) (fun a => (x a : ℝ)) ((P.vertex γ).last true) -
        qApply (Path.Qinv P γ) (fun a => (x a : ℝ)) ((P.vertex γ).last false) := by
    simpa using hallLin_Acoef_eq P γ (fun a => (x a : ℝ))
  rw [hmain]
  have h1 : qApply (Path.Qinv P γ) (fun a => (x a : ℝ)) = w := by
    rw [hwx, Path.qApply_Qinv_Q P hP hn γ w]
  rw [h1, heq]
  ring

/-- The chart map, with values in `ℝ≥0`. -/
noncomputable def gchart (P : IETDatum₂ α (m + 1)) (v : Fin m → ℝ) : α → ℝ≥0 :=
  fun a => (chart m v (P.piBottom a)).toNNReal

omit [DecidableEq α] in
theorem measurable_gchart (P : IETDatum₂ α (m + 1)) : Measurable (gchart P) := by
  refine measurable_pi_iff.mpr fun a => ?_
  exact (((continuous_apply (P.piBottom a)).comp (continuous_chart m))).measurable.real_toNNReal

omit [DecidableEq α] in
/-- **`simplexVolumeOn α` in the free coordinates**: it is the Lebesgue measure of the open
region pushed forward by the chart and the coordinatewise coercion to `ℝ≥0`. -/
theorem simplexVolumeOn_eq_map_gchart (P : IETDatum₂ α (m + 1)) :
    simplexVolumeOn α = (volume.restrict (region m)).map (gchart P) := by
  have hre : Measurable (fun l : Fin (m + 1) → ℝ≥0 => fun a => l (P.piBottom a)) :=
    measurable_pi_iff.mpr fun a => measurable_pi_apply (P.piBottom a)
  have htn : Measurable (fun x : Fin (m + 1) → ℝ => fun i => (x i).toNNReal) :=
    measurable_coord_toNNReal (m + 1)
  rw [simplexVolumeOn_eq_map P, simplexVolume_succ_eq_map_toNNReal m,
    Measure.map_map hre htn, Measure.map_map (hre.comp htn) (continuous_chart m).measurable]
  rfl

omit [DecidableEq α] in
/-- The measure of a measurable set in the free coordinates. -/
theorem simplexVolumeOn_apply_gchart (P : IETDatum₂ α (m + 1)) (S : Set (α → ℝ≥0))
    (hS : MeasurableSet S) :
    simplexVolumeOn α S = volume (gchart P ⁻¹' S ∩ region m) := by
  rw [simplexVolumeOn_eq_map_gchart P, Measure.map_apply (measurable_gchart P) hS,
    Measure.restrict_apply (hS.preimage (measurable_gchart P))]

/-- **The chart preimage of the stopping functional's zero set is Lebesgue-null.** -/
theorem volume_gchart_preimage_hyperplane (P : IETDatum₂ α (m + 1)) (γ : List Bool)
    (hA : Acoef P γ ≠ 0) :
    volume (gchart P ⁻¹'
      {x : α → ℝ≥0 | hallLin (Acoef P γ) (fun i => ((x (P.piBottom.symm i) : ℝ≥0) : ℝ)) = 0}
        ∩ region m) = 0 := by
  refine measure_mono_null ?_ (volume_hallLin_chart_eq_zero hA)
  intro v hv
  obtain ⟨hv1, hv2⟩ := hv
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hv1 ⊢
  have hg : (fun i => ((gchart P v (P.piBottom.symm i) : ℝ≥0) : ℝ)) = chart m v := by
    funext i
    simp only [gchart, Equiv.apply_symm_apply]
    exact Real.coe_toNNReal _ (le_of_lt (chart_pos hv2 i))
  rw [hg] at hv1
  exact hv1

end NullVolume

/-- **The stopping set is null** — this is the "up to a null set" half of hypothesis (H1): the two
children of a cylinder are disjoint and the complement of their union in the cylinder
carries no mass. -/
theorem simplexVolumeOn_cylStop (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) : simplexVolumeOn α (cylStop P γ) = 0 := by
  rcases n with _ | m
  · exact absurd rfl (NeZero.ne 0)
  · have hA : Acoef P γ ≠ 0 := Acoef_ne_zero P hP hn γ
    have hS : MeasurableSet {x : α → ℝ≥0 |
        hallLin (Acoef P γ) (fun i => ((x (P.piBottom.symm i) : ℝ≥0) : ℝ)) = 0} := by
      have hcont : Continuous fun x : α → ℝ≥0 =>
          hallLin (Acoef P γ) (fun i => ((x (P.piBottom.symm i) : ℝ≥0) : ℝ)) := by
        simp only [hallLin_apply]
        exact continuous_finsetSum _ fun i _ =>
          continuous_const.mul (NNReal.continuous_coe.comp (continuous_apply _))
      exact (isClosed_eq hcont continuous_const).measurableSet
    refine measure_mono_null (cylStop_subset_hyperplane P hP hn γ) ?_
    rw [simplexVolumeOn_apply_gchart P _ hS]
    exact volume_gchart_preimage_hyperplane P γ hA

/-! ## 9. Measurability of the cylinders and additivity of the measure -/

section Measurable

variable {m : ℕ}

omit [Fintype α] in
/-- The coordinatewise coercion to real vectors is continuous. -/
theorem continuous_coe_lengths (α : Type*) :
    Continuous (fun x : α → ℝ≥0 => fun a => (x a : ℝ)) :=
  continuous_pi fun a => NNReal.continuous_coe.comp (continuous_apply a)

omit [DecidableEq α] in
theorem continuous_qApply_coord (Q : Matrix α α ℤ) (a : α) :
    Continuous fun x : α → ℝ => qApply Q x a := by
  have h : (fun x : α → ℝ => qApply Q x a) = fun x => ∑ b, (Q a b : ℝ) * x b := by
    funext x
    exact qApply_apply Q x a
  rw [h]
  have hc : Continuous fun x : α → ℝ => ∑ b ∈ (Finset.univ : Finset α), (Q a b : ℝ) * x b :=
    continuous_finsetSum (Finset.univ)
      (f := fun b (x : α → ℝ) => (Q a b : ℝ) * x b)
      (fun b _ => continuous_const.mul (continuous_apply b))
  simpa using hc

/-- The right inverse of `Q(γ)` on real vectors (the mirror of `qApply_Qinv_Q`). -/
theorem qApply_rvMat_qApply_rvMatInv (P : IETDatum₂ α n) (ε : Bool)
    (hne : P.last ε ≠ P.last (!ε)) (y : α → ℝ) :
    qApply (P.rvMat ε) (qApply (P.rvMatInv ε) y) = y := by
  funext a
  rw [qApply_rvMat_apply P ε hne]
  by_cases ha : a = P.last ε
  · rw [ha, ite_eq_left rfl]
    have hq : qApply (P.rvMatInv ε) y (P.last (!ε)) = y (P.last (!ε)) := by
      rw [qApply_rvMatInv_apply P ε hne]
      simp [Ne.symm hne]
    have hq' : qApply (P.rvMatInv ε) y (P.last ε) = y (P.last ε) - y (P.last (!ε)) := by
      rw [qApply_rvMatInv_apply P ε hne]
      simp
    rw [hq, hq']
    ring
  · rw [ite_eq_right ha]
    have hq' : qApply (P.rvMatInv ε) y a = y a := by
      rw [qApply_rvMatInv_apply P ε hne]
      simp [ha]
    rw [hq', add_zero]

theorem Path.qApply_Q_Qinv (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) (y : α → ℝ) : qApply (Q P γ) (qApply (Qinv P γ) y) = y := by
  induction γ generalizing P y with
  | nil =>
    simp [Qinv, Q_nil, qApply, qMat, Matrix.map_one, Matrix.one_mulVec]
  | cons e es ih =>
    have hne := last_ne_last_not P hP hn e
    rw [Q_cons, Qinv, qApply_mul, qApply_mul]
    rw [ih (P.rvStep e) (rvStep_irreducible P hP e) (qApply (P.rvMatInv e) y)]
    exact qApply_rvMat_qApply_rvMatInv P e hne y

/-- **Membership in the cone, in terms of the inverse matrix.** -/
theorem mem_cone_iff (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) (γ : List Bool)
    (x : α → ℝ) : x ∈ cone (Path.Q P γ) ↔ ∀ a, 0 < qApply (Path.Qinv P γ) x a := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hq : (fun a => ∑ b, (Path.Q P γ a b : ℝ) * y b) = qApply (Path.Q P γ) y :=
      (qApply_eq (Path.Q P γ) y).symm
    rw [hq, Path.qApply_Qinv_Q P hP hn γ y]
    exact hy
  · intro hx
    refine ⟨qApply (Path.Qinv P γ) x, hx, ?_⟩
    rw [← qApply_eq (Path.Q P γ) (qApply (Path.Qinv P γ) x)]
    exact (Path.qApply_Q_Qinv P hP hn γ x).symm

/-- **A path cone is open.** -/
theorem isOpen_cone (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) (γ : List Bool) :
    IsOpen (cone (Path.Q P γ)) := by
  have h : cone (Path.Q P γ) = {x : α → ℝ | ∀ a, 0 < qApply (Path.Qinv P γ) x a} := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_cone_iff P hP hn γ x]
  rw [h, Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun a =>
    isOpen_lt continuous_const (continuous_qApply_coord (Path.Qinv P γ) a)

/-- **The path cylinders are Borel sets.** -/
theorem measurableSet_simplexCyl (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ : List Bool) : MeasurableSet (simplexCyl P γ) := by
  have h1 : MeasurableSet
      ((fun x : α → ℝ≥0 => fun a => (x a : ℝ)) ⁻¹' cone (Path.Q P γ)) :=
    (isOpen_cone P hP hn γ).measurableSet.preimage (continuous_coe_lengths α).measurable
  have h2 : MeasurableSet (simplex α) := by
    have h3 : simplex α = {x : α → ℝ≥0 | ∑ a, x a = 1} := (rfl)
    rw [h3]
    refine (isClosed_eq ?_ continuous_const).measurableSet
    exact continuous_finsetSum _ fun a _ => continuous_apply a
  exact h1.inter h2

end Measurable

/-! ## 10. Capstones -/

omit [DecidableEq α] in
/-- **The column sums are the total lengths**: `∑_a (Q y) a = ∑_b Q_β y_b`.  In particular, for
`x = Q(γ) λ̂` with `x ∈ simplex α` one has `∑_b Q_β λ̂_b = 1`, the normalisation of the
renormalised length vector. -/
theorem sum_qApply (Q : Matrix α α ℤ) (y : α → ℝ) :
    ∑ a, qApply Q y a = ∑ b, ((∑ a, Q a b : ℤ) : ℝ) * y b := by
  simp only [qApply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  push_cast
  rw [Finset.sum_mul]

end IETDatum₂

end IntervalExchange

end
