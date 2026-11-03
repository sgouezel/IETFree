/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.RauzyVeech.InvariantMeasure
import IETFree.RauzyVeech.TrueStep
import IETFree.RauzyVeech.MeshShrink
import IETFree.RauzyVeech.LengthInjective
import IETFree.RauzyVeech.TowerGlue
import IETFree.RauzyVeech.RauzyPath
import IETFree.RauzyVeech.IterGlue2

/-!
# Injectivity of the length map, from the tower decomposition

The length vector of an invariant probability measure determines the measure.  This file proves it
from the floors of the Rokhlin tower decomposition: the level-`k` floors of a Rauzy path have masses
that are linear functions of the length vector (`cellAt_mass_eq`, `floor_mass_eq`), they refine with
`k` (`FloorPartitionData`), and their diameters go to `0` (`length_injective_of_floors`,
`length_injective_of_tower_of_floors`), so a refining-partition argument (`LengthInjective`) forces
two measures with the same length vector to agree.  The tiling that feeds `FloorPartitionData`
almost everywhere is proved in `IETFree/RauzyVeech/TowerTiling.lean`. -/


open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators Topology

namespace TowerInjectivity

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Step 2 of the route: equal length vectors give equal level-cell masses -/

/-- **Level-cell masses are determined by the length vector.** Two invariant probability measures of
`P.toIET lam` with the same length vector give the same mass to every level-`γ` cell: the tower
formula (`TowerTrue.tower_formula_level_pathQ_any`) writes the length vector as `Q(γ)` applied to
the level-`γ` cell masses, and `Q(γ)` acts injectively on real vectors (`IETDatum₂.det_Path.Q` gives
`det Q(γ) = 1`, so `Q(γ)` is invertible over `ℤ`, and `IETDatum₂.injective_qApply_Q` is the real
form used here). -/
theorem cellAt_mass_eq (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {lam : α → ℝ≥0} (hsim : lam ∈ simplexOn α) (γ : List Bool)
    (hOK : TowerTrue.IterOK P lam γ)
    {μ ν : ProbabilityMeasure ℝ}
    (hμ : Invariant μ (P.toIET lam)) (hν : Invariant ν (P.toIET lam))
    (hlen : InvariantMeasure.lambdaOf μ P lam = InvariantMeasure.lambdaOf ν P lam) (b : α) :
    (μ : Measure ℝ) (Tower.cellAt P γ lam b)
      = (ν : Measure ℝ) (Tower.cellAt P γ lam b) := by
  have hQ : ∀ a b, 0 ≤ IETDatum₂.Path.Q P γ a b := fun a b => IETDatum₂.Path.Q_nonneg P γ a b
  have h1 : (fun a => InvariantMeasure.lambdaOf μ P lam a)
      = IETDatum₂.qApply (IETDatum₂.Path.Q P γ)
          (fun b => ((μ : Measure ℝ) (Tower.cellAt P γ lam b)).toReal) :=
    TowerGlue.real_eq_qApply P (μ : Measure ℝ) hQ (fun b => measure_ne_top _ _)
      (fun a => TowerTrue.tower_formula_level_pathQ_any P hP hn lam hsim
        (μ : Measure ℝ) hμ γ hOK a)
  have h2 : (fun a => InvariantMeasure.lambdaOf ν P lam a)
      = IETDatum₂.qApply (IETDatum₂.Path.Q P γ)
          (fun b => ((ν : Measure ℝ) (Tower.cellAt P γ lam b)).toReal) :=
    TowerGlue.real_eq_qApply P (ν : Measure ℝ) hQ (fun b => measure_ne_top _ _)
      (fun a => TowerTrue.tower_formula_level_pathQ_any P hP hn lam hsim
        (ν : Measure ℝ) hν γ hOK a)
  have hy : (fun b => ((μ : Measure ℝ) (Tower.cellAt P γ lam b)).toReal)
      = (fun b => ((ν : Measure ℝ) (Tower.cellAt P γ lam b)).toReal) :=
    IETDatum₂.injective_qApply_Q P hP hn γ (h1.symm.trans (hlen.trans h2))
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    (congrFun hy b)

/-! ## 2. Step 3 of the route: all floors of a tower have the mass of their cell -/

/-- **Floors have the mass of their cell.**  An iterate image of a level-`γ` cell has the same
`μ`-mass as the cell itself, by invariance (`Tower.measure_image_iterate`); with step 2 it has the
same mass for `μ` and for `ν`. -/
theorem floor_mass_eq (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {lam : α → ℝ≥0} (hsim : lam ∈ simplexOn α) (γ : List Bool)
    (hOK : TowerTrue.IterOK P lam γ)
    {μ ν : ProbabilityMeasure ℝ}
    (hμ : Invariant μ (P.toIET lam)) (hν : Invariant ν (P.toIET lam))
    (hlen : InvariantMeasure.lambdaOf μ P lam = InvariantMeasure.lambdaOf ν P lam)
    {b : α} {j : ℕ} :
    (μ : Measure ℝ) ((P.toIET lam)^[j] '' Tower.cellAt P γ lam b)
      = (ν : Measure ℝ) ((P.toIET lam)^[j] '' Tower.cellAt P γ lam b) := by
  have hcoe : ⇑(P.toIET lam) = Tower.exch P.perm (P.lengthsInBottom lam) := by
    rw [IETDatum₂.toIET_eq_mkIET1 P hsim, IETDatum₂.coe_mkIET1']
    rfl
  have hμ' : (μ : Measure ℝ).map (Tower.exch P.perm (P.lengthsInBottom lam))
      = (μ : Measure ℝ) := by
    rw [← hcoe]; exact hμ
  have hν' : (ν : Measure ℝ).map (Tower.exch P.perm (P.lengthsInBottom lam))
      = (ν : Measure ℝ) := by
    rw [← hcoe]; exact hν
  rw [hcoe]
  rw [Tower.measure_image_iterate P.perm (P.lengthsInBottom lam) (μ : Measure ℝ) hμ'
      (Tower.cellAt P γ lam b) measurableSet_Ico j,
    Tower.measure_image_iterate P.perm (P.lengthsInBottom lam) (ν : Measure ℝ) hν'
      (Tower.cellAt P γ lam b) measurableSet_Ico j]
  exact cellAt_mass_eq P hP hn hsim γ hOK hμ hν hlen b

/-! ## 3. The measure-theoretic interface (step 4/5) -/

/-- **The floor-partition datum.**  `Pf k` is a finite partition of `[0,1)` into measurable sets,
refining as `k` grows, with mesh tending to `0`.  This is exactly the interface of
`LengthInjective.measure_eq_of_floors`. -/
def TowerPartitions (Pf : ℕ → Finset (Set ℝ)) : Prop :=
  (∀ k A, A ∈ Pf k → MeasurableSet A) ∧
  (∀ k A, A ∈ Pf k → A ⊆ Set.Ico (0:ℝ) 1) ∧
  (∀ k x, x ∈ Set.Ico (0:ℝ) 1 → ∃ A ∈ Pf k, x ∈ A) ∧
  (∀ k A, A ∈ Pf k → ∀ B ∈ Pf k, A ≠ B → Disjoint A B) ∧
  (∀ k A, A ∈ Pf (k+1) → ∃ B ∈ Pf k, A ⊆ B) ∧
  (∀ ε > 0, ∀ᶠ k in atTop, ∀ A ∈ Pf k, ∀ x ∈ A, ∀ y ∈ A, dist x y < ε)

/-- **Injectivity from floor partitions.**  If every atom of the level-`k` partition is an iterate
image of a level-`γ k` cell (a "floor" of the level-`k` tower), the two invariant probability
measures assign the same mass to every atom, and `measure_eq_of_floors` gives `μ = ν`. -/
theorem length_injective_of_floors (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {lam : α → ℝ≥0} (hsim : lam ∈ simplexOn α)
    (γ : ℕ → List Bool) (hOK : ∀ k, TowerTrue.IterOK P lam (γ k))
    (Pf : ℕ → Finset (Set ℝ))
    (hfloor : ∀ k A, A ∈ Pf k →
      ∃ (b : α) (j : ℕ), A = (P.toIET lam)^[j] '' Tower.cellAt P (γ k) lam b)
    (hpart : TowerPartitions Pf)
    {μ ν : ProbabilityMeasure ℝ}
    (hμ : Invariant μ (P.toIET lam)) (hν : Invariant ν (P.toIET lam))
    (hμm : (μ : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1)
    (hνm : (ν : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1)
    (hlen : InvariantMeasure.lambdaOf μ P lam = InvariantMeasure.lambdaOf ν P lam) :
    μ = ν := by
  have haeμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Set.Ico (0:ℝ) 1 := by
    refine MeasureTheory.ae_iff.mpr ?_
    change (μ : Measure ℝ) (Set.Ico (0:ℝ) 1)ᶜ = 0
    rw [measure_compl measurableSet_Ico (by rw [hμm]; exact ENNReal.one_ne_top), hμm]
    simp
  have haeν : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Set.Ico (0:ℝ) 1 := by
    refine MeasureTheory.ae_iff.mpr ?_
    change (ν : Measure ℝ) (Set.Ico (0:ℝ) 1)ᶜ = 0
    rw [measure_compl measurableSet_Ico (by rw [hνm]; exact ENNReal.one_ne_top), hνm]
    simp
  have heq : ∀ k A, A ∈ Pf k → (μ : Measure ℝ) A = (ν : Measure ℝ) A := by
    intro k A hA
    obtain ⟨b, j, rfl⟩ := hfloor k A hA
    exact floor_mass_eq P hP hn hsim (γ k) (hOK k) hμ hν hlen
  have hmain : (μ : Measure ℝ) = (ν : Measure ℝ) :=
    LengthInjective.measure_eq_of_floors haeμ haeν Pf hpart.1 hpart.2.1 hpart.2.2.1
      hpart.2.2.2.1 hpart.2.2.2.2.1 hpart.2.2.2.2.2 heq
  exact Subtype.ext hmain

/-! ## 5. The mesh condition from atom lengths -/

/-- **The mesh hypothesis of `TowerPartitions` from a length bound on the atoms.** If every atom of
`Pf k` is a half-open interval of length at most `ℓ k`, and `ℓ k → 0`, then any two points of an
atom are eventually arbitrarily close. This is the form in which the tower supplies the mesh: the
floors `T^[j] '' cellAt P (γ k) lam b` of the level-`k` tower are intervals of length
`(Tower.lamAfter P (γ k) lam b : ℝ) ≤ λ^{(k)}_*`, and `λ^{(k)}_* → 0`. -/
theorem mesh_of_Ico_lengths (Pf : ℕ → Finset (Set ℝ)) (ℓ : ℕ → ℝ)
    (hℓ : Tendsto ℓ atTop (𝓝 0))
    (hIco : ∀ k A, A ∈ Pf k → ∃ u v, A = Set.Ico u v ∧ v - u ≤ ℓ k) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ A ∈ Pf k, ∀ x ∈ A, ∀ y ∈ A, dist x y < ε := by
  intro ε hε
  filter_upwards [hℓ.eventually (isOpen_Iio.mem_nhds hε)] with k hk A hA x hx y hy
  obtain ⟨u, v, rfl, huv⟩ := hIco k A hA
  have hk' : ℓ k < ε := hk
  rw [Real.dist_eq, abs_lt]
  constructor <;> simp only [Set.mem_Ico] at hx hy <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-! ## 6. The tower bookkeeping that is still missing, and the conditional theorem -/

/-- **The missing tower input.**  For `lam ∈ simplexOn α` there is a family of words `γ` satisfying
the type rule, and finite partitions `Pf k` of `[0,1)` into *floors* `T^[j] '' cellAt P (γ k) lam b`
which are measurable, refine and have mesh `→ 0`.  This is a purely measure/dynamics statement about
the interval exchange itself, with no reference to `μ` or `ν`: it is the level-`k` Rauzy–Veech tower
decomposition of `[0,1)`.  Its content is *not* the conclusion of `length_injective_of_tower` (a
statement about invariant measures), so taking it as a hypothesis does not smuggle in the goal. -/
def FloorPartitionData (P : IETDatum₂ α n) (lam : α → ℝ≥0) : Prop :=
  ∃ (γ : ℕ → List Bool) (Pf : ℕ → Finset (Set ℝ)),
    (∀ k, TowerTrue.IterOK P lam (γ k)) ∧ TowerPartitions Pf ∧
      (∀ k A, A ∈ Pf k → ∃ (b : α) (j : ℕ),
        A = (P.toIET lam)^[j] '' Tower.cellAt P (γ k) lam b)

/-- **Injectivity from the floor partitions.** The target `length_injective_of_tower`, with the
level-`k` tower decomposition supplied as the single hypothesis `FloorPartitionData`. -/
theorem length_injective_of_tower_of_floors (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (hfloor : ∀ᵐ lam ∂(simplexVolumeOn α), FloorPartitionData P lam) :
    ∀ᵐ lam ∂(simplexVolumeOn α), ∀ μ ν : ProbabilityMeasure ℝ,
      Invariant μ (P.toIET lam) → Invariant ν (P.toIET lam) →
      (μ : Measure ℝ) (Set.Ico 0 1) = 1 → (ν : Measure ℝ) (Set.Ico 0 1) = 1 →
      InvariantMeasure.lambdaOf μ P lam = InvariantMeasure.lambdaOf ν P lam → μ = ν := by
  have hcard : Fintype.card α ≠ 0 := by
    rw [Fintype.card_congr P.piTop, Fintype.card_fin]
    omega
  filter_upwards [hfloor, ae_mem_simplexOn_of_card_ne_zero (α := α) hcard]
    with lam hdata hsim
  obtain ⟨γ, Pf, hOK, hpart, hfl⟩ := hdata
  intro μ ν hμ hν hμm hνm hlen
  exact length_injective_of_floors P hP hn hsim γ hOK Pf hfl hpart hμ hν hμm hνm hlen

/-! ## 8. The tower input in its concrete (classical) form -/

/-- The height of the level-`k` tower over `b`: the column sum of the path matrix `Q(γ k)`. -/
noncomputable def hgt (P : IETDatum₂ α n) (γ : ℕ → List Bool) (k : ℕ) (b : α) : ℕ :=
  ∑ a, (IETDatum₂.Path.Q P (γ k) a b).toNat

/-- **The floors of the level-`k` tower**: the iterate images `T^[j] (cell_k b)`, `j < h_k b`, of
the level-`k` cells. -/
noncomputable def floors (P : IETDatum₂ α n) (lam : α → ℝ≥0) (γ : ℕ → List Bool)
    (k : ℕ) :
    Finset (Set ℝ) := by
  classical
  exact ((Finset.univ : Finset (Σ b : α, Fin (hgt P γ k b)))).image
    (fun p => (P.toIET lam)^[(p.2 : ℕ)] '' Tower.cellAt P (γ k) lam p.1)

/-- **The level-`k` tower decomposition, concrete form.**  The floors `T^[j] (cell_k b)`, `j < h_k b
= ∑_a Q(γ k)_{ab}`, are half-open intervals of the level-`k` lengths, each inside a single level-`0`
cell; they are measurable, pairwise disjoint, cover `[0,1)`, and the level-`(k+1)` family refines
the level-`k` family.  It is the input that `length_injective_of_tower` consumes; it is proved in
`IETFree/RauzyVeech/TowerTiling.lean`. -/
def TowerTiling (P : IETDatum₂ α n) (lam : α → ℝ≥0) (γ : ℕ → List Bool) : Prop :=
  (∀ k, TowerTrue.IterOK P lam (γ k)) ∧
  (∀ k A, A ∈ floors P lam γ k → MeasurableSet A) ∧
  (∀ k A, A ∈ floors P lam γ k → A ⊆ Set.Ico (0:ℝ) 1) ∧
  (∀ k A, A ∈ floors P lam γ k → ∀ B ∈ floors P lam γ k, A ≠ B → Disjoint A B) ∧
  (∀ k x, x ∈ Set.Ico (0:ℝ) 1 → ∃ A ∈ floors P lam γ k, x ∈ A) ∧
  (∀ k A, A ∈ floors P lam γ (k+1) → ∃ B ∈ floors P lam γ k, A ⊆ B) ∧
  (∀ k A, A ∈ floors P lam γ k → ∃ (b : α) (j : ℕ),
      A = (P.toIET lam)^[j] '' Tower.cellAt P (γ k) lam b ∧
        ∃ u v, A = Set.Ico u v ∧ v - u = (Tower.lamAfter P (γ k) lam b : ℝ))

/-- **The concrete tower statement implies the floor-partition input of the injectivity.** -/
theorem floorPartitionData_of_tiling (P : IETDatum₂ α n) (lam : α → ℝ≥0)
    (γ : ℕ → List Bool)
    (hT : TowerTiling P lam γ)
    (hlim : Tendsto (fun k => ∑ b, (Tower.lamAfter P (γ k) lam b : ℝ)) atTop (𝓝 0)) :
    FloorPartitionData P lam := by
  obtain ⟨hOK, hmeas, hsub, hdisj, hcov, href, hshape⟩ := hT
  refine ⟨γ, fun k => floors P lam γ k, hOK, ⟨hmeas, hsub, hcov, hdisj, href, ?_⟩, ?_⟩
  · refine mesh_of_Ico_lengths _ _ hlim ?_
    intro k A hA
    obtain ⟨b, j, -, u, v, hAv, huv⟩ := hshape k A hA
    exact ⟨u, v, hAv, huv.trans_le (Finset.single_le_sum
      (f := fun b => (Tower.lamAfter P (γ k) lam b : ℝ))
      (fun b _ => (Tower.lamAfter P (γ k) lam b).coe_nonneg) (Finset.mem_univ b))⟩
  · intro k A hA
    obtain ⟨b, j, hAj, -, -⟩ := hshape k A hA
    exact ⟨b, j, hAj⟩

/-- **Injectivity from the concrete tower decomposition.**  The statement
`length_injective_of_tower`, with the single a.e. hypothesis that some Rauzy path through `lam`
carries the level-`k` tower decomposition `TowerTiling`.  (The path membership, the type rule and
the positivity of the renormalised lengths are all proved elsewhere --
`IETDatum₂.ae_notMem_cylStop_all`, `IterGlue2.iterOK_pathWord` -- and are kept in the hypothesis
only to fix the path; the shrinking of the level-`k` base is derived here from
`MeshShrink.tendsto_total`.) -/
theorem length_injective_of_tower_of_tiling (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (h : ∀ᵐ lam ∂(simplexVolumeOn α), ∃ p : ℕ → Bool,
      (∀ k, TowerTrue.IterOK P lam (PrefixWord.pfx p k)) ∧
      (∀ k a, 0 < Tower.lamAfter P (PrefixWord.pfx p k) lam a) ∧
      TowerTiling P lam (PrefixWord.pfx p)) :
    ∀ᵐ lam ∂(simplexVolumeOn α), ∀ μ ν : ProbabilityMeasure ℝ,
      Invariant μ (P.toIET lam) → Invariant ν (P.toIET lam) →
      (μ : Measure ℝ) (Set.Ico 0 1) = 1 → (ν : Measure ℝ) (Set.Ico 0 1) = 1 →
      InvariantMeasure.lambdaOf μ P lam = InvariantMeasure.lambdaOf ν P lam → μ = ν := by
  refine length_injective_of_tower_of_floors P hP hn ?_
  filter_upwards [h] with lam hlam
  obtain ⟨p, hOK, hpos, hT⟩ := hlam
  have hw : ∀ k, IETDatum₂.IsRenorm P (PrefixWord.pfx p k) lam
      (fun a => (Tower.lamAfter P (PrefixWord.pfx p k) lam a : ℝ)) :=
    fun k => (IETDatum₂.isRenorm_iff P _ lam _).mpr
      ⟨hpos k, (IterGlue.qApply_lamAfter P hP hn _ lam (hOK k)).symm⟩
  have hlim : Tendsto (fun k => ∑ b, (Tower.lamAfter P (PrefixWord.pfx p k) lam b : ℝ))
      atTop (𝓝 0) := MeshShrink.tendsto_total P p lam _ hP hn hw
  exact floorPartitionData_of_tiling P lam _ hT hlim

end TowerInjectivity

