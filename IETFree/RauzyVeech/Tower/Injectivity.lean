/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.Measure.RefiningPartition
public import IETFree.RauzyVeech.IterGlue
public import IETFree.RauzyVeech.MeshShrink
public import IETFree.RauzyVeech.Tower.Glue

/-!
# Injectivity of the length map, from the tower decomposition

The length vector of an invariant probability measure determines the measure.  This file proves it
from the floors of the Rokhlin tower decomposition: the level-`k` floors of a Rauzy path have masses
that are linear functions of the length vector (`cellAt_mass_eq`, `floor_mass_eq`), they refine with
`k` (`FloorPartitionData`), and their diameters go to `0` (`length_injective_of_floors`,
`length_injective_of_tower_of_floors`), so a refining-partition argument (`RefiningPartition`)
forces
two measures with the same length vector to agree.  The tiling that feeds `FloorPartitionData`
almost everywhere is proved in `IETFree/RauzyVeech/Tower/Tiling.lean`. -/

@[expose] public section

open MeasureTheory Filter
open IntervalExchange.Measure
open scoped NNReal ENNReal BigOperators Topology

namespace IntervalExchange.RauzyVeech

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Step 2 of the route: equal length vectors give equal level-cell masses -/

/-- **Level-cell masses are determined by the length vector.** Two invariant probability measures of
`P.toIET lam` with the same length vector give the same mass to every level-`γ` cell: the tower
formula (`tower_formula_level_pathQ_any`) writes the length vector as `Q(γ)` applied to
the level-`γ` cell masses, and `Q(γ)` acts injectively on real vectors (`IETDatum₂.Path.Q_det` gives
`det Q(γ) = 1`, so `Q(γ)` is invertible over `ℤ`, and `IETDatum₂.injective_qApply_Q` is the real
form used here). -/
theorem cellAt_mass_eq (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {lam : α → ℝ≥0} (hsim : lam ∈ simplex α) (γ : List Bool)
    (hOK : IsRauzyPath P lam γ)
    {μ ν : ProbabilityMeasure ℝ}
    (hμ : Invariant μ (P.toIET lam)) (hν : Invariant ν (P.toIET lam))
    (hlen : lambdaOf μ P lam = lambdaOf ν P lam) (b : α) :
    (μ : Measure ℝ) (cellAt P γ lam b)
      = (ν : Measure ℝ) (cellAt P γ lam b) := by
  have hQ (a) (b) : 0 ≤ IETDatum₂.Path.Q P γ a b := IETDatum₂.Path.Q_nonneg P γ a b
  have h1 : (fun a => lambdaOf μ P lam a)
      = qApply (IETDatum₂.Path.Q P γ)
          (fun b => ((μ : Measure ℝ) (cellAt P γ lam b)).toReal) :=
    real_eq_qApply P (μ : Measure ℝ) hQ (fun b => measure_ne_top _ _)
      (fun a => tower_formula_level_pathQ_any P lam hsim
        (μ : Measure ℝ) hμ γ hOK a)
  have h2 : (fun a => lambdaOf ν P lam a)
      = qApply (IETDatum₂.Path.Q P γ)
          (fun b => ((ν : Measure ℝ) (cellAt P γ lam b)).toReal) :=
    real_eq_qApply P (ν : Measure ℝ) hQ (fun b => measure_ne_top _ _)
      (fun a => tower_formula_level_pathQ_any P lam hsim
        (ν : Measure ℝ) hν γ hOK a)
  have hy : (fun b => ((μ : Measure ℝ) (cellAt P γ lam b)).toReal)
      = (fun b => ((ν : Measure ℝ) (cellAt P γ lam b)).toReal) :=
    IETDatum₂.injective_qApply_Q P hP hn γ (h1.symm.trans (hlen.trans h2))
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    (congrFun hy b)

/-! ## 2. Step 3 of the route: all floors of a tower have the mass of their cell -/

/-- **Floors have the mass of their cell.**  An iterate image of a level-`γ` cell has the same
`μ`-mass as the cell itself, by invariance (`measure_image_iterate`); with step 2 it has the
same mass for `μ` and for `ν`. -/
theorem floor_mass_eq (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {lam : α → ℝ≥0} (hsim : lam ∈ simplex α) (γ : List Bool)
    (hOK : IsRauzyPath P lam γ)
    {μ ν : ProbabilityMeasure ℝ}
    (hμ : Invariant μ (P.toIET lam)) (hν : Invariant ν (P.toIET lam))
    (hlen : lambdaOf μ P lam = lambdaOf ν P lam)
    {b : α} {j : ℕ} :
    (μ : Measure ℝ) ((P.toIET lam)^[j] '' cellAt P γ lam b)
      = (ν : Measure ℝ) ((P.toIET lam)^[j] '' cellAt P γ lam b) := by
  have hcoe : ⇑(P.toIET lam) = mkIETFun (P.lengthsInBottom lam) P.perm 0 := by
    rw [IETDatum₂.toIET_eq_mkIET1 P hsim, coe_mkIET1']
  have hμ' : (μ : Measure ℝ).map (mkIETFun (P.lengthsInBottom lam) P.perm 0)
      = (μ : Measure ℝ) := by
    rw [← hcoe]; exact hμ
  have hν' : (ν : Measure ℝ).map (mkIETFun (P.lengthsInBottom lam) P.perm 0)
      = (ν : Measure ℝ) := by
    rw [← hcoe]; exact hν
  rw [hcoe]
  rw [measure_image_iterate P.perm (P.lengthsInBottom lam) (μ : Measure ℝ) hμ'
      (cellAt P γ lam b) measurableSet_Ico j,
    measure_image_iterate P.perm (P.lengthsInBottom lam) (ν : Measure ℝ) hν'
      (cellAt P γ lam b) measurableSet_Ico j]
  exact cellAt_mass_eq P hP hn hsim γ hOK hμ hν hlen b

/-! ## 3. The measure-theoretic interface (step 4/5) -/

/-- **The floor-partition datum.**  `Pf k` is a finite partition of `[0,1)` into measurable sets,
refining as `k` grows, with mesh tending to `0`.  This is exactly the interface of
`measure_restrict_eq_of_refining_partitions`. -/
def TowerPartitions (Pf : ℕ → Finset (Set ℝ)) : Prop :=
  (∀ k A, A ∈ Pf k → MeasurableSet A) ∧
  (∀ k A, A ∈ Pf k → A ⊆ Set.Ico (0:ℝ) 1) ∧
  (∀ k x, x ∈ Set.Ico (0:ℝ) 1 → ∃ A ∈ Pf k, x ∈ A) ∧
  (∀ k A, A ∈ Pf k → ∀ B ∈ Pf k, A ≠ B → Disjoint A B) ∧
  (∀ k A, A ∈ Pf (k+1) → ∃ B ∈ Pf k, A ⊆ B) ∧
  (∀ ε > 0, ∀ᶠ k in atTop, ∀ A ∈ Pf k, ∀ x ∈ A, ∀ y ∈ A, dist x y < ε)

/-- **Injectivity from floor partitions.**  If every atom of the level-`k` partition is an iterate
image of a level-`γ k` cell (a "floor" of the level-`k` tower), the two invariant probability
measures assign the same mass to every atom, and `measure_restrict_eq_of_refining_partitions` gives
`μ = ν`. -/
theorem length_injective_of_floors (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {lam : α → ℝ≥0} (hsim : lam ∈ simplex α)
    (γ : ℕ → List Bool) (hOK : ∀ k, IsRauzyPath P lam (γ k))
    (Pf : ℕ → Finset (Set ℝ))
    (hfloor : ∀ k A, A ∈ Pf k →
      ∃ (b : α) (j : ℕ), A = (P.toIET lam)^[j] '' cellAt P (γ k) lam b)
    (hpart : TowerPartitions Pf)
    {μ ν : ProbabilityMeasure ℝ}
    (hμ : Invariant μ (P.toIET lam)) (hν : Invariant ν (P.toIET lam))
    (hμm : (μ : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1)
    (hνm : (ν : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1)
    (hlen : lambdaOf μ P lam = lambdaOf ν P lam) :
    μ = ν := by
  have haeμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Set.Ico (0:ℝ) 1 := by
    refine MeasureTheory.ae_iff.mpr ?_
    simp only [← Set.compl_ofPred, Set.ofPred_mem_eq]
    rw [measure_compl measurableSet_Ico (by rw [hμm]; exact ENNReal.one_ne_top), hμm]
    simp
  have haeν : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Set.Ico (0:ℝ) 1 := by
    refine MeasureTheory.ae_iff.mpr ?_
    simp only [← Set.compl_ofPred, Set.ofPred_mem_eq]
    rw [measure_compl measurableSet_Ico (by rw [hνm]; exact ENNReal.one_ne_top), hνm]
    simp
  have heq (k A) (hA : A ∈ Pf k) : (μ : Measure ℝ) A = (ν : Measure ℝ) A := by
    obtain ⟨b, j, rfl⟩ := hfloor k A hA
    exact floor_mass_eq P hP hn hsim (γ k) (hOK k) hμ hν hlen
  -- the refining-partition lemma gives equality after restriction to `[0, 1)`; the a.e. hypotheses
  -- remove the restriction
  have hres := measure_restrict_eq_of_refining_partitions (μ := (μ : Measure ℝ))
    (ν := (ν : Measure ℝ)) (Set.Ico (0:ℝ) 1) Pf hpart.1 hpart.2.1 hpart.2.2.1
      hpart.2.2.2.1 hpart.2.2.2.2.1 hpart.2.2.2.2.2 heq
  rw [Measure.restrict_eq_self_of_ae_mem haeμ, Measure.restrict_eq_self_of_ae_mem haeν] at hres
  have hmain : (μ : Measure ℝ) = (ν : Measure ℝ) := hres
  exact Subtype.ext hmain

/-! ## 4. The mesh condition from atom lengths -/

/-- **The mesh hypothesis of `TowerPartitions` from a length bound on the atoms.** If every atom of
`Pf k` is a half-open interval of length at most `ℓ k`, and `ℓ k → 0`, then any two points of an
atom are eventually arbitrarily close. This is the form in which the tower supplies the mesh: the
floors `T^[j] '' cellAt P (γ k) lam b` of the level-`k` tower are intervals of length
`(lamAfter P (γ k) lam b : ℝ) ≤ λ^{(k)}_*`, and `λ^{(k)}_* → 0`. -/
theorem mesh_of_Ico_lengths (Pf : ℕ → Finset (Set ℝ)) (ℓ : ℕ → ℝ)
    (hℓ : Tendsto ℓ atTop (𝓝 0))
    (hIco : ∀ k A, A ∈ Pf k → ∃ u v, A = Set.Ico u v ∧ v - u ≤ ℓ k)
    (ε : ℝ) (hε : ε > 0) : ∀ᶠ k in atTop, ∀ A ∈ Pf k, ∀ x ∈ A, ∀ y ∈ A, dist x y < ε := by
  filter_upwards [hℓ.eventually (isOpen_Iio.mem_nhds hε)] with k hk A hA x hx y hy
  obtain ⟨u, v, rfl, huv⟩ := hIco k A hA
  rw [Real.dist_eq, abs_lt]
  constructor <;> simp only [Set.mem_Ico] at hx hy <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-! ## 5. The tower bookkeeping that is still missing, and the conditional theorem -/

/-- **The missing tower input.**  For `lam ∈ simplex α` there is a family of words `γ` satisfying
the type rule, and finite partitions `Pf k` of `[0,1)` into *floors* `T^[j] '' cellAt P (γ k) lam b`
which are measurable, refine and have mesh `→ 0`.  This is a purely measure/dynamics statement about
the interval exchange itself, with no reference to `μ` or `ν`: it is the level-`k` Rauzy–Veech tower
decomposition of `[0,1)`.  Its content is *not* the conclusion of `length_injective_of_tower` (a
statement about invariant measures), so taking it as a hypothesis does not smuggle in the goal. -/
def FloorPartitionData (P : IETDatum₂ α n) (lam : α → ℝ≥0) : Prop :=
  ∃ (γ : ℕ → List Bool) (Pf : ℕ → Finset (Set ℝ)),
    (∀ k, IsRauzyPath P lam (γ k)) ∧ TowerPartitions Pf ∧
      (∀ k A, A ∈ Pf k → ∃ (b : α) (j : ℕ),
        A = (P.toIET lam)^[j] '' cellAt P (γ k) lam b)

/-- **Injectivity from the floor partitions.** The target `length_injective_of_tower`, with the
level-`k` tower decomposition supplied as the single hypothesis `FloorPartitionData`. -/
theorem length_injective_of_tower_of_floors (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (hfloor : ∀ᵐ lam ∂(simplexVolumeOn α), FloorPartitionData P lam) :
    ∀ᵐ lam ∂(simplexVolumeOn α), ∀ μ ν : ProbabilityMeasure ℝ,
      Invariant μ (P.toIET lam) → Invariant ν (P.toIET lam) →
      (μ : Measure ℝ) (Set.Ico 0 1) = 1 → (ν : Measure ℝ) (Set.Ico 0 1) = 1 →
      lambdaOf μ P lam = lambdaOf ν P lam → μ = ν := by
  have hcard : Fintype.card α ≠ 0 := by
    rw [Fintype.card_congr P.piTop, Fintype.card_fin]
    omega
  filter_upwards [hfloor, ae_mem_simplex_of_card_ne_zero (α := α) hcard]
    with lam hdata hsim
  obtain ⟨γ, Pf, hOK, hpart, hfl⟩ := hdata
  intro μ ν hμ hν hμm hνm hlen
  exact length_injective_of_floors P hP hn hsim γ hOK Pf hfl hpart hμ hν hμm hνm hlen

/-! ## 6. The tower input in its concrete (classical) form -/

/-- **The floors of the level-`k` tower**: the iterate images `T^[j] (cell_k b)`, `j < h_k b`, of
the level-`k` cells. -/
noncomputable def floors (P : IETDatum₂ α n) (lam : α → ℝ≥0) (γ : ℕ → List Bool)
    (k : ℕ) :
    Finset (Set ℝ) := by
  exact ((Finset.univ : Finset (Σ b : α, Fin (IETDatum₂.Path.height P (γ k) b)))).image
    (fun p => (P.toIET lam)^[(p.2 : ℕ)] '' cellAt P (γ k) lam p.1)

/-- **The level-`k` tower decomposition, concrete form.**  The floors `T^[j] (cell_k b)`, `j < h_k b
= ∑_a Q(γ k)_{ab}`, are half-open intervals of the level-`k` lengths, each inside a single level-`0`
cell; they are measurable, pairwise disjoint, cover `[0,1)`, and the level-`(k+1)` family refines
the level-`k` family.  It is the input that `length_injective_of_tower` consumes; it is proved in
`IETFree/RauzyVeech/Tower/Tiling.lean`. -/
def TowerTiling (P : IETDatum₂ α n) (lam : α → ℝ≥0) (γ : ℕ → List Bool) : Prop :=
  (∀ k, IsRauzyPath P lam (γ k)) ∧
  (∀ k A, A ∈ floors P lam γ k → MeasurableSet A) ∧
  (∀ k A, A ∈ floors P lam γ k → A ⊆ Set.Ico (0:ℝ) 1) ∧
  (∀ k A, A ∈ floors P lam γ k → ∀ B ∈ floors P lam γ k, A ≠ B → Disjoint A B) ∧
  (∀ k x, x ∈ Set.Ico (0:ℝ) 1 → ∃ A ∈ floors P lam γ k, x ∈ A) ∧
  (∀ k A, A ∈ floors P lam γ (k+1) → ∃ B ∈ floors P lam γ k, A ⊆ B) ∧
  (∀ k A, A ∈ floors P lam γ k → ∃ (b : α) (j : ℕ),
      A = (P.toIET lam)^[j] '' cellAt P (γ k) lam b ∧
        ∃ u v, A = Set.Ico u v ∧ v - u = (lamAfter P (γ k) lam b : ℝ))

/-- **The concrete tower statement implies the floor-partition input of the injectivity.** -/
theorem floorPartitionData_of_tiling (P : IETDatum₂ α n) (lam : α → ℝ≥0)
    (γ : ℕ → List Bool)
    (hT : TowerTiling P lam γ)
    (hlim : Tendsto (fun k => ∑ b, (lamAfter P (γ k) lam b : ℝ)) atTop (𝓝 0)) :
    FloorPartitionData P lam := by
  obtain ⟨hOK, hmeas, hsub, hdisj, hcov, href, hshape⟩ := hT
  refine ⟨γ, fun k => floors P lam γ k, hOK, ⟨hmeas, hsub, hcov, hdisj, href, ?_⟩, ?_⟩
  · refine mesh_of_Ico_lengths _ _ hlim ?_
    intro k A hA
    obtain ⟨b, j, -, u, v, hAv, huv⟩ := hshape k A hA
    exact ⟨u, v, hAv, huv.trans_le (Finset.single_le_sum
      (f := fun b => (lamAfter P (γ k) lam b : ℝ))
      (fun b _ => (lamAfter P (γ k) lam b).coe_nonneg) (Finset.mem_univ b))⟩
  · intro k A hA
    obtain ⟨b, j, hAj, -, -⟩ := hshape k A hA
    exact ⟨b, j, hAj⟩

/-- **Injectivity from the concrete tower decomposition.**  The statement
`length_injective_of_tower`, with the single a.e. hypothesis that some Rauzy path through `lam`
carries the level-`k` tower decomposition `TowerTiling`.  (The path membership, the type rule and
the positivity of the renormalised lengths are all proved elsewhere --
`IETDatum₂.ae_notMem_cylStop_all`, `isRauzyPath_pathWord` -- and are kept in the hypothesis
only to fix the path; the shrinking of the level-`k` base is derived here from
`tendsto_total`.) -/
theorem length_injective_of_tower_of_tiling (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (h : ∀ᵐ lam ∂(simplexVolumeOn α), ∃ p : ℕ → Bool,
      (∀ k, IsRauzyPath P lam (pfx p k)) ∧
      (∀ k a, 0 < lamAfter P (pfx p k) lam a) ∧
      TowerTiling P lam (pfx p)) :
    ∀ᵐ lam ∂(simplexVolumeOn α), ∀ μ ν : ProbabilityMeasure ℝ,
      Invariant μ (P.toIET lam) → Invariant ν (P.toIET lam) →
      (μ : Measure ℝ) (Set.Ico 0 1) = 1 → (ν : Measure ℝ) (Set.Ico 0 1) = 1 →
      lambdaOf μ P lam = lambdaOf ν P lam → μ = ν := by
  refine length_injective_of_tower_of_floors P hP hn ?_
  filter_upwards [h] with lam hlam
  obtain ⟨p, hOK, hpos, hT⟩ := hlam
  have hw (k) : IETDatum₂.IsRenorm P (pfx p k) lam
      (fun a => (lamAfter P (pfx p k) lam a : ℝ)) := (IETDatum₂.isRenorm_iff P _
          lam _).mpr
      ⟨hpos k, (qApply_lamAfter P hP hn _ lam (hOK k)).symm⟩
  have hlim : Tendsto (fun k => ∑ b, (lamAfter P (pfx p k) lam b : ℝ))
      atTop (𝓝 0) := tendsto_total P p lam _ hP hn hw
  exact floorPartitionData_of_tiling P lam _ hT hlim

end IntervalExchange.RauzyVeech

end
