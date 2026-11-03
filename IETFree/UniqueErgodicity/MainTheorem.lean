/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.PosBlocks
public import IETFree.RauzyVeech.RichPath.RichGreedyPath
public import IETFree.RauzyVeech.TowerTiling

/-!
# Masur–Veech: a.e. unique ergodicity of interval exchange maps

Masur–Veech, for the two-bijection datum: almost every length vector gives an exchange with a unique
invariant probability measure carried by `[0, 1)`.  The two inputs of the proof are theorems, in
modules below this one:

* richness of the greedy path with the vertices pinned — `RichPath.richGreedyPath`, in
  `IETFree/RauzyVeech/RichPath/RichGreedyPath.lean`, by the graded induction of the source;
* the ray criterion from positive blocks — `positiveBlocksRay`, in
  `IETFree/RauzyVeech/PosBlocks.lean`.

Neither is a hypothesis of anything: the three steps of the assembly below take no arguments
beyond `P`, `hP` and `2 ≤ n`:

* `hasPositiveBlocks_ae` — richness, and the uniform bound on the entries, give positive blocks a.e.
  with one bound `M` (`IETDatum₂.exists_uniform_bound'`, where `2 ≤ n` enters);
* `rayCondition_of_components` — those blocks, and the ray criterion, give the ray condition a.e.;
* `main_of_components` — the ray condition and the injectivity of the length map give the theorem.

The measure is required to live on `[0, 1)`: without `μ (Ico 0 1) = 1` the statement is false, as
the exchange is the identity off `[0,1)` and the Dirac mass at `2` is invariant too.

The statement is given for the two-bijection datum `IETDatum₂` used by the induction; the
single-permutation form, stated with the copied `mkIET1'`, is `masurVeech_ae_unique_invariant_perm`
below. -/

@[expose] public section


open MeasureTheory

/-! ## The assembly: the two inputs, one a.e. step each, and the length map -/

section AssemblySteps

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- **Richness gives the hypothesis of the ray criterion a.e., with one bound `M` for all the
blocks**: richness returns to the base vertex `P` at unbounded times and then follows a strictly
positive word `v`, whose entries are bounded by one constant for every irreducible vertex
(`IETDatum₂.exists_uniform_bound'`, which is where `2 ≤ n` enters).  This is where the pinned vertex
of `RichPath.richGreedyPath` is used, and where the bound comes from. -/
theorem hasPositiveBlocks_ae (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∀ᵐ lam ∂(simplexVolumeOn α), ∃ M : ℕ, HasPositiveBlocks P lam M := by
  classical
  obtain ⟨C₁, -, hword⟩ := IETDatum₂.exists_uniform_bound' (α := α) (n := n) hn
  obtain ⟨M, hM⟩ := exists_nat_ge C₁
  obtain ⟨v, hv⟩ := hword P hP
  filter_upwards [RichPath.richGreedyPath P hP hn P [] rfl v] with lam hl
  refine ⟨M, fun k => ?_⟩
  obtain ⟨m, hm, w, hw, hvert, hcyl⟩ := hl k
  refine ⟨m, hm, w, v, hw, hcyl, ?_⟩
  rw [hvert]
  intro a b
  refine ⟨(hv a b).1, ?_⟩
  have h2' := (hv a b).2
  have h3 : ((IETDatum₂.Path.Q P v a b : ℤ) : ℝ) ≤ (M : ℝ) := le_trans h2' hM
  exact_mod_cast h3

omit [DecidableEq α] in
/-- **The ray criterion gives the ray condition a.e.**, hence the first component of the assembly.
The null-set condition `lam ∉ cylStop P (pathWord P lam k)` is discharged by
`IETDatum₂.ae_notMem_cylStop_all`. -/
theorem rayCondition_of_components (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∀ᵐ lam ∂(simplexVolumeOn α), RayCondition P lam := by
  classical
  filter_upwards [hasPositiveBlocks_ae P hP hn, IETDatum₂.ae_notMem_cylStop_all P hP hn]
    with lam hbl hstop
  obtain ⟨M, hM⟩ := hbl
  exact positiveBlocksRay P hP hn M lam (fun k => hstop _) hM

omit [DecidableEq α] in
/-- **The assembly: the two inputs give the main theorem.**  `hasPositiveBlocks_ae` turns richness,
and the uniform bound on the entries of a positive Rauzy matrix, into the hypothesis of the ray
criterion; `positiveBlocksRay` then gives the ray condition a.e.;
`InvariantMeasure.masurVeech_of_components` closes the argument with the unconditional injectivity
`TowerInjectivity.length_injective_of_tower`. -/
theorem main_of_components (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∀ᵐ lam ∂(simplexVolumeOn α), ∃! μ : ProbabilityMeasure ℝ,
      Invariant μ (P.toIET lam) ∧ (μ : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1 := by
  classical
  have hcard : Fintype.card α = n := by
    rw [Fintype.card_congr P.piTop, Fintype.card_fin]
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  exact InvariantMeasure.masurVeech_of_components P (rayCondition_of_components P hP hn)
    (TowerInjectivity.length_injective_of_tower P hP hn)

end AssemblySteps

/-- **Masur–Veech, measure form.** For irreducible combinatorial data on at least two letters,
almost every length vector gives an exchange with exactly one invariant probability measure carried
by `[0, 1)`. -/
theorem masurVeech_ae_unique_invariant {α : Type*} [Fintype α]
    (n : ℕ) (hn : 2 ≤ n) [NeZero n] (P : IETDatum₂ α n) (hP : P.Irreducible) :
    ∀ᵐ lam ∂(simplexVolumeOn α), ∃! μ : ProbabilityMeasure ℝ,
      Invariant μ (P.toIET lam) ∧ (μ : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1 := by
  classical
  exact main_of_components P hP hn

/-! ### Axiom report

Every declaration of the Rauzy–Veech development is used in the proof of
`masurVeech_ae_unique_invariant`, and the report of its axioms is `[propext, Classical.choice,
Quot.sound]`, with no `sorryAx` and no custom axiom.  The library's single axiom report is the one
printed in `IETFree/ChallengeSolved.lean`, for the main theorem, whose proof reaches this one. -/


/-- **Masur–Veech, single-permutation form.**  For an irreducible permutation of `n ≥ 2` letters,
almost every length vector of the simplex gives the exchange `mkIET1 lam π` a unique invariant
probability measure carried by `[0, 1)`.  This is the form of the theorem in the copied
single-permutation API; no hypothesis on `lam` is needed, since `simplexVolume` is carried by
the simplex.  The datum `IETDatum₂.ofPerm π` of `IETFree/TopBotFormalism.lean` has `π` as its
permutation and the identity as its bottom order; `IETDatum₂.ofPerm_toIET` identifies its exchange
with `mkIET1' lam π h`, `mkIET1_of_mem` with `mkIET1 lam π` on the simplex, and
`simplexVolumeOn_fin` identifies `simplexVolumeOn (Fin n)` with `simplexVolume n`, which is the
whole proof. -/
theorem masurVeech_ae_unique_invariant_perm {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    (π : Equiv.Perm (Fin n)) (hπ : IsIrreduciblePerm π) :
    ∀ᵐ lam ∂(simplexVolume n), ∃! μ : ProbabilityMeasure ℝ,
      Invariant μ (mkIET1 lam π) ∧ (μ : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1 := by
  have hmain := masurVeech_ae_unique_invariant (α := Fin n) n hn (IETDatum₂.ofPerm π)
    ((IETDatum₂.ofPerm_irreducible_iff π).mpr hπ)
  rw [simplexVolumeOn_fin n] at hmain
  filter_upwards [hmain, ae_mem_simplexOn_fin (Nat.pos_iff_ne_zero.mp (by omega))]
    with lam hl h
  rwa [IETDatum₂.ofPerm_toIET π h, ← mkIET1_of_mem h] at hl

end
