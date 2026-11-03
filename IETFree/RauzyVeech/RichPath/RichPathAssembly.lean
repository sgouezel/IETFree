/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.RauzyVeech.MainComponents
import IETFree.RauzyVeech.RichPath.BoundedLag
import IETFree.RauzyVeech.CylinderRecurrence
import IETFree.RauzyVeech.RichPath.NodeHeight

/-!
# Richness of the greedy path from the graded induction

This file reduces richness of the greedy path to **one** hard input, the graded estimate at level
`#α` with a single constant — `NodeHeight.GradedStep P (#α) C C` for some `C > 1`, which is the end
of the induction of `IETFree/RauzyVeech/RichPath/GradedInduction.lean` — together with the analytic
work that turns it into richness. Contents:

* §1 `GoodAt`, the per-node condition of the estimate in cylinder coordinates.
* §2 the bridge `bal_of_good`: the graded estimate produces `C`-*balanced* states in the sense of
  `BoundedLag.Bal`, which is what bounded distortion consumes.
* §3 `step_pinned`: from the estimate, a definite fraction of every cylinder `Δ(w)` consists of
  points which, at a time `≥ |w|`, sit at a *prescribed* vertex `π₀` and lie in the cylinder of a
  prescribed word `γ₀` read from there.
* §4 the pinned Lévy recurrence (`levy_cylinder`): the recurrence of
  `IETFree/RauzyVeech/CylinderRecurrence.lean` instantiated at the cylinder partition, for an
  arbitrary level-measurable target set.
* §5 the vertex-pinned target set `ZpinTgt`, and its agreement with the level form off a null set.

The step from the estimate to richness itself is `RichPath.richGreedyPath`
(`IETFree/RauzyVeech/RichPath/RichGreedyPath.lean`), which uses §3–§5 below.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators Topology

namespace RichPath

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. The graded estimate in cylinder coordinates

The input the analysis below consumes is `NodeHeight.GradedStep P (#α) C C` for some `C > 1`, in the
*minimal-family* (prefix-free) form: for every node `w` of the diagram of `P` there is a prefix-free
family of continuations `δ` of total relative mass `> 1/C` (`CylinderMass.cond P w δ =
σ(Δ(w ++ δ))/σ(Δ w)`) at each of which `GoodAt P C w δ` holds.  The state of the node `w` is
`q_w = B_w·1` (`NodeHeight.st P w`, the column sums of `IETDatum₂.Path.Q P w`), the functionals are
`𝔐 = NodeHeight.Mk 1` and `𝔪 = NodeHeight.Mk (#α)` (`NodeHeight.Mk_card`), and a *later state* of
`w` is `w ++ δ`.  The source's theorem is uniform in the state `q ∈ ℝ^𝒜_{>0}` and in the vertex;
here the states that occur are the `q_w`, and the set `{q_w}` is closed under `q ↦ B_δ q = q_{wδ}`
(`CylinderMass.cs_append_eq_sum`), which is all the induction inside the theorem uses. -/

/-- **The per-node condition of the graded estimate at the node `w`**: the state at the later node
`w ++ δ` has maximum `< C · min{𝔪(state at w ++ δ), 𝔐(state at w)}`, i.e. it is `C`-balanced and its
maximum has grown by at most `C`.  Here `𝔐 = NodeHeight.Mk 1`, `𝔪 = NodeHeight.Mk (#α)`
(`NodeHeight.Mk_card`) and `q_w = B_w·1` is `NodeHeight.st P w`; this is the inner conjunct of
`NodeHeight.GradedStep P (#α) C C`. -/
def GoodAt (P : IETDatum₂ α n) (C : ℝ) (w δ : List Bool) : Prop :=
  NodeHeight.Mk 1 (NodeHeight.st P (w ++ δ)) <
    C * min (NodeHeight.Mk (Fintype.card α) (NodeHeight.st P (w ++ δ)))
      (NodeHeight.Mk 1 (NodeHeight.st P w))

/-! ## 2. The state produced by the estimate is balanced  Bounded distortion
(`BoundedLag.cond_ge_of_balanced`) needs the state in the form `∀ b b', q b ≤ C · q b'` of
`BoundedLag.Bal`; the graded estimate gives it in the form `Mk 1 < C · min (Mk (#α)) (Mk 1)`.  The
bridge is `NodeHeight.Mk_card`. -/

theorem bal_of_good (P : IETDatum₂ α n) {C : ℝ} (hC : 1 ≤ C) {w δ : List Bool}
    (h : GoodAt P C w δ) : BoundedLag.Bal P (w ++ δ) C := by
  intro b b'
  have h1 : NodeHeight.st P (w ++ δ) b ≤ NodeHeight.Mk 1 (NodeHeight.st P (w ++ δ)) :=
    NodeHeight.le_Mk_one b
  have h2 : NodeHeight.Mk (Fintype.card α) (NodeHeight.st P (w ++ δ))
      = NodeHeight.mmin Finset.univ (NodeHeight.st P (w ++ δ)) := NodeHeight.Mk_card _
  have h3 : NodeHeight.mmin Finset.univ (NodeHeight.st P (w ++ δ)) ≤ NodeHeight.st P (w ++ δ) b' :=
    NodeHeight.mmin_le (Finset.mem_univ b')
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC
  refine le_of_lt (a := NodeHeight.st P (w ++ δ) b) (b := C * NodeHeight.st P (w ++ δ) b') ?_
  calc NodeHeight.st P (w ++ δ) b ≤ NodeHeight.Mk 1 (NodeHeight.st P (w ++ δ)) := h1
    _ < C * min (NodeHeight.Mk (Fintype.card α) (NodeHeight.st P (w ++ δ)))
          (NodeHeight.Mk 1 (NodeHeight.st P w)) := h
    _ ≤ C * NodeHeight.Mk (Fintype.card α) (NodeHeight.st P (w ++ δ)) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hC0
    _ = C * NodeHeight.mmin Finset.univ (NodeHeight.st P (w ++ δ)) := by rw [h2]
    _ ≤ C * NodeHeight.st P (w ++ δ) b' := mul_le_mul_of_nonneg_left h3 hC0

end RichPath

namespace RichPath

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 3. Balanced descendants, with the vertex *pinned* -/

/-- The greedy words are nested: `pathWord x m` is a prefix of `pathWord x N` for `m ≤ N`. -/
theorem pathWord_prefix (P : IETDatum₂ α n) (x : α → ℝ≥0) {m N : ℕ} (h : m ≤ N) :
    IETDatum₂.pathWord P x m <+: IETDatum₂.pathWord P x N := by
  induction N with
  | zero =>
    rw [Nat.le_zero.mp h]
  | succ N ih =>
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · rw [h']
    · rw [IETDatum₂.pathWord_succ]
      exact (ih (by omega)).trans (List.prefix_append _ _)

/-- The length-`m` prefix of the greedy word of length `N`. -/
theorem take_pathWord_le (P : IETDatum₂ α n) (x : α → ℝ≥0) {m N : ℕ} (h : m ≤ N) :
    (IETDatum₂.pathWord P x N).take m = IETDatum₂.pathWord P x m := by
  obtain ⟨t, ht⟩ := pathWord_prefix P x h
  have h1 : (IETDatum₂.pathWord P x N).take m = (IETDatum₂.pathWord P x m ++ t).take m := by
    rw [← ht]
  rw [h1, List.take_append_of_le_length (by rw [IETDatum₂.pathWord_length]),
    List.take_of_length_le (by rw [IETDatum₂.pathWord_length])]

/-- **Balanced descendants, with the vertex pinned.**  Given the graded estimate
`NodeHeight.GradedStep P (#α) C C` and a vertex `π₀` reachable from `P`, there is `δ > 0` such that
from every node `w` a fraction `δ` of `Δ(w)` consists of points which, at some time `m ≥ |w|`, sit
at `π₀` and lie in the cylinder of `γ₀` read from there.  Construction: apply the estimate at `w` (a
prefix-free family `S` of `C`-balanced descendants of mass `> 1/C`), and from each `w ++ δ` follow
the *pad* `padWord P π_wδ`, which returns to the base vertex `P` in bounded time and therefore lands
at `P`; the reading of `u₀` then pins the vertex to `π₀ = vertex P u₀`, and `γ₀` follows.  The
mass of the child cylinder is `cond P (w ++ δ) (pad ++ u₀ ++ γ₀) ≥ (1/(C·d·M))^d` by Kerckhoff's
corollary at a balanced node (`BoundedLag.cond_ge_of_balanced`), uniformly in `w`. -/
theorem step_pinned (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {π₀ : IETDatum₂ α n} (hπ : ∃ u : List Bool, IETDatum₂.vertex P u = π₀) {γ₀ : List Bool}
    (h : ∃ C : ℝ, 1 < C ∧ NodeHeight.GradedStep P (Fintype.card α) C C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : List Bool, ∃ F : Set (α → ℝ≥0),
      F ⊆ IETDatum₂.simplexCyl P w ∧
      ENNReal.ofReal δ * simplexVolumeOn α (IETDatum₂.simplexCyl P w) ≤ simplexVolumeOn α F ∧
      ∀ x ∈ F, ∃ m ≥ w.length, IETDatum₂.vertex P (IETDatum₂.pathWord P x m) = π₀ ∧
        x ∈ IETDatum₂.simplexCyl P (IETDatum₂.pathWord P x m ++ γ₀) := by
  classical
  obtain ⟨C, hC, hS⟩ := h
  obtain ⟨u₀, hu₀⟩ := hπ
  have hC1 : 1 ≤ C := le_of_lt hC
  have hCpos : (0 : ℝ) < C := lt_trans zero_lt_one hC
  -- the constants: `δ₂` from Kerckhoff's corollary, and the loss `1/C` of the a priori estimate
  set δ₂ : ℝ := (1 / (C * (Fintype.card α : ℝ) * BoundedLag.lagBound P (u₀ ++ γ₀))) ^
    (Fintype.card α) with hδ₂def
  have hcardpos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    have h1 : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨P.piTop.symm ⟨0, Nat.pos_of_ne_zero
      (NeZero.ne n)⟩⟩
    exact_mod_cast h1
  have hδ₂pos : 0 < δ₂ := by
    rw [hδ₂def]
    have hlag : (0 : ℝ) < BoundedLag.lagBound P (u₀ ++ γ₀) :=
      BoundedLag.lagBound_pos P (u₀ ++ γ₀)
    have : (0 : ℝ) < 1 / (C * (Fintype.card α : ℝ) * BoundedLag.lagBound P (u₀ ++ γ₀)) := by
      positivity
    exact pow_pos this _
  refine ⟨δ₂ / C, div_pos hδ₂pos hCpos, fun w => ?_⟩
  obtain ⟨S, hpf, hgood, hmass⟩ := hS w
  -- the pad from the vertex reached by `w ++ δ` back to `P`
  set pd : List Bool → List Bool := fun δ => BoundedLag.padWord P (IETDatum₂.vertex P (w ++ δ))
    with hpd
  -- the balanced descendants are balanced in the sense of bounded distortion
  have hbal : ∀ δ ∈ S, BoundedLag.Bal P (w ++ δ) C := fun δ hδ => bal_of_good P hC1 (hgood δ hδ)
  -- the child cylinder of each member of the family
  set F : Set (α → ℝ≥0) :=
    ⋃ δ ∈ S, IETDatum₂.simplexCyl P (w ++ (δ ++ (pd δ ++ (u₀ ++ γ₀)))) with hF
  refine ⟨F, ?_, ?_, ?_⟩
  · -- `F ⊆ Δ(w)`
    intro x hx
    simp only [hF, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨δ, -, hxδ⟩ := hx
    exact PosBlock.simplexCyl_append_left P hP hn w (δ ++ (pd δ ++ (u₀ ++ γ₀))) hxδ
  · -- the mass of `F`
    have hanti := hpf.antichain
    have hdisj : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
        Disjoint (IETDatum₂.simplexCyl P (w ++ (a ++ (pd a ++ (u₀ ++ γ₀)))))
          (IETDatum₂.simplexCyl P (w ++ (b ++ (pd b ++ (u₀ ++ γ₀))))) := by
      intro a ha b hb hne
      have h1 : IETDatum₂.simplexCyl P (w ++ (a ++ (pd a ++ (u₀ ++ γ₀))))
          ⊆ IETDatum₂.simplexCyl P (w ++ a) := by
        simpa only [List.append_assoc] using
          PosBlock.simplexCyl_append_left P hP hn (w ++ a) (pd a ++ (u₀ ++ γ₀))
      have h2 : IETDatum₂.simplexCyl P (w ++ (b ++ (pd b ++ (u₀ ++ γ₀))))
          ⊆ IETDatum₂.simplexCyl P (w ++ b) := by
        simpa only [List.append_assoc] using
          PosBlock.simplexCyl_append_left P hP hn (w ++ b) (pd b ++ (u₀ ++ γ₀))
      exact Disjoint.mono h1 h2 (BalancedCylinders.disjoint_simplexCyl_of_not_isPrefix P hP hn
        (hanti a ha b hb hne) (hanti b hb a ha (Ne.symm hne)))
    have hFsum : simplexVolumeOn α F = ∑ δ ∈ S,
        simplexVolumeOn α (IETDatum₂.simplexCyl P (w ++ (δ ++ (pd δ ++ (u₀ ++ γ₀))))) :=
      measure_biUnion_finset hdisj fun δ _ => IETDatum₂.measurableSet_simplexCyl P hP hn _
    have hunion : simplexVolumeOn α (⋃ δ ∈ S, IETDatum₂.simplexCyl P (w ++ δ))
        = ∑ δ ∈ S, simplexVolumeOn α (IETDatum₂.simplexCyl P (w ++ δ)) :=
      BalancedCylinders.volume_iUnion_antichain P hP hn w S hanti
    -- each child carries a definite fraction of its parent
    have hterm : ∀ δ ∈ S, ENNReal.ofReal δ₂ *
        simplexVolumeOn α (IETDatum₂.simplexCyl P (w ++ δ)) ≤
          simplexVolumeOn α (IETDatum₂.simplexCyl P (w ++ (δ ++ (pd δ ++ (u₀ ++ γ₀))))) := by
      intro δ hδ
      have hpdδ : pd δ = BoundedLag.padWord P (IETDatum₂.vertex P (w ++ δ)) := by
        rw [hpd]
      have hcond : δ₂ ≤ CylinderMass.cond P (w ++ δ) (pd δ ++ (u₀ ++ γ₀)) := by
        rw [hδ₂def, hpdδ]
        exact BoundedLag.cond_ge_of_balanced P hC1 (hbal δ hδ)
          (BoundedLag.one_le_lagBound P (u₀ ++ γ₀))
          (BoundedLag.pathQ_padWord_le P (u₀ ++ γ₀) (IETDatum₂.vertex P (w ++ δ)))
      have hchain : CylinderMass.cond P w (δ ++ (pd δ ++ (u₀ ++ γ₀)))
          = CylinderMass.cond P w δ * CylinderMass.cond P (w ++ δ) (pd δ ++ (u₀ ++ γ₀)) :=
        CylinderMass.cond_append P w δ (pd δ ++ (u₀ ++ γ₀))
      have hcw : (0 : ℝ) < CylinderMass.cond P w δ := CylinderMass.cond_pos P w δ
      rw [CylinderMass.volume_append_eq_cond P w (δ ++ (pd δ ++ (u₀ ++ γ₀))), hchain,
        CylinderMass.volume_append_eq_cond P w δ]
      have hstep : ENNReal.ofReal (CylinderMass.cond P w δ * δ₂)
          ≤ ENNReal.ofReal (CylinderMass.cond P w δ *
              CylinderMass.cond P (w ++ δ) (pd δ ++ (u₀ ++ γ₀))) :=
        ENNReal.ofReal_le_ofReal (by nlinarith [hcw, hcond])
      calc ENNReal.ofReal δ₂ *
            (ENNReal.ofReal (CylinderMass.cond P w δ) * simplexVolumeOn α
              (IETDatum₂.simplexCyl P w))
          = ENNReal.ofReal (CylinderMass.cond P w δ * δ₂) * simplexVolumeOn α
              (IETDatum₂.simplexCyl P w) := by
            rw [← mul_assoc,
              mul_comm (ENNReal.ofReal δ₂) (ENNReal.ofReal (CylinderMass.cond P w δ)),
              ← ENNReal.ofReal_mul hcw.le]
        _ ≤ ENNReal.ofReal (CylinderMass.cond P w δ *
              CylinderMass.cond P (w ++ δ) (pd δ ++ (u₀ ++ γ₀))) * simplexVolumeOn α
              (IETDatum₂.simplexCyl P w) := by
            exact mul_le_mul_of_nonneg_right hstep bot_le
    have hsplit : ENNReal.ofReal (δ₂ / C) = ENNReal.ofReal δ₂ * ENNReal.ofReal (1 / C) := by
      rw [← ENNReal.ofReal_mul hδ₂pos.le, mul_one_div]
    rw [hFsum]
    calc ENNReal.ofReal (δ₂ / C) * simplexVolumeOn α (IETDatum₂.simplexCyl P w)
        = ENNReal.ofReal δ₂ *
            (ENNReal.ofReal (1 / C) * simplexVolumeOn α (IETDatum₂.simplexCyl P w)) := by
          rw [hsplit, mul_assoc]
      _ ≤ ENNReal.ofReal δ₂ * simplexVolumeOn α (⋃ δ ∈ S, IETDatum₂.simplexCyl P (w ++ δ)) := by
          gcongr
          exact NodeHeight.volume_union_ge P hP hn hpf w hmass
      _ = ∑ δ ∈ S, ENNReal.ofReal δ₂ *
            simplexVolumeOn α (IETDatum₂.simplexCyl P (w ++ δ)) := by
          rw [hunion, Finset.mul_sum]
      _ ≤ ∑ δ ∈ S, simplexVolumeOn α
            (IETDatum₂.simplexCyl P (w ++ (δ ++ (pd δ ++ (u₀ ++ γ₀))))) :=
          Finset.sum_le_sum hterm
  · -- the pinned hitting property
    intro x hx
    simp only [hF, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨δ, -, hxδ⟩ := hx
    set N₁ : ℕ := (w ++ (δ ++ (pd δ ++ u₀))).length with hN₁
    have hsplit : w ++ (δ ++ (pd δ ++ (u₀ ++ γ₀))) = (w ++ (δ ++ (pd δ ++ u₀))) ++ γ₀ := by
      simp only [List.append_assoc]
    have hW : IETDatum₂.pathWord P x (w ++ (δ ++ (pd δ ++ (u₀ ++ γ₀)))).length
        = w ++ (δ ++ (pd δ ++ (u₀ ++ γ₀))) := PosBlock.pathWord_eq_of_mem P hP hn _ hxδ
    have hlen : (w ++ (δ ++ (pd δ ++ (u₀ ++ γ₀)))).length = N₁ + γ₀.length := by
      rw [hsplit, List.length_append]
    have htake : IETDatum₂.pathWord P x N₁ = w ++ (δ ++ (pd δ ++ u₀)) := by
      have h1 : IETDatum₂.pathWord P x (N₁ + γ₀.length) = (w ++ (δ ++ (pd δ ++ u₀))) ++ γ₀ := by
        rw [← hlen, ← hsplit]
        exact hW
      calc IETDatum₂.pathWord P x N₁
          = (IETDatum₂.pathWord P x (N₁ + γ₀.length)).take N₁ :=
              (take_pathWord_le P x (by omega)).symm
        _ = ((w ++ (δ ++ (pd δ ++ u₀))) ++ γ₀).take N₁ := by rw [h1]
        _ = w ++ (δ ++ (pd δ ++ u₀)) := by
            rw [List.take_append_of_le_length (by rw [hN₁]), List.take_of_length_le (by rw [hN₁])]
    have hpdδ : pd δ = BoundedLag.padWord P (IETDatum₂.vertex P (w ++ δ)) := by rw [hpd]
    have hpad : IETDatum₂.vertex (IETDatum₂.vertex P (w ++ δ)) (pd δ) = P := by
      rw [hpdδ]
      exact BoundedLag.padWord_spec ⟨w ++ δ, rfl⟩
    refine ⟨N₁, ?_, ?_, ?_⟩
    · have hle : w.length ≤ (w ++ (δ ++ (pd δ ++ u₀))).length := by simp
      simpa only [hN₁] using hle
    · rw [htake, show w ++ (δ ++ (pd δ ++ u₀)) = ((w ++ δ) ++ pd δ) ++ u₀ from by
        simp only [List.append_assoc], IETDatum₂.vertex_append, IETDatum₂.vertex_append, hpad, hu₀]
    · have hmem : x ∈ IETDatum₂.simplexCyl P ((w ++ (δ ++ (pd δ ++ u₀))) ++ γ₀) := by
        rw [← hsplit]
        exact hxδ
      rwa [← htake] at hmem

end RichPath

namespace RichPath

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 4. The Lévy recurrence at the cylinder partition, arbitrary target -/

/-- **The Lévy recurrence instantiated at the level-`k` cylinder partition**, for an *arbitrary*
level-measurable target `Z`: if every level-`k` cylinder (`k ≥ N`) carries a subset of relative mass
`≥ δ` which misses `Z`, then `Z` is null.  This is the cylinder recurrence with the target `Z` not
tied to the letters-only condition `Ztgt`; richness needs `Z` to be the *vertex-pinned*
target `ZpinTgt` ("follows `γ₀` from `π₀` at no late time"), which is not of the form `Ztgt`. -/
theorem levy_cylinder (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (Z : Set (α → ℝ≥0))
    (hZ : MeasurableSet[⨆ j, MeasurableSpace.comap (CylRec.lvl P j) ⊤] Z)
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ (k : ℕ), N ≤ k → ∀ w : List Bool, w.length = k →
      ∃ Fw : Set (α → ℝ≥0), Fw ⊆ IETDatum₂.simplexCyl P w ∧
        ENNReal.ofReal δ * simplexVolumeOn α (IETDatum₂.simplexCyl P w) ≤ simplexVolumeOn α Fw ∧
        Disjoint (Fw \ CylRec.Nbad P) Z) :
    simplexVolumeOn α Z = 0 := by
  classical
  set c : ℝ≥0∞ := (simplexVolumeOn α (Set.univ : Set (α → ℝ≥0)))⁻¹ with hc
  have hμuniv : simplexVolumeOn α (Set.univ : Set (α → ℝ≥0)) = volume (region (n - 1)) :=
    CylRec.simplexVolumeOn_univ P
  have hμ0 : simplexVolumeOn α (Set.univ : Set (α → ℝ≥0)) ≠ 0 := by
    rw [hμuniv]; exact ne_of_gt (RegionVolume.volume_region_pos _)
  have hμtop : simplexVolumeOn α (Set.univ : Set (α → ℝ≥0)) ≠ ⊤ := by
    rw [hμuniv]; exact RegionVolume.volume_region_ne_top _
  have hcne : c ≠ 0 := by
    rw [hc]
    simpa using hμtop
  have hscale : ∀ s : Set (α → ℝ≥0),
      (c • simplexVolumeOn α) s = c * simplexVolumeOn α s := by
    intro s; rw [Measure.smul_apply, smul_eq_mul]
  have hprob : (c • simplexVolumeOn α) Set.univ = 1 := by
    rw [hscale, hc]
    exact ENNReal.inv_mul_cancel hμ0 hμtop
  have key : (c • simplexVolumeOn α) Z = 0 := by
    refine @LevyRecurrence.levy_recurrence (α → ℝ≥0) _ (c • simplexVolumeOn α) ⟨hprob⟩
      CylRec.Word _ _ _ (fun k => CylRec.lvl P k) (fun k => CylRec.measurable_lvl P hP hn k)
      (fun k x y hxy => CylRec.lvl_refine P k x y hxy) Z hZ N δ hδ ?_
    intro k hk y
    obtain ⟨Fw, hFwsub, hFwbd, hFwdisj⟩ := h k hk y.1 y.2
    refine ⟨Fw \ CylRec.Nbad P, ?_, ?_, ?_⟩
    · intro x hx
      have hxN : x ∉ CylRec.Nbad P := hx.2
      have hp : IETDatum₂.pathWord P x k = y.1 := by
        have h := (CylRec.mem_cyl_iff_pathWord P hP hn hxN (w := y.1)).mp (hFwsub hx.1)
        rwa [y.2] at h
      change CylRec.lvl P k x = y
      exact Subtype.ext hp
    · have hatom_eq : {x : α → ℝ≥0 | CylRec.lvl P k x = y} \ CylRec.Nbad P =
          IETDatum₂.simplexCyl P y.1 \ CylRec.Nbad P := by
        ext x
        rw [Set.mem_sdiff, Set.mem_sdiff, Set.mem_ofPred_eq, CylRec.lvl_eq_iff]
        constructor
        · rintro ⟨hp, hxN⟩
          exact ⟨(CylRec.mem_cyl_iff_pathWord P hP hn hxN (w := y.1)).mpr (by rw [y.2]; exact hp),
            hxN⟩
        · rintro ⟨hmem, hxN⟩
          have h := (CylRec.mem_cyl_iff_pathWord P hP hn hxN (w := y.1)).mp hmem
          rw [y.2] at h
          exact ⟨h, hxN⟩
      have hatom : simplexVolumeOn α {x : α → ℝ≥0 | CylRec.lvl P k x = y} =
          simplexVolumeOn α (IETDatum₂.simplexCyl P y.1) :=
        CylRec.measure_eq_of_sdiff_Nbad_eq P hP hn hatom_eq
      have hkey : ENNReal.ofReal δ * simplexVolumeOn α (IETDatum₂.simplexCyl P y.1) ≤
          simplexVolumeOn α (Fw \ CylRec.Nbad P) :=
        le_trans hFwbd (CylRec.measure_le_measure_sdiff_Nbad P hP hn Fw)
      rw [hscale, hscale, hatom]
      calc ENNReal.ofReal δ * (c * simplexVolumeOn α (IETDatum₂.simplexCyl P y.1))
          = c * (ENNReal.ofReal δ * simplexVolumeOn α (IETDatum₂.simplexCyl P y.1)) := by
            rw [← mul_assoc, mul_comm (ENNReal.ofReal δ) c, mul_assoc]
        _ ≤ c * simplexVolumeOn α (Fw \ CylRec.Nbad P) :=
            mul_le_mul_of_nonneg_left hkey bot_le
    · exact hFwdisj
  rw [hscale] at key
  rcases mul_eq_zero.mp key with h0 | h0
  · exact absurd h0 hcne
  · exact h0

/-! ## 5. The vertex-pinned target set -/

/-- The good event pinning the vertex at time `m`: the greedy word of length `m + |γ₀|` follows `γ₀`
after a prefix of length `m` which sits at `π₀`.  Written at the level of words, so that it is
manifestly a finite union of level-`(m + |γ₀|)` atoms. -/
def GoodPin (P : IETDatum₂ α n) (π₀ : IETDatum₂ α n) (γ₀ : List Bool) (m : ℕ) :
    Set (α → ℝ≥0) :=
  ⋃ u : {u : CylRec.Word m // IETDatum₂.vertex P u.1 = π₀},
    {x | CylRec.lvl P (m + γ₀.length) x = CylRec.push γ₀ u.1}

/-- The good event is a union of atoms, hence measurable for the σ-algebra of the levels. -/
theorem measurableSet_GoodPin (P : IETDatum₂ α n) (π₀ : IETDatum₂ α n) (γ₀ : List Bool) (m : ℕ) :
    MeasurableSet[⨆ j, MeasurableSpace.comap (CylRec.lvl P j) ⊤] (GoodPin P π₀ γ₀ m) :=
  MeasurableSet.iUnion fun u =>
    CylRec.measurableSet_lvl_atom P (m + γ₀.length) (CylRec.push γ₀ u.1)

/-- The good event, off the null set `Nbad`, is the vertex-pinned cylinder condition. -/
theorem mem_GoodPin_iff (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (π₀ : IETDatum₂ α n) (γ₀ : List Bool) (m : ℕ) {x : α → ℝ≥0} (hx : x ∉ CylRec.Nbad P) :
    x ∈ GoodPin P π₀ γ₀ m ↔
      IETDatum₂.vertex P (IETDatum₂.pathWord P x m) = π₀ ∧
        x ∈ IETDatum₂.simplexCyl P (IETDatum₂.pathWord P x m ++ γ₀) := by
  constructor
  · intro hxG
    rw [GoodPin, Set.mem_iUnion] at hxG
    obtain ⟨u, hxu⟩ := hxG
    have h1 : IETDatum₂.pathWord P x (m + γ₀.length) = u.1.1 ++ γ₀ := by
      have := congrArg Subtype.val hxu
      simpa only [CylRec.lvl_coe, CylRec.push_coe] using this
    have h2 : IETDatum₂.pathWord P x m = u.1.1 := by
      have htake := take_pathWord_le P x (m := m) (N := m + γ₀.length) (by omega)
      rw [h1, List.take_append_of_le_length (le_of_eq u.1.2.symm),
        List.take_of_length_le (le_of_eq u.1.2)] at htake
      exact htake.symm
    refine ⟨?_, ?_⟩
    · rw [h2]; exact u.2
    · exact (CylRec.mem_cyl_append_iff_pathWord P hP hn hx m γ₀).mpr (by rw [h1, h2])
  · rintro ⟨hv, hmem⟩
    refine Set.mem_iUnion.mpr
      ⟨⟨⟨IETDatum₂.pathWord P x m, IETDatum₂.pathWord_length P x m⟩, hv⟩, ?_⟩
    have h2 := (CylRec.mem_cyl_append_iff_pathWord P hP hn hx m γ₀).mp hmem
    exact Subtype.ext h2

/-- The level form of the pinned target: it never follows `γ₀` from `π₀` at a time `≥ N`. -/
def ZpinLev (P : IETDatum₂ α n) (π₀ : IETDatum₂ α n) (γ₀ : List Bool) (N : ℕ) :
    Set (α → ℝ≥0) :=
  ⋂ m : {m : ℕ // N ≤ m}, (GoodPin P π₀ γ₀ m.1)ᶜ

/-- `ZpinLev` is measurable for the σ-algebra generated by the levels. -/
theorem measurableSet_ZpinLev (P : IETDatum₂ α n) (π₀ : IETDatum₂ α n) (γ₀ : List Bool) (N : ℕ) :
    MeasurableSet[⨆ j, MeasurableSpace.comap (CylRec.lvl P j) ⊤] (ZpinLev P π₀ γ₀ N) :=
  MeasurableSet.iInter fun m => (measurableSet_GoodPin P π₀ γ₀ m.1).compl

/-- The actual target set of richness: the points of the root cylinder which, at no time
`m ≥ N`, sit at `π₀` and lie in the cylinder of `γ₀` read from there. -/
def ZpinTgt (P : IETDatum₂ α n) (π₀ : IETDatum₂ α n) (γ₀ : List Bool) (N : ℕ) :
    Set (α → ℝ≥0) :=
  {x | x ∈ IETDatum₂.simplexCyl P [] ∧ ∀ m ≥ N,
    ¬ (IETDatum₂.vertex P (IETDatum₂.pathWord P x m) = π₀ ∧
      x ∈ IETDatum₂.simplexCyl P (IETDatum₂.pathWord P x m ++ γ₀))}

/-- The level form and the point form of the pinned target agree off the null set `Nbad`. -/
theorem ZpinLev_inter_Nbad (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (π₀ : IETDatum₂ α n) (γ₀ : List Bool) (N : ℕ) :
    ZpinLev P π₀ γ₀ N ∩ (CylRec.Nbad P)ᶜ = ZpinTgt P π₀ γ₀ N ∩ (CylRec.Nbad P)ᶜ := by
  ext x
  simp only [ZpinLev, ZpinTgt, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hgood, hx⟩
    have hroot : x ∈ IETDatum₂.simplexCyl P [] := by
      by_contra h
      exact hx (Or.inr h)
    refine ⟨⟨hroot, ?_⟩, hx⟩
    exact fun m hm hpin =>
      hgood ⟨m, hm⟩ ((mem_GoodPin_iff P hP hn π₀ γ₀ m hx).mpr hpin)
  · rintro ⟨⟨hroot, hbad⟩, hx⟩
    refine ⟨?_, hx⟩
    rintro ⟨m, hm⟩
    exact fun hg => hbad m hm ((mem_GoodPin_iff P hP hn π₀ γ₀ m hx).mp hg)

end RichPath

