/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.Tower.Injectivity
public import IETFree.RauzyVeech.Tower.LevelN
public import IETFree.RauzyVeech.Tower.Node

/-!
# The tower tiling of `[0, 1)`, almost everywhere

For almost every length vector there is a Rauzy path whose level-`k` floors are half-open intervals
of the renormalised lengths, pairwise disjoint and covering `[0, 1)`, with the level-`(k+1)` family
refining the level-`k` one and the mesh going to `0` (`ae_towerTiling`, from `towerTiling` along the
greedy word `towerTiling_pathWord`).  This is the geometric input of the injectivity of the length
map, `length_injective_of_tower`. -/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators Topology

namespace IntervalExchange.RauzyVeech

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Basic rewrites for a path given by its step types -/

theorem int_toNat_coe_real {k : ℤ} (h : 0 ≤ k) : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg h

/-- The coefficient formula for the renormalised lengths, in `ℝ`. -/
theorem renorm_apply (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {lam : α → ℝ≥0} {γ : List Bool}
    (hOK : IsRauzyPath P lam γ) (a : α) :
    (∑ b, ((IETDatum₂.Path.Q P γ a b).toNat : ℝ) * (lamAfter P γ lam b : ℝ))
      = (lam a : ℝ) := by
  have h1 := qApply_lamAfter P hP hn γ lam hOK
  have h2 (b) : ((IETDatum₂.Path.Q P γ a b).toNat : ℝ) = (IETDatum₂.Path.Q P γ a b : ℝ) :=
      int_toNat_coe_real (IETDatum₂.Path.Q_nonneg P γ a b)
  have h3 := congrFun h1 a
  simp only [qApply_apply] at h3
  rw [← h3]
  exact Finset.sum_congr rfl (fun b _ => by rw [h2 b])

omit [DecidableEq α] [NeZero n] in
theorem totalLength_eq_one {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hlam : lam ∈ simplex α) :
    totalLength (P.lengthsInBottom lam) = 1 := by
  rw [totalLength_lengthsInBottom]
  have h := congrArg (fun t : ℝ≥0 => (t : ℝ)) hlam
  push_cast at h
  exact h

omit [DecidableEq α] in
theorem mkIETFun_mapsTo_one {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hlam : lam ∈ simplex α)
    {y : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    mkIETFun (P.lengthsInBottom lam) P.perm 0 y ∈ Set.Ico (0 : ℝ) 1 := by
  have htot : totalLength (P.lengthsInBottom lam) = 1 := totalLength_eq_one hlam
  have hy' : y ∈ Set.Ico (0 : ℝ) (totalLength (P.lengthsInBottom lam)) := by
    rw [htot]; exact hy
  have h := mapsTo_mkIETFun P.perm (P.lengthsInBottom lam) hy'
  rwa [htot] at h

omit [DecidableEq α] in
theorem mkIETFun_iterate_mapsTo_one {P : IETDatum₂ α n} {lam : α → ℝ≥0}
    (hlam : lam ∈ simplex α)
    (j : ℕ) {y : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    (mkIETFun (P.lengthsInBottom lam) P.perm 0)^[j] y ∈ Set.Ico (0 : ℝ) 1 := by
  induction j with
  | zero => simpa using hy
  | succ m ih => rw [Function.iterate_succ_apply']; exact mkIETFun_mapsTo_one hlam ih

/-! ## 2. The fixed data of the induction -/

namespace TowerStep

variable (P : IETDatum₂ α n) (γ : ℕ → List Bool) (p : ℕ → Bool) (lam : α → ℝ≥0)

/-- The combinatorial data at level `k`. -/
noncomputable def datumAt (k : ℕ) : IETDatum₂ α n := IETDatum₂.vertex P (γ k)

/-- The length vector at level `k`. -/
noncomputable def lamAt (k : ℕ) : α → ℝ≥0 := lamAfter P (γ k) lam

/-- The level-`k` cell of the letter `b`. -/
noncomputable def levelCell (k : ℕ) (b : α) : Set ℝ := cellAt P (γ k) lam b

/-- The level-`k` height of the letter `b`. -/
noncomputable def heightAt (k : ℕ) (b : α) : ℕ := IETDatum₂.Path.height P (γ k) b

/-- The exchange at level `k`. -/
noncomputable def exchangeAt (k : ℕ) : ℝ → ℝ :=
  mkIETFun ((datumAt P γ k).lengthsInBottom (lamAt P γ lam k)) (datumAt P γ k).perm 0

end TowerStep

variable {P : IETDatum₂ α n} {γ : ℕ → List Bool} {p : ℕ → Bool} {lam : α → ℝ≥0}

/-! ## 3. One-step rewrites -/

theorem levelCell_succ {γ : ℕ → List Bool} {p : ℕ → Bool}
    (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (k : ℕ) (b : α) :
    TowerStep.levelCell P γ lam (k + 1) b
      = cellAt (TowerStep.datumAt P γ k) [p k] (TowerStep.lamAt P γ lam k) b := by
  rw [TowerStep.levelCell, TowerStep.datumAt, TowerStep.lamAt, hstep k]
  exact cellAt_succ P (γ k) (p k) lam b

theorem lamAt_succ {γ : ℕ → List Bool} {p : ℕ → Bool}
    (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (k : ℕ) :
    TowerStep.lamAt P γ lam (k + 1)
      = hatLam (TowerStep.datumAt P γ k) (p k) (TowerStep.lamAt P γ lam k) := by
  rw [TowerStep.lamAt, TowerStep.datumAt, TowerStep.lamAt, hstep k]
  exact lamAfter_append_singleton P lam (γ k) (p k)

omit [DecidableEq α] in
theorem datumAt_succ {γ : ℕ → List Bool} {p : ℕ → Bool}
    (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (k : ℕ) : TowerStep.datumAt P γ (k + 1) = (TowerStep.datumAt P γ k).rvStep (p k) := by
  rw [TowerStep.datumAt, TowerStep.datumAt, hstep k, IETDatum₂.vertex_append_singleton]

theorem levelCell_zero (hzero : γ 0 = []) (b : α) :
    TowerStep.levelCell P γ lam 0 b = cellOf P lam b := by
  simp only [TowerStep.levelCell, hzero, cellAt, cellOf, IETDatum₂.vertex,
    lamAfter]

theorem lamAt_zero (hzero : γ 0 = []) : TowerStep.lamAt P γ lam 0 = lam := by
  rw [TowerStep.lamAt, hzero]
  rfl

theorem heightAt_zero (hzero : γ 0 = []) (b : α) : TowerStep.heightAt P γ 0 b = 1 := by
  simp only [TowerStep.heightAt, IETDatum₂.Path.height, hzero, IETDatum₂.Path.Q]
  refine (Finset.sum_congr rfl (fun x _ => ?_)).trans (sum_ite_single (c := b) 1)
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem exchangeAt_zero (hzero : γ 0 = []) (hlam : lam ∈ simplex α) :
    TowerStep.exchangeAt P γ lam 0 = ⇑(P.toIET lam) := by
  rw [coe_toIET hlam, TowerStep.exchangeAt, TowerStep.datumAt, TowerStep.lamAt, hzero]
  rfl

/-! ## 4. The total length of the level-`k` base is at most one -/

theorem lamAt_step_le {γ : ℕ → List Bool} {p : ℕ → Bool}
    (hstep : ∀ k, γ (k + 1) = γ k ++ [p k]) (k : ℕ) (b : α) :
    TowerStep.lamAt P γ lam (k + 1) b ≤ TowerStep.lamAt P γ lam k b := by
  rw [lamAt_succ hstep, hatLam]
  split_ifs
  · exact tsub_le_self
  · exact le_rfl

theorem sum_LL_le {γ : ℕ → List Bool} {p : ℕ → Bool} (hzero : γ 0 = [])
    (hstep : ∀ k, γ (k + 1) = γ k ++ [p k]) (hlam : lam ∈ simplex α) (k : ℕ) :
    (∑ b, (TowerStep.lamAt P γ lam k b : ℝ)) ≤ 1 := by
  induction k with
  | zero =>
    rw [lamAt_zero hzero]
    have h := congrArg (fun t : ℝ≥0 => (t : ℝ)) hlam
    push_cast at h
    rw [h]
  | succ m ih =>
    refine le_trans (Finset.sum_le_sum (fun b _ => ?_)) ih
    exact_mod_cast lamAt_step_le hstep m b

theorem levelCell_sub_base (k : ℕ) (b : α) :
    TowerStep.levelCell P γ lam k b
      ⊆ Set.Ico (0 : ℝ) (∑ b, (TowerStep.lamAt P γ lam k b : ℝ)) := by
  have hsum : (∑ i, ((TowerStep.datumAt P γ k).lengthsInBottom
        (TowerStep.lamAt P γ lam k) i : ℝ))
      = ∑ b, (TowerStep.lamAt P γ lam k b : ℝ) :=
    Equiv.sum_comp (TowerStep.datumAt P γ k).piBottom.symm
      (fun b => (TowerStep.lamAt P γ lam k b : ℝ))
  have h := cellOf_subset (TowerStep.datumAt P γ k) (TowerStep.lamAt P γ lam k) b
  rw [hsum] at h
  exact h

theorem levelCell_sub_one {γ : ℕ → List Bool} {p : ℕ → Bool} (hzero : γ 0 = [])
    (hstep : ∀ k, γ (k + 1) = γ k ++ [p k]) (hlam : lam ∈ simplex α) (k : ℕ) (b : α) :
    TowerStep.levelCell P γ lam k b ⊆ Set.Ico (0 : ℝ) 1 :=
  fun _x hx => Set.Ico_subset_Ico le_rfl (sum_LL_le hzero hstep hlam k) (levelCell_sub_base k b hx)

/-! ## 5. Floors: membership, measurability, containment in `[0,1)` -/

theorem mem_floors_iff (k : ℕ) (A : Set ℝ) :
    A ∈ floors P lam γ k ↔ ∃ (b : α) (j : ℕ), j < TowerStep.heightAt P γ k b ∧
      A = (P.toIET lam)^[j] '' TowerStep.levelCell P γ lam k b := by
  rw [floors, Finset.mem_image]
  constructor
  · rintro ⟨q, -, rfl⟩
    exact ⟨q.1, (q.2 : ℕ), q.2.isLt, rfl⟩
  · rintro ⟨b, j, hj, rfl⟩
    exact ⟨⟨b, ⟨j, hj⟩⟩, Finset.mem_univ _, rfl⟩

theorem measurableSet_floor (hlam : lam ∈ simplex α) (k : ℕ) (b : α) (j : ℕ) :
    MeasurableSet ((P.toIET lam)^[j] '' TowerStep.levelCell P γ lam k b) := by
  rw [coe_toIET hlam]
  exact measurableSet_image_iterate P.perm (P.lengthsInBottom lam) measurableSet_Ico j

theorem floor_subset_one {γ : ℕ → List Bool} {p : ℕ → Bool} (hzero : γ 0 = [])
    (hstep : ∀ k, γ (k + 1) = γ k ++ [p k]) (hlam : lam ∈ simplex α) (k : ℕ) (b : α)
    (j : ℕ) :
    (P.toIET lam)^[j] '' TowerStep.levelCell P γ lam k b ⊆ Set.Ico (0 : ℝ) 1 := by
  rw [coe_toIET hlam]
  rintro x ⟨y, hy, rfl⟩
  exact mkIETFun_iterate_mapsTo_one hlam j (levelCell_sub_one hzero hstep hlam k b hy)

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
variable {P : IETDatum₂ α n} {γ : ℕ → List Bool} {p : ℕ → Bool} {lam : α → ℝ≥0}

/-! ## 6. The height recursion and the two names, in the notation of the induction -/

omit [DecidableEq α] in
theorem datumAt_last_ne (hP : P.Irreducible) (hn : 2 ≤ n) (k : ℕ) (e : Bool) :
    (TowerStep.datumAt P γ k).last e ≠ (TowerStep.datumAt P γ k).last (!e) := by
  rw [TowerStep.datumAt]
  cases e with
  | false => simpa using (IETDatum₂.vertex_last_ne P hP hn (γ k)).symm
  | true => simpa using IETDatum₂.vertex_last_ne P hP hn (γ k)

theorem isRauzyStep_at {γ : ℕ → List Bool} {p : ℕ → Bool}
    (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (hOK : ∀ k, IsRauzyPath P lam (γ k)) (k : ℕ) :
    IsRauzyStep (TowerStep.datumAt P γ k) (TowerStep.lamAt P γ lam k) (p k) := by
  have h' : IsRauzyPath P lam (γ k ++ [p k]) := by rw [← hstep k]; exact hOK (k + 1)
  exact ((isRauzyPath_append_singleton P lam (γ k) (p k)).mp h').2

/-- **The height recursion** in the notation of the induction. -/
theorem heightAt_succ (hP : P.Irreducible) (hn : 2 ≤ n)
    (hstep : ∀ k, γ (k + 1) = γ k ++ [p k]) (k : ℕ) (b : α) :
    TowerStep.heightAt P γ (k + 1) b = TowerStep.heightAt P γ k b
      + if b = (TowerStep.datumAt P γ k).last (!(p k)) then
          TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last (p k)) else 0 := by
  set e := p k with he
  set V := TowerStep.datumAt P γ k with hV
  have hne : V.last e ≠ V.last (!e) := datumAt_last_ne hP hn k e
  have hQ (a) : IETDatum₂.Path.Q P (γ (k + 1)) a b
      = IETDatum₂.Path.Q P (γ k) a b
        + if b = V.last (!e) then IETDatum₂.Path.Q P (γ k) a (V.last e) else 0 := by
    rw [hstep k, IETDatum₂.Path.Q_append, IETDatum₂.Path.Q_singleton, Matrix.mul_apply, hV]
    exact mulVec_rvMat (IETDatum₂.Path.Q P (γ k)) (TowerStep.datumAt P γ k) e hne a b
  have key (a : α) :
    (IETDatum₂.Path.Q P (γ (k + 1)) a b).toNat
      = (IETDatum₂.Path.Q P (γ k) a b).toNat
        + (if b = V.last (!e) then (IETDatum₂.Path.Q P (γ k) a (V.last e)).toNat else 0) := by
    rw [hQ a]
    have h1 : (0 : ℤ) ≤ IETDatum₂.Path.Q P (γ k) a b := IETDatum₂.Path.Q_nonneg P _ a b
    have h2 : (0 : ℤ) ≤ (if b = V.last (!e) then
        IETDatum₂.Path.Q P (γ k) a (V.last e) else 0) := by
      split
      · exact IETDatum₂.Path.Q_nonneg P _ a _
      · exact le_refl 0
    rw [Int.toNat_add h1 h2]
    congr 1
    split <;> simp
  simp only [TowerStep.heightAt, IETDatum₂.Path.height]
  calc (∑ a, (IETDatum₂.Path.Q P (γ (k + 1)) a b).toNat)
      = ∑ a, ((IETDatum₂.Path.Q P (γ k) a b).toNat
          + (if b = V.last (!e) then (IETDatum₂.Path.Q P (γ k) a (V.last e)).toNat else 0)) :=
        Finset.sum_congr rfl (fun a _ => key a)
    _ = (∑ a, (IETDatum₂.Path.Q P (γ k) a b).toNat)
          + ∑ a, (if b = V.last (!e) then
              (IETDatum₂.Path.Q P (γ k) a (V.last e)).toNat else 0) :=
        Finset.sum_add_distrib
    _ = (∑ a, (IETDatum₂.Path.Q P (γ k) a b).toNat)
          + if b = V.last (!e) then (∑ a, (IETDatum₂.Path.Q P (γ k) a (V.last e)).toNat)
            else 0 := by
        congr 1
        by_cases hb : b = V.last (!e)
        · simp only [ite_eq_left hb]
        · rw [ite_eq_right hb]
          exact Finset.sum_eq_zero (fun a _ => by simp only [ite_eq_right hb])

theorem cellAt_nil_eq (k : ℕ) (b : α) :
    cellAt (TowerStep.datumAt P γ k) [] (TowerStep.lamAt P γ lam k) b
      = TowerStep.levelCell P γ lam k b := (rfl)

/-! ## 7. The nesting of the level-`k+1` cells, in the notation of the induction -/

theorem levelCell_succ_sub_false (hstep : ∀ k, γ (k + 1) = γ k ++ [p k]) (k : ℕ) (b : α)
    (hp : p k = false) :
    TowerStep.levelCell P γ lam (k + 1) b ⊆ TowerStep.levelCell P γ lam k b := by
  rw [levelCell_succ hstep, hp, ← cellAt_nil_eq]
  exact names_false_sub (TowerStep.datumAt P γ k) (TowerStep.lamAt P γ lam k) b

theorem levelCell_succ_sub_true (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (hOK : ∀ k, IsRauzyPath P lam (γ k)) (k : ℕ) (b : α) (hp : p k = true)
    (hb : b ≠ (TowerStep.datumAt P γ k).last false) :
    TowerStep.levelCell P γ lam (k + 1) b ⊆ TowerStep.levelCell P γ lam k b := by
  have hS := isRauzyStep_at (P := P) (γ := γ) (p := p) hstep hOK k
  rw [hp] at hS
  rw [levelCell_succ hstep, hp, ← cellAt_nil_eq]
  exact names_true_sub (TowerStep.datumAt P γ k) (TowerStep.lamAt P γ lam k) hS b hb

theorem levelCell_succ_sub_true_scd (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (hOK : ∀ k, IsRauzyPath P lam (γ k)) (k : ℕ) (hp : p k = true) :
    TowerStep.levelCell P γ lam (k + 1) ((TowerStep.datumAt P γ k).last false)
      ⊆ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last true) := by
  have hS := isRauzyStep_at (P := P) (γ := γ) (p := p) hstep hOK k
  rw [hp] at hS
  rw [levelCell_succ hstep, hp, ← cellAt_nil_eq]
  exact names_true_sub_scd (TowerStep.datumAt P γ k) (TowerStep.lamAt P γ lam k) hS

theorem exchangeAt_image_false_scd (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (hOK : ∀ k, IsRauzyPath P lam (γ k)) (k : ℕ) (hp : p k = false) :
    TowerStep.exchangeAt P γ lam k ''
      TowerStep.levelCell P γ lam (k + 1) ((TowerStep.datumAt P γ k).last true)
      ⊆ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last false) := by
  have hS := isRauzyStep_at (P := P) (γ := γ) (p := p) hstep hOK k
  rw [hp] at hS
  rw [levelCell_succ hstep, hp]
  exact names_false_image (TowerStep.datumAt P γ k) (TowerStep.lamAt P γ lam k) hS

theorem exchangeAt_image_true_scd (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (hOK : ∀ k, IsRauzyPath P lam (γ k)) (k : ℕ) (hp : p k = true) :
    TowerStep.exchangeAt P γ lam k ''
      TowerStep.levelCell P γ lam (k + 1) ((TowerStep.datumAt P γ k).last false)
      ⊆ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last false) := by
  have hS := isRauzyStep_at (P := P) (γ := γ) (p := p) hstep hOK k
  rw [hp] at hS
  rw [levelCell_succ hstep, hp]
  exact names_true_image (TowerStep.datumAt P γ k) (TowerStep.lamAt P γ lam k) hS

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
variable {P : IETDatum₂ α n} {γ : ℕ → List Bool} {p : ℕ → Bool} {lam : α → ℝ≥0}

/-! ## 8. The first-return identity at every level -/

/-- **The first-return identity at every level.** -/
theorem FR_all (hzero : γ 0 = []) (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (hP : P.Irreducible) (hn : 2 ≤ n) (hlam : lam ∈ simplex α)
    (hOK : ∀ k, IsRauzyPath P lam (γ k)) (k : ℕ) (b : α) (y : ℝ)
    (hy : y ∈ TowerStep.levelCell P γ lam k b) :
      (⇑(P.toIET lam))^[TowerStep.heightAt P γ k b] y = TowerStep.exchangeAt P γ lam k y := by
  induction k generalizing b y with
  -- at level zero a cell is one cell of `P`, so the height is one and `exchangeAt 0` is one step
  | zero =>
    rw [heightAt_zero hzero b, Function.iterate_one, exchangeAt_zero hzero hlam]
  -- at level `k + 1` the cell sits in a level-`k` parent, and its return is a stack of parents
  | succ k ih =>
    have hS := isRauzyStep_at (P := P) (γ := γ) (p := p) hstep hOK k
    have hne (e : Bool) : (TowerStep.datumAt P γ k).last e ≠ (TowerStep.datumAt P γ k).last (!e) :=
        datumAt_last_ne (P := P) (γ := γ) hP hn k e
    have hcell : y ∈ cellAt (TowerStep.datumAt P γ k) [p k] (TowerStep.lamAt P γ lam k) b := by
      rw [← levelCell_succ hstep]; exact hy
    have hfr : (TowerStep.exchangeAt P γ lam k)^[IETDatum₂.Path.height
        (TowerStep.datumAt P γ k) [(p k)] b] y
        = TowerStep.exchangeAt P γ lam (k + 1) y := by
      simp only [TowerStep.exchangeAt, datumAt_succ hstep, lamAt_succ hstep]
      cases hp : p k with
      | false =>
        rw [hp] at hS hcell
        exact firstReturn_false _ hne _ hS b hcell
      | true =>
        rw [hp] at hS hcell
        exact firstReturn_true _ hne _ hS b hcell
    -- a letter at the head of the top cell has height two, so its return is `exchangeAt k` twice
    by_cases hb : b = (TowerStep.datumAt P γ k).last (!(p k))
    · have hg2 : IETDatum₂.Path.height (TowerStep.datumAt P γ k) [(p k)] b = 2 := by
        rw [height_singleton_eq _ hne, hb]; simp
      have key : TowerStep.exchangeAt P γ lam (k + 1) y
          = TowerStep.exchangeAt P γ lam k (TowerStep.exchangeAt P γ lam k y) := by
        rw [← hfr, hg2, ← one_add_one_eq_two, Function.iterate_add_apply,
          Function.iterate_one]
      have hHs : TowerStep.heightAt P γ (k + 1) b
          = TowerStep.heightAt P γ k b
            + TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last (p k)) := by
        rw [heightAt_succ hP hn hstep]; simp only [ite_eq_left hb]
    -- and its height is the sum of the heights of the two floors that the step exchanges
      cases hp : p k with
      | false =>
        have hb' : b = (TowerStep.datumAt P γ k).last true := by rw [hb, hp]; rfl
        rw [hb'] at hy hHs ⊢
        rw [hp] at hHs
        have hy1 : y ∈ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last true) :=
          levelCell_succ_sub_false hstep k _ hp hy
        have hmem : TowerStep.exchangeAt P γ lam k y
            ∈ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last false) :=
          exchangeAt_image_false_scd (P := P) (γ := γ) (p := p) hstep hOK k hp ⟨y, hy, rfl⟩
        have i1 := ih ((TowerStep.datumAt P γ k).last true) y hy1
        have i2 := ih ((TowerStep.datumAt P γ k).last false) (TowerStep.exchangeAt P γ lam k y) hmem
        have hcomm : TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last false)
            + TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)
            = TowerStep.heightAt P γ (k + 1) ((TowerStep.datumAt P γ k).last true) := by
          rw [hHs, Nat.add_comm]
        calc (⇑(P.toIET lam))^[TowerStep.heightAt P γ (k + 1)
              ((TowerStep.datumAt P γ k).last true)] y
            = (⇑(P.toIET lam))^[TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last false)
                + TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)] y := by
              rw [← hcomm]
          _ = (⇑(P.toIET lam))^[TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last false)]
                ((⇑(P.toIET lam))^[TowerStep.heightAt P γ k
                  ((TowerStep.datumAt P γ k).last true)] y) := by
              rw [Function.iterate_add_apply]
          _ = (⇑(P.toIET lam))^[TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last false)]
                (TowerStep.exchangeAt P γ lam k y) := by rw [i1]
          _ = TowerStep.exchangeAt P γ lam k (TowerStep.exchangeAt P γ lam k y) := i2
          _ = TowerStep.exchangeAt P γ lam (k + 1) y := key.symm
      | true =>
        have hb' : b = (TowerStep.datumAt P γ k).last false := by rw [hb, hp]; rfl
        rw [hb'] at hy hHs ⊢
        rw [hp] at hHs
        have hy1 : y ∈ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last true) :=
          levelCell_succ_sub_true_scd (P := P) (γ := γ) (p := p) hstep hOK k hp hy
        have hmem : TowerStep.exchangeAt P γ lam k y
            ∈ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last false) :=
          exchangeAt_image_true_scd (P := P) (γ := γ) (p := p) hstep hOK k hp ⟨y, hy, rfl⟩
        have i1 := ih ((TowerStep.datumAt P γ k).last true) y hy1
        have i2 := ih ((TowerStep.datumAt P γ k).last false) (TowerStep.exchangeAt P γ lam k y) hmem
        calc (⇑(P.toIET lam))^[TowerStep.heightAt P γ (k + 1)
              ((TowerStep.datumAt P γ k).last false)] y
            = (⇑(P.toIET lam))^[TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last false)
                + TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)] y := by
              rw [← hHs]
          _ = (⇑(P.toIET lam))^[TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last false)]
                ((⇑(P.toIET lam))^[TowerStep.heightAt P γ k
                  ((TowerStep.datumAt P γ k).last true)] y) := by
              rw [Function.iterate_add_apply]
          _ = (⇑(P.toIET lam))^[TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last false)]
                (TowerStep.exchangeAt P γ lam k y) := by rw [i1]
          _ = TowerStep.exchangeAt P γ lam k (TowerStep.exchangeAt P γ lam k y) := i2
          _ = TowerStep.exchangeAt P γ lam (k + 1) y := key.symm
    -- a letter the step does not move keeps its height and has its cell shrunk
    · have hg1 : IETDatum₂.Path.height (TowerStep.datumAt P γ k) [(p k)] b = 1 := by
        rw [height_singleton_eq _ hne]; simp only [ite_eq_right hb, add_zero]
      have key : TowerStep.exchangeAt P γ lam (k + 1) y = TowerStep.exchangeAt P γ lam k y := by
        rw [← hfr, hg1, Function.iterate_one]
      have hHs : TowerStep.heightAt P γ (k + 1) b = TowerStep.heightAt P γ k b := by
        rw [heightAt_succ hP hn hstep]; simp only [ite_eq_right hb, add_zero]
      have hy1 : y ∈ TowerStep.levelCell P γ lam k b := by
        cases hp : p k with
        | false => exact levelCell_succ_sub_false hstep k b hp hy
        | true => exact levelCell_succ_sub_true hstep hOK k b hp (by rw [hp] at hb; exact hb) hy
      have i1 := ih b y hy1
      rw [hHs, key]
      exact i1

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
variable {P : IETDatum₂ α n} {γ : ℕ → List Bool} {p : ℕ → Bool} {lam : α → ℝ≥0}

/-! ## 9. `T` is a translation on every level-`k` cell, up to the level-`k` height -/

/-- **Every floor is a translate of its cell.**  For `j ≤ heightAt k b` the `j`-th iterate of the
exchange is a translation on the level-`k` cell of `b`: there is a `τ` with `T^[j] y = y + τ`
for every `y` in that cell. -/
theorem exists_iterate_eq_add_on_cell (hzero : γ 0 = []) (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (hP : P.Irreducible) (hn : 2 ≤ n) (hlam : lam ∈ simplex α)
    (hOK : ∀ k, IsRauzyPath P lam (γ k)) (k : ℕ) (b : α) (j : ℕ)
    (hj : j ≤ TowerStep.heightAt P γ k b) :
    ∃ τ : ℝ, ∀ y ∈ TowerStep.levelCell P γ lam k b, (⇑(P.toIET lam))^[j] y = y + τ := by
  induction k generalizing b j with
  -- at level zero the iterate is the identity or one step of `P`, a translation on a cell
  | zero =>
    rw [heightAt_zero hzero b] at hj
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with h0 | h1
    · refine ⟨0, fun y _ => ?_⟩
      rw [h0, Function.iterate_zero_apply, add_zero]
    · refine ⟨translationVector P.perm (P.lengthsInBottom lam) (P.piBottom b), fun y hy => ?_⟩
      rw [h1, Function.iterate_one, coe_toIET hlam]
      have hy1 : y ∈ Set.Ico (0 : ℝ) 1 := levelCell_sub_one hzero hstep hlam 0 b hy
      have hy' : y ∈ Set.Ico (0 : ℝ) (totalLength (P.lengthsInBottom lam)) := by
        rw [totalLength_eq_one hlam]; exact hy1
      have hcell : y ∈ cellOf P lam b := by
        rw [← levelCell_zero hzero b]; exact hy
      have hidx : idx (P.lengthsInBottom lam) y hy'.1 = P.piBottom b :=
        idx_eq (P.lengthsInBottom lam) hy' hcell.1 hcell.2
      rw [mkIETFun_zero_of_mem hy', hidx]
  | succ k ih =>
    have hne (e : Bool) : (TowerStep.datumAt P γ k).last e ≠ (TowerStep.datumAt P γ k).last (!e) :=
        datumAt_last_ne (P := P) (γ := γ) hP hn k e
    -- a letter moved by the step has its height split over the two floors the step exchanges
    by_cases hb : b = (TowerStep.datumAt P γ k).last (!(p k))
    · have hHs : TowerStep.heightAt P γ (k + 1) b
          = TowerStep.heightAt P γ k b
            + TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last (p k)) := by
        rw [heightAt_succ hP hn hstep]; simp only [ite_eq_left hb]
      cases hp : p k with
      | false =>
        have hb' : b = (TowerStep.datumAt P γ k).last true := by rw [hb, hp]; rfl
        rw [hb'] at hj hHs ⊢
        rw [hp] at hHs
        have hsub : TowerStep.levelCell P γ lam (k + 1) ((TowerStep.datumAt P γ k).last true)
            ⊆ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last true) :=
          levelCell_succ_sub_false hstep k _ hp
        have himg : TowerStep.exchangeAt P γ lam k ''
            TowerStep.levelCell P γ lam (k + 1) ((TowerStep.datumAt P γ k).last true)
            ⊆ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last false) :=
          exchangeAt_image_false_scd (P := P) (γ := γ) (p := p) hstep hOK k hp
        -- inside the source floor the cell is smaller and the same translation works
        by_cases hj1 : j ≤ TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)
        · obtain ⟨τ, hτ⟩ := ih _ j hj1
          exact ⟨τ, fun y hy => hτ y (hsub hy)⟩
        -- past it, `j` is a stack of the source floor plus a point of its image: translations add
        · push Not at hj1
          have hjp : j - TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)
              ≤ TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last false) := by
            rw [hHs] at hj; omega
          obtain ⟨τ1, hτ1⟩ := ih ((TowerStep.datumAt P γ k).last true)
            (TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)) le_rfl
          obtain ⟨τ2, hτ2⟩ := ih ((TowerStep.datumAt P γ k).last false)
            (j - TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)) hjp
          refine ⟨τ1 + τ2, fun y hy => ?_⟩
          have hmem1 : y ∈ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last true) :=
            hsub hy
          have hmem2 : TowerStep.exchangeAt P γ lam k y
              ∈ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last false) :=
              himg ⟨y, hy, rfl⟩
          have hfr := FR_all hzero hstep hP hn hlam hOK k _ y hmem1
          have e1 : j = (j - TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true))
              + TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true) := by omega
          rw [e1, Function.iterate_add_apply, hfr, hτ2 _ hmem2, ← hfr, hτ1 y hmem1]
          ring
      | true =>
        have hb' : b = (TowerStep.datumAt P γ k).last false := by rw [hb, hp]; rfl
        rw [hb'] at hj hHs ⊢
        rw [hp] at hHs
        have hsub : TowerStep.levelCell P γ lam (k + 1) ((TowerStep.datumAt P γ k).last false)
            ⊆ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last true) :=
          levelCell_succ_sub_true_scd (P := P) (γ := γ) (p := p) hstep hOK k hp
        have himg : TowerStep.exchangeAt P γ lam k ''
            TowerStep.levelCell P γ lam (k + 1) ((TowerStep.datumAt P γ k).last false)
            ⊆ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last false) :=
          exchangeAt_image_true_scd (P := P) (γ := γ) (p := p) hstep hOK k hp
        by_cases hj1 : j ≤ TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)
        · obtain ⟨τ, hτ⟩ := ih _ j hj1
          exact ⟨τ, fun y hy => hτ y (hsub hy)⟩
        · push Not at hj1
          have hjp : j - TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)
              ≤ TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last false) := by
            rw [hHs] at hj; omega
          obtain ⟨τ1, hτ1⟩ := ih ((TowerStep.datumAt P γ k).last true)
            (TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)) le_rfl
          obtain ⟨τ2, hτ2⟩ := ih ((TowerStep.datumAt P γ k).last false)
            (j - TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)) hjp
          refine ⟨τ1 + τ2, fun y hy => ?_⟩
          have hmem1 : y ∈ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last true) :=
            hsub hy
          have hmem2 : TowerStep.exchangeAt P γ lam k y
              ∈ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last false) :=
              himg ⟨y, hy, rfl⟩
          have hfr := FR_all hzero hstep hP hn hlam hOK k _ y hmem1
          have e1 : j = (j - TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true))
              + TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true) := by omega
          rw [e1, Function.iterate_add_apply, hfr, hτ2 _ hmem2, ← hfr, hτ1 y hmem1]
          ring
    · have hHs : TowerStep.heightAt P γ (k + 1) b = TowerStep.heightAt P γ k b := by
        rw [heightAt_succ hP hn hstep]; simp only [ite_eq_right hb, add_zero]
      -- a letter the step does not move keeps its height and has its cell shrunk
      have hsub : TowerStep.levelCell P γ lam (k + 1) b ⊆ TowerStep.levelCell P γ lam k b := by
        cases hp : p k with
        | false => exact levelCell_succ_sub_false hstep k b hp
        | true =>
          refine levelCell_succ_sub_true hstep hOK k b hp (fun hh => hb ?_)
          rw [hp]; exact hh
      rw [hHs] at hj
      obtain ⟨τ, hτ⟩ := ih b j hj
      exact ⟨τ, fun y hy => hτ y (hsub hy)⟩

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
variable {P : IETDatum₂ α n} {γ : ℕ → List Bool} {p : ℕ → Bool} {lam : α → ℝ≥0}

/-! ## 10. Elementary rewriting lemmas for the bundled notation -/

theorem levelCell_eq_Ico (k : ℕ) (b : α) :
    TowerStep.levelCell P γ lam k b
      = Set.Ico (leftEnd ((TowerStep.datumAt P γ k).lengthsInBottom (TowerStep.lamAt P γ lam k))
          ((TowerStep.datumAt P γ k).piBottom b))
        (upperEnd ((TowerStep.datumAt P γ k).lengthsInBottom (TowerStep.lamAt P γ lam k))
          ((TowerStep.datumAt P γ k).piBottom b)) := (rfl)

/-! ## 11. Each floor is an interval of the level-`k` length -/

theorem image_Ico_of_translation {A : Set ℝ} {u v τ : ℝ} (hA : A = Set.Ico u v)
    {f : ℝ → ℝ} (hf : ∀ y ∈ A, f y = y + τ) :
    f '' A = Set.Ico (u + τ) (v + τ) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hf y hy]
    have hy' : y ∈ Set.Ico u v := hA ▸ hy
    exact ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
  · rintro ⟨h1, h2⟩
    have hmem : z - τ ∈ A := by rw [hA]; exact ⟨by linarith, by linarith⟩
    exact ⟨z - τ, hmem, by rw [hf _ hmem]; ring⟩

theorem floor_Ico (hzero : γ 0 = []) (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (hP : P.Irreducible) (hn : 2 ≤ n) (hlam : lam ∈ simplex α)
    (hOK : ∀ k, IsRauzyPath P lam (γ k)) (k : ℕ) (b : α) (j : ℕ)
    (hj : j ≤ TowerStep.heightAt P γ k b) :
    ∃ u v : ℝ, (⇑(P.toIET lam))^[j] '' TowerStep.levelCell P γ lam k b = Set.Ico u v ∧
      v - u = (TowerStep.lamAt P γ lam k b : ℝ) := by
  obtain ⟨τ, hτ⟩ := exists_iterate_eq_add_on_cell hzero hstep hP hn hlam hOK k b j hj
  refine ⟨leftEnd ((TowerStep.datumAt P γ k).lengthsInBottom (TowerStep.lamAt P γ lam k))
        ((TowerStep.datumAt P γ k).piBottom b) + τ,
      upperEnd ((TowerStep.datumAt P γ k).lengthsInBottom (TowerStep.lamAt P γ lam k))
        ((TowerStep.datumAt P γ k).piBottom b) + τ,
      image_Ico_of_translation (levelCell_eq_Ico (P := P) (γ := γ) (lam := lam) k b)
        (fun y hy => hτ y hy), ?_⟩
  rw [upperEnd_eq, IETDatum₂.lengthsInBottom, Equiv.symm_apply_apply]
  ring

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
variable {P : IETDatum₂ α n} {γ : ℕ → List Bool} {p : ℕ → Bool} {lam : α → ℝ≥0}

/-! ## 12. The total length identity `∑ h λ = 1` -/

theorem heightAt_coe_eq (k : ℕ) (b : α) :
    (TowerStep.heightAt P γ k b : ℝ) = ∑ a, ((IETDatum₂.Path.Q P (γ k) a b).toNat : ℝ) := by
  simp only [TowerStep.heightAt, IETDatum₂.Path.height]
  push_cast
  rfl

/-- **The tower has total mass `1`**: the lengths of the floors of the level-`k` base, counted
with their heights, add up to `1`.  This is the unimodularity of the path matrix read on the
renormalised length vector. -/
theorem sum_height_mul_len_eq_one (hP : P.Irreducible) (hn : 2 ≤ n) (hlam : lam ∈ simplex α)
    (hOK : ∀ k, IsRauzyPath P lam (γ k)) (k : ℕ) :
    (∑ b, (TowerStep.heightAt P γ k b : ℝ) * (TowerStep.lamAt P γ lam k b : ℝ)) = 1 := by
  have hQ (a) (b : α) : (0 : ℤ) ≤ IETDatum₂.Path.Q P (γ k) a b := IETDatum₂.Path.Q_nonneg P (γ k) a
      b
  calc (∑ b, (TowerStep.heightAt P γ k b : ℝ) * (TowerStep.lamAt P γ lam k b : ℝ))
      = ∑ b, (∑ a, ((IETDatum₂.Path.Q P (γ k) a b).toNat : ℝ))
          * (TowerStep.lamAt P γ lam k b : ℝ) :=
        Finset.sum_congr rfl (fun b _ => by rw [heightAt_coe_eq])
    _ = ∑ b, ∑ a, ((IETDatum₂.Path.Q P (γ k) a b).toNat : ℝ)
          * (TowerStep.lamAt P γ lam k b : ℝ) :=
        Finset.sum_congr rfl (fun b _ => Finset.sum_mul _ _ _)
    _ = ∑ a, ∑ b, ((IETDatum₂.Path.Q P (γ k) a b).toNat : ℝ)
          * (TowerStep.lamAt P γ lam k b : ℝ) := Finset.sum_comm
    _ = ∑ a, (lam a : ℝ) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        exact renorm_apply P hP hn (hOK k) a
    _ = 1 := by
        have h := congrArg (fun t : ℝ≥0 => (t : ℝ)) hlam
        push_cast at h
        exact h

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
variable {P : IETDatum₂ α n} {γ : ℕ → List Bool} {p : ℕ → Bool} {lam : α → ℝ≥0}

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
variable {P : IETDatum₂ α n} {γ : ℕ → List Bool} {p : ℕ → Bool} {lam : α → ℝ≥0}

/-! ## 13. The composite covering step -/

theorem heightAt_succ_ne (hP : P.Irreducible) (hn : 2 ≤ n)
    (hstep : ∀ k, γ (k + 1) = γ k ++ [p k]) (k : ℕ) (e : Bool) (hp : p k = e)
    {c : α} (hc : c ≠ (TowerStep.datumAt P γ k).last (!e)) :
    TowerStep.heightAt P γ (k + 1) c = TowerStep.heightAt P γ k c := by
  rw [heightAt_succ hP hn hstep, hp]
  cases e with
  | false =>
    simp only [Bool.not_false] at hc ⊢
    rw [ite_eq_right hc, add_zero]
  | true =>
    simp only [Bool.not_true] at hc ⊢
    rw [ite_eq_right hc, add_zero]

theorem heightAt_succ_scd (hP : P.Irreducible) (hn : 2 ≤ n)
    (hstep : ∀ k, γ (k + 1) = γ k ++ [p k]) (k : ℕ) (e : Bool) (hp : p k = e) :
    TowerStep.heightAt P γ (k + 1) ((TowerStep.datumAt P γ k).last (!e))
      = TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last (!e))
        + TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last e) := by
  rw [heightAt_succ hP hn hstep, hp]
  cases e with
  | false => rw [Bool.not_false, ite_eq_left rfl]
  | true => rw [Bool.not_true, ite_eq_left rfl]

theorem cover_step_false_of_tower (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (hP : P.Irreducible) (hn : 2 ≤ n) (hlam : lam ∈ simplex α)
    (hOK : ∀ k, IsRauzyPath P lam (γ k)) (k : ℕ) (hp : p k = false) {x : ℝ}
    (hx : ∃ (b : α) (j : ℕ), j < TowerStep.heightAt P γ k b ∧
      x ∈ (⇑(P.toIET lam))^[j] '' TowerStep.levelCell P γ lam k b) :
    ∃ (b : α) (j : ℕ), j < TowerStep.heightAt P γ (k + 1) b ∧
      x ∈ (⇑(P.toIET lam))^[j] '' TowerStep.levelCell P γ lam (k + 1) b := by
  have hstep' : γ (k + 1) = γ k ++ [false] := by rw [hstep k, hp]
  have hOK' : IsRauzyPath P lam (γ k ++ [false]) := hstep' ▸ hOK (k + 1)
  have h := cover_step_false (P := P) (lam := lam) hP hn hlam (γ := γ k) hOK' hx
  simpa [TowerStep.heightAt, TowerStep.levelCell, hstep k, hp] using h

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
variable {P : IETDatum₂ α n} {γ : ℕ → List Bool} {p : ℕ → Bool} {lam : α → ℝ≥0}

theorem cover_step_true_of_tower (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (hP : P.Irreducible) (hn : 2 ≤ n) (hlam : lam ∈ simplex α)
    (hOK : ∀ k, IsRauzyPath P lam (γ k)) (k : ℕ) (hp : p k = true) {x : ℝ}
    (hx : ∃ (b : α) (j : ℕ), j < TowerStep.heightAt P γ k b ∧
      x ∈ (⇑(P.toIET lam))^[j] '' TowerStep.levelCell P γ lam k b) :
    ∃ (b : α) (j : ℕ), j < TowerStep.heightAt P γ (k + 1) b ∧
      x ∈ (⇑(P.toIET lam))^[j] '' TowerStep.levelCell P γ lam (k + 1) b := by
  have hstep' : γ (k + 1) = γ k ++ [true] := by rw [hstep k, hp]
  have hOK' : IsRauzyPath P lam (γ k ++ [true]) := hstep' ▸ hOK (k + 1)
  have h := cover_step_true (P := P) (lam := lam) hP hn hlam (γ := γ k) hOK' hx
  simpa [TowerStep.heightAt, TowerStep.levelCell, hstep k, hp] using h

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
variable {P : IETDatum₂ α n} {γ : ℕ → List Bool} {p : ℕ → Bool} {lam : α → ℝ≥0}

/-! ## 14. The level-`k` floors cover `[0,1)` -/

/-- **The level-`k` floors cover `[0, 1)`**: every point of `[0, 1)` lies on the `j`-th floor of
the tower over some letter `b`, with `j < heightAt k b`. -/
theorem Ico_subset_iUnion_iterate_image_cell (hzero : γ 0 = [])
    (hstep : ∀ k, γ (k + 1) = γ k ++ [p k]) (hP : P.Irreducible) (hn : 2 ≤ n)
    (hlam : lam ∈ simplex α) (hOK : ∀ k, IsRauzyPath P lam (γ k)) (k : ℕ) (x : ℝ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
      ∃ (b : α) (j : ℕ), j < TowerStep.heightAt P γ k b ∧
        x ∈ (⇑(P.toIET lam))^[j] '' TowerStep.levelCell P γ lam k b := by
  induction k generalizing x with
  | zero =>
    have hx' : x ∈ Set.Ico (0 : ℝ) (∑ i, (P.lengthsInBottom lam i : ℝ)) := by
      have h1 : (∑ i, (P.lengthsInBottom lam i : ℝ)) = ∑ a, (lam a : ℝ) :=
        totalLength_lengthsInBottom P lam
      rw [h1]
      have h2 := congrArg (fun t : ℝ≥0 => (t : ℝ)) hlam
      push_cast at h2
      rw [h2]
      exact hx
    refine ⟨P.piBottom.symm (idx (P.lengthsInBottom lam) x hx'.1), 0, ?_, ?_⟩
    · rw [heightAt_zero hzero]
      exact Nat.one_pos
    · refine ⟨x, ?_, by simp⟩
      rw [levelCell_zero hzero]
      exact mem_cellOf_idx P lam hx'
  | succ k ih =>
    cases hp : p k with
    | false => exact cover_step_false_of_tower hstep hP hn hlam hOK k hp (ih x hx)
    | true => exact cover_step_true_of_tower hstep hP hn hlam hOK k hp (ih x hx)

/-! ## 15. Refinement of the level-`k+1` floors in the level-`k` floors -/

theorem refine_step_false (hzero : γ 0 = []) (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (hP : P.Irreducible) (hn : 2 ≤ n) (hlam : lam ∈ simplex α)
    (hOK : ∀ k, IsRauzyPath P lam (γ k)) (k : ℕ) (hp : p k = false) (b : α) (J : ℕ)
    (hJ : J < TowerStep.heightAt P γ (k + 1) b) :
    ∃ (c : α) (j : ℕ), j < TowerStep.heightAt P γ k c ∧
      (⇑(P.toIET lam))^[J] '' TowerStep.levelCell P γ lam (k + 1) b
        ⊆ (⇑(P.toIET lam))^[j] '' TowerStep.levelCell P γ lam k c := by
  by_cases hbs : b = (TowerStep.datumAt P γ k).last true
  · subst b
    -- Split the `J`-th floor of level `k + 1` by its origin: the floors of the top cell (index
    -- `J`) and the pushed images of the other cells (index `J - heightAt`), the height split being
    -- `heightAt_succ_scd`.
    have hHs := heightAt_succ_scd (P := P) (γ := γ) hP hn hstep k false hp
    simp only [Bool.not_false] at hHs
    rw [hHs] at hJ
    have hsub : TowerStep.levelCell P γ lam (k + 1) ((TowerStep.datumAt P γ k).last true)
        ⊆ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last true) :=
      levelCell_succ_sub_false hstep k _ hp
    by_cases hJ1 : J < TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)
    · exact ⟨_, J, hJ1, fun z hz => Set.image_mono hsub hz⟩
    · push Not at hJ1
      refine ⟨(TowerStep.datumAt P γ k).last false,
        J - TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true), by omega, ?_⟩
      have himg : TowerStep.exchangeAt P γ lam k ''
          TowerStep.levelCell P γ lam (k + 1) ((TowerStep.datumAt P γ k).last true)
          ⊆ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last false) :=
        exchangeAt_image_false_scd (P := P) (γ := γ) (p := p) hstep hOK k hp
      rintro z ⟨x, hx, rfl⟩
      have hFRx := FR_all hzero hstep hP hn hlam hOK k _ x (hsub hx)
      have hmem : TowerStep.exchangeAt P γ lam k x
          ∈ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last false) :=
            himg ⟨x, hx, rfl⟩
      refine ⟨TowerStep.exchangeAt P γ lam k x, hmem, ?_⟩
      have he : J = (J - TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true))
          + TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true) := by omega
      calc (⇑(P.toIET lam))^[J - TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)]
            (TowerStep.exchangeAt P γ lam k x)
          = (⇑(P.toIET lam))^[J - TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)]
              ((⇑(P.toIET lam))^[TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)]
                x) := by rw [hFRx]
        _ = (⇑(P.toIET lam))^[(J - TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true))
              + TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)] x :=
            (by rw [Function.iterate_add_apply])
        _ = (⇑(P.toIET lam))^[J] x :=
            congrArg (fun n => (⇑(P.toIET lam))^[n] x) he.symm
  · have hHs := heightAt_succ_ne (P := P) (γ := γ) hP hn hstep k false hp
      (fun h => hbs (by simpa using h))
    rw [hHs] at hJ
    have hsub : TowerStep.levelCell P γ lam (k + 1) b ⊆ TowerStep.levelCell P γ lam k b :=
      levelCell_succ_sub_false hstep k b hp
    exact ⟨b, J, hJ, fun z hz => Set.image_mono hsub hz⟩

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
variable {P : IETDatum₂ α n} {γ : ℕ → List Bool} {p : ℕ → Bool} {lam : α → ℝ≥0}

theorem refine_step_true (hzero : γ 0 = []) (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (hP : P.Irreducible) (hn : 2 ≤ n) (hlam : lam ∈ simplex α)
    (hOK : ∀ k, IsRauzyPath P lam (γ k)) (k : ℕ) (hp : p k = true) (b : α) (J : ℕ)
    (hJ : J < TowerStep.heightAt P γ (k + 1) b) :
    ∃ (c : α) (j : ℕ), j < TowerStep.heightAt P γ k c ∧
      (⇑(P.toIET lam))^[J] '' TowerStep.levelCell P γ lam (k + 1) b
        ⊆ (⇑(P.toIET lam))^[j] '' TowerStep.levelCell P γ lam k c := by
  by_cases hbs : b = (TowerStep.datumAt P γ k).last false
  · subst b
    have hHs := heightAt_succ_scd (P := P) (γ := γ) hP hn hstep k true hp
    simp only [Bool.not_true] at hHs
    rw [hHs] at hJ
    have hsub : TowerStep.levelCell P γ lam (k + 1) ((TowerStep.datumAt P γ k).last false)
        ⊆ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last true) :=
      levelCell_succ_sub_true_scd (P := P) (γ := γ) (p := p) hstep hOK k hp
    by_cases hJ1 : J < TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)
    · exact ⟨_, J, hJ1, Set.image_mono hsub⟩
    · push Not at hJ1
      refine ⟨(TowerStep.datumAt P γ k).last false,
        J - TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true), by omega, ?_⟩
      have himg : TowerStep.exchangeAt P γ lam k ''
          TowerStep.levelCell P γ lam (k + 1) ((TowerStep.datumAt P γ k).last false)
          ⊆ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last false) :=
        exchangeAt_image_true_scd (P := P) (γ := γ) (p := p) hstep hOK k hp
      rintro z ⟨x, hx, rfl⟩
      have hFRx := FR_all hzero hstep hP hn hlam hOK k _ x (hsub hx)
      have hmem : TowerStep.exchangeAt P γ lam k x
          ∈ TowerStep.levelCell P γ lam k ((TowerStep.datumAt P γ k).last false) :=
            himg ⟨x, hx, rfl⟩
      refine ⟨TowerStep.exchangeAt P γ lam k x, hmem, ?_⟩
      have he : J = (J - TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true))
          + TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true) := by omega
      calc (⇑(P.toIET lam))^[J - TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)]
            (TowerStep.exchangeAt P γ lam k x)
          = (⇑(P.toIET lam))^[J - TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)]
              ((⇑(P.toIET lam))^[TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)]
                x) := by rw [hFRx]
        _ = (⇑(P.toIET lam))^[(J - TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true))
              + TowerStep.heightAt P γ k ((TowerStep.datumAt P γ k).last true)] x :=
            (by rw [Function.iterate_add_apply])
        _ = (⇑(P.toIET lam))^[J] x :=
            congrArg (fun n => (⇑(P.toIET lam))^[n] x) he.symm
  · have hHs := heightAt_succ_ne (P := P) (γ := γ) hP hn hstep k true hp
      (fun h => hbs (by simpa using h))
    rw [hHs] at hJ
    have hsub : TowerStep.levelCell P γ lam (k + 1) b ⊆ TowerStep.levelCell P γ lam k b :=
      levelCell_succ_sub_true hstep hOK k b hp hbs
    exact ⟨b, J, hJ, Set.image_mono hsub⟩

theorem href_all (hzero : γ 0 = []) (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (hP : P.Irreducible) (hn : 2 ≤ n) (hlam : lam ∈ simplex α)
    (hOK : ∀ k, IsRauzyPath P lam (γ k)) (k : ℕ) (A : Set ℝ) (hA : A ∈ floors P lam γ (k + 1)) :
      ∃ B ∈ floors P lam γ k, A ⊆ B := by
  rw [mem_floors_iff] at hA
  obtain ⟨b, J, hJ, rfl⟩ := hA
  cases hp : p k with
  | false =>
    obtain ⟨c, j, hj, hsub⟩ := refine_step_false hzero hstep hP hn hlam hOK k hp b J hJ
    exact ⟨_, (mem_floors_iff k _).mpr ⟨c, j, hj, rfl⟩, hsub⟩
  | true =>
    obtain ⟨c, j, hj, hsub⟩ := refine_step_true hzero hstep hP hn hlam hOK k hp b J hJ
    exact ⟨_, (mem_floors_iff k _).mpr ⟨c, j, hj, rfl⟩, hsub⟩

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
variable {P : IETDatum₂ α n} {γ : ℕ → List Bool} {p : ℕ → Bool} {lam : α → ℝ≥0}

/-! ## 16. The floors of a fixed level are pairwise disjoint -/

/-- The `(b,j)`-floor of the level-`k` tower. -/
noncomputable def FL (P : IETDatum₂ α n) (γ : ℕ → List Bool) (lam : α → ℝ≥0) (k : ℕ)
    (r : Σ b : α, Fin (TowerStep.heightAt P γ k b)) : Set ℝ :=
  (⇑(P.toIET lam))^[(r.2 : ℕ)] '' TowerStep.levelCell P γ lam k r.1

theorem floors_eq_image (k : ℕ) :
    floors P lam γ k = (Finset.univ : Finset (Σ b : α, Fin (TowerStep.heightAt P γ k b))).image
      (FL P γ lam k) := (rfl)

theorem sigma_disjoint (hzero : γ 0 = []) (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (hP : P.Irreducible) (hn : 2 ≤ n) (hlam : lam ∈ simplex α)
    (hOK : ∀ k, IsRauzyPath P lam (γ k)) (k : ℕ)
    (p q : (Σ b : α, Fin (TowerStep.heightAt P γ k b))) (hpq : p ≠ q) :
      Disjoint (FL P γ lam k p) (FL P γ lam k q) := by
  set fr : (Σ b : α, Fin (TowerStep.heightAt P γ k b)) → Set ℝ := FL P γ lam k with hfr
  -- Each floor `fr r` is a half-open interval (`hIco`) of volume `lamAt r` (`hvol`), hence
  -- measurable (`hmeas`), inside `[0,1)` (`hsub`) and finite (`hfin`); the volumes sum to `1`
  -- (`hsum`).  Distinct floors are intervals, so they cannot share a set of positive volume.
  have hIco (r : (Σ b : α, Fin (TowerStep.heightAt P γ k b))) :
    ∃ u v : ℝ, fr r = Set.Ico u v ∧ v - u = (TowerStep.lamAt P γ lam k r.1 : ℝ) := by
    rw [hfr]
    exact floor_Ico hzero hstep hP hn hlam hOK k r.1 (r.2 : ℕ) (le_of_lt r.2.isLt)
  have hvol (r) : volume (fr r) = ENNReal.ofReal (TowerStep.lamAt P γ lam k r.1 : ℝ) := by
    obtain ⟨u, v, h1, h2⟩ := hIco r
    rw [h1, Real.volume_Ico, h2]
  have hfin (r) : volume (fr r) ≠ ⊤ := by rw [hvol r]; exact ENNReal.ofReal_ne_top
  have hbdd (S : Set ℝ) (hS : S ⊆ Set.Ico (0 : ℝ) 1) : volume S ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hS)
    rw [Real.volume_Ico, sub_zero, ENNReal.ofReal_one]
    exact ENNReal.one_ne_top
  have hmeas (r) : MeasurableSet (fr r) := by
    rw [hfr]; exact measurableSet_floor hlam k r.1 (r.2 : ℕ)
  have hsub (r) : fr r ⊆ Set.Ico (0 : ℝ) 1 := by
    rw [hfr]; exact floor_subset_one hzero hstep hlam k r.1 (r.2 : ℕ)
  have hsumR : (∑ r : (Σ b : α, Fin (TowerStep.heightAt P γ k b)),
      (TowerStep.lamAt P γ lam k r.1 : ℝ)) = 1 := by
    have h2 (b : α) :
      (∑ _j : Fin (TowerStep.heightAt P γ k b),
        (TowerStep.lamAt P γ lam k b : ℝ)) = (TowerStep.heightAt P γ k b : ℝ)
          * (TowerStep.lamAt P γ lam k b : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.univ_sigma_univ,
      ← Finset.sum_sigma' (f := fun a (_ : Fin (TowerStep.heightAt P γ k a)) =>
        (TowerStep.lamAt P γ lam k a : ℝ))]
    rw [Finset.sum_congr rfl (fun a _ => h2 a)]
    exact sum_height_mul_len_eq_one hP hn hlam hOK k
  have hsum : (∑ r : (Σ b : α, Fin (TowerStep.heightAt P γ k b)), (volume (fr r)).toReal) = 1 := by
    have h1 (r) : (volume (fr r)).toReal = (TowerStep.lamAt P γ lam k r.1 : ℝ) := by
      rw [hvol r, ENNReal.toReal_ofReal (TowerStep.lamAt P γ lam k r.1).coe_nonneg]
    simp only [h1]
    exact hsumR
  have hunion : (⋃ r : (Σ b : α, Fin (TowerStep.heightAt P γ k b)), fr r) = Set.Ico (0 : ℝ) 1 := by
    refine Set.Subset.antisymm (Set.iUnion_subset hsub) ?_
    intro x hx
    obtain ⟨b, j, hj, hmem⟩ :=
      Ico_subset_iUnion_iterate_image_cell hzero hstep hP hn hlam hOK k x hx
    exact Set.mem_iUnion.mpr ⟨⟨b, ⟨j, hj⟩⟩, hmem⟩
  have key (p : (Σ b : α, Fin (TowerStep.heightAt P γ k b))) :
    volume (fr p ∩ ⋃ r ∈ (Finset.univ :
        Finset (Σ b : α, Fin (TowerStep.heightAt P γ k b))).erase p,
        fr r) = 0 := by
    set G : Set ℝ := ⋃ r ∈ (Finset.univ : Finset
      (Σ b : α, Fin (TowerStep.heightAt P γ k b))).erase p, fr r with hG
    have hsplit : (⋃ r ∈ (Finset.univ : Finset (Σ b : α, Fin (TowerStep.heightAt P γ k b))), fr r)
        = fr p ∪ G := by
      rw [hG]
      conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ p), Finset.set_biUnion_insert]
    have hiunion : (⋃ r : (Σ b : α, Fin (TowerStep.heightAt P γ k b)), fr r)
        = ⋃ r ∈ (Finset.univ : Finset (Σ b : α, Fin (TowerStep.heightAt P γ k b))), fr r := by
      ext x
      simp only [Set.mem_iUnion, exists_prop, Finset.mem_univ, true_and]
    have hGmeas : MeasurableSet G :=
      Finset.measurableSet_biUnion _ (fun r _ => hmeas r)
    have hGsub : G ⊆ Set.Ico (0 : ℝ) 1 := by
      rw [hG]
      exact Set.iUnion₂_subset (fun r _ => hsub r)
    have hUsub : fr p ∪ G ⊆ Set.Ico (0 : ℝ) 1 := by
      rw [← hsplit, ← hiunion]
      exact Set.iUnion_subset hsub
    have hadd : volume (fr p ∪ G) + volume (fr p ∩ G) = volume (fr p) + volume G :=
      measure_union_add_inter (fr p) hGmeas
    have e1 : (volume (fr p ∪ G)).toReal + (volume (fr p ∩ G)).toReal
        = (volume (fr p)).toReal + (volume G).toReal := by
      rw [← ENNReal.toReal_add (hbdd _ hUsub) (ne_top_of_le_ne_top (hfin p)
          (measure_mono (Set.inter_subset_left))),
        ← ENNReal.toReal_add (hfin p) (hbdd _ hGsub), hadd]
    have e2 : (volume (fr p ∪ G)).toReal = 1 := by
      rw [← hsplit, ← hiunion, hunion, Real.volume_Ico]
      norm_num
    have hsumG : (∑ r ∈ (Finset.univ : Finset (Σ b : α, Fin (TowerStep.heightAt P γ k b))).erase p,
        (volume (fr r)).toReal) + (volume (fr p)).toReal = 1 := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ p)]
      exact hsum
    have hle : (volume G).toReal ≤ ∑ r ∈ (Finset.univ : Finset
        (Σ b : α, Fin (TowerStep.heightAt P γ k b))).erase p, (volume (fr r)).toReal := by
      have h := measure_biUnion_finset_le (μ := volume)
        ((Finset.univ : Finset (Σ b : α, Fin (TowerStep.heightAt P γ k b))).erase p) fr
      have hfs : (∑ r ∈ (Finset.univ : Finset (Σ b : α, Fin (TowerStep.heightAt P γ k b))).erase p,
          volume (fr r)) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun r _ => hfin r)
      refine le_trans (ENNReal.toReal_mono hfs h) (le_of_eq ?_)
      exact ENNReal.toReal_sum (fun r _ => hfin r)
    have hx0 : (0 : ℝ) ≤ (volume (fr p ∩ G)).toReal := ENNReal.toReal_nonneg
    have hvolzero : (volume (fr p ∩ G)).toReal = 0 := by linarith
    rcases (ENNReal.toReal_eq_zero_iff _).mp hvolzero with h | h
    · exact h
    · exact absurd h (ne_top_of_le_ne_top (hfin p) (measure_mono (Set.inter_subset_left)))
  have hmem : volume (fr p ∩ fr q) = 0 := by
    refine measure_mono_null ?_ (key p)
    intro x hx
    exact ⟨hx.1, Set.mem_iUnion₂.mpr ⟨q, Finset.mem_erase.mpr
      ⟨fun h => hpq h.symm, Finset.mem_univ q⟩, hx.2⟩⟩
  obtain ⟨u, v, h1, h2⟩ := hIco p
  obtain ⟨u', v', h1', h2'⟩ := hIco q
  have hgoal : fr p ∩ fr q = Set.Ico (u ⊔ u') (v ⊓ v') := by rw [h1, h1', Set.Ico_inter_Ico]
  have hle : v ⊓ v' ≤ u ⊔ u' := by
    by_contra hcon
    push Not at hcon
    have hpos : volume (Set.Ico (u ⊔ u') (v ⊓ v')) ≠ 0 := by
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
    rw [← hgoal] at hpos
    exact hpos hmem
  rw [Set.disjoint_iff_inter_eq_empty, hgoal, Set.Ico_eq_empty_of_le hle]

theorem floors_disjoint (hzero : γ 0 = []) (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (hP : P.Irreducible) (hn : 2 ≤ n) (hlam : lam ∈ simplex α)
    (hOK : ∀ k, IsRauzyPath P lam (γ k)) (k : ℕ) (A : Set ℝ) (hA : A ∈ floors P lam γ k)
    (B : Set ℝ) (hB : B ∈ floors P lam γ k) (hAB : A ≠ B) : Disjoint A B := by
  rw [floors_eq_image] at hA hB
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hB
  exact sigma_disjoint hzero hstep hP hn hlam hOK k p q (fun h => hAB (by rw [h]))

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
variable {P : IETDatum₂ α n} {γ : ℕ → List Bool} {p : ℕ → Bool} {lam : α → ℝ≥0}

/-! ## 17. `TowerTiling` -/

theorem towerTiling (hzero : γ 0 = []) (hstep : ∀ k, γ (k + 1) = γ k ++ [p k])
    (hP : P.Irreducible) (hn : 2 ≤ n) (hlam : lam ∈ simplex α)
    (hOK : ∀ k, IsRauzyPath P lam (γ k)) :
    TowerTiling P lam γ := by
  refine ⟨hOK, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k A hA
    obtain ⟨b, j, -, rfl⟩ := (mem_floors_iff (P := P) (γ := γ) (lam := lam) k A).mp hA
    exact measurableSet_floor hlam k b j
  · intro k A hA
    obtain ⟨b, j, -, rfl⟩ := (mem_floors_iff (P := P) (γ := γ) (lam := lam) k A).mp hA
    exact floor_subset_one hzero hstep hlam k b j
  · intro k A hA B hB hAB
    exact floors_disjoint hzero hstep hP hn hlam hOK k A hA B hB hAB
  · intro k x hx
    obtain ⟨b, j, hj, hmem⟩ :=
      Ico_subset_iUnion_iterate_image_cell hzero hstep hP hn hlam hOK k x hx
    exact ⟨_, (mem_floors_iff (P := P) (γ := γ) (lam := lam) k _).mpr
      ⟨b, j, hj, rfl⟩, hmem⟩
  · intro k A hA
    exact href_all hzero hstep hP hn hlam hOK k A hA
  · intro k A hA
    obtain ⟨b, j, hj, rfl⟩ := (mem_floors_iff (P := P) (γ := γ) (lam := lam) k A).mp hA
    obtain ⟨u, v, huv, hlen⟩ := floor_Ico hzero hstep hP hn hlam hOK k b j (le_of_lt hj)
    exact ⟨b, j, rfl, u, v, huv, hlen⟩

/-- **`TowerTiling` for the greedy Rauzy path.** -/
theorem towerTiling_pathWord (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {lam : α → ℝ≥0} (h0 : lam ∈ IETDatum₂.simplexCyl P [])
    (hstop : ∀ w : List Bool, lam ∉ IETDatum₂.cylStop P w) :
    TowerTiling P lam (IETDatum₂.pathWord P lam) := by
  have hlam : lam ∈ simplex α := ((IETDatum₂.mem_simplexCyl_iff P [] lam).mp h0).1
  have hOK (k) : IsRauzyPath P lam (IETDatum₂.pathWord P lam k) := (isRauzyPath_pathWord
      P hP hn h0 hstop k).1
  exact towerTiling (γ := IETDatum₂.pathWord P lam) (p := IETDatum₂.pathStep P lam)
    (IETDatum₂.pathWord_zero P lam) (IETDatum₂.pathWord_succ P lam) hP hn hlam hOK

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 18. Capstones -/

/-- **`TowerTiling` holds for a.e. `lam`, with the greedy path.**  This is exactly the hypothesis of
`length_injective_of_tower_of_tiling`. -/
theorem ae_towerTiling (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∀ᵐ lam ∂(simplexVolumeOn α), ∃ q : ℕ → Bool,
      (∀ k, IsRauzyPath P lam (pfx q k)) ∧
      (∀ k a, 0 < lamAfter P (pfx q k) lam a) ∧
      TowerTiling P lam (pfx q) := by
  filter_upwards [IETDatum₂.ae_mem_simplexCyl_nil P, IETDatum₂.ae_notMem_cylStop_all P hP hn]
    with lam h0 hstop
  refine ⟨IETDatum₂.pathStep P lam, ?_, ?_, ?_⟩
  · intro k
    rw [IETDatum₂.pfx_pathStep]
    exact (isRauzyPath_pathWord P hP hn h0 hstop k).1
  · intro k a
    rw [IETDatum₂.pfx_pathStep]
    exact (isRauzyPath_pathWord P hP hn h0 hstop k).2 a
  · rw [funext (fun k => IETDatum₂.pfx_pathStep P lam k)]
    exact towerTiling_pathWord P hP hn h0 hstop

omit [DecidableEq α] in
/-- **Injectivity of the length map**: for a.e. length vector, the invariant probability measure of
the exchange is determined by its length vector. This is `length_injective_of_tower_of_tiling` fed
with `ae_towerTiling`. -/
theorem length_injective_of_tower (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∀ᵐ lam ∂(simplexVolumeOn α), ∀ μ ν : ProbabilityMeasure ℝ,
      Invariant μ (P.toIET lam) → Invariant ν (P.toIET lam) →
      (μ : Measure ℝ) (Set.Ico 0 1) = 1 → (ν : Measure ℝ) (Set.Ico 0 1) = 1 →
      lambdaOf μ P lam = lambdaOf ν P lam → μ = ν := by
  classical
  exact length_injective_of_tower_of_tiling P hP hn (ae_towerTiling P hP hn)

end IntervalExchange.RauzyVeech

end
