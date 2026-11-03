/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.RauzyPath
public import IETFree.RauzyVeech.LevyRecurrence

/-!
# The cylinder recurrence: a definite fraction of every cylinder avoiding `Z` makes `Z` null

This file instantiates `LevyRecurrence.levy_recurrence` to the **level-`n` cylinder partition** of
the simplex of length vectors, which is the form in which richness of the greedy path
(`RichPath.richGreedyPath`) uses it.

* the level type is `CylRec.Word k = {w : List Bool // w.length = k}` (finite);
* the level map is `x ↦ IETDatum₂.pathWord P x k`, whose atoms are the level-`k` cylinders
  `IETDatum₂.simplexCyl P w` (`measurableSet_lvl_atom`, `lvl_refine` for the refinement);  the
  boundary where the greedy path is not defined is the null set `Nbad` (`measure_Nbad`);
* the cylinder of a word is the level atom of the path word (`mem_cyl_iff_pathWord`,
  `mem_cyl_append_iff_pathWord`), and the partition refines with the level (`lvl_refine`); the
  members of `push`-families are measurable (`measurableSet_lvl_atom`);
* the two measure facts the recurrence consumes on this partition: a set which agrees with `Z`
  outside `Nbad` has the same measure (`measure_eq_of_sdiff_Nbad_eq`), and the mass of a level atom
  is at most the mass of the simplex (`measure_le_measure_sdiff_Nbad`,
 `simplexVolumeOn_univ`).
-/

@[expose] public section


open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace CylRec

/-! ## 1. Words of a fixed length -/

/-- The finite type of words of length `k`. -/
abbrev Word (k : ℕ) : Type := {w : List Bool // w.length = k}

theorem word_injective (k : ℕ) :
    Function.Injective (fun w : Word k => fun i : Fin k => w.1[i.1]?) := by
  intro w₁ w₂ h
  refine Subtype.ext (List.ext_getElem?' ?_)
  intro j hj
  exact congrFun h ⟨j, by have := w₁.2; have := w₂.2; omega⟩

noncomputable instance (k : ℕ) : Fintype (Word k) :=
  Fintype.ofInjective _ (word_injective k)

instance (k : ℕ) : MeasurableSpace (Word k) := ⊤

/-- Needed by `LevyRecurrence.levy_recurrence` (`[∀ n, MeasurableSingletonClass (Y n)]`). -/
instance (k : ℕ) : MeasurableSingletonClass (Word k) := inferInstance

/-- The level map: the greedy word of length `k`. -/
noncomputable def lvl {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (k : ℕ) (x : α → ℝ≥0) : Word k :=
  ⟨IETDatum₂.pathWord P x k, IETDatum₂.pathWord_length P x k⟩

theorem lvl_coe {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (k : ℕ) (x : α → ℝ≥0) :
    (lvl P k x).1 = IETDatum₂.pathWord P x k := rfl

theorem lvl_eq_iff {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (k : ℕ) (x : α → ℝ≥0) (w : Word k) :
    lvl P k x = w ↔ IETDatum₂.pathWord P x k = w.1 :=
  Subtype.ext_iff

/-! ## 2. Measurability of the levels -/

section Meas

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

theorem measurableSet_pathWord_eq (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∀ (k : ℕ) (w : List Bool), w.length = k →
      MeasurableSet {x : α → ℝ≥0 | IETDatum₂.pathWord P x k = w} := by
  intro k
  induction k with
  | zero =>
    intro w hw
    obtain rfl : w = [] := List.eq_nil_of_length_eq_zero hw
    have h : {x : α → ℝ≥0 | IETDatum₂.pathWord P x 0 = []} = Set.univ := by
      ext x; simp [IETDatum₂.pathWord_zero]
    rw [h]; exact MeasurableSet.univ
  | succ k ih =>
    intro w hw
    rcases List.eq_nil_or_concat w with rfl | ⟨u, b, rfl⟩
    · simp at hw
    · simp only [List.concat_eq_append] at hw ⊢
      have hu : u.length = k := by
        simp only [List.length_append, List.length_singleton] at hw
        omega
      have hstep (x : α → ℝ≥0) :
        IETDatum₂.pathWord P x (k + 1) = u ++ [b] ↔
            (IETDatum₂.pathWord P x k = u ∧ IETDatum₂.pathBranch P x u = b) := by
        rw [IETDatum₂.pathWord_succ]
        constructor
        · intro h
          obtain ⟨h1, h2⟩ := List.append_inj h (by rw [IETDatum₂.pathWord_length, hu])
          refine ⟨h1, ?_⟩
          rw [← h1]
          exact List.singleton_inj.mp h2
        · rintro ⟨h1, h2⟩
          simp only [h1, IETDatum₂.pathStep, h2]
      have hset : {x : α → ℝ≥0 | IETDatum₂.pathWord P x (k + 1) = u ++ [b]} =
          {x : α → ℝ≥0 | IETDatum₂.pathWord P x k = u} ∩
            (if b then IETDatum₂.simplexCyl P (u ++ [true])
              else (IETDatum₂.simplexCyl P (u ++ [true]))ᶜ) := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, hstep x]
        cases b with
        | true => simp [IETDatum₂.pathBranch_eq_true_iff]
        | false => simp [IETDatum₂.pathBranch_eq_false_iff]
      rw [hset]
      refine MeasurableSet.inter (ih u hu) ?_
      by_cases hb : b
      · rw [if_pos hb]
        exact IETDatum₂.measurableSet_simplexCyl P hP hn _
      · rw [if_neg hb]
        exact (IETDatum₂.measurableSet_simplexCyl P hP hn _).compl

theorem measurableSet_lvl (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) (k : ℕ)
    (w : Word k) : MeasurableSet {x : α → ℝ≥0 | lvl P k x = w} := by
  have h : {x : α → ℝ≥0 | lvl P k x = w} =
      {x : α → ℝ≥0 | IETDatum₂.pathWord P x k = w.1} := by
    ext x; exact lvl_eq_iff P k x w
  rw [h]
  exact measurableSet_pathWord_eq P hP hn k w.1 w.2

theorem measurable_lvl (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) (k : ℕ) :
    Measurable (lvl P k) := by
  classical
  intro s _
  have h : lvl P k ⁻¹' s = ⋃ w ∈ s, {x : α → ℝ≥0 | lvl P k x = w} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨fun hx => ⟨lvl P k x, hx, rfl⟩, fun ⟨w, hw, hxw⟩ => hxw ▸ hw⟩
  rw [h]
  exact MeasurableSet.biUnion (f := fun w => {x : α → ℝ≥0 | lvl P k x = w})
    s.toFinite.countable (fun w _ => measurableSet_lvl P hP hn k w)

theorem take_pathWord (P : IETDatum₂ α n) (x : α → ℝ≥0) (k : ℕ) :
    List.take k (IETDatum₂.pathWord P x k ++ [IETDatum₂.pathStep P x k]) =
      IETDatum₂.pathWord P x k := by
  rw [List.take_append_of_le_length (i := k) (l₁ := IETDatum₂.pathWord P x k)
      (l₂ := [IETDatum₂.pathStep P x k]) (by rw [IETDatum₂.pathWord_length]),
    List.take_of_length_le (by rw [IETDatum₂.pathWord_length])]

theorem lvl_refine (P : IETDatum₂ α n) (k : ℕ) (x y : α → ℝ≥0)
    (h : lvl P (k + 1) x = lvl P (k + 1) y) : lvl P k x = lvl P k y := by
  have h' := congrArg Subtype.val h
  simp only [lvl_coe] at h'
  rw [IETDatum₂.pathWord_succ, IETDatum₂.pathWord_succ] at h'
  have htake := congrArg (List.take k) h'
  rw [take_pathWord, take_pathWord] at htake
  exact Subtype.ext htake

end Meas

/-! ## 3. The exceptional null set, and the level formulation of the target -/

section Null

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- The exceptional set: the points outside the root cylinder, or in some stopping set.  It is
`simplexVolumeOn α`-null (`measure_Nbad`) but appears in no statement as a hypothesis. -/
def Nbad (P : IETDatum₂ α n) : Set (α → ℝ≥0) :=
  (⋃ γ : List Bool, IETDatum₂.cylStop P γ) ∪ (IETDatum₂.simplexCyl P [])ᶜ

theorem mem_Nbad_iff (P : IETDatum₂ α n) (x : α → ℝ≥0) :
    x ∈ Nbad P ↔ (∃ γ : List Bool, x ∈ IETDatum₂.cylStop P γ) ∨
      x ∉ IETDatum₂.simplexCyl P [] := by
  simp [Nbad]

theorem measure_Nbad (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    simplexVolumeOn α (Nbad P) = 0 := by
  have h1 : simplexVolumeOn α (⋃ γ : List Bool, IETDatum₂.cylStop P γ) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [IETDatum₂.ae_notMem_cylStop_all P hP hn] with x hx
    simp only [Set.mem_iUnion]
    rintro ⟨γ, hγ⟩
    exact hx γ hγ
  have h2 : simplexVolumeOn α ((IETDatum₂.simplexCyl P [])ᶜ) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [IETDatum₂.ae_mem_simplexCyl_nil P] with x hx
    simpa using hx
  exact measure_union_null h1 h2

/-- **Membership in a cylinder is the greedy word condition**, off the null set. -/
theorem mem_cyl_iff_pathWord (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {x : α → ℝ≥0} (hx : x ∉ Nbad P) {w : List Bool} :
    x ∈ IETDatum₂.simplexCyl P w ↔ IETDatum₂.pathWord P x w.length = w := by
  obtain ⟨hstop, hroot⟩ := not_or.mp ((mem_Nbad_iff P x).not.mp hx)
  have hx1 : x ∈ IETDatum₂.simplexCyl P [] := not_not.mp hroot
  have hx2 : ∀ γ : List Bool, x ∉ IETDatum₂.cylStop P γ := by
    intro γ hγ
    exact hstop ⟨γ, hγ⟩
  constructor
  · intro hxw
    have hmem := IETDatum₂.mem_pathWord P hP hn hx1 hx2 w.length
    have hpre := BalancedCylinders.isPrefix_or_isPrefix_of_mem_inter P hP hn w []
      (IETDatum₂.pathWord P x w.length) x (by simpa using hxw) (by simpa using hmem)
    rcases hpre with h | h
    · exact (h.eq_of_length (by rw [IETDatum₂.pathWord_length])).symm
    · exact h.eq_of_length (by rw [IETDatum₂.pathWord_length])
  · intro h
    have hmem := IETDatum₂.mem_pathWord P hP hn hx1 hx2 w.length
    rwa [h] at hmem

/-- The cylinder of `γ₀` at time `m` is the level-`(m + |γ₀|)` condition, off the null set. -/
theorem mem_cyl_append_iff_pathWord (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {x : α → ℝ≥0} (hx : x ∉ Nbad P) (k : ℕ) (γ₀ : List Bool) :
    x ∈ IETDatum₂.simplexCyl P (IETDatum₂.pathWord P x k ++ γ₀) ↔
      IETDatum₂.pathWord P x (k + γ₀.length) = IETDatum₂.pathWord P x k ++ γ₀ := by
  have h := mem_cyl_iff_pathWord P hP hn hx (w := IETDatum₂.pathWord P x k ++ γ₀)
  rwa [List.length_append, IETDatum₂.pathWord_length] at h

/-- Sets that agree outside `Nbad` have the same mass. -/
theorem measure_le_measure_sdiff_Nbad (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (S : Set (α → ℝ≥0)) :
    simplexVolumeOn α S ≤ simplexVolumeOn α (S \ Nbad P) := by
  have hN := measure_Nbad P hP hn
  have hsub : S ⊆ (S \ Nbad P) ∪ Nbad P := by
    intro x hx
    by_cases hxN : x ∈ Nbad P
    · exact Or.inr hxN
    · exact Or.inl ⟨hx, hxN⟩
  calc simplexVolumeOn α S ≤ simplexVolumeOn α ((S \ Nbad P) ∪ Nbad P) := measure_mono hsub
    _ ≤ simplexVolumeOn α (S \ Nbad P) + simplexVolumeOn α (Nbad P) := measure_union_le _ _
    _ = simplexVolumeOn α (S \ Nbad P) := by rw [hN, add_zero]

theorem measure_eq_of_sdiff_Nbad_eq (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {S T : Set (α → ℝ≥0)} (h : S \ Nbad P = T \ Nbad P) :
    simplexVolumeOn α S = simplexVolumeOn α T := by
  have h1 := measure_le_measure_sdiff_Nbad P hP hn S
  have h2 := measure_le_measure_sdiff_Nbad P hP hn T
  have h3 : simplexVolumeOn α (T \ Nbad P) ≤ simplexVolumeOn α S := by
    rw [← h]
    exact measure_mono (Set.sdiff_subset)
  have h4 : simplexVolumeOn α (T \ Nbad P) ≤ simplexVolumeOn α T :=
    measure_mono (Set.sdiff_subset)
  rw [h] at h1
  exact le_antisymm (le_trans h1 h4) (le_trans h2 h3)

end Null

/-! ## 4. `Zlev` is measurable for the σ-algebra generated by the levels -/

section LevMeas

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- The word of length `m + |γ₀|` obtained by appending `γ₀` to a word of length `m`. -/
def push (γ₀ : List Bool) {m : ℕ} (u : Word m) : Word (m + γ₀.length) :=
  ⟨u.1 ++ γ₀, by rw [List.length_append, u.2]⟩

theorem push_coe (γ₀ : List Bool) {m : ℕ} (u : Word m) : (push γ₀ u).1 = u.1 ++ γ₀ := rfl

theorem measurableSet_lvl_atom (P : IETDatum₂ α n) (k : ℕ) (w : Word k) :
    MeasurableSet[⨆ j, MeasurableSpace.comap (lvl P j) ⊤]
      {x : α → ℝ≥0 | lvl P k x = w} := by
  have h1 : MeasurableSet[MeasurableSpace.comap (lvl P k) ⊤]
      {x : α → ℝ≥0 | lvl P k x = w} :=
    MeasurableSpace.measurableSet_comap.mpr ⟨{w}, trivial, rfl⟩
  exact le_iSup (fun j => MeasurableSpace.comap (lvl P j) ⊤) k _ h1

end LevMeas

/-! ## 5. The mass of the whole space -/

section Vol

theorem simplexVolumeOn_univ {α : Type*} [Fintype α] {n : ℕ} (P : IETDatum₂ α n) :
    simplexVolumeOn α (Set.univ : Set (α → ℝ≥0)) = volume (region (n - 1)) := by
  rw [simplexVolumeOn_eq_map P,
    Measure.map_apply (measurable_pi_iff.mpr fun a => measurable_pi_apply (P.piBottom a))
      MeasurableSet.univ]
  simp only [Set.preimage_univ]
  rw [simplexVolume, Measure.map_apply (measurable_simplexMap n) MeasurableSet.univ]
  simp only [Set.preimage_univ, Measure.restrict_apply_univ]
  rfl

end Vol

end CylRec

end
