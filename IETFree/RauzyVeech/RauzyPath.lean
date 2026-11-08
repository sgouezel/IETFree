/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.Nesting
public import IETFree.RauzyVeech.PrefixWord

/-!
# The greedy Rauzy–Veech path of a length vector

For `simplexVolumeOn α`-almost every length vector the greedy choice of the type of the next step
gives an infinite type sequence all of whose prefixes are path cylinders.  The
ingredients, none assumed:

* `ae_pos_simplexVolumeOn` (and `ae_pos_simplexVolume_fin`): a.e. `x` is strictly positive on every
  letter — this is where the boundary of the simplex is excluded, since `simplexCyl P []` is the
  *open* simplex;
* `IETDatum₂.pathBranch`, `IETDatum₂.pathStep`, `IETDatum₂.pathWord`: the greedy branch and the word
  it reads, with `mem_pathWord` (the path is in its own cylinder as long as no stopping time is
  met), `mem_pathWord_of_notMem_cylStop`, `pfx_pathStep`, and `ae_notMem_cylStop_all` (a.e. point
  meets no stopping time at any time);
* `simplexCyl_pfx_succ_subset`: the cylinders along the path are nested.
-/

open MeasureTheory IntervalExchange.RauzyVeech IntervalExchange.IETDatum₂
open scoped BigOperators ENNReal NNReal

@[expose] public section

namespace IntervalExchange.RauzyVeech

/-!
# Almost every point of the simplex is strictly positive

`simplexCyl P []` is the set of *strictly positive* points of the simplex (`cone (Q [])` with
`Q [] = 1`), so the a.e. infinite-path conclusion needs the a.e. strict positivity of every
coordinate for `simplexVolumeOn α`.

The proof is short because `simplexVolume d` is, by definition, the image of the Lebesgue measure on
the free region `simplexRegion d` under the parametrisation `simplexMap d`, and `simplexMap d` takes
**strictly positive** values on the free region: the free coordinates are `> 0` there and the last
one is `1 - ∑` with `∑ < 1`.  So strict positivity holds not only a.e. but *everywhere* on the
support; no hyperplane-nullity argument is needed. Main results: * `ae_pos_simplexVolume_fin` — a.e.
`l : Fin d → ℝ≥0` has `0 < l i`, for each `i`; * `ae_pos_simplexVolumeOn` — a.e. `x` w.r.t.
`simplexVolumeOn α` has `0 < x a` for **all** `a`. -/

/-- **Strict positivity in free coordinates.**  For every `d` and every `i : Fin d`, almost every
`l` for `simplexVolume d` satisfies `0 < l i`.  `simplexVolume d` is carried by the image of the
free region, and on that image every coordinate is strictly positive (`simplexMap_castSucc`,
`simplexMap_last`). -/
theorem ae_pos_simplexVolume_fin {d : ℕ} (i : Fin d) :
    ∀ᵐ l ∂(simplexVolume d), 0 < l i := by
  have hd : d ≠ 0 := by
    rintro rfl
    exact i.elim0
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  rw [simplexVolume]
  refine (ae_map_iff (f := simplexMap (m + 1)) (μ := volume.restrict (simplexRegion (m + 1)))
    (measurable_simplexMap (m + 1)).aemeasurable ?_).mpr ?_
  · exact measurableSet_lt measurable_const (measurable_pi_apply i)
  · filter_upwards [ae_restrict_mem (measurableSet_simplexRegion (m + 1))] with v hv
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | hlast
    · rw [simplexMap_castSucc, Real.toNNReal_pos]
      exact hv.1 j
    · rw [hlast, simplexMap_last, Real.toNNReal_pos]
      have h : ∑ j : Fin m, v j < 1 := hv.2
      linarith

/-- **Strict positivity for the alphabet measure.**  Almost every `x` for `simplexVolumeOn α` has
all its coordinates strictly positive.  Transported from `ae_pos_simplexVolume_fin` along the
reindexing `Fintype.equivFin α` that defines `simplexVolumeOn`; the index set `α` is finite, so
`ae_all_iff` applies. -/
theorem ae_pos_simplexVolumeOn (α : Type*) [Fintype α] :
    ∀ᵐ x ∂(simplexVolumeOn α), ∀ a : α, 0 < x a := by
  have hmeas : Measurable
      (fun l : Fin (Fintype.card α) → ℝ≥0 => fun a => l (Fintype.equivFin α a)) := by
    refine measurable_pi_iff.mpr fun a => ?_
    exact measurable_pi_apply (Fintype.equivFin α a)
  have hset : MeasurableSet {x : α → ℝ≥0 | ∀ a, 0 < x a} := by
    have h : {x : α → ℝ≥0 | ∀ a, 0 < x a} = ⋂ a, {x : α → ℝ≥0 | 0 < x a} := by
      ext x
      simp
    rw [h]
    exact MeasurableSet.iInter fun a => measurableSet_lt measurable_const (measurable_pi_apply a)
  rw [simplexVolumeOn]
  refine (ae_map_iff (f := fun l : Fin (Fintype.card α) → ℝ≥0 => fun a => l (Fintype.equivFin α a))
    (μ := simplexVolume (Fintype.card α)) hmeas.aemeasurable hset).mpr ?_
  rw [ae_all_iff]
  intro a
  exact ae_pos_simplexVolume_fin (Fintype.equivFin α a)

end IntervalExchange.RauzyVeech

namespace IntervalExchange

namespace IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. The greedy word -/

/-- The branch test of the algorithm at a *fixed* word `γ`: `true` when the point lies in the `true`
child of the cylinder of `γ`. (On `cylStop P γ` both tests fail, and the algorithm stops.) -/
noncomputable def pathBranch (P : IETDatum₂ α n) (x : α → ℝ≥0) (γ : List Bool) : Bool := by
  classical
  exact if x ∈ simplexCyl P (γ ++ [true]) then true else false

theorem pathBranch_eq_true_iff (P : IETDatum₂ α n) (x : α → ℝ≥0) (γ : List Bool) :
    pathBranch P x γ = true ↔ x ∈ simplexCyl P (γ ++ [true]) := by
  unfold pathBranch
  by_cases h : x ∈ simplexCyl P (γ ++ [true])
  · rw [ite_eq_left h]
    simp [h]
  · rw [ite_eq_right h]
    simp [h]

theorem pathBranch_eq_false_iff (P : IETDatum₂ α n) (x : α → ℝ≥0) (γ : List Bool) :
    pathBranch P x γ = false ↔ x ∉ simplexCyl P (γ ++ [true]) := by
  unfold pathBranch
  by_cases h : x ∈ simplexCyl P (γ ++ [true])
  · rw [ite_eq_left h]
    simp [h]
  · rw [ite_eq_right h]
    simp [h]

/-- **The greedy word** of `x`: start with the empty word and append, at each step, the type of the
child of the current cylinder that still contains `x` (with the `false` branch as the default, used
exactly when the `true` child fails to contain `x`). -/
noncomputable def pathWord (P : IETDatum₂ α n) (x : α → ℝ≥0) : ℕ → List Bool
  | 0 => []
  | (k + 1) => pathWord P x k ++ [pathBranch P x (pathWord P x k)]

/-- The type taken at step `k`. -/
noncomputable def pathStep (P : IETDatum₂ α n) (x : α → ℝ≥0) (k : ℕ) : Bool :=
  pathBranch P x (pathWord P x k)

theorem pathWord_succ (P : IETDatum₂ α n) (x : α → ℝ≥0) (k : ℕ) :
    pathWord P x (k + 1) = pathWord P x k ++ [pathStep P x k] := (rfl)

theorem pathWord_zero (P : IETDatum₂ α n) (x : α → ℝ≥0) : pathWord P x 0 = [] := (rfl)

theorem pathWord_length (P : IETDatum₂ α n) (x : α → ℝ≥0) (k : ℕ) :
    (pathWord P x k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pathWord_succ, List.length_append, ih]; rfl

/-! ## 2. The greedy word stays inside the cylinders -/

/-- **The invariant of the greedy algorithm**, with the hypothesis exactly along the path: if `x`
starts in the root cylinder `Δ[]` and never lies in the stopping set of its own greedy word, then it
lies in the cylinder of that word at every level.  The step is the exact partition
`Δγ = Δγ⁺ ∪ Δγ⁻ ∪ cylStop P γ`. -/
theorem mem_pathWord_of_notMem_cylStop (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {x : α → ℝ≥0} (h0 : x ∈ simplexCyl P []) (hstop : ∀ k, x ∉ cylStop P (pathWord P x k))
    (k : ℕ) : x ∈ simplexCyl P (pathWord P x k) := by
  induction k with
  | zero => rw [pathWord_zero]; exact h0
  | succ k ih =>
    rw [pathWord_succ]
    by_cases h : x ∈ simplexCyl P (pathWord P x k ++ [true])
    · have hb : pathStep P x k = true := by
        rw [pathStep, pathBranch_eq_true_iff]
        exact h
      rw [hb]
      exact h
    · have hb : pathStep P x k = false := by
        rw [pathStep, pathBranch_eq_false_iff]
        exact h
      rw [hb]
      have hunion : x ∈ simplexCyl P (pathWord P x k ++ [true]) ∪
          simplexCyl P (pathWord P x k ++ [false]) ∪ cylStop P (pathWord P x k) := by
        rw [← simplexCyl_eq_union P hP hn (pathWord P x k)]
        exact ih
      rcases hunion with (h1 | h1) | h1
      · exact absurd h1 h
      · exact h1
      · exact absurd h1 (hstop k)

/-- **The path word stays in its own cylinder**, under the stronger hypothesis that `x` lies in
*no* stopping set. -/
theorem mem_pathWord (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {x : α → ℝ≥0}
    (h0 : x ∈ simplexCyl P []) (hstop : ∀ γ : List Bool, x ∉ cylStop P γ) (k : ℕ) :
    x ∈ simplexCyl P (pathWord P x k) :=
  mem_pathWord_of_notMem_cylStop P hP hn h0 (fun _ => hstop _) k

/-- The prefixes of the greedy sequence are the greedy words. -/
theorem pfx_pathStep (P : IETDatum₂ α n) (x : α → ℝ≥0) (k : ℕ) :
    pfx (pathStep P x) k = pathWord P x k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pfx_succ, ih, pathWord_succ]

end IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## 3. The root cylinder is the open simplex -/

/-- `cone 1` is the open positive orthant. -/
theorem mem_cone_one_iff (y : α → ℝ) :
    y ∈ cone (1 : Matrix α α ℤ) ↔ ∀ a, 0 < y a := by
  constructor
  · rintro ⟨y', hy', rfl⟩ a
    simpa [Matrix.one_apply] using hy' a
  · intro hy
    refine ⟨y, hy, ?_⟩
    funext a
    simp [Matrix.one_apply]

namespace IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-- **The root cylinder**: `simplexCyl P []` is the set of *strictly positive* points of the
simplex, since `Q ([]) = 1`. -/
theorem mem_simplexCyl_nil_iff (P : IETDatum₂ α n) (x : α → ℝ≥0) :
    x ∈ simplexCyl P [] ↔ x ∈ simplex α ∧ ∀ a, 0 < x a := by
  have hQ : Path.Q P ([] : List Bool) = 1 := (rfl)
  rw [simplexCyl, hQ]
  constructor
  · rintro ⟨hc, hs⟩
    exact ⟨hs, mem_cone_one_iff (fun a => (x a : ℝ)) |>.mp hc⟩
  · rintro ⟨hs, hpos⟩
    refine ⟨mem_cone_one_iff (fun a => (x a : ℝ)) |>.mpr (fun a => ?_), hs⟩
    exact_mod_cast hpos a

/-- Almost every point of the simplex is in the root cylinder.  (No irreducibility is needed:
`simplexCyl P [] = cone 1 ∩ simplex α` does not depend on `P`.) -/
theorem ae_mem_simplexCyl_nil (P : IETDatum₂ α n) :
    ∀ᵐ x ∂(simplexVolumeOn α), x ∈ simplexCyl P [] := by
  have hcard : Fintype.card α ≠ 0 := by
    rw [Fintype.card_congr P.piTop, Fintype.card_fin]
    exact NeZero.ne n
  filter_upwards [ae_mem_simplex_of_card_ne_zero hcard, ae_pos_simplexVolumeOn α] with x hs hpos
  exact (mem_simplexCyl_nil_iff P x).mpr ⟨hs, hpos⟩

/-- Almost every point lies in no stopping set: `List Bool` is countable and each `cylStop
P γ` is null. -/
theorem ae_notMem_cylStop_all (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∀ᵐ x ∂(simplexVolumeOn α), ∀ γ : List Bool, x ∉ cylStop P γ := by
  rw [ae_all_iff]
  intro γ
  exact measure_eq_zero_iff_ae_notMem.mp (simplexVolumeOn_cylStop P hP hn γ)

end IETDatum₂

end IntervalExchange

namespace IntervalExchange.RauzyVeech

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 4. Nesting of the path cylinders -/

/-- **Nesting**: consecutive path cylinders of an infinite sequence are nested. -/
theorem simplexCyl_pfx_succ_subset (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (p : ℕ → Bool) (k : ℕ) :
    IETDatum₂.simplexCyl P (pfx p (k + 1)) ⊆
      IETDatum₂.simplexCyl P (pfx p k) := by
  rw [pfx_succ]
  exact IETDatum₂.simplexCyl_append_subset P hP hn (pfx p k) (p k)

end IntervalExchange.RauzyVeech

end
