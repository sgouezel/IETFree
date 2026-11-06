/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib

/-!
# A finite measure on `ℝ` is determined by a refining sequence of partitions of mesh → 0

Standalone measure-theory lemma for the injectivity step of the Masur–Veech proof: the level-`n`
floors of the Rokhlin tower decomposition form a refining sequence of finite partitions of `[0, λ*)`
whose mesh tends to `0`, so two invariant finite measures agreeing on every floor of every level
agree everywhere.

Formally: let `μ`, `ν` be finite measures on `ℝ` and, for each `n`, let `P n` be a finite family
of pairwise disjoint measurable subsets of a set `I`, covering `I`, such that `P (n+1)` refines
`P n`, the mesh of `P n` tends to `0`, and `μ` and `ν` give the same mass to every atom.  Then
`μ` and `ν` agree on `I` (`measure_restrict_eq_of_refining_partitions`), indeed on every Borel
subset of `I` (`measure_eq_of_measurableSet_subset`).

No hypothesis on the *shape* of the atoms is used: they need not be intervals, and `I` need not
be an interval either.  The argument is purely metric and runs as follows.

* Pertinent to a closed `F ⊆ I` and a level `n`, let `E n` be the union of the atoms of `P n`
  that meet `F`.  Refinement makes `n ↦ E n` antitone, and `⋂ n, E n = F`: any `z` in the
  intersection lies in atoms of arbitrarily small diameter each meeting `F`, so `z` is a limit
  point of `F`.  This is the only place where the mesh hypothesis and closedness are used.
* Since `μ` and `ν` agree on every atom, they agree on each `E n` (a finite disjoint union of
  measurable atoms).  Continuity from above for the finite measures `μ`, `ν` along the
  decreasing sequence `E n` therefore gives `μ F = ν F`.
* A finite measure on `ℝ` is inner regular by compact sets, so agreement on all closed subsets
  of `I` upgrades to agreement on all Borel subsets of `I`.

The mesh hypothesis `hmesh` is stated as "any two points of an atom are `< ε` apart", so no
boundedness of the atoms is needed: `Metric.diam` of an *unbounded* set is `0` in Mathlib, and a
diameter formulation would therefore need the atom bounded as a side condition. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace RefiningPartition

variable {μ ν : Measure ℝ}

/-! ### Two elementary steps -/

/-- A finite union of pairwise disjoint measurable sets has the same `μ`- and `ν`-measure as soon
as each of the pieces does. -/
theorem measure_biUnion_eq {s : Finset (Set ℝ)}
    (hdisj : ∀ A ∈ s, ∀ B ∈ s, A ≠ B → Disjoint A B)
    (hmeas : ∀ A ∈ s, MeasurableSet A) (hagr : ∀ A ∈ s, μ A = ν A) :
    μ (⋃ A ∈ s, A) = ν (⋃ A ∈ s, A) := by
  have hd : Set.PairwiseDisjoint (↑s) id := fun A hA B hB hne => hdisj A hA B hB hne
  have h1 : μ (⋃ A ∈ s, A) = ∑ A ∈ s, μ A := by
    simpa using measure_biUnion_finset (μ := μ) (f := id) hd hmeas
  have h2 : ν (⋃ A ∈ s, A) = ∑ A ∈ s, ν A := by
    simpa using measure_biUnion_finset (μ := ν) (f := id) hd hmeas
  rw [h1, h2]
  exact Finset.sum_congr rfl fun A hA => hagr A hA

/-- **Agreement on closed subsets.**  Given a refining sequence of partitions of `I` with mesh
tending to `0` on which `μ` and `ν` agree, the two measures agree on every closed `F ⊆ I`. -/
theorem measure_eq_of_isClosed [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (I : Set ℝ) (P : ℕ → Finset (Set ℝ))
    (hmeas : ∀ n A, A ∈ P n → MeasurableSet A)
    (hcov : ∀ n x, x ∈ I → ∃ A ∈ P n, x ∈ A)
    (hdisj : ∀ n A, A ∈ P n → ∀ B ∈ P n, A ≠ B → Disjoint A B)
    (href : ∀ n A, A ∈ P (n + 1) → ∃ B ∈ P n, A ⊆ B)
    (hmesh : ∀ ε > 0, ∀ᶠ n in atTop, ∀ A ∈ P n, ∀ x ∈ A, ∀ y ∈ A, dist x y < ε)
    (hagr : ∀ n A, A ∈ P n → μ A = ν A)
    {F : Set ℝ} (hF : IsClosed F) (hFI : F ⊆ I) : μ F = ν F := by
  classical
  -- refinement, iterated
  have href_le ⦃n m : ℕ⦄ (hnm : n ≤ m) : ∀ A, A ∈ P m → ∃ B ∈ P n, A ⊆ B := by
    refine Nat.le_induction (m := n)
      (P := fun k _ => ∀ A, A ∈ P k → ∃ B ∈ P n, A ⊆ B) ?_ ?_ m hnm
    · exact fun A hA => ⟨A, hA, subset_rfl⟩
    · intro k _ ih A hA
      obtain ⟨B, hB, hAB⟩ := href k A hA
      obtain ⟨C, hC, hCB⟩ := ih B hB
      exact ⟨C, hC, hAB.trans hCB⟩
  -- the atoms meeting `F`
  set S : ℕ → Finset (Set ℝ) := fun n => (P n).filter fun A => (A ∩ F).Nonempty with hS
  set E : ℕ → Set ℝ := fun n => ⋃ A ∈ S n, A with hE
  have hES (n) (A) : A ∈ S n ↔ A ∈ P n ∧ (A ∩ F).Nonempty := Finset.mem_filter
  have hEmeas (n) : MeasurableSet (E n) := Finset.measurableSet_biUnion _ fun A hA => hmeas n A
      ((hES n A).1 hA).1
  -- `E` is decreasing
  have hanti : Antitone E := by
    intro n m hnm z hz
    obtain ⟨A, hA, hzA⟩ := Set.mem_iUnion₂.1 hz
    have hAS := (hES m A).1 hA
    obtain ⟨B, hB, hAB⟩ := href_le hnm A hAS.1
    have hBS : B ∈ S n := (hES n B).2 ⟨hB, hAS.2.imp fun w hw => ⟨hAB hw.1, hw.2⟩⟩
    exact Set.mem_biUnion hBS (hAB hzA)
  -- the intersection of the `E n` is `F`
  have hInter : ⋂ n, E n = F := by
    refine Set.Subset.antisymm ?_ fun x hx => ?_
    · intro z hz
      have hzcl : z ∈ closure F := by
        rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨N, hN⟩ := eventually_atTop.1 (hmesh ε hε)
        obtain ⟨A, hA, hzA⟩ := Set.mem_iUnion₂.1 (Set.mem_iInter.1 hz N)
        obtain ⟨y, hyA, hyF⟩ := ((hES N A).1 hA).2
        exact ⟨y, hyF, hN N le_rfl A ((hES N A).1 hA).1 z hzA y hyA⟩
      rwa [hF.closure_eq] at hzcl
    · refine Set.mem_iInter.2 fun n => ?_
      obtain ⟨A, hA, hxA⟩ := hcov n x (hFI hx)
      exact Set.mem_biUnion ((hES n A).2 ⟨hA, ⟨x, hxA, hx⟩⟩) hxA
  -- `μ` and `ν` agree on each `E n`
  have hagree (n) : μ (E n) = ν (E n) := measure_biUnion_eq
      (fun A hA B hB hne => hdisj n A ((hES n A).1 hA).1 B ((hES n B).1 hB).1 hne)
      (fun A hA => hmeas n A ((hES n A).1 hA).1)
      (fun A hA => hagr n A ((hES n A).1 hA).1)
  -- continuity from above
  have hμt : Tendsto (fun n => μ (E n)) atTop (𝓝 (μ F)) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) (s := E)
      (fun n => (hEmeas n).nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
    rw [hInter] at h
    exact h
  have hνt : Tendsto (fun n => ν (E n)) atTop (𝓝 (ν F)) := by
    have h := tendsto_measure_iInter_atTop (μ := ν) (s := E)
      (fun n => (hEmeas n).nullMeasurableSet) hanti ⟨0, measure_ne_top ν _⟩
    rw [hInter] at h
    exact h
  have hfun : (fun n => μ (E n)) = fun n => ν (E n) := funext hagree
  rw [hfun] at hμt
  exact tendsto_nhds_unique hμt hνt

/-! ### The main statement -/

/-- The set `I` is measurable: it is the union of the level-`0` atoms. -/
theorem measurableSet_of_partitions (I : Set ℝ) (P : ℕ → Finset (Set ℝ))
    (hmeas : ∀ n A, A ∈ P n → MeasurableSet A)
    (hsub : ∀ n A, A ∈ P n → A ⊆ I)
    (hcov : ∀ n x, x ∈ I → ∃ A ∈ P n, x ∈ A) : MeasurableSet I := by
  have h0 : I = ⋃ A ∈ P 0, A := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      obtain ⟨A, hA, hxA⟩ := hcov 0 x hx
      exact Set.mem_biUnion hA hxA
    · intro x hx
      obtain ⟨A, hA, hxA⟩ := Set.mem_iUnion₂.1 hx
      exact hsub 0 A hA hxA
  rw [h0]
  exact Finset.measurableSet_biUnion _ fun A hA => hmeas 0 A hA

/-- **A finite measure on `ℝ` is determined by refining partitions of mesh → 0** (Borel form).  Let
`P n` be a sequence of finite families of pairwise disjoint measurable subsets of `I` covering `I`,
each refining the previous one, with the mesh tending to `0` (`hmesh`), and suppose that `μ` and `ν`
give the same mass to every atom.  Then `μ` and `ν` agree on every Borel subset of `I`.  No
hypothesis on the shape of the atoms is needed: they need not be intervals. -/
theorem measure_eq_of_measurableSet_subset [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (I : Set ℝ) (P : ℕ → Finset (Set ℝ))
    (hmeas : ∀ n A, A ∈ P n → MeasurableSet A)
    (hcov : ∀ n x, x ∈ I → ∃ A ∈ P n, x ∈ A)
    (hdisj : ∀ n A, A ∈ P n → ∀ B ∈ P n, A ≠ B → Disjoint A B)
    (href : ∀ n A, A ∈ P (n + 1) → ∃ B ∈ P n, A ⊆ B)
    (hmesh : ∀ ε > 0, ∀ᶠ n in atTop, ∀ A ∈ P n, ∀ x ∈ A, ∀ y ∈ A, dist x y < ε)
    (hagr : ∀ n A, A ∈ P n → μ A = ν A)
    {B : Set ℝ} (hB : MeasurableSet B) (hBI : B ⊆ I) : μ B = ν B := by
  have hkey {F : Set ℝ} : IsClosed F → F ⊆ I → μ F = ν F :=
    measure_eq_of_isClosed (μ := μ) (ν := ν) I P hmeas hcov hdisj href hmesh hagr
  -- agreement on Borel subsets of `I`, by inner regularity of finite measures on `ℝ`
  refine le_antisymm ?_ ?_
  · rw [hB.measure_eq_iSup_isCompact_of_ne_top (measure_ne_top μ B)]
    refine iSup_le fun K => iSup_le fun hK => iSup_le fun hcK => ?_
    calc μ K = ν K := hkey hcK.isClosed (hK.trans hBI)
      _ ≤ ν B := measure_mono hK
  · rw [hB.measure_eq_iSup_isCompact_of_ne_top (measure_ne_top ν B)]
    refine iSup_le fun K => iSup_le fun hK => iSup_le fun hcK => ?_
    calc ν K = μ K := (hkey hcK.isClosed (hK.trans hBI)).symm
      _ ≤ μ B := measure_mono hK

/-- **A finite measure on `ℝ` is determined by refining partitions of mesh → 0.**  The conclusion of
`measure_eq_of_measurableSet_subset` in the form used by the injectivity step: `μ` and `ν` agree
after restriction to `I`. -/
theorem measure_restrict_eq_of_refining_partitions [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (I : Set ℝ) (P : ℕ → Finset (Set ℝ))
    (hmeas : ∀ n A, A ∈ P n → MeasurableSet A)
    (hsub : ∀ n A, A ∈ P n → A ⊆ I)
    (hcov : ∀ n x, x ∈ I → ∃ A ∈ P n, x ∈ A)
    (hdisj : ∀ n A, A ∈ P n → ∀ B ∈ P n, A ≠ B → Disjoint A B)
    (href : ∀ n A, A ∈ P (n + 1) → ∃ B ∈ P n, A ⊆ B)
    (hmesh : ∀ ε > 0, ∀ᶠ n in atTop, ∀ A ∈ P n, ∀ x ∈ A, ∀ y ∈ A, dist x y < ε)
    (hagr : ∀ n A, A ∈ P n → μ A = ν A) :
    μ.restrict I = ν.restrict I := by
  have hImeas := measurableSet_of_partitions I P hmeas hsub hcov
  refine Measure.ext fun B hB => ?_
  rw [Measure.restrict_apply hB, Measure.restrict_apply hB]
  exact measure_eq_of_measurableSet_subset I P hmeas hcov hdisj href hmesh hagr
    (hB.inter hImeas) Set.inter_subset_right

end RefiningPartition

end
