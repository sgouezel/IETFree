/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.UniqueErgodicity.Main
public import IETFree.UniqueErgodicity.Germ
public import IETFree.UniqueErgodicity.MeasPrep
public import IETFree.UniqueErgodicity.CompactTool
public import IETFree.UniqueErgodicity.TransferConv
public import IETFree.UniqueErgodicity.SubtypeConv
public import IETFree.UniqueErgodicity.GermIterate

/-!
# Theorem 2: uniform Birkhoff convergence from a unique invariant measure

The results:

* `uniqueErgodicOn_rightPart` — **Theorem 4.11**: the germ map `T̃` of the interval exchange
  `mkIETEquiv lam π 0`, restricted to the compact space `[0⁺, 1⁻]` of right germs of `[0, 1)`, is
  uniquely ergodic as soon as Lebesgue measure on `[0, 1)` is the only invariant probability of the
  exchange carried by `[0, 1)`.  Every invariant probability on `[0⁺, 1⁻]` is then the lift of
  `unitMeas` along the total section `germSectionIco`.
* `uniformBirkhoff_mkIET1` — **Theorem 2**: for `mkIET1 lam π`, the weak form of unique ergodicity
  (`UniqueErgodic`, a unique invariant probability carried by `[0, 1)`) implies the strong one
  (`UniformBirkhoff`, uniform convergence of the Birkhoff averages of continuous functions).
* `uniformBirkhoff_of_uniqueErgodic` — Theorem 2 for an *arbitrary* exchange on `[0, 1)`, obtained
  by re-presenting it as `mkIETEquiv lam π 0` (`exists_mkIETEquiv_eq`).
* `exists_uniform_birkhoff` — **Lemma 2.9**: the uniform bound on the Birkhoff sums of the indicator
  of a finite union of half-open intervals, the form in which the free-group development consumes
  unique ergodicity (`IETFree/Pair/Irreducible.lean`).

The proof of Theorem 4.11 is the transfer argument: push an invariant probability
`ν` of `[0⁺, 1⁻]` to the whole split interval, write `J` for the finite set of points at which the
left limit and the exchange differ, check that the only obstruction to `proj_*ν` being invariant is
the mass of the left germs `leftGerm c`, `c ∈ J`, and kill that mass — by the orbit argument for
`c ≠ 0` (this is where (H2), deduced from (H1) by `noPeriodicLeftLimit_of_unique`, is used) and by
`leftGerm 0 ∉ [0⁺, 1⁻]` for `c = 0`.  Theorem 4.6 then gives `proj_*ν = unitMeas`, and the
corrected lift lemma `lift_unique_on_Ico` identifies `ν`.

Theorem 2 then applies Tool 1 (`tendsto_uniform_birkhoffAverage`) to the restriction of the germ map
to `[0⁺, 1⁻]`, whose unique invariant probability is the lift above, and transfers the convergence
back to the exchange along the right-germ section.

The iterate bridge for the left germs is in `UniqueErgodicity/GermIterate.lean`, which provides
`germMapOf_leftGerm`, `proj_iterate_germMapOf_leftGerm` and `germMapOf_orbit_infinite`; this file
uses them directly.
-/

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal BigOperators

namespace IETFree.UniqueErgodicity

/-! ## Notation for the exchange of the germ map -/

/-- The split set of the exchange `mkIETEquiv lam π 0`, for the cut set
`mkIETCuts lam 0 1`. -/
abbrev ietSplitSet {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n)) : Set ℝ :=
  splitSet (mkIETEquiv lam π 0) (mkIETCuts lam 0 1)

/-- The right part `[0⁺, 1⁻]` of the split interval of that exchange. -/
abbrev ietRightPart {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n)) :
    Set (SplitI (ietSplitSet lam π)) :=
  SplitI.rightPart (ietSplitSet lam π)

/-- The germ map of that exchange, restricted to the right part `[0⁺, 1⁻]`. -/
noncomputable abbrev ietGermRight {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (hsum : (∑ i, (lam i : ℝ)) ≤ 1) : ↥(ietRightPart lam π) → ↥(ietRightPart lam π) :=
  restrictTo (germMap lam π hsum) (mapsTo_rightPart lam π hsum)

/-- The restriction of the germ map to `[0⁺, 1⁻]` is continuous. -/
theorem continuous_ietGermRight {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin n)) (hsum : (∑ i, (lam i : ℝ)) ≤ 1) :
    Continuous (ietGermRight lam π hsum) :=
  Continuous.subtype_mk ((continuous_germMap lam π hsum).comp continuous_subtype_val) _

/-! ## The total section of the right part along `[0, 1)` -/

/-- The clamp of a real number into `[0, 1)`: `clampI` below `1`, and the constant `1/2` above.
Unlike `clampI`, its values avoid `1`, so that the right germ of its value always lies in the right
part `[0⁺, 1⁻]`. -/
noncomputable def clampIco (x : ℝ) : ℝ := if x < 1 then clampI x else 1 / 2

theorem measurable_clampIco : Measurable clampIco :=
  Measurable.ite measurableSet_Iio measurable_clampI measurable_const

theorem clampIco_mem (x : ℝ) : clampIco x ∈ Set.Ico (0 : ℝ) 1 := by
  unfold clampIco
  split_ifs with h
  · exact ⟨(clampI_mem x).1, lt_of_le_of_lt (min_le_left _ _) (max_lt h zero_lt_one)⟩
  · norm_num

theorem clampIco_eq_self {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) : clampIco x = x := by
  rw [clampIco, if_pos hx.2, clampI_eq_self ⟨hx.1, hx.2.le⟩]

theorem clampIco_mem_Icc (x : ℝ) : clampIco x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(clampIco_mem x).1, (clampIco_mem x).2.le⟩

/-- The right germ of a measurable function with values in `[0, 1]` is measurable. -/
theorem measurable_rightGerm_comp {D : Set ℝ} {c : ℝ → ℝ} (hc : Measurable c)
    (hmem : ∀ x, c x ∈ Set.Icc (0 : ℝ) 1) :
    Measurable fun x => SplitI.rightGerm (D := D) (c x) (hmem x) := by
  have hpair : Measurable fun x =>
      ((c x, fun d : D => decide ((d : ℝ) ≤ c x)) : ℝ × (D → Bool)) := by
    refine Measurable.prodMk hc ?_
    rw [measurable_pi_iff]
    intro d
    have hif : (fun x : ℝ => decide ((d : ℝ) ≤ c x))
        = fun x : ℝ => if (d : ℝ) ≤ c x then true else false := by
      funext x
      by_cases h : (d : ℝ) ≤ c x <;> simp [h]
    rw [hif]
    exact Measurable.ite (measurableSet_Ici.preimage hc) measurable_const measurable_const
  exact Measurable.subtype_mk hpair

/-- **The total section of the right part** `[0⁺, 1⁻]`: the right germ of the clamp of `x` into
`[0, 1)`.  It is a total measurable function `ℝ → [0⁺, 1⁻]` which is a section of the projection
on `[0, 1)`. -/
noncomputable def germSectionIco {D : Set ℝ} (x : ℝ) : ↥(SplitI.rightPart D) :=
  ⟨SplitI.rightGerm (clampIco x) (clampIco_mem_Icc x),
    SplitI.rightGerm_mem_rightPart (clampIco_mem x)⟩

theorem measurable_germSectionIco {D : Set ℝ} : Measurable (germSectionIco (D := D)) :=
  Measurable.subtype_mk (measurable_rightGerm_comp measurable_clampIco clampIco_mem_Icc)

theorem proj_germSectionIco {D : Set ℝ} {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    SplitI.proj (germSectionIco (D := D) x).1 = x := by
  have h1 : (germSectionIco (D := D) x).1
      = SplitI.rightGerm (D := D) (clampIco x) (clampIco_mem_Icc x) := rfl
  rw [h1, SplitI.proj_rightGerm, clampIco_eq_self hx]

/-- The total section of the left germs, used to state the behaviour of the germ map at the jumps:
at a jump `c ∈ [0, 1]` it is the left germ of `c`. -/
noncomputable def leftGermSection {D : Set ℝ} (c : ℝ) : SplitI D :=
  SplitI.leftGerm (clampI c) (clampI_mem c)

theorem leftGermSection_eq {D : Set ℝ} {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    leftGermSection (D := D) c = SplitI.leftGerm (D := D) c hc :=
  leftGerm_congr (clampI_mem c) hc (clampI_eq_self hc)

/-! ## Small facts about the split interval -/

/-- The right germ of `1` does not belong to the right part `[0⁺, 1⁻]`: the clopen set
`{1 < proj} ∪ {rightGerm 1}` is a neighbourhood of it that meets the right germs of `[0, 1)` only
at the point `rightGerm 1` itself, which is excluded. -/
theorem rightGerm_one_notMem_rightPart {D : Set ℝ} (h1 : (1 : ℝ) ∈ D) :
    SplitI.rightGerm (D := D) 1 ⟨zero_le_one, le_rfl⟩ ∉ SplitI.rightPart D := by
  intro hmem
  obtain ⟨z, hzU, y, rfl⟩ :=
    mem_closure_iff.mp hmem (SplitI.upSet (D := D) 1 ⟨zero_le_one, le_rfl⟩)
      (SplitI.isOpen_upSet ⟨zero_le_one, le_rfl⟩ h1) (Or.inr rfl)
  have hy : (1 : ℝ) ≤ y.1 := SplitI.upSet_subset hzU
  exact absurd hy (not_le.mpr y.2.2)

/-! ## The iterate bridge for the left germs -/

section IterateBridge

variable {T : ℝ ≃ ℝ} {s : Finset ℝ}

/-- **The jump set of the left limit is finite**: a point `x ∈ [0, 1]` at which the left limit
differs from the exchange is either a cut or the right end `1`.  This is the finite set `J` of
Blueprint 2, Definition 1.4, over which the defect identity sums. -/
theorem finite_jumpSet (hT : IsCutSet (⇑T) 0 1 s) :
    {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧ leftLimit hT x ≠ ⇑T x}.Finite := by
  refine Set.Finite.subset (s.finite_toSet.union (Set.finite_singleton 1)) ?_
  rintro x ⟨hxIcc, hxne⟩
  rcases eq_or_lt_of_le hxIcc.2 with hx1 | hx1
  · exact Or.inr hx1
  · exact Or.inl (by_contra fun hxs => hxne (leftLimit_eq_apply hT ⟨hxIcc.1, hx1⟩ hxs))

end IterateBridge

/-! ## Theorem 4.11: the transfer of invariance and the uniqueness of the lift -/

/-- **Theorem 4.11, first part**: a probability on `[0⁺, 1⁻]` invariant under the germ map projects
to Lebesgue measure on `[0, 1)`, as soon as Lebesgue measure is the only invariant probability of
the exchange carried by `[0, 1)`.

The proof pushes `ν` forward to the whole split interval and applies the abstract transfer theorem
`Transfer.map_map_eq_self`: the defect is carried by the left germs of the finite set `J` of
points at
which the left limit differs from the exchange, and each of these germs carries no mass — for `0`
because `leftGerm 0 ∉ [0⁺, 1⁻]`, for the others because (H2) makes their orbit infinite. -/
theorem map_proj_eq_unitMeas_of_invariant {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin n)) (h : (∑ i, (lam i : ℝ)) = 1)
    (hH1 : ∀ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ).map (mkIETFun lam π 0) = (μ : Measure ℝ) →
      (μ : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1 → (μ : Measure ℝ) = unitMeas)
    (ν : ProbabilityMeasure ↥(ietRightPart lam π))
    (hν : (ν : Measure ↥(ietRightPart lam π)).map (ietGermRight lam π h.le)
      = (ν : Measure ↥(ietRightPart lam π))) :
    (ν : Measure ↥(ietRightPart lam π)).map (fun z => SplitI.proj z.1) = unitMeas :=
  haveI : Countable (ietSplitSet lam π) := splitSet_countable _ _
  by
  classical
  have hT : IsCutSet (⇑(mkIETEquiv lam π 0)) 0 1 (mkIETCuts lam 0 1) := isCutSet_mkIET lam π h.le
  have hH2 : NoPeriodicLeftLimit hT := noPeriodicLeftLimit_of_unique hT hH1
  -- the pushforward of `ν` to the whole split interval
  set ν₀ : ProbabilityMeasure (SplitI (ietSplitSet lam π)) :=
    ⟨(ν : Measure ↥(ietRightPart lam π)).map Subtype.val,
      Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable⟩ with hν₀
  have hν₀' : (ν₀ : Measure (SplitI (ietSplitSet lam π)))
      = (ν : Measure ↥(ietRightPart lam π)).map Subtype.val := by
    rw [hν₀]
    exact ProbabilityMeasure.coe_mk _ _
  have hgr : Measurable (ietGermRight lam π h.le) := (continuous_ietGermRight lam π h.le).measurable
  -- `ν₀` is invariant under the germ map
  have hν₀inv : (ν₀ : Measure _).map (germMap lam π h.le) = (ν₀ : Measure _) := by
    calc (ν₀ : Measure _).map (germMap lam π h.le)
        = ((ν : Measure ↥(ietRightPart lam π)).map Subtype.val).map (germMap lam π h.le) := by
          rw [hν₀']
      _ = (ν : Measure ↥(ietRightPart lam π)).map (germMap lam π h.le ∘ Subtype.val) :=
          Measure.map_map (continuous_germMap lam π h.le).measurable measurable_subtype_coe
      _ = (ν : Measure ↥(ietRightPart lam π)).map
            (Subtype.val ∘ ietGermRight lam π h.le) := rfl
      _ = ((ν : Measure ↥(ietRightPart lam π)).map (ietGermRight lam π h.le)).map
            Subtype.val := (Measure.map_map measurable_subtype_coe hgr).symm
      _ = (ν : Measure ↥(ietRightPart lam π)).map Subtype.val := by
          rw [hν]
      _ = (ν₀ : Measure _) := by rw [hν₀']
  -- the finite set of jumps of the left limit
  obtain ⟨J, hJmem⟩ : ∃ J : Finset ℝ, ∀ c : ℝ,
      c ∈ J ↔ c ∈ Set.Icc (0 : ℝ) 1 ∧ leftLimit hT c ≠ ⇑(mkIETEquiv lam π 0) c := by
    have hfin := finite_jumpSet hT
    exact ⟨hfin.toFinset, fun c => hfin.mem_toFinset⟩
  have hJD : ∀ c ∈ J, c ∈ ietSplitSet lam π := by
    intro c hc
    obtain ⟨hcIcc, hcne⟩ := (hJmem c).mp hc
    rcases eq_or_lt_of_le hcIcc.2 with hc1 | hc1
    · rw [hc1]
      exact one_mem_splitSet _ _
    · exact mem_splitSet_of_mem _ _
        (by_contra fun hcs => hcne (leftLimit_eq_apply hT ⟨hcIcc.1, hc1⟩ hcs))
  -- the total left-germ map at the jumps
  set e : ℝ → SplitI (ietSplitSet lam π) := leftGermSection (D := ietSplitSet lam π) with he
  have hpe : ∀ c ∈ J, SplitI.proj (e c) = c := by
    intro c hc
    have hcIcc := ((hJmem c).mp hc).1
    rw [he]
    change SplitI.proj (leftGermSection (D := ietSplitSet lam π) c) = c
    rw [leftGermSection_eq hcIcc, SplitI.proj_leftGerm]
  have hdef : ∀ c ∈ J, SplitI.proj (germMap lam π h.le (e c)) = leftLimit hT c := by
    intro c hc
    have hcIcc := ((hJmem c).mp hc).1
    have hcD := hJD c hc
    rw [he]
    change SplitI.proj (germMap lam π h.le (leftGermSection (D := ietSplitSet lam π) c))
      = leftLimit hT c
    rw [leftGermSection_eq hcIcc, germMap_eq_germMapOf, proj_germMapOf,
      germProjOf_of_side_false hT (SplitI.side_leftGerm hcIcc hcD), SplitI.proj_leftGerm]
  have hTeq : ∀ z : SplitI (ietSplitSet lam π), (∀ c ∈ J, z ≠ e c) →
      SplitI.proj (germMap lam π h.le z) = ⇑(mkIETEquiv lam π 0) (SplitI.proj z) := by
    intro z hz
    have hzIcc : SplitI.proj z ∈ Set.Icc (0 : ℝ) 1 := SplitI.proj_mem_Icc z
    by_cases hside : SplitI.side z = true
    · rw [germMap_eq_germMapOf, proj_germMapOf, germProjOf_of_side_true hT hside]
    · have hside' : SplitI.side z = false := by
        cases hv : SplitI.side z with
        | false => rfl
        | true => exact absurd hv hside
      rw [germMap_eq_germMapOf, proj_germMapOf, germProjOf_of_side_false hT hside']
      by_contra hne
      have hxJ : SplitI.proj z ∈ J := (hJmem _).mpr ⟨hzIcc, hne⟩
      have hze : z = e (SplitI.proj z) := by
        rw [he]
        rw [leftGermSection_eq hzIcc]
        exact eq_leftGerm_of_side_false hside'
      exact hz _ hxJ hze
  have hvan : ∀ c ∈ J, (ν₀ : Measure _) {e c} = 0 := by
    intro c hc
    have hcIcc := ((hJmem c).mp hc).1
    have hcD := hJD c hc
    have hec : e c = SplitI.leftGerm (D := ietSplitSet lam π) c hcIcc := by
      rw [he]
      exact leftGermSection_eq hcIcc
    rw [hec]
    by_cases hc0 : c = 0
    · subst hc0
      have hempty : ((Subtype.val : ↥(ietRightPart lam π) →
          SplitI (ietSplitSet lam π)) ⁻¹'
          ({SplitI.leftGerm (D := ietSplitSet lam π) 0 hcIcc} :
            Set (SplitI (ietSplitSet lam π)))) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z hz
        have hz1 : (z : SplitI (ietSplitSet lam π))
            = SplitI.leftGerm (D := ietSplitSet lam π) 0 hcIcc := by simpa using hz
        exact leftGerm_zero_notMem_rightPart lam π h.le (by rw [← hz1]; exact z.2)
      rw [hν₀', Measure.map_apply measurable_subtype_coe (measurableSet_singleton _), hempty,
        measure_empty]
    · have hcIoc : c ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hcIcc.1 (Ne.symm hc0), hcIcc.2⟩
      exact measure_singleton_eq_zero_of_injOn_orbit (germMap lam π h.le)
        (germMap_inj lam π h.le) (continuous_germMap lam π h.le).measurable hν₀inv _
        (germMapOf_orbit_infinite hT hH2 hcIoc hcD)
  -- transfer of invariance
  have htrans : ((ν₀ : Measure (SplitI (ietSplitSet lam π))).map
        (SplitI.proj (D := ietSplitSet lam π))).map (⇑(mkIETEquiv lam π 0))
      = (ν₀ : Measure (SplitI (ietSplitSet lam π))).map
        (SplitI.proj (D := ietSplitSet lam π)) :=
    map_map_eq_self (G := germMap lam π h.le)
      (continuous_germMap lam π h.le).measurable (germMap_inj lam π h.le) hν₀inv
      (SplitI.proj (D := ietSplitSet lam π)) measurable_proj (⇑(mkIETEquiv lam π 0))
      (leftLimit hT) hT.measurable J e hpe hdef hTeq hvan
  -- `proj_*ν₀` is carried by `[0, 1)`
  have hprojIcc : (SplitI.proj (D := ietSplitSet lam π)) ⁻¹' (Set.Icc (0 : ℝ) 1) = Set.univ :=
    Set.eq_univ_of_forall fun z => SplitI.proj_mem_Icc z
  have hIcc : ((ν₀ : Measure (SplitI (ietSplitSet lam π))).map
        (SplitI.proj (D := ietSplitSet lam π))) (Set.Icc (0 : ℝ) 1) = 1 := by
    -- the projection of `ν₀` lives on `[0,1]`
    rw [Measure.map_apply measurable_proj measurableSet_Icc, hprojIcc, measure_univ]
  have h1zero : ((ν₀ : Measure (SplitI (ietSplitSet lam π))).map
        (SplitI.proj (D := ietSplitSet lam π))) ({1} : Set ℝ) = 0 := by
    rw [Measure.map_apply measurable_proj (measurableSet_singleton (1 : ℝ))]
    have hsub : SplitI.proj ⁻¹' ({1} : Set ℝ) ⊆
        {SplitI.leftGerm (D := ietSplitSet lam π) 1 ⟨zero_le_one, le_rfl⟩,
          SplitI.rightGerm (D := ietSplitSet lam π) 1 ⟨zero_le_one, le_rfl⟩} := by
      intro z hz
      have hz1 : SplitI.proj z = 1 := hz
      rcases SplitI.eq_rightGerm_or_leftGerm z with hz' | hz'
      · rw [hz']
        exact Or.inr (rightGerm_congr _ ⟨zero_le_one, le_rfl⟩ hz1)
      · rw [hz']
        exact Or.inl (leftGerm_congr _ ⟨zero_le_one, le_rfl⟩ hz1)
    refine measure_mono_null hsub (measure_union_null ?_ ?_)
    · exact measure_singleton_eq_zero_of_injOn_orbit (germMap lam π h.le)
        (germMap_inj lam π h.le) (continuous_germMap lam π h.le).measurable hν₀inv _
        (germMapOf_orbit_infinite hT hH2 ⟨zero_lt_one, le_rfl⟩ (one_mem_splitSet _ _))
    · have hnotmem := rightGerm_one_notMem_rightPart (D := ietSplitSet lam π)
        (one_mem_splitSet _ _)
      have hempty : ((Subtype.val : ↥(ietRightPart lam π) →
          SplitI (ietSplitSet lam π)) ⁻¹'
          ({SplitI.rightGerm (D := ietSplitSet lam π) 1 ⟨zero_le_one, le_rfl⟩} :
            Set (SplitI (ietSplitSet lam π)))) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z hz
        have hz1 : (z : SplitI (ietSplitSet lam π))
            = SplitI.rightGerm (D := ietSplitSet lam π) 1 ⟨zero_le_one, le_rfl⟩ := by
          simpa using hz
        exact hnotmem (by rw [← hz1]; exact z.2)
      rw [hν₀', Measure.map_apply measurable_subtype_coe (measurableSet_singleton _), hempty,
        measure_empty]
  have hIco : ((ν₀ : Measure (SplitI (ietSplitSet lam π))).map
        (SplitI.proj (D := ietSplitSet lam π))) (Set.Ico (0 : ℝ) 1) = 1 := by
    have hdisj : Disjoint (Set.Ico (0 : ℝ) 1) ({1} : Set ℝ) :=
      Set.disjoint_singleton_right.mpr fun h => lt_irrefl (1 : ℝ) h.2
    have hset : Set.Ico (0 : ℝ) 1 ∪ ({1} : Set ℝ) = Set.Icc (0 : ℝ) 1 := by
      ext x
      simp only [Set.mem_union, Set.mem_Ico, Set.mem_singleton_iff, Set.mem_Icc]
      constructor
      · rintro (⟨h0, h1⟩ | rfl)
        · exact ⟨h0, le_of_lt h1⟩
        · exact ⟨zero_le_one, le_rfl⟩
      · rintro ⟨h0, h1⟩
        rcases lt_or_eq_of_le h1 with h | h
        · exact Or.inl ⟨h0, h⟩
        · exact Or.inr h
    have hunion : ((ν₀ : Measure (SplitI (ietSplitSet lam π))).map
        (SplitI.proj (D := ietSplitSet lam π))) ({1} : Set ℝ) +
        ((ν₀ : Measure (SplitI (ietSplitSet lam π))).map
        (SplitI.proj (D := ietSplitSet lam π))) (Set.Ico (0 : ℝ) 1)
        = ((ν₀ : Measure (SplitI (ietSplitSet lam π))).map
        (SplitI.proj (D := ietSplitSet lam π))) (Set.Icc (0 : ℝ) 1) := by
      rw [add_comm, ← measure_union hdisj (measurableSet_singleton (1 : ℝ)), hset]
    rw [hIcc, h1zero, zero_add] at hunion
    exact hunion
  -- (H1) identifies the pushforward
  have hprob : IsProbabilityMeasure ((ν₀ : Measure (SplitI (ietSplitSet lam π))).map
        (SplitI.proj (D := ietSplitSet lam π))) :=
    Measure.isProbabilityMeasure_map measurable_proj.aemeasurable
  have hfinal : (ν₀ : Measure (SplitI (ietSplitSet lam π))).map
        (SplitI.proj (D := ietSplitSet lam π)) = unitMeas :=
    hH1 ⟨((ν₀ : Measure (SplitI (ietSplitSet lam π)))).map
        (SplitI.proj (D := ietSplitSet lam π)), hprob⟩ htrans hIco
  rw [hν₀', Measure.map_map measurable_proj measurable_subtype_coe] at hfinal
  exact hfinal

/-- **Theorem 4.11, uniqueness half**: the only probability on the compact space `[0⁺, 1⁻]`
invariant under the germ map is the lift of Lebesgue measure along the total section
`germSectionIco`.  Together with `map_germSectionIco_invariant` just below — which supplies the
existence half — this is the full statement of unique ergodicity of `T̃` on `[0⁺, 1⁻]`.  Tool 1
consumes only this uniqueness form. -/
theorem uniqueErgodicOn_rightPart {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin n)) (h : (∑ i, (lam i : ℝ)) = 1)
    (hH1 : ∀ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ).map (mkIETFun lam π 0) = (μ : Measure ℝ) →
      (μ : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1 → (μ : Measure ℝ) = unitMeas) :
    ∀ ν : ProbabilityMeasure ↥(ietRightPart lam π),
      (ν : Measure ↥(ietRightPart lam π)).map (ietGermRight lam π h.le)
        = (ν : Measure ↥(ietRightPart lam π)) →
      (ν : Measure ↥(ietRightPart lam π))
        = unitMeas.map (germSectionIco (D := ietSplitSet lam π)) :=
  haveI : Countable (ietSplitSet lam π) := splitSet_countable _ _
  by
  intro ν hν
  have hpush := map_proj_eq_unitMeas_of_invariant lam π h hH1 ν hν
  exact lift_unique_on_Ico (lam := unitMeas) unitMeas_singleton (ietSplitSet lam π)
    (splitSet_countable _ _) (fun z : ↥(ietRightPart lam π) => SplitI.proj z.1)
    (germSectionIco (D := ietSplitSet lam π)) (measurable_proj.comp measurable_subtype_coe)
    (fun x hx => proj_germSectionIco hx) measurable_germSectionIco
    (fun z z' hz hzD => Subtype.ext (SplitI.eq_of_proj_eq_of_notMem hz hzD)) hpush unitMeas_Ico

/-- **The lift of Lebesgue measure is invariant under the germ map**, Blueprint 2 Lemma 4.8 for the
exchange: together with `uniqueErgodicOn_rightPart` (at most one invariant probability) this is the
full statement of unique ergodicity of `T̃` on `[0⁺, 1⁻]`. -/
theorem map_germSectionIco_invariant {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin n)) (h : (∑ i, (lam i : ℝ)) = 1) :
    (unitMeas.map (germSectionIco (D := ietSplitSet lam π))).map
        (ietGermRight lam π h.le) =
      unitMeas.map (germSectionIco (D := ietSplitSet lam π)) := by
  classical
  have _ : Countable (ietSplitSet lam π) := splitSet_countable _ _
  have hT := isCutSet_mkIET lam π h.le
  have hkey : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      ietGermRight lam π h.le (germSectionIco (D := ietSplitSet lam π) x)
        = germSectionIco (D := ietSplitSet lam π) (mkIETFun lam π 0 x) := by
    intro x hx
    have hTx : mkIETFun lam π 0 x ∈ Set.Ico (0 : ℝ) 1 := hT.mapsTo x hx
    apply Subtype.ext
    have h1 : (germSectionIco (D := ietSplitSet lam π) x).1
        = SplitI.rightGerm (D := ietSplitSet lam π) x ⟨hx.1, le_of_lt hx.2⟩ :=
      rightGerm_congr (clampIco_mem_Icc x) ⟨hx.1, le_of_lt hx.2⟩ (clampIco_eq_self hx)
    have h2 : (germSectionIco (D := ietSplitSet lam π) (mkIETFun lam π 0 x)).1
        = SplitI.rightGerm (D := ietSplitSet lam π) (mkIETFun lam π 0 x)
            ⟨hTx.1, le_of_lt hTx.2⟩ :=
      rightGerm_congr (clampIco_mem_Icc _) ⟨hTx.1, le_of_lt hTx.2⟩ (clampIco_eq_self hTx)
    change ((ietGermRight lam π h.le (germSectionIco (D := ietSplitSet lam π) x) :
        ↥(ietRightPart lam π)) : SplitI (ietSplitSet lam π)) = _
    rw [show ((ietGermRight lam π h.le (germSectionIco (D := ietSplitSet lam π) x) :
          ↥(ietRightPart lam π)) : SplitI (ietSplitSet lam π))
        = germMap lam π h.le (germSectionIco (D := ietSplitSet lam π) x).1 from rfl]
    calc germMap lam π h.le (germSectionIco (D := ietSplitSet lam π) x).1
        = germMap lam π h.le (SplitI.rightGerm (D := ietSplitSet lam π) x
            ⟨hx.1, le_of_lt hx.2⟩) := by rw [h1]
      _ = SplitI.rightGerm (D := ietSplitSet lam π) (mkIETFun lam π 0 x)
            ⟨hTx.1, le_of_lt hTx.2⟩ := germMap_rightGerm lam π h.le hx
      _ = _ := h2.symm
  have hae : (fun x => ietGermRight lam π h.le (germSectionIco (D := ietSplitSet lam π) x))
      =ᵐ[unitMeas]
        (fun x => germSectionIco (D := ietSplitSet lam π) (mkIETFun lam π 0 x)) := by
    rw [Filter.EventuallyEq, ae_iff]
    have hcompl : unitMeas (Set.Ico (0 : ℝ) 1)ᶜ = 0 := by
      rw [measure_compl measurableSet_Ico (measure_ne_top _ _), unitMeas_Ico, measure_univ,
        tsub_self]
    refine measure_mono_null ?_ hcompl
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    exact fun hxI => hx (hkey x hxI)
  have hnn : (∑ i, lam i : ℝ≥0) = 1 := by
    rw [← NNReal.coe_inj, NNReal.coe_sum]
    exact_mod_cast h
  have hinv : unitMeas.map (mkIETFun lam π 0) = unitMeas := by
    have h1 := InvariantMeasure.invariant_unitMeas (mkIET1' lam π hnn)
    unfold Invariant at h1
    rw [← IETDatum₂.toEquiv_mkIET1 lam π hnn]
    simpa using h1
  calc (unitMeas.map (germSectionIco (D := ietSplitSet lam π))).map
        (ietGermRight lam π h.le)
      = unitMeas.map ((fun z => ietGermRight lam π h.le z) ∘
          (germSectionIco (D := ietSplitSet lam π))) := by
        rw [Measure.map_map (continuous_ietGermRight lam π h.le).measurable
          measurable_germSectionIco]
    _ = unitMeas.map ((germSectionIco (D := ietSplitSet lam π)) ∘
          (mkIETFun lam π 0)) := Measure.map_congr hae
    _ = (unitMeas.map (mkIETFun lam π 0)).map
          (germSectionIco (D := ietSplitSet lam π)) := by
        exact (Measure.map_map measurable_germSectionIco hT.measurable).symm
    _ = unitMeas.map (germSectionIco (D := ietSplitSet lam π)) := by rw [hinv]

/-! ## Theorem 2: uniform Birkhoff convergence from unique ergodicity -/

/-- **Theorem 2**: uniform Birkhoff convergence for the interval exchange `mkIET1 lam π`, from
unique ergodicity alone — Definition 2.1's weak form, a unique invariant probability measure carried
by `[0, 1)`.

The proof applies Tool 1 to the restriction of the germ map to the compact space `[0⁺, 1⁻]`, whose
unique invariant probability is the lift of Lebesgue measure (Theorem 4.11), and transfers the
convergence back to the exchange along the right-germ section.  Its first step is the content of
Definition 2.1: the invariant probability measure with mass `1` on `[0, 1)` is Lebesgue measure
(`invariant_unitMeas`, `unitMeas_Ico`, and the uniqueness). -/
theorem uniformBirkhoff_mkIET1 {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin n)) (h : lam ∈ simplex n)
    (hue : UniqueErgodic (mkIET1 lam π)) :
    UniformBirkhoff (mkIET1 lam π) := by
  rw [mkIET1_of_mem h]
  -- the weak form: every invariant probability with mass `1` on `[0, 1)` is Lebesgue measure
  have hH1 : ∀ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ).map (mkIETFun lam π 0) = (μ : Measure ℝ) →
      (μ : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1 → (μ : Measure ℝ) = unitMeas := by
    intro μ hμinv hμm
    have hcoe : ⇑(mkIET1 lam π) = mkIETFun lam π 0 := coe_mkIET1 lam π h
    have hμInv : Invariant μ (mkIET1 lam π) := by
      unfold Invariant
      rw [hcoe]
      exact hμinv
    have hlebInv : Invariant InvariantMeasure.lebesgue (mkIET1 lam π) :=
      InvariantMeasure.invariant_unitMeas (mkIET1 lam π)
    have hlebMass : (InvariantMeasure.lebesgue : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1 := unitMeas_Ico
    have hue' : ∃! μ : ProbabilityMeasure ℝ,
        Invariant μ (mkIET1 lam π) ∧ (μ : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1 := hue
    obtain ⟨m, ⟨hmInv, hmMass⟩, huniq⟩ := hue'
    have hμeq : μ = InvariantMeasure.lebesgue :=
      (huniq μ ⟨hμInv, hμm⟩).trans (huniq InvariantMeasure.lebesgue ⟨hlebInv, hlebMass⟩).symm
    rw [hμeq]
    rfl
  have : Countable (ietSplitSet lam π) := splitSet_countable _ _
  have hsum : (∑ i, (lam i : ℝ)) = 1 := by exact_mod_cast h
  classical
  -- the lift of Lebesgue measure to `[0⁺, 1⁻]`
  set μ₀ : ProbabilityMeasure ↥(ietRightPart lam π) :=
    ⟨unitMeas.map (germSectionIco (D := ietSplitSet lam π)),
      Measure.isProbabilityMeasure_map measurable_germSectionIco.aemeasurable⟩ with hμ₀
  -- uniqueness of the invariant probability on `[0⁺, 1⁻]`
  have huniq : ∀ ν : ProbabilityMeasure ↥(ietRightPart lam π),
      (ν : Measure ↥(ietRightPart lam π)).map (ietGermRight lam π hsum.le)
        = (ν : Measure ↥(ietRightPart lam π)) → ν = μ₀ := by
    intro ν hν
    have h1 := uniqueErgodicOn_rightPart lam π hsum hH1 ν hν
    refine Subtype.ext ?_
    have h2 : (μ₀ : Measure ↥(ietRightPart lam π))
        = unitMeas.map (germSectionIco (D := ietSplitSet lam π)) := by
      rw [hμ₀]
      exact ProbabilityMeasure.coe_mk _ _
    exact h1.trans h2.symm
  -- the two limits agree
  have hint : ∀ ψ : SplitI (ietSplitSet lam π) → ℝ, Continuous ψ →
      ∫ w, ψ w.1 ∂(μ₀ : Measure ↥(ietRightPart lam π))
        = ∫ z, ψ z ∂((μ₀ : Measure ↥(ietRightPart lam π)).map Subtype.val) := by
    intro ψ hψ
    exact (integral_map measurable_subtype_coe.aemeasurable hψ.aestronglyMeasurable).symm
  -- Tool 1 on `[0⁺, 1⁻]`, transported to the whole split interval
  have hconv : ∀ ψ : SplitI (ietSplitSet lam π) → ℝ, Continuous ψ → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∀ z ∈ SplitI.rightPart (ietSplitSet lam π),
        |birkhoffAverage ℝ (germMap lam π hsum.le) ψ n z
          - ∫ z, ψ z ∂((μ₀ : Measure ↥(ietRightPart lam π)).map Subtype.val)| ≤ ε := by
    intro ψ hψ ε hε
    have h := forall_mem_rightPart_of_subtype (germMap lam π hsum.le)
      (mapsTo_rightPart lam π hsum.le) ψ
      (c := ∫ w, ψ w.1 ∂(μ₀ : Measure ↥(ietRightPart lam π)))
      (fun ε hε => tendsto_uniform_birkhoffAverage (ietGermRight lam π hsum.le)
        (continuous_ietGermRight lam π hsum.le) μ₀ huniq (fun w => ψ w.1)
        (hψ.comp continuous_subtype_val) ε hε)
    rw [hint ψ hψ] at h
    exact h ε hε
  -- the exchange and its equivariance with the germ map
  have hTIco : ∀ x ∈ Set.Ico (0 : ℝ) 1, mkIETFun lam π 0 x ∈ Set.Ico (0 : ℝ) 1 := fun x hx =>
    (isCutSet_mkIET lam π hsum.le).mapsTo x hx
  have hG : ∀ x (hx : x ∈ Set.Ico (0 : ℝ) 1),
      germMap lam π hsum.le (SplitI.rightGerm x ⟨hx.1, le_of_lt hx.2⟩)
        = SplitI.rightGerm (mkIETFun lam π 0 x) ⟨(hTIco x hx).1, (hTIco x hx).2.le⟩ :=
    fun x hx => germMap_rightGerm lam π hsum.le hx
  refine uniformBirkhoff_of_proj (D := ietSplitSet lam π) (germMap lam π hsum.le) (mkIET1' lam π h)
    ((μ₀ : Measure ↥(ietRightPart lam π)).map Subtype.val) hTIco hG hconv ?_
  -- the lift of Lebesgue measure projects back to Lebesgue measure
  have hμ₀' : (μ₀ : Measure ↥(ietRightPart lam π))
      = unitMeas.map (germSectionIco (D := ietSplitSet lam π)) := by
    rw [hμ₀]
    exact ProbabilityMeasure.coe_mk _ _
  have hae : (fun x => SplitI.proj (germSectionIco (D := ietSplitSet lam π) x).1)
      =ᵐ[unitMeas] id := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx using proj_germSectionIco hx
  calc ((μ₀ : Measure ↥(ietRightPart lam π)).map Subtype.val).map SplitI.proj
      = (unitMeas.map (germSectionIco (D := ietSplitSet lam π))).map
          (SplitI.proj ∘ Subtype.val) := by
        rw [hμ₀', Measure.map_map measurable_proj measurable_subtype_coe]
    _ = unitMeas.map
          ((SplitI.proj ∘ Subtype.val) ∘ germSectionIco (D := ietSplitSet lam π)) :=
        Measure.map_map (measurable_proj.comp measurable_subtype_coe) measurable_germSectionIco
    _ = unitMeas.map id := Measure.map_congr hae
    _ = unitMeas := Measure.map_id

/-! ## Every exchange: the strong form, and Lemma 2.9 -/

/-- **Unique ergodicity is uniform Birkhoff convergence**, for every exchange on `[0, 1)` — not only
for the presentations `mkIET1 lam π`: re-present the exchange as `mkIETEquiv lam π 0`
(`exists_mkIETEquiv_eq`), apply Theorem 2 (`uniformBirkhoff_mkIET1`), and transport the conclusion
along the equality of the underlying functions. -/
theorem uniformBirkhoff_of_uniqueErgodic (f : IET 0 1) (hue : UniqueErgodic f) :
    UniformBirkhoff f := by
  obtain ⟨n, hn, lam, π, hsum, he⟩ := exists_mkIETEquiv_eq (a := 0) (b := 1) zero_le_one f.isIET
  -- the re-presentation, as functions
  have hcoe : ⇑f = mkIETFun lam π 0 := by
    rw [show ⇑f = ⇑f.toEquiv from rfl, he, coe_mkIETEquiv]
  have hmem : lam ∈ simplex n := by
    simp only [simplex, Set.mem_ofPred_eq]
    have h1 : (∑ i, (lam i : ℝ)) = 1 := by rw [hsum]; norm_num
    exact_mod_cast h1
  -- hence `f` *is* `mkIET1 lam π`
  have hfun : ⇑(mkIET1 lam π) = ⇑f := (coe_mkIET1 lam π hmem).trans hcoe.symm
  have hIET : mkIET1 lam π = f := IET.ext fun x => congrFun hfun x
  rw [← hIET]
  exact uniformBirkhoff_mkIET1 lam π hmem (by rw [hIET]; exact hue)

/-- **Lemma 2.9** (display (2.2)).  Get a continuous function `ψ ≥ 1_S` with `∫ ψ ≤ Leb S + ε/2`
from the closure-plus-Urysohn route (no re-presentation of `S` by disjoint pieces is needed: the
open set comes from outer regularity applied to the closure, whose measure is that of `S` because
`S` is a finite union of half-open intervals), then apply uniform Birkhoff convergence — Theorem 2,
`uniformBirkhoff_of_uniqueErgodic` — to `ψ`. -/
theorem exists_uniform_birkhoff (f : IET 0 1) (hue : UniqueErgodic f) (S : Set ℝ)
    (hS : IsFiniteUnionIntervals S) (ε : ℝ) (hε : 0 < ε) (hvol : unitMeas.real S ≤ ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Set.Ico (0 : ℝ) 1,
      (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, S.indicator (fun _ => (1 : ℝ)) ((f ^ i) x) ≤ 2 * ε := by
  classical
  -- `S` is given as a finite union of half-open intervals
  obtain ⟨P, hP⟩ := hS
  have hS_eq : S = ⋃ p ∈ P, Set.Ico p.1 p.2 := by
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    exact hP x
  have hSmeas : MeasurableSet S := by
    rw [hS_eq]
    exact Finset.measurableSet_biUnion _ (fun p _ => measurableSet_Ico)
  -- only the part of `S` inside `[0, 1)` matters
  set T : Set ℝ := S ∩ Set.Ico (0 : ℝ) 1 with hT
  have hunitS : unitMeas.real S = volume.real T := by
    rw [hT, unitMeas, Measure.real, Measure.real, Measure.restrict_apply hSmeas,
      Set.inter_comm S]
  have hTsub : T ⊆ Set.Ico (0 : ℝ) 1 := Set.inter_subset_right
  have hT_eq : T = ⋃ p ∈ P, Set.Ico (max p.1 0) (min p.2 1) := by
    rw [hT, hS_eq]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop, Set.mem_Ico]
    constructor
    · rintro ⟨⟨p, hp, hxp⟩, h0, h1⟩
      exact ⟨p, hp, max_le hxp.1 h0, lt_min hxp.2 h1⟩
    · rintro ⟨p, hp, hmax, hmin⟩
      exact ⟨⟨p, hp, ⟨le_trans (le_max_left _ _) hmax, lt_of_lt_of_le hmin (min_le_left _ _)⟩⟩,
        le_trans (le_max_right _ _) hmax, lt_of_lt_of_le hmin (min_le_right _ _)⟩
  -- the closed over-approximation `⋃ [max a 0, min b 1]` of `T`
  have hclosed : IsClosed (⋃ p ∈ P, Set.Icc (max p.1 0) (min p.2 1)) := by
    have h : IsClosed (⋃ p : {p : ℝ × ℝ // p ∈ P}, Set.Icc (max (p.1).1 0) (min (p.1).2 1)) :=
      isClosed_iUnion_of_finite (fun p => isClosed_Icc)
    have heq : (⋃ p ∈ P, Set.Icc (max p.1 0) (min p.2 1))
        = ⋃ p : {p : ℝ × ℝ // p ∈ P}, Set.Icc (max (p.1).1 0) (min (p.1).2 1) := by
      ext x
      simp only [Set.mem_iUnion, Subtype.exists, exists_prop]
    rw [heq]
    exact h
  have hcl_sub : closure T ⊆ ⋃ p ∈ P, Set.Icc (max p.1 0) (min p.2 1) := by
    rw [IsClosed.closure_subset_iff hclosed]
    intro x hx
    rw [hT_eq] at hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨p, hp, ⟨hxp.1, le_of_lt hxp.2⟩⟩
  -- `closure T \ T` consists of right endpoints, hence is null
  have hdiff : closure T \ T ⊆ ⋃ p ∈ P, ({min p.2 1} : Set ℝ) := by
    rintro x ⟨hxcl, hxT⟩
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hcl_sub hxcl)
    have hxa : max p.1 0 ≤ x := hxp.1
    have hxb : x ≤ min p.2 1 := hxp.2
    have hne : x = min p.2 1 := by
      by_contra hne'
      have hlt : x < min p.2 1 := lt_of_le_of_ne hxb hne'
      refine hxT ?_
      rw [hT_eq]
      exact Set.mem_iUnion₂.mpr ⟨p, hp, ⟨hxa, hlt⟩⟩
    exact Set.mem_iUnion₂.mpr ⟨p, hp, by simp [hne]⟩
  have hcl_le : volume (closure T) ≤ volume T := by
    have h1 : closure T ⊆ T ∪ ⋃ p ∈ P, ({min p.2 1} : Set ℝ) := by
      intro x hx
      by_cases h : x ∈ T
      · exact Or.inl h
      · exact Or.inr (hdiff ⟨hx, h⟩)
    have h3 : volume (⋃ p ∈ P, ({min p.2 1} : Set ℝ)) = 0 := by
      refine le_bot_iff.mp (le_trans (measure_biUnion_finset_le P (fun p => ({min p.2 1} : Set ℝ)))
        ?_)
      simp
    calc volume (closure T) ≤ volume (T ∪ ⋃ p ∈ P, ({min p.2 1} : Set ℝ)) := measure_mono h1
      _ ≤ volume T + volume (⋃ p ∈ P, ({min p.2 1} : Set ℝ)) := measure_union_le _ _
      _ = volume T := by rw [h3, add_zero]
  have hTfin : volume T ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hTsub)
    rw [Real.volume_Ico]
    norm_num
  have hcl_fin : volume (closure T) ≠ ⊤ := ne_top_of_le_ne_top hTfin hcl_le
  -- an open set above the closure, of almost the same measure
  have hcl_meas : MeasurableSet (closure T) := isClosed_closure.measurableSet
  obtain ⟨U, hTU, hUopen, hUfin, hUdiff⟩ :=
    hcl_meas.exists_isOpen_sdiff_lt hcl_fin
      (ε := ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  -- Urysohn: a continuous function that is `1` on `closure T` and `0` off `U`
  obtain ⟨ψ, hψ0, hψ1, hψrange⟩ :=
    exists_continuous_zero_one_of_isClosed hUopen.isClosed_compl isClosed_closure
      (Set.disjoint_left.mpr (fun x hx hx' => hx (hTU hx')))
  have hψcont : Continuous (⇑ψ) := ψ.continuous
  have hψ_ge : ∀ x ∈ T, (1 : ℝ) ≤ ψ x := by
    intro x hx
    have h := hψ1 (subset_closure hx)
    simp only [Pi.one_apply] at h
    rw [h]
  have hψ_nonneg : ∀ x, 0 ≤ ψ x := fun x => (hψrange x).1
  have hψ_01 : ∀ x, ψ x ≤ 1 := fun x => (hψrange x).2
  have hψ_le_ind : ∀ x, ψ x ≤ U.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx]; exact hψ_01 x
    · have h0 := hψ0 (by simpa using hx)
      simp only [Pi.zero_apply] at h0
      rw [Set.indicator_of_notMem hx, h0]
  -- the integral of `ψ` is at most `ε + ε/2`
  have hInt : ∫ y, ψ y ∂unitMeas ≤ unitMeas.real S + ε / 2 := by
    have hψ_int : Integrable (⇑ψ) unitMeas := by
      refine Integrable.of_bound hψcont.aestronglyMeasurable 1 ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hψ_nonneg x], hψ_01 x⟩
    have hind_int : Integrable (fun x => U.indicator (fun _ => (1 : ℝ)) x) unitMeas :=
      Integrable.indicator (integrable_const 1) hUmeas
    have h1 : ∫ y, ψ y ∂unitMeas ≤ ∫ y, U.indicator (fun _ => (1 : ℝ)) y ∂unitMeas :=
      integral_mono hψ_int hind_int hψ_le_ind
    have h2 : ∫ y, U.indicator (fun _ => (1 : ℝ)) y ∂unitMeas = unitMeas.real U :=
      integral_indicator_one hUmeas
    have h3 : unitMeas.real U ≤ volume.real U := by
      rw [unitMeas, Measure.real, Measure.real, Measure.restrict_apply hUmeas]
      exact ENNReal.toReal_mono hUfin.ne (measure_mono Set.inter_subset_left)
    have h4 : volume.real U ≤ volume.real (closure T) + ε / 2 := by
      have hun : closure T ∪ (U \ closure T) = U := by
        ext x
        simp only [Set.mem_union, Set.mem_sdiff]
        constructor
        · rintro (h | ⟨h, -⟩)
          · exact hTU h
          · exact h
        · intro h
          by_cases hc : x ∈ closure T
          · exact Or.inl hc
          · exact Or.inr ⟨h, hc⟩
      have hle : volume U ≤ volume (closure T) + volume (U \ closure T) := by
        have h := measure_union_le (μ := volume) (closure T) (U \ closure T)
        rwa [hun] at h
      have hfin2 : volume (U \ closure T) ≠ ⊤ :=
        ne_top_of_le_ne_top hUfin.ne (measure_mono Set.sdiff_subset)
      have hsmall : (volume (U \ closure T)).toReal ≤ ε / 2 := by
        have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (le_of_lt hUdiff)
        rwa [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ ε / 2)] at h
      calc volume.real U ≤ (volume (closure T) + volume (U \ closure T)).toReal := by
            rw [Measure.real]; exact ENNReal.toReal_mono (by simp [hcl_fin, hfin2]) hle
        _ = volume.real (closure T) + (volume (U \ closure T)).toReal :=
            ENNReal.toReal_add hcl_fin hfin2
        _ ≤ volume.real (closure T) + ε / 2 := by linarith
    have h5 : volume.real (closure T) ≤ volume.real T := by
      rw [Measure.real, Measure.real]
      exact ENNReal.toReal_mono hTfin hcl_le
    have h6 : volume.real T = unitMeas.real S := hunitS.symm
    linarith
  -- uniform Birkhoff convergence, from unique ergodicity (Theorem 2)
  have hNB := uniformBirkhoff_of_uniqueErgodic f hue (⇑ψ) hψcont (ε / 2) (by linarith)
  obtain ⟨N, hNpos, hN⟩ := hNB
  refine ⟨N, hNpos, fun x hx => ?_⟩
  have hbirk := hN N le_rfl x hx
  simp only [birkhoffAverage, birkhoffSum, smul_eq_mul] at hbirk
  have h2 : (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, ψ ((f ^ i) x) ≤ 2 * ε := by
    have h3 : (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, ψ ((f ^ i) x) - ∫ y, ψ y ∂unitMeas ≤ ε / 2 := by
      simpa only [IET.pow_apply_iterate] using (abs_le.mp hbirk).2
    linarith
  -- pointwise comparison of the two Birkhoff sums
  have hfmap : ∀ y ∈ Set.Ico (0 : ℝ) 1, f y ∈ Set.Ico (0 : ℝ) 1 :=
    fun y hy => f.isIET.mapsTo hy
  have hpow (i : ℕ) : (f ^ i) x ∈ Set.Ico (0 : ℝ) 1 := by
    induction i with
    | zero => simpa using hx
    | succ k ih => rw [pow_succ']; exact hfmap _ ih
  have hsum : ∑ i ∈ Finset.range N, S.indicator (fun _ => (1 : ℝ)) ((f ^ i) x)
      ≤ ∑ i ∈ Finset.range N, ψ ((f ^ i) x) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hmem := hpow i
    by_cases h : (f ^ i) x ∈ S
    · rw [Set.indicator_of_mem h]
      exact hψ_ge _ ⟨h, hmem⟩
    · rw [Set.indicator_of_notMem h]
      exact hψ_nonneg _
  have h4 : (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, S.indicator (fun _ => (1 : ℝ)) ((f ^ i) x)
      ≤ (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, ψ ((f ^ i) x) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  linarith

end IETFree.UniqueErgodicity

end
