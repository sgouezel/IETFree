/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The split interval

The interval `[0,1]` with the points of a set `D ⊆ ℝ` doubled: a point of the split interval
is a pair `z = (x, χ)` where `x ∈ [0, 1]` and `χ : D → Bool` records, for every `d ∈ D`,
whether `x` lies to the left or to the right of `d`; when `x = d` the value `χ d` is free,
which is exactly the doubling of `d`.  The topology is the subspace topology of
`ℝ × (D → Bool)`.

We prove that the split interval is a compact Hausdorff pseudo-metrizable Borel space, define the
projection and the two germs of a point of `[0,1]`, and show that every point is one of the two
germs of its projection, describing the one-sided neighbourhoods.  The germ map of an interval
exchange itself, and its equivariance on right germs, are `germMapOf` in `Germ/Basic.lean`, above.
`clampI`, the real-valued projection onto `[0, 1]`, is here because both the germ section and its
transfer use it.
-/

@[expose] public section

open Set Function Filter Topology
open scoped BigOperators

namespace IntervalExchange.UniqueErgodicity

/-- The defining condition of the split interval: `x ∈ [0,1]` and the side choice `χ` is
compatible with `x`. -/
def SplitCond (D : Set ℝ) (z : ℝ × (D → Bool)) : Prop :=
  z.1 ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ d : D, (z.1 < (d : ℝ) → z.2 d = false) ∧ ((d : ℝ) < z.1 → z.2 d = true)

/-- **The split interval** over `[0,1]` with split points `D`: the interval `[0,1]` in which each
point of `D` is doubled.  It is a subtype of `ℝ × (D → Bool)`. -/
abbrev SplitI (D : Set ℝ) : Type := {z : ℝ × (D → Bool) // SplitCond D z}

namespace SplitI

variable {D : Set ℝ}

theorem isClosed_splitCond : IsClosed {z : ℝ × (D → Bool) | SplitCond D z} := by
  have hEq : {z : ℝ × (D → Bool) | SplitCond D z}
      = {z : ℝ × (D → Bool) | z.1 ∈ Set.Icc (0 : ℝ) 1} ∩
        ⋂ d : D, ({z : ℝ × (D → Bool) | z.1 < (d : ℝ) → z.2 d = false} ∩
          {z : ℝ × (D → Bool) | (d : ℝ) < z.1 → z.2 d = true}) := by
    ext z
    simp only [SplitCond, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, forall_and]
  rw [hEq]
  refine IsClosed.inter (isClosed_Icc.preimage continuous_fst) (isClosed_iInter fun d => ?_)
  have h1 : {z : ℝ × (D → Bool) | z.1 < (d : ℝ) → z.2 d = false}
      = {z : ℝ × (D → Bool) | (d : ℝ) ≤ z.1}
          ∪ {z : ℝ × (D → Bool) | z.2 d = false} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro hz
      by_cases hlt : z.1 < (d : ℝ)
      · exact Or.inr (hz hlt)
      · exact Or.inl (not_lt.mp hlt)
    · rintro (hz | hz) hlt
      · exact absurd hlt (not_lt.mpr hz)
      · exact hz
  have h2 : {z : ℝ × (D → Bool) | (d : ℝ) < z.1 → z.2 d = true}
      = {z : ℝ × (D → Bool) | z.1 ≤ (d : ℝ)}
          ∪ {z : ℝ × (D → Bool) | z.2 d = true} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro hz
      by_cases hlt : (d : ℝ) < z.1
      · exact Or.inr (hz hlt)
      · exact Or.inl (not_lt.mp hlt)
    · rintro (hz | hz) hlt
      · exact absurd hlt (not_lt.mpr hz)
      · exact hz
  rw [h1, h2]
  refine IsClosed.inter ?_ ?_
  · exact (isClosed_le continuous_const continuous_fst).union
      (isClosed_eq ((continuous_apply d).comp continuous_snd) continuous_const)
  · exact (isClosed_le continuous_fst continuous_const).union
      (isClosed_eq ((continuous_apply d).comp continuous_snd) continuous_const)

theorem isCompact_splitCond : IsCompact {z : ℝ × (D → Bool) | SplitCond D z} :=
  (isCompact_Icc.prod isCompact_univ).of_isClosed_subset isClosed_splitCond
    (fun _ hz => ⟨hz.1, mem_univ _⟩)

instance instCompactSpace : CompactSpace (SplitI D) :=
  isCompact_iff_compactSpace.mp isCompact_splitCond

/-- **The projection** of the split interval onto `[0,1]`: it collapses the two germs of a split
point. -/
def proj (z : SplitI D) : ℝ := z.1.1

theorem continuous_proj : Continuous (proj (D := D)) :=
  continuous_fst.comp continuous_subtype_val

theorem proj_mem_Icc (z : SplitI D) : proj z ∈ Set.Icc (0 : ℝ) 1 := z.2.1

/-- The `d`-th coordinate of a point of the split interval, as a continuous function. -/
theorem continuous_coord (d : D) : Continuous (fun z : SplitI D => z.1.2 d) :=
  (continuous_apply d).comp (continuous_snd.comp continuous_subtype_val)

/-- The side constraint at a split point lying to the left of the projection. -/
theorem coord_of_lt {z : SplitI D} {d : D} (h : (d : ℝ) < proj z) : z.1.2 d = true :=
  (z.2.2 d).2 h

/-- The side constraint at a split point lying to the right of the projection. -/
theorem coord_of_lt' {z : SplitI D} {d : D} (h : proj z < (d : ℝ)) : z.1.2 d = false :=
  (z.2.2 d).1 h

@[ext] theorem ext {z z' : SplitI D} (h1 : proj z = proj z') (h2 : z.1.2 = z'.1.2) : z = z' :=
  Subtype.ext (Prod.ext h1 h2)

/-- **The fibre of the projection over a point outside the split set is a single point.**  Two
points of the split interval with the same projection outside `D` have the same side choices, so
they are equal. -/
theorem eq_of_proj_eq_of_notMem {z z' : SplitI D} (h : proj z = proj z')
    (hz : proj z ∉ D) : z = z' := by
  refine ext h (funext fun d => ?_)
  rcases lt_trichotomy (d : ℝ) (proj z) with hlt | heq | hgt
  · rw [coord_of_lt hlt, coord_of_lt (h ▸ hlt)]
  · exact absurd (heq ▸ d.2) hz
  · rw [coord_of_lt' hgt, coord_of_lt' (h ▸ hgt)]

/-- **The right germ** of a point `x ∈ [0,1]`: the point of the split interval sitting at `x` and
to the right of every split point `d ≤ x`. -/
noncomputable def rightGerm (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : SplitI D :=
  ⟨(x, fun _d : D => decide ((_d : ℝ) ≤ x)),
    ⟨hx, fun d => ⟨fun h => decide_eq_false_iff_not.mpr (not_le.mpr (h : x < (d : ℝ))),
      fun h => decide_eq_true_iff.mpr (le_of_lt (h : (d : ℝ) < x))⟩⟩⟩

/-- **The left germ** of a point `x ∈ [0,1]`: the point of the split interval sitting at `x` and
to the left of every split point `d ≥ x`. -/
noncomputable def leftGerm (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : SplitI D :=
  ⟨(x, fun _d : D => decide ((_d : ℝ) < x)),
    ⟨hx, fun d =>
      ⟨fun h => decide_eq_false_iff_not.mpr (not_lt.mpr (le_of_lt (h : x < (d : ℝ)))),
        fun h => decide_eq_true_iff.mpr (h : (d : ℝ) < x)⟩⟩⟩

theorem coord_leftGerm (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (d : D) :
    (leftGerm (D := D) x hx).1.2 d = decide ((d : ℝ) < x) := (rfl)

/-- The coordinate of the **right** germ: `decide (d ≤ x)`. -/
theorem coord_rightGerm (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (d : D) :
    (rightGerm (D := D) x hx).1.2 d = decide ((d : ℝ) ≤ x) := (rfl)

@[simp]
theorem proj_rightGerm (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    proj (D := D) (rightGerm x hx) = x := (rfl)

@[simp]
theorem proj_leftGerm (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    proj (D := D) (leftGerm x hx) = x := (rfl)

theorem rightGerm_eq_leftGerm {x : ℝ} (hx : x ∉ D) (hx1 : x ∈ Set.Icc (0 : ℝ) 1) :
    rightGerm (D := D) x hx1 = leftGerm x hx1 := by
  refine ext rfl (funext fun d => ?_)
  rw [coord_rightGerm, coord_leftGerm]
  rcases lt_trichotomy (d : ℝ) x with h | h | h
  · rw [decide_eq_true_iff.mpr (le_of_lt h), decide_eq_true_iff.mpr h]
  · exact absurd (by rw [← h]; exact d.2) hx
  · rw [decide_eq_false_iff_not.mpr (not_le.mpr h),
      decide_eq_false_iff_not.mpr (not_lt.mpr (le_of_lt h))]

/-- A point of the split interval is determined by its projection and the side choice at its
projection, when the projection is a split point: there are exactly two points above each point of
`[0,1]`. -/
theorem eq_rightGerm_or_leftGerm (z : SplitI D) :
    z = rightGerm (D := D) (proj z) (proj_mem_Icc z) ∨
      z = leftGerm (D := D) (proj z) (proj_mem_Icc z) := by
  by_cases hxD : proj z ∈ D
  · by_cases hb : z.1.2 ⟨proj z, hxD⟩ = true
    · left
      refine ext rfl (funext fun d => ?_)
      rw [coord_rightGerm]
      rcases lt_trichotomy (d : ℝ) (proj z) with h | h | h
      · rw [coord_of_lt h, decide_eq_true_iff.mpr (le_of_lt h)]
      · have hd : d = ⟨proj z, hxD⟩ := Subtype.ext h
        rw [hd, hb, decide_eq_true_iff.mpr le_rfl]
      · rw [coord_of_lt' h, decide_eq_false_iff_not.mpr (not_le.mpr h)]
    · right
      have hf : z.1.2 ⟨proj z, hxD⟩ = false := by
        cases hv : z.1.2 ⟨proj z, hxD⟩
        · rfl
        · exact absurd hv hb
      refine ext rfl (funext fun d => ?_)
      rw [coord_leftGerm]
      rcases lt_trichotomy (d : ℝ) (proj z) with h | h | h
      · rw [coord_of_lt h, decide_eq_true_iff.mpr h]
      · have hd : d = ⟨proj z, hxD⟩ := Subtype.ext h
        rw [hd, hf, decide_eq_false_iff_not.mpr (not_lt.mpr le_rfl)]
      · rw [coord_of_lt' h, decide_eq_false_iff_not.mpr (not_lt.mpr (le_of_lt h))]
  · right
    refine ext rfl (funext fun d => ?_)
    rw [coord_leftGerm]
    rcases lt_trichotomy (d : ℝ) (proj z) with h | h | h
    · rw [coord_of_lt h, decide_eq_true_iff.mpr h]
    · exact absurd (by rw [← h]; exact d.2) hxD
    · rw [coord_of_lt' h, decide_eq_false_iff_not.mpr (not_lt.mpr (le_of_lt h))]

/-- A point whose side choice at its projection is `true` is the right germ of its projection. -/
theorem eq_rightGerm_of_coord_true {z : SplitI D} {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hxD : x ∈ D) (hp : proj z = x) (h : z.1.2 ⟨x, hxD⟩ = true) :
    z = rightGerm (D := D) x hx := by
  subst hp
  refine ext rfl (funext fun d => ?_)
  rw [coord_rightGerm]
  rcases lt_trichotomy (d : ℝ) (proj z) with hlt | heq | hgt
  · rw [coord_of_lt hlt, decide_eq_true_iff.mpr (le_of_lt hlt)]
  · have hd : d = ⟨proj z, hxD⟩ := Subtype.ext heq
    rw [hd, h, decide_eq_true_iff.mpr le_rfl]
  · rw [coord_of_lt' hgt, decide_eq_false_iff_not.mpr (not_le.mpr hgt)]

/-- A point whose side choice at its projection is `false` is the left germ of its projection. -/
theorem eq_leftGerm_of_coord_false {z : SplitI D} {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hxD : x ∈ D) (hp : proj z = x) (h : z.1.2 ⟨x, hxD⟩ = false) :
    z = leftGerm (D := D) x hx := by
  subst hp
  refine ext rfl (funext fun d => ?_)
  rw [coord_leftGerm]
  rcases lt_trichotomy (d : ℝ) (proj z) with hlt | heq | hgt
  · rw [coord_of_lt hlt, decide_eq_true_iff.mpr hlt]
  · have hd : d = ⟨proj z, hxD⟩ := Subtype.ext heq
    rw [hd, h, decide_eq_false_iff_not.mpr (not_lt.mpr le_rfl)]
  · rw [coord_of_lt' hgt, decide_eq_false_iff_not.mpr (not_lt.mpr (le_of_lt hgt))]

/-- The side choice at the projection: `true` unless the point is the left germ of a split
point. -/
noncomputable def side (z : SplitI D) : Bool := by
  classical
  exact if h : proj z ∈ D then z.1.2 ⟨proj z, h⟩ else true

theorem side_rightGerm (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    side (rightGerm (D := D) x hx) = true := by
  unfold side
  split_ifs with h
  · have h' : decide (x ≤ x) = true := by simp
    exact h'
  · rfl

theorem side_leftGerm {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hxD : x ∈ D) :
    side (leftGerm (D := D) x hx) = false := by
  unfold side
  split_ifs with h
  · have h' : decide (x < x) = false := by simp
    exact h'
  · exact absurd hxD h

/-- The set of points of the split interval lying strictly to the right of `x`, together with the
right germ of `x`.  For `x ∈ D` this is the clopen set `{z : χ z x = true}`. -/
def upSet (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : Set (SplitI D) :=
  {z | x < proj z} ∪ {rightGerm x hx}

/-- The set of points of the split interval lying strictly to the left of `x`, together with the
left germ of `x`.  For `x ∈ D` this is the clopen set `{z : χ z x = false}`. -/
def downSet (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : Set (SplitI D) :=
  {z | proj z < x} ∪ {leftGerm x hx}

theorem le_proj_of_mem_upSet {x : ℝ} {hx : x ∈ Set.Icc (0 : ℝ) 1} {z : SplitI D}
    (hz : z ∈ upSet x hx) : x ≤ proj z := by
  have hz' : x < proj z ∨ z = rightGerm (D := D) x hx := hz
  rcases hz' with hz' | rfl
  · exact le_of_lt hz'
  · simp

theorem proj_le_of_mem_downSet {x : ℝ} {hx : x ∈ Set.Icc (0 : ℝ) 1} {z : SplitI D}
    (hz : z ∈ downSet x hx) : proj z ≤ x := by
  have hz' : proj z < x ∨ z = leftGerm (D := D) x hx := hz
  rcases hz' with hz' | rfl
  · exact le_of_lt hz'
  · simp

theorem isClosed_compl_upSet {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hxD : x ∈ D) :
    IsClosed (upSet (D := D) x hx)ᶜ := by
  have hset : (upSet (D := D) x hx)ᶜ
      = {z : SplitI D | proj z ≤ x} ∩ {z : SplitI D | z.1.2 ⟨x, hxD⟩ = false} := by
    ext z
    simp only [upSet, Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_singleton_iff]
    constructor
    · intro hz
      have h1 : ¬ (x < proj z) := fun h => hz (Or.inl h)
      have h2 : z ≠ rightGerm (D := D) x hx := fun h => hz (Or.inr h)
      have hle : proj z ≤ x := not_lt.mp h1
      refine ⟨hle, ?_⟩
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact coord_of_lt' hlt
      · cases hv : z.1.2 ⟨x, hxD⟩
        · rfl
        · exact absurd (eq_rightGerm_of_coord_true hx hxD heq hv) h2
    · rintro ⟨h1, h2⟩ (hz | hz)
      · exact absurd hz (not_lt.mpr h1)
      · rw [hz] at h2
        have h2' : decide (x ≤ x) = false := h2
        simp at h2'
  rw [hset]
  exact (isClosed_le continuous_proj continuous_const).inter
    (isClosed_eq (continuous_coord ⟨x, hxD⟩) continuous_const)

theorem isOpen_upSet {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hxD : x ∈ D) :
    IsOpen (upSet (D := D) x hx) := by
  simpa using (isClosed_compl_upSet hx hxD).isOpen_compl

theorem isClosed_compl_downSet {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hxD : x ∈ D) :
    IsClosed (downSet (D := D) x hx)ᶜ := by
  have hset : (downSet (D := D) x hx)ᶜ
      = {z : SplitI D | x ≤ proj z} ∩ {z : SplitI D | z.1.2 ⟨x, hxD⟩ = true} := by
    ext z
    simp only [downSet, Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_singleton_iff]
    constructor
    · intro hz
      have h1 : ¬ (proj z < x) := fun h => hz (Or.inl h)
      have h2 : z ≠ leftGerm (D := D) x hx := fun h => hz (Or.inr h)
      have hle : x ≤ proj z := not_lt.mp h1
      refine ⟨hle, ?_⟩
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact coord_of_lt hlt
      · cases hv : z.1.2 ⟨x, hxD⟩
        · exact absurd (eq_leftGerm_of_coord_false hx hxD heq.symm hv) h2
        · rfl
    · rintro ⟨h1, h2⟩ (hz | hz)
      · exact absurd hz (not_lt.mpr h1)
      · rw [hz] at h2
        have h2' : decide (x < x) = true := h2
        simp at h2'
  rw [hset]
  exact (isClosed_le continuous_const continuous_proj).inter
    (isClosed_eq (continuous_coord ⟨x, hxD⟩) continuous_const)

theorem isOpen_downSet {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hxD : x ∈ D) :
    IsOpen (downSet (D := D) x hx) := by
  simpa using (isClosed_compl_downSet hx hxD).isOpen_compl

/-- The closed subspace of points that are limits of right germs of points of `[0,1)`: the split
interval with the two endpoint germs `leftGerm 0` and `rightGerm 1` removed. -/
def rightPart (D : Set ℝ) : Set (SplitI D) :=
  closure (range (fun x : Set.Ico (0 : ℝ) 1 => rightGerm x.1 ⟨x.2.1, le_of_lt x.2.2⟩))

theorem isCompact_rightPart (D : Set ℝ) : IsCompact (rightPart D) :=
  isClosed_closure.isCompact

theorem rightGerm_mem_rightPart {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    rightGerm (D := D) x ⟨hx.1, le_of_lt hx.2⟩ ∈ rightPart D :=
  subset_closure ⟨⟨x, hx⟩, rfl⟩

end SplitI

variable {f : ℝ → ℝ} {s : Finset ℝ}

/-- **The split set**: the union of the orbits under `T` of the cuts and of the right end `1`. -/
noncomputable def splitSet (T : ℝ ≃ ℝ) (s : Finset ℝ) : Set ℝ :=
  ⋃ k : ℤ, ⇑(T ^ k) '' ((s : Set ℝ) ∪ {1})

theorem subset_splitSet (T : ℝ ≃ ℝ) (s : Finset ℝ) :
    (s : Set ℝ) ∪ {1} ⊆ splitSet T s :=
  fun _ hx => mem_iUnion.mpr ⟨0, by simpa using hx⟩

theorem mem_splitSet_of_mem (T : ℝ ≃ ℝ) (s : Finset ℝ) {x : ℝ} (hx : x ∈ s) :
    x ∈ splitSet T s :=
  subset_splitSet T s (Or.inl hx)

theorem one_mem_splitSet (T : ℝ ≃ ℝ) (s : Finset ℝ) : (1 : ℝ) ∈ splitSet T s :=
  subset_splitSet T s (Or.inr rfl)

namespace SplitI

end SplitI

/-- The clamp of a real number into `[0, 1]`, used to make the germ section total.  This is
Mathlib's `Set.projIcc 0 1 zero_le_one` composed with the coercion to `ℝ`, kept as a real-valued
function because every use site is an ordinary real number. -/
noncomputable def clampI (x : ℝ) : ℝ := min (max x 0) 1

theorem continuous_clampI : Continuous clampI :=
  (continuous_id.max continuous_const).min continuous_const

theorem clampI_mem (x : ℝ) : clampI x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min (le_max_right x 0) zero_le_one, min_le_right _ _⟩

theorem clampI_eq_self {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : clampI x = x := by
  unfold clampI
  rw [max_eq_left hx.1, min_eq_left hx.2]

end IntervalExchange.UniqueErgodicity

end
