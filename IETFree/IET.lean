/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.CutSetMeasure

/-!
Interval exchanges: the predicate, the explicit construction, and the group.

`IsIET a b f` says that the bare function `f` is the identity or has a cut set, and `cutSet` is the
minimal cut set of such a map.  The file then constructs the exchange attached to a length vector
and a permutation explicitly (`mkIETFun`, `mkIETEquiv`, `mkIET1`, with the cut set `mkIETCuts`),
exhibits the simplex of length vectors as a measure space (`simplexRegion`, `simplexMap`,
`simplexVolume`), with `Positive` for the positivity of a length vector, and
proves the classification `exists_mkIETEquiv_eq` / `isIET_iff_exists_mkIETEquiv`: every exchange is
`mkIETFun` of the lengths and the permutation of any of its cut sets.  It closes with the type
`IET a b` of exchanges as permutations of `ℝ` fixing the complement of `[a, b)`, and its group
structure.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal
/-! ## Exchanges, and the minimal cut set

A cut set forces `a < b` (`IsCutSet.lt`), because `a` is one of its cuts.  So on an **empty**
interval `[a, b)` (that is, `b ≤ a`) the only exchange is the identity, and `IsIET` has to say so
explicitly: it is "the identity, or a map with a cut set". -/

/-- **`f` is an interval exchange on `[a, b)`**: it is the identity, or it has a cut set.  When
`a < b` the two are the same as far as the interesting cases go (`IsIET.exists_isCutSet`); the
identity is listed separately only so that the empty-interval case is not excluded. -/
def IsIET (a b : ℝ) (f : ℝ → ℝ) : Prop := (∀ x, f x = x) ∨ ∃ s, IsCutSet f a b s

namespace IsIET

variable {a b : ℝ} {f g : ℝ → ℝ}

/-- The identity is an exchange. -/
theorem id (a b : ℝ) : IsIET a b id := Or.inl fun _ => rfl

/-- **An exchange on a nonempty interval has a cut set.**  In the identity case, `{a}` is one. -/
theorem exists_isCutSet (h : IsIET a b f) (hab : a < b) : ∃ s, IsCutSet f a b s := by
  rcases h with hid | ⟨s, hs⟩
  · refine ⟨{a}, fun x _ => hid x, fun x _ => hid x, ?_, Finset.mem_singleton_self a, ?_, ?_⟩
    · intro x hx
      rw [hid x]; exact hx
    · intro c hc
      rw [Finset.mem_singleton.mp hc]; exact ⟨le_rfl, hab⟩
    · intro x y _ _ _
      rw [hid x, hid y]; ring
  · exact ⟨s, hs⟩

/-- **On an empty interval only the identity qualifies.** -/
theorem eq_id_of_le (h : IsIET a b f) (hba : b ≤ a) : ∀ x, f x = x := by
  rcases h with hid | ⟨s, hs⟩
  · exact hid
  · exact absurd hs.lt (not_lt.mpr hba)

/-- **An exchange is the identity outside its interval.** -/
theorem eq_of_notMem (h : IsIET a b f) {x : ℝ} (hx : x ∉ Set.Ico a b) : f x = x := by
  rcases h with hid | ⟨s, hs⟩
  · exact hid x
  · rcases not_and_or.mp hx with h1 | h2
    · exact hs.apply_eq_self_of_lt x (not_le.mp h1)
    · exact hs.apply_eq_self_of_le x (not_lt.mp h2)

/-- **An exchange is the identity below `a`.** -/
theorem apply_eq_self_of_lt (h : IsIET a b f) {x : ℝ} (hx : x < a) : f x = x :=
  h.eq_of_notMem (fun hcon => absurd hcon.1 (not_le.mpr hx))

/-- **An exchange is the identity from `b` on.** -/
theorem apply_eq_self_of_le (h : IsIET a b f) {x : ℝ} (hx : b ≤ x) : f x = x :=
  h.eq_of_notMem (fun hcon => absurd hcon.2 (not_lt.mpr hx))

/-- **An exchange maps `[a, b)` into itself.** -/
theorem mapsTo (h : IsIET a b f) {x : ℝ} (hx : x ∈ Set.Ico a b) : f x ∈ Set.Ico a b := by
  rcases h with hid | ⟨s, hs⟩
  · rw [hid x]; exact hx
  · exact hs.mapsTo x hx

/-- **Monotonicity**: an exchange on `[a, b)` is an exchange on any larger interval. -/
theorem mono (h : IsIET a b f) {a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') : IsIET a' b' f := by
  rcases h with hid | ⟨s, hs⟩
  · exact Or.inl hid
  · classical
    have hab : a < b := hs.lt
    have hab' : a' ≤ b := le_trans ha (le_of_lt hab)
    have ha' : a' ∈ (insert a' (s ∪ {a, b})).filter (fun c => c ∈ Set.Ico a' b') := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_insert_self a' _, le_rfl, ?_⟩
      exact lt_of_lt_of_le (lt_of_le_of_lt ha hab) hb
    refine Or.inr ⟨(insert a' (s ∪ {a, b})).filter (fun c => c ∈ Set.Ico a' b'),
      ?_, ?_, ?_, ha', ?_, ?_⟩
    · intro x hx
      exact hs.apply_eq_self_of_lt x (lt_of_lt_of_le hx ha)
    · intro x hx
      exact hs.apply_eq_self_of_le x (le_trans hb hx)
    · intro x hx
      rcases lt_or_ge x a with hxa | hxa
      · rw [hs.apply_eq_self_of_lt x hxa]; exact hx
      · rcases lt_or_ge x b with hxb | hxb
        · exact ⟨le_trans ha (hs.mapsTo x ⟨hxa, hxb⟩).1,
            lt_of_lt_of_le (hs.mapsTo x ⟨hxa, hxb⟩).2 hb⟩
        · rw [hs.apply_eq_self_of_le x hxb]; exact hx
    · intro c hc
      exact (Finset.mem_filter.mp hc).2
    · intro x y hx hy hns
      have hs_sub : s ⊆ (insert a' (s ∪ {a, b})).filter (fun c => c ∈ Set.Ico a' b') := by
        intro c hc
        refine Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ hc),
          ⟨le_trans ha (hs.cuts_mem c hc).1, lt_of_lt_of_le (hs.cuts_mem c hc).2 hb⟩⟩
      rcases lt_or_ge x a with hxa | hxa
      · rw [hs.apply_eq_self_of_lt x hxa]
        rcases lt_or_ge y a with hya | hya
        · rw [hs.apply_eq_self_of_lt y hya]; ring
        · exact absurd ⟨a, Finset.mem_filter.mpr
            ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_insert_self _ _)),
              ha, lt_of_le_of_lt hya hy.2⟩,
            lt_of_le_of_lt (min_le_left _ _) hxa, le_trans hya (le_max_right _ _)⟩ hns
      · rcases lt_or_ge x b with hxb | hxb
        · rcases lt_or_ge y a with hya | hya
          · exact absurd ⟨a, Finset.mem_filter.mpr
              ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_insert_self _ _)),
                ha, lt_of_le_of_lt hxa hx.2⟩,
              lt_of_le_of_lt (min_le_right _ _) hya, le_trans hxa (le_max_left _ _)⟩ hns
          · rcases lt_or_ge y b with hyb | hyb
            · exact hs.transl_of_not_separated x y ⟨hxa, hxb⟩ ⟨hya, hyb⟩ (fun hh => hns
                (Separated.mono hh hs_sub))
            · exact absurd ⟨b, Finset.mem_filter.mpr
                ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_insert_of_mem
                  (Finset.mem_singleton_self b))), hab', lt_of_le_of_lt hyb hy.2⟩,
                lt_of_le_of_lt (min_le_left _ _) hxb, le_trans hyb (le_max_right _ _)⟩ hns
        · rw [hs.apply_eq_self_of_le x hxb]
          rcases lt_or_ge y b with hyb | hyb
          · exact absurd ⟨b, Finset.mem_filter.mpr
              ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_insert_of_mem
                (Finset.mem_singleton_self b))), hab', lt_of_le_of_lt hxb hx.2⟩,
              lt_of_le_of_lt (min_le_right _ _) hyb, le_trans hxb (le_max_left _ _)⟩ hns
          · rw [hs.apply_eq_self_of_le y hyb]; ring

/-- **Composition**: exchanges on `[a, b)` are closed under composition. -/
theorem comp (hf : IsIET a b f) (hg : IsIET a b g) : IsIET a b (g ∘ f) := by
  rcases hf with hid | ⟨s, hs⟩
  · have hgf : (g ∘ f) = g := funext fun x => by simp only [Function.comp_apply, hid x]
    rw [hgf]; exact hg
  · rcases hg with hid | ⟨t, ht⟩
    · have hgf : (g ∘ f) = f := funext fun x => by
        simp only [Function.comp_apply]
        exact hid (f x)
      rw [hgf]; exact Or.inr ⟨s, hs⟩
    · exact Or.inr ⟨_, IsCutSet.comp (f := f) (g := g) hs ht⟩

end IsIET

/-- The cardinalities of the cut sets of `f` are attained. -/
theorem exists_card_cutSet {f : ℝ → ℝ} {a b : ℝ} (h : ∃ s, IsCutSet f a b s) :
    ∃ n, ∃ s, IsCutSet f a b s ∧ s.card = n := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s.card, s, hs, rfl⟩

/-- The **minimal cut set** of `f` on `[a, b)`: a cut set of smallest cardinality, empty if there is
none.  It is contained in *every* cut set (see `cutSet_subset`). -/
noncomputable def cutSet (f : ℝ → ℝ) (a b : ℝ) : Finset ℝ := by
  classical
  exact if h : ∃ s, IsCutSet f a b s then (Nat.find_spec (exists_card_cutSet h)).choose else ∅

/-- The minimal cut set is a cut set, provided there is one. -/
theorem cutSet_isCutSet {f : ℝ → ℝ} {a b : ℝ} (h : ∃ s, IsCutSet f a b s) :
    IsCutSet f a b (cutSet f a b) := by
  classical
  unfold cutSet
  rw [dif_pos h]
  exact (Nat.find_spec (exists_card_cutSet h)).choose_spec.1

/-- The minimal cut set is a cut set for an exchange on a nonempty interval. -/
theorem IsIET.cutSet_isCutSet {f : ℝ → ℝ} {a b : ℝ} (h : IsIET a b f) (hab : a < b) :
    IsCutSet f a b (cutSet f a b) :=
  _root_.cutSet_isCutSet (h.exists_isCutSet hab)

-- the data of one cut set, in scope below (`hs` stays a binder of each declaration)
variable {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}

/-- The minimal cut set has no more cuts than any cut set. -/
theorem card_cutSet_le (hs : IsCutSet f a b s) :
    (cutSet f a b).card ≤ s.card := by
  have h : ∃ t, IsCutSet f a b t := ⟨s, hs⟩
  classical
  unfold cutSet
  rw [dif_pos h]
  have h1 : (Nat.find_spec (exists_card_cutSet h)).choose.card = Nat.find (exists_card_cutSet h) :=
    (Nat.find_spec (exists_card_cutSet h)).choose_spec.2
  rw [h1]
  exact Nat.find_min' (exists_card_cutSet h) ⟨s, hs, rfl⟩

/-- **The minimal cut set is contained in every cut set.** -/
theorem cutSet_subset (hs : IsCutSet f a b s) :
    cutSet f a b ⊆ s := by
  have h : ∃ t, IsCutSet f a b t := ⟨s, hs⟩
  have h₁ : IsCutSet f a b (cutSet f a b ∩ s) := (cutSet_isCutSet h).inter hs
  have h₂ : (cutSet f a b ∩ s).card ≤ (cutSet f a b).card :=
    Finset.card_le_card Finset.inter_subset_left
  have h₃ : (cutSet f a b).card ≤ (cutSet f a b ∩ s).card := card_cutSet_le h₁
  have h₄ : (cutSet f a b).card = (cutSet f a b ∩ s).card := le_antisymm h₃ h₂
  have h₅ : cutSet f a b ∩ s = cutSet f a b :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq h₄)
  exact Finset.inter_eq_left.mp h₅

/-- **The cut set of a composite** is contained in the cut sets of the factors (the second one
pulled back). -/
theorem cutSet_comp_subset {f g : ℝ → ℝ} {a b : ℝ} {s t : Finset ℝ}
    (hf : IsCutSet f a b s) (hg : IsCutSet g a b t) :
    cutSet (g ∘ f) a b ⊆ s ∪ hf.preimage t :=
  cutSet_subset (IsCutSet.comp (f := f) (g := g) hf hg)

/-! ## Lebesgue measure on the simplex -/

/-- The free region: the `d - 1` free coordinates are positive and have total mass less than `1`,
so that every coordinate of the image, including the last one `1 - ∑`, is positive. -/
def simplexRegion (d : ℕ) : Set (Fin (d - 1) → ℝ) :=
  {v | (∀ i, 0 < v i) ∧ ∑ i, v i < 1}

/-- The parametrisation of the simplex: the `d - 1` free coordinates, the last being `1 - ∑`. -/
noncomputable def simplexMap (d : ℕ) (v : Fin (d - 1) → ℝ) : Fin d → ℝ≥0 :=
  fun i =>
    if h : i.val + 1 = d then (1 - ∑ j, v j).toNNReal
    else (v ⟨i.val, by have := i.isLt; omega⟩).toNNReal

/-- **Lebesgue measure on the simplex**: Lebesgue measure on the `d - 1` free coordinates,
restricted to the region where their total mass is less than `1`, transported by the
parametrisation `λ_d = 1 - ∑_{i<d} λ_i`.  Almost every point of the image is in the simplex. -/
noncomputable def simplexVolume (d : ℕ) : Measure (Fin d → ℝ≥0) :=
  Measure.map (simplexMap d) (volume.restrict (simplexRegion d))

/-- **A length vector is positive** when all its coordinates are.  This is the hypothesis under
which the endpoints of the arrangement and the block mass behave (`leftEnd_lt_total`,
`leftEnd_pos_of_ne_zero`, `blockMass_pos`). -/
abbrev Positive {n : ℕ} (lam : Fin n → ℝ≥0) : Prop :=
  ∀ i, 0 < lam i

/-- **The indices of a block of `n` cells**: `k < l ≤ n`.  The instance `NeZero (l - k)`, which
`blockLam` and `mkIET1` need to form the rescaled block, is derived here once, so that no statement
about a block has to carry it. -/
structure BlockIdx (n : ℕ) where
  /-- The index of the first cell of the block. -/
  k : ℕ
  /-- One past the index of the last cell of the block. -/
  l : ℕ
  hkl : k < l
  hln : l ≤ n

instance BlockIdx.instNeZeroLen {n : ℕ} (I : BlockIdx n) : NeZero (I.l - I.k) :=
  ⟨by have := I.hkl; omega⟩

namespace BlockIdx

/-- `k` as an index of `Fin n`.  An `abbrev`, not a `def`: statements about a block mention `I.kFin`
where their proofs work with `⟨k, _⟩`, and a reducible definition lets `rw` and `exact` see through
it (a regular `def` does not unfold during rewrite matching). -/
abbrev kFin {n : ℕ} (I : BlockIdx n) : Fin n := ⟨I.k, by have := I.hkl; have := I.hln; omega⟩

end BlockIdx

/-! ## The exchange built from a length vector and a permutation

**FROZEN.**  The definitions from here to `coe_mkIETEquiv` (`leftEnd`, `upperEnd`, `imageLeft`,
`translationVector`, `imageLengths`, `idx`, `mkIETFun`, `mkIETFun_inv_left`, `mkIETEquiv`) are
frozen: they mirror `Challenge.lean`, which is the comparator target.  Do not change them. -/

/-- Left endpoint of the `i`-th interval of the arrangement with lengths `lam`. -/
noncomputable def leftEnd {n : ℕ} (lam : Fin n → ℝ≥0) (i : Fin n) : ℝ :=
  ∑ j with j < i, (lam j : ℝ)

/-- The right endpoint of the `i`-th interval. -/
noncomputable def upperEnd {n : ℕ} (lam : Fin n → ℝ≥0) (i : Fin n) : ℝ :=
  ∑ j with j ≤ i, (lam j : ℝ)

/-- The left endpoint of the image of the `i`-th interval. -/
noncomputable def imageLeft {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0)
    (i : Fin n) : ℝ :=
  ∑ j with π j < π i, (lam j : ℝ)

/-- The translation vector of the exchange on its `i`-th interval. -/
noncomputable def translationVector {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0)
    (i : Fin n) : ℝ := imageLeft π lam i - leftEnd lam i

/-- The lengths reordered into the order of the images. -/
def imageLengths {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) : Fin n → ℝ≥0 :=
  fun k => lam (π.symm k)

@[simp] theorem leftEnd_zero {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) : leftEnd lam 0 = 0 := by
  simp [leftEnd]

theorem upperEnd_eq {n : ℕ} (lam : Fin n → ℝ≥0) (i : Fin n) :
    upperEnd lam i = leftEnd lam i + (lam i : ℝ) := by
  have h : Finset.univ.filter (fun j : Fin n => j ≤ i)
      = insert i (Finset.univ.filter (fun j : Fin n => j < i)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      rcases lt_or_eq_of_le hj with hlt | heq
      · exact Or.inr hlt
      · exact Or.inl heq
    · rintro (rfl | hlt)
      · exact le_rfl
      · exact le_of_lt hlt
  rw [upperEnd, leftEnd, h, Finset.sum_insert (by simp)]
  ring

theorem leftEnd_le {n : ℕ} (lam : Fin n → ℝ≥0) {i j : Fin n} (hij : i ≤ j) :
    leftEnd lam i ≤ leftEnd lam j := by
  rw [leftEnd, leftEnd]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact lt_of_lt_of_le hk hij
  · intro k _ _; exact (lam k).coe_nonneg

/-- The cells are disjoint: the right end of the `i`-th interval is at most the left end of any
later one.  Only nonnegativity of the lengths is used. -/
theorem upperEnd_le_leftEnd {n : ℕ} (lam : Fin n → ℝ≥0) {i j : Fin n} (hij : i < j) :
    upperEnd lam i ≤ leftEnd lam j := by
  rw [upperEnd, leftEnd]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact lt_of_le_of_lt hk hij
  · intro k _ _; exact (lam k).coe_nonneg

theorem upperEnd_of_max {n : ℕ} (lam : Fin n → ℝ≥0) {i : Fin n}
    (hi : ∀ j : Fin n, j ≤ i) : upperEnd lam i = ∑ j, (lam j : ℝ) := by
  rw [upperEnd]
  congr 1
  ext j
  simp [hi j]

theorem leftEnd_nonneg {n : ℕ} (lam : Fin n → ℝ≥0) (i : Fin n) : 0 ≤ leftEnd lam i :=
  Finset.sum_nonneg fun j _ => (lam j).coe_nonneg

theorem upperEnd_nonneg {n : ℕ} (lam : Fin n → ℝ≥0) (i : Fin n) : 0 ≤ upperEnd lam i :=
  Finset.sum_nonneg fun j _ => (lam j).coe_nonneg

theorem leftEnd_le_total {n : ℕ} (lam : Fin n → ℝ≥0) (i : Fin n) :
    leftEnd lam i ≤ ∑ j, (lam j : ℝ) := by
  rw [leftEnd]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun k _ _ => (lam k).coe_nonneg)

theorem upperEnd_le_total {n : ℕ} (lam : Fin n → ℝ≥0) (i : Fin n) :
    upperEnd lam i ≤ ∑ j, (lam j : ℝ) := by
  rw [upperEnd]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun k _ _ => (lam k).coe_nonneg)

/-- The intervals whose left endpoint is at most `x`. -/
noncomputable def idxSet {n : ℕ} (lam : Fin n → ℝ≥0) (x : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => leftEnd lam i ≤ x)

/-- The index of the interval, in the arrangement with lengths `lam`, that contains `x`. -/
noncomputable def idx {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (x : ℝ) (hx : 0 ≤ x) : Fin n :=
  (idxSet lam x).max'
    (by
      refine ⟨0, ?_⟩
      simp only [idxSet, Finset.mem_filter, Finset.mem_univ, true_and, leftEnd_zero]
      exact hx)

theorem idx_mem {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (x : ℝ) (hx : 0 ≤ x) :
    leftEnd lam (idx lam x hx) ≤ x := by
  have h : idx lam x hx ∈ idxSet lam x := by
    unfold idx
    exact Finset.max'_mem _ _
  exact (Finset.mem_filter.mp h).2

theorem le_idx {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (x : ℝ) (hx : 0 ≤ x) {i : Fin n}
    (hi : leftEnd lam i ≤ x) : i ≤ idx lam x hx := by
  unfold idx
  exact Finset.le_max' (idxSet lam x) i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

/-- **Cover.**  The selected interval contains `x`. -/
theorem lt_upperEnd_idx {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) {x : ℝ}
    (hx : x ∈ Set.Ico 0 (∑ i, (lam i : ℝ))) : x < upperEnd lam (idx lam x hx.1) := by
  by_contra hcon
  rw [not_lt] at hcon
  set k := idx lam x hx.1 with hk
  by_cases hlt : k.val + 1 < n
  · set k' : Fin n := ⟨k.val + 1, hlt⟩ with hk'
    have hkk' : k < k' := by simp [Fin.lt_def, hk']
    have hE : leftEnd lam k' = upperEnd lam k := by
      rw [leftEnd, upperEnd]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Fin.lt_def, Fin.le_def, hk']
      dsimp only [Fin.val_mk]
      omega
    have : k' ≤ k := le_idx lam x hx.1 (by rw [hE]; exact hcon)
    omega
  · have hd : k.val + 1 = n := by have := k.isLt; omega
    have hmax : ∀ j : Fin n, j ≤ k := by
      intro j
      simp only [Fin.le_def]
      omega
    have hone : upperEnd lam k = ∑ i, (lam i : ℝ) := upperEnd_of_max lam hmax
    rw [hone] at hcon
    linarith [hx.2]

/-- **Uniqueness.**  The index is determined by the interval that contains `x`. -/
theorem idx_eq {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) {x : ℝ}
    (hx : x ∈ Set.Ico 0 (∑ i, (lam i : ℝ))) {i : Fin n}
    (h1 : leftEnd lam i ≤ x) (h2 : x < upperEnd lam i) : idx lam x hx.1 = i := by
  set k := idx lam x hx.1 with hk
  have hk1 : leftEnd lam k ≤ x := idx_mem lam x hx.1
  have hk2 : x < upperEnd lam k := lt_upperEnd_idx lam hx
  rcases lt_trichotomy k i with h | h | h
  · exact absurd hk2 (not_lt.mpr (le_trans (upperEnd_le_leftEnd lam h) h1))
  · exact h
  · exact absurd h2 (not_lt.mpr (le_trans (upperEnd_le_leftEnd lam h) hk1))

/-! ### The images are the cells of the reordered lengths -/

theorem sum_imageLengths {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    ∑ k, (imageLengths π lam k : ℝ) = ∑ j, (lam j : ℝ) := by
  have h : (∑ k, (fun j => (lam j : ℝ)) (π.symm k)) = ∑ j, (lam j : ℝ) :=
    Equiv.sum_comp π.symm (fun j => (lam j : ℝ))
  simpa only [imageLengths] using h

theorem imageLengths_self {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) :
    imageLengths π.symm (imageLengths π lam) = lam := by
  funext j
  simp only [imageLengths, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem imageLeft_eq_leftEnd {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0)
    (i : Fin n) : imageLeft π lam i = leftEnd (imageLengths π lam) (π i) := by
  simp only [imageLeft, leftEnd, imageLengths]
  have hmem : (Finset.univ.filter (fun k : Fin n => k < π i)).image π.symm
      = Finset.univ.filter (fun j : Fin n => π j < π i) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa using hk
    · intro hj
      exact ⟨π j, hj, π.symm_apply_apply j⟩
  have h := Finset.sum_image (f := fun j : Fin n => (lam j : ℝ))
    (s := Finset.univ.filter (fun k : Fin n => k < π i))
    (g := (π.symm : Fin n → Fin n)) (fun x _ y _ hxy => π.symm.injective hxy)
  rw [← h, hmem]

theorem imageLeft_nonneg {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0)
    (i : Fin n) : 0 ≤ imageLeft π lam i := by
  rw [imageLeft]
  exact Finset.sum_nonneg fun j _ => (lam j).coe_nonneg

theorem imageLeft_add_le_total {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0)
    (i : Fin n) : imageLeft π lam i + (lam i : ℝ) ≤ ∑ j, (lam j : ℝ) := by
  have hins : Finset.univ.filter (fun j : Fin n => π j ≤ π i)
      = insert i (Finset.univ.filter (fun j : Fin n => π j < π i)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      rcases lt_or_eq_of_le hj with hlt | heq
      · exact Or.inr hlt
      · exact Or.inl (π.injective heq)
    · rintro (rfl | hlt)
      · exact le_rfl
      · exact le_of_lt hlt
  have hgoal : imageLeft π lam i + (lam i : ℝ)
      = (Finset.univ.filter (fun j : Fin n => π j ≤ π i)).sum (fun j => (lam j : ℝ)) := by
    rw [imageLeft, hins, Finset.sum_insert (by simp)]
    ring
  rw [hgoal]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun k _ _ => (lam k).coe_nonneg)

/-! ### The function, its inverse, and the bijectivity -/

/-- The function underlying the exchange with lengths `lam` and permutation `π`. -/
private noncomputable def mkIETFunCore {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin
  n)) :
    ℝ → ℝ :=
  fun x => if hx : x ∈ Set.Ico 0 (∑ i, (lam i : ℝ)) then
    x + translationVector π lam (idx lam x hx.1) else x

private theorem mkIETFunCore_of_mem {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    {x : ℝ} (hx : x ∈ Set.Ico 0 (∑ i, (lam i : ℝ))) :
    mkIETFunCore lam π x = x + translationVector π lam (idx lam x hx.1) := by
  unfold mkIETFunCore
  exact dif_pos hx

private theorem mkIETFunCore_of_notMem {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin
  n))
    {x : ℝ} (hx : x ∉ Set.Ico 0 (∑ i, (lam i : ℝ))) : mkIETFunCore lam π x = x := by
  unfold mkIETFunCore
  exact dif_neg hx

/-- The image of the `i`-th interval lies in the image interval of `i`. -/
theorem image_point_mem {n : ℕ} (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    {x : ℝ} (_hx : x ∈ Set.Ico 0 (∑ i, (lam i : ℝ))) {i : Fin n}
    (h1 : leftEnd lam i ≤ x) (h2 : x < upperEnd lam i) :
    x + translationVector π lam i ∈ Set.Ico 0 (∑ i, (lam i : ℝ)) ∧
      imageLeft π lam i ≤ x + translationVector π lam i ∧
        x + translationVector π lam i < imageLeft π lam i + (lam i : ℝ) := by
  have htv : translationVector π lam i = imageLeft π lam i - leftEnd lam i := rfl
  have h2' : x < leftEnd lam i + (lam i : ℝ) := by rw [upperEnd_eq] at h2; exact h2
  have h1' : 0 ≤ x + translationVector π lam i := by
    have := imageLeft_nonneg π lam i; rw [htv]; linarith
  have h2'' : x + translationVector π lam i < ∑ j, (lam j : ℝ) := by
    have := imageLeft_add_le_total π lam i; rw [htv]; linarith
  exact ⟨⟨h1', h2''⟩, by rw [htv]; linarith, by rw [htv]; linarith⟩

/-- **The inverse relation**: the exchange with the inverse permutation and the reordered lengths
is a left inverse. -/
private theorem mkIETFunCore_inv_left {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin
  n)) :
    ∀ x, mkIETFunCore (imageLengths π lam) π.symm (mkIETFunCore lam π x) = x := by
  intro x
  by_cases hx : x ∈ Set.Ico 0 (∑ i, (lam i : ℝ))
  · have htot : (∑ k, (imageLengths π lam k : ℝ)) = ∑ i, (lam i : ℝ) := sum_imageLengths π lam
    set i := idx lam x hx.1 with hi
    have h1 : leftEnd lam i ≤ x := idx_mem lam x hx.1
    have h2 : x < upperEnd lam i := lt_upperEnd_idx lam hx
    obtain ⟨hIm, hlow, hhigh⟩ := image_point_mem lam π hx h1 h2
    rw [← htot] at hIm
    -- the index, in the reordered arrangement, of the image point is `π i`
    have hidx : idx (imageLengths π lam) (x + translationVector π lam i) hIm.1 = π i := by
      refine idx_eq (imageLengths π lam) hIm ?_ ?_
      · rwa [← imageLeft_eq_leftEnd π lam i]
      · rw [upperEnd_eq, ← imageLeft_eq_leftEnd π lam i]
        have hli : (imageLengths π lam (π i) : ℝ) = (lam i : ℝ) := by
          simp [imageLengths]
        rw [hli]
        exact hhigh
    -- the two translation vectors cancel
    have htv : translationVector π.symm (imageLengths π lam) (π i)
        = -translationVector π lam i := by
      have hA : imageLeft π.symm (imageLengths π lam) (π i) = leftEnd lam i := by
        rw [imageLeft_eq_leftEnd π.symm (imageLengths π lam) (π i), imageLengths_self π lam,
          Equiv.symm_apply_apply]
      have hB : leftEnd (imageLengths π lam) (π i) = imageLeft π lam i :=
        (imageLeft_eq_leftEnd π lam i).symm
      rw [translationVector, translationVector, hA, hB]
      ring
    rw [mkIETFunCore_of_mem lam π hx, mkIETFunCore_of_mem (imageLengths π lam) π.symm hIm, hidx,
      htv]
    ring
  · have hx' : x ∉ Set.Ico 0 (∑ k, (imageLengths π lam k : ℝ)) := by
      rwa [sum_imageLengths π lam]
    rw [mkIETFunCore_of_notMem lam π hx, mkIETFunCore_of_notMem (imageLengths π lam) π.symm hx']

/-- **The other inverse relation.** -/
private theorem mkIETFunCore_inv_right {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin
  n)) :
    ∀ x, mkIETFunCore lam π (mkIETFunCore (imageLengths π lam) π.symm x) = x := by
  intro x
  simpa only [imageLengths_self π lam, Equiv.symm_symm]
    using mkIETFunCore_inv_left (imageLengths π lam) π.symm x

/-- **The function of the interval exchange** with lengths `lam` and permutation `π`, placed on
`[a, a + ∑ lam)`. -/
noncomputable def mkIETFun {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a x : ℝ) : ℝ :=
  if hx : x ∈ Set.Ico a (a + ∑ i, (lam i : ℝ)) then
    x + translationVector π lam (idx lam (x - a) (by linarith [hx.1]))
  else x

theorem mkIETFun_of_mem {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a : ℝ) {x : ℝ} (hx : x ∈ Set.Ico a (a + ∑ i, (lam i : ℝ))) :
    mkIETFun lam π a x
      = x + translationVector π lam (idx lam (x - a) (by linarith [hx.1])) := by
  unfold mkIETFun
  exact dif_pos hx

theorem mkIETFun_of_notMem {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a : ℝ) {x : ℝ} (hx : x ∉ Set.Ico a (a + ∑ i, (lam i : ℝ))) :
    mkIETFun lam π a x = x := by
  unfold mkIETFun
  exact dif_neg hx

/-- The shifted formula is the shift of the formula at `0`. -/
private theorem mkIETFun_eq_shift {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin n)) (a y : ℝ) :
    mkIETFun lam π a y = a + mkIETFunCore lam π (y - a) := by
  unfold mkIETFun mkIETFunCore
  by_cases hy : y ∈ Set.Ico a (a + ∑ i, (lam i : ℝ))
  · have hy' : y - a ∈ Set.Ico 0 (∑ i, (lam i : ℝ)) :=
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
    rw [dif_pos hy, dif_pos hy']
    ring
  · have hy' : y - a ∉ Set.Ico 0 (∑ i, (lam i : ℝ)) := by
      intro h
      exact hy ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [dif_neg hy, dif_neg hy']
    ring

theorem mkIETFun_inv_left {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a x : ℝ) : mkIETFun (imageLengths π lam) π.symm a (mkIETFun lam π a x) = x := by
  rw [mkIETFun_eq_shift, mkIETFun_eq_shift,
    show a + mkIETFunCore lam π (x - a) - a = mkIETFunCore lam π (x - a) from by ring,
    mkIETFunCore_inv_left]
  ring

/-- **The interval exchange with lengths `lam` and permutation `π`, placed on `[a, a + ∑ lam)`.** -/
noncomputable def mkIETEquiv {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a : ℝ) : Equiv ℝ ℝ where
  toFun := mkIETFun lam π a
  invFun := mkIETFun (imageLengths π lam) π.symm a
  left_inv := mkIETFun_inv_left lam π a
  right_inv := fun x => by
    -- the right inverse is the left inverse of the inverse permutation
    rw [mkIETFun_eq_shift, mkIETFun_eq_shift,
      show a + mkIETFunCore (imageLengths π lam) π.symm (x - a) - a
        = mkIETFunCore (imageLengths π lam) π.symm (x - a) from by ring,
      mkIETFunCore_inv_right]
    ring

/-- **The coercion of `mkIETEquiv`**: as a map, the exchange with lengths `lam` and permutation `π`
shifted by `a` is `mkIETFun lam π a`.  This is an equality of *functions* (a coercion lemma, and a
definitional one), not the value at a point; hence `coe_mkIETEquiv` and not `mkIETEquiv_apply`. -/
theorem coe_mkIETEquiv {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a : ℝ) : ⇑(mkIETEquiv lam π a) = mkIETFun lam π a := rfl

/-! ## The group of exchanges on `[a, b)` -/

namespace Equiv

/-- An equiv is an exchange on `[a, b)` if its underlying function is. -/
abbrev IsIET (a b : ℝ) (e : Equiv ℝ ℝ) : Prop := _root_.IsIET a b (⇑e)

end Equiv

/-- **The cuts of `mkIETFun lam π a` on `[a, a + t)`**: the cell starts `a + leftEnd lam i`,
together with `a + ∑ lam` when `[a, a + t)` is longer than the total length.  This is the cut set
that `isIET_mkIETFun` uses, now with a name, and `isCutSet_mkIETCuts` says it is one. -/
noncomputable def mkIETCuts {n : ℕ} (lam : Fin n → ℝ≥0) (a t : ℝ) : Finset ℝ :=
  (Finset.univ.image (fun i => a + leftEnd lam i) ∪
      (if (∑ i, (lam i : ℝ)) < t then {a + ∑ i, (lam i : ℝ)} else ∅)).filter
    (fun c => c ∈ Set.Ico a (a + t))

theorem isCutSet_mkIETCuts {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a : ℝ) {t : ℝ} (ht : (∑ i, (lam i : ℝ)) ≤ t) (htpos : 0 < t) :
    IsCutSet (mkIETFun lam π a) a (a + t) (mkIETCuts lam a t) := by
  classical
  set T := ∑ i, (lam i : ℝ) with hT
  set cuts := Finset.univ.image (fun i => a + leftEnd lam i) ∪ (if T < t then {a + T} else ∅) with
    hcuts
  have hEq : mkIETCuts lam a t = cuts.filter (fun c => c ∈ Set.Ico a (a + t)) := by
    rw [mkIETCuts, hcuts, hT]
  rw [hEq]
  have h0 : (fun i => a + leftEnd lam i) 0 = a := by
    change a + leftEnd lam 0 = a
    rw [leftEnd_zero, add_zero]
  have hamem : a ∈ cuts.filter (fun c => c ∈ Set.Ico a (a + t)) := by
    refine Finset.mem_filter.mpr ⟨?_, le_rfl, by linarith⟩
    rw [hcuts]
    refine Finset.mem_union.mpr (Or.inl ?_)
    refine Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, ?_⟩
    exact h0
  refine ⟨?_, ?_, ?_, hamem, ?_, ?_⟩
  · -- identity below `a`
    intro x hx
    exact mkIETFun_of_notMem lam π a (fun hcon => absurd hcon.1 (not_le.mpr hx))
  · -- identity from `a + t` on
    intro x hx
    exact mkIETFun_of_notMem lam π a (fun hcon => absurd hcon.2 (not_lt.mpr (by linarith [ht, hx,
      hT])))
  · -- the map stays inside the interval
    intro x hx
    by_cases hxT : x ∈ Set.Ico a (a + T)
    · rw [mkIETFun_of_mem lam π a hxT]
      set i := idx lam (x - a) (by linarith [hxT.1]) with hi
      have h1 : leftEnd lam i ≤ x - a := idx_mem lam (x - a) (by linarith [hxT.1])
      have hxT' : x - a ∈ Set.Ico 0 (∑ i, (lam i : ℝ)) := by
        refine ⟨by linarith [hxT.1], ?_⟩
        rw [← hT]; linarith [hxT.2]
      have h2 : x - a < leftEnd lam i + (lam i : ℝ) := by
        have := lt_upperEnd_idx lam hxT'
        rwa [upperEnd_eq] at this
      have h3 : 0 ≤ imageLeft π lam i := imageLeft_nonneg π lam i
      have h4 : imageLeft π lam i + (lam i : ℝ) ≤ T := imageLeft_add_le_total π lam i
      have htv : translationVector π lam i = imageLeft π lam i - leftEnd lam i := rfl
      constructor
      · rw [htv]; linarith
      · rw [htv]; linarith
    · rw [mkIETFun_of_notMem lam π a hxT]; exact hx
  · -- the cuts lie in the interval
    intro c hc
    exact (Finset.mem_filter.mp hc).2
  · -- the displacement is constant on the pieces
    intro x y hx hy hns
    have hns' : ¬ Separated cuts x y := by
      rintro ⟨c, hc, hci⟩
      exact hns ⟨c, Finset.mem_filter.mpr ⟨hc,
        ⟨by linarith [le_min hx.1 hy.1, hci.1], by linarith [max_lt hx.2 hy.2, hci.2]⟩⟩, hci⟩
    by_cases hxT : x ∈ Set.Ico a (a + T)
    · by_cases hyT : y ∈ Set.Ico a (a + T)
      · -- both points are in `[a, a + T)`: they must lie in one cell
        rw [mkIETFun_of_mem lam π a hyT, mkIETFun_of_mem lam π a hxT]
        set i := idx lam (x - a) (by linarith [hxT.1]) with hi
        set j := idx lam (y - a) (by linarith [hyT.1]) with hj
        have hxi' : x - a ∈ Set.Ico 0 (∑ i, (lam i : ℝ)) := by
          refine ⟨by linarith [hxT.1], ?_⟩
          rw [← hT]; linarith [hxT.2]
        have hxi : leftEnd lam i ≤ x - a ∧ x - a < leftEnd lam i + (lam i : ℝ) := by
          refine ⟨idx_mem lam _ (by linarith [hxT.1]), ?_⟩
          have := lt_upperEnd_idx lam hxi'
          rwa [upperEnd_eq] at this
        have hyj' : y - a ∈ Set.Ico 0 (∑ i, (lam i : ℝ)) := by
          refine ⟨by linarith [hyT.1], ?_⟩
          rw [← hT]; linarith [hyT.2]
        have hyj : leftEnd lam j ≤ y - a ∧ y - a < leftEnd lam j + (lam j : ℝ) := by
          refine ⟨idx_mem lam _ (by linarith [hyT.1]), ?_⟩
          have := lt_upperEnd_idx lam hyj'
          rwa [upperEnd_eq] at this
        have hij : i = j := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · -- the `j`-th cell starts strictly to the right of `x`
            have hsep : a + leftEnd lam j ∈ cuts := by
              rw [hcuts]
              exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
            have hxj : x - a < leftEnd lam j := by
              have h1 := upperEnd_le_leftEnd lam hlt
              linarith [hxi.2, upperEnd_eq lam i]
            exact hns' ⟨a + leftEnd lam j, hsep, by
              constructor
              · linarith [hxj, min_le_left x y, min_le_right x y]
              · linarith [hyj.1, le_max_left x y, le_max_right x y]⟩
          · have hsep : a + leftEnd lam i ∈ cuts := by
              rw [hcuts]
              exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
            have hyi : y - a < leftEnd lam i := by
              have h1 := upperEnd_le_leftEnd lam hlt
              linarith [hyj.2, upperEnd_eq lam j]
            exact hns' ⟨a + leftEnd lam i, hsep, by
              constructor
              · linarith [hyi, min_le_left x y, min_le_right x y]
              · linarith [hxi.1, le_max_left x y, le_max_right x y]⟩
        rw [hij]
        ring
      · -- `y` is outside: the cut `a + T` separates them
        have hyT' : a + T ≤ y := by
          rcases not_and_or.mp hyT with h | h
          · exact absurd hy.1 h
          · linarith
        have hTt : T < t := by
          rcases lt_or_ge T t with h | h
          · exact h
          · exfalso; linarith [hy.2]
        have hsep : a + T ∈ cuts := by
          rw [hcuts]
          exact Finset.mem_union_right _ (by rw [if_pos hTt]; exact Finset.mem_singleton_self _)
        exact absurd ⟨a + T, hsep, by
          constructor
          · linarith [hxT.2, min_le_left x y, min_le_right x y]
          · linarith [hyT', le_max_left x y, le_max_right x y]⟩ hns'
    · -- `x` is outside
      by_cases hyT : y ∈ Set.Ico a (a + T)
      · have hxT' : a + T ≤ x := by
          rcases not_and_or.mp hxT with h | h
          · exact absurd hx.1 h
          · linarith
        have hTt : T < t := by
          rcases lt_or_ge T t with h | h
          · exact h
          · exfalso; linarith [hx.2]
        have hsep : a + T ∈ cuts := by
          rw [hcuts]
          exact Finset.mem_union_right _ (by rw [if_pos hTt]; exact Finset.mem_singleton_self _)
        exact absurd ⟨a + T, hsep, by
          constructor
          · linarith [hyT.2, min_le_left x y, min_le_right x y]
          · linarith [hxT', le_max_left x y, le_max_right x y]⟩ hns'
      · -- both are outside: both are the identity
        rw [mkIETFun_of_notMem lam π a hyT, mkIETFun_of_notMem lam π a hxT]
        ring

/-- **`mkIETFun` is an exchange on `[a, a + t)`** as soon as the total length is at most `t`: its
cut set is `mkIETCuts lam a t` (`isCutSet_mkIETCuts`), or it is the identity when all lengths
vanish. -/
theorem isIET_mkIETFun {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a : ℝ) {t : ℝ} (ht : (∑ i, (lam i : ℝ)) ≤ t) : IsIET a (a + t) (mkIETFun lam π a) := by
  classical
  rcases le_or_gt (∑ i, (lam i : ℝ)) 0 with hT0 | hTpos
  · -- all the lengths vanish: the map is the identity
    left
    intro x
    refine mkIETFun_of_notMem lam π a (fun hcon => absurd hcon.2 ?_)
    linarith [hcon.1]
  · exact Or.inr ⟨mkIETCuts lam a t, isCutSet_mkIETCuts lam π a ht (lt_of_lt_of_le hTpos ht)⟩

theorem isIET_mkIETEquiv {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a : ℝ) {t : ℝ} (ht : (∑ i, (lam i : ℝ)) ≤ t) : IsIET a (a + t) (mkIETEquiv lam π a) := by
  exact isIET_mkIETFun lam π a ht

/-! ## The exchange attached to a cut set

Every cut set, not only the minimal one, gives a length vector and a permutation: the lengths of its
cells and the permutation of the cells induced by the images.  The original map is `mkIETFun` of
that data.  This is the API the classification `exists_mkIETEquiv_eq` is an instance of, and it is
what lets the other results of this file be stated in terms of `mkIETFun` and `mkIETEquiv`
(`IsCutSet.eq_mkIETFun`, `IsCutSet.eq_mkIETEquiv`) whenever an explicit cut set is at hand. -/

/-- **The length vector of a cut set**: the lengths of its cells. -/
noncomputable def IsCutSet.lengths (hs : IsCutSet f a b s) :
    Fin s.card → ℝ≥0 :=
  fun i => ⟨hs.cellLen i, by
    have h1 := hs.cellPos_of_lt i.isLt
    have h2 := hs.cellStarts_lt_cellPos i
    unfold IsCutSet.cellLen
    rw [h1]; linarith⟩

/-- **The permutation of a cut set**: the `i`-th cell goes to the position of its image. -/
noncomputable def IsCutSet.perm (hs : IsCutSet f a b s)
    (hinj : Function.Injective f) : Equiv.Perm (Fin s.card) :=
  hs.cellPerm hinj

/-- The lengths of the cells of a cut set add up to `b - a`. -/
theorem IsCutSet.sum_lengths (hs : IsCutSet f a b s) :
    (∑ i, (hs.lengths i : ℝ)) = b - a := by
  simp only [IsCutSet.lengths]
  exact hs.sum_cellLen

/-- The left end of the `i`-th cell, in the length vector of the cut set. -/
theorem IsCutSet.leftEnd_lengths (hs : IsCutSet f a b s)
    (i : Fin s.card) : leftEnd hs.lengths i = hs.cellStarts i - a :=
  hs.sum_cellLen_lt i

/-- The left end of the image of the `i`-th cell, in the data of the cut set. -/
theorem IsCutSet.imageLeft_lengths {a b : ℝ} {e : Equiv ℝ ℝ} {s : Finset ℝ}
    (hs : IsCutSet (⇑e) a b s) (i : Fin s.card) :
    imageLeft (hs.perm e.injective) hs.lengths i = ⇑e (hs.cellStarts i) - a :=
  hs.sum_cellLen_image i

/-- The translation vector on the `i`-th cell, in the data of the cut set. -/
theorem IsCutSet.translationVector_lengths {a b : ℝ} {e : Equiv ℝ ℝ} {s : Finset ℝ}
    (hs : IsCutSet (⇑e) a b s) (i : Fin s.card) :
    translationVector (hs.perm e.injective) hs.lengths i
      = ⇑e (hs.cellStarts i) - hs.cellStarts i := by
  rw [translationVector, hs.imageLeft_lengths i, hs.leftEnd_lengths i]
  ring

/-- **An exchange is `mkIETFun` of its cut-set data**: on the cells of the cut set it shifts by the
translation vector of the corresponding cell, and outside `[a, b)` both are the identity. -/
theorem IsCutSet.eq_mkIETFun {a b : ℝ} {e : Equiv ℝ ℝ} {s : Finset ℝ} [NeZero s.card]
    (hs : IsCutSet (⇑e) a b s) :
    ∀ x : ℝ, ⇑e x = mkIETFun hs.lengths (hs.perm e.injective) a x := by
  classical
  intro x
  have hsum := hs.sum_lengths
  by_cases hx : x ∈ Set.Ico a b
  · -- `x` lies in the `i`-th cell
    obtain ⟨i, hi⟩ := hs.exists_mem_cell hx
    have hleft : leftEnd hs.lengths i = hs.cellStarts i - a := hs.leftEnd_lengths i
    have hi_mem : leftEnd hs.lengths i ≤ x - a := by rw [hleft]; linarith [hi.1]
    have hβ : (hs.lengths i : ℝ) = hs.cellPos (i.val + 1) - hs.cellStarts i := by
      have hc : (hs.lengths i : ℝ) = hs.cellLen i := rfl
      rw [hc, IsCutSet.cellLen, hs.cellPos_of_lt i.isLt]
    have hi_lt : x - a < leftEnd hs.lengths i + (hs.lengths i : ℝ) := by
      rw [hleft, hβ]; linarith [hi.2]
    have hidx : idx hs.lengths (x - a) (by linarith [hx.1]) = i := by
      refine idx_eq hs.lengths ⟨by linarith [hx.1], ?_⟩ hi_mem ?_
      · rw [hsum]; linarith [hx.2]
      · rw [upperEnd_eq]; linarith
    have hxmem : x ∈ Set.Ico a (a + ∑ i, (hs.lengths i : ℝ)) :=
      ⟨hx.1, by linarith [hsum, hx.2]⟩
    rw [mkIETFun_of_mem _ _ a hxmem, hidx, IsCutSet.translationVector_lengths]
    linarith [hs.map_of_mem_cell hi]
  · -- outside `[a, b)` both are the identity
    have hx' : x ∉ Set.Ico a (a + ∑ i, (hs.lengths i : ℝ)) := by
      intro hcon
      exact hx ⟨hcon.1, by linarith [hsum, hcon.2]⟩
    have he : ⇑e x = x := by
      rcases not_and_or.mp hx with h1 | h2
      · exact hs.apply_eq_self_of_lt x (not_le.mp h1)
      · exact hs.apply_eq_self_of_le x (not_lt.mp h2)
    rw [mkIETFun_of_notMem _ _ a hx', he]

/-- **An exchange is `mkIETEquiv` of its cut-set data.** -/
theorem IsCutSet.eq_mkIETEquiv {a b : ℝ} {e : Equiv ℝ ℝ} {s : Finset ℝ} [NeZero s.card]
    (hs : IsCutSet (⇑e) a b s) :
    ⇑e = ⇑(mkIETEquiv hs.lengths (hs.perm e.injective) a) := by
  funext x
  rw [coe_mkIETEquiv]
  exact hs.eq_mkIETFun x

/-- **Classification**: every exchange on `[a, b)` is `mkIETEquiv` of some length vector and some
permutation, placed at `a`. -/
theorem exists_mkIETEquiv_eq {a b : ℝ} {e : Equiv ℝ ℝ} (hab : a ≤ b) (h : IsIET a b e) :
    ∃ (n : ℕ) (_ : NeZero n) (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n)),
      (∑ i, (lam i : ℝ)) = b - a ∧ e = mkIETEquiv lam π a := by
  classical
  rcases eq_or_lt_of_le hab with hEq | hlt
  · -- the interval is empty: both sides are the identity
    have hid : ∀ x, ⇑e x = x := h.eq_id_of_le (le_of_eq hEq.symm)
    refine ⟨1, inferInstance, fun _ => 0, 1, ?_, ?_⟩
    · rw [← hEq]; simp
    ext x
    rw [hid x, coe_mkIETEquiv]
    have hx : x ∉ Set.Ico a (a + ∑ i, (((fun _ => (0 : ℝ≥0)) : Fin 1 → ℝ≥0) i : ℝ)) := by simp
    exact (mkIETFun_of_notMem (lam := fun _ => (0 : ℝ≥0))
      (π := (1 : Equiv.Perm (Fin 1))) (a := a) hx).symm
  · -- the cut set of `e` gives the data
    obtain ⟨s, hs⟩ := h.exists_isCutSet hlt
    have : NeZero s.card := ⟨hs.card_pos.ne'⟩
    exact ⟨s.card, ‹NeZero s.card›, hs.lengths, hs.perm e.injective, hs.sum_lengths,
      Equiv.ext hs.eq_mkIETFun⟩

theorem isIET_iff_exists_mkIETEquiv {a b : ℝ} (hab : a ≤ b) (e : Equiv ℝ ℝ) :
    e.IsIET a b ↔ ∃ (n : ℕ) (_ : NeZero n) (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n)),
      (∑ i, (lam i : ℝ)) = b - a ∧ e = mkIETEquiv lam π a := by
  constructor
  · intro h
    exact exists_mkIETEquiv_eq hab h
  · rintro ⟨n, hn, lam, π, hsum, rfl⟩
    have h := isIET_mkIETEquiv lam π a (t := b - a) (le_of_eq hsum)
    rwa [show a + (b - a) = b from by ring] at h

namespace Equiv

/-- **The inverse of an exchange is an exchange**, from the classification: the inverse of
`mkIETEquiv lam π a` is `mkIETEquiv` of the reordered lengths and the inverse permutation. -/
theorem IsIET.symm {a b : ℝ} {e : Equiv ℝ ℝ} (h : IsIET a b e) : IsIET a b e.symm := by
  rcases le_or_gt a b with hab | hba
  · obtain ⟨n, hn, lam, π, hsum, rfl⟩ := exists_mkIETEquiv_eq hab h
    have hsum' : (∑ i, (imageLengths π lam i : ℝ)) = b - a := by
      rw [sum_imageLengths]; exact hsum
    have h1 := isIET_mkIETEquiv (imageLengths π lam) π.symm a (t := b - a) (le_of_eq hsum')
    rw [show a + (b - a) = b from by ring] at h1
    change IsIET a b (mkIETEquiv (imageLengths π lam) π.symm a)
    exact h1
  · -- the interval is empty, so `e` is the identity and so is its inverse
    have hid : ∀ x, e x = x := h.eq_id_of_le (le_of_lt hba)
    have hthis : e.symm = 1 := by
      ext x
      change e.symm x = x
      calc e.symm x = e.symm (e x) := by rw [hid x]
        _ = x := Equiv.symm_apply_apply e x
    rw [hthis]
    exact IsIET.id a b

end Equiv

/-- The interval exchange transformations of `[a, b)`: the permutations of `ℝ` that fix everything
outside and are piecewise translations inside. -/
structure IET (a b : ℝ) extends Equiv ℝ ℝ where
  /-- The piecewise-translation datum. -/
  isIET : Equiv.IsIET a b toEquiv

namespace IET

variable {a b : ℝ}

instance : CoeFun (IET a b) (fun _ => ℝ → ℝ) := ⟨fun f => f.toEquiv⟩

@[ext] theorem ext {f g : IET a b} (h : ∀ x : ℝ, f x = g x) : f = g := by
  have h' : f.toEquiv = g.toEquiv := Equiv.ext h
  obtain ⟨e, he⟩ := f
  obtain ⟨e', he'⟩ := g
  simp only at h'
  cases h'
  rfl

theorem injective (f : IET a b) : Function.Injective f := by
  intro x y h
  have h' := congrArg (fun t => f.toEquiv.symm t) h
  simpa using h'

/-- The identity exchange. -/
def id (a b : ℝ) : IET a b where
  toEquiv := Equiv.refl ℝ
  isIET := IsIET.id a b

instance : One (IET a b) := ⟨id a b⟩
instance : Mul (IET a b) :=
  ⟨fun g f => ⟨f.toEquiv.trans g.toEquiv, by
    have h := IsIET.comp (f := ⇑f.toEquiv) (g := ⇑g.toEquiv) f.isIET g.isIET
    convert h using 2
    funext x
    rfl⟩⟩
instance : Inv (IET a b) := ⟨fun f => ⟨f.toEquiv.symm, Equiv.IsIET.symm f.isIET⟩⟩
instance : Div (IET a b) := ⟨fun g f => g * f⁻¹⟩

instance : Group (IET a b) where
  mul_assoc := by intro x y z; ext t; rfl
  one_mul := by intro x; ext t; rfl
  mul_one := by intro x; ext t; rfl
  inv_mul_cancel := by intro x; ext t; exact Equiv.symm_apply_apply x.toEquiv t

@[simp] theorem symm_apply_apply (f : IET a b) (x : ℝ) : f⁻¹ (f x) = x :=
  Equiv.symm_apply_apply f.toEquiv x

@[simp] theorem apply_symm_apply' (f : IET a b) (x : ℝ) : f (f⁻¹ x) = x :=
  Equiv.apply_symm_apply f.toEquiv x

@[simp] theorem mul_apply (g h : IET a b) (x : ℝ) : (g * h) x = g (h x) := rfl

@[simp] theorem one_apply (x : ℝ) : (1 : IET a b) x = x := rfl

/-- **Iterating an exchange**: the `n`-th power in the group `IET a b` is the `n`-th iterate of the
underlying function.  (The paper's ergodicity statements are about iterates.) -/
theorem pow_apply_iterate (f : IET a b) (n : ℕ) : ∀ x : ℝ, (f ^ n) x = f^[n] x := by
  induction n with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    rw [pow_succ, mul_apply, Function.iterate_succ_apply, ih]

end IET

/-- The exchange `mkIETEquiv` as an element of `IET 0 1`, when the total length is `1`. -/
noncomputable def mkIET1 {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (h : (∑ i, lam i) = 1) : IET 0 1 where
  toEquiv := mkIETEquiv lam π 0
  isIET := by
    have h1 : (∑ i, (lam i : ℝ)) = 1 := by exact_mod_cast h
    have h2 := isIET_mkIETEquiv lam π 0 (t := 1) (le_of_eq h1)
    simpa using h2

/-- **The cut set of `mkIET1`**: `mkIETCuts lam 0 1` cuts the exchange on `[0, 1)` into
translations. This is the named form of what `isIET_mkIETFun` provides, and it is what makes the
cell API (`cellStarts`, `cellLen`, `lengths`, `perm`) available for the paper's exchanges. -/
theorem isCutSet_mkIET1 {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (hl : (∑ i, lam i) = 1) :
    IsCutSet (mkIET1 lam π hl) 0 1 (mkIETCuts lam 0 1) := by
  have hl' : (∑ i, (lam i : ℝ)) = 1 := by exact_mod_cast hl
  have h : ⇑(mkIET1 lam π hl).toEquiv = mkIETFun lam π 0 := rfl
  rw [h]
  simpa using isCutSet_mkIETCuts (t := 1) lam π 0 (le_of_eq hl') one_pos

/-- **An exchange is measurable.** -/
theorem IET.measurable {a b : ℝ} (f : IET a b) : Measurable f := by
  rcases f.isIET with hid | ⟨s, hs⟩
  · have : (f : ℝ → ℝ) = fun x => x := funext hid
    rw [this]
    exact measurable_id
  · exact hs.measurable
