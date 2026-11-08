/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module
public import IETFree.CutSet.Measure
public import IETFree.RauzyVeech.SimplexVolume
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Interval exchanges: the predicate, the explicit construction, and the group

`IsIET a b f` says that the bare function `f` is the identity or has a cut set.  The file then
constructs the exchange attached to a length vector
and a permutation explicitly (`mkIETFun`, `mkIETEquiv`, `mkIET1'`, with the cut set `mkIETCuts`),
exhibits the simplex of length vectors as a measure space (`simplexRegion`, `simplexMap`,
`simplexVolume`), with `Positive` for the positivity of a length vector, and
proves the classification `exists_mkIETEquiv_eq`: every exchange is
`mkIETFun` of the lengths and the permutation of any of its cut sets.  It closes with the type
`IET a b` of exchanges as permutations of `ℝ` fixing the complement of `[a, b)`, and its group
structure.

## Sources

The notions are Definitions 2.1 and 2.2 of Sébastien Gouëzel, *Almost every pair of interval
exchange transformations does not generate a free group* (arXiv:2610.29993), whose Theorem 1.1
is the target of the library; the two results that paper quotes from the literature are proved
here, in `IETFree/RauzyVeech/` (after J.-C. Yoccoz, *Continued fraction algorithms for interval
exchange maps: an introduction*) and `IETFree/Rigidity/` (after W. A. Veech, *Interval exchange
transformations and measured foliations*, 1984).  `IETFree/RauzyVeech/RichPath/` follows
Appendix A of A. Avila, S. Gouëzel and J.-C. Yoccoz, *Exponential mixing for the Teichmüller
flow* — "AGY" in the docstrings.
-/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

namespace IntervalExchange

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
theorem eq_id_of_le (h : IsIET a b f) (hba : b ≤ a) (x : ℝ) : f x = x := by
  rcases h with hid | ⟨s, hs⟩
  · exact hid x
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

-- the data of one cut set, in scope below (`hs` stays a binder of each declaration)

/-! ## Lebesgue measure on the simplex -/

/-- The free region: the `d - 1` free coordinates are positive and have total mass less than `1`,
so that every coordinate of the image, including the last one `1 - ∑`, is positive.

This is `RauzyVeech.region` at `d - 1`: the chart's own indexing (a simplex in `n + 1` dimensions
has `n` free coordinates) is in `RauzyVeech/SimplexVolume.lean`, which needs only Mathlib, and the
`d`-indexed form the length vectors use is this instance of it. -/
def simplexRegion (d : ℕ) : Set (Fin (d - 1) → ℝ) :=
  RauzyVeech.region (d - 1)

/-- The `d - 1` free coordinates sit below `d - 1` in the `d`-th slot of the last coordinate.
`omega` would be shorter, but it generates an auxiliary declaration, and auxiliaries are private to
their module: this statement is copied verbatim into `Challenge.lean`, and the comparator compares
the two proof terms, so the copies would no longer be the same declaration. -/
theorem simplexMap_val_lt (d : ℕ) (i : Fin d) (h : ¬ i.val + 1 = d) : i.val < d - 1 :=
  Nat.lt_pred_iff.2 (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.isLt) h)

/-- The parametrisation of the simplex: the `d - 1` free coordinates, the last being `1 - ∑`. -/
noncomputable def simplexMap (d : ℕ) (v : Fin (d - 1) → ℝ) : Fin d → ℝ≥0 :=
  fun i =>
    if h : i.val + 1 = d then (1 - ∑ j, v j).toNNReal
    else (v ⟨i.val, simplexMap_val_lt d i h⟩).toNNReal

/-- **Lebesgue measure on the simplex**: Lebesgue measure on the `d - 1` free coordinates,
restricted to the region where their total mass is less than `1`, transported by the
parametrisation `λ_d = 1 - ∑_{i<d} λ_i`.  Almost every point of the image is in the simplex. -/
noncomputable def simplexVolume (d : ℕ) : Measure (Fin d → ℝ≥0) :=
  Measure.map (simplexMap d) (volume.restrict (simplexRegion d))

/-- The definition of `simplexVolume`, as an equation: use it rather than `unfold` (`simp` does not
know the equation, since `simplexVolume` is not a `simp` lemma). -/
theorem simplexVolume_def (d : ℕ) :
    simplexVolume d = Measure.map (simplexMap d) (volume.restrict (simplexRegion d)) := (rfl)

/-- **A length vector is positive** when all its coordinates are.  This is the hypothesis under
which the endpoints of the arrangement and the block mass behave (`leftEnd_lt_total`,
`leftEnd_pos_of_ne_zero`, `blockMass_pos`).  It is stated on an arbitrary alphabet, like
`totalLength` and `simplex`: the `α`-indexed half of the tower writes the same hypothesis.

An `abbrev`, not a `def`: it is a hypothesis, destructured with `h i` and unfolded by `rw`, in
files across the block development, so its body has to be visible to clients. -/
abbrev Positive {α : Type*} (lam : α → ℝ≥0) : Prop :=
  ∀ a, 0 < lam a

/-- **The total length** `Λ = ∑ lam` of a length vector, on an arbitrary alphabet: the mass of the
interval the exchange acts on, when that interval is `[0, Λ)`. -/
def totalLength {α : Type*} [Fintype α] (lam : α → ℝ≥0) : ℝ := ∑ a, (lam a : ℝ)

/-- **The indices of a block of `n` cells**: `k < l ≤ n`.  The instance `NeZero (l - k)`, which
`blockLam` and `mkIET1'` need to form the rescaled block, is derived here once, so that no statement
about a block has to carry it.

Two layers use the indices: the *raw* API of `blockMass` / `blockLam` / `blockPerm` takes
`(k) {l} (hkl : k < l) (hln : l ≤ n)` as plain arguments — it is stated for an arbitrary
length vector, with no region in scope — and the *block-level* statements (`GoodRegion.Block`,
`mkIET1_rescale_subinterval`, `idx_rescaleMap`) take the bundle `BlockIdx n` (or a `Block`,
which extends it).  The bundle is not threaded through the raw API: the raw statements are about an
arbitrary length vector, and the block hypothesis `k < l ≤ n` is what their proofs use. -/
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

/-- Two block indices with the same `k` and `l` are equal: the bounds are propositions. -/
@[ext] theorem ext {n : ℕ} {I J : BlockIdx n} (hk : I.k = J.k) (hl : I.l = J.l) : I = J := by
  cases I; cases J
  simp only at hk hl
  subst hk hl
  rfl

end BlockIdx

/-! ## The exchange built from a length vector and a permutation -/

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

/-- `leftEnd` is monotone in the index. -/
theorem leftEnd_mono {n : ℕ} (lam : Fin n → ℝ≥0) {i j : Fin n} (h : i ≤ j) :
    leftEnd lam i ≤ leftEnd lam j := by
  rw [leftEnd, leftEnd]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_)
    (fun k _ _ => (lam k).coe_nonneg)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact lt_of_lt_of_le hk h

/-- The left end of the `(i+1)`-st interval is the right end of the `i`-th. -/
theorem leftEnd_succ_eq_upperEnd {n : ℕ} (lam : Fin n → ℝ≥0) (i : Fin n) (h : i.val + 1 < n) :
    leftEnd lam ⟨i.val + 1, h⟩ = upperEnd lam i := by
  rw [leftEnd, upperEnd]
  congr 1

/-- The cells are disjoint: the right end of the `i`-th interval is at most the left end of any
later one. -/
theorem upperEnd_le_leftEnd {n : ℕ} (lam : Fin n → ℝ≥0) {i j : Fin n} (hij : i < j) :
    upperEnd lam i ≤ leftEnd lam j := by
  have hlt : i.val + 1 < n := by
    have := j.isLt
    rw [Fin.lt_def] at hij
    omega
  have h1 : leftEnd lam ⟨i.val + 1, hlt⟩ ≤ leftEnd lam j := by
    refine leftEnd_mono lam ?_
    rw [Fin.le_def]
    dsimp only [Fin.val_mk]
    rw [Fin.lt_def] at hij
    omega
  rwa [leftEnd_succ_eq_upperEnd lam i hlt] at h1

theorem upperEnd_of_max {n : ℕ} (lam : Fin n → ℝ≥0) {i : Fin n}
    (hi : ∀ j : Fin n, j ≤ i) : upperEnd lam i = ∑ j, (lam j : ℝ) := by
  rw [upperEnd]
  congr 1
  ext j
  simp [hi j]

theorem leftEnd_nonneg {n : ℕ} (lam : Fin n → ℝ≥0) (i : Fin n) : 0 ≤ leftEnd lam i :=
  Finset.sum_nonneg fun j _ => (lam j).coe_nonneg

theorem upperEnd_le_total {n : ℕ} (lam : Fin n → ℝ≥0) (i : Fin n) :
    upperEnd lam i ≤ ∑ j, (lam j : ℝ) := by
  rw [upperEnd]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun k _ _ => (lam k).coe_nonneg)

/-- **Every cell starts before the total length**, for a positive length vector. -/
theorem leftEnd_lt_total {n : ℕ} [NeZero n] {lam : Fin n → ℝ≥0} (hpos : Positive lam)
    (i : Fin n) : leftEnd lam i < ∑ j, (lam j : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_one_add_one (NeZero.ne n)).symm⟩
  have hle : leftEnd lam i ≤ leftEnd lam (Fin.last m) := leftEnd_mono lam (Fin.le_last i)
  have hu : upperEnd lam (Fin.last m) = ∑ j, (lam j : ℝ) :=
    upperEnd_of_max lam (fun j => Fin.le_last j)
  have h2 : upperEnd lam (Fin.last m) = leftEnd lam (Fin.last m) + (lam (Fin.last m) : ℝ) :=
    upperEnd_eq lam _
  have h3 : (0 : ℝ) < (lam (Fin.last m) : ℝ) := by exact_mod_cast hpos _
  linarith

/-- **A cell ends before the total length**: the left end plus the length of the `i`-th cell is at
most `∑ j, lam j`, the cells of the bottom order being disjoint half-open intervals. -/
theorem leftEnd_add_le_total {n : ℕ} (lam : Fin n → ℝ≥0) (i : Fin n) :
    leftEnd lam i + (lam i : ℝ) ≤ ∑ j, (lam j : ℝ) := by
  rw [← upperEnd_eq]
  exact upperEnd_le_total lam i

/-- The intervals whose left endpoint is at most `x`. -/
noncomputable def idxSet {n : ℕ} (lam : Fin n → ℝ≥0) (x : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => leftEnd lam i ≤ x)

/-- The set of intervals whose left endpoint is at most `x` is never empty.

The proof generates no auxiliary declaration (`refine`/`exact`, no `simp`): this statement is copied
verbatim into `Challenge.lean`, and the two copies must elaborate to the same term. -/
theorem idxSet_nonempty {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (x : ℝ) (hx : 0 ≤ x) :
    (idxSet lam x).Nonempty := by
  refine ⟨0, Finset.mem_filter.2 ⟨Finset.mem_univ 0, ?_⟩⟩
  exact le_of_eq_of_le (Finset.sum_eq_zero fun j hj =>
    absurd (Finset.mem_filter.1 hj).2 (Fin.not_lt_zero j)) hx

/-- The index of the interval, in the arrangement with lengths `lam`, that contains `x`. -/
noncomputable def idx {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (x : ℝ) (hx : 0 ≤ x) : Fin n :=
  (idxSet lam x).max' (idxSet_nonempty lam x hx)

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
    have : k' ≤ k := le_idx lam x hx.1 (by rw [hE]; exact hcon)
    omega
  · have hd : k.val + 1 = n := by have := k.isLt; omega
    have hmax (j : Fin n) : j ≤ k := by
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

/-- The cells whose image starts at or before the image of the `i`-th cell are exactly the `i`-th
one and those before it. -/
theorem filter_perm_le_eq_insert {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) :
    Finset.univ.filter (fun j : Fin n => π j ≤ π i)
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

theorem imageLeft_add_le_total {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0)
    (i : Fin n) : imageLeft π lam i + (lam i : ℝ) ≤ ∑ j, (lam j : ℝ) := by
  have hgoal : imageLeft π lam i + (lam i : ℝ)
      = (Finset.univ.filter (fun j : Fin n => π j ≤ π i)).sum (fun j => (lam j : ℝ)) := by
    rw [imageLeft, filter_perm_le_eq_insert π i, Finset.sum_insert (by simp)]
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
  exact dite_eq_left hx

private theorem mkIETFunCore_of_notMem {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin
  n))
    {x : ℝ} (hx : x ∉ Set.Ico 0 (∑ i, (lam i : ℝ))) : mkIETFunCore lam π x = x := by
  unfold mkIETFunCore
  exact dite_eq_right hx

/-- The image of the `i`-th interval lies in the image interval of `i`. -/
theorem image_point_mem {n : ℕ} (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    {x : ℝ} {i : Fin n}
    (h1 : leftEnd lam i ≤ x) (h2 : x < upperEnd lam i) :
    x + translationVector π lam i ∈ Set.Ico 0 (∑ i, (lam i : ℝ)) ∧
      imageLeft π lam i ≤ x + translationVector π lam i ∧
        x + translationVector π lam i < imageLeft π lam i + (lam i : ℝ) := by
  have htv : translationVector π lam i = imageLeft π lam i - leftEnd lam i := (rfl)
  have h2' : x < leftEnd lam i + (lam i : ℝ) := by rw [upperEnd_eq] at h2; exact h2
  have h1' : 0 ≤ x + translationVector π lam i := by
    have := imageLeft_nonneg π lam i; rw [htv]; linarith
  have h2'' : x + translationVector π lam i < ∑ j, (lam j : ℝ) := by
    have := imageLeft_add_le_total π lam i; rw [htv]; linarith
  exact ⟨⟨h1', h2''⟩, by rw [htv]; linarith, by rw [htv]; linarith⟩

/-- **The inverse relation**: the exchange with the inverse permutation and the reordered lengths
is a left inverse. -/
private theorem mkIETFunCore_inv_left {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin
  n)) (x : ℝ) :
    mkIETFunCore (imageLengths π lam) π.symm (mkIETFunCore lam π x) = x := by
  by_cases hx : x ∈ Set.Ico 0 (∑ i, (lam i : ℝ))
  · have htot : (∑ k, (imageLengths π lam k : ℝ)) = ∑ i, (lam i : ℝ) := sum_imageLengths π lam
    set i := idx lam x hx.1 with hi
    have h1 : leftEnd lam i ≤ x := idx_mem lam x hx.1
    have h2 : x < upperEnd lam i := lt_upperEnd_idx lam hx
    obtain ⟨hIm, hlow, hhigh⟩ := image_point_mem lam π h1 h2
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
      unfold translationVector
      rw [hA, hB]
      ring
    rw [mkIETFunCore_of_mem lam π hx, mkIETFunCore_of_mem (imageLengths π lam) π.symm hIm, hidx,
      htv]
    ring
  · have hx' : x ∉ Set.Ico 0 (∑ k, (imageLengths π lam k : ℝ)) := by
      rwa [sum_imageLengths π lam]
    rw [mkIETFunCore_of_notMem lam π hx, mkIETFunCore_of_notMem (imageLengths π lam) π.symm hx']

/-- **The other inverse relation.** -/
private theorem mkIETFunCore_inv_right {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin
  n)) (x : ℝ) :
    mkIETFunCore lam π (mkIETFunCore (imageLengths π lam) π.symm x) = x := by
  simpa only [imageLengths_self π lam, Equiv.symm_symm]
    using mkIETFunCore_inv_left (imageLengths π lam) π.symm x

/-- **The interval exchange transformation**, as a bare function, with lengths `lam` and
permutation `π`, placed on `[a, a + ∑ lam)`, and outside that interval the identity. -/
noncomputable def mkIETFun {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a x : ℝ) : ℝ :=
  if hx : x ∈ Set.Ico a (a + ∑ i, (lam i : ℝ)) then
    x + translationVector π lam (idx lam (x - a) (by linarith [hx.1]))
  else x

/-- **The value of an interval exchange inside its interval.**  The formula is an implementation
detail of `mkIETFun` and is **deliberately not a `simp` lemma**: `mkIETFun` is meant to stay folded,
and the formula is unfolded by naming this lemma where the formula is what one wants. -/
theorem mkIETFun_of_mem {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a : ℝ) {x : ℝ} (hx : x ∈ Set.Ico a (a + ∑ i, (lam i : ℝ))) :
    mkIETFun lam π a x
      = x + translationVector π lam (idx lam (x - a) (by linarith [hx.1])) := by
  unfold mkIETFun
  exact dite_eq_left hx

/-- **The value of an interval exchange outside its interval** — the identity.  Like the `of_mem`
form, **deliberately not a `simp` lemma**: the `if` in `mkIETFun` is an implementation
detail. -/
theorem mkIETFun_of_notMem {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a : ℝ) {x : ℝ} (hx : x ∉ Set.Ico a (a + ∑ i, (lam i : ℝ))) :
    mkIETFun lam π a x = x := by
  unfold mkIETFun
  exact dite_eq_right hx

/-- The shifted formula is the shift of the formula at `0`. -/
private theorem mkIETFun_eq_shift {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin n)) (a y : ℝ) :
    mkIETFun lam π a y = a + mkIETFunCore lam π (y - a) := by
  unfold mkIETFun mkIETFunCore
  by_cases hy : y ∈ Set.Ico a (a + ∑ i, (lam i : ℝ))
  · have hy' : y - a ∈ Set.Ico 0 (∑ i, (lam i : ℝ)) :=
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
    rw [dite_eq_left hy, dite_eq_left hy']
    ring
  · have hy' : y - a ∉ Set.Ico 0 (∑ i, (lam i : ℝ)) := by
      intro h
      exact hy ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [dite_eq_right hy, dite_eq_right hy']
    ring

theorem mkIETFun_inv_left {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a x : ℝ) : mkIETFun (imageLengths π lam) π.symm a (mkIETFun lam π a x) = x := by
  rw [mkIETFun_eq_shift, mkIETFun_eq_shift,
    add_sub_cancel_left,
    mkIETFunCore_inv_left]
  ring

/-- **The interval exchange transformation**, as an equiv, with lengths `lam` and permutation `π`,
placed on `[a, a + ∑ lam)`: its inverse is the exchange of the inverse permutation with the lengths
reordered (`imageLengths`). -/
noncomputable def mkIETEquiv {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a : ℝ) : Equiv ℝ ℝ where
  toFun := mkIETFun lam π a
  invFun := mkIETFun (imageLengths π lam) π.symm a
  left_inv := mkIETFun_inv_left lam π a
  right_inv := fun x => by
    -- the right inverse is the left inverse of the inverse permutation
    -- (the `show` in it cancels the `+ a - a` so that the shift lemma fires)
    rw [mkIETFun_eq_shift, mkIETFun_eq_shift,
      show a + mkIETFunCore (imageLengths π lam) π.symm (x - a) - a
        = mkIETFunCore (imageLengths π lam) π.symm (x - a) from by ring,
      mkIETFunCore_inv_right]
    ring

/-- **The coercion of `mkIETEquiv`**: as a map, the exchange with lengths `lam` and permutation `π`
shifted by `a` is `mkIETFun lam π a`.  This is an equality of *functions* (a coercion lemma, and a
definitional one), not the value at a point; hence `coe_mkIETEquiv` and not `mkIETEquiv_apply`. -/
theorem coe_mkIETEquiv {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a : ℝ) : ⇑(mkIETEquiv lam π a) = mkIETFun lam π a := (rfl)

/-- **The evaluation of a word in two equivs**: the `Equiv`-valued evaluation of `w` at a pair of
permutations `(f, g)` of `ℝ` — the form the main theorem is stated with, since its exchanges are
`mkIETEquiv p π 0 : Equiv ℝ ℝ` rather than bundled exchanges.  The evaluation on bundled exchanges
is `IntervalExchange.Pair.evalWord`, and `evalWord_toEquiv` says the two agree.

The generator map is `Fin.cases f fun _ => g` rather than `if i = 0 then f else g`: the latter
carries a `DecidableEq (Fin 2)` instance whose proof is an auxiliary declaration of the module it is
written in, and this definition is copied verbatim into `Challenge.lean`, where the comparator
compares the two elaborated bodies. -/
noncomputable def evalWordEquiv (w : FreeGroup (Fin 2)) (f g : Equiv ℝ ℝ) : Equiv ℝ ℝ :=
  FreeGroup.lift (Fin.cases f fun _ => g) w

/-! ## The group of exchanges on `[a, b)` -/

end IntervalExchange

namespace Equiv
open IntervalExchange

/-- An equiv is an exchange on `[a, b)` if its underlying function is. -/
abbrev IsIET (a b : ℝ) (e : Equiv ℝ ℝ) : Prop := IntervalExchange.IsIET a b (⇑e)

end Equiv

namespace IntervalExchange

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
  set T := ∑ i, (lam i : ℝ) with hT
  set cuts := Finset.univ.image (fun i => a + leftEnd lam i) ∪ (if T < t then {a + T} else ∅) with
    hcuts
  have hEq : mkIETCuts lam a t = cuts.filter (fun c => c ∈ Set.Ico a (a + t)) := by
    rw [mkIETCuts, hcuts, hT]
  rw [hEq]
  have h0 : (fun i => a + leftEnd lam i) 0 = a := by
    simp only []
    rw [leftEnd_zero, add_zero]
  have hamem : a ∈ cuts.filter (fun c => c ∈ Set.Ico a (a + t)) := by
    refine Finset.mem_filter.mpr ⟨?_, le_rfl, by linarith⟩
    rw [hcuts]
    refine Finset.mem_union.mpr (Or.inl ?_)
    refine Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, ?_⟩
    exact h0
  -- the bounds on the cell of a point of `[a, a + T)`, once, for the three places that need them
  have cell_bounds {u : ℝ} (hu0 : 0 ≤ u - a) (huT : u - a < T) :
      u - a ∈ Set.Ico 0 (∑ i, (lam i : ℝ)) ∧
        leftEnd lam (idx lam (u - a) hu0) ≤ u - a ∧
        u - a < leftEnd lam (idx lam (u - a) hu0) + (lam (idx lam (u - a) hu0) : ℝ) := by
    have hmem : u - a ∈ Set.Ico 0 (∑ i, (lam i : ℝ)) := by
      refine ⟨hu0, ?_⟩
      rw [← hT]; exact huT
    exact ⟨hmem, idx_mem lam _ hu0, by
      have := lt_upperEnd_idx lam hmem
      rwa [upperEnd_eq] at this⟩
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
      obtain ⟨-, h1, h2⟩ := cell_bounds (u := x) (by linarith [hxT.1]) (by linarith [hxT.2])
      have h3 : 0 ≤ imageLeft π lam i := imageLeft_nonneg π lam i
      have h4 : imageLeft π lam i + (lam i : ℝ) ≤ T := imageLeft_add_le_total π lam i
      have htv : translationVector π lam i = imageLeft π lam i - leftEnd lam i := (rfl)
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
        obtain ⟨-, hxi1, hxi2⟩ := cell_bounds (u := x) (by linarith [hxT.1]) (by linarith [hxT.2])
        obtain ⟨-, hyj1, hyj2⟩ := cell_bounds (u := y) (by linarith [hyT.1]) (by linarith [hyT.2])
        have hij : i = j := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · -- the `j`-th cell starts strictly to the right of `x`
            have hsep : a + leftEnd lam j ∈ cuts := by
              rw [hcuts]
              exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
            have hxj : x - a < leftEnd lam j := by
              have h1 := upperEnd_le_leftEnd lam hlt
              linarith [hxi2, upperEnd_eq lam i]
            exact hns' ⟨a + leftEnd lam j, hsep, by
              constructor
              · linarith [hxj, min_le_left x y, min_le_right x y]
              · linarith [hyj1, le_max_left x y, le_max_right x y]⟩
          · have hsep : a + leftEnd lam i ∈ cuts := by
              rw [hcuts]
              exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
            have hyi : y - a < leftEnd lam i := by
              have h1 := upperEnd_le_leftEnd lam hlt
              linarith [hyj2, upperEnd_eq lam j]
            exact hns' ⟨a + leftEnd lam i, hsep, by
              constructor
              · linarith [hyi, min_le_left x y, min_le_right x y]
              · linarith [hxi1, le_max_left x y, le_max_right x y]⟩
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
          exact Finset.mem_union_right _
            (by rw [ite_eq_left hTt]; exact Finset.mem_singleton_self _)
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
          exact Finset.mem_union_right _
            (by rw [ite_eq_left hTt]; exact Finset.mem_singleton_self _)
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

variable {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}

/-! ## The exchange attached to a cut set

Every cut set, not only the minimal one, gives a length vector and a permutation: the lengths of its
cells and the permutation of the cells induced by the images.  The original map is `mkIETFun` of
that data.  This is the API the classification `exists_mkIETEquiv_eq` is an instance of, and it is
what lets the other results of this file be stated in terms of `mkIETFun` and `mkIETEquiv`
(`IsCutSet.eq_mkIETFun`) whenever an explicit cut set is at hand. -/

/-- **The length vector of a cut set**: the lengths of its cells. -/
noncomputable def IsCutSet.lengths (hs : IsCutSet f a b s) :
    Fin s.card → ℝ≥0 :=
  fun i => ⟨hs.cellLen i, by
    have h1 := hs.cellPos_of_lt i.isLt
    have h2 := hs.cellStarts_lt_cellPos i
    rw [IsCutSet.cellLen_def]
    rw [h1]; linarith⟩

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
    imageLeft (hs.cellPerm e.injective) hs.lengths i = ⇑e (hs.cellStarts i) - a :=
  hs.sum_cellLen_image i

/-- The translation vector on the `i`-th cell, in the data of the cut set. -/
theorem IsCutSet.translationVector_lengths {a b : ℝ} {e : Equiv ℝ ℝ} {s : Finset ℝ}
    (hs : IsCutSet (⇑e) a b s) (i : Fin s.card) :
    translationVector (hs.cellPerm e.injective) hs.lengths i
      = ⇑e (hs.cellStarts i) - hs.cellStarts i := by
  unfold translationVector
  rw [hs.imageLeft_lengths i, hs.leftEnd_lengths i]
  ring

/-- **An exchange is `mkIETFun` of its cut-set data**: on the cells of the cut set it shifts by the
translation vector of the corresponding cell, and outside `[a, b)` both are the identity. -/
theorem IsCutSet.eq_mkIETFun {a b : ℝ} {e : Equiv ℝ ℝ} {s : Finset ℝ} [NeZero s.card]
    (hs : IsCutSet (⇑e) a b s) (x : ℝ) :
    ⇑e x = mkIETFun hs.lengths (hs.cellPerm e.injective) a x := by
  have hsum := hs.sum_lengths
  by_cases hx : x ∈ Set.Ico a b
  · -- `x` lies in the `i`-th cell
    obtain ⟨i, hi⟩ := hs.exists_mem_cell hx
    have hleft : leftEnd hs.lengths i = hs.cellStarts i - a := hs.leftEnd_lengths i
    have hi_mem : leftEnd hs.lengths i ≤ x - a := by rw [hleft]; linarith [hi.1]
    have hβ : (hs.lengths i : ℝ) = hs.cellPos (i.val + 1) - hs.cellStarts i := by
      have hc : (hs.lengths i : ℝ) = hs.cellLen i := (rfl)
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

/-- **Classification**: every exchange on `[a, b)` is `mkIETEquiv` of some length vector and some
permutation, placed at `a`. -/
theorem exists_mkIETEquiv_eq {a b : ℝ} {e : Equiv ℝ ℝ} (hab : a ≤ b) (h : IsIET a b e) :
    ∃ (n : ℕ) (_ : NeZero n) (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n)),
      (∑ i, (lam i : ℝ)) = b - a ∧ e = mkIETEquiv lam π a := by
  rcases eq_or_lt_of_le hab with hEq | hlt
  · -- the interval is empty: both sides are the identity
    have hid (x) : ⇑e x = x := h.eq_id_of_le (le_of_eq hEq.symm) x
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
    exact ⟨s.card, ‹NeZero s.card›, hs.lengths, hs.cellPerm e.injective, hs.sum_lengths,
      Equiv.ext hs.eq_mkIETFun⟩

end IntervalExchange

namespace Equiv
open IntervalExchange

/-- **The inverse of an exchange is an exchange**, from the classification: the inverse of
`mkIETEquiv lam π a` is `mkIETEquiv` of the reordered lengths and the inverse permutation. -/
theorem IsIET.symm {a b : ℝ} {e : Equiv ℝ ℝ} (h : IsIET a b e) : IsIET a b e.symm := by
  rcases le_or_gt a b with hab | hba
  · obtain ⟨n, hn, lam, π, hsum, rfl⟩ := exists_mkIETEquiv_eq hab h
    have hsum' : (∑ i, (imageLengths π lam i : ℝ)) = b - a := by
      rw [sum_imageLengths]; exact hsum
    have h1 := isIET_mkIETEquiv (imageLengths π lam) π.symm a (t := b - a) (le_of_eq hsum')
    rw [add_sub_cancel] at h1
    exact h1
  · -- the interval is empty, so `e` is the identity and so is its inverse
    have hid (x) : e x = x := h.eq_id_of_le (le_of_lt hba) x
    have hthis : e.symm = 1 := by
      ext x
      calc e.symm x = e.symm (e x) := by rw [hid x]
        _ = x := Equiv.symm_apply_apply e x
    rw [hthis]
    exact IsIET.id a b

end Equiv

namespace IntervalExchange

/-- The interval exchange transformations of `[a, b)`: the permutations of `ℝ` that fix
everything outside and are piecewise translations inside. -/
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

instance : One (IET a b) where
  one := ⟨Equiv.refl ℝ, IsIET.id a b⟩
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

@[simp] theorem mul_apply (g h : IET a b) (x : ℝ) : (g * h) x = g (h x) := (rfl)

@[simp] theorem one_apply (x : ℝ) : (1 : IET a b) x = x := (rfl)

/-- The coercion of an exchange to the underlying permutation, as a monoid homomorphism. -/
def coeHom {a b : ℝ} : IET a b →* Equiv.Perm ℝ where
  toFun e := e.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem coeHom_apply {a b : ℝ} (e : IET a b) :
    coeHom e = e.toEquiv := (rfl)

/-- **Iterating an exchange**: the `n`-th power in the group `IET a b` is the `n`-th iterate of the
underlying function.  (The paper's ergodicity statements are about iterates.) -/
theorem pow_apply_iterate (f : IET a b) (n : ℕ) (x : ℝ) : (f ^ n) x = f^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, mul_apply, Function.iterate_succ_apply, ih]

end IET

/-- The exchange `mkIETEquiv` as an element of `IET 0 1`, when the total length is `1`. -/
noncomputable def mkIET1' {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (h : (∑ i, lam i) = 1) : IET 0 1 where
  toEquiv := mkIETEquiv lam π 0
  isIET := by
    have h1 : (∑ i, (lam i : ℝ)) = 1 := by exact_mod_cast h
    have h2 := isIET_mkIETEquiv lam π 0 (t := 1) (le_of_eq h1)
    simpa using h2

/-- **The function of `mkIET1'`**: the unfolding of the definition, `mkIET1' lam π hl` acting on `ℝ`
is `mkIETFun lam π 0`. -/
theorem coe_mkIET1' {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (hl : (∑ i, lam i) = 1) : ⇑(mkIET1' lam π hl) = mkIETFun lam π 0 := (rfl)

/-- The pointwise form of `coe_mkIET1'`. -/
theorem mkIET1_eq_mkIETFun {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (hl : (∑ i, lam i) = 1) (x : ℝ) : mkIET1' lam π hl x = mkIETFun lam π 0 x :=
  congrFun (coe_mkIET1' lam π hl) x

/-- **The cut set of `mkIET1'`**: `mkIETCuts lam 0 1` cuts the exchange on `[0, 1)` into
translations. This is the named form of what `isIET_mkIETFun` provides, and it is what makes the
cell API (`cellStarts`, `cellLen`, `lengths`, `perm`) available for the paper's exchanges. -/
theorem isCutSet_mkIET1 {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (hl : (∑ i, lam i) = 1) :
    IsCutSet (mkIET1' lam π hl) 0 1 (mkIETCuts lam 0 1) := by
  have hl' : (∑ i, (lam i : ℝ)) = 1 := by exact_mod_cast hl
  have h : ⇑(mkIET1' lam π hl).toEquiv = mkIETFun lam π 0 := coe_mkIET1' lam π hl
  rw [h]
  simpa using isCutSet_mkIETCuts (t := 1) lam π 0 (le_of_eq hl') one_pos

/-- **The exchange of a length vector and a permutation, total in the length vector**:
`mkIET1 lam π` is `mkIET1' lam π h` when the lengths sum to `1`, and the identity otherwise.  This
is the form the a.e. statements use — they quantify over all length vectors, and
`lam ∈ simplex (Fin n)` holds almost everywhere
(`ae_mem_simplex_of_card_ne_zero`, `ae_mem_simplex_of_nonempty`), so no
hypothesis on `lam` has to be carried in the statement. -/
noncomputable def mkIET1 {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n)) :
    IET 0 1 :=
  if h : (∑ i, lam i) = 1 then mkIET1' lam π h else 1

/-- On the simplex, the total `mkIET1` is `mkIET1'`. -/
theorem mkIET1_of_mem {n : ℕ} [NeZero n] {lam : Fin n → ℝ≥0} {π : Equiv.Perm (Fin n)}
    (h : (∑ i, lam i) = 1) : mkIET1 lam π = mkIET1' lam π h := by
  rw [mkIET1, dite_eq_left h]

/-- Off the simplex, the total `mkIET1` is the identity. -/
theorem mkIET1_of_notMem {n : ℕ} [NeZero n] {lam : Fin n → ℝ≥0} {π : Equiv.Perm (Fin n)}
    (h : ¬ (∑ i, lam i) = 1) : mkIET1 lam π = 1 := by
  rw [mkIET1, dite_eq_right h]

/-- **The function of the total `mkIET1` on the simplex** is `mkIETFun lam π 0`. -/
theorem coe_mkIET1 {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (hl : (∑ i, lam i) = 1) : ⇑(mkIET1 lam π) = mkIETFun lam π 0 := by
  rw [mkIET1_of_mem hl]
  exact coe_mkIET1' lam π hl

namespace IET

/-- **An exchange is measurable.** -/
theorem measurable {a b : ℝ} (f : IET a b) : Measurable f := by
  rcases f.isIET with hid | ⟨s, hs⟩
  · have : (f : ℝ → ℝ) = fun x => x := funext hid
    rw [this]
    exact measurable_id
  · exact hs.measurable

/-- Iterates of an exchange are measurable: the group power is the iterate
(`pow_apply_iterate`), so this is `Measurable.iterate` applied to the
measurability of one power. -/
theorem measurable_pow {a b : ℝ} (f : IET a b) (n : ℕ) : Measurable ⇑(f ^ n) := by
  have h : ⇑(f ^ n) = f^[n] := funext fun x => pow_apply_iterate f n x
  rw [h]
  exact (measurable f).iterate n

/-! ## Lebesgue measure on `[0, 1)`

`unitMeas` is the reference measure of an exchange of `[0, 1)`: Lebesgue measure restricted to the
interval, as a probability measure.  Both developments above the single-exchange layer use it — the
free-group one (`IETFree/Pair/`) and the unique-ergodicity one (`IETFree/UniqueErgodicity/`) — so
it is defined here, with the measure-preservation lemmas they share. -/

end IET

/-- Lebesgue measure on `[0, 1)`, as a probability measure on `ℝ`. -/
noncomputable def unitMeas : Measure ℝ := volume.restrict (Set.Ico 0 1)

noncomputable instance : IsProbabilityMeasure unitMeas := ⟨by simp [unitMeas]⟩

/-- **Lebesgue measure on `[0, 1)` has mass `1` there** — the one proof of this fact in the library.
Its real-valued form is `Measure.real` applied to it. -/
theorem unitMeas_Ico : unitMeas (Set.Ico (0 : ℝ) 1) = 1 := by
  rw [unitMeas, Measure.restrict_apply measurableSet_Ico, Set.inter_self, Real.volume_Ico,
    sub_zero, ENNReal.ofReal_one]

/-- The measure of a complement, for `unitMeas.real`. -/
theorem unitMeas_real_compl (A : Set ℝ) (hA : MeasurableSet A) :
    unitMeas.real Aᶜ = 1 - unitMeas.real A := by
  have h : unitMeas.real A + unitMeas.real Aᶜ = 1 := by
    rw [measureReal_add_measureReal_compl (μ := unitMeas) hA]
    simp [measureReal_def]
  linarith

/-- A closed interval has `unitMeas.real`-measure at most its length. -/
theorem unitMeas_real_Icc_le (a b : ℝ) : unitMeas.real (Set.Icc a b) ≤ max (b - a) 0 := by
  have h1 : unitMeas (Set.Icc a b) ≤ volume (Set.Icc a b) := by
    rw [unitMeas, Measure.restrict_apply measurableSet_Icc]
    exact measure_mono Set.inter_subset_left
  have h2 : volume (Set.Icc a b) = ENNReal.ofReal (b - a) := Real.volume_Icc
  calc unitMeas.real (Set.Icc a b) = (unitMeas (Set.Icc a b)).toReal := (rfl)
    _ ≤ (volume (Set.Icc a b)).toReal :=
        ENNReal.toReal_mono (by rw [h2]; exact ENNReal.ofReal_ne_top) h1
    _ = max (b - a) 0 := by rw [h2, ENNReal.toReal_ofReal']

namespace IET

/-- **Exchanges preserve the measure** on `[0, 1)`. -/
theorem unitMeas_preimage (f : IET 0 1) {A : Set ℝ} (hA : MeasurableSet A) :
    unitMeas (⇑f ⁻¹' A) = unitMeas A := by
  have h1 : (volume.restrict (Set.Ico 0 1)) (⇑f ⁻¹' A)
      = volume (⇑f ⁻¹' A ∩ Set.Ico 0 1) :=
    Measure.restrict_apply (hA.preimage (measurable f))
  have h2 : (volume.restrict (Set.Ico 0 1)) A = volume (A ∩ Set.Ico 0 1) :=
    Measure.restrict_apply hA
  rw [unitMeas, h1, h2]
  obtain ⟨s, hs⟩ := f.isIET.exists_isCutSet zero_lt_one
  exact IsCutSet.measure_preimage (e := f.toEquiv) hs hA

/-- **Exchanges preserve the measure**: real-valued form. -/
theorem unitMeas_real_preimage (f : IET 0 1) {A : Set ℝ} (hA : MeasurableSet A) :
    unitMeas.real (⇑f ⁻¹' A) = unitMeas.real A := by
  rw [Measure.real, Measure.real, unitMeas_preimage f hA]

end IET

/-! ## Invariant measures, unique ergodicity, and rigidity

The notions the main theorem is stated with, here rather than higher up: they are shared by
`IETFree/Pair/` (the free-group development), `IETFree/UniqueErgodicity/` (which turns unique
ergodicity into uniform convergence of Birkhoff averages) and `IETFree/Rigidity/`.  All three are
stated with the reference measure `unitMeas` above, which is why they come after it. -/

/-- Invariance of a probability measure under an exchange: `μ ∘ f⁻¹ = μ`.

This is the invariance equation alone.  **The carrier condition `μ (Ico 0 1) = 1` is not part of
it**: an exchange is the identity off the interval it is built on (`mkIETFun_of_notMem`), so every
probability measure on `[0, 1)ᶜ` is invariant, and the unrestricted `∃! μ, Invariant μ f` is false
for every exchange (the Dirac mass at `2` is invariant alongside Lebesgue's).  Each consumer
conjoins the carrier condition — `UniqueErgodic` below, `RayCondition` in
`RauzyVeech/MainComponents.lean`, `length_injective_of_floors` — and with it `μ ↦ μ|_{[0,1)}` is
injective.  Why no hypothesis on the length vector is needed is a remark about the a.e. statement,
in `IETFree/TopBotFormalism.lean`. -/
def Invariant (μ : ProbabilityMeasure ℝ) (f : IET 0 1) : Prop := (μ : Measure ℝ).map ⇑f = μ

/-- **Definition 2.1 of the paper**: unique ergodicity — there is exactly one invariant probability
measure carried by `[0, 1)`.

This is the weak form.  The strong form — the Birkhoff averages of every continuous test function
converge to their integral, uniformly over the initial point — is not the definition: it is the
theorem `IntervalExchange.UniqueErgodicity.uniformBirkhoff_of_uniqueErgodic`, proved by the transfer
argument of `IETFree/UniqueErgodicity/` and stated there as `UniformBirkhoff`. -/
def UniqueErgodic (f : IET 0 1) : Prop :=
  ∃! μ : ProbabilityMeasure ℝ, Invariant μ f ∧ (μ : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1

/-- **Definition 2.2 of the paper, with the sets required to lie in `[0, 1)`**: rigid by
translations — some powers of the exchange are translations on sets whose measure tends to `1`.
The extra conjunct `B n ⊆ [0, 1)` is a strengthening, recorded in `formalization.yaml`.  That
almost every irreducible exchange is rigid is Veech's rigidity theorem: `veechRigidity` in
`IETFree/Pair/Irreducible.lean`, proved in `IETFree/Rigidity/`
(`Rigidity.ae_isRigidByTranslations`). -/
def IsRigidByTranslations (f : IET 0 1) : Prop :=
  ∃ q : ℕ → ℕ, ∃ t : ℕ → ℝ, ∃ B : ℕ → Set ℝ,
    Tendsto q atTop atTop ∧ Tendsto t atTop (nhds 0) ∧
      (∀ n, B n ⊆ Set.Ico (0 : ℝ) 1) ∧ (∀ n, MeasurableSet (B n)) ∧
        Tendsto (fun n => unitMeas.real (B n)) atTop (nhds 1) ∧
          ∀ (n : ℕ) (x : ℝ), x ∈ B n → ((f ^ q n) x) = x + t n

/-! ## Measurability of the simplex chart -/

/-- The free region of the simplex chart is measurable. -/
theorem measurableSet_simplexRegion (d : ℕ) : MeasurableSet (simplexRegion d) := by
  have h1 : MeasurableSet {v : Fin (d - 1) → ℝ | ∀ i, 0 < v i} := by
    simpa only [Set.ofPred_forall] using
      MeasurableSet.iInter fun i =>
        measurableSet_lt measurable_const (continuous_apply i).measurable
  have h2 : MeasurableSet {v : Fin (d - 1) → ℝ | ∑ i, v i < 1} :=
    measurableSet_lt (Finset.measurable_sum _ fun i _ => (continuous_apply i).measurable)
      measurable_const
  exact h1.inter h2

/-- The parametrisation of the simplex is measurable. -/
theorem measurable_simplexMap (d : ℕ) : Measurable (simplexMap d) := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [simplexMap]
  split_ifs with h
  · exact continuous_real_toNNReal.measurable.comp
      (measurable_const.sub (Finset.measurable_sum _ fun j _ => measurable_pi_apply j))
  · exact continuous_real_toNNReal.measurable.comp (measurable_pi_apply _)

/-- The last coordinate of `simplexMap (m + 1) v` is `1 - ∑ v` (a `NNReal`). -/
theorem simplexMap_last {m : ℕ} (v : Fin m → ℝ) :
    simplexMap (m + 1) v (Fin.last m) = (1 - ∑ j, v j).toNNReal := by
  simp only [simplexMap]
  rw [dite_eq_left (by simp)]
  rfl

/-- The `j`-th coordinate of `simplexMap (m + 1) v` is `v j` (a `NNReal`). -/
theorem simplexMap_castSucc {m : ℕ} (v : Fin m → ℝ) (j : Fin m) :
    simplexMap (m + 1) v j.castSucc = (v j).toNNReal := by
  simp only [simplexMap]
  rw [dite_eq_right (by simp [Fin.val_castSucc]; omega)]
  congr 1

/-! ## Irreducibility of a permutation -/

/-- The paper's irreducibility of a permutation: the only initial segment `{i | i ≤ k}` mapped into
itself by `π` is the whole of `Fin d`. For `(π₀,π₁) = (id,π₁)` this is Yoccoz's condition (2.5).
-/
def IsIrreduciblePerm {d : ℕ} (π : Equiv.Perm (Fin d)) : Prop :=
  ∀ k : Fin d, (∀ i : Fin d, i ≤ k → π i ≤ k) → ∀ i : Fin d, i ≤ k

end IntervalExchange

end
