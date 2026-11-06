/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.CutSetMeasure

/-!
# The one-sided limits of an interval exchange

An exchange `f` with cut set `s` on `[a, b)` is a translation on each cell `[c, c')` cut out by
`s`, and the identity outside `[a, b)`.  This module studies its two one-sided limits:

* `cutBelow h x` is the largest cut strictly below `x`, and `leftLimit h x` is the left limit of `f`
  at `x` (Definition 1.1 of the blueprint): `f y → leftLimit h x` as `y ↑ x`;
* `leftLimit` is a translation on each left cell `(c, c']`, hence injective (`leftLimit_injOn`).

The last theorem, `exists_invariant_ne_of_periodic_leftLimit`, is Lemma 4.9 of the blueprint: a
periodic point of the left limit bounds a periodic interval, and the orbit of a point of that
interval carries an invariant probability measure which is not Lebesgue.  This is what shows that
unique ergodicity forbids periodic left limits.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology BigOperators ENNReal NNReal

variable {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}

/-! ## The cut just below a point -/

/-- **The largest cut strictly below `x`** (`x > a`, so that `a` itself qualifies).  This is the
left end of the cell `(cutBelow h x, x]` whose translation gives the left limit at `x`. -/
noncomputable def cutBelow (h : IsCutSet f a b s) (x : ℝ) (hx : a < x) : ℝ :=
  (s.filter (fun c => c < x)).max' ⟨a, Finset.mem_filter.mpr ⟨h.a_mem, hx⟩⟩

theorem cutBelow_mem (h : IsCutSet f a b s) {x : ℝ} (hx : a < x) : cutBelow h x hx ∈ s := by
  have hmem : (s.filter (fun c => c < x)).max' ⟨a, Finset.mem_filter.mpr ⟨h.a_mem, hx⟩⟩
      ∈ s.filter (fun c => c < x) := Finset.max'_mem _ _
  exact (Finset.mem_filter.mp hmem).1

theorem cutBelow_lt (h : IsCutSet f a b s) {x : ℝ} (hx : a < x) : cutBelow h x hx < x := by
  have hmem : (s.filter (fun c => c < x)).max' ⟨a, Finset.mem_filter.mpr ⟨h.a_mem, hx⟩⟩
      ∈ s.filter (fun c => c < x) := Finset.max'_mem _ _
  exact (Finset.mem_filter.mp hmem).2

theorem lt_cutBelow (h : IsCutSet f a b s) {x c : ℝ} (hx : a < x) (hc : c ∈ s) (hcx : c < x) :
    c ≤ cutBelow h x hx :=
  Finset.le_max' (s.filter (fun c => c < x)) c (Finset.mem_filter.mpr ⟨hc, hcx⟩)

theorem cutBelow_mem_Ico (h : IsCutSet f a b s) {x : ℝ} (hx : a < x) :
    cutBelow h x hx ∈ Set.Ico a b :=
  h.cuts_mem _ (cutBelow_mem h hx)

/-- No cut lies in `(cutBelow h x, y]` for `cutBelow h x < y < x`. -/
theorem not_separated_cutBelow_of_lt (h : IsCutSet f a b s) {x y : ℝ} (hx : a < x) (hy : y < x)
    (hcy : cutBelow h x hx < y) : ¬ Separated s (cutBelow h x hx) y := by
  intro hsep
  obtain ⟨c, hc, h1, h2⟩ := hsep.exists_of_le hcy.le
  rcases lt_or_eq_of_le h2 with hlt | heq
  · exact absurd (lt_cutBelow h hx hc (lt_trans hlt hy)) (not_le.mpr h1)
  · rw [heq] at hc h1
    exact absurd h1 (not_lt.mpr (lt_cutBelow h hx hc hy))

/-- **On the left cell of `x`, `f` is a translation**: for `cutBelow h x < y < x`,
`f y = y + (f (cutBelow h x) - cutBelow h x)`. -/
theorem apply_eq_add_cutBelow (h : IsCutSet f a b s) {x y : ℝ} (hx : x ∈ Set.Ioc a b)
    (hy : y ∈ Set.Ioo (cutBelow h x hx.1) x) :
    f y = y + (f (cutBelow h x hx.1) - cutBelow h x hx.1) := by
  have hc := cutBelow_mem_Ico h hx.1
  have hyab : y ∈ Set.Ico a b := ⟨hc.1.trans_lt hy.1 |>.le, hy.2.trans_le hx.2⟩
  have hns := not_separated_cutBelow_of_lt h hx.1 hy.2 hy.1
  have htrans := h.transl_of_not_separated _ _ hc hyab hns
  linarith

/-- The cut below a point is constant on the left cell of that point. -/
theorem cutBelow_eq_of_mem (h : IsCutSet f a b s) {x y : ℝ} (hx : a < x) (hy : y < x)
    (hy' : cutBelow h x hx < y) :
    cutBelow h y ((cutBelow_mem_Ico h hx).1.trans_lt hy') = cutBelow h x hx := by
  have hay : a < y := (cutBelow_mem_Ico h hx).1.trans_lt hy'
  refine le_antisymm ?_ (lt_cutBelow h hay (cutBelow_mem h hx) hy')
  refine Finset.max'_le (s.filter (fun c => c < y)) _ (cutBelow h x hx) (fun c hc => ?_)
  obtain ⟨hcs, hclt⟩ := Finset.mem_filter.mp hc
  exact lt_cutBelow h hx hcs (lt_trans hclt hy)

/-! ## The left limit -/

/-- **The left limit of `f` at `x`** (Definition 1.1 of the blueprint): at `x ≤ a` it is `x`, and
for `a < x` it is `x + (f c - c)`, where `c = cutBelow h x` is the largest cut strictly below `x`.
On `Ioc a b` that is the limit of `f y` as `y ↑ x` (`tendsto_left`).

The function is total, and outside `Icc a b` it is *not* claimed to be a one-sided limit: for
`x > b` the cell formula keeps running past the last cell (Blueprint §1.2 extends `L` by the
identity off `[a,b]` only "if a total function is wanted"). No proof in this repository evaluates
`leftLimit` outside `Icc a b`. -/
noncomputable def leftLimit (h : IsCutSet f a b s) (x : ℝ) : ℝ :=
  if hx : a < x then x + (f (cutBelow h x hx) - cutBelow h x hx) else x

theorem leftLimit_of_le (h : IsCutSet f a b s) {x : ℝ} (hx : x ≤ a) : leftLimit h x = x := by
  rw [leftLimit, dif_neg (not_lt.mpr hx)]

/-- **Lemma 1.8**: on the cell `(c, c']`, `leftLimit` is `y ↦ y + (f c - c)`. -/
theorem leftLimit_eq_add (h : IsCutSet f a b s) {x : ℝ} (hx : x ∈ Set.Ioc a b) :
    leftLimit h x = x + (f (cutBelow h x hx.1) - cutBelow h x hx.1) := by
  rw [leftLimit, dif_pos hx.1]

/-- **The left limit is the limit from the left.** -/
theorem tendsto_left (h : IsCutSet f a b s) {x : ℝ} (hx : x ∈ Set.Ioc a b) :
    Tendsto f (𝓝[<] x) (𝓝 (leftLimit h x)) := by
  have hc := cutBelow_lt h hx.1
  have heq : f =ᶠ[𝓝[<] x] fun y => y + (f (cutBelow h x hx.1) - cutBelow h x hx.1) := by
    filter_upwards [Ioo_mem_nhdsLT hc] with y hy
    exact apply_eq_add_cutBelow h hx hy
  have htend : Tendsto (fun y : ℝ => y + (f (cutBelow h x hx.1) - cutBelow h x hx.1))
      (𝓝[<] x) (𝓝 (leftLimit h x)) := by
    have h' : Tendsto (fun y : ℝ => y + (f (cutBelow h x hx.1) - cutBelow h x hx.1)) (𝓝 x)
        (𝓝 (x + (f (cutBelow h x hx.1) - cutBelow h x hx.1))) :=
      tendsto_id.add tendsto_const_nhds
    rw [leftLimit_eq_add h hx]
    exact tendsto_nhdsWithin_of_tendsto_nhds h'
  exact Tendsto.congr' heq.symm htend

/-- **The left limit stays in the interval** (Lemma 1.2 (i)). -/
theorem leftLimit_mem (h : IsCutSet f a b s) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    leftLimit h x ∈ Set.Icc a b := by
  rcases eq_or_lt_of_le hx.1 with hxa | hax
  · rw [← hxa, leftLimit_of_le h le_rfl]
    exact ⟨le_rfl, hxa ▸ hx.2⟩
  · have hx' : x ∈ Set.Ioc a b := ⟨hax, hx.2⟩
    refine IsClosed.mem_of_tendsto isClosed_Icc (tendsto_left h hx') ?_
    filter_upwards [Ioo_mem_nhdsLT (cutBelow_lt h hax)] with y hy
    have hyab : y ∈ Set.Ico a b :=
      ⟨(cutBelow_mem_Ico h hax).1.trans_lt hy.1 |>.le, hy.2.trans_le hx.2⟩
    exact ⟨(h.mapsTo y hyab).1, (h.mapsTo y hyab).2.le⟩

/-- The left limit equals the value off the cut set (Lemma 1.2 (iv)). -/
theorem leftLimit_eq_apply (h : IsCutSet f a b s) {x : ℝ} (hx : x ∈ Set.Ico a b)
    (hxs : x ∉ s) : leftLimit h x = f x := by
  have hax : a < x := lt_of_le_of_ne hx.1 (fun hcon => hxs (hcon ▸ h.a_mem))
  rw [leftLimit_eq_add h ⟨hax, hx.2.le⟩]
  have hns : ¬ Separated s (cutBelow h x hax) x := by
    intro hsep
    obtain ⟨c, hc, h1, h2⟩ := hsep.exists_of_le (cutBelow_lt h hax).le
    rcases lt_or_eq_of_le h2 with hlt | heq
    · exact absurd (lt_cutBelow h hax hc hlt) (not_le.mpr h1)
    · exact hxs (heq ▸ hc)
  have htrans := h.transl_of_not_separated _ _ (cutBelow_mem_Ico h hax) hx hns
  linarith

/-! ## The left limit is a bijection of the interval

`leftLimit` is a translation on each left cell `(c, c']`, and the images of these cells are pairwise
disjoint, so `leftLimit` is injective.  Everything in this section assumes that the exchange is
injective (in the application it is a bijection of `[a, b)`).
-/

/-- If `x` is in the left cell of the cut `cellStarts i`, then `x` is at most the right end of that
cell. -/
theorem le_cellPos_of_cutBelow_eq (h : IsCutSet f a b s) {x : ℝ} (hx : x ∈ Set.Ioc a b)
    {i : Fin s.card} (hi : h.cellStarts i = cutBelow h x hx.1) : x ≤ h.cellPos (i.val + 1) := by
  by_contra hcon
  rw [not_le] at hcon
  rcases h.cellPos_succ i with ⟨hlt, hh⟩ | ⟨heq, hh⟩
  · rw [hh] at hcon
    have hmem : h.cellStarts ⟨i.val + 1, hlt⟩ ∈ s := h.cellStarts_mem _
    have hle := lt_cutBelow h hx.1 hmem hcon
    rw [← hi] at hle
    have hlt' : h.cellStarts i < h.cellStarts ⟨i.val + 1, hlt⟩ :=
      h.cellStarts_lt_iff.mpr (Fin.lt_def.mpr (by simp))
    linarith
  · rw [hh] at hcon
    linarith [hx.2, hcon.le]

/-- **`leftLimit` maps the left cell of each cut onto the image of the cell**: for `x ∈ (a, b]`
there is a cell `i` with `cutBelow h x = cellStarts i` and
`leftLimit h x ∈ (f (cellStarts i), f (cellStarts i) + cellLen i]`. -/
theorem leftLimit_mem_Ioc_image (h : IsCutSet f a b s) {x : ℝ} (hx : x ∈ Set.Ioc a b) :
    ∃ i : Fin s.card, h.cellStarts i = cutBelow h x hx.1 ∧
      leftLimit h x ∈ Set.Ioc (f (h.cellStarts i)) (f (h.cellStarts i) + h.cellLen i) := by
  obtain ⟨i, hi⟩ := h.cellStarts_surj (cutBelow_mem h hx.1)
  have hcx := cutBelow_lt h hx.1
  have hpos : h.cellPos i.val = h.cellStarts i := h.cellPos_of_lt i.isLt
  refine ⟨i, hi, ?_, ?_⟩
  · rw [leftLimit_eq_add h hx, hi]
    linarith
  · rw [leftLimit_eq_add h hx, hi, IsCutSet.cellLen, hpos]
    have hle := le_cellPos_of_cutBelow_eq h hx hi
    linarith

/-- The left limit of a point of `(a, b]` is strictly larger than `a`. -/
theorem lt_leftLimit (h : IsCutSet f a b s) {x : ℝ} (hx : x ∈ Set.Ioc a b) :
    a < leftLimit h x := by
  obtain ⟨i, _, hmem⟩ := leftLimit_mem_Ioc_image h hx
  have hge : a ≤ f (h.cellStarts i) := (h.mapsTo _ (h.cellStarts_mem_Ico i)).1
  linarith [hmem.1]

/-- The images of the cells, taken closed on the right, are pairwise disjoint (the images of the
half-open cells are disjoint, and a right end of one is not the left end of another). -/
theorem image_cell_Ioc_disjoint (h : IsCutSet f a b s) (hinj : Function.Injective f)
    {i j : Fin s.card} (hij : i ≠ j) :
    Disjoint (Set.Ioc (f (h.cellStarts i)) (f (h.cellStarts i) + h.cellLen i))
      (Set.Ioc (f (h.cellStarts j)) (f (h.cellStarts j) + h.cellLen j)) := by
  rw [Set.disjoint_left]
  intro z hzi hzj
  obtain ⟨hzi1, hzi2⟩ := hzi
  obtain ⟨hzj1, hzj2⟩ := hzj
  set w : ℝ := (max (f (h.cellStarts i)) (f (h.cellStarts j)) + z) / 2 with hw
  have hw1 : f (h.cellStarts i) < w := by
    rw [hw]; linarith [le_max_left (f (h.cellStarts i)) (f (h.cellStarts j)), hzi1]
  have hw2 : w < z := by
    rw [hw]; linarith [max_lt hzi1 hzj1]
  have hw3 : f (h.cellStarts j) < w := by
    rw [hw]; linarith [le_max_right (f (h.cellStarts i)) (f (h.cellStarts j)), hzj1]
  have hmi : w ∈ f '' Set.Ico (h.cellStarts i) (h.cellPos (i.val + 1)) := by
    rw [h.image_cell i]
    exact ⟨hw1.le, lt_of_lt_of_le hw2 hzi2⟩
  have hmj : w ∈ f '' Set.Ico (h.cellStarts j) (h.cellPos (j.val + 1)) := by
    rw [h.image_cell j]
    exact ⟨hw3.le, lt_of_lt_of_le hw2 hzj2⟩
  exact (Set.disjoint_left.mp (h.image_cell_disjoint hinj hij) hmi) hmj

/-- **`leftLimit` is injective on `[a, b]`** (Lemma 1.8 (ii)-(iii)).  The injectivity of the
exchange is needed: `leftLimit` is a translation on each left cell, and the injectivity of `f` is
what makes the images of distinct cells disjoint. -/
theorem leftLimit_injOn (h : IsCutSet f a b s) (hinj : Function.Injective f) :
    Set.InjOn (leftLimit h) (Set.Icc a b) := by
  have key {u v : ℝ} : a < u → u ≤ v → v ≤ b →
      leftLimit h u = leftLimit h v → u = v := by
    intro hau huv hvb heq
    by_contra hne
    have hlt : u < v := lt_of_le_of_ne huv hne
    obtain ⟨i, hi, hmem_i⟩ := leftLimit_mem_Ioc_image h ⟨hau, huv.trans hvb⟩
    obtain ⟨j, hj, hmem_j⟩ := leftLimit_mem_Ioc_image h ⟨hau.trans_le huv, hvb⟩
    by_cases hij : i = j
    · subst hij
      have hcx : cutBelow h u hau = cutBelow h v (hau.trans hlt) := by rw [← hi, hj]
      rw [leftLimit_eq_add h ⟨hau, huv.trans hvb⟩,
        leftLimit_eq_add h ⟨hau.trans hlt, hvb⟩, hcx] at heq
      linarith
    · have hmem_j' : leftLimit h u ∈
          Set.Ioc (f (h.cellStarts j)) (f (h.cellStarts j) + h.cellLen j) := by
        rw [heq]; exact hmem_j
      exact (Set.disjoint_left.mp (image_cell_Ioc_disjoint h hinj hij) hmem_i) hmem_j'
  intro x hx y hy hxy
  rcases le_total x y with hle | hle
  · rcases eq_or_lt_of_le hx.1 with hxa | hax
    · rcases eq_or_lt_of_le hy.1 with hya | hay
      · rw [← hxa, ← hya]
      · exfalso
        have h1 : leftLimit h x = a := by rw [← hxa, leftLimit_of_le h le_rfl]
        rw [h1] at hxy
        have := lt_leftLimit h ⟨hay, hy.2⟩
        linarith
    · exact key hax hle hy.2 hxy
  · rcases eq_or_lt_of_le hy.1 with hya | hay
    · rcases eq_or_lt_of_le hx.1 with hxa | hax
      · rw [← hxa, ← hya]
      · exfalso
        have h1 : leftLimit h y = a := by rw [← hya, leftLimit_of_le h le_rfl]
        rw [h1] at hxy
        have := lt_leftLimit h ⟨hax, hx.2⟩
        linarith
    · exact (key hay hle hx.2 hxy.symm).symm

/-! ## A periodic left limit is a periodic interval

Blueprint Lemma 4.9, in the form needed downstream: if some `x₀ ∈ (a, b]` is periodic
for the left limit `leftLimit h` with period `k ≥ 1`, then the left cells of the cycle
all have a common length `ε > 0`, and the point `x₀ - ε/2` is periodic for `f` itself
with period `k`.  The orbit of that point therefore supports an `f`-invariant
probability measure which is atomic, hence not Lebesgue.
-/

/-- **Lemma 4.9**: a periodic point of the left limit gives an invariant probability measure
different from Lebesgue. -/
theorem exists_invariant_ne_of_periodic_leftLimit (h : IsCutSet f a b s)
    (hper : ∃ x ∈ Set.Ioc a b, ∃ k : ℕ, 0 < k ∧ (leftLimit h)^[k] x = x) :
    ∃ ν : ProbabilityMeasure ℝ, (ν : Measure ℝ).map f = ν ∧
      (ν : Measure ℝ) (Set.Ico a b) = 1 ∧
      (ν : Measure ℝ) ≠ volume.restrict (Set.Ico a b) := by
  obtain ⟨x₀, hx₀, k, hk, hperk⟩ := hper
  set c : ℕ → ℝ := fun i => (leftLimit h)^[i] x₀ with hc
  have hc_zero : c 0 = x₀ := rfl
  have hc_succ (i) : c (i + 1) = leftLimit h (c i) := by
    rw [hc]
    exact Function.iterate_succ_apply' _ _ _
  have hc_k : c k = x₀ := hperk
  have hc_mem (i) : c i ∈ Set.Icc a b := by
    induction i with
    | zero => rw [hc_zero]; exact ⟨hx₀.1.le, hx₀.2⟩
    | succ i ih => rw [hc_succ i]; exact leftLimit_mem h ih
  have hc_ne (i) (hi : i ≤ k) : c i ≠ a := by
    intro hia
    have hstep (j) : c (i + j) = a := by
      induction j with
      | zero => simpa using hia
      | succ j ih =>
        rw [← Nat.add_assoc]
        rw [hc_succ (i + j), ih, leftLimit_of_le h le_rfl]
    have hka : c k = a := by
      rw [← Nat.add_sub_cancel' hi]
      exact hstep (k - i)
    rw [hc_k] at hka
    linarith [hx₀.1]
  have hca (i) (hi : i ≤ k) : c i ∈ Set.Ioc a
      b := ⟨lt_of_le_of_ne (hc_mem i).1 (Ne.symm (hc_ne i hi)), (hc_mem i).2⟩
  have hc_period (i) : c (i + k) = c i := by
    simp only [hc]
    rw [Function.iterate_add_apply, hperk]
  have hc_mod (q i) : c (i + q * k) = c i := by
    induction q with
    | zero => rw [Nat.zero_mul, Nat.add_zero]
    | succ q ih =>
      rw [Nat.succ_mul, ← Nat.add_assoc, hc_period, ih]
  have hc_all (i) : c i ∈ Set.Ioc a b := by
    have hi : i % k + (i / k) * k = i := by
      rw [Nat.mul_comm]
      exact Nat.mod_add_div i k
    rw [← hi, hc_mod (i / k) (i % k)]
    exact hca (i % k) (Nat.mod_lt _ hk).le
  -- the common length of the left cells of the cycle
  set d : ℕ → ℝ := fun i => c i - cutBelow h (c i) (hc_all i).1 with hd
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image (Finset.range k) d
    ⟨0, Finset.mem_range.mpr hk⟩
  set ε : ℝ := d i₀ with hε
  have hi₀' : i₀ < k := Finset.mem_range.mp hi₀
  have hε_pos : 0 < ε := by
    rw [hε, hd]
    exact sub_pos.mpr (cutBelow_lt h _)
  have hε_le (i : ℕ) (hi : i < k) : ε ≤ c i - cutBelow h (c i) (hc_all i).1 := by
    have hle : ε ≤ d i := hmin i (Finset.mem_range.mpr hi)
    rwa [hε, hd] at hle
  -- on the left cell of `c i`, `f` translates by the displacement of the left limit
  have step (i : ℕ) (hi : i < k) : f (c i - ε / 2) = c (i + 1) - ε / 2 := by
    have hci : c i ∈ Set.Ioc a b := hc_all i
    have hlt : ε / 2 < c i - cutBelow h (c i) hci.1 := by
      have := hε_le i hi
      linarith
    have hy : c i - ε / 2 ∈ Set.Ioo (cutBelow h (c i) hci.1) (c i) :=
      ⟨by linarith [cutBelow_lt h hci.1], by linarith⟩
    have htrans := apply_eq_add_cutBelow h hci hy
    have hL : leftLimit h (c i) = c (i + 1) := (hc_succ i).symm
    have hadd := leftLimit_eq_add h hci
    rw [hL] at hadd
    linarith
  -- the point `x₀ - ε/2` is periodic for `f`, with period `k`
  have hkey (j) (hj : j ≤ k) : (f^[j]) (c 0 - ε / 2) = c j - ε / 2 := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact step j (by omega)
  set y : ℝ := c 0 - ε / 2 with hy_def
  have hy_per : (f^[k]) y = y := by
    rw [hy_def, hkey k le_rfl, hc_k, hc_zero]
  have hy_mem (j) (hj : j < k) : (f^[j]) y ∈ Set.Ico a b := by
    have h1 : (f^[j]) y = c j - ε / 2 := by rw [hy_def]; exact hkey j hj.le
    have hcj : c j ∈ Set.Ioc a b := hc_all j
    have hlt : ε / 2 < c j - cutBelow h (c j) hcj.1 := by
      have := hε_le j hj
      linarith
    have hlow := (cutBelow_mem_Ico h hcj.1).1
    rw [h1]
    exact ⟨by linarith, by linarith [hcj.2]⟩
  -- the empirical measure of the periodic orbit
  set ν₀ : Measure ℝ := ∑ i ∈ Finset.range k, Measure.dirac ((f^[i]) y) with hν₀
  have hν₀_apply (A : Set ℝ) :
      ν₀ A = ∑ i ∈ Finset.range k, Measure.dirac ((f^[i]) y) A :=
    Measure.finsetSum_apply _ _ A
  have hν₀_univ : ν₀ Set.univ = (k : ℝ≥0∞) := by
    rw [hν₀_apply]
    simp [Finset.card_range]
  have hshift : (∑ i ∈ Finset.range k, Measure.dirac ((f^[i + 1]) y))
      = ∑ i ∈ Finset.range k, Measure.dirac ((f^[i]) y) := by
    obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    subst hm
    conv_lhs => rw [Finset.sum_range_succ]
    conv_rhs => rw [Finset.sum_range_succ', Function.iterate_zero_apply]
    rw [hy_per]
  have hmap : Measure.map f ν₀ = ν₀ := by
    have hfs := Measure.map_finset_sum (s := Finset.range k)
      (m := fun i => Measure.dirac ((f^[i]) y)) (f := f) h.measurable.aemeasurable
    rw [hν₀, hfs]
    rw [show (∑ i ∈ Finset.range k, Measure.map f (Measure.dirac ((f^[i]) y)))
        = ∑ i ∈ Finset.range k, Measure.dirac ((f^[i + 1]) y) from
      Finset.sum_congr rfl (fun i _ => by
        rw [Measure.map_dirac, Function.iterate_succ_apply'])]
    exact hshift
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by simp [hk.ne']
  have hktop : (k : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top k
  refine ⟨⟨((k : ℝ≥0∞))⁻¹ • ν₀, ?_⟩, ?_, ?_, ?_⟩
  · rw [isProbabilityMeasure_iff, Measure.smul_apply, hν₀_univ]
    exact ENNReal.inv_mul_cancel hk0 hktop
  · simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_smul, hmap]
  · simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.smul_apply, hν₀_apply]
    have h1 (i) (hi : i ∈ Finset.range k) : Measure.dirac ((f^[i]) y) (Set.Ico a b) = 1 := by
      rw [Measure.dirac_apply, Set.indicator_of_mem (hy_mem i (Finset.mem_range.mp hi))]
      simp
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel hk0 hktop
  · intro hcontra
    have hcontra' : (((k : ℝ≥0∞))⁻¹ • ν₀) = volume.restrict (Set.Ico a b) := hcontra
    have hyIco : y ∈ Set.Ico a b := hy_mem 0 hk
    have h0 : Measure.dirac ((f^[0]) y) {y} = 1 := by
      rw [Function.iterate_zero_apply, Measure.dirac_apply,
        Set.indicator_of_mem (Set.mem_singleton y)]
      simp
    have hge : (1 : ℝ≥0∞) ≤ ν₀ {y} := by
      rw [hν₀_apply]
      calc (1 : ℝ≥0∞) = Measure.dirac ((f^[0]) y) {y} := h0.symm
        _ ≤ ∑ i ∈ Finset.range k, Measure.dirac ((f^[i]) y) {y} :=
            Finset.single_le_sum (f := fun i => Measure.dirac ((f^[i]) y) {y})
              (fun i _ => zero_le) (Finset.mem_range.mpr hk)
    have hne : ν₀ {y} ≠ 0 := by
      intro h0
      rw [h0] at hge
      exact absurd hge (not_le.mpr (zero_lt_one))
    have hpos : 0 < ((k : ℝ≥0∞))⁻¹ * ν₀ {y} :=
      ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hktop) hne
    have hvol : (volume.restrict (Set.Ico a b)) {y} = 0 := by
      rw [Measure.restrict_apply (measurableSet_singleton y), Set.singleton_inter_of_mem hyIco,
        Real.volume_singleton]
    rw [← hcontra', Measure.smul_apply] at hvol
    exact absurd hvol hpos.ne'

/-! ## The jump set -/

/-- **(H2)**: the left limit has no periodic point in `(a, b]`.  This is not a hypothesis of the
main theorem: it follows from unique ergodicity, which is Corollary 4.10 below. -/
def NoPeriodicLeftLimit (_h : IsCutSet f a b s) : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ x ∈ Set.Ioc a b, (leftLimit _h)^[k] x ≠ x

/-- **Corollary 4.10**: unique ergodicity forbids periodic left limits. -/
theorem noPeriodicLeftLimit_of_unique (h : IsCutSet f a b s)
    (hH1 : ∀ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ).map f = μ →
      (μ : Measure ℝ) (Set.Ico a b) = 1 → (μ : Measure ℝ) = volume.restrict (Set.Ico a b)) :
    NoPeriodicLeftLimit h := by
  intro k hk x hx hper
  obtain ⟨ν, hν, hνIco, hνne⟩ :=
    exists_invariant_ne_of_periodic_leftLimit h ⟨x, hx, k, hk, hper⟩
  exact hνne (hH1 ν hν hνIco)

end
