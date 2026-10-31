/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.Irreducible

/-!
The reduction data: the blocks and the pair-splitting singularities, the good parameter set `O`, and
the covering step.

This file sets up the interface that the reduction runs on:

* the blocks of the pair `(f, g)`: `IsBlock` is the paper's pair of consecutive pair-splitting
  singularities, and `IsPairSplitting` the splitting singularities of one exchange inside a fixed
  interval of the other (`IsSplitting`, `IsFixedCell`);
* `O`, the complement of the finitely many hyperplanes `k + ∑ aᵢλᵢ + ∑ bⱼμⱼ = 0` over which the
  combinatorial type of the pair `(f, g)` can change (`IsBadParam`, `goodParams`), with its two
  consequences `ae_goodParams` and `coeffs_eq_of_good` / `coeffs_zero_of_good`;
* the covering step `measure_zero_of_forall_exists_isOpen_null`, which turns the local statements of
  `GoodRegion` into an almost-everywhere statement.

The parameter space is `PReal d e` — the **free** lengths `(λ₁, …, λ_{d-1})` and `(μ₁, …, μ_{e-1})`,
the last length of each vector being `1` minus their sum.  The choice is essential: with all `d + e`
lengths as coordinates (or even with the `d + e - 2` "redundant" ones) the relation
`-1 + ∑ λᵢ = 0` holds on the whole simplex and every parameter is bad.  See `NOTES.md`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-! ## 0. Blocks and pair-splitting singularities

The interval `[0, 1)` splits into blocks between consecutive *pair-splitting* singularities of the
pair `(f, g)`; on each block the pair is irreducible, which is what lets Theorem 2.6 be applied
there.  The definitions and the invariance part of Lemma 3.2 are here; the irreducibility part,
which needs the good parameter set `O`, is `block_irreducible_on_good` in section 4. -/

/-- **An interval exchange, presented by its data**: a permutation of `Fin n` and a point `v` of
`simplexRegion n`, i.e. the `n - 1` free lengths, positive and with total mass `< 1` (the last
length being `1 - ∑ v`).

This is the presentation Section 3 works with: `mkIET1` of a permutation and a length vector, with
the length vector in *free coordinates*.  Taking the lengths from `simplexRegion` — the very set
that `simplexVolume` is built on — makes the datum literally a point of the measure space:
`simplexVolume n` is Lebesgue measure on `simplexRegion n` pushed forward by `simplexMap n`, and a
pair of data is a point of `PReal`. -/
structure IETDatum (n : ℕ) [NeZero n] where
  /-- the permutation of the cells -/
  π : Equiv.Perm (Fin n)
  /-- the `n - 1` free lengths, as a point of the free region -/
  v : Fin (n - 1) → ℝ
  /-- the free lengths are positive with total mass `< 1`, so that `1 - ∑ v` is positive -/
  mem_region : v ∈ simplexRegion n

namespace IETDatum

variable {n : ℕ} [NeZero n]

/-- **The free lengths of a datum are positive.** -/
theorem pos (D : IETDatum n) : ∀ i, 0 < D.v i := D.mem_region.1

/-- **The free lengths of a datum have total mass less than `1`.** -/
theorem sum_lt_one (D : IETDatum n) : ∑ i, D.v i < 1 := D.mem_region.2

/-- A datum from a point of the free region: the way data arise almost everywhere. -/
def ofMem (π : Equiv.Perm (Fin n)) {v : Fin (n - 1) → ℝ} (hv : v ∈ simplexRegion n) :
    IETDatum n :=
  ⟨π, v, hv⟩

/-- The length vector of the datum: the free coordinates, with `1 - ∑ v` as the last length. -/
noncomputable def lam (D : IETDatum n) : Fin n → ℝ≥0 := simplexMap n D.v

/-- The length vector is in the simplex. -/
theorem mem_simplex (D : IETDatum n) : D.lam ∈ simplex n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_one_add_one (NeZero.ne n)).symm⟩
  exact simplexMap_mem_simplex D.pos D.sum_lt_one

/-- **The exchange itself**, as a function. -/
noncomputable def toFun (D : IETDatum n) : ℝ → ℝ := mkIETFun D.lam D.π 0

/-- The exchange as an element of `IET 0 1`.  (This is derived data, not an input: everything below
takes the datum `D`, never an `IET 0 1`.) -/
noncomputable def toIET (D : IETDatum n) : IET 0 1 := mkIET1 D.lam D.π D.mem_simplex

theorem toIET_apply (D : IETDatum n) (x : ℝ) : D.toIET x = D.toFun x := rfl

/-- **An exchange maps `[0, 1)` into itself.** -/
theorem mapsTo (D : IETDatum n) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    D.toFun x ∈ Set.Ico (0 : ℝ) 1 :=
  D.toIET.isIET.mapsTo hx

/-- **An exchange is the identity outside `[0, 1)`.** -/
theorem eq_of_notMem (D : IETDatum n) {x : ℝ} (hx : x ∉ Set.Ico (0 : ℝ) 1) : D.toFun x = x :=
  D.toIET.isIET.eq_of_notMem hx

end IETDatum

/-! ### The combinatorial definitions of the paper

The singularities of `D` are the marked points `∑_{i<k} λ_i` (`k = 0, …, n`); the `k`-th one is
**splitting** when the cells on its left are mapped among themselves, `π {i | i < k} = {i | i < k}`.
This is a condition on the *permutation* `D.π` alone, which is why the definitions below take the
datum `D` and no extra parameter. -/

/-- **The `k`-th marked point of `D`** (the `k`-th singularity, in the paper's language): the total
length of the cells before `k`, i.e. `∑_{i<k} λᵢ`.  For `k = 0` this is `0`, for `k = n` it is
`1`. -/
noncomputable def IETDatum.mark {n : ℕ} [NeZero n] (D : IETDatum n) (k : Fin (n + 1)) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k.val), (D.lam i : ℝ)

/-- The first marked point is `0`. -/
@[simp] theorem IETDatum.mark_zero {n : ℕ} [NeZero n] (D : IETDatum n) : D.mark 0 = 0 := by
  simp only [IETDatum.mark, Fin.val_zero, Nat.not_lt_zero, Finset.filter_false, Finset.sum_empty]

/-- The `i`-th marked point is the left end of the `i`-th cell. -/
theorem IETDatum.mark_castSucc {n : ℕ} [NeZero n] (D : IETDatum n) (i : Fin n) :
    D.mark i.castSucc = leftEnd D.lam i := rfl

/-- The `(i+1)`-th marked point is the right end of the `i`-th cell. -/
theorem IETDatum.mark_succ {n : ℕ} [NeZero n] (D : IETDatum n) (i : Fin n) :
    D.mark i.succ = upperEnd D.lam i := by
  have hstep : D.mark i.succ = leftEnd D.lam i + (D.lam i : ℝ) := by
    simp only [IETDatum.mark, leftEnd, Fin.val_succ]
    rw [show Finset.univ.filter (fun j : Fin n => j.val < i.val + 1)
        = insert i (Finset.univ.filter (fun j : Fin n => j.val < i.val)) from by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      omega,
      Finset.sum_insert (by simp)]
    simp only [Fin.lt_def]
    ring
  rw [hstep, upperEnd_eq]

/-- The total length is `1`. -/
theorem IETDatum.sum_lam {n : ℕ} [NeZero n] (D : IETDatum n) : ∑ i, (D.lam i : ℝ) = 1 := by
  have h := D.mem_simplex
  simp only [simplex, Set.mem_ofPred_eq] at h
  rw [← NNReal.coe_sum, h]
  simp

/-- The marked points are monotone in the index. -/
theorem IETDatum.mark_mono {n : ℕ} [NeZero n] (D : IETDatum n) : Monotone D.mark := by
  intro a b hab
  simp only [IETDatum.mark]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      omega)
    (fun i _ _ => (D.lam i).coe_nonneg)

/-- The last marked point is `1`. -/
@[simp] theorem IETDatum.mark_last {n : ℕ} [NeZero n] (D : IETDatum n) :
    D.mark (Fin.last n) = 1 := by
  simp only [IETDatum.mark, Fin.val_last]
  rw [show Finset.univ.filter (fun i : Fin n => i.val < n) = Finset.univ from ?_]
  · have h := D.mem_simplex
    simp only [simplex, Set.mem_ofPred_eq] at h
    rw [← NNReal.coe_sum, h]
    simp
  · ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact i.isLt

/-- **The marked points lie in `[0, 1]`.** -/
theorem IETDatum.mark_mem_Icc {n : ℕ} [NeZero n] (D : IETDatum n) (k : Fin (n + 1)) :
    D.mark k ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · rw [← D.mark_zero]
    exact D.mark_mono (Fin.zero_le k)
  · rw [← D.mark_last]
    exact D.mark_mono (Fin.le_last k)

/-- **The `k`-th marked point of `D` is splitting**: `π {i | i < k} = {i | i < k}`, i.e. the cells
left of it are mapped among themselves.  For `k = 0` and `k = n` this is vacuous, which is the
paper's convention that `0` and `1` are splitting. -/
def IETDatum.IsSplitting {n : ℕ} [NeZero n] (D : IETDatum n) (k : Fin (n + 1)) : Prop :=
  ∀ i : Fin n, i.val < k.val ↔ (D.π i).val < k.val

/-- **A cell is fixed** when both of its ends are splitting singularities: then `D` is the identity
on it (the paper's "the `ℓ`-th interval is fixed if both the `ℓ-1`-th and the `ℓ`-th singularities
are splitting; then `g` acts as the identity on `J_ℓ`"). -/
def IETDatum.IsFixedCell {n : ℕ} [NeZero n] (D : IETDatum n) (l : Fin n) : Prop :=
  D.IsSplitting l.castSucc ∧ D.IsSplitting l.succ

/-- **A fixed cell is fixed**: on the `l`-th cell, `D` is the identity.  Both ends splitting force
`π l = l`, hence the displacement of `D` on that cell is `0`. -/
theorem IETDatum.isFixedCell_apply {n : ℕ} [NeZero n] (D : IETDatum n) {l : Fin n}
    (hl : D.IsFixedCell l) {x : ℝ}
    (hx : x ∈ Set.Ico (D.mark l.castSucc) (D.mark l.succ)) : D.toFun x = x := by
  -- both ends splitting force `π l = l`
  have hπl : D.π l = l := by
    have h1 := hl.2 l
    have h2 := hl.1 l
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
    have h3 : (D.π l).val < l.val + 1 := h1.mp (Nat.lt_succ_self _)
    have h4 : ¬ (D.π l).val < l.val := fun h => absurd (h2.mpr h) (lt_irrefl _)
    refine Fin.ext ?_
    omega
  -- hence the cells left of `l` are exactly the images left of `π l`
  have hset : (Finset.univ.filter (fun j : Fin n => D.π j < D.π l))
      = Finset.univ.filter (fun j : Fin n => j < l) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, hπl]
    exact (hl.1 j).symm
  -- so the displacement on the `l`-th cell vanishes
  have hzero : translationVector D.π D.lam l = 0 := by
    have h1 : imageLeft D.π D.lam l = leftEnd D.lam l := by
      rw [imageLeft, leftEnd, hset]
    rw [translationVector, h1]
    ring
  -- and the marked points are the cell ends of `D.lam`
  have hleft : D.mark l.castSucc = leftEnd D.lam l := rfl
  have hstep : D.mark l.succ = leftEnd D.lam l + (D.lam l : ℝ) := by
    simp only [IETDatum.mark, leftEnd, Fin.val_succ]
    rw [show Finset.univ.filter (fun i : Fin n => i.val < l.val + 1)
        = insert l (Finset.univ.filter (fun i : Fin n => i.val < l.val)) from by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      omega,
      Finset.sum_insert (by simp)]
    simp only [Fin.lt_def]
    ring
  have hupper : D.mark l.succ = upperEnd D.lam l := by
    rw [hstep, upperEnd_eq]
  have hx' : x ∈ Set.Ico (leftEnd D.lam l) (upperEnd D.lam l) := by
    rw [← hleft, ← hupper]; exact hx
  have hx0 : 0 ≤ x := le_trans (leftEnd_nonneg D.lam l) hx'.1
  have hxT : x < ∑ i, (D.lam i : ℝ) := lt_of_lt_of_le hx'.2 (upperEnd_le_total D.lam l)
  have hidx : idx D.lam (x - 0) (by simpa using hx0) = l :=
    idx_eq D.lam ⟨by simpa using hx0, by simpa using hxT⟩ (by simpa using hx'.1)
      (by simpa using hx'.2)
  rw [IETDatum.toFun, mkIETFun_of_mem D.lam D.π 0 ⟨hx0, by simpa using hxT⟩, hidx, hzero]
  ring

/-- The cells whose image starts at or before the image of the `i`-th cell are exactly the `i`-th
one and those before it, so their total length is `imageLeft + λ i`. -/
theorem imageLeft_add {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0) (i : Fin n) :
    imageLeft π lam i + (lam i : ℝ)
      = ∑ j ∈ Finset.univ.filter (fun j : Fin n => π j ≤ π i), (lam j : ℝ) := by
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
  rw [hins, Finset.sum_insert (by simp), imageLeft]
  ring

/-- **A splitting singularity leaves the left side invariant**: if the `k`-th marked point of `D` is
splitting, then every `y < mark k` is sent below `mark k`. -/
theorem IETDatum.isSplitting_below {n : ℕ} [NeZero n] (D : IETDatum n) {k : Fin (n + 1)}
    (hk : D.IsSplitting k) {y : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 1) (hyk : y < D.mark k) :
    D.toFun y < D.mark k := by
  -- the cell of `y` is one of those left of `k`
  set i := idx D.lam y hy.1 with hi
  have hyT : y < ∑ i, (D.lam i : ℝ) := by
    refine lt_of_lt_of_le hyk ?_
    rw [IETDatum.mark]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => (D.lam i).coe_nonneg)
  have hiy : y < upperEnd D.lam i :=
    lt_upperEnd_idx D.lam ⟨hy.1, hyT⟩
  have hle : leftEnd D.lam i ≤ y := idx_mem D.lam y hy.1
  -- `i < k`, since `y` lies below the `k`-th marked point
  have hik : i.val < k.val := by
    rcases Nat.eq_zero_or_pos k.val with h0 | h0
    · have hk0 : k = 0 := Fin.ext h0
      rw [hk0, IETDatum.mark_zero] at hyk
      linarith [hy.1]
    · by_contra hcon
      rw [not_lt] at hcon
      have hle : D.mark k ≤ leftEnd D.lam i := by
        refine le_trans (D.mark_mono (a := k) (b := i.castSucc) ?_) ?_
        · simp only [Fin.le_def, Fin.val_castSucc]; exact hcon
        · rfl
      linarith
  -- hence the image cell is also left of `k`
  have hπ : (D.π i).val < k.val := (hk i).mp hik
  -- so the whole image cell is below the `k`-th marked point
  have himg : imageLeft D.π D.lam i + (D.lam i : ℝ) ≤ D.mark k := by
    rw [imageLeft_add, IETDatum.mark]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => (D.lam j).coe_nonneg)
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact (hk j).mpr (lt_of_le_of_lt hj hπ)
  -- and the displacement sends the cell there
  have hidx : idx D.lam (y - 0) (by simpa using hy.1) = i := by
    refine idx_eq D.lam ⟨by simpa using hy.1, by simpa using hyT⟩ (by simpa using hle)
      (by simpa using hiy)
  rw [IETDatum.toFun, mkIETFun_of_mem D.lam D.π 0 ⟨hy.1, by simpa using hyT⟩, hidx,
    translationVector]
  have h1 : y < leftEnd D.lam i + (D.lam i : ℝ) := by rw [← upperEnd_eq]; exact hiy
  linarith

/-- **A splitting singularity leaves the right side invariant**: if the `k`-th marked point of `D`
is splitting, then every `y ≥ mark k` is sent above `mark k`. -/
theorem IETDatum.isSplitting_above {n : ℕ} [NeZero n] (D : IETDatum n) {k : Fin (n + 1)}
    (hk : D.IsSplitting k) {y : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 1) (hyk : D.mark k ≤ y) :
    D.mark k ≤ D.toFun y := by
  set i := idx D.lam y hy.1 with hi
  have hyT : y < ∑ i, (D.lam i : ℝ) := by
    rw [D.sum_lam]; exact hy.2
  have hiy : y < upperEnd D.lam i := lt_upperEnd_idx D.lam ⟨hy.1, hyT⟩
  have hle : leftEnd D.lam i ≤ y := idx_mem D.lam y hy.1
  -- the cell of `y` is not one of those left of `k`
  have hik : k.val ≤ i.val := by
    by_contra hcon
    rw [not_le] at hcon
    -- then `y` lies below the cell of `k`, hence below `mark k`
    have hlt : upperEnd D.lam i ≤ D.mark k := by
      rw [← D.mark_succ i]
      exact D.mark_mono (by simp only [Fin.le_def, Fin.val_succ]; exact hcon)
    linarith
  -- so its image cell is right of `mark k`
  have hπ : k.val ≤ (D.π i).val := by
    by_contra hcon
    rw [not_le] at hcon
    exact absurd ((hk i).mpr hcon) (by omega)
  have himg : D.mark k ≤ imageLeft D.π D.lam i := by
    have h1 : D.mark k = ∑ j ∈ Finset.univ.filter (fun j : Fin n => (D.π j).val < k.val),
        (D.lam j : ℝ) := by
      rw [IETDatum.mark]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hk j
    rw [h1, imageLeft]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => (D.lam j).coe_nonneg)
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    omega
  -- and `D.toFun y` is at least the left end of its image cell
  have hidx : idx D.lam (y - 0) (by simpa using hy.1) = i := by
    refine idx_eq D.lam ⟨by simpa using hy.1, by simpa using hyT⟩ (by simpa using hle)
      (by simpa using hiy)
  rw [IETDatum.toFun, mkIETFun_of_mem D.lam D.π 0 ⟨hy.1, by simpa using hyT⟩, hidx,
    translationVector]
  linarith

/-- **A splitting singularity of `D` lies in a fixed cell of `E`**: its marked point belongs to a
cell of `E` on which `E` is the identity (the paper's "belongs to a fixed interval for `g`").

The interval is **left-closed**, so this is `≤` and not `<` on the left: the paper's fixed interval
is `J_ℓ = [s_{ℓ-1}, s_ℓ)`, and a singularity sitting at its left end belongs to it.  This matters
for the case analysis of Lemma 3.2, where the point produced is a marked point *and* a cell boundary
(see `NOTES.md`); the invariance that `IsPairSplitting` is for holds either way, since
`E.IsFixedCell l` gives `E.IsSplitting l`. -/
def IETDatum.InFixedCell {d e : ℕ} [NeZero d] [NeZero e] (D : IETDatum d) (E : IETDatum e)
    (k : Fin (d + 1)) : Prop :=
  ∃ l : Fin e, E.IsFixedCell l ∧ E.mark l.castSucc ≤ D.mark k ∧ D.mark k < E.mark l.succ

/-- **The paper's derivation**: if the `k`-th marked point `x` of `D` is a splitting singularity and
lies strictly inside a cell of `E` on which `E` is the identity, then `x` is pair-splitting: both
`D` and `E` map `[0, x)` into itself and `[x, 1)` into itself. -/
theorem pairSplitting_invariant {d e : ℕ} [NeZero d] [NeZero e] (D : IETDatum d) (E : IETDatum e)
    {k : Fin (d + 1)} (hk : D.IsSplitting k) (hfix : D.InFixedCell E k) :
    (∀ y ∈ Set.Ico (0 : ℝ) 1, y < D.mark k → D.toFun y < D.mark k) ∧
      (∀ y ∈ Set.Ico (0 : ℝ) 1, D.mark k ≤ y → D.mark k ≤ D.toFun y) ∧
      (∀ y ∈ Set.Ico (0 : ℝ) 1, y < D.mark k → E.toFun y < D.mark k) ∧
        ∀ y ∈ Set.Ico (0 : ℝ) 1, D.mark k ≤ y → D.mark k ≤ E.toFun y := by
  obtain ⟨l, hl, hlow, hhigh⟩ := hfix
  refine ⟨fun y hy hyk => D.isSplitting_below hk hy hyk,
    fun y hy hyk => D.isSplitting_above hk hy hyk, ?_, ?_⟩
  · -- below: `y` is either left of the fixed cell, or inside it
    intro y hy hyk
    rcases lt_or_ge y (E.mark l.castSucc) with h | h
    · refine lt_of_lt_of_le (E.isSplitting_below hl.1 hy h) ?_
      linarith
    · have hyc : y ∈ Set.Ico (E.mark l.castSucc) (E.mark l.succ) :=
        ⟨h, lt_trans hyk hhigh⟩
      rw [E.isFixedCell_apply hl hyc]
      exact hyk
  · -- above: `y` is either right of the fixed cell, or inside it
    intro y hy hyk
    rcases lt_or_ge y (E.mark l.succ) with h | h
    · have hyc : y ∈ Set.Ico (E.mark l.castSucc) (E.mark l.succ) :=
        ⟨le_trans hlow hyk, h⟩
      rw [E.isFixedCell_apply hl hyc]
      exact hyk
    · exact le_trans (le_of_lt hhigh) (E.isSplitting_above hl.2 hy h)

/-- **The pair-splitting singularities of `(D, E)`**, as a predicate on points of `[0, 1)`: the
endpoints `0` and `1` by convention, and the splitting singularities of one of the two exchanges
which belong to a fixed interval of the other. -/
def IsPairSplitting {d e : ℕ} [NeZero d] [NeZero e] (D : IETDatum d) (E : IETDatum e)
    (x : ℝ) : Prop :=
  x = 0 ∨ x = 1 ∨
    (∃ k : Fin (d + 1), D.IsSplitting k ∧ D.mark k = x ∧ D.InFixedCell E k) ∨
      ∃ j : Fin (e + 1), E.IsSplitting j ∧ E.mark j = x ∧ E.InFixedCell D j

/-- **A pair-splitting point is invariant, two-sidedly, for both maps.** -/
theorem IsPairSplitting.invariant {d e : ℕ} [NeZero d] [NeZero e] {D : IETDatum d}
    {E : IETDatum e} {x : ℝ} (h : IsPairSplitting D E x) :
    (∀ y ∈ Set.Ico (0 : ℝ) 1, y < x → D.toFun y < x) ∧
      (∀ y ∈ Set.Ico (0 : ℝ) 1, x ≤ y → x ≤ D.toFun y) ∧
      (∀ y ∈ Set.Ico (0 : ℝ) 1, y < x → E.toFun y < x) ∧
        ∀ y ∈ Set.Ico (0 : ℝ) 1, x ≤ y → x ≤ E.toFun y := by
  rcases h with rfl | rfl | ⟨k, hk, rfl, hfix⟩ | ⟨j, hj, rfl, hfix⟩
  · -- `x = 0`: nothing lies below, and `0 ≤ y` is preserved since `[0,1)` is mapped into itself
    exact ⟨fun y hy hlt => absurd hlt (not_lt.mpr hy.1), fun y hy _ => (D.mapsTo hy).1,
      fun y hy hlt => absurd hlt (not_lt.mpr hy.1), fun y hy _ => (E.mapsTo hy).1⟩
  · -- `x = 1`: nothing lies above, and `y < 1` is preserved
    exact ⟨fun y hy _ => (D.mapsTo hy).2, fun y hy hle => absurd hle (by linarith [hy.2]),
      fun y hy _ => (E.mapsTo hy).2, fun y hy hle => absurd hle (by linarith [hy.2])⟩
  · exact pairSplitting_invariant D E hk hfix
  · obtain ⟨a, b, c, d⟩ := pairSplitting_invariant E D hj hfix
    exact ⟨c, d, a, b⟩

/-- **A pair-splitting point lies in `[0, 1]`.** -/
theorem IsPairSplitting.mem_Icc {d e : ℕ} [NeZero d] [NeZero e] {D : IETDatum d} {E : IETDatum e}
    {x : ℝ} (h : IsPairSplitting D E x) : x ∈ Set.Icc (0 : ℝ) 1 := by
  rcases h with rfl | rfl | ⟨k, _, rfl, _⟩ | ⟨j, _, rfl, _⟩
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩
  · exact D.mark_mem_Icc k
  · exact E.mark_mem_Icc j

/-- **A pair-splitting interval is mapped onto itself** by both maps: on `[0,1)`, `y` and `F y` are
on the same side of both ends. -/
theorem IsPairSplitting.iff_mem {d e : ℕ} [NeZero d] [NeZero e] {D : IETDatum d} {E : IETDatum e}
    {u v : ℝ} (hu : IsPairSplitting D E u) (hv : IsPairSplitting D E v) {y : ℝ}
    (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    (u ≤ y ∧ y < v ↔ u ≤ D.toFun y ∧ D.toFun y < v) ∧
      (u ≤ y ∧ y < v ↔ u ≤ E.toFun y ∧ E.toFun y < v) := by
  obtain ⟨hu1, hu2, hu3, hu4⟩ := hu.invariant
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv.invariant
  have hD : D.toFun y ∈ Set.Ico (0 : ℝ) 1 := D.mapsTo hy
  have hE : E.toFun y ∈ Set.Ico (0 : ℝ) 1 := E.mapsTo hy
  have key : ∀ {F : ℝ → ℝ} {x : ℝ}, (∀ z ∈ Set.Ico (0 : ℝ) 1, z < x → F z < x) →
      (∀ z ∈ Set.Ico (0 : ℝ) 1, x ≤ z → x ≤ F z) → (y < x ↔ F y < x) := by
    intro F x h1 h2
    refine ⟨fun h => h1 y hy h, fun h => ?_⟩
    by_contra hcon
    rw [not_lt] at hcon
    exact absurd (h2 y hy hcon) (by linarith)
  have key2 : ∀ {F : ℝ → ℝ} {x : ℝ}, (∀ z ∈ Set.Ico (0 : ℝ) 1, z < x → F z < x) →
      (∀ z ∈ Set.Ico (0 : ℝ) 1, x ≤ z → x ≤ F z) → (x ≤ y ↔ x ≤ F y) := by
    intro F x h1 h2
    refine ⟨fun h => h2 y hy h, fun h => ?_⟩
    by_contra hcon
    rw [not_le] at hcon
    exact absurd (h1 y hy hcon) (by linarith)
  constructor
  · constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(key2 hu1 hu2).mp h1, (key hv1 hv2).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(key2 hu1 hu2).mpr h1, (key hv1 hv2).mpr h2⟩
  · constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(key2 hu3 hu4).mp h1, (key hv3 hv4).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(key2 hu3 hu4).mpr h1, (key hv3 hv4).mpr h2⟩

/-- **The blocks of the pair `(D, E)`**: the successive pair-splitting singularities.  A block is
given by two consecutive pair-splitting points, so `IsBlock D E u v` says that `u` and `v` are
pair-splitting and that there is no pair-splitting point strictly between them.

Stated as a structure rather than as a conjunction so that the four pieces have names
(`left`, `right`, `lt`, `consecutive`) at the places where they are used. -/
structure IsBlock {d e : ℕ} [NeZero d] [NeZero e] (D : IETDatum d) (E : IETDatum e)
    (u v : ℝ) : Prop where
  /-- the left end is pair-splitting, so `[u, v)` is mapped into itself on the left -/
  left : IsPairSplitting D E u
  /-- the right end is pair-splitting -/
  right : IsPairSplitting D E v
  /-- the block is nonempty -/
  lt : u < v
  /-- no pair-splitting point lies strictly inside, so the block is minimal -/
  consecutive : ∀ w : ℝ, IsPairSplitting D E w → u < w → w < v → False

/-- **Lemma 3.3**: if `{i | ρ i < ρ a} = {i | i < b}` then `ρ a = b` and `ρ` preserves
`{i | i < b}`. -/
theorem perm_eq_of_preimage {n : ℕ} (ρ : Equiv.Perm (Fin n)) (a b : Fin n)
    (h : ∀ i : Fin n, (ρ i < ρ a) ↔ (i < b)) :
    ρ a = b ∧ ∀ i : Fin n, (ρ i < b ↔ i < b) := by
  -- `ρ` maps the initial segment below `a` in the source order onto the initial segment below
  -- `ρ a` in the target order; comparing cardinalities identifies `b` with `ρ a`.
  have hcard : b.val = (ρ a).val := by
    have hS : (Finset.univ.filter (fun i : Fin n => i < b))
        = (Finset.univ.filter (fun i : Fin n => ρ i < ρ a)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (h i).symm
    have h1 : (Finset.univ.filter (fun i : Fin n => i < b)).card = b.val := by
      rw [← Fin.card_Iio b]
      congr 1
      ext i
      simp
    have h2 : (Finset.univ.filter (fun i : Fin n => ρ i < ρ a)).card = (ρ a).val := by
      have himg : (Finset.univ.filter (fun i : Fin n => ρ i < ρ a)).image ρ = Finset.Iio (ρ a) := by
        ext j
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
        constructor
        · rintro ⟨i, hi, rfl⟩
          exact hi
        · intro hj
          exact ⟨ρ.symm j, by simpa using hj, by simp⟩
      calc (Finset.univ.filter (fun i : Fin n => ρ i < ρ a)).card
          = ((Finset.univ.filter (fun i : Fin n => ρ i < ρ a)).image ρ).card :=
            (Finset.card_image_of_injective _ ρ.injective).symm
        _ = (Finset.Iio (ρ a)).card := by rw [himg]
        _ = (ρ a).val := Fin.card_Iio (ρ a)
    rw [← h1, hS, h2]
  have hba : ρ a = b := Fin.ext hcard.symm
  subst hba
  exact ⟨rfl, fun i => h i⟩

/-! ## 1. The open set `O` (the paper's "connected component of the complement of the hyperplanes")

The paper fixes the finitely many expressions `k + ∑ aᵢ λᵢ + ∑ bⱼ μⱼ` whose integer coefficients are
bounded by `4`, and discards the hyperplanes where one vanishes.  `O` is a connected component of
the complement.

The bound is `4` and not `2`, which is a decision taken with the user.  `2` is enough for Case 1a of
the case analysis of Lemma 3.2 (its relations have coefficients in `{-1,0,1}`, and trivialising a
relation with coefficients `≤ 1` needs the bound on *free* coefficients, which are differences
`aᵢ - a_last`, so `2`).  It is **not** enough for Case 1b, whose relation has coefficients up to `2`
(`λ_i` gets `[π i < π k] + [π i < π m] - [i < m]`): a full-coordinate relation with coefficients
`≤ 2` has free coefficients `≤ 4`, so its trivialisation needs the bound `4` — the paper's choice.
See `NOTES.md`, "the bound `2` problem". -/

/-- **The real parameter space**: the `d - 1` free coordinates of `λ` and the `e - 1` free
coordinates of `μ`, as real vectors.  This is the space of `d + e - 2` degrees of freedom on which
the Lebesgue measure of Lemma 3.1 lives, and it is the space `simplexVolume` is built from
(`simplexRegion d ⊆ (Fin (d-1) → ℝ)`); it is *not* `(Fin d → ℝ) × (Fin e → ℝ)`, whose extra
coordinate `λ_last = 1 - ∑` is determined. -/
abbrev PReal (d e : ℕ) := (Fin (d - 1) → ℝ) × (Fin (e - 1) → ℝ)

/-- **A singularity of `g ∘ f`, as a function of the free parameters**: an affine function, in
Mathlib's sense (`AffineMap`), of `PReal d e`.  This is the type of the singularity list `s` of a
presentation on a region, and stating affinity this way makes it a *global* affine-map condition
rather than a check on each coordinate: the whole vector `s · q` is an affine image of `q`. -/
abbrev ParamAffine (d e : ℕ) := PReal d e →ᵃ[ℝ] ℝ

/-- **A small nontrivial integer relation vanishing at `q`**: the coefficient data `(k, a, b)` of
`IsBadParam`, with its five conditions named rather than conjoined. -/
structure IsSmallRelation {d e : ℕ} (q : PReal d e) (k : ℤ) (a : Fin (d - 1) → ℤ)
    (b : Fin (e - 1) → ℤ) : Prop where
  /-- the coefficient of each free `λᵢ` is bounded by `4` -/
  a_bound : ∀ i, |a i| ≤ 4
  /-- the coefficient of each free `μⱼ` is bounded by `4` -/
  b_bound : ∀ j, |b j| ≤ 4
  /-- the constant term is bounded by `4` -/
  k_bound : |k| ≤ 4
  /-- the relation is nontrivial -/
  nontrivial : k ≠ 0 ∨ (∃ i, a i ≠ 0) ∨ ∃ j, b j ≠ 0
  /-- the relation vanishes at `q` -/
  vanishes : (k : ℝ) + (∑ i, (a i : ℝ) * q.1 i) + (∑ j, (b j : ℝ) * q.2 j) = 0

/-- **A bad parameter pair**: a nontrivial relation `k + ∑ aᵢ λᵢ + ∑ bⱼ μⱼ = 0` between the *free*
coordinates `λ₁, …, λ_{d-1}`, `μ₁, …, μ_{e-1}`, with all coefficients bounded by `4` in absolute
value.  The five conditions on the coefficients are the named fields of `IsSmallRelation`.

It is stated on `PReal d e`, the space of the `d + e - 2` free coordinates, and not on the length
vectors themselves: the coordinates must be the free ones, since with all `d + e` lengths the
relation `-1 + ∑ᵢ λᵢ = 0` holds on the whole simplex and would make every parameter pair bad.  This
is the paper's own convention — it ranges `i` over `1, …, d-1` and `j` over `1, …, e-1`. -/
def IsBadParam {d e : ℕ} (q : PReal d e) : Prop :=
  ∃ (k : ℤ) (a : Fin (d - 1) → ℤ) (b : Fin (e - 1) → ℤ), IsSmallRelation q k a b

/-- **`O`**: the points of the free-coordinate space on which no small nontrivial integer relation
holds. -/
def goodParams (d e : ℕ) : Set (PReal d e) := {q | ¬ IsBadParam q}

/-! ### Passing from a parameter pair to its free coordinates

The two length vectors live in `(Fin d → ℝ≥0) × (Fin e → ℝ≥0)`, which is where `simplexVolume` and
hence Masur–Veech and Veech's rigidity are stated, but which is not a real vector space: there is no
subtraction, no `Convex`, no `convex_ball`, no `LinearMap` and no Haar measure.  The `d + e - 2`
degrees of freedom are the free coordinates, a point of `PReal`, and `toReal` is the projection to
them. -/

/-- The **free coordinates** of a parameter pair, as a point of `PReal`. -/
def toReal {d e : ℕ} (p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0)) : PReal d e :=
  ((fun i => (p.1 (Fin.castLE (Nat.sub_le d 1) i) : ℝ)),
    (fun j => (p.2 (Fin.castLE (Nat.sub_le e 1) j) : ℝ)))

theorem continuous_toReal {d e : ℕ} : Continuous (toReal (d := d) (e := e)) := by
  unfold toReal
  fun_prop

/-! ### The finite enumeration of the coefficient data

`coeffs_eq_of_good` and the openness of `O` both rest on the same fact: there are only finitely many
coefficient vectors, so "no small relation vanishes" is a *finite* condition.  The coefficients are
indexed by `(Fin d ⊕ Fin e) ⊕ Fin 1`: the `aᵢ`, the `bⱼ` and the constant term. -/

/-- A coefficient index: the `aᵢ`, the `bⱼ` and the constant term. -/
abbrev CoeffIndex (d e : ℕ) := (Fin (d - 1) ⊕ Fin (e - 1)) ⊕ Fin 1

/-- A full set of coefficients: the `aᵢ`, the `bⱼ` and the constant `k`. -/
abbrev CoeffData (d e : ℕ) := CoeffIndex d e → ℤ

/-- The constant term of a coefficient vector. -/
def constCoeff {d e : ℕ} (t : CoeffData d e) : ℤ := t (Sum.inr 0)

/-- The value of the relation with coefficient vector `t` at `q`. -/
def relReal {d e : ℕ} (t : CoeffData d e) (q : PReal d e) : ℝ :=
  (constCoeff t : ℝ) + (∑ i, (t (Sum.inl (Sum.inl i)) : ℝ) * q.1 i)
    + ∑ j, (t (Sum.inl (Sum.inr j)) : ℝ) * q.2 j

/-- The coefficients are not all zero. -/
def NontrivialCoeff {d e : ℕ} (t : CoeffData d e) : Prop :=
  constCoeff t ≠ 0 ∨ (∃ i, t (Sum.inl (Sum.inl i)) ≠ 0) ∨ ∃ j, t (Sum.inl (Sum.inr j)) ≠ 0

/-- The coefficient vector with prescribed components. -/
def ofCoeffs {d e : ℕ} (k : ℤ) (a : Fin (d - 1) → ℤ) (b : Fin (e - 1) → ℤ) : CoeffData d e :=
  fun ix => match ix with
    | Sum.inl (Sum.inl i) => a i
    | Sum.inl (Sum.inr j) => b j
    | Sum.inr _ => k

theorem relReal_ofCoeffs {d e : ℕ} (k : ℤ) (a : Fin (d - 1) → ℤ) (b : Fin (e - 1) → ℤ)
    (q : PReal d e) :
    relReal (ofCoeffs k a b) q
      = (k : ℝ) + (∑ i, (a i : ℝ) * q.1 i) + ∑ j, (b j : ℝ) * q.2 j := by
  simp [relReal, constCoeff, ofCoeffs]

/-- The finitely many coefficient vectors with all coefficients of absolute value at most `4`. -/
noncomputable def smallCoeffs (d e : ℕ) : Finset (CoeffData d e) :=
  Fintype.piFinset fun _ => Finset.Icc (-4 : ℤ) 4

theorem mem_smallCoeffs {d e : ℕ} {t : CoeffData d e} :
    t ∈ smallCoeffs d e ↔ ∀ ix, |t ix| ≤ 4 := by
  simp only [smallCoeffs, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

theorem isBadParam_iff {d e : ℕ} {q : PReal d e} :
    IsBadParam q ↔ ∃ t ∈ smallCoeffs d e, NontrivialCoeff t ∧ relReal t q = 0 := by
  constructor
  · rintro ⟨k, a, b, ha, hb, hk, hnt, hrel⟩
    refine ⟨ofCoeffs k a b, ?_, ?_, ?_⟩
    · rw [mem_smallCoeffs]
      rintro (⟨i | j⟩ | u)
      · exact ha i
      · exact hb j
      · exact hk
    · simpa [NontrivialCoeff, constCoeff, ofCoeffs] using hnt
    · rw [relReal_ofCoeffs]
      exact hrel
  · rintro ⟨t, ht, hnt, hrel⟩
    rw [mem_smallCoeffs] at ht
    refine ⟨constCoeff t, fun i => t (Sum.inl (Sum.inl i)), fun j => t (Sum.inl (Sum.inr j)),
      fun i => ht (Sum.inl (Sum.inl i)), fun j => ht (Sum.inl (Sum.inr j)), ?_, hnt, ?_⟩
    · exact ht (Sum.inr 0)
    · simpa [relReal] using hrel

theorem continuous_relReal {d e : ℕ} (t : CoeffData d e) : Continuous (relReal t) := by
  unfold relReal constCoeff
  fun_prop

/-- The bad set is a finite union of hyperplanes, hence closed. -/
theorem isClosed_badParam (d e : ℕ) : IsClosed {q : PReal d e | IsBadParam q} := by
  classical
  have hset : {q : PReal d e | IsBadParam q}
      = ⋃ t ∈ (smallCoeffs d e).filter NontrivialCoeff, {q : PReal d e | relReal t q = 0} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, exists_prop]
    rw [isBadParam_iff]
    constructor
    · rintro ⟨t, ht, hnt, hrel⟩
      exact ⟨t, ⟨ht, hnt⟩, hrel⟩
    · rintro ⟨t, ⟨ht, hnt⟩, hrel⟩
      exact ⟨t, ht, hnt, hrel⟩
  rw [hset]
  refine (Finset.finite_toSet ((smallCoeffs d e).filter NontrivialCoeff)).isClosed_biUnion ?_
  intro t _
  exact isClosed_eq (continuous_relReal t) continuous_const

/-- **`O` is open** in the free-coordinate space: it is the complement of a finite union of closed
hyperplanes. -/
theorem isOpen_goodParams (d e : ℕ) : IsOpen (goodParams d e) :=
  (isClosed_badParam d e).isOpen_compl

/-- The value of `simplexMap` at a *free* coordinate is that coordinate. -/
theorem simplexMap_castLE {d : ℕ} [NeZero d] {v : Fin (d - 1) → ℝ} (i : Fin (d - 1)) :
    simplexMap d v (Fin.castLE (Nat.sub_le d 1) i) = (v i).toNNReal := by
  have hlt : (Fin.castLE (Nat.sub_le d 1) i).val + 1 ≠ d := by
    rw [Fin.val_castLE]
    have h1 := i.isLt
    have h2 := NeZero.pos d
    omega
  simp only [simplexMap, dif_neg hlt]
  congr 1

/-- **`toReal` is the inverse of `simplexMap` on the free region**: at a point with positive
coordinates, taking the free coordinates of the length vector gives the point back. -/
theorem toReal_simplexMap {d e : ℕ} [NeZero d] [NeZero e] {v : Fin (d - 1) → ℝ}
    {w : Fin (e - 1) → ℝ} (hv : ∀ i, 0 < v i) (hw : ∀ j, 0 < w j) :
    toReal (simplexMap d v, simplexMap e w) = (v, w) := by
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp only [toReal, simplexMap_castLE, Real.coe_toNNReal _ (le_of_lt (hv i))]
  · simp only [toReal, simplexMap_castLE, Real.coe_toNNReal _ (le_of_lt (hw j))]

/-- A bad pair at the point of the simplex given by the free coordinates `z` puts `z` in the tube of
the corresponding integer form. -/
theorem isBadParam_mem_badSet {d e N : ℕ} [NeZero d] [NeZero e]
    {z : (Fin (d - 1) → ℝ) × (Fin (e - 1) → ℝ)}
    (hz : z ∈ ubox (d - 1) ×ˢ ubox (e - 1)) (hN : 4 ≤ N)
    (hbad : IsBadParam (toReal (simplexMap d z.1, simplexMap e z.2))) :
    z ∈ badSet (d - 1) (e - 1) N := by
  have hposv : ∀ i, 0 < z.1 i := fun i => (Set.mem_pi.mp hz.1 i (Set.mem_univ i)).1
  have hposw : ∀ j, 0 < z.2 j := fun j => (Set.mem_pi.mp hz.2 j (Set.mem_univ j)).1
  rw [toReal_simplexMap hposv hposw] at hbad
  obtain ⟨k, a, b, ha, hb, hk, hnt, hrel⟩ := hbad
  -- after `toReal_simplexMap` the relation is already in the free coordinates
  have hrel' : (∑ i, (a i : ℝ) * z.1 i) + (∑ j, (b j : ℝ) * z.2 j) + (k : ℝ) = 0 := by
    linarith
  -- the coefficients are in the box at scale `N`
  have hbox : (a, (b, k)) ∈ formBox (d - 1) (e - 1) N := by
    rw [mem_formBox]
    refine ⟨fun i => ?_, fun j => ?_, ?_⟩
    · have := ha i
      omega
    · have := hb j
      omega
    · have := hk
      omega
  -- and `a` and `b` are not both zero
  have hnt' : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨ha0, hb0⟩ := hcon
    rcases hnt with h | ⟨i, hi⟩ | ⟨j, hj⟩
    · apply h
      have h1 := hrel'
      rw [ha0, hb0] at h1
      simp only [Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, zero_add] at h1
      exact_mod_cast h1
    · exact hi (by rw [ha0]; rfl)
    · exact hj (by rw [hb0]; rfl)
  refine Set.mem_biUnion (Finset.mem_filter.mpr ⟨hbox, hnt'⟩) ?_
  refine ⟨hz, ?_⟩
  have hε : (0 : ℝ) < ((N : ℝ) + 1) ^ (-(expo (d - 1) (e - 1) : ℝ)) := by positivity
  simp only [Set.mem_ofPred_eq]
  rw [show (∑ i, (a i : ℝ) * z.1 i) + (∑ j, (b j : ℝ) * z.2 j) + (k : ℝ) = 0 from hrel']
  simpa using hε

/-- **Almost every point of the product of the two free regions lies in their product.** -/
theorem ae_mem_simplexRegion_prod {d e : ℕ} :
    ∀ᵐ z ∂((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))),
      z.1 ∈ simplexRegion d ∧ z.2 ∈ simplexRegion e := by
  have h1 : ((volume.restrict (simplexRegion d)).prod
      (volume.restrict (simplexRegion e)))
      {z : (Fin (d - 1) → ℝ) × (Fin (e - 1) → ℝ) | z.1 ∉ simplexRegion d} = 0 := by
    have hset : {z : (Fin (d - 1) → ℝ) × (Fin (e - 1) → ℝ) | z.1 ∉ simplexRegion d}
        = (simplexRegion d)ᶜ ×ˢ (Set.univ : Set (Fin (e - 1) → ℝ)) := by
      ext z
      simp
    rw [hset, Measure.prod_prod,
      Measure.restrict_apply (measurableSet_simplexRegion d).compl, Set.compl_inter_self,
      measure_empty, zero_mul]
  have h2 : ((volume.restrict (simplexRegion d)).prod
      (volume.restrict (simplexRegion e)))
      {z : (Fin (d - 1) → ℝ) × (Fin (e - 1) → ℝ) | z.2 ∉ simplexRegion e} = 0 := by
    have hset : {z : (Fin (d - 1) → ℝ) × (Fin (e - 1) → ℝ) | z.2 ∉ simplexRegion e}
        = (Set.univ : Set (Fin (d - 1) → ℝ)) ×ˢ (simplexRegion e)ᶜ := by
      ext z
      simp
    rw [hset, Measure.prod_prod,
      Measure.restrict_apply (measurableSet_simplexRegion e).compl, Set.compl_inter_self,
      measure_empty, mul_zero]
  filter_upwards [MeasureTheory.ae_iff.mpr h1, MeasureTheory.ae_iff.mpr h2] with z hz1 hz2
  exact ⟨hz1, hz2⟩

/-- **Almost every point of the free region is good**: the free-coordinate form of `ae_goodParams`.
This is the form Section 3 uses, since every region `O` there is a set of free parameters. -/
theorem ae_goodParams_real {d e : ℕ} [NeZero d] [NeZero e] :
    ∀ᵐ z ∂((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))),
      ¬ IsBadParam z := by
  filter_upwards [ae_eventually_notMem_badSet (simplexRegion d) (simplexRegion e),
    ae_mem_simplexRegion_prod (d := d) (e := e)] with z hz hmemz
  obtain ⟨N₀, hzN⟩ := Filter.eventually_atTop.mp hz
  intro hbad
  have hbad' : IsBadParam (toReal (simplexMap d z.1, simplexMap e z.2)) := by
    rwa [toReal_simplexMap hmemz.1.1 hmemz.2.1]
  exact hzN (max N₀ 4) (le_max_left _ _)
    (isBadParam_mem_badSet ⟨simplexRegion_subset_ubox d hmemz.1,
      simplexRegion_subset_ubox e hmemz.2⟩ (le_max_right _ _) hbad')

/-- **Except on finitely many hyperplanes of zero measure**, no small nontrivial integer relation
holds.  Note the ambient measure: there is no `volume` on `Fin d → ℝ≥0` in this Mathlib, so the
statement is made for the project's `simplexVolume`, which is the measure `MasurVeech` and
`VeechRigidity` use.

The proof is the one of Proposition 2.5 in `Diophantine.lean`: `simplexVolume d` is the pushforward
of Lebesgue measure on the free coordinates `simplexRegion d ⊆ (Fin (d - 1) → ℝ)` under
`simplexMap d`, so `(simplexVolume d).prod (simplexVolume e)` is the pushforward under
`simplexMap d × simplexMap e`
(`Measure.map_prod_map`); a bad relation becomes the integer form
`k + ∑ aᵢ z.1 i + ∑ bⱼ z.2 j` in the free coordinates, and `ae_eventually_notMem_badSet` says that
almost every free point is outside the tube of every such form. -/
theorem ae_goodParams (d e : ℕ) [NeZero d] [NeZero e] :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)), ¬ IsBadParam (toReal p) := by
  classical
  set ν : Measure ((Fin (d - 1) → ℝ) × (Fin (e - 1) → ℝ)) :=
    ((volume : Measure (Fin (d - 1) → ℝ)).restrict (simplexRegion d)).prod
      (volume.restrict (simplexRegion e)) with hν
  -- the parameter measure is the pushforward of Lebesgue measure in the free coordinates
  have hmap : (simplexVolume d).prod (simplexVolume e)
      = ν.map (Prod.map (simplexMap d) (simplexMap e)) := by
    rw [hν, simplexVolume, simplexVolume, MeasureTheory.Measure.map_prod_map _ _
      (measurable_simplexMap d) (measurable_simplexMap e)]
  have hset : MeasurableSet {p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0) | ¬ IsBadParam (toReal p)} :=
    (isOpen_goodParams d e).measurableSet.preimage continuous_toReal.measurable
  rw [hmap, MeasureTheory.ae_map_iff ((measurable_simplexMap d).prodMap
    (measurable_simplexMap e)).aemeasurable hset]
  -- the free coordinates are in the simplex region
  have hmem : ∀ᵐ z ∂ν, z.1 ∈ simplexRegion d ∧ z.2 ∈ simplexRegion e := by
    rw [hν]
    exact ae_mem_simplexRegion_prod
  filter_upwards [ae_goodParams_real (d := d) (e := e), hmem] with z hz hmemz
  have hz' : ¬ IsBadParam (toReal (simplexMap d z.1, simplexMap e z.2)) := by
    rwa [toReal_simplexMap hmemz.1.1 hmemz.2.1]
  exact hz'

/-- **The only way `O` is consumed**: two relations with coefficients bounded by `1` that agree on a
good pair are the same relation.  (`2 = 1 + 1 ≤ 4`: the difference of the two relations is a small
relation.) -/
theorem coeffs_eq_of_good {d e : ℕ} {q : PReal d e} (hp : ¬ IsBadParam q)
    {a a' : Fin (d - 1) → ℤ} {b b' : Fin (e - 1) → ℤ}
    (ha : ∀ i, |a i| ≤ 1) (ha' : ∀ i, |a' i| ≤ 1)
    (hb : ∀ j, |b j| ≤ 1) (hb' : ∀ j, |b' j| ≤ 1)
    (h : (∑ i, (a i : ℝ) * q.1 i) + (∑ j, (b j : ℝ) * q.2 j)
      = (∑ i, (a' i : ℝ) * q.1 i) + (∑ j, (b' j : ℝ) * q.2 j)) :
    a = a' ∧ b = b' := by
  by_contra hne
  apply hp
  have hda : ∀ i, |(a - a') i| ≤ 4 := by
    intro i
    have h1 := abs_le.mp (ha i)
    have h2 := abs_le.mp (ha' i)
    simp only [Pi.sub_apply]
    rw [abs_le]
    constructor <;> omega
  have hdb : ∀ j, |(b - b') j| ≤ 4 := by
    intro j
    have h1 := abs_le.mp (hb j)
    have h2 := abs_le.mp (hb' j)
    simp only [Pi.sub_apply]
    rw [abs_le]
    constructor <;> omega
  refine ⟨0, a - a', b - b', hda, hdb, by norm_num, ?_, ?_⟩
  · rcases not_and_or.mp hne with hne | hne
    · right; left
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      exact ⟨i, by simpa only [Pi.sub_apply] using sub_ne_zero.mpr hi⟩
    · right; right
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      exact ⟨j, by simpa only [Pi.sub_apply] using sub_ne_zero.mpr hj⟩
  · have h1 : (∑ i, ((a - a') i : ℝ) * q.1 i)
        = (∑ i, (a i : ℝ) * q.1 i)
          - ∑ i, (a' i : ℝ) * q.1 i := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.sub_apply, Int.cast_sub]
      ring
    have h2 : (∑ j, ((b - b') j : ℝ) * q.2 j)
        = (∑ j, (b j : ℝ) * q.2 j)
          - ∑ j, (b' j : ℝ) * q.2 j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.sub_apply, Int.cast_sub]
      ring
    rw [h1, h2]
    push_cast
    linarith

/-- **The vanishing form**, which is the one the case analysis of Lemma 3.2 uses when a relation is
collected into a single equation before being compared with another: a relation with coefficients
bounded by `4` that vanishes on a good pair is trivial. -/
theorem coeffs_zero_of_good {d e : ℕ} {q : PReal d e} (hp : ¬ IsBadParam q)
    {a : Fin (d - 1) → ℤ} {b : Fin (e - 1) → ℤ} (ha : ∀ i, |a i| ≤ 4) (hb : ∀ j, |b j| ≤ 4)
    (h : (∑ i, (a i : ℝ) * q.1 i) + (∑ j, (b j : ℝ) * q.2 j) = 0) :
    a = 0 ∧ b = 0 := by
  by_contra hne
  apply hp
  refine ⟨0, a, b, ha, hb, by norm_num, ?_, ?_⟩
  · rcases not_and_or.mp hne with h | h
    · right; left
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      exact ⟨i, by simpa using hi⟩
    · right; right
      obtain ⟨j, hj⟩ := Function.ne_iff.mp h
      exact ⟨j, by simpa using hj⟩
  · simpa using h

/-- The last index of `Fin n`: the length determined by `∑ λ = 1`. -/
def lastIdx (n : ℕ) [NeZero n] : Fin n := ⟨n - 1, by have := NeZero.pos n; omega⟩

theorem lastIdx_eq_last {m : ℕ} : lastIdx (m + 1) = Fin.last m := Fin.ext rfl

/-- **A sum over all the lengths, split into the last coordinate and the free ones.** -/
theorem sum_eq_last_add_free {m : ℕ} (lam : Fin (m + 1) → ℝ≥0) (hl : (∑ i, lam i) = 1)
    (a : Fin (m + 1) → ℝ) :
    (∑ i, a i * (lam i : ℝ))
      = a (Fin.last m)
        + ∑ i : Fin m, (a i.castSucc - a (Fin.last m)) * (lam i.castSucc : ℝ) := by
  have hcoe : (∑ i, (lam i : ℝ)) = 1 := by
    rw [← NNReal.coe_sum, hl]
    simp
  have hsplit : (∑ i, (lam i : ℝ))
      = (lam (Fin.last m) : ℝ) + ∑ i : Fin m, (lam i.castSucc : ℝ) := by
    rw [Fin.sum_univ_castSucc]
    ring
  have hlast : (lam (Fin.last m) : ℝ) = 1 - ∑ i : Fin m, (lam i.castSucc : ℝ) := by
    linarith
  have h1 : (∑ i : Fin (m + 1), a i * (lam i : ℝ))
      = a (Fin.last m) * (lam (Fin.last m) : ℝ)
        + ∑ i : Fin m, a i.castSucc * (lam i.castSucc : ℝ) := by
    rw [Fin.sum_univ_castSucc]
    ring
  have h2 : (∑ i : Fin m, (a i.castSucc - a (Fin.last m)) * (lam i.castSucc : ℝ))
      = (∑ i : Fin m, a i.castSucc * (lam i.castSucc : ℝ))
        - a (Fin.last m) * ∑ i : Fin m, (lam i.castSucc : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2, hlast]
  ring

/-- **The vanishing form with the constant term**: a relation between the *free* coordinates with
coefficients bounded by `4` — constant term included — that vanishes at a good pair is trivial. -/
theorem coeffs_zero_of_good_with_const {d e : ℕ} {q : PReal d e} (hp : ¬ IsBadParam q)
    {k : ℤ} {a : Fin (d - 1) → ℤ} {b : Fin (e - 1) → ℤ} (ha : ∀ i, |a i| ≤ 4)
    (hb : ∀ j, |b j| ≤ 4) (hk : |k| ≤ 4)
    (h : (k : ℝ) + (∑ i, (a i : ℝ) * q.1 i) + (∑ j, (b j : ℝ) * q.2 j) = 0) :
    k = 0 ∧ a = 0 ∧ b = 0 := by
  by_contra hne
  apply hp
  have hnt : k ≠ 0 ∨ (∃ i, a i ≠ 0) ∨ ∃ j, b j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne ⟨hcon.1, funext hcon.2.1, funext hcon.2.2⟩
  exact ⟨k, a, b, ha, hb, hk, hnt, h⟩

/-- **`O` in full coordinates**: at a good pair, a homogeneous relation among *all* the lengths with
coefficients bounded by `2` in absolute value forces the coefficients to be constant, with the two
constants cancelling.

This is the mechanism of the case analysis of Lemma 3.2 (and of the injectivity of `ν` in Lemma
3.1): the relations produced there equate a sum of some `λ`'s and `μ`'s with another such sum, and
the conclusion "each coefficient is `0`" is this lemma applied to the difference.  The bound `2` is
what Case 1b of Lemma 3.2 needs (its `λ`-coefficients are `[π i < π k] + [π i < π m] - [i < m]`);
Case 1a only uses coefficients in `{-1,0,1}`. -/
theorem relation_of_good {d e : ℕ} [NeZero d] [NeZero e] {p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0)}
    (hp : ¬ IsBadParam (toReal p)) {a : Fin d → ℤ} {b : Fin e → ℤ}
    (ha : ∀ i, |a i| ≤ 2) (hb : ∀ j, |b j| ≤ 2)
    (hl : p.1 ∈ simplex d) (hm : p.2 ∈ simplex e)
    (h : (∑ i, (a i : ℝ) * (p.1 i : ℝ)) + (∑ j, (b j : ℝ) * (p.2 j : ℝ)) = 0) :
    (∀ i, a i = a (lastIdx d)) ∧ (∀ j, b j = b (lastIdx e)) ∧
      a (lastIdx d) + b (lastIdx e) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by have := NeZero.pos d; omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by have := NeZero.pos e; omega⟩
  rw [lastIdx_eq_last, lastIdx_eq_last]
  have hlam : (∑ i : Fin (m + 1), (p.1 i : ℝ)) = 1 := by
    rw [← NNReal.coe_sum]; exact_mod_cast hl
  have hmu : (∑ j : Fin (n + 1), (p.2 j : ℝ)) = 1 := by
    rw [← NNReal.coe_sum]; exact_mod_cast hm
  have h1 := sum_eq_last_add_free p.1 hl (fun i => (a i : ℝ))
  have h2 := sum_eq_last_add_free p.2 hm (fun j => (b j : ℝ))
  -- the relation, in the free coordinates
  have e1 : (∑ i : Fin m, (((a i.castSucc - a (Fin.last m)) : ℤ) : ℝ) * (p.1 i.castSucc : ℝ))
      = (∑ i, (a i : ℝ) * (p.1 i : ℝ)) - (a (Fin.last m) : ℝ) := by
    rw [h1]
    push_cast
    ring
  have e2 : (∑ j : Fin n, (((b j.castSucc - b (Fin.last n)) : ℤ) : ℝ) * (p.2 j.castSucc : ℝ))
      = (∑ j, (b j : ℝ) * (p.2 j : ℝ)) - (b (Fin.last n) : ℝ) := by
    rw [h2]
    push_cast
    ring
  have hrel : ((a (Fin.last m) + b (Fin.last n) : ℤ) : ℝ)
      + (∑ i : Fin m, (((a i.castSucc - a (Fin.last m)) : ℤ) : ℝ) * (p.1 i.castSucc : ℝ))
      + (∑ j : Fin n, (((b j.castSucc - b (Fin.last n)) : ℤ) : ℝ) * (p.2 j.castSucc : ℝ)) = 0 := by
    rw [e1, e2]
    push_cast
    linarith
  -- the free coefficients are bounded by `4` (`2 + 2` from the hypothesis)
  have hda : ∀ i : Fin m, |(a i.castSucc - a (Fin.last m) : ℤ)| ≤ 4 := by
    intro i
    have h1 := abs_le.mp (ha i.castSucc)
    have h2 := abs_le.mp (ha (Fin.last m))
    rw [abs_le]
    omega
  have hdb : ∀ j : Fin n, |(b j.castSucc - b (Fin.last n) : ℤ)| ≤ 4 := by
    intro j
    have h1 := abs_le.mp (hb j.castSucc)
    have h2 := abs_le.mp (hb (Fin.last n))
    rw [abs_le]
    omega
  have hk : |a (Fin.last m) + b (Fin.last n)| ≤ 4 := by
    have h1 := abs_le.mp (ha (Fin.last m))
    have h2 := abs_le.mp (hb (Fin.last n))
    rw [abs_le]
    omega
  obtain ⟨hk0, ha0, hb0⟩ := coeffs_zero_of_good_with_const (d := m + 1) (e := n + 1) hp
    (k := a (Fin.last m) + b (Fin.last n))
    (a := fun i => a i.castSucc - a (Fin.last m)) (b := fun j => b j.castSucc - b (Fin.last n))
    hda hdb hk hrel
  refine ⟨?_, ?_, hk0⟩
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have := congrFun ha0 j
      simp only [Pi.zero_apply] at this
      omega
    · rfl
  · intro j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · have := congrFun hb0 k
      simp only [Pi.zero_apply] at this
      omega
    · rfl

/-! ## 1'. The covering step: a measure is determined by what it gives near each point

`ae_goodParams` says that a.e. parameter pair is good, and `ae_exists_goodRegion` that a.e. pair has
a good neighbourhood.  The step from the second to "the set where anything goes wrong is null" is
the following elementary fact, which is where the second countability of the parameter space is
used. -/

/-- **A measure is determined by what it gives near each point.**  If every point of `s` has an open
neighbourhood `O` with `μ (O ∩ bad) = 0`, then `μ (s ∩ bad) = 0`: in a second-countable space,
countably many such neighbourhoods cover `s`. -/
theorem measure_zero_of_forall_exists_isOpen_null {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [SecondCountableTopology α] {μ : Measure α} {s bad : Set α}
    (h : ∀ p ∈ s, ∃ O : Set α, IsOpen O ∧ p ∈ O ∧ μ (O ∩ bad) = 0) :
    μ (s ∩ bad) = 0 := by
  classical
  obtain ⟨basis, hbasis⟩ := TopologicalSpace.exists_seq_basis (α := α)
  -- the basis elements that sit inside a good neighbourhood
  set good : Set ℕ := {n | ∃ O : Set α, IsOpen O ∧ μ (O ∩ bad) = 0 ∧ basis n ⊆ O} with hgood
  have hnull : ∀ n ∈ good, μ (basis n ∩ bad) = 0 := by
    rintro n ⟨O, -, hO, hbO⟩
    exact measure_mono_null (Set.inter_subset_inter_left bad hbO) hO
  have hcover : s ∩ bad ⊆ ⋃ n ∈ good, basis n ∩ bad := by
    rintro p ⟨hps, hpb⟩
    obtain ⟨O, hOopen, hpO, hOμ⟩ := h p hps
    obtain ⟨W, hW, hpW, hWO⟩ := hbasis.exists_subset_of_mem_open hpO hOopen
    obtain ⟨n, rfl⟩ := hW
    exact Set.mem_biUnion ⟨O, hOopen, hOμ, hWO⟩ ⟨hpW, hpb⟩
  refine measure_mono_null hcover ?_
  rw [measure_biUnion_null_iff]
  · exact hnull
  · exact Set.Countable.mono (Set.subset_univ good) Set.countable_univ

/-- **Proposition 2.5 in the free coordinates**: almost every point of the product of the two free
regions gives a Diophantine pair of length vectors.  This is the form Lemma 3.4 consumes: the
Diophantine condition there is stated for the length vectors `simplexMap d z.1`, `simplexMap e z.2`
of the two exchanges with parameter `z`.

No measurability of the Diophantine condition is needed: `MeasureTheory.ae_of_ae_map` pulls an
almost-sure statement back along a measurable map without asking about the set. -/
theorem ae_diophantine_real {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) :
    ∀ᵐ z ∂((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))),
      IsDiophantine (simplexMap d z.1) (simplexMap e z.2) := by
  classical
  set ν : Measure ((Fin (d - 1) → ℝ) × (Fin (e - 1) → ℝ)) :=
    ((volume : Measure (Fin (d - 1) → ℝ)).restrict (simplexRegion d)).prod
      (volume.restrict (simplexRegion e)) with hν
  have hmap : (simplexVolume d).prod (simplexVolume e)
      = ν.map (Prod.map (simplexMap d) (simplexMap e)) := by
    rw [hν, simplexVolume, simplexVolume, MeasureTheory.Measure.map_prod_map _ _
      (measurable_simplexMap d) (measurable_simplexMap e)]
  have hmap' : ∀ᵐ p ∂(ν.map (Prod.map (simplexMap d) (simplexMap e))),
      IsDiophantine p.1 p.2 := by
    rw [← hmap]
    exact ae_diophantine π σ
  have h := MeasureTheory.ae_of_ae_map (μ := ν)
    ((measurable_simplexMap d).prodMap (measurable_simplexMap e)).aemeasurable hmap'
  rw [hν] at h
  exact h
