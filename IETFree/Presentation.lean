/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.ReductionData

/-!
The presentation of `g ∘ f`: the length vector `ν` and the permutation `ρ`.

`IsCompPresentation` is the paper's sentence "the map `g ∘ f` is an interval exchange on `[0, 1)`
with respect to a permutation `ρ` which does not depend on the parameters in `O`, with singularity
set `S_f ∪ f⁻¹ S_g`"; `compLen` is the length vector it induces, and `IsCompType` the combinatorial
type of the refinement (which cut of `f` is which marked point, and which cell of `g` contains the
image of each marked cell).

The file also writes the singularities, the cuts and the lengths as **affine functions of the free
parameters** (`ParamAffine d e = PReal d e →ᵃ[ℝ] ℝ`): `cutAffine`, `imageLeftAffine`,
`cutAffineRight`, `imageLenAffine`, `preimageCutAffine`, together with the tools that make the order
of such a family locally constant — `affine_comb` / `comb_zero` ("the sign of an affine function
changes only where it vanishes", on a ball: `pos_on_ball_of_vanish_imp` / `sign_congr_on_ball`) and
`sum_len_eq_of_tiling` (a tiling of `[0, 1)` by intervals gives the partial sums), and
`exists_ball_strictMono`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-! ## 2. The presentation of `g ∘ f`: the length vector `ν` and the permutation `ρ`

The paper: "the map `gf` is an interval exchange transformation on `[0,1)` with respect to a
permutation `ρ` which does not depend on the parameters in `O`.  Its singularity set is
`S_f ∪ f⁻¹ S_g`, these singularities are all distinct and there are `d - 1 + e - 1` of them."

`IsCompPresentation` is that sentence.  `s` is the increasing list of the singularities of `g ∘ f`
(`n = d + e - 1` cells) and `ρ` is the permutation of the exchange: with `ν i = s (i+1) - s i` the
lengths of the cells, the image of the `i`-th cell is the interval `[listImageLeft ρ s i,
listImageLeft ρ s i + ν i)`, so that `g ∘ f` is the exchange `(ν, ρ)`, i.e. `mkIET1 ν ρ` written in
the coordinates of the list.  Everything Section 3 needs about `ρ`, and about the length vector
`ν`, is read off from this datum. -/

/-- **The combinatorial type of the refinement**, as a proposition about two given functions: `a i`
is the index, in the marked list `s`, of the `i`-th cut of `f` (i.e. of `leftEnd lam i`), and
`B k` is the cell of `g` that contains the image of the `k`-th marked cell.

This is the data that makes the length vector of the composition invertible: the marked cells with
index in `[a i.castSucc, a i.succ)` are exactly those inside the `i`-th cell of `f`, so `λ i` is the
sum of their lengths (`IsCompPresentation.lam_eq_sum`).  It is stated as a predicate on `a`, `B`
rather than as a field of `IsCompPresentation` because it is *data* and `IsCompPresentation` is a
proposition; and it is not a function of the length vector at a single parameter — it is constant on
a good region.  The three pieces are named `top`, `cut` and `image`. -/
structure IsCompType {d e n : ℕ} [NeZero d] [NeZero e] (lam : Fin d → ℝ≥0)
    (π : Equiv.Perm (Fin d)) (hl : (∑ i, lam i) = 1) (mu : Fin e → ℝ≥0)
    (s : Fin (n + 1) → ℝ) (a : Fin (d + 1) → Fin (n + 1)) (B : Fin n → Fin e) : Prop where
  /-- the top cut of `f` is the last marked point -/
  top : a (Fin.last d) = Fin.last n
  /-- `a i.castSucc` is the marked index of the `i`-th cut of `f` -/
  cut : ∀ i : Fin d, s (a i.castSucc) = leftEnd lam i
  /-- the image of the `k`-th marked cell lies in the `B k`-th cell of `g` -/
  image : ∀ k : Fin n, leftEnd mu (B k) ≤ mkIET1 lam π hl (s k.castSucc) ∧
    mkIET1 lam π hl (s k.castSucc) + (s k.succ - s k.castSucc)
      ≤ leftEnd mu (B k) + (mu (B k) : ℝ)

/-- The length of the `i`-th cell of a list `s` of marked points. -/
noncomputable def listLen {n : ℕ} (s : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  s i.succ - s i.castSucc

/-- **The left end of the `i`-th cell**, written in the lengths of the list. -/
noncomputable def listLeftEnd {n : ℕ} (s : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), (s j.succ - s j.castSucc)

/-- **The left end of the image of the `i`-th cell**, in the image order given by the permutation
`ρ`: the total length of the cells whose image sits to the left of the image of the `i`-th. -/
noncomputable def listImageLeft {n : ℕ} (ρ : Equiv.Perm (Fin n)) (s : Fin (n + 1) → ℝ)
    (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => ρ j < ρ i), (s j.succ - s j.castSucc)

/-- **`(s, ρ)` presents `g ∘ f` as the interval exchange with singularity list `s` and permutation
`ρ`** — with `s` the list of the **marked** singularities, the common refinement of the partition of
`f` into its cells and of the preimage under `f` of the partition of `g` (`f_transl`, `g_transl`),
which has `d + e - 1` cells (`card_eq`).

`cell` says that on the `i`-th cell, `g ∘ f` is the translation of the exchange with lengths
`ν i = s (i+1) - s i` and permutation `ρ`, namely by
`listImageLeft ρ s i - listLeftEnd s i`: the image of the cell is the interval
`[listImageLeft ρ s i, listImageLeft ρ s i + ν i)`.  Note that
this image need **not** be one of the cells of the list — for `g = id` the marked list is a cut
set of `f`, and `f`'s cells are *not* mapped onto cells in general (the images of its cells are
the `λ`-intervals rearranged according to `π`).  The weaker statement "the image of the `i`-th
cell is the `ρ i`-th cell" holds only when the marked list is *minimal*, i.e. when `g ∘ f` is
discontinuous at every marked point; it is false for `g = id` and `d = 2`, `π` the transposition,
`λ = (1/3, 2/3)`, where the images of the two cells start at `2/3` and `0` while the marked
points are `0, 1/3, 1`.

The marking matters: a singularity of `f` need not be a discontinuity of `g ∘ f` (`g` maps `0` and
`1` to the same point, so the jump of `f` at a cell boundary can be cancelled), and with a coarser
list `g ∘ f` is still presented by it; but then the length vector is not the one Lemma 3.1 is
about. -/
structure IsCompPresentation {d e : ℕ} [NeZero d] [NeZero e] (lam : Fin d → ℝ≥0)
    (π : Equiv.Perm (Fin d)) (mu : Fin e → ℝ≥0) (σ : Equiv.Perm (Fin e))
    (hl : (∑ i, lam i) = 1) (hm : (∑ j, mu j) = 1)
    (n : ℕ) (s : Fin (n + 1) → ℝ) (ρ : Equiv.Perm (Fin n)) : Prop where
  /-- the list starts at `0` -/
  zero : s 0 = 0
  /-- the list ends at `1` -/
  top : s (Fin.last n) = 1
  /-- the singularities are increasing, so the cells `[s i, s (i+1))` are nonempty -/
  mono : StrictMono s
  /-- **`g ∘ f` is the exchange with lengths `s (i+1) - s i` and permutation `ρ`**: it translates
  the `i`-th cell by `listImageLeft ρ s i - listLeftEnd s i` -/
  cell : ∀ (i : Fin n) (x : ℝ), s i.castSucc ≤ x → x < s i.succ →
    (mkIET1 mu σ hm * mkIET1 lam π hl) x = x + (listImageLeft ρ s i - listLeftEnd s i)
  /-- **`f` translates each `s`-cell**: the list refines the partition of `f` into its cells. -/
  f_transl : ∀ (i : Fin n), ∃ δ : ℝ, ∀ x : ℝ, s i.castSucc ≤ x → x < s i.succ →
    (mkIET1 lam π hl) x = x + δ
  /-- **`g` translates the image of each `s`-cell**: the list also refines the partition pulled back
  from `g`, i.e. the `s`-points include `f⁻¹` of the cuts of `g`. -/
  g_transl : ∀ (i : Fin n), ∃ δ : ℝ, ∀ x : ℝ, s i.castSucc ≤ x → x < s i.succ →
    (mkIET1 mu σ hm) ((mkIET1 lam π hl) x) = (mkIET1 lam π hl) x + δ
  /-- the list has the `d + e - 1` **marked** cells: the common refinement of the partition of `f`
  and of the preimage of the partition of `g` -/
  card_eq : n = d + e - 1

/-- The length vector of a presentation: the `i`-th coordinate is the length of the `i`-th cell. -/
noncomputable def compLen {n : ℕ} {s : Fin (n + 1) → ℝ} (hmono : StrictMono s) (i : Fin n) : ℝ≥0 :=
  ⟨s i.succ - s i.castSucc, sub_nonneg.mpr (le_of_lt (hmono (Fin.castSucc_lt_succ (i := i))))⟩

/-- **The length vector of a presentation at a single point**, from the monotonicity of the list *at
that point*.  This is the only form of the length vector: a global monotonicity hypothesis
`∀ q, StrictMono fun k => s k q` is not derivable from the data of a good region (the list is known
to be monotone only on the region), so everything in Section 3 is stated at a point. -/
noncomputable def compLenVec {d e n : ℕ} (s : Fin (n + 1) → ParamAffine d e) (q : PReal d e)
    (hmono : StrictMono fun k => s k q) : Fin n → ℝ≥0 :=
  fun i => compLen hmono i

/-- **The cells of a strictly increasing list with `0` and `1` as endpoints cover `[0, 1)`.**  The
discrete counterpart of `IsCutSet.exists_mem_cell`: with the list `s` of an `IsCompPresentation`
(or of any partition of `[0, 1)`), every point of `[0, 1)` lies in one of the pieces
`[s i, s (i+1))`. -/
theorem exists_cell_of_strictMono {n : ℕ} {s : Fin (n + 1) → ℝ} (hmono : StrictMono s)
    (h0 : s 0 = 0) (h1 : s (Fin.last n) = 1) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    ∃ i : Fin n, s i.castSucc ≤ x ∧ x < s i.succ := by
  classical
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exact absurd (h0.symm.trans h1) (by norm_num)
    · exact h
  -- the largest cell start at most `x`
  set S := Finset.univ.filter (fun i : Fin n => s i.castSucc ≤ x) with hS
  have hne : S.Nonempty :=
    ⟨⟨0, hn⟩, by
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show s (⟨0, hn⟩ : Fin n).castSucc = s 0 from rfl, h0]
      exact hx.1⟩
  refine ⟨S.max' hne, (Finset.mem_filter.mp (Finset.max'_mem S hne)).2, ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  have hlt' : (S.max' hne).val + 1 ≤ n := (S.max' hne).isLt
  rcases lt_or_eq_of_le hlt' with hlt | heq
  · -- the next cell start is also at most `x`, contradicting maximality
    have hj : (⟨(S.max' hne).val + 1, hlt⟩ : Fin n) ∈ S := by
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show s (⟨(S.max' hne).val + 1, hlt⟩ : Fin n).castSucc = s (S.max' hne).succ from rfl]
      exact hcon
    have hle := Finset.le_max' S _ hj
    simp only [Fin.le_def] at hle
    omega
  · -- the largest index is the last one, and there `s (i+1) = 1 > x`
    have hlast : (S.max' hne).succ = Fin.last n :=
      Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
    rw [hlast, h1] at hcon
    linarith [hx.2]

/-! ### The images of the marked points

The case analysis of Lemma 3.2 needs the images of the singularities under `g ∘ f` in coordinates.
For the marked point `s k` write it as `s k.castSucc` for `k : Fin n`; the two pieces of information
are "which cell of `f` it lies in" and "which cell of `g` its image `f (s k)` lies in".  The lemmas
below give the coordinates in the two cases, in the form the paper uses:

* if `s k` is a singularity of `f`, then `f (s k) = imageLeft π lam i` where `i` is the cell of `f`;
* if `s k` is a preimage of a singularity of `g`, then `g (f (s k)) = imageLeft σ mu j`.

Both are evaluations of `mkIETFun` at a left end of a cell, which is `mkIETFun_leftEnd`. -/

/-- **`mkIETFun` at the left end of a cell**: if the `i`-th cell of the exchange is nonempty
(`leftEnd lam i < upperEnd lam i`), the exchange sends the left end of the cell to the left end of
the image of the cell.  This is the coordinate computation behind every case of Lemma 3.2. -/
theorem mkIETFun_leftEnd {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (a : ℝ) {i : Fin n} (hi : 0 < (lam i : ℝ))
    (hb : a + leftEnd lam i < a + ∑ k, (lam k : ℝ)) :
    mkIETFun lam π a (a + leftEnd lam i) = a + imageLeft π lam i := by
  have hx : a + leftEnd lam i ∈ Set.Ico a (a + ∑ k, (lam k : ℝ)) :=
    ⟨by linarith [leftEnd_nonneg lam i], hb⟩
  have hx0 : 0 ≤ leftEnd lam i := leftEnd_nonneg lam i
  rw [mkIETFun_of_mem lam π a hx]
  have hidx : idx lam (a + leftEnd lam i - a) (by linarith) = i := by
    refine idx_eq lam ⟨by linarith, ?_⟩ (by linarith) ?_
    · linarith
    · rw [upperEnd_eq]; linarith
  rw [hidx, translationVector]
  ring

/-- On the open simplex region, the value of `simplexMap d v` at an index that is not the last one
is the corresponding free coordinate. -/
theorem simplexMap_of_lt {d : ℕ} {v : Fin (d - 1) → ℝ} (hv : v ∈ simplexRegion d)
    {j : Fin d} (hj : j.val < d - 1) :
    (simplexMap d v j : ℝ) = v ⟨j.val, hj⟩ := by
  have hne : j.val + 1 ≠ d := by omega
  rw [simplexMap, dif_neg hne, Real.coe_toNNReal _ (le_of_lt (hv.1 _))]

/-- **Membership in the simplex from the free region**, in the index form `Fin (n - 1)` (the
version in `Diophantine.lean` is stated for `p + 1`). -/
theorem simplexMap_mem_simplex_fin {n : ℕ} [NeZero n] {v : Fin (n - 1) → ℝ}
    (hpos : ∀ i, 0 < v i) (hsum : ∑ i, v i < 1) : simplexMap n v ∈ simplex n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_one_add_one (NeZero.ne n)).symm⟩
  exact simplexMap_mem_simplex hpos hsum

/-- **The cuts of `f` are affine functions of the free parameters**: on the open simplex region the
`i`-th cut of `simplexMap d v` is the sum of the free coordinates of index `< i`.  `i = 0` gives the
empty sum and `i` the last index gives `1 - (last free coordinate)`, as it must. -/
theorem leftEnd_simplexMap {d : ℕ} {v : Fin (d - 1) → ℝ} (hv : v ∈ simplexRegion d)
    (i : Fin d) :
    leftEnd (simplexMap d v) i = ∑ j : Fin (d - 1), if j.val < i.val then v j else 0 := by
  classical
  rw [leftEnd]
  have hL : (∑ j ∈ Finset.univ.filter (fun j : Fin d => j < i), (simplexMap d v j : ℝ))
      = ∑ k ∈ Finset.univ.filter (fun k : Fin (d - 1) => k.val < i.val), v k := by
    refine Finset.sum_bij
      (fun (j : Fin d) (hj : j ∈ Finset.univ.filter (fun j : Fin d => j < i)) =>
        (⟨j.val, ?_⟩ : Fin (d - 1))) ?_ ?_ ?_ ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Fin.lt_def] at hj
      have := i.isLt
      omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rw [Fin.lt_def] at hj
      exact hj
    · intro j₁ _ j₂ _ h
      exact Fin.ext (by simpa using congrArg Fin.val h)
    · intro k hk
      refine ⟨(Fin.castLE (Nat.sub_le d 1) k : Fin d), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Fin.lt_def, Fin.val_castLE]
        simpa using hk
      · exact Fin.ext (by simp)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact simplexMap_of_lt hv (by have := i.isLt; rw [Fin.lt_def] at hj; omega)
  rw [hL, Finset.sum_filter]

/-- **A cut of `g` is not a sum of lengths of `f`** at a good parameter pair: for `j ≠ 0` and any
set `S` of cells of `f`, `leftEnd μ j ≠ ∑_{i ∈ S} λ i`.

For `S = {i | i < k}` this says that no cut of `g` is a cut of `f`; for `S = {i | π i < m}` that no
cut of `g` is a left end of an *image* interval of `f`.  The relation
`∑_{i<j} μᵢ - ∑_{i∈S} λᵢ = 0` has coefficients in `{0,1}`, so `relation_of_good` forces both
coefficient functions to be constant in their index; the `μ` one is not, because it is `1` at `0`
and `0` at the last index (`j ≠ 0`). -/
theorem leftEnd_ne_sum_lam_of_good {d e : ℕ} [NeZero d] [NeZero e]
    {p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0)}
    (hp : ¬ IsBadParam (toReal p)) (hl : p.1 ∈ simplex d) (hm : p.2 ∈ simplex e)
    {j : Fin e} (hj : j ≠ 0) (S : Finset (Fin d)) :
    leftEnd p.2 j ≠ ∑ i ∈ S, (p.1 i : ℝ) := by
  intro h
  set b : Fin e → ℤ := fun i => if i < j then 1 else 0 with hb
  set a : Fin d → ℤ := fun i => -if i ∈ S then 1 else 0 with ha
  have hbfun : ∀ i : Fin e, ((b i : ℝ) * (p.2 i : ℝ)) = if i < j then (p.2 i : ℝ) else 0 := by
    intro i
    by_cases hij : i < j
    · simp only [hb, if_pos hij]; push_cast; ring
    · simp only [hb, if_neg hij]; push_cast; ring
  have hafun : ∀ i : Fin d, ((a i : ℝ) * (p.1 i : ℝ)) = -(if i ∈ S then (p.1 i : ℝ) else 0) := by
    intro i
    by_cases hik : i ∈ S
    · simp only [ha, if_pos hik]; push_cast; ring
    · simp only [ha, if_neg hik]; push_cast; ring
  have hbval : (∑ i, (b i : ℝ) * (p.2 i : ℝ)) = leftEnd p.2 j := by
    simp only [hbfun, leftEnd, ← Finset.sum_filter]
  have haval : (∑ i, (a i : ℝ) * (p.1 i : ℝ)) = -∑ i ∈ S, (p.1 i : ℝ) := by
    simp only [hafun]
    rw [Finset.sum_neg_distrib]
    congr 1
    rw [Finset.sum_ite_mem_eq]
  have hrel : (∑ i, (a i : ℝ) * (p.1 i : ℝ)) + (∑ i, (b i : ℝ) * (p.2 i : ℝ)) = 0 := by
    rw [hbval, haval]
    linarith
  have ha2 : ∀ i, |a i| ≤ 2 := by
    intro i; simp only [ha]; split <;> norm_num
  have hb2 : ∀ i, |b i| ≤ 2 := by
    intro i; simp only [hb]; split <;> norm_num
  obtain ⟨-, hbconst, -⟩ := relation_of_good hp ha2 hb2 hl hm hrel
  have h0 := hbconst 0
  have hj0 : (0 : Fin e) < j := Fin.pos_iff_ne_zero.mpr hj
  have hlast : ¬ ((lastIdx e) < j) := by
    rw [Fin.lt_def]
    change ¬ ((e - 1 : ℕ) < j.val)
    have := j.isLt
    omega
  simp only [hb] at h0
  rw [if_pos hj0, if_neg hlast] at h0
  exact one_ne_zero h0

/-- **A singularity of `g` sits strictly inside the image of a cell of `f`**: at a good parameter
pair, each `j`-th cut of `g` with `j ≠ 0` lies strictly inside the image `Ico (imageLeft k)
(imageLeft k + λ k)` of a cell `k` of `f`.  The cell is the one indexed by `idx` for the *image*
lengths `imageLengths π λ`; the strictness at the left end is where goodness is used
(`leftEnd_ne_sum_lam_of_good`, with `S = {i | π i < m}`). -/
theorem exists_lt_imageLeft_of_good {d e : ℕ} [NeZero d] [NeZero e]
    {p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0)}
    (hp : ¬ IsBadParam (toReal p)) (hl : p.1 ∈ simplex d) (hm : p.2 ∈ simplex e)
    (hpos : ∀ i, 0 < p.2 i) (π : Equiv.Perm (Fin d)) {j : Fin e} (hj : j ≠ 0) :
    ∃ k : Fin d, imageLeft π p.1 k < leftEnd p.2 j ∧
      leftEnd p.2 j < imageLeft π p.1 k + (p.1 k : ℝ) := by
  have hsum : (∑ i, (p.1 i : ℝ)) = 1 := by rw [← NNReal.coe_sum]; exact_mod_cast hl
  have hsum2 : (∑ i, (p.2 i : ℝ)) = 1 := by rw [← NNReal.coe_sum]; exact_mod_cast hm
  have hy0 : 0 ≤ leftEnd p.2 j := leftEnd_nonneg p.2 j
  have hy1 : leftEnd p.2 j < ∑ i, (imageLengths π p.1 i : ℝ) := by
    rw [sum_imageLengths π p.1, hsum]
    have h1 : leftEnd p.2 j < leftEnd p.2 j + (p.2 j : ℝ) := by linarith [hpos j]
    rw [← upperEnd_eq] at h1
    refine h1.trans_le (le_trans (upperEnd_le_total p.2 j) ?_)
    rw [hsum2]
  set m := idx (imageLengths π p.1) (leftEnd p.2 j) hy0 with hmdef
  -- the left end of the image of the cell `π.symm m` is the sum over `{i | π i < m}`
  have hkey : imageLeft π p.1 (π.symm m)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin d => π i < m), (p.1 i : ℝ) := by
    simp only [imageLeft, Equiv.apply_symm_apply]
  have hleft : leftEnd (imageLengths π p.1) m = imageLeft π p.1 (π.symm m) := by
    rw [imageLeft_eq_leftEnd]
    simp
  refine ⟨π.symm m, ?_, ?_⟩
  · -- strictness at the left end
    have hle : imageLeft π p.1 (π.symm m) ≤ leftEnd p.2 j := by
      rw [← hleft]
      exact idx_mem (imageLengths π p.1) (leftEnd p.2 j) hy0
    refine lt_of_le_of_ne hle ?_
    intro hc
    exact leftEnd_ne_sum_lam_of_good hp hl hm hj
      (Finset.univ.filter (fun i : Fin d => π i < m)) (by rw [← hc, hkey])
  · -- the upper end
    have hlt := lt_upperEnd_idx (imageLengths π p.1) (x := leftEnd p.2 j) ⟨hy0, hy1⟩
    have heq : upperEnd (imageLengths π p.1) m
        = imageLeft π p.1 (π.symm m) + (p.1 (π.symm m) : ℝ) := by
      rw [upperEnd_eq, imageLeft_eq_leftEnd]
      simp [imageLengths]
    rwa [heq] at hlt

/-- **`f⁻¹` of a point strictly inside the image of a cell**: the translate back by the translation
vector of that cell. -/
theorem mkIET1_inv_of_lt_imageLeft {d e : ℕ} [NeZero d]
    {p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0)} (hl : p.1 ∈ simplex d)
    {π : Equiv.Perm (Fin d)} {k : Fin d} {y : ℝ}
    (h1 : imageLeft π p.1 k < y) (h2 : y < imageLeft π p.1 k + (p.1 k : ℝ)) :
    (mkIET1 p.1 π hl)⁻¹ y = y - translationVector π p.1 k := by
  have hsum : (∑ i, (p.1 i : ℝ)) = 1 := by rw [← NNReal.coe_sum]; exact_mod_cast hl
  have htv : translationVector π p.1 k = imageLeft π p.1 k - leftEnd p.1 k := rfl
  set x := y - translationVector π p.1 k with hx
  have hmem : x ∈ Set.Ico (leftEnd p.1 k) (upperEnd p.1 k) := by
    rw [hx, htv, upperEnd_eq]
    constructor <;> linarith
  have hx1 : x ∈ Set.Ico (0 : ℝ) (∑ i, (p.1 i : ℝ)) := by
    refine ⟨by linarith [leftEnd_nonneg p.1 k, hmem.1], ?_⟩
    exact hmem.2.trans_le (upperEnd_le_total p.1 k)
  have hidx : idx p.1 x (by linarith [hx1.1]) = k := idx_eq p.1 hx1 hmem.1 hmem.2
  have happ : ⇑(mkIET1 p.1 π hl) x = y := by
    have hfun : ⇑(mkIET1 p.1 π hl) x = mkIETFun p.1 π 0 x := rfl
    rw [hfun, mkIETFun_of_mem p.1 π 0 (by simpa using hx1)]
    simp only [sub_zero, hidx]
    rw [hx]
    ring
  rw [← happ, IET.symm_apply_apply]

/-- **Pointwise evaluation of a finite sum of affine maps.**  Mathlib has no `AffineMap.sum_apply`,
and `Finset.sum_apply` does not fire because of the coercion `AffineMap → function`. -/
theorem AffineMap.sum_apply {ι : Type*} {k V1 P1 V2 : Type*} [Ring k] [AddCommGroup V1]
    [Module k V1] [AddTorsor V1 P1] [AddCommGroup V2] [Module k V2] (s : Finset ι)
    (F : ι → P1 →ᵃ[k] V2) (q : P1) :
    ((s.sum F : P1 →ᵃ[k] V2)) q = s.sum (fun i => F i q) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have h1 : ∀ f g : P1 →ᵃ[k] V2, (f + g) q = f q + g q := fun f g => rfl
      rw [h1, ih]

/-- **A tiling of `[0,1)` by intervals gives the partial sums**: if the intervals
`Ico (P i) (P i + ν i)` are pairwise disjoint and cover `[0,1)`, then the left end of each is the
total length of those that start strictly to its left.  This is the partial-sum identity behind both
the cell lengths of the composition (`P = s`) and its image starts (`P = (g ∘ f) (s ·)`). -/
theorem sum_len_eq_of_tiling {n : ℕ} {P ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    (h0 : ∀ i, 0 ≤ P i) (h1 : ∀ i, P i + ν i ≤ 1)
    (hdisj : ∀ i j : Fin n, i ≠ j →
      Disjoint (Set.Ico (P i) (P i + ν i)) (Set.Ico (P j) (P j + ν j)))
    (hcover : ∀ y ∈ Set.Ico (0 : ℝ) 1, ∃ i : Fin n, y ∈ Set.Ico (P i) (P i + ν i))
    (i : Fin n) :
    P i = ∑ j ∈ Finset.univ.filter (fun j : Fin n => P j < P i), ν j := by
  classical
  set F := Finset.univ.filter (fun j : Fin n => P j < P i) with hF
  -- no interval of `F` crosses `P i`
  have hle : ∀ j ∈ F, P j + ν j ≤ P i := by
    intro j hj
    have hjlt : P j < P i := by
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hj
    by_contra hcon
    rw [not_le] at hcon
    have hPi : P i ∈ Set.Ico (P j) (P j + ν j) := ⟨le_of_lt hjlt, hcon⟩
    have hii : P i ∈ Set.Ico (P i) (P i + ν i) := ⟨le_rfl, by linarith [hν i]⟩
    refine Set.disjoint_left.mp (hdisj j i ?_) hPi hii
    rintro rfl
    exact absurd hjlt (lt_irrefl _)
  -- the intervals of `F` are exactly `[0, P i)`
  have hunion : (⋃ j ∈ F, Set.Ico (P j) (P j + ν j)) = Set.Ico 0 (P i) := by
    ext y
    constructor
    · intro hy
      obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
      exact ⟨le_trans (h0 j) hyj.1, lt_of_lt_of_le hyj.2 (hle j hj)⟩
    · intro hy
      obtain ⟨hy0, hy1⟩ := hy
      have hy1' : y < 1 := by linarith [hν i, h1 i]
      obtain ⟨j, hj⟩ := hcover y ⟨hy0, hy1'⟩
      refine Set.mem_iUnion₂.mpr ⟨j, ?_, hj⟩
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_lt hj.1 hy1
  -- compare volumes
  have hnn : ∀ j ∈ F, 0 ≤ ν j := fun j _ => le_of_lt (hν j)
  have hmain : ENNReal.ofReal (P i) = ∑ j ∈ F, ENNReal.ofReal (ν j) := by
    have h2 : volume (Set.Ico (0 : ℝ) (P i))
        = ∑ j ∈ F, volume (Set.Ico (P j) (P j + ν j)) := by
      rw [← hunion]
      exact measure_biUnion_finset (fun j _ k _ hjk => hdisj j k hjk)
        (fun j _ => measurableSet_Ico)
    rw [Real.volume_Ico, sub_zero] at h2
    rw [h2]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Real.volume_Ico]
    congr 1
    ring
  rw [← ENNReal.ofReal_sum_of_nonneg hnn] at hmain
  exact (ENNReal.ofReal_eq_ofReal_iff (h0 i) (Finset.sum_nonneg hnn)).mp hmain

/-- **An affine function of the parameters, evaluated at an affine combination.** -/
theorem affine_comb {d e : ℕ} (G : ParamAffine d e) (q₀ q : PReal d e) (t : ℝ) :
    G ((1 - t) • q₀ + t • q) = (1 - t) * G q₀ + t * G q := by
  have h0 : ∀ x : PReal d e, G x = G.linear x + G 0 := by
    intro x
    have h := AffineMap.map_vadd G (0 : PReal d e) x
    simp only [vadd_eq_add, add_zero] at h
    linarith [h]
  have h1 : (1 - t) • q₀ + t • q = t • (q - q₀) + q₀ := by
    rw [smul_sub, sub_smul, one_smul]
    module
  have h1' : t • (q - q₀) + q₀ = (t • (q - q₀)) +ᵥ q₀ := rfl
  rw [h1, h1', AffineMap.map_vadd, map_smul, smul_eq_mul]
  have h2 : G.linear (q - q₀) = G.linear q - G.linear q₀ := map_sub _ _ _
  rw [h2, h0 q, h0 q₀, vadd_eq_add]
  ring

/-- The key algebra: if `c > 0 > b` then `(1 - t) * c + t * b = 0` for `t = c / (c - b)`. -/
theorem comb_zero {b c : ℝ} (hc : 0 < c) (hb : b < 0) :
    (1 - c / (c - b)) * c + (c / (c - b)) * b = 0 := by
  have hden : c - b ≠ 0 := by linarith
  field_simp
  ring

/-- **Strict positivity propagates on a ball**, given that vanishing at any point of the ball forces
`G` to vanish identically.  The ball is convex, so the affine combination
`(1 - t) • q₀ + t • q` (`affine_comb`) stays inside it. -/
theorem pos_on_ball_of_vanish_imp {d e : ℕ} {G : ParamAffine d e} {q₀ : PReal d e} {ε : ℝ}
    (hε : 0 < ε) (hv : ∀ q ∈ Metric.ball q₀ ε, G q = 0 → G = 0) (h0 : 0 < G q₀) :
    ∀ q ∈ Metric.ball q₀ ε, 0 < G q := by
  intro q hq
  by_contra hcon
  rw [not_lt] at hcon
  rcases lt_or_eq_of_le hcon with hq' | hq'
  · -- the affine combination of `q₀` and `q` where `G` vanishes lies in the ball
    have hden : (0 : ℝ) < G q₀ - G q := by linarith
    have ht1 : G q₀ / (G q₀ - G q) ≤ 1 := by
      rw [div_le_one hden]; linarith
    have hmem : (1 - G q₀ / (G q₀ - G q)) • q₀ + (G q₀ / (G q₀ - G q)) • q ∈ Metric.ball q₀ ε := by
      refine (convex_ball q₀ ε) (Metric.mem_ball_self hε) hq
        (by linarith : (0 : ℝ) ≤ 1 - G q₀ / (G q₀ - G q))
        (div_nonneg (le_of_lt h0) (le_of_lt hden)) (by ring)
    have hzero : G ((1 - G q₀ / (G q₀ - G q)) • q₀ + (G q₀ / (G q₀ - G q)) • q) = 0 := by
      rw [affine_comb]
      exact comb_zero h0 hq'
    have hG := hv _ hmem hzero
    rw [hG] at h0
    simp at h0
  · have hG : G = 0 := hv q hq hq'
    rw [hG] at h0
    simp at h0

/-- **A nonnegative value propagates on a ball**, under the same vanishing hypothesis: either `G`
vanishes at `q₀` and hence identically, or it is strictly positive there and
`pos_on_ball_of_vanish_imp` applies. -/
theorem nonneg_on_ball_of_vanish_imp {d e : ℕ} {G : ParamAffine d e} {q₀ : PReal d e} {ε : ℝ}
    (hε : 0 < ε) (hv : ∀ q ∈ Metric.ball q₀ ε, G q = 0 → G = 0) (h0 : 0 ≤ G q₀) :
    ∀ q ∈ Metric.ball q₀ ε, 0 ≤ G q := by
  intro q hq
  rcases eq_or_lt_of_le h0 with h | h
  · have hG : G = 0 := hv q₀ (Metric.mem_ball_self hε) h.symm
    rw [hG]
    simp
  · exact le_of_lt (pos_on_ball_of_vanish_imp hε hv h q hq)

/-- **The sign of an affine function is constant on a ball** on which it does not vanish. -/
theorem sign_congr_on_ball {d e : ℕ} (G : ParamAffine d e) {q₀ : PReal d e} {ε : ℝ}
    (_hε : 0 < ε) (hne : ∀ q ∈ Metric.ball q₀ ε, G q ≠ 0) {q q' : PReal d e}
    (hq : q ∈ Metric.ball q₀ ε) (hq' : q' ∈ Metric.ball q₀ ε) :
    0 < G q ↔ 0 < G q' := by
  constructor
  · intro hpos
    by_contra hcon
    rw [not_lt] at hcon
    rcases lt_or_eq_of_le hcon with hneg | hzero
    · -- the affine combination where `G` vanishes lies in the ball
      have hden : (0 : ℝ) < G q - G q' := by linarith
      have ht1 : G q / (G q - G q') ≤ 1 := by
        rw [div_le_one hden]; linarith
      have hmem : (1 - G q / (G q - G q')) • q + (G q / (G q - G q')) • q'
          ∈ Metric.ball q₀ ε := by
        refine (convex_ball q₀ ε) hq hq'
          (by linarith : (0 : ℝ) ≤ 1 - G q / (G q - G q'))
          (div_nonneg (le_of_lt hpos) (le_of_lt hden)) (by ring)
      have hz : G ((1 - G q / (G q - G q')) • q + (G q / (G q - G q')) • q') = 0 := by
        rw [affine_comb]
        exact comb_zero hpos hneg
      exact hne _ hmem hz
    · exact hne q' hq' hzero
  · intro hpos
    by_contra hcon
    rw [not_lt] at hcon
    rcases lt_or_eq_of_le hcon with hneg | hzero
    · have hden : (0 : ℝ) < G q' - G q := by linarith
      have ht1 : G q' / (G q' - G q) ≤ 1 := by
        rw [div_le_one hden]; linarith
      have hmem : (1 - G q' / (G q' - G q)) • q' + (G q' / (G q' - G q)) • q
          ∈ Metric.ball q₀ ε := by
        refine (convex_ball q₀ ε) hq' hq
          (by linarith : (0 : ℝ) ≤ 1 - G q' / (G q' - G q))
          (div_nonneg (le_of_lt hpos) (le_of_lt hden)) (by ring)
      have hz : G ((1 - G q' / (G q' - G q)) • q' + (G q' / (G q' - G q)) • q) = 0 := by
        rw [affine_comb]
        exact comb_zero hpos hneg
      exact hne _ hmem hz
    · exact hne q hq hzero

/-- **The pointwise order of a family of affine functions is constant on a ball on which the values
never collide.** -/
theorem lt_iff_lt_of_ne_on_ball {d e m : ℕ} (F : Fin m → ParamAffine d e) {q₀ : PReal d e} {ε : ℝ}
    (hε : 0 < ε) (hne : ∀ (i j : Fin m), i ≠ j → ∀ q ∈ Metric.ball q₀ ε, F i q ≠ F j q)
    {q q' : PReal d e} (hq : q ∈ Metric.ball q₀ ε) (hq' : q' ∈ Metric.ball q₀ ε) (i j : Fin m) :
    F i q < F j q ↔ F i q' < F j q' := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  have hsign : (0 < F j q - F i q) ↔ (0 < F j q' - F i q') := by
    have h1 : (F j - F i) q = F j q - F i q := rfl
    have h2 : (F j - F i) q' = F j q' - F i q' := rfl
    rw [← h1, ← h2]
    refine sign_congr_on_ball (F j - F i) hε (fun x hx => ?_) hq hq'
    rw [show (F j - F i) x = F j x - F i x from rfl]
    exact sub_ne_zero.mpr (Ne.symm (hne i j hij x hx))
  constructor
  · intro hlt
    have h1 : 0 < F j q - F i q := by linarith
    have h2 := hsign.mp h1
    linarith
  · intro hlt
    have h1 : 0 < F j q' - F i q' := by linarith
    have h2 := hsign.mpr h1
    linarith

/-- **The permutation of the images**: the rank of `F · q₀` among the values `F · q₀`, which is the
same as the rank at any `q` of the ball on which the values do not collide. -/
theorem exists_rank_perm {d e m : ℕ} (F : Fin m → ParamAffine d e) {q₀ : PReal d e} {ε : ℝ}
    (hε : 0 < ε) (hne : ∀ (i j : Fin m), i ≠ j → ∀ q ∈ Metric.ball q₀ ε, F i q ≠ F j q) :
    ∃ ρ : Equiv.Perm (Fin m), ∀ q ∈ Metric.ball q₀ ε, ∀ i j : Fin m,
      (ρ i < ρ j ↔ F i q < F j q) := by
  classical
  -- the finite set of values at `q₀`, and its increasing enumeration
  set T := Finset.univ.image (fun i : Fin m => F i q₀) with hT
  have hinj : Function.Injective (fun i : Fin m => F i q₀) := by
    intro i j hij
    by_contra hne'
    exact hne i j hne' q₀ (Metric.mem_ball_self hε) hij
  have hcard : T.card = m := by
    rw [hT, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  set iso := Finset.orderIsoOfFin T hcard with hiso
  have hmem : ∀ i : Fin m, F i q₀ ∈ T := fun i => by
    rw [hT]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  -- the permutation
  have hbij : Function.Bijective
      (fun i : Fin m => iso.symm (⟨F i q₀, hmem i⟩ : T)) := by
    constructor
    · intro i j hij
      have h1 : (⟨F i q₀, hmem i⟩ : T) = ⟨F j q₀, hmem j⟩ := iso.symm.injective hij
      exact hinj (congrArg Subtype.val h1)
    · intro k
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (show (iso k : T).val ∈ T from (iso k).2)
      refine ⟨i, ?_⟩
      beta_reduce
      have h1 : (⟨F i q₀, hmem i⟩ : T) = iso k := Subtype.ext hi
      rw [h1, iso.symm_apply_apply]
  refine ⟨Equiv.ofBijective _ hbij, ?_⟩
  intro q hq i j
  have hkey : ∀ i : Fin m, iso (Equiv.ofBijective _ hbij i) = (⟨F i q₀, hmem i⟩ : T) := by
    intro i
    exact iso.apply_symm_apply _
  rw [← iso.lt_iff_lt, hkey i, hkey j]
  have hsub : (⟨F i q₀, hmem i⟩ : T) < ⟨F j q₀, hmem j⟩ ↔ F i q₀ < F j q₀ :=
    Subtype.mk_lt_mk
  rw [hsub]
  exact lt_iff_lt_of_ne_on_ball F hε hne (Metric.mem_ball_self hε) hq i j

/-- The free coordinate `q ↦ q.1 j`, as an affine function of the parameters. -/
noncomputable def leftCoordAffine {d e : ℕ} (j : Fin (d - 1)) : ParamAffine d e :=
  ((LinearMap.proj j).comp (LinearMap.fst ℝ (Fin (d - 1) → ℝ) (Fin (e - 1) → ℝ))).toAffineMap

theorem leftCoordAffine_apply {d e : ℕ} (j : Fin (d - 1)) (q : PReal d e) :
    leftCoordAffine (e := e) j q = q.1 j := rfl

/-- **The `i`-th cut of `f`, as an affine function of the free parameters.** -/
noncomputable def cutAffine {d e : ℕ} (i : Fin d) : ParamAffine d e :=
  ∑ j : Fin (d - 1), if j.val < i.val then leftCoordAffine (e := e) j else 0

theorem cutAffine_apply {d e : ℕ} (i : Fin d) (q : PReal d e) :
    cutAffine (e := e) i q = ∑ j : Fin (d - 1), if j.val < i.val then q.1 j else 0 := by
  rw [cutAffine, AffineMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : j.val < i.val
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

/-- **On the open simplex region the `i`-th cut of `f` is the affine function `cutAffine i`.** -/
theorem cutAffine_eq_leftEnd {d e : ℕ} {q : PReal d e}
    (hq : q.1 ∈ simplexRegion d) (i : Fin d) :
    cutAffine (e := e) i q = leftEnd (simplexMap d q.1) i := by
  rw [cutAffine_apply, leftEnd_simplexMap hq]

/-- The `j`-th length of the simplex, as an affine function of the free parameters: the free
coordinate `q.1 j` at a free index, and the remaining mass `1 - ∑ q.1` at the last index. -/
noncomputable def imageLenAffine {d e : ℕ} [NeZero d] (j : Fin d) : ParamAffine d e :=
  if h : j.val + 1 = d then
    AffineMap.const ℝ (PReal d e) 1 - ∑ m : Fin (d - 1), leftCoordAffine (e := e) m
  else leftCoordAffine (e := e) ⟨j.val, by
    have h1 := j.isLt
    have h2 := NeZero.pos d
    omega⟩

theorem imageLenAffine_apply_last {d e : ℕ} [NeZero d] {j : Fin d} (h : j.val + 1 = d)
    (q : PReal d e) :
    imageLenAffine (e := e) j q = 1 - ∑ m : Fin (d - 1), q.1 m := by
  rw [imageLenAffine, dif_pos h]
  have hsub : ∀ (f g : ParamAffine d e), (f - g) q = f q - g q := fun f g => rfl
  rw [hsub, AffineMap.sum_apply]
  simp [leftCoordAffine_apply]

theorem imageLenAffine_apply_free {d e : ℕ} [NeZero d] {j : Fin d} (h : ¬ j.val + 1 = d)
    (q : PReal d e) :
    imageLenAffine (e := e) j q
      = q.1 ⟨j.val, by have h1 := j.isLt; have h2 := NeZero.pos d; omega⟩ := by
  simp only [imageLenAffine, dif_neg h, leftCoordAffine_apply]

/-- **The left end of the image of the `k`-th cell, as an affine function of the free
parameters.** -/
noncomputable def imageLeftAffine {d e : ℕ} [NeZero d] (π : Equiv.Perm (Fin d)) (k : Fin d) :
    ParamAffine d e :=
  ∑ j : Fin d, if π j < π k then imageLenAffine (e := e) j else 0

theorem imageLeftAffine_apply {d e : ℕ} [NeZero d] (π : Equiv.Perm (Fin d)) (k : Fin d)
    (q : PReal d e) :
    imageLeftAffine (e := e) π k q
      = ∑ j : Fin d, if π j < π k then imageLenAffine (e := e) j q else 0 := by
  rw [imageLeftAffine, AffineMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : π j < π k
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    rfl

/-- **On the open simplex region the left end of the image of the `k`-th cell is the affine
function `imageLeftAffine π k`.** -/
theorem imageLeftAffine_eq {d e : ℕ} [NeZero d] (π : Equiv.Perm (Fin d)) {q : PReal d e}
    (hq : q.1 ∈ simplexRegion d) (k : Fin d) :
    imageLeftAffine (e := e) π k q = imageLeft π (simplexMap d q.1) k := by
  rw [imageLeftAffine_apply, imageLeft, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hjk : π j < π k
  · rw [if_pos hjk, if_pos hjk]
    by_cases hj : j.val + 1 = d
    · rw [imageLenAffine_apply_last hj, simplexMap, dif_pos hj,
        Real.coe_toNNReal _ (by linarith [hq.2])]
    · have hj' : j.val < d - 1 := by
        have h1 := j.isLt
        have h2 := NeZero.pos d
        omega
      rw [imageLenAffine_apply_free hj, simplexMap_of_lt hq hj']
  · rw [if_neg hjk, if_neg hjk]

/-- On the open simplex region, `imageLenAffine j` is the `j`-th length of `simplexMap`. -/
theorem imageLenAffine_eq {d e : ℕ} [NeZero d] {q : PReal d e} (hq : q.1 ∈ simplexRegion d)
    (j : Fin d) : imageLenAffine (e := e) j q = (simplexMap d q.1 j : ℝ) := by
  by_cases h : j.val + 1 = d
  · rw [imageLenAffine_apply_last h, simplexMap, dif_pos h,
      Real.coe_toNNReal _ (by linarith [hq.2])]
  · have hj' : j.val < d - 1 := by
      have h1 := j.isLt
      have h2 := NeZero.pos d
      omega
    rw [imageLenAffine_apply_free h, simplexMap_of_lt hq hj']

/-- The open simplex region is open: it is cut out by the strict inequalities `0 < v i` and
`∑ v < 1`. -/
theorem isOpen_simplexRegion (d : ℕ) : IsOpen (simplexRegion d) := by
  have h1 : IsOpen {v : Fin (d - 1) → ℝ | ∀ i, 0 < v i} := by
    rw [show {v : Fin (d - 1) → ℝ | ∀ i, 0 < v i} = ⋂ i, {v : Fin (d - 1) → ℝ | 0 < v i} from by
      ext v
      simp]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have h2 : IsOpen {v : Fin (d - 1) → ℝ | ∑ i, v i < 1} :=
    isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  exact h1.inter h2

/-- The free coordinate `q ↦ q.2 j` of the second factor, as an affine function of the
parameters. -/
noncomputable def rightCoordAffine {d e : ℕ} (j : Fin (e - 1)) : ParamAffine d e :=
  ((LinearMap.proj j).comp (LinearMap.snd ℝ (Fin (d - 1) → ℝ) (Fin (e - 1) → ℝ))).toAffineMap

theorem rightCoordAffine_apply {d e : ℕ} (j : Fin (e - 1)) (q : PReal d e) :
    rightCoordAffine (d := d) j q = q.2 j := rfl

/-- **The `j`-th cut of `g`, as an affine function of the free parameters.** -/
noncomputable def cutAffineRight {d e : ℕ} (j : Fin e) : ParamAffine d e :=
  ∑ m : Fin (e - 1), if m.val < j.val then rightCoordAffine (d := d) m else 0

theorem cutAffineRight_apply {d e : ℕ} (j : Fin e) (q : PReal d e) :
    cutAffineRight (d := d) j q = ∑ m : Fin (e - 1), if m.val < j.val then q.2 m else 0 := by
  rw [cutAffineRight, AffineMap.sum_apply]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  by_cases h : m.val < j.val
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

/-- **On the open simplex region the `j`-th cut of `g` is the affine function
`cutAffineRight j`.** -/
theorem cutAffineRight_eq_leftEnd {d e : ℕ} {q : PReal d e}
    (hq : q.2 ∈ simplexRegion e) (j : Fin e) :
    cutAffineRight (d := d) j q = leftEnd (simplexMap e q.2) j := by
  rw [cutAffineRight_apply, leftEnd_simplexMap hq]

/-- The coordinates of `simplexMap` are positive on the open simplex region. -/
theorem pos_simplexMap {m : ℕ} {v : Fin (m - 1) → ℝ} (hv : v ∈ simplexRegion m)
    (i : Fin m) : 0 < simplexMap m v i := by
  rw [← NNReal.coe_pos]
  by_cases h : i.val + 1 = m
  · rw [simplexMap, dif_pos h, Real.coe_toNNReal _ (by linarith [hv.2])]
    linarith [hv.2]
  · rw [simplexMap, dif_neg h, Real.coe_toNNReal _ (le_of_lt (hv.1 _))]
    exact hv.1 _

/-- **Step 2 of the local presentation: each cut of `g` sits strictly inside a cell of `f`.**

At a good parameter pair in the open simplex region and for `j ≠ 0`, the cut `leftEnd μ j` of `g`
lies strictly inside the image of a cell `k` of `f`; consequently `f⁻¹ (leftEnd μ j)` is the
translate `leftEnd μ j - translationVector π λ k`, which is an affine function of the free
parameters.  Goodness is consumed exactly once, in the strict inequality at the left end. -/
theorem exists_lt_imageLeft_simplexMap {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d))
    {q : PReal d e} (hq : q ∈ goodParams d e) (hr : q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e)
    {j : Fin e} (hj : j ≠ 0) :
    ∃ k : Fin d, imageLeft π (simplexMap d q.1) k < leftEnd (simplexMap e q.2) j ∧
      leftEnd (simplexMap e q.2) j < imageLeft π (simplexMap d q.1) k + (simplexMap d q.1 k : ℝ) ∧
      (mkIET1 (simplexMap d q.1) π (simplexMap_mem_simplex_fin hr.1.1 hr.1.2))⁻¹
          (leftEnd (simplexMap e q.2) j)
        = leftEnd (simplexMap e q.2) j - translationVector π (simplexMap d q.1) k := by
  have hl : simplexMap d q.1 ∈ simplex d := simplexMap_mem_simplex_fin hr.1.1 hr.1.2
  have hm : simplexMap e q.2 ∈ simplex e := simplexMap_mem_simplex_fin hr.2.1 hr.2.2
  have hp : ¬ IsBadParam (toReal (simplexMap d q.1, simplexMap e q.2)) := by
    rw [toReal_simplexMap hr.1.1 hr.2.1]
    exact hq
  have hpos : ∀ i, 0 < (simplexMap e q.2) i := fun i => pos_simplexMap hr.2 i
  obtain ⟨k, h1, h2⟩ := exists_lt_imageLeft_of_good
    (p := (simplexMap d q.1, simplexMap e q.2)) hp hl hm hpos π hj
  exact ⟨k, h1, h2, mkIET1_inv_of_lt_imageLeft
    (p := (simplexMap d q.1, simplexMap e q.2)) hl h1 h2⟩

/-- **The affine candidate for `f⁻¹ (leftEnd μ j)`**, for a fixed cell `k` of `f`:
`leftEnd μ j - translationVector π λ k`, written out as
`cutAffineRight j - imageLeft k + cutAffine k`. -/
noncomputable def preimageCutAffine {d e : ℕ} [NeZero d] (π : Equiv.Perm (Fin d)) (j : Fin e)
    (k : Fin d) : ParamAffine d e :=
  cutAffineRight (d := d) j - imageLeftAffine (e := e) π k + cutAffine (e := e) k

theorem preimageCutAffine_apply {d e : ℕ} [NeZero d] (π : Equiv.Perm (Fin d)) (j : Fin e)
    (k : Fin d) (q : PReal d e) :
    preimageCutAffine π j k q
      = cutAffineRight (d := d) j q - imageLeftAffine (e := e) π k q + cutAffine (e := e) k q := by
  rw [preimageCutAffine]
  have h1 : ∀ (f g : ParamAffine d e), (f - g) q = f q - g q := fun f g => rfl
  have h2 : ∀ (f g : ParamAffine d e), (f + g) q = f q + g q := fun f g => rfl
  rw [h2, h1]

/-- **At a good parameter pair, `f⁻¹` of a cut of `g` is the affine function
`preimageCutAffine`.** -/
theorem preimageCutAffine_eq {d e : ℕ} [NeZero d] (π : Equiv.Perm (Fin d))
    {q : PReal d e} (hr : q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e)
    {j : Fin e} {k : Fin d}
    (h1 : imageLeft π (simplexMap d q.1) k < leftEnd (simplexMap e q.2) j)
    (h2 : leftEnd (simplexMap e q.2) j
      < imageLeft π (simplexMap d q.1) k + (simplexMap d q.1 k : ℝ)) :
    (mkIET1 (simplexMap d q.1) π (simplexMap_mem_simplex_fin hr.1.1 hr.1.2))⁻¹
        (leftEnd (simplexMap e q.2) j)
      = preimageCutAffine π j k q := by
  have hl : simplexMap d q.1 ∈ simplex d := simplexMap_mem_simplex_fin hr.1.1 hr.1.2
  rw [mkIET1_inv_of_lt_imageLeft (p := (simplexMap d q.1, simplexMap e q.2)) hl h1 h2,
    preimageCutAffine_apply, cutAffineRight_eq_leftEnd hr.2,
    imageLeftAffine_eq π hr.1, cutAffine_eq_leftEnd hr.1, translationVector]
  ring

/-- **The cell of `f` whose image contains a cut of `g` is locally constant**, with a strict
containment that persists on a ball.  The strict inequalities are between continuous (indeed
affine) functions of the parameters, and the two ambient conditions — being in `goodParams` and in
the open simplex region — are open. -/
theorem exists_ball_imageLeft_lt {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    {q₀ : PReal d e} (hq₀ : q₀ ∈ goodParams d e)
    (hr₀ : q₀.1 ∈ simplexRegion d ∧ q₀.2 ∈ simplexRegion e) {j : Fin e} (hj : j ≠ 0) :
    ∃ (k : Fin d) (ε : ℝ), 0 < ε ∧ Metric.ball q₀ ε ⊆ goodParams d e ∧
      (∀ q ∈ Metric.ball q₀ ε, q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e) ∧
      (∀ q ∈ Metric.ball q₀ ε, imageLeftAffine (e := e) π k q < cutAffineRight (d := d) j q ∧
        cutAffineRight (d := d) j q
          < imageLeftAffine (e := e) π k q + imageLenAffine (e := e) k q) ∧
      (∀ q ∈ Metric.ball q₀ ε, ∀ (hl : simplexMap d q.1 ∈ simplex d),
        (mkIET1 (simplexMap d q.1) π hl)⁻¹ (leftEnd (simplexMap e q.2) j)
          = preimageCutAffine π j k q) := by
  have hl₀ : simplexMap d q₀.1 ∈ simplex d := simplexMap_mem_simplex_fin hr₀.1.1 hr₀.1.2
  have hm₀ : simplexMap e q₀.2 ∈ simplex e := simplexMap_mem_simplex_fin hr₀.2.1 hr₀.2.2
  obtain ⟨k, h1, h2, -⟩ := exists_lt_imageLeft_simplexMap π hq₀ hr₀ hj
  -- the same two inequalities, in affine form, at `q₀`
  have h1' : imageLeftAffine (e := e) π k q₀ < cutAffineRight (d := d) j q₀ := by
    rw [imageLeftAffine_eq π hr₀.1, cutAffineRight_eq_leftEnd hr₀.2]
    exact h1
  have h2' : cutAffineRight (d := d) j q₀
      < imageLeftAffine (e := e) π k q₀ + imageLenAffine (e := e) k q₀ := by
    rw [cutAffineRight_eq_leftEnd hr₀.2, imageLeftAffine_eq π hr₀.1,
      imageLenAffine_eq hr₀.1]
    exact h2
  -- the open set of parameters where everything still holds
  have hcont1 : Continuous (fun q : PReal d e => imageLeftAffine (e := e) π k q) :=
    AffineMap.continuous_of_finiteDimensional _
  have hcont2 : Continuous (fun q : PReal d e => cutAffineRight (d := d) j q) :=
    AffineMap.continuous_of_finiteDimensional _
  have hcont3 : Continuous (fun q : PReal d e =>
      imageLeftAffine (e := e) π k q + imageLenAffine (e := e) k q) :=
    (AffineMap.continuous_of_finiteDimensional _).add
      (AffineMap.continuous_of_finiteDimensional _)
  set W : Set (PReal d e) :=
    {q | imageLeftAffine (e := e) π k q < cutAffineRight (d := d) j q} ∩
      {q | cutAffineRight (d := d) j q
        < imageLeftAffine (e := e) π k q + imageLenAffine (e := e) k q} ∩
      goodParams d e ∩ (simplexRegion d ×ˢ simplexRegion e) with hW
  have hWopen : IsOpen W := by
    refine IsOpen.inter (IsOpen.inter (IsOpen.inter (isOpen_lt hcont1 hcont2) ?_)
      (isOpen_goodParams d e)) ?_
    · exact isOpen_lt hcont2 hcont3
    · exact (isOpen_simplexRegion d).prod (isOpen_simplexRegion e)
  have hq₀W : q₀ ∈ W := ⟨⟨⟨h1', h2'⟩, hq₀⟩, hr₀⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hWopen q₀ hq₀W
  refine ⟨k, ε, hε, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact (hball hq).1.2
  · intro q hq
    exact (hball hq).2
  · intro q hq
    exact (hball hq).1.1
  · intro q hq _
    have hreg := (hball hq).2
    have i1 : imageLeft π (simplexMap d q.1) k < leftEnd (simplexMap e q.2) j := by
      rw [← imageLeftAffine_eq π hreg.1, ← cutAffineRight_eq_leftEnd hreg.2]
      exact (hball hq).1.1.1
    have i2 : leftEnd (simplexMap e q.2) j
        < imageLeft π (simplexMap d q.1) k + (simplexMap d q.1 k : ℝ) := by
      rw [← cutAffineRight_eq_leftEnd hreg.2, ← imageLeftAffine_eq π hreg.1,
        ← imageLenAffine_eq hreg.1]
      exact (hball hq).1.1.2
    exact preimageCutAffine_eq π hreg i1 i2

/-- **A strictly increasing list of affine functions of the parameters stays strictly increasing on
a small ball.**  The set of parameters on which the finitely many strict inequalities
`F i q < F j q` (`i < j`) hold is a finite intersection of open sets. -/
theorem exists_ball_lt_of_lt {d e m : ℕ} (F : Fin m → ParamAffine d e) {q₀ : PReal d e}
    (h : ∀ i j : Fin m, i < j → F i q₀ < F j q₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ Metric.ball q₀ ε, ∀ i j : Fin m, i < j → F i q < F j q := by
  classical
  set W : Set (PReal d e) := {q | ∀ i j : Fin m, i < j → F i q < F j q} with hW
  have hWopen : IsOpen W := by
    have : W = ⋂ (p : {p : Fin m × Fin m // p.1 < p.2}),
        {q : PReal d e | F p.1.1 q < F p.1.2 q} := by
      ext q
      simp only [hW, Set.mem_ofPred_eq, Set.mem_iInter, Subtype.forall]
      constructor
      · rintro h1 ⟨i, j⟩ hij
        exact h1 i j hij
      · rintro h1 i j hij
        exact h1 ⟨i, j⟩ hij
    rw [this]
    exact isOpen_iInter_of_finite fun p =>
      isOpen_lt (AffineMap.continuous_of_finiteDimensional _)
        (AffineMap.continuous_of_finiteDimensional _)
  have hq₀ : q₀ ∈ W := h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hWopen q₀ hq₀
  exact ⟨ε, hε, fun q hq => hball hq⟩

/-- The same, in the form of `StrictMono`. -/
theorem exists_ball_strictMono {d e m : ℕ} (F : Fin m → ParamAffine d e) {q₀ : PReal d e}
    (h : StrictMono fun i => F i q₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ Metric.ball q₀ ε, StrictMono fun i => F i q :=
  exists_ball_lt_of_lt F fun _ _ hij => h hij
