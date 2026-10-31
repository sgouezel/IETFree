/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.Presentation

/-!
Lemma 3.2: irreducibility on a block.

On a block `[u, v)` whose ends are pair-splitting singularities, the composition `g ∘ f` is
irreducible: no proper initial union of cells inside the block is mapped into itself.  Everything
here is stated on the data `(D, E)` (`IsCompIrreducibleOn`), not on the parameters.

The proof goes through the Diophantine condition on the pair: a pair-splitting point `c` inside the
block would split both exchanges (the four cases are `IETDatum.pairSplitting_of_mark_image`,
`.pairSplitting_of_mark_preimage`, `.pairSplitting_of_preimage_preimage` and
`.false_of_preimage_mark`), which `IsBlock` forbids (`block_irreducible_on_good`, through
`exists_pairSplitting_of_invariant`).

The other content is the API of a datum that the reduction uses: the cuts and marked points of
`IETDatum` (`markCuts`, `mark_mem_markCuts`, `isCutSet_markCuts`), the cut set of a composition
(`mem_comp_markCuts`), and the local form of `IsCompIrreducibleOn` (`IsCompIrreducibleOn.toDatum`).
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
/-! ## 4. Lemma 3.2: irreducibility on a block is a statement about the data

Lemma 3.2 says that the restriction of `g ∘ f` to a block is an irreducible exchange.  "Irreducible"
is a property of a **permutation together with its cells**, so it is stated here on `IETDatum`
(`IsIrreducibleOn`) and on a pair of data (`IsCompIrreducibleOn`) — never on an `IET 0 1`, which
forgets its marked points: the same function can be an exchange with one cell or with many, and only
the data say which initial unions of cells exist.

Phrasing it on the data also removes the need for the `O`-hypothesis in the *statement*: with the
marked points fixed by the data, taking `f = g` to be an involution without a splitting point (a
two-interval exchange, e.g. the rotation by `1/2`) gives `g ∘ f = 1`, whose datum has two cells and
*is* irreducible — the earlier failure of `IsIrreducibleOn (1 : IET 0 1) 0 1` came from allowing an
arbitrary cut set `S`, i.e. from forgetting the cells.  The invariance of the block under `f`
and under `g` (`IsPairSplitting.invariant`, in `IETFree.ReductionData`) and under `g ∘ f`
(`comp_lt_iff_of_pairSplitting`, in `IETFree.BlockDatum`) is about the functions and is proved. -/

/-! ### The position sub-lemma: the cells of the composition `E ∘ D`

The composition of two exchanges presented by data is again an exchange (the `IET 0 1` structure
is a group), so it has a cut set, hence a translation on each piece between consecutive cuts.
That is the *position* information the case analysis of Lemma 3.2 starts from. -/

/-! ### The marked points as a cut set, and the refinement of two data

`D` is a translation on each interval between consecutive marked points: this is `IET.lean`'s
`isCutSet_mkIETCuts` read through `IETDatum.mark`.  The cuts of the composition `E ∘ D` are the
marked points of `D` together with the preimages under `D` of the marked points of `E`
(`IsCutSet.comp`).  That is the refinement the case analysis of Lemma 3.2 runs on, and every one
of its points is either a marked point of `D` or is mapped by `D` to a marked point of `E`. -/

namespace IETDatum

variable {n : ℕ} [NeZero n]

/-- **The lengths of a datum are positive.** -/
theorem lam_pos (D : IETDatum n) (i : Fin n) : 0 < (D.lam i : ℝ) := by
  rw [IETDatum.lam, simplexMap]
  split_ifs with h
  · rw [Real.coe_toNNReal _ (by linarith [D.sum_lt_one])]
    linarith [D.sum_lt_one]
  · rw [Real.coe_toNNReal _ (le_of_lt (D.pos _))]
    exact D.pos _

/-- The left end of a cell is below the total length. -/
theorem leftEnd_lt_sum (D : IETDatum n) (i : Fin n) :
    leftEnd D.lam i < ∑ j, (D.lam j : ℝ) := by
  refine lt_of_lt_of_le ?_ (upperEnd_le_total D.lam i)
  rw [upperEnd_eq]
  have := D.lam_pos i
  linarith

/-- **The marked points of `D`, as a cut set.** -/
noncomputable def markCuts (D : IETDatum n) : Finset ℝ :=
  Finset.univ.image (fun i : Fin n => D.mark i.castSucc)

theorem mark_mem_markCuts (D : IETDatum n) (i : Fin n) : D.mark i.castSucc ∈ D.markCuts :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem mem_markCuts {D : IETDatum n} {x : ℝ} :
    x ∈ D.markCuts ↔ ∃ i : Fin n, D.mark i.castSucc = x := by
  simp only [markCuts, Finset.mem_image, Finset.mem_univ, true_and]

/-- The cut set is literally `mkIETCuts`, the cut set of `isIET_mkIETFun`. -/
theorem mkIETCuts_eq_markCuts (D : IETDatum n) : mkIETCuts D.lam 0 1 = D.markCuts := by
  have hsum : (∑ i, (D.lam i : ℝ)) = 1 := D.sum_lam
  have hmem : ∀ c ∈ Finset.univ.image (fun i : Fin n => leftEnd D.lam i),
      c ∈ Set.Ico (0 : ℝ) 1 := by
    intro c hc
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨leftEnd_nonneg D.lam i, by rw [← hsum]; exact D.leftEnd_lt_sum i⟩
  rw [mkIETCuts, hsum, if_neg (lt_irrefl (1 : ℝ)), Finset.union_empty]
  simp only [zero_add]
  rw [Finset.filter_true_of_mem hmem]
  simp only [IETDatum.markCuts, IETDatum.mark_castSucc]

/-- **`D` is a translation on each interval between consecutive marked points.** -/
theorem isCutSet_markCuts (D : IETDatum n) : IsCutSet D.toFun 0 1 D.markCuts := by
  have h := isCutSet_mkIETCuts D.lam D.π (a := 0) (t := 1) (by rw [D.sum_lam]) one_pos
  rw [D.mkIETCuts_eq_markCuts] at h
  simpa [IETDatum.toFun] using h

end IETDatum

/-! ### Irreducibility on a block: the statement, on the data

The paper's Lemma 3.2 asserts that "the restriction to `P` of the permutation `ρ` associated to
`gf` is irreducible".  That is a property of a *permutation together with its marked points*, so it
is stated here on `IETDatum` — an `IET 0 1` on its own forgets its cells, and the predicate would
then have to be given an arbitrary cut set `S`, which is exactly the data a datum carries. -/

/-- **Irreducibility of a datum on a block.**  The marked points of `D` cut `D.toFun` into
translations; `D` is irreducible on the block `[u, v)` when no proper initial *union of cells* — a
`[u, c)` with `c` a marked point of the datum — is mapped into itself.

A permutation of an exchange is reducible exactly when the cells of some proper initial segment are
mapped among themselves, i.e. when `D.toFun x ∈ Set.Ico u c` for every `x ∈ Set.Ico u c` at a marked
point `c`; this is that statement, read on the cells determined by the marks.

Both restrictions in the definition matter, each being a counterexample recorded in `NOTES.md`
("Lemma 3.2 as first stated is false"):

* `c` must range over the **marked points**, not over all of `(u, v)`.  For the pair `λ = 2/5`,
  `μ = 3/7` with both permutations the identity one has `F = E ∘ D = id` and `[0, 2/5)` is a block
  of a single cell; the identity maps every `[0, c)` into itself, but a permutation of one cell is
  irreducible.
* the target must be `Set.Ico u c`, not `Set.Ico u v`: an exchange maps the whole block `[u, v)`
  into itself, so `Ico u v` makes the predicate false for every block. -/
def IsIrreducibleOn {n : ℕ} [NeZero n] (D : IETDatum n) (u v : ℝ) : Prop :=
  ∀ c ∈ D.markCuts, u < c → c < v →
    ¬ (∀ x ∈ Set.Ico (0 : ℝ) 1, u ≤ x → x < c → D.toFun x ∈ Set.Ico u c)

/-- **Irreducibility of the composition of two data on a block.**  The cells of `E ∘ D` are cut by
`D.markCuts ∪ D ⁻¹' E.markCuts`; the predicate says that no proper initial union of those cells
inside `[u, v)` is mapped into itself by `E ∘ D`.  This is Lemma 3.2's conclusion.  It is the same
statement as `IsIrreducibleOn`, but `E ∘ D` is not a single datum — its cells are the pieces cut by
the two mark sets — so the two data are carried separately. -/
def IsCompIrreducibleOn {d e : ℕ} [NeZero d] [NeZero e] (D : IETDatum d) (E : IETDatum e)
    (u v : ℝ) : Prop :=
  ∀ c ∈ D.markCuts ∪ D.isCutSet_markCuts.preimage E.markCuts, u < c → c < v →
    ¬ (∀ x ∈ Set.Ico (0 : ℝ) 1, u ≤ x → x < c → E.toFun (D.toFun x) ∈ Set.Ico u c)

/-- **From the pair to a presentation.**  If a datum `F` presents the composition `E ∘ D` and its
marked points contain the cuts of the composition, then irreducibility of the pair on the block
transfers to `F`.  This is the step from Lemma 3.2 to the permutation of a presentation. -/
theorem IsCompIrreducibleOn.toDatum {d e n : ℕ} [NeZero d] [NeZero e] [NeZero n]
    {D : IETDatum d} {E : IETDatum e} {F : IETDatum n} {u v : ℝ}
    (h : IsCompIrreducibleOn D E u v) (hfun : ∀ x, F.toFun x = E.toFun (D.toFun x))
    (hcuts : ∀ c ∈ F.markCuts, c ∈ D.markCuts ∪ D.isCutSet_markCuts.preimage E.markCuts) :
    IsIrreducibleOn F u v := by
  intro c hc huc hcv hinv
  exact h c (hcuts c hc) huc hcv (fun x hx hux hxc => by rw [← hfun]; exact hinv x hx hux hxc)

/-- **The cuts of the composition `E ∘ D`**: the marked points of `D`, together with the preimages
under `D` of the marked points of `E`. -/
theorem isCutSet_comp_markCuts {d e : ℕ} [NeZero d] [NeZero e] (D : IETDatum d)
    (E : IETDatum e) :
    IsCutSet (fun x => E.toFun (D.toFun x)) 0 1
      (D.markCuts ∪ D.isCutSet_markCuts.preimage E.markCuts) :=
  D.isCutSet_markCuts.comp E.isCutSet_markCuts

/-- **Every cut of the composition is a marked point of `D`, or is mapped by `D` to a marked point
of `E`.**  This is the dichotomy the case analysis of Lemma 3.2 starts from. -/
theorem mem_comp_markCuts {d e : ℕ} [NeZero d] [NeZero e] (D : IETDatum d) (E : IETDatum e)
    {x : ℝ} (hx : x ∈ D.markCuts ∪ D.isCutSet_markCuts.preimage E.markCuts) :
    (∃ k : Fin (d + 1), D.mark k = x) ∨ (∃ j : Fin (e + 1), E.mark j = D.toFun x) := by
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨i, hi⟩ := D.mem_markCuts.mp hx
    exact Or.inl ⟨i.castSucc, hi⟩
  · obtain ⟨i, hi⟩ := E.mem_markCuts.mp (D.isCutSet_markCuts.mem_preimage.mp hx)
    exact Or.inr ⟨i.castSucc, hi⟩

/-- **`D` at a marked point**: the `i`-th marked point of `D` is sent to the left end of the image
of the `i`-th cell, i.e. to `imageLeft D.π D.lam i`. -/
theorem IETDatum.toFun_mark_castSucc {n : ℕ} [NeZero n] (D : IETDatum n) (i : Fin n) :
    D.toFun (D.mark i.castSucc) = imageLeft D.π D.lam i := by
  have h := mkIETFun_leftEnd (a := 0) D.lam D.π (i := i) (D.lam_pos i)
    (by simpa [D.sum_lam] using D.leftEnd_lt_sum i)
  simpa [IETDatum.toFun, IETDatum.mark_castSucc] using h

/-- **`D` is a translation on the `i`-th cell.** -/
theorem IETDatum.toFun_eq_of_mem_cell {n : ℕ} [NeZero n] (D : IETDatum n) (i : Fin n) {x : ℝ}
    (hx : x ∈ Set.Ico (D.mark i.castSucc) (D.mark i.succ)) :
    D.toFun x = x + translationVector D.π D.lam i := by
  have hle : leftEnd D.lam i ≤ x := hx.1
  have hlt : x < upperEnd D.lam i := by rw [← D.mark_succ i]; exact hx.2
  have hx' : x ∈ Set.Ico (0 : ℝ) (∑ k, (D.lam k : ℝ)) :=
    ⟨le_trans (leftEnd_nonneg D.lam i) hle, lt_of_lt_of_le hlt (upperEnd_le_total D.lam i)⟩
  have hidx : idx D.lam x (by simpa using hx'.1) = i := by
    refine idx_eq D.lam (i := i) (by simpa using hx') (by simpa using hle) (by simpa using hlt)
  rw [IETDatum.toFun, mkIETFun_of_mem D.lam D.π 0 (by simpa using hx')]
  simp only [sub_zero]
  rw [hidx]

/-- An indicator sum as a filtered sum:
`∑ i, (if p i then 1 else 0) * f i = ∑ i ∈ filter p, f i`. -/
theorem sum_ite_one_mul {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (f : Fin n → ℝ) :
    (∑ i, ((if p i then (1 : ℤ) else 0 : ℤ) : ℝ) * f i) = ∑ i ∈ Finset.univ.filter p, f i := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : p i <;> simp [h]

/-- The difference of two indicators vanishes exactly when the two predicates agree. -/
theorem ite_one_sub_ite_one_eq_zero {p q : Prop} [Decidable p] [Decidable q] :
    ((if p then (1 : ℤ) else 0) - (if q then 1 else 0)) = 0 ↔ (p ↔ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- **Case 1a of Lemma 3.2, in coordinates.**  If the equation
`imageLeft π lam k + imageLeft σ mu l - leftEnd mu l = leftEnd lam n` holds at a good pair, then
`π k = n`, `π` splits at `n` and `σ` splits at `l`.

This is the paper's Case 1a: `x = D.mark k.castSucc` is a singularity of `f`, its image `f x` lies
in the `l`-th cell of `g`, and `g f x = D.mark n.castSucc` is a singularity of `f`.  The relation
has coefficients in `{-1,0,1}`, so `relation_of_good` forces them to be constant; the constant is
`0` — the other two possibilities contradict the total length being `1`, at the last index — and
the vanishing of the coefficients is exactly the splitting condition (`perm_eq_of_preimage`).

This is the reusable core of the case analysis: every case of Lemma 3.2 produces a relation of this
shape, and what is left is bookkeeping about which cells the two points lie in. -/
theorem splitting_of_imageLeft_relation {d e : ℕ} [NeZero d] [NeZero e]
    {lam : Fin d → ℝ≥0} {π : Equiv.Perm (Fin d)} {mu : Fin e → ℝ≥0}
    {σ : Equiv.Perm (Fin e)} (hgood : ¬ IsBadParam (toReal (lam, mu)))
    (hl : lam ∈ simplex d) (hm : mu ∈ simplex e) {k : Fin d} {l : Fin e} {n : Fin d}
    (h : imageLeft π lam k + imageLeft σ mu l - leftEnd mu l = leftEnd lam n) :
    π k = n ∧ (∀ i : Fin d, (π i).val < n.val ↔ i.val < n.val) ∧ σ l = l ∧
      ∀ j : Fin e, (σ j).val < l.val ↔ j.val < l.val := by
  classical
  set a : Fin d → ℤ := fun i =>
    (if (π i).val < (π k).val then 1 else 0) - (if i.val < n.val then 1 else 0) with ha_def
  set b : Fin e → ℤ := fun j =>
    (if (σ j).val < (σ l).val then 1 else 0) - (if j.val < l.val then 1 else 0) with hb_def
  have hlam : (∑ i, (a i : ℝ) * (lam i : ℝ)) = imageLeft π lam k - leftEnd lam n := by
    have hsplit : (∑ i, (a i : ℝ) * (lam i : ℝ))
        = (∑ i, ((if (π i).val < (π k).val then (1 : ℤ) else 0 : ℤ) : ℝ) * (lam i : ℝ))
          - ∑ i, ((if i.val < n.val then (1 : ℤ) else 0 : ℤ) : ℝ) * (lam i : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ha_def, Int.cast_sub]
      ring
    rw [hsplit, sum_ite_one_mul, sum_ite_one_mul]
    rfl
  have hmu : (∑ j, (b j : ℝ) * (mu j : ℝ)) = imageLeft σ mu l - leftEnd mu l := by
    have hsplit : (∑ j, (b j : ℝ) * (mu j : ℝ))
        = (∑ j, ((if (σ j).val < (σ l).val then (1 : ℤ) else 0 : ℤ) : ℝ) * (mu j : ℝ))
          - ∑ j, ((if j.val < l.val then (1 : ℤ) else 0 : ℤ) : ℝ) * (mu j : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hb_def, Int.cast_sub]
      ring
    rw [hsplit, sum_ite_one_mul, sum_ite_one_mul]
    rfl
  have hrel : (∑ i, (a i : ℝ) * (lam i : ℝ)) + (∑ j, (b j : ℝ) * (mu j : ℝ)) = 0 := by
    rw [hlam, hmu]
    linarith
  have hA : ∀ i, |a i| ≤ 1 := by
    intro i
    simp only [ha_def]
    split_ifs <;> simp
  have hB : ∀ j, |b j| ≤ 1 := by
    intro j
    simp only [hb_def]
    split_ifs <;> simp
  -- the coefficients here are even in `{-1,0,1}`, but `relation_of_good` is stated for `≤ 2`
  obtain ⟨haconst, hbconst, hsum0⟩ := relation_of_good (p := (lam, mu)) hgood
    (fun i => le_trans (hA i) (by norm_num)) (fun j => le_trans (hB j) (by norm_num)) hl hm hrel
  set t : ℤ := a (lastIdx d) with ht
  have hbt : ∀ j : Fin e, b j = -t := by
    intro j
    rw [hbconst j]
    linarith
  have ht1 : t = -1 ∨ t = 0 ∨ t = 1 := by
    have hle := abs_le.mp (hA (lastIdx d))
    omega
  rcases ht1 with h1 | h1 | h1
  · -- `t = -1` is impossible: the last index of `d` is not below `n`
    exfalso
    have hi := haconst (lastIdx d)
    rw [h1] at hi
    simp only [ha_def] at hi
    have hlast : ¬ ((lastIdx d).val < n.val) := by
      simp only [lastIdx]
      have := n.isLt
      have := NeZero.pos d
      omega
    simp only [hlast, if_false] at hi
    split_ifs at hi <;> omega
  · -- `t = 0`: all coefficients vanish, and the two set equalities are the splitting conditions
    have hiff : ∀ i : Fin d, (π i).val < (π k).val ↔ i.val < n.val := by
      intro i
      have hi := haconst i
      rw [h1] at hi
      simp only [ha_def] at hi
      exact ite_one_sub_ite_one_eq_zero.mp hi
    obtain ⟨hpn, hsplit⟩ := perm_eq_of_preimage π k n hiff
    have hiffall : ∀ j : Fin e, (σ j).val < (σ l).val ↔ j.val < l.val := by
      intro j
      have hj := hbt j
      rw [h1] at hj
      simp only [neg_zero, hb_def] at hj
      exact ite_one_sub_ite_one_eq_zero.mp hj
    exact ⟨hpn, hsplit, (perm_eq_of_preimage σ l l hiffall).1,
      (perm_eq_of_preimage σ l l hiffall).2⟩
  · -- `t = 1` is impossible: the last index of `e` is not below `l`
    exfalso
    have hj := hbt (lastIdx e)
    rw [h1] at hj
    simp only [hb_def] at hj
    have hlast : ¬ ((lastIdx e).val < l.val) := by
      simp only [lastIdx]
      have := l.isLt
      have := NeZero.pos e
      omega
    simp only [hlast, if_false] at hj
    split_ifs at hj <;> omega

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-- `A + B - C = 0` for three indicators: `C` holds exactly when one of `A`, `B` does, and never
both. -/
theorem ite_add_ite_sub_ite {p q r : Prop} [Decidable p] [Decidable q] [Decidable r]
    (h : ((if p then (1 : ℤ) else 0) + (if q then 1 else 0) - (if r then 1 else 0)) = 0) :
    (r ↔ (p ∨ q)) ∧ ¬ (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> simp [hp, hq, hr] at h ⊢

/-- `A - B - C = 0` for three indicators: `A` holds exactly when one of `B`, `C` does, and never
both. -/
theorem ite_sub_ite_sub_ite {p q r : Prop} [Decidable p] [Decidable q] [Decidable r]
    (h : ((if p then (1 : ℤ) else 0) - (if q then 1 else 0) - (if r then 1 else 0)) = 0) :
    (p ↔ (q ∨ r)) ∧ ¬ (q ∧ r) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> simp [hp, hq, hr] at h ⊢

/-- **Case 1b of Lemma 3.2, in coordinates.**  The equation
`imageLeft π lam k + imageLeft σ mu l − leftEnd mu l + imageLeft π lam m − leftEnd lam m
= leftEnd mu n`
holds at a good pair, with `0 < n` (the point `gf x` is not `0`).  Then `σ` fixes its first cell and
splits at `n`, `π k = 0`, and `π` fixes `m` and splits there. -/
theorem splitting_of_imageLeft_relation_add {d e : ℕ} [NeZero d] [NeZero e]
    {lam : Fin d → ℝ≥0} {π : Equiv.Perm (Fin d)} {mu : Fin e → ℝ≥0}
    {σ : Equiv.Perm (Fin e)} (hgood : ¬ IsBadParam (toReal (lam, mu)))
    (hl : lam ∈ simplex d) (hm : mu ∈ simplex e) {k m : Fin d} {l n : Fin e}
    (hn : 0 < n.val)
    (h : imageLeft π lam k + imageLeft σ mu l - leftEnd mu l + imageLeft π lam m - leftEnd lam m
      = leftEnd mu n) :
    σ 0 = n ∧ (∀ j : Fin e, (σ j).val < n.val ↔ j.val < n.val) ∧
      π k = 0 ∧ π m = m ∧ ∀ i : Fin d, (π i).val < m.val ↔ i.val < m.val := by
  classical
  set a : Fin d → ℤ := fun i => (if (π i).val < (π k).val then 1 else 0)
    + (if (π i).val < (π m).val then 1 else 0) - (if i.val < m.val then 1 else 0) with ha_def
  set b : Fin e → ℤ := fun j => (if (σ j).val < (σ l).val then 1 else 0)
    - (if j.val < l.val then 1 else 0) - (if j.val < n.val then 1 else 0) with hb_def
  have hlam : (∑ i, (a i : ℝ) * (lam i : ℝ))
      = imageLeft π lam k + imageLeft π lam m - leftEnd lam m := by
    have hsplit : (∑ i, (a i : ℝ) * (lam i : ℝ))
        = (∑ i, ((if (π i).val < (π k).val then (1 : ℤ) else 0 : ℤ) : ℝ) * (lam i : ℝ))
          + (∑ i, ((if (π i).val < (π m).val then (1 : ℤ) else 0 : ℤ) : ℝ) * (lam i : ℝ))
          - ∑ i, ((if i.val < m.val then (1 : ℤ) else 0 : ℤ) : ℝ) * (lam i : ℝ) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ha_def, Int.cast_add, Int.cast_sub]
      ring
    rw [hsplit, sum_ite_one_mul, sum_ite_one_mul, sum_ite_one_mul]
    rfl
  have hmu : (∑ j, (b j : ℝ) * (mu j : ℝ))
      = imageLeft σ mu l - leftEnd mu l - leftEnd mu n := by
    have hsplit : (∑ j, (b j : ℝ) * (mu j : ℝ))
        = (∑ j, ((if (σ j).val < (σ l).val then (1 : ℤ) else 0 : ℤ) : ℝ) * (mu j : ℝ))
          - (∑ j, ((if j.val < l.val then (1 : ℤ) else 0 : ℤ) : ℝ) * (mu j : ℝ))
          - ∑ j, ((if j.val < n.val then (1 : ℤ) else 0 : ℤ) : ℝ) * (mu j : ℝ) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hb_def, Int.cast_sub]
      ring
    rw [hsplit, sum_ite_one_mul, sum_ite_one_mul, sum_ite_one_mul]
    rfl
  have hrel : (∑ i, (a i : ℝ) * (lam i : ℝ)) + (∑ j, (b j : ℝ) * (mu j : ℝ)) = 0 := by
    rw [hlam, hmu]
    linarith
  have hA : ∀ i, |a i| ≤ 2 := by
    intro i
    simp only [ha_def]
    split_ifs <;> simp
  have hB : ∀ j, |b j| ≤ 2 := by
    intro j
    simp only [hb_def]
    split_ifs <;> simp
  obtain ⟨haconst, hbconst, hsum0⟩ := relation_of_good (p := (lam, mu)) hgood hA hB hl hm hrel
  -- the coefficient of the last index of `a` is `0` or `1`, and `1` is impossible
  have ham : a m = (if (π m).val < (π k).val then 1 else 0) := by
    simp only [ha_def]
    simp
  have ha0 : a (lastIdx d) = 0 := by
    have hmt : a (lastIdx d) = (if (π m).val < (π k).val then 1 else 0) := by
      rw [← haconst m]
      exact ham
    have hcases : a (lastIdx d) = 0 ∨ a (lastIdx d) = 1 := by
      rw [hmt]
      split_ifs <;> omega
    rcases hcases with h0 | h1
    · exact h0
    · exfalso
      have hpmk : (π m).val < (π k).val := by
        by_contra hc
        rw [if_neg hc] at hmt
        omega
      have hk1 : a k = 1 := by rw [haconst k, h1]
      simp only [ha_def] at hk1
      rw [if_neg (lt_irrefl _)] at hk1
      split_ifs at hk1 <;> omega
  -- hence every coefficient vanishes
  have ha : ∀ i, a i = 0 := fun i => by rw [haconst i, ha0]
  have hb : ∀ j, b j = 0 := by
    intro j
    rw [hbconst j]
    linarith [hsum0, ha0]
  -- the `b` relation: `σ l` is the `n`-th singularity of `σ`, and `l = 0`
  have hb1 : ∀ j : Fin e, (σ j).val < (σ l).val ↔ (j.val < l.val ∨ j.val < n.val) := by
    intro j
    have h := hb j
    simp only [hb_def] at h
    exact (ite_sub_ite_sub_ite h).1
  have hb2 : ∀ j : Fin e, ¬ (j.val < l.val ∧ j.val < n.val) := by
    intro j
    have h := hb j
    simp only [hb_def] at h
    exact (ite_sub_ite_sub_ite h).2
  have hl0 : l = 0 := by
    by_contra hne
    have hpos : 0 < l.val := Nat.pos_of_ne_zero (fun h => hne (Fin.ext h))
    have h0 : (0 : Fin e).val < l.val := by simpa using hpos
    have hn0 : (0 : Fin e).val < n.val := by simpa using hn
    exact hb2 0 ⟨h0, hn0⟩
  have hbiff : ∀ j : Fin e, (σ j).val < (σ 0).val ↔ j.val < n.val := by
    intro j
    have h := hb1 j
    rw [hl0] at h
    simpa using h
  obtain ⟨hs0, hssplit⟩ := perm_eq_of_preimage σ 0 n hbiff
  -- the `a` relation: one of `π k`, `π m` is `0`, and `π` splits at `m`
  have ha1 : ∀ i : Fin d, ((π i).val < (π k).val ∨ (π i).val < (π m).val) ↔
      i.val < m.val := by
    intro i
    have h := ha i
    simp only [ha_def] at h
    exact (ite_add_ite_sub_ite h).1.symm
  have ha2 : ∀ i : Fin d, ¬ ((π i).val < (π k).val ∧ (π i).val < (π m).val) := by
    intro i
    have h := ha i
    simp only [ha_def] at h
    exact (ite_add_ite_sub_ite h).2
  have hkm : π k = 0 ∨ π m = 0 := by
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hk0, hm0⟩ := hcon
    have hk0' : 0 < (π k).val := Nat.pos_of_ne_zero (fun h => hk0 (Fin.ext h))
    have hm0' : 0 < (π m).val := Nat.pos_of_ne_zero (fun h => hm0 (Fin.ext h))
    have h := ha2 (π.symm 0)
    simp only [Equiv.apply_symm_apply] at h
    exact h ⟨hk0', hm0'⟩
  -- in the second case `π m = 0`, and splitting at `m` then forces `m = 0`
  have hm0_case : π m = 0 → m = 0 := by
    intro hm'
    by_contra hne
    have hpos : 0 < m.val := Nat.pos_of_ne_zero (fun h => hne (Fin.ext h))
    have hiff : ∀ i : Fin d, (π i).val < (π k).val ↔ i.val < m.val := by
      intro i
      have h := ha1 i
      rw [hm'] at h
      simpa using h
    have hlt : (π m).val < m.val := by rw [hm']; exact hpos
    have h2 := (perm_eq_of_preimage π k m hiff).2 m
    exact absurd (h2.mp hlt) (lt_irrefl m)
  have hsplit_main : ∀ i : Fin d, (π i).val < m.val ↔ i.val < m.val := by
    rcases hkm with hk | hm'
    · have hiff : ∀ i : Fin d, (π i).val < (π m).val ↔ i.val < m.val := by
        intro i
        have h := ha1 i
        rw [hk] at h
        simpa using h
      exact (perm_eq_of_preimage π m m hiff).2
    · have hiff : ∀ i : Fin d, (π i).val < (π k).val ↔ i.val < m.val := by
        intro i
        have h := ha1 i
        rw [hm'] at h
        simpa using h
      exact (perm_eq_of_preimage π k m hiff).2
  have hmfix : π m = m := by
    rcases hkm with hk | hm'
    · have hiff : ∀ i : Fin d, (π i).val < (π m).val ↔ i.val < m.val := by
        intro i
        have h := ha1 i
        rw [hk] at h
        simpa using h
      exact (perm_eq_of_preimage π m m hiff).1
    · have hm0 := hm0_case hm'
      rw [hm0] at hm' ⊢
      exact hm'
  have hk0 : π k = 0 := by
    rcases hkm with hk | hm'
    · exact hk
    · have hiff : ∀ i : Fin d, (π i).val < (π k).val ↔ i.val < m.val := by
        intro i
        have h := ha1 i
        rw [hm'] at h
        simpa using h
      rw [(perm_eq_of_preimage π k m hiff).1, hm0_case hm']
  exact ⟨hs0, hssplit, hk0, hmfix, hsplit_main⟩

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-- **The cells starting in `[u, c)` have total length `c - u`.**  This is the length count behind
the covering step of the position lemma of Lemma 3.2 (`u` and `c` are cuts, so `[u, c)` is a union
of whole cells). -/
theorem IsCutSet.sum_cellLen_filter {F : ℝ → ℝ} {S : Finset ℝ} (hS : IsCutSet F 0 1 S)
    {u c : ℝ} (hu : u ∈ S) (hc : c ∈ S) (huc : u < c) :
    ∑ j ∈ Finset.univ.filter
        (fun j : Fin S.card => u ≤ hS.cellStarts j ∧ hS.cellStarts j < c),
        hS.cellLen j = c - u := by
  classical
  obtain ⟨k₀, hk₀⟩ := hS.cellStarts_surj hu
  obtain ⟨k₁, hk₁⟩ := hS.cellStarts_surj hc
  have hmono := hS.cellStarts_strictMono
  have hklt : k₀ < k₁ := by
    rw [← hS.cellStarts_lt_iff, hk₀, hk₁]
    exact huc
  -- the cells starting in `[u, c)` are the cells with index in `{k₀ ≤ j < k₁}`
  have hfilter : Finset.univ.filter
        (fun j : Fin S.card => u ≤ hS.cellStarts j ∧ hS.cellStarts j < c)
      = Finset.univ.filter (fun j : Fin S.card => k₀ ≤ j ∧ j < k₁) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hk₀, ← hk₁, hmono.le_iff_le, hS.cellStarts_lt_iff]
  -- and the latter is `{j < k₁}` minus `{j < k₀}`
  have hsplit : Finset.univ.filter (fun j : Fin S.card => k₀ ≤ j ∧ j < k₁)
      = (Finset.univ.filter (fun j : Fin S.card => j < k₁)).filter (fun j => ¬ (j < k₀)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hinner : (Finset.univ.filter (fun j : Fin S.card => j < k₁)).filter (fun j => j < k₀)
      = Finset.univ.filter (fun j : Fin S.card => j < k₀) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨lt_trans h hklt, h⟩⟩
  have hstep : ∑ j ∈ Finset.univ.filter (fun j : Fin S.card => k₀ ≤ j ∧ j < k₁), hS.cellLen j
      = (∑ j ∈ Finset.univ.filter (fun j : Fin S.card => j < k₁), hS.cellLen j)
        - ∑ j ∈ Finset.univ.filter (fun j : Fin S.card => j < k₀), hS.cellLen j := by
    have h := Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ.filter (fun j : Fin S.card => j < k₁)) (p := fun j => j < k₀)
      (f := hS.cellLen)
    rw [hinner, ← hsplit] at h
    linarith
  rw [hfilter, hstep, hS.sum_cellLen_lt k₀, hS.sum_cellLen_lt k₁, hk₀, hk₁]
  ring

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-- **The position lemma of Lemma 3.2.**  If a cut set `S` of `e` has `u, c ∈ S` with `u < c` and
`e` maps `[u, c)` into itself, then `c` is the image of a cut: the cell of `e.symm c` cannot be one
of the cells starting in `[u, c)` (its image would then be inside `[u, c)`, putting `c` there), and
if it is any other cell, its image starts below `c` and straddles it, which gives a piece of
`[u, c)` outside the images of the cells of `[u, c)` — against `∑ cellLen = c - u`. -/
theorem IsCutSet.exists_imageStart_of_mapsTo {e : Equiv ℝ ℝ} {S : Finset ℝ}
    (hS : IsCutSet (⇑e) 0 1 S) {u c : ℝ} (hu : u ∈ S) (hc : c ∈ S) (huc : u < c)
    (hinv : ∀ x ∈ Set.Ico u c, ⇑e x ∈ Set.Ico u c) :
    ∃ x ∈ S, ⇑e x = c := by
  classical
  obtain ⟨k₁, hk₁⟩ := hS.cellStarts_surj hc
  -- the cells starting in `[u, c)`
  set J : Finset (Fin S.card) :=
    Finset.univ.filter (fun j => u ≤ hS.cellStarts j ∧ hS.cellStarts j < c) with hJ
  have hmemJ : ∀ j : Fin S.card, j ∈ J ↔ (u ≤ hS.cellStarts j ∧ hS.cellStarts j < c) := by
    intro j
    simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and]
  -- the cut after such a cell is at most `c`
  have hnext : ∀ j : Fin S.card, j ∈ J → hS.cellPos (j.val + 1) ≤ c := by
    intro j hj
    obtain ⟨-, hjc⟩ := (hmemJ j).mp hj
    rcases lt_or_eq_of_le (show j.val + 1 ≤ S.card from j.isLt) with hlt | heq
    · rw [hS.cellPos_of_lt hlt]
      by_contra hcon
      rw [not_le] at hcon
      have h5 : j < k₁ := by
        rw [← hS.cellStarts_lt_iff, hk₁]
        exact hjc
      have h6 : k₁ < (⟨j.val + 1, hlt⟩ : Fin S.card) := by
        rw [← hS.cellStarts_lt_iff, hk₁]
        exact hcon
      simp only [Fin.lt_def] at h5 h6
      omega
    · exfalso
      have h5 : j < k₁ := by
        rw [← hS.cellStarts_lt_iff, hk₁]
        exact hjc
      simp only [Fin.lt_def] at h5
      omega
  have hcell_sub : ∀ j ∈ J,
      Set.Ico (hS.cellStarts j) (hS.cellPos (j.val + 1)) ⊆ Set.Ico u c := fun j hj =>
    Set.Ico_subset_Ico (hmemJ j |>.mp hj).1 (hnext j hj)
  -- the union of their images
  set A : Set ℝ := ⋃ j ∈ J, ⇑e '' Set.Ico (hS.cellStarts j) (hS.cellPos (j.val + 1)) with hA
  have hA_sub : A ⊆ Set.Ico u c := by
    intro y hy
    obtain ⟨j, hjJ, hyj⟩ := Set.mem_iUnion₂.mp hy
    obtain ⟨x, hx, rfl⟩ := hyj
    exact hinv x (hcell_sub j hjJ hx)
  have hdisj : (↑J : Set (Fin S.card)).PairwiseDisjoint
      (fun j => ⇑e '' Set.Ico (hS.cellStarts j) (hS.cellPos (j.val + 1))) := by
    intro j _ k _ hjk
    exact hS.image_cell_disjoint e.injective hjk
  have hlen_nonneg : ∀ j : Fin S.card, 0 ≤ hS.cellLen j := by
    intro j
    have h1 := hS.cellStarts_lt_cellPos j
    unfold IsCutSet.cellLen
    rw [hS.cellPos_of_lt j.isLt]
    linarith
  have hvolA : volume A = ENNReal.ofReal (c - u) := by
    rw [hA, measure_biUnion_finset hdisj (fun j _ => by
      rw [hS.image_cell j]
      exact measurableSet_Ico)]
    have hterm : ∀ j ∈ J, volume (⇑e '' Set.Ico (hS.cellStarts j) (hS.cellPos (j.val + 1)))
        = ENNReal.ofReal (hS.cellLen j) := by
      intro j _
      rw [hS.image_cell j, Real.volume_Ico]
      congr 1
      ring
    rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hlen_nonneg j)]
    rw [show (∑ j ∈ J, hS.cellLen j) = c - u from hS.sum_cellLen_filter hu hc huc]
  -- the contradiction: a cell outside `J` whose image starts below `c` and straddles it
  have hcontra : ∀ j : Fin S.card, j ∉ J → ⇑e (hS.cellStarts j) < c →
      c < ⇑e (hS.cellStarts j) + hS.cellLen j → False := by
    intro j hjJ hltc hltc'
    set B : Set ℝ := Set.Ico (max (⇑e (hS.cellStarts j)) u) c with hB
    have hBsub : B ⊆ ⇑e '' Set.Ico (hS.cellStarts j) (hS.cellPos (j.val + 1)) := by
      rw [hS.image_cell j]
      exact Set.Ico_subset_Ico (le_max_left _ _) hltc'.le
    have hBdisj : Disjoint B A := by
      refine Set.disjoint_left.mpr ?_
      intro y hyB hyA
      obtain ⟨j', hj'J, hyj'⟩ := Set.mem_iUnion₂.mp hyA
      have hyj : y ∈ ⇑e '' Set.Ico (hS.cellStarts j) (hS.cellPos (j.val + 1)) := hBsub hyB
      have hne : j ≠ j' := by
        rintro rfl
        exact hjJ hj'J
      exact Set.disjoint_left.mp (hS.image_cell_disjoint e.injective hne) hyj hyj'
    have hB_meas : MeasurableSet B := measurableSet_Ico
    have hA_meas : MeasurableSet A := by
      rw [hA]
      exact Finset.measurableSet_biUnion _ (fun j _ => by
        rw [hS.image_cell j]
        exact measurableSet_Ico)
    have hUnion_sub : B ∪ A ⊆ Set.Ico u c :=
      Set.union_subset (Set.Ico_subset_Ico (le_max_right _ _) le_rfl) hA_sub
    have h1 : volume (B ∪ A) ≤ volume (Set.Ico u c) := measure_mono hUnion_sub
    rw [measure_union hBdisj hA_meas, hvolA, Real.volume_Ico, Real.volume_Ico] at h1
    have hbpos : 0 < c - max (⇑e (hS.cellStarts j)) u := by
      have : max (⇑e (hS.cellStarts j)) u < c := max_lt hltc huc
      linarith
    have hzero : ENNReal.ofReal (c - max (⇑e (hS.cellStarts j)) u) = 0 := by
      have hfin : ENNReal.ofReal (c - u) ≠ ⊤ := ENNReal.ofReal_ne_top
      have h2 : ENNReal.ofReal (c - max (⇑e (hS.cellStarts j)) u) + ENNReal.ofReal (c - u)
          ≤ 0 + ENNReal.ofReal (c - u) := by
        simpa using h1
      have h3 := (ENNReal.add_le_add_iff_right hfin).mp h2
      simpa using h3
    exact (ENNReal.ofReal_pos.mpr hbpos).ne' hzero
  -- now the cell of the preimage of `c`
  have hc01 : c ∈ Set.Ico (0 : ℝ) 1 := hS.cuts_mem c hc
  have hw01 : e.symm c ∈ Set.Ico (0 : ℝ) 1 := Equiv.IsIET.symm_mapsTo hS hc01
  obtain ⟨i, hi⟩ := hS.exists_mem_cell hw01
  have hcidx : ⇑e (e.symm c) = (e.symm c) + (⇑e (hS.cellStarts i) - hS.cellStarts i) :=
    hS.map_of_mem_cell hi
  have hle : ⇑e (hS.cellStarts i) ≤ c := by
    rw [Equiv.apply_symm_apply] at hcidx
    linarith [hcidx, hi.1]
  have hlt : c < ⇑e (hS.cellStarts i) + hS.cellLen i := by
    have hmem : c ∈ ⇑e '' Set.Ico (hS.cellStarts i) (hS.cellPos (i.val + 1)) :=
      ⟨e.symm c, hi, Equiv.apply_symm_apply e c⟩
    rw [hS.image_cell i] at hmem
    exact hmem.2
  rcases lt_or_eq_of_le hle with hltc | heqc
  · exfalso
    by_cases hiJ : i ∈ J
    · -- the cell is inside `[u, c)`, so `e.symm c` is, so `c = e (e.symm c)` would be
      exact absurd (hinv (e.symm c) (hcell_sub i hiJ hi)) (by
        simp only [Equiv.apply_symm_apply, Set.mem_Ico, not_and, not_lt]
        exact fun _ => le_rfl)
    · exact hcontra i hiJ hltc hlt
  · exact ⟨hS.cellStarts i, hS.cellStarts_mem i, heqc⟩

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-- **The image of a marked point of `D` under the composition, in coordinates.**  If `x` is the
`k`-th marked point of `D` and `D x` lies in the `l`-th cell of `E`, then
`E (D x) = imageLeft π λ k + (imageLeft σ μ l - leftEnd μ l)`: the paper's equation (eq:gfx). -/
theorem IETDatum.comp_toFun_mark_castSucc {d e : ℕ} [NeZero d] [NeZero e] (D : IETDatum d)
    (E : IETDatum e) (k : Fin d) {l : Fin e}
    (hl : imageLeft D.π D.lam k ∈ Set.Ico (E.mark l.castSucc) (E.mark l.succ)) :
    E.toFun (D.toFun (D.mark k.castSucc))
      = imageLeft D.π D.lam k + (imageLeft E.π E.lam l - leftEnd E.lam l) := by
  rw [IETDatum.toFun_mark_castSucc, IETDatum.toFun_eq_of_mem_cell E l hl, translationVector]

/-- **A pair-splitting singularity is a cut of the composition** (or the point `1`, which is not a
cut).  This is what lets the position lemma be applied at the left end of a block. -/
theorem IsPairSplitting.eq_one_or_mem_markCuts {d e : ℕ} [NeZero d] [NeZero e] {D : IETDatum d}
    {E : IETDatum e} {x : ℝ} (h : IsPairSplitting D E x) :
    x = 1 ∨ x ∈ D.markCuts ∪ D.isCutSet_markCuts.preimage E.markCuts := by
  have hzero : (0 : ℝ) ∈ D.markCuts := by
    have h := D.mark_mem_markCuts 0
    rwa [IETDatum.mark_castSucc, leftEnd_zero] at h
  rcases h with rfl | rfl | ⟨k, -, rfl, -⟩ | ⟨j, -, rfl, hjfix⟩
  · exact Or.inr (Finset.mem_union_left _ hzero)
  · exact Or.inl rfl
  · -- `x = D.mark k`
    rcases lt_or_ge k.val d with hlt | hge
    · refine Or.inr (Finset.mem_union_left _ ?_)
      have hk : k = (⟨k.val, hlt⟩ : Fin d).castSucc := Fin.ext rfl
      rw [hk]
      exact D.mark_mem_markCuts _
    · refine Or.inl ?_
      have hk : k = Fin.last d := Fin.ext (by simp only [Fin.val_last]; omega)
      simp only [hk, IETDatum.mark_last]
  · -- `x = E.mark j`
    rcases lt_or_ge j.val e with hlt | hge
    · -- `x` is a marked point of `E` inside a fixed cell of `D`, so `D x = x`
      obtain ⟨l, hlfix, hlow, hhigh⟩ := hjfix
      refine Or.inr (Finset.mem_union_right _ ?_)
      rw [D.isCutSet_markCuts.mem_preimage]
      have hde : D.toFun (E.mark j) = E.mark j :=
        D.isFixedCell_apply hlfix ⟨hlow, hhigh⟩
      rw [hde]
      have hj : j = (⟨j.val, hlt⟩ : Fin e).castSucc := Fin.ext rfl
      rw [hj]
      exact E.mark_mem_markCuts _
    · refine Or.inl ?_
      have hj : j = Fin.last e := Fin.ext (by simp only [Fin.val_last]; omega)
      simp only [hj, IETDatum.mark_last]

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-- **A splitting singularity and a fixed cell give a splitting singularity one step up**: if the
`l`-th singularity of `D` is splitting and the `l`-th cell is fixed (`π l = l`), then the
`(l+1)`-th singularity is splitting, i.e. `D.IsFixedCell l`. -/
theorem IETDatum.isSplitting_succ {n : ℕ} [NeZero n] (D : IETDatum n) {l : Fin n}
    (hl : D.IsSplitting l.castSucc) (hfix : D.π l = l) : D.IsSplitting l.succ := by
  intro i
  have h1 : i.val < l.val ↔ (D.π i).val < l.val := by
    simpa only [Fin.val_castSucc] using hl i
  simp only [Fin.val_succ]
  constructor
  · intro h
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with h' | h'
    · exact Nat.lt_succ_of_lt (h1.mp h')
    · have hi : i = l := Fin.ext h'
      rw [hi, hfix]
      omega
  · intro h
    by_contra hcon
    rw [not_lt] at hcon
    have h2 : ¬ ((D.π i).val < l.val) := by
      intro h3
      have := h1.mpr h3
      omega
    have h3 : (D.π i).val = l.val := by omega
    have h4 : D.π i = l := Fin.ext h3
    have h5 : D.π i = D.π l := by rw [h4, hfix]
    have h6 : i = l := D.π.injective h5
    rw [h6] at hcon
    omega

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-- **Case 1a of Lemma 3.2: the conclusion.**  If the `k`-th marked point of `D` is sent by the
composition to the `n`-th marked point of `D` (so both `x` and `F x` are singularities of `D`),
then that common point is pair-splitting. -/
theorem IETDatum.pairSplitting_of_mark_image {d e : ℕ} [NeZero d] [NeZero e] (D : IETDatum d)
    (E : IETDatum e) (hp : ¬ IsBadParam (D.v, E.v)) {k n : Fin d}
    (h : E.toFun (D.toFun (D.mark k.castSucc)) = D.mark n.castSucc) :
    IsPairSplitting D E (D.mark n.castSucc) := by
  classical
  have hx01 : D.mark k.castSucc ∈ Set.Ico (0 : ℝ) 1 := by
    refine ⟨(D.mark_mem_Icc _).1, ?_⟩
    have h1 : D.mark k.castSucc < D.mark k.succ := by
      rw [IETDatum.mark_castSucc, IETDatum.mark_succ, upperEnd_eq]
      have := D.lam_pos k
      linarith
    have h2 : D.mark k.succ ≤ D.mark (Fin.last d) := D.mark_mono (Fin.le_last _)
    rw [← D.mark_last]
    exact lt_of_lt_of_le h1 h2
  have hy01 : D.toFun (D.mark k.castSucc) ∈ Set.Ico (0 : ℝ) 1 := D.mapsTo hx01
  set y := imageLeft D.π D.lam k with hy
  have hy_split : y = D.toFun (D.mark k.castSucc) := (IETDatum.toFun_mark_castSucc D k).symm
  rw [← hy_split] at hy01
  set l := idx E.lam y hy01.1 with hl
  have hlmem : y ∈ Set.Ico (E.mark l.castSucc) (E.mark l.succ) :=
    ⟨idx_mem E.lam y hy01.1, by
      rw [E.mark_succ]
      exact lt_upperEnd_idx E.lam ⟨hy01.1, by rw [E.sum_lam]; exact hy01.2⟩⟩
  have hrel : imageLeft D.π D.lam k + imageLeft E.π E.lam l - leftEnd E.lam l
      = leftEnd D.lam n := by
    have h1 := IETDatum.comp_toFun_mark_castSucc D E k hlmem
    rw [h, IETDatum.mark_castSucc] at h1
    linarith [h1]
  have hgood : ¬ IsBadParam (toReal (D.lam, E.lam)) := by
    simp only [IETDatum.lam]
    rw [toReal_simplexMap D.pos E.pos]
    exact hp
  obtain ⟨hkn, hnsplit, hπl, hlsplit⟩ :=
    splitting_of_imageLeft_relation (lam := D.lam) (π := D.π) (mu := E.lam) (σ := E.π)
      hgood D.mem_simplex E.mem_simplex hrel
  have hfixcell : E.IsFixedCell l :=
    ⟨fun i => (hlsplit i).symm, E.isSplitting_succ (fun i => (hlsplit i).symm) hπl⟩
  have hyc : y = D.mark n.castSucc := by
    rw [← E.isFixedCell_apply hfixcell hlmem, hy_split]
    exact h
  refine Or.inr (Or.inr (Or.inl ⟨n.castSucc, fun i => (hnsplit i).symm, rfl, l, hfixcell, ?_, ?_⟩))
  · rw [← hyc]
    exact hlmem.1
  · rw [← hyc]
    exact hlmem.2

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-- If `π` fixes the initial segment below `π j` in the sense of a splitting singularity, then the
image of the `j`-th cell starts where the `j`-th domain cell starts (in the `π j`-index). -/
theorem imageLeft_eq_leftEnd_of_splitting {n : ℕ} (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ≥0)
    {j k : Fin n} (hpk : π j = k) (hsp : ∀ i : Fin n, i.val < k.val ↔ (π i).val < k.val) :
    imageLeft π lam j = leftEnd lam k := by
  rw [imageLeft, leftEnd, hpk]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (hsp i).symm

/-- **`O` is symmetric**: swapping the two length vectors preserves goodness. -/
theorem isBadParam_swap {d e : ℕ} {q : PReal d e} :
    IsBadParam (q.2, q.1) ↔ IsBadParam q := by
  constructor
  · rintro ⟨k, a, b, ha, hb, hk, hnt, hrel⟩
    refine ⟨k, b, a, hb, ha, hk, ?_, ?_⟩
    · rcases hnt with h | ⟨j, hj⟩ | ⟨i, hi⟩
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨j, hj⟩)
      · exact Or.inr (Or.inl ⟨i, hi⟩)
    · linarith
  · rintro ⟨k, a, b, ha, hb, hk, hnt, hrel⟩
    refine ⟨k, b, a, hb, ha, hk, ?_, ?_⟩
    · rcases hnt with h | ⟨i, hi⟩ | ⟨j, hj⟩
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨i, hi⟩)
      · exact Or.inr (Or.inl ⟨j, hj⟩)
    · linarith

/-- **The preimage of `0` under `D` is a marked point of `D`.** -/
theorem IETDatum.exists_mark_of_toFun_eq_zero {n : ℕ} [NeZero n] (D : IETDatum n) {c : ℝ}
    (hc : c ∈ Set.Ico (0 : ℝ) 1) (h : D.toFun c = 0) : ∃ m : Fin n, D.mark m.castSucc = c := by
  classical
  set m := idx D.lam c hc.1 with hm
  have hcmem : c ∈ Set.Ico (D.mark m.castSucc) (D.mark m.succ) :=
    ⟨idx_mem D.lam c hc.1, by
      rw [D.mark_succ]
      exact lt_upperEnd_idx D.lam ⟨hc.1, by rw [D.sum_lam]; exact hc.2⟩⟩
  have hdisp := D.toFun_eq_of_mem_cell m hcmem
  have hleft : leftEnd D.lam m ≤ c := hcmem.1
  have himg : 0 ≤ imageLeft D.π D.lam m := imageLeft_nonneg _ _ _
  have key : c = leftEnd D.lam m := by
    rw [hdisp, translationVector] at h
    linarith
  exact ⟨m, by rw [D.mark_castSucc, key]⟩

/-- **Case 2a of Lemma 3.2 is impossible**: if the image of a singularity of `E` (inside a cell of
`D`) is a singularity of `D`, then that point is `0`. -/
theorem leftEnd_eq_zero_of_imageLeft_eq {d e : ℕ} [NeZero d] [NeZero e]
    {lam : Fin d → ℝ≥0} {mu : Fin e → ℝ≥0} {σ : Equiv.Perm (Fin e)}
    (hgood : ¬ IsBadParam (toReal (lam, mu))) (hl : lam ∈ simplex d) (hm : mu ∈ simplex e)
    {n : Fin d} {l : Fin e} (h : imageLeft σ mu l = leftEnd lam n) : leftEnd lam n = 0 := by
  classical
  set a : Fin d → ℤ := fun i => -(if i.val < n.val then 1 else 0) with ha_def
  set b : Fin e → ℤ := fun j => (if (σ j).val < (σ l).val then 1 else 0) with hb_def
  have hlam : (∑ i, (a i : ℝ) * (lam i : ℝ)) = -leftEnd lam n := by
    have hsplit : (∑ i, (a i : ℝ) * (lam i : ℝ))
        = -∑ i, ((if i.val < n.val then (1 : ℤ) else 0 : ℤ) : ℝ) * (lam i : ℝ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ha_def, Int.cast_neg]
      ring
    rw [hsplit, sum_ite_one_mul]
    rfl
  have hmu : (∑ j, (b j : ℝ) * (mu j : ℝ)) = imageLeft σ mu l := by
    rw [hb_def, sum_ite_one_mul]
    rfl
  have hrel : (∑ i, (a i : ℝ) * (lam i : ℝ)) + (∑ j, (b j : ℝ) * (mu j : ℝ)) = 0 := by
    rw [hlam, hmu, h]
    ring
  have hA : ∀ i, |a i| ≤ 2 := by
    intro i
    simp only [ha_def]
    split_ifs <;> simp
  have hB : ∀ j, |b j| ≤ 2 := by
    intro j
    simp only [hb_def]
    split_ifs <;> simp
  obtain ⟨haconst, -, -⟩ := relation_of_good (p := (lam, mu)) hgood hA hB hl hm hrel
  -- the coefficient at the last index vanishes, so all of them do
  have hlast : a (lastIdx d) = 0 := by
    simp only [ha_def]
    have h : ¬ ((lastIdx d).val < n.val) := by
      simp only [lastIdx]
      have h1 := n.isLt
      have h2 := NeZero.pos d
      omega
    rw [if_neg h]
    simp
  have hzero : ∀ i, a i = 0 := fun i => by rw [haconst i, hlast]
  have hn0 : n = 0 := by
    have h := hzero ⟨0, NeZero.pos d⟩
    simp only [ha_def] at h
    by_contra hne
    have hpos : 0 < n.val := Nat.pos_of_ne_zero (fun h0 => hne (Fin.ext h0))
    rw [if_pos (show (⟨0, NeZero.pos d⟩ : Fin d).val < n.val from hpos)] at h
    simp at h
  rw [hn0, leftEnd_zero]

/-- The `0 < c` and `c ∈ [0,1)` facts for the composition at a cut: `c = F x` with `x ∈ [0,1)`. -/
theorem IETDatum.mark_mem_Ico {n : ℕ} [NeZero n] (D : IETDatum n) (k : Fin n) :
    D.mark k.castSucc ∈ Set.Ico (0 : ℝ) 1 := by
  refine ⟨(D.mark_mem_Icc _).1, ?_⟩
  have h1 : D.mark k.castSucc < D.mark k.succ := by
    rw [IETDatum.mark_castSucc, IETDatum.mark_succ, upperEnd_eq]
    have := D.lam_pos k
    linarith
  have h2 : D.mark k.succ ≤ D.mark (Fin.last n) := D.mark_mono (Fin.le_last _)
  rw [← D.mark_last]
  exact lt_of_lt_of_le h1 h2

/-- **Case 1b of Lemma 3.2: the conclusion.**  If the `k`-th marked point of `D` is sent by the
composition to a point `c` which is a preimage under `D` of a singularity of `E`, then `c` is
pair-splitting (as a singularity of `E` in a fixed cell of `D`). -/
theorem IETDatum.pairSplitting_of_mark_preimage {d e : ℕ} [NeZero d] [NeZero e] (D : IETDatum d)
    (E : IETDatum e) (hp : ¬ IsBadParam (D.v, E.v)) {k : Fin d} {n : Fin e} {c : ℝ}
    (hc01 : c ∈ Set.Ico (0 : ℝ) 1)
    (h : E.toFun (D.toFun (D.mark k.castSucc)) = c)
    (hc : D.toFun c = E.mark n.castSucc) : IsPairSplitting D E c := by
  classical
  have hy01 : imageLeft D.π D.lam k ∈ Set.Ico (0 : ℝ) 1 := by
    rw [← IETDatum.toFun_mark_castSucc D k]
    exact D.mapsTo (D.mark_mem_Ico k)
  set l := idx E.lam (imageLeft D.π D.lam k) hy01.1 with hl
  have hlmem : imageLeft D.π D.lam k ∈ Set.Ico (E.mark l.castSucc) (E.mark l.succ) :=
    ⟨idx_mem E.lam _ hy01.1, by
      rw [E.mark_succ]
      exact lt_upperEnd_idx E.lam ⟨hy01.1, by rw [E.sum_lam]; exact hy01.2⟩⟩
  have hc_coord : c = imageLeft D.π D.lam k
      + (imageLeft E.π E.lam l - leftEnd E.lam l) := by
    rw [← h, IETDatum.comp_toFun_mark_castSucc D E k hlmem]
  set m := idx D.lam c hc01.1 with hm
  have hcmem : c ∈ Set.Ico (D.mark m.castSucc) (D.mark m.succ) :=
    ⟨idx_mem D.lam c hc01.1, by
      rw [D.mark_succ]
      exact lt_upperEnd_idx D.lam ⟨hc01.1, by rw [D.sum_lam]; exact hc01.2⟩⟩
  have hDc : leftEnd E.lam n = c + (imageLeft D.π D.lam m - leftEnd D.lam m) := by
    have h1 := D.toFun_eq_of_mem_cell m hcmem
    rw [h1] at hc
    rw [IETDatum.mark_castSucc, translationVector] at hc
    linarith
  rcases eq_or_ne n 0 with hn0 | hn0
  · -- `D c = 0`: `c` is a marked point of `D`, so Case 1a applies
    obtain ⟨m', hm'⟩ := D.exists_mark_of_toFun_eq_zero hc01 (by rw [hc, hn0]; simp)
    rw [← hm']
    exact D.pairSplitting_of_mark_image E hp (h.trans hm'.symm)
  · have hnpos : 0 < n.val := Nat.pos_of_ne_zero (fun hv => hn0 (Fin.ext hv))
    have hrel : imageLeft D.π D.lam k + imageLeft E.π E.lam l - leftEnd E.lam l
        + imageLeft D.π D.lam m - leftEnd D.lam m = leftEnd E.lam n := by
      rw [hDc]
      linarith [hc_coord]
    have hgood : ¬ IsBadParam (toReal (D.lam, E.lam)) := by
      simp only [IETDatum.lam]
      rw [toReal_simplexMap D.pos E.pos]
      exact hp
    obtain ⟨-, hEsplit, -, hDm, hDsplit⟩ :=
      splitting_of_imageLeft_relation_add (lam := D.lam) (π := D.π) (mu := E.lam) (σ := E.π)
        hgood D.mem_simplex E.mem_simplex hnpos hrel
    have hDfix : D.IsFixedCell m :=
      ⟨fun i => (hDsplit i).symm, D.isSplitting_succ (fun i => (hDsplit i).symm) hDm⟩
    have hceq : E.mark n.castSucc = c := by
      rw [IETDatum.mark_castSucc]
      have hfix := D.isFixedCell_apply hDfix hcmem
      rw [IETDatum.toFun_eq_of_mem_cell D m hcmem, translationVector] at hfix
      linarith [hDc, hfix]
    have hinfix : E.InFixedCell D n.castSucc :=
      ⟨m, hDfix, by rw [hceq]; exact hcmem.1, by rw [hceq]; exact hcmem.2⟩
    exact Or.inr (Or.inr (Or.inr ⟨n.castSucc, fun i => (hEsplit i).symm, hceq, hinfix⟩))

/-- **Case 2a of Lemma 3.2 is impossible.** -/
theorem IETDatum.false_of_preimage_mark {d e : ℕ} [NeZero d] [NeZero e] (D : IETDatum d)
    (E : IETDatum e) (hp : ¬ IsBadParam (D.v, E.v)) {j : Fin e} {n : Fin d} {x c : ℝ}
    (hcpos : 0 < c) (hc : c = D.mark n.castSucc)
    (hDx : D.toFun x = E.mark j.castSucc)
    (h : E.toFun (D.toFun x) = c) : False := by
  classical
  have hrel : imageLeft E.π E.lam j = leftEnd D.lam n := by
    rw [hDx, IETDatum.toFun_mark_castSucc E j, hc, IETDatum.mark_castSucc] at h
    exact h
  have hgood : ¬ IsBadParam (toReal (D.lam, E.lam)) := by
    simp only [IETDatum.lam]
    rw [toReal_simplexMap D.pos E.pos]
    exact hp
  have h0 := leftEnd_eq_zero_of_imageLeft_eq (σ := E.π) hgood D.mem_simplex E.mem_simplex hrel
  rw [hc, IETDatum.mark_castSucc, h0] at hcpos
  exact absurd hcpos (lt_irrefl 0)

/-- **Case 2b of Lemma 3.2: the conclusion.**  If both `x` and `c = F x` are preimages under `D` of
singularities of `E`, then `c` is a splitting singularity of `E` in a fixed cell of `D`. -/
theorem IETDatum.pairSplitting_of_preimage_preimage {d e : ℕ} [NeZero d] [NeZero e]
    (D : IETDatum d) (E : IETDatum e) (hp : ¬ IsBadParam (D.v, E.v)) {j n : Fin e} {x c : ℝ}
    (hc01 : c ∈ Set.Ico (0 : ℝ) 1)
    (hDx : D.toFun x = E.mark j.castSucc)
    (hc : D.toFun c = E.mark n.castSucc)
    (h : E.toFun (D.toFun x) = c) : IsPairSplitting D E c := by
  classical
  have hc_coord : c = imageLeft E.π E.lam j := by
    rw [← h, hDx, IETDatum.toFun_mark_castSucc E j]
  set m := idx D.lam c hc01.1 with hm
  have hcmem : c ∈ Set.Ico (D.mark m.castSucc) (D.mark m.succ) :=
    ⟨idx_mem D.lam c hc01.1, by
      rw [D.mark_succ]
      exact lt_upperEnd_idx D.lam ⟨hc01.1, by rw [D.sum_lam]; exact hc01.2⟩⟩
  have hDc : leftEnd E.lam n = c + (imageLeft D.π D.lam m - leftEnd D.lam m) := by
    have h1 := D.toFun_eq_of_mem_cell m hcmem
    rw [h1] at hc
    rw [IETDatum.mark_castSucc, translationVector] at hc
    linarith
  have hrel : imageLeft E.π E.lam j + imageLeft D.π D.lam m - leftEnd D.lam m
      = leftEnd E.lam n := by
    rw [hDc]
    linarith [hc_coord]
  have hgood' : ¬ IsBadParam (toReal (E.lam, D.lam)) := by
    simp only [IETDatum.lam]
    rw [toReal_simplexMap E.pos D.pos]
    exact fun hb => hp (isBadParam_swap.mp hb)
  obtain ⟨hjn, hEsplit, hDm, hDsplit⟩ :=
    splitting_of_imageLeft_relation (lam := E.lam) (π := E.π) (mu := D.lam) (σ := D.π)
      hgood' E.mem_simplex D.mem_simplex hrel
  have hDfix : D.IsFixedCell m :=
    ⟨fun i => (hDsplit i).symm, D.isSplitting_succ (fun i => (hDsplit i).symm) hDm⟩
  have hcn : c = E.mark n.castSucc := by
    rw [hc_coord, imageLeft_eq_leftEnd_of_splitting E.π E.lam hjn (fun i => (hEsplit i).symm),
      IETDatum.mark_castSucc]
  have hinfix : E.InFixedCell D n.castSucc :=
    ⟨m, hDfix, by rw [← hcn]; exact hcmem.1, by rw [← hcn]; exact hcmem.2⟩
  exact Or.inr (Or.inr (Or.inr ⟨n.castSucc, fun i => (hEsplit i).symm, hcn.symm, hinfix⟩))

/-- A marked point below `1` is the left end of a cell. -/
theorem IETDatum.exists_castSucc_mark_of_lt_one {n : ℕ} [NeZero n] (D : IETDatum n) {y : ℝ}
    (hy : y < 1) {k : Fin (n + 1)} (hk : D.mark k = y) : ∃ k' : Fin n, D.mark k'.castSucc = y := by
  have hklt : k.val < n := by
    by_contra hcon
    rw [not_lt] at hcon
    have hlast : k = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [hlast, IETDatum.mark_last] at hk
    linarith
  refine ⟨⟨k.val, hklt⟩, ?_⟩
  have hkk : (⟨k.val, hklt⟩ : Fin n).castSucc = k := Fin.ext rfl
  rw [hkk]
  exact hk

/-- **The geometric core of Lemma 3.2.**  If `c` is a cut of the composition `E ∘ D`, and `[u, c)`
is mapped into itself by `E ∘ D`, then `c` itself is a pair-splitting point.

The hypothesis `u ∈ S` is what the position lemma needs; `IsPairSplitting.eq_one_or_mem_markCuts`
supplies it at the left end of a block. -/
theorem exists_pairSplitting_of_invariant {d e : ℕ} [NeZero d] [NeZero e] (D : IETDatum d)
    (E : IETDatum e) (hp : ¬ IsBadParam (D.v, E.v)) {u c : ℝ} (hu0 : 0 ≤ u) (huc : u < c)
    (huS : u ∈ D.markCuts ∪ D.isCutSet_markCuts.preimage E.markCuts)
    (hcS : c ∈ D.markCuts ∪ D.isCutSet_markCuts.preimage E.markCuts)
    (hinv : ∀ x ∈ Set.Ico (0 : ℝ) 1, u ≤ x → x < c →
      E.toFun (D.toFun x) ∈ Set.Ico u c) :
    IsPairSplitting D E c := by
  classical
  set S := D.markCuts ∪ D.isCutSet_markCuts.preimage E.markCuts with hSdef
  have hS : IsCutSet (fun x => E.toFun (D.toFun x)) 0 1 S := isCutSet_comp_markCuts D E
  have hc01 : c ∈ Set.Ico (0 : ℝ) 1 := hS.cuts_mem c hcS
  have hcpos : 0 < c := lt_of_le_of_lt hu0 huc
  -- the position lemma: `c` is the image of a cut
  have hinv' : ∀ y ∈ Set.Ico u c, E.toFun (D.toFun y) ∈ Set.Ico u c := by
    intro y hy
    exact hinv y ⟨le_trans hu0 hy.1, lt_of_lt_of_le hy.2 hc01.2.le⟩ hy.1 hy.2
  have hSe : IsCutSet (⇑(E.toIET * D.toIET).toEquiv) 0 1 S := hS
  obtain ⟨x, hxS, hFx⟩ :=
    IsCutSet.exists_imageStart_of_mapsTo hSe huS hcS huc hinv'
  have hx01 : x ∈ Set.Ico (0 : ℝ) 1 := hS.cuts_mem x hxS
  have hFx' : E.toFun (D.toFun x) = c := hFx
  -- the four cases
  rcases mem_comp_markCuts D E hxS with ⟨kx, hkx⟩ | ⟨jx, hjx⟩
  · rcases mem_comp_markCuts D E hcS with ⟨kc, hkc⟩ | ⟨jc, hjc⟩
    · -- case 1a: both are singularities of `D`
      obtain ⟨k', hk'⟩ := D.exists_castSucc_mark_of_lt_one hx01.2 hkx
      obtain ⟨n', hn'⟩ := D.exists_castSucc_mark_of_lt_one hc01.2 hkc
      have heq : E.toFun (D.toFun (D.mark k'.castSucc)) = D.mark n'.castSucc := by
        rw [hk', hn']
        exact hFx'
      have hres := D.pairSplitting_of_mark_image E hp (k := k') (n := n') heq
      rwa [hn'] at hres
    · -- case 1b: `x` is a singularity of `D`, `c` a preimage of one of `E`
      obtain ⟨k', hk'⟩ := D.exists_castSucc_mark_of_lt_one hx01.2 hkx
      obtain ⟨n', hn'⟩ := E.exists_castSucc_mark_of_lt_one (y := D.toFun c) (D.mapsTo hc01).2 hjc
      refine D.pairSplitting_of_mark_preimage E hp (k := k') (n := n') hc01 ?_ ?_
      · rw [hk']
        exact hFx'
      · rw [hn']
  · rcases mem_comp_markCuts D E hcS with ⟨kc, hkc⟩ | ⟨jc, hjc⟩
    · -- case 2a: impossible
      obtain ⟨n', hn'⟩ := D.exists_castSucc_mark_of_lt_one hc01.2 hkc
      obtain ⟨j', hj'⟩ := E.exists_castSucc_mark_of_lt_one (y := D.toFun x) (D.mapsTo hx01).2 hjx
      exact absurd (D.false_of_preimage_mark E hp (n := n') (j := j') hcpos (by rw [hn'])
        hj'.symm hFx') id
    · -- case 2b: both are preimages of singularities of `E`
      obtain ⟨j', hj'⟩ := E.exists_castSucc_mark_of_lt_one (y := D.toFun x) (D.mapsTo hx01).2 hjx
      obtain ⟨n', hn'⟩ := E.exists_castSucc_mark_of_lt_one (y := D.toFun c) (D.mapsTo hc01).2 hjc
      exact D.pairSplitting_of_preimage_preimage E hp (j := j') (n := n') hc01 hj'.symm
        (by rw [hn']) hFx'

/-- **Lemma 3.2** (irreducibility on a block), reduced to the geometric core.  The cuts of the
composition being what they are, a proper initial union of cells `[u, c)` inside a block that is
mapped into itself has `c` pair-splitting by `exists_pairSplitting_of_invariant`, which `IsBlock`
forbids. -/
theorem block_irreducible_on_good {d e : ℕ} [NeZero d] [NeZero e] (D : IETDatum d) (E : IETDatum e)
    (hp : ¬ IsBadParam (D.v, E.v)) (u v : ℝ) (hb : IsBlock D E u v) :
    IsCompIrreducibleOn D E u v := by
  intro c hcS huc hcv hinv
  have huS : u ∈ D.markCuts ∪ D.isCutSet_markCuts.preimage E.markCuts := by
    rcases hb.left.eq_one_or_mem_markCuts with h1 | h1
    · exfalso
      have hv := (hb.right.mem_Icc).2
      rw [h1] at huc
      linarith
    · exact h1
  exact hb.consecutive c
    (exists_pairSplitting_of_invariant D E hp hb.left.mem_Icc.1 huc huS hcS hinv) huc hcv
