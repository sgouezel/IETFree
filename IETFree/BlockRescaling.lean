/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.SingularityList

/-!
The rescaling of an exchange to a block of marked cells, the block length vector and the block
permutation, and the irreducibility of that permutation.

Lemma 3.4 applies Theorem 2.6 to the pair `(f, g)` **restricted to a block** `[u, v)` and rescaled
to `[0, 1)`; Theorem 2.6 asks for a pair of exchanges of `[0, 1)`, one of them uniquely ergodic and
rigid by translations, and Masur–Veech and Veech's rigidity apply to the *permutation* of that
exchange. So the block permutation must be irreducible, which is what
`irreduciblePerm_of_no_invariant_cut` below supplies: the geometric irreducibility of Lemma 3.2
(`IsIrreducibleOn`: no invariant initial interval `[0, leftEnd lam k)`) implies `IsIrreduciblePerm`
of the permutation.

The rescaling itself is the affine change of variables `x ↦ (x - u)/(v - u)`: `rescaleMap` and its
inverse `rescaleMapInv`, and `rescaleFun`, the rescaled restriction of a function to `[u, v)`.

The rest of the file computes on the marked list: the prefix sums (`lamNat`, `leftEndNat`), the
block data `blockMass` / `blockLam` / `blockPerm`, and the main technical statement
`mkIET1_rescale_subinterval` — the rescaled restriction of the exchange of a marked list to a block
of its cells is `mkIET1` of the block lengths and the block permutation.  The comparison of the
singular points of the list with the cells of `f` and of `g` (`listLeftEnd`, `listImageLeft`,
`comp_image_cell`) is also here, together with the conjugacy of a word under a change of *both*
generators (`evalWord_conj_apply`), which the transport back from the rescaled block needs; the
evaluation of a word in two exchanges is `evalWord` in `IETFree.MeasureTools`; its `Equiv`-valued
form (`evalWordEquiv`, with the bridge `evalWord_toEquiv`) is in `IETFree/ChallengeWeakSolved.lean`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

-- `simp only [Fin.val_mk]` is needed in the pure `Fin`-index goals below (removing it breaks the
-- following `omega`/`rw`), but this version of the `unusedSimpArgs` linter reports it as unused.
set_option linter.unusedSimpArgs false

/-- The affine rescaling of `[u, v)` onto `[0, 1)`. -/
noncomputable def rescaleMap (u v x : ℝ) : ℝ := (x - u) / (v - u)

/-- Its inverse: `[0, 1)` back onto `[u, v)`. -/
noncomputable def rescaleMapInv (u v y : ℝ) : ℝ := u + y * (v - u)

theorem rescaleMap_rescaleMapInv {u v : ℝ} (h : u < v) (y : ℝ) :
    rescaleMap u v (rescaleMapInv u v y) = y := by
  have hne : v - u ≠ 0 := by linarith
  simp only [rescaleMap, rescaleMapInv]
  rw [show u + y * (v - u) - u = y * (v - u) from by ring]
  field_simp

theorem rescaleMapInv_rescaleMap {u v : ℝ} (h : u < v) (x : ℝ) :
    rescaleMapInv u v (rescaleMap u v x) = x := by
  have hne : v - u ≠ 0 := by linarith
  simp only [rescaleMap, rescaleMapInv]
  rw [div_mul_cancel₀ _ hne]
  ring

/-- The rescaling sends `[u, v)` onto `[0, 1)`. -/
theorem rescaleMap_mem {u v x : ℝ} (h : u < v) :
    rescaleMap u v x ∈ Set.Ico (0 : ℝ) 1 ↔ x ∈ Set.Ico u v := by
  have hpos : (0 : ℝ) < v - u := by linarith
  constructor
  · rintro ⟨h1, h2⟩
    simp only [rescaleMap] at h1 h2
    rw [div_lt_one hpos] at h2
    rw [div_nonneg_iff] at h1
    rcases h1 with h1 | h1
    · exact ⟨by linarith, by linarith⟩
    · linarith [h1.2, hpos]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · exact div_nonneg (by linarith) (le_of_lt hpos)
    · rw [rescaleMap, div_lt_one hpos]
      linarith

/-- The rescaled restriction of a function to `[u, v)`. -/
noncomputable def rescaleFun (u v : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun y => rescaleMap u v (f (rescaleMapInv u v y))

/-- **`mkIET1` at a point of `[0,1)` is the translation of its cell.** -/
theorem mkIET1_apply {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n))
    (hl : (∑ i, lam i) = 1) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) (∑ i, (lam i : ℝ))) :
    mkIET1 lam π hl x
      = x + (imageLeft π lam (idx lam x hx.1) - leftEnd lam (idx lam x hx.1)) := by
  have hlink : (mkIET1 lam π hl) x = mkIETFun lam π 0 x := rfl
  rw [hlink, mkIETFun_of_mem _ _ 0 (by simpa using hx), translationVector]
  simp only [sub_zero]

/-- **An invariant initial segment of the permutation gives an invariant initial interval.** -/
theorem imageLeft_add_le_of_invariant {n : ℕ} {lam : Fin n → ℝ≥0}
    {π : Equiv.Perm (Fin n)} {k i : Fin n}
    (hklt : k.val + 1 < n) (hinv : ∀ m : Fin n, m ≤ k → π m ≤ k) (hik : i ≤ k) :
    imageLeft π lam i + (lam i : ℝ) ≤ leftEnd lam ⟨k.val + 1, hklt⟩ := by
  classical
  -- `π` preserves `{m | m ≤ k}` both ways
  have hiff : ∀ m : Fin n, π m ≤ k ↔ m ≤ k := by
    have hS : (Finset.univ.filter (fun m : Fin n => m ≤ k)).image π
        = Finset.univ.filter (fun m : Fin n => m ≤ k) := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro y hy
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
        exact hinv m hm
      · rw [Finset.card_image_of_injective _ π.injective]
    intro m
    refine ⟨fun h => ?_, hinv m⟩
    have hmem : π m ∈ (Finset.univ.filter (fun m : Fin n => m ≤ k)).image π := by
      rw [hS]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h
    obtain ⟨m', hm', hm'm⟩ := Finset.mem_image.mp hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm'
    rw [← π.injective hm'm]
    exact hm'
  -- the relevant indices are all `≤ k`
  have hsub : Finset.univ.filter (fun m : Fin n => π m < π i) ∪ {i}
      ⊆ Finset.univ.filter (fun m : Fin n => m ≤ k) := by
    intro m hm
    rcases Finset.mem_union.mp hm with hm | hm
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
      exact (hiff m).mp (le_of_lt (hm.trans_le ((hiff i).mpr hik)))
    · rw [Finset.mem_singleton] at hm
      rw [hm]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hik
  have hnotmem : i ∉ Finset.univ.filter (fun m : Fin n => π m < π i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_irrefl _
  have hsum : imageLeft π lam i + (lam i : ℝ)
      = ∑ m ∈ Finset.univ.filter (fun m : Fin n => π m < π i) ∪ {i}, (lam m : ℝ) := by
    rw [Finset.sum_union (Finset.disjoint_singleton_right.mpr hnotmem), Finset.sum_singleton]
    rfl
  rw [hsum, leftEnd, show Finset.univ.filter (fun m : Fin n => m < ⟨k.val + 1, hklt⟩)
      = Finset.univ.filter (fun m : Fin n => m ≤ k) from by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def]
    omega]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => (lam m).coe_nonneg)

/-- **The permutation of an exchange with no invariant initial interval is irreducible.**  This is
the form of irreducibility Masur–Veech and Veech's rigidity need, obtained from the geometric
statement (no invariant initial segment `[0, leftEnd λ k)`) used in Lemma 3.2. -/
theorem irreduciblePerm_of_no_invariant_cut {n : ℕ} [NeZero n] {lam : Fin n → ℝ≥0}
    (hpos : Positive lam) (hl : (∑ i, lam i) = 1) (π : Equiv.Perm (Fin n))
    (h : ∀ k : Fin n, k ≠ 0 →
      ¬ ∀ x ∈ Set.Ico (0 : ℝ) 1, x < leftEnd lam k → mkIET1 lam π hl x < leftEnd lam k) :
    IsIrreduciblePerm π := by
  intro k hinv
  by_cases hkl : k.val + 1 = n
  · intro i
    rw [Fin.le_def]
    have := i.isLt
    omega
  · exfalso
    have hklt : k.val + 1 < n := by have := k.isLt; omega
    set k' : Fin n := ⟨k.val + 1, hklt⟩ with hk'
    have hk'0 : k' ≠ 0 := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_zero, hk']
      omega
    refine h k' hk'0 ?_
    intro x hx hxc
    have hsum1 : (∑ i, (lam i : ℝ)) = 1 := by
      rw [← NNReal.coe_sum]; exact_mod_cast hl
    have hx' : x ∈ Set.Ico (0 : ℝ) (∑ i, (lam i : ℝ)) := by
      rw [hsum1]; exact hx
    set i := idx lam x hx'.1 with hi
    have hxi : leftEnd lam i ≤ x := idx_mem lam x hx'.1
    have hlt : x < leftEnd lam k' := hxc
    -- the cell index is `≤ k`
    have hik : i ≤ k := by
      by_contra hcon
      rw [not_le] at hcon
      rw [Fin.lt_def] at hcon
      have hle : k' ≤ i := by
        rw [Fin.le_def]
        have h2 : k'.val = k.val + 1 := rfl
        omega
      have h1 : leftEnd lam k' ≤ leftEnd lam i := by
        rcases lt_or_eq_of_le hle with h2 | h2
        · exact le_of_lt (leftEnd_lt_leftEnd hpos h2)
        · rw [h2]
      linarith
    -- the image of the cell ends before `leftEnd λ k'`
    have hkey := imageLeft_add_le_of_invariant (lam := lam) hklt hinv hik
    have hupper : x < leftEnd lam i + (lam i : ℝ) := by
      have h2 : x < upperEnd lam i := lt_upperEnd_idx lam hx'
      rw [upperEnd_eq] at h2
      exact h2
    have happ := mkIET1_apply lam π hl hx'
    rw [happ] at *
    linarith

/-- **The same criterion, on a datum.**  An exchange presented by a datum has an irreducible
permutation as soon as no initial interval `[0, leftEnd D.lam k)` with `k ≠ 0` is mapped into itself
— the statement is made on the datum, so the marked points are not forgotten. -/
theorem IETDatum.irreduciblePerm_of_no_invariant_cut {n : ℕ} [NeZero n] (D : IETDatum n)
    (h : ∀ k : Fin n, k ≠ 0 →
      ¬ ∀ x ∈ Set.Ico (0 : ℝ) 1, x < leftEnd D.lam k → D.toFun x < leftEnd D.lam k) :
    IsIrreduciblePerm D.π := by
  have hlNN : (∑ i, D.lam i) = 1 := by
    rw [← NNReal.coe_inj, NNReal.coe_sum, D.sum_lam, NNReal.coe_one]
  have hposNN : ∀ i : Fin n, 0 < D.lam i := by
    intro i
    rw [← NNReal.coe_pos, IETDatum.lam, simplexMap]
    split_ifs with hh
    · rw [Real.coe_toNNReal _ (by linarith [D.sum_lt_one])]
      linarith [D.sum_lt_one]
    · rw [Real.coe_toNNReal _ (le_of_lt (D.pos _))]
      exact D.pos _
  refine @_root_.irreduciblePerm_of_no_invariant_cut n _ D.lam hposNN hlNN D.π
    (fun k hk0 hinv => h k hk0 ?_)
  intro x hx hxc
  have hlt := hinv x hx hxc
  have hlink : (mkIET1 D.lam D.π hlNN) x = mkIETFun D.lam D.π 0 x := rfl
  rw [hlink] at hlt
  simpa only [IETDatum.toFun] using hlt

/-- **A splitting point of `E` inside a fixed cell of `D` is fixed by `D`.**  This is the input that
turns the `g`-side of a pair-splitting point into a *fixed* point, hence into a marked point of the
list (the list contains the `f`-preimages of the marked points of `g`). -/
theorem mark_fixed_of_inFixedCell {d e : ℕ} [NeZero d] [NeZero e] (D : IETDatum d) (E : IETDatum e)
    (j : Fin (e + 1)) (h : E.InFixedCell D j) : D.toFun (E.mark j) = E.mark j := by
  obtain ⟨l, hl, h1, h2⟩ := h
  exact D.isFixedCell_apply hl ⟨h1, h2⟩

/-- **The pair-splitting points are marked points.**  If the list `s` contains the marked points of
`D` and the `D`-preimages of the marked points of `E` (which is exactly what the marked list of
`exists_markedList` does), then every pair-splitting point is one of the `s i`.

The `f`-side is immediate; the `g`-side uses `mark_fixed_of_inFixedCell`: a splitting point of `E`
lying in a fixed cell of `D` is fixed by `D`, so its `D`-preimage is itself, hence an `s`-point. -/
theorem pairSplitting_mem_markedList {d e n : ℕ} [NeZero d] [NeZero e]
    {D : IETDatum d} {E : IETDatum e} {s : Fin (n + 1) → ℝ}
    (hD : ∀ k : Fin (d + 1), ∃ i : Fin (n + 1), s i = D.mark k)
    (hE : ∀ j : Fin (e + 1), ∃ i : Fin (n + 1), s i = D.toIET⁻¹ (E.mark j))
    {x : ℝ} (hx : IsPairSplitting D E x) : ∃ i : Fin (n + 1), s i = x := by
  rcases hx with rfl | rfl | ⟨k, -, rfl, -⟩ | ⟨j, -, rfl, hf⟩
  · obtain ⟨i, hi⟩ := hD 0
    exact ⟨i, by rw [hi, IETDatum.mark_zero]⟩
  · obtain ⟨i, hi⟩ := hD (Fin.last d)
    exact ⟨i, by rw [hi, IETDatum.mark_last]⟩
  · exact hD k
  · -- `x = E.mark j` lies in a fixed cell of `D`, so `D` fixes it, so its `D`-preimage is itself
    obtain ⟨i, hi⟩ := hE j
    have hfix : D.toFun (E.mark j) = E.mark j := mark_fixed_of_inFixedCell D E j hf
    have hpre : D.toIET⁻¹ (E.mark j) = E.mark j := by
      refine D.toIET.injective ?_
      rw [IET.apply_symm_apply']
      exact hfix.symm
    exact ⟨i, by rw [hi, hpre]⟩

/-- **The left end of the image is strictly increasing in the image order.**  If all the cell
lengths are positive, then `ρ j₁ < ρ j₂` forces `listImageLeft ρ S j₁ < listImageLeft ρ S j₂`: the
set of indices before `j₁` in the image order is a strict subset of the set before `j₂` (the index
`j₁` itself is in the second and not the first), and the added length is positive.

This is the combinatorial half of "the `ρ`-values on a block are consecutive": once the block
is characterized by an *interval of image coordinates* (`P i₀ ≤ P j < P i₀ + L`), monotonicity of
`P` in the `ρ`-value turns that into an interval of `ρ`-values. -/
theorem listImageLeft_lt {n : ℕ} {ρ : Equiv.Perm (Fin n)} {S : Fin (n + 1) → ℝ}
    (hpos : ∀ j : Fin n, 0 < S j.succ - S j.castSucc) {j₁ j₂ : Fin n} (h : ρ j₁ < ρ j₂) :
    listImageLeft ρ S j₁ < listImageLeft ρ S j₂ := by
  classical
  set A := Finset.univ.filter (fun j : Fin n => ρ j < ρ j₁) with hA
  set B := Finset.univ.filter (fun j : Fin n => ρ j < ρ j₂) with hB
  have hsub : A ⊆ B := by
    intro j hj
    simp only [hA, hB, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact lt_trans hj h
  have hmemB : j₁ ∈ B := by
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  have hnotA : j₁ ∉ A := by
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_irrefl _
  have hsplit := Finset.sum_sdiff (f := fun j : Fin n => S j.succ - S j.castSucc) hsub
  have hpos' : 0 < ∑ j ∈ B \ A, (S j.succ - S j.castSucc) := by
    refine Finset.sum_pos (fun j _ => hpos j) ?_
    exact ⟨j₁, Finset.mem_sdiff.mpr ⟨hmemB, hnotA⟩⟩
  have hAB : listImageLeft ρ S j₁ = ∑ j ∈ A, (S j.succ - S j.castSucc) := rfl
  have hBB : listImageLeft ρ S j₂ = ∑ j ∈ B, (S j.succ - S j.castSucc) := rfl
  rw [hAB, hBB]
  linarith

/-! ### Transporting a word along a conjugacy of the generators

Lemma 3.4 applies Theorem 2.6 to the **rescaled** pair `(g̃f̃, g̃)` on a block and then transports
the word back to the block.  The transport only uses that `φ = rescaleMapInv u v` conjugates each
generator, and its inverse, to the rescaled one. -/

/-- **The word transport.**  If `φ : ℝ → ℝ` conjugates the two generators of `(F, G)` to those of
`(F', G')` — and the same for the inverses — then it conjugates every evaluated word.  No
hypothesis on `φ` itself is needed: the identities `F (φ y) = φ (F' y)` and
`F⁻¹ (φ y) = φ (F'⁻¹ y)`, applied to the words produced by the induction, already say everything. -/
theorem evalWord_conj_apply {F G F' G' : IET 0 1} {φ : ℝ → ℝ}
    (hF : ∀ y ∈ Set.Ico (0 : ℝ) 1, F (φ y) = φ (F' y))
    (hFi : ∀ y ∈ Set.Ico (0 : ℝ) 1, F⁻¹ (φ y) = φ (F'⁻¹ y))
    (hG : ∀ y ∈ Set.Ico (0 : ℝ) 1, G (φ y) = φ (G' y))
    (hGi : ∀ y ∈ Set.Ico (0 : ℝ) 1, G⁻¹ (φ y) = φ (G'⁻¹ y)) (w : FreeGroup Gen) :
    ∀ y ∈ Set.Ico (0 : ℝ) 1, (evalWord w F G) (φ y) = φ ((evalWord w F' G') y) := by
  refine FreeGroup.induction_on (C := fun w => ∀ y ∈ Set.Ico (0 : ℝ) 1,
    (evalWord w F G) (φ y) = φ ((evalWord w F' G') y)) w ?_ ?_ ?_ ?_
  · intro y _
    rw [evalWord_one, IET.one_apply, evalWord_one, IET.one_apply]
  · intro i y _
    fin_cases i
    · exact hF y ‹_›
    · exact hG y ‹_›
  · intro i _ y _
    fin_cases i
    · exact hFi y ‹_›
    · exact hGi y ‹_›
  · intro u v hu hv y hy
    have hy' : (evalWord v F' G') y ∈ Set.Ico (0 : ℝ) 1 := (evalWord v F' G').isIET.mapsTo hy
    rw [evalWord_mul, IET.mul_apply, hv y hy,
      show (evalWord (u * v) F' G') y = (evalWord u F' G') ((evalWord v F' G') y) from by
        rw [evalWord_mul, IET.mul_apply]]
    exact hu _ hy'

section LeftEnd

variable {n : ℕ}

/-- The `ℕ`-indexed extension of a length vector (zero past the end). -/
noncomputable def lamNat (lam : Fin n → ℝ≥0) (m : ℕ) : ℝ :=
  if h : m < n then (lam ⟨m, h⟩ : ℝ) else 0

theorem lamNat_of_lt {lam : Fin n → ℝ≥0} {m : ℕ} (h : m < n) : lamNat lam m = (lam ⟨m, h⟩ : ℝ) :=
  dif_pos h

/-- The `ℕ`-indexed extension of the `i`-th cut, as a summand. -/
noncomputable def leftEndNat (lam : Fin n → ℝ≥0) (i : Fin n) (m : ℕ) : ℝ :=
  if h : m < n then (if (⟨m, h⟩ : Fin n) < i then (lam ⟨m, h⟩ : ℝ) else 0) else 0

theorem leftEndNat_of_lt {lam : Fin n → ℝ≥0} {i : Fin n} {m : ℕ} (hm : m < n) :
    leftEndNat lam i m = if (⟨m, hm⟩ : Fin n) < i then (lam ⟨m, hm⟩ : ℝ) else 0 :=
  dif_pos hm

/-- `leftEnd` as a sum over `Finset.range`. -/
theorem leftEnd_eq_sum_range (lam : Fin n → ℝ≥0) (i : Fin n) :
    leftEnd lam i = ∑ m ∈ Finset.range i.val, lamNat lam m := by
  have h1 : leftEnd lam i = ∑ m ∈ Finset.range n, leftEndNat lam i m := by
    rw [leftEnd, Finset.sum_filter]
    rw [show (∑ j : Fin n, (if j < i then (lam j : ℝ) else 0))
        = ∑ j : Fin n, leftEndNat lam i ↑j from
      Finset.sum_congr rfl (fun j _ => by rw [leftEndNat_of_lt j.isLt])]
    rw [Fin.sum_univ_eq_sum_range (leftEndNat lam i)]
  have hsub : Finset.range i.val ⊆ Finset.range n := by
    intro m hm
    simp only [Finset.mem_range] at hm ⊢
    omega
  have hvanish : ∀ m ∈ Finset.range n, m ∉ Finset.range i.val → leftEndNat lam i m = 0 := by
    intro m hm hnot
    rw [Finset.mem_range] at hm hnot
    rw [leftEndNat_of_lt hm, if_neg (by simp only [Fin.lt_def]; omega)]
  rw [h1, ← Finset.sum_subset hsub hvanish]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mem_range] at hm
  rw [leftEndNat_of_lt (by omega), if_pos (by simp only [Fin.lt_def]; exact hm),
    lamNat_of_lt (by omega)]

end LeftEnd

section Block

variable {n : ℕ}

/-- The total length of the block of cells `k, …, l - 1`. -/
noncomputable def blockMass (lam : Fin n → ℝ≥0) (k : ℕ) {l : ℕ} (hln : l ≤ n) : ℝ :=
  ∑ j : Fin (l - k), (lam ⟨k + j.val, by omega⟩ : ℝ)

theorem blockMass_pos {lam : Fin n → ℝ≥0} (hpos : Positive lam) (k : ℕ) {l : ℕ} (hkl : k < l)
    (hln : l ≤ n) : 0 < blockMass lam k hln := by
  refine Finset.sum_pos (fun j _ => hpos _) ?_
  rw [Finset.univ_nonempty_iff]
  exact ⟨⟨0, by omega⟩⟩

/-- The length vector of the block `k, …, l - 1`, rescaled to total mass `1`. -/
noncomputable def blockLam (lam : Fin n → ℝ≥0) (k : ℕ) {l : ℕ} (hkl : k < l) (hln : l ≤ n)
    (hpos : Positive lam) : Fin (l - k) → ℝ≥0 :=
  fun j => ⟨(lam ⟨k + j.val, by omega⟩ : ℝ) / blockMass lam k hln,
    div_nonneg (lam _).coe_nonneg (le_of_lt (blockMass_pos hpos k hkl hln))⟩

theorem blockLam_coe (lam : Fin n → ℝ≥0) (k : ℕ) {l : ℕ} (hkl : k < l) (hln : l ≤ n)
    (hpos : Positive lam) (j : Fin (l - k)) :
    (blockLam lam k hkl hln hpos j : ℝ) = (lam ⟨k + j.val, by omega⟩ : ℝ) / blockMass lam k hln :=
  rfl

/-- The rescaled lengths of the block add up to `1`. -/
theorem blockLam_sum (lam : Fin n → ℝ≥0) (k : ℕ) {l : ℕ} (hkl : k < l) (hln : l ≤ n)
    (hpos : Positive lam) : (∑ j : Fin (l - k), blockLam lam k hkl hln hpos j) = 1 := by
  rw [← NNReal.coe_inj]
  simp only [blockLam_coe, NNReal.coe_sum, NNReal.coe_one, ← Finset.sum_div]
  rw [div_eq_one_iff_eq (ne_of_gt (blockMass_pos hpos k hkl hln))]
  simp only [blockMass]

/-- The permutation induced by `π` on the invariant block of indices `{k, …, l - 1}`, shifted so
that it acts on `Fin (l - k)`. -/
noncomputable def blockPerm (π : Equiv.Perm (Fin n)) (k : ℕ) {l : ℕ} (hkl : k < l) (hln : l ≤ n)
    (hstab : ∀ i : Fin n, (i.val < k ↔ (π i).val < k) ∧ (i.val < l ↔ (π i).val < l)) :
    Equiv.Perm (Fin (l - k)) where
  toFun j := ⟨(π ⟨k + j.val, by omega⟩).val - k, by
    have h2 : k + j.val < l := by omega
    have h4 : (π ⟨k + j.val, by omega⟩).val < l := (hstab _).2.mp h2
    have h1 : ¬ k + j.val < k := by omega
    have h3 : ¬ (π ⟨k + j.val, by omega⟩).val < k := fun hc => h1 ((hstab _).1.mpr hc)
    omega⟩
  invFun j := ⟨(π.symm ⟨k + j.val, by omega⟩).val - k, by
    have h2 : k + j.val < l := by omega
    have h4 : (π.symm ⟨k + j.val, by omega⟩).val < l := by
      have h := (hstab (π.symm ⟨k + j.val, by omega⟩)).2
      simp only [Equiv.apply_symm_apply] at h
      exact h.mpr h2
    have h1 : ¬ k + j.val < k := by omega
    have h3 : ¬ (π.symm ⟨k + j.val, by omega⟩).val < k := by
      intro hc
      have h := (hstab (π.symm ⟨k + j.val, by omega⟩)).1
      simp only [Equiv.apply_symm_apply] at h
      exact h1 (h.mp hc)
    omega⟩
  left_inv j := by
    refine Fin.ext ?_
    have h2 : k + j.val < l := by omega
    have h4 : (π ⟨k + j.val, by omega⟩).val < l := (hstab _).2.mp h2
    have h1 : ¬ k + j.val < k := by omega
    have h3 : ¬ (π ⟨k + j.val, by omega⟩).val < k := fun hc => h1 ((hstab _).1.mpr hc)
    have hk : k + ((π ⟨k + j.val, by omega⟩).val - k) = (π ⟨k + j.val, by omega⟩).val := by omega
    simp only [Fin.val_mk]
    rw [show (⟨k + ((π ⟨k + j.val, by omega⟩).val - k), by omega⟩ : Fin n)
      = π ⟨k + j.val, by omega⟩ from Fin.ext hk]
    simp only [Equiv.symm_apply_apply]
    omega
  right_inv j := by
    refine Fin.ext ?_
    have h2 : k + j.val < l := by omega
    have h4 : (π.symm ⟨k + j.val, by omega⟩).val < l := by
      have h := (hstab (π.symm ⟨k + j.val, by omega⟩)).2
      simp only [Equiv.apply_symm_apply] at h
      exact h.mpr h2
    have h1 : ¬ k + j.val < k := by omega
    have h3 : ¬ (π.symm ⟨k + j.val, by omega⟩).val < k := by
      intro hc
      have h := (hstab (π.symm ⟨k + j.val, by omega⟩)).1
      simp only [Equiv.apply_symm_apply] at h
      exact h1 (h.mp hc)
    have hk : k + ((π.symm ⟨k + j.val, by omega⟩).val - k) = (π.symm ⟨k + j.val, by omega⟩).val :=
      by omega
    simp only [Fin.val_mk]
    rw [show (⟨k + ((π.symm ⟨k + j.val, by omega⟩).val - k), by omega⟩ : Fin n)
      = π.symm ⟨k + j.val, by omega⟩ from Fin.ext hk]
    simp only [Equiv.apply_symm_apply]
    omega

end Block

/-- **The left end of a cell of the block, in the original coordinates.**  A cell of the block
whose lengths are rescaled to total mass `1` starts, in the original interval, at the left end of
the block plus the rescaled position times the mass of the block. -/
theorem leftEnd_blockLam {n : ℕ} {lam : Fin n → ℝ≥0} {k l : ℕ} (hpos : Positive lam)
    (hkl : k < l) (hln : l ≤ n) (j : Fin (l - k)) :
    leftEnd lam ⟨k + j.val, by omega⟩
      = leftEnd lam ⟨k, by omega⟩
        + blockMass lam k hln * leftEnd (blockLam lam k hkl hln hpos) j := by
  have hkj : k + j.val < n := by omega
  rw [leftEnd_eq_sum_range lam ⟨k + j.val, hkj⟩, leftEnd_eq_sum_range lam ⟨k, by omega⟩,
    Finset.sum_range_add (lamNat lam) k j.val]
  congr 1
  rw [leftEnd_eq_sum_range (blockLam lam k hkl hln hpos) j, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.mem_range] at hx
  rw [lamNat_of_lt (by omega), lamNat_of_lt (by omega), blockLam_coe]
  have hm : blockMass lam k hln ≠ 0 := ne_of_gt (blockMass_pos hpos k hkl hln)
  field_simp

section Extra

variable {n : ℕ}

/-- Monotonicity of the left ends. -/
theorem leftEnd_le_leftEnd {lam : Fin n → ℝ≥0} {i i' : Fin n} (h : i ≤ i') :
    leftEnd lam i ≤ leftEnd lam i' := by
  rw [leftEnd, leftEnd]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => (lam j).coe_nonneg)
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  rw [Fin.lt_def] at hj ⊢
  rw [Fin.le_def] at h
  omega

end Extra

/-! ### The restriction of an exchange to an invariant block -/

namespace RescaleBlock

/-! ### Prefix sums, in the form of sums over `Fin n` -/

theorem leftEnd_eq_filter {n : ℕ} (lam : Fin n → ℝ≥0) (i : Fin n) :
    leftEnd lam i = ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), (lam j : ℝ) := by
  unfold leftEnd
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]

/-! ### The block permutation -/

theorem blockPerm_apply_val {n : ℕ} {π : Equiv.Perm (Fin n)} {k l : ℕ} (hkl : k < l) (hln : l ≤ n)
    (hstab : ∀ i : Fin n, (i.val < k ↔ (π i).val < k) ∧ (i.val < l ↔ (π i).val < l))
    (t : Fin (l - k)) :
    ((blockPerm π k hkl hln hstab) t).val = (π ⟨k + t.val, by omega⟩).val - k := rfl

theorem blockPerm_lt_iff {n : ℕ} {π : Equiv.Perm (Fin n)} {k l : ℕ} (hkl : k < l) (hln : l ≤ n)
    (hstab : ∀ i : Fin n, (i.val < k ↔ (π i).val < k) ∧ (i.val < l ↔ (π i).val < l))
    (t t' : Fin (l - k)) :
    ((blockPerm π k hkl hln hstab) t < (blockPerm π k hkl hln hstab) t')
      ↔ (π ⟨k + t.val, by omega⟩ < π ⟨k + t'.val, by omega⟩) := by
  have hge : ∀ t : Fin (l - k), k ≤ (π ⟨k + t.val, by omega⟩).val := by
    intro t
    have h1 : ¬ ((⟨k + t.val, by omega⟩ : Fin n).val < k) := by
      simp only [Fin.val_mk]; omega
    have h2 : ¬ ((π ⟨k + t.val, by omega⟩).val < k) := fun hc => h1 ((hstab _).1.mpr hc)
    omega
  rw [Fin.lt_def, Fin.lt_def, blockPerm_apply_val hkl hln hstab t,
    blockPerm_apply_val hkl hln hstab t']
  have h1 := hge t
  have h2 := hge t'
  constructor <;> intro h <;> omega

/-- **The image start of a cell of the block, in the original coordinates.**  (Auxiliary form
without the unused ambient hypothesis `hl`.) -/
theorem imageLeft_blockPerm_aux {n : ℕ} {lam : Fin n → ℝ≥0} {π : Equiv.Perm (Fin n)}
    {k l : ℕ} (hpos : Positive lam) (hkl : k < l) (hln : l ≤ n)
    (hstab : ∀ i : Fin n, (i.val < k ↔ (π i).val < k) ∧ (i.val < l ↔ (π i).val < l))
    (j : Fin (l - k)) :
    imageLeft π lam ⟨k + j.val, by omega⟩ - leftEnd lam ⟨k, by omega⟩
      = blockMass lam k hln
        * imageLeft (blockPerm π k hkl hln hstab) (blockLam lam k hkl hln hpos) j := by
  classical
  have hjlt : k + j.val < l := by have := j.isLt; omega
  -- ### the block part, as the image of the block indices
  have hset : (Finset.univ.filter (fun t : Fin (l - k) =>
        (blockPerm π k hkl hln hstab) t < (blockPerm π k hkl hln hstab) j)).image
        (fun t => (⟨k + t.val, by omega⟩ : Fin n))
      = Finset.univ.filter (fun m : Fin n =>
          ¬ m.val < k ∧ π m < π ⟨k + j.val, by omega⟩) := by
    ext m
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨by simp only [Fin.val_mk]; omega, ?_⟩
      exact (blockPerm_lt_iff hkl hln hstab t j).mp ht
    · rintro ⟨hmk, hmpi⟩
      have hmge : k ≤ m.val := by omega
      have hmlt : m.val < l := by
        have h2 : (π m).val < l := by
          rw [Fin.lt_def] at hmpi
          exact lt_trans hmpi ((hstab _).2.mp hjlt)
        exact (hstab m).2.mpr h2
      refine ⟨⟨m.val - k, by omega⟩, ?_, ?_⟩
      · rw [blockPerm_lt_iff hkl hln hstab]
        rw [show (⟨k + (⟨m.val - k, by omega⟩ : Fin (l - k)).val, by omega⟩ : Fin n) = m from
          Fin.ext (by simp only [Fin.val_mk]; omega)]
        exact hmpi
      · exact Fin.ext (by simp only [Fin.val_mk]; omega)
  -- ### the pointwise splitting identity
  have hpt : ∀ m : Fin n, (if π m < π ⟨k + j.val, by omega⟩ then (lam m : ℝ) else 0)
      = (if m.val < k then (lam m : ℝ) else 0)
        + (if ¬ m.val < k ∧ π m < π ⟨k + j.val, by omega⟩ then (lam m : ℝ) else 0) := by
    intro m
    by_cases h1 : m.val < k
    · have h2 : π m < π ⟨k + j.val, by omega⟩ := by
        rw [Fin.lt_def]
        have h3 : (π m).val < k := (hstab m).1.mp h1
        have h4 : k ≤ (π ⟨k + j.val, by omega⟩).val := by
          have h5 : ¬ ((⟨k + j.val, by omega⟩ : Fin n).val < k) := by
            simp only [Fin.val_mk]; omega
          have h6 : ¬ ((π ⟨k + j.val, by omega⟩).val < k) := fun hc => h5 ((hstab _).1.mpr hc)
          omega
        omega
      simp [h1, h2]
    · by_cases h2 : π m < π ⟨k + j.val, by omega⟩ <;> simp [h1, h2]
  -- ### the split of the image-left sum
  have hsplit : imageLeft π lam ⟨k + j.val, by omega⟩
      = (∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val < k), (lam m : ℝ))
        + ∑ m ∈ Finset.univ.filter (fun m : Fin n =>
            ¬ m.val < k ∧ π m < π ⟨k + j.val, by omega⟩), (lam m : ℝ) := by
    rw [imageLeft, Finset.sum_filter]
    rw [show (∑ m : Fin n, (if π m < π ⟨k + j.val, by omega⟩ then (lam m : ℝ) else 0))
        = ∑ m : Fin n, ((if m.val < k then (lam m : ℝ) else 0)
          + (if ¬ m.val < k ∧ π m < π ⟨k + j.val, by omega⟩ then (lam m : ℝ) else 0)) from
      Finset.sum_congr rfl (fun m _ => hpt m)]
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  -- ### the block sum
  have hS : ∑ m ∈ Finset.univ.filter (fun m : Fin n =>
        ¬ m.val < k ∧ π m < π ⟨k + j.val, by omega⟩), (lam m : ℝ)
      = blockMass lam k hln * ∑ t ∈ Finset.univ.filter (fun t : Fin (l - k) =>
          (blockPerm π k hkl hln hstab) t < (blockPerm π k hkl hln hstab) j),
          (blockLam lam k hkl hln hpos t : ℝ) := by
    have h1 : ∑ m ∈ Finset.univ.filter (fun m : Fin n =>
          ¬ m.val < k ∧ π m < π ⟨k + j.val, by omega⟩), (lam m : ℝ)
        = ∑ t ∈ Finset.univ.filter (fun t : Fin (l - k) =>
            (blockPerm π k hkl hln hstab) t < (blockPerm π k hkl hln hstab) j),
            (lam ⟨k + t.val, by omega⟩ : ℝ) := by
      rw [← hset]
      refine Finset.sum_image (fun a _ b _ hab => ?_)
      simp only [Fin.mk.injEq] at hab
      exact Fin.ext (by omega)
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have hc := blockLam_coe lam k hkl hln hpos t
    have hM : blockMass lam k hln ≠ 0 := ne_of_gt (blockMass_pos hpos k hkl hln)
    rw [hc]
    field_simp
  rw [hsplit, hS, leftEnd_eq_filter lam ⟨k, by omega⟩, imageLeft]
  ring

/-! ### The mass of the block and the prefix sums -/

theorem sum_range_lamNat_nonneg {n : ℕ} (lam : Fin n → ℝ≥0) (m : ℕ) : 0 ≤ lamNat lam m := by
  unfold lamNat
  split_ifs with h
  · exact (lam _).coe_nonneg
  · exact le_refl 0

theorem sum_range_lamNat_mono {n : ℕ} (lam : Fin n → ℝ≥0) {a b : ℕ} (hab : a ≤ b) :
    ∑ m ∈ Finset.range a, lamNat lam m ≤ ∑ m ∈ Finset.range b, lamNat lam m := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => sum_range_lamNat_nonneg lam m)
  intro x hx
  simp only [Finset.mem_range] at hx ⊢
  omega

theorem sum_range_lamNat_eq_total {n : ℕ} (lam : Fin n → ℝ≥0) :
    ∑ m ∈ Finset.range n, lamNat lam m = ∑ i, (lam i : ℝ) := by
  rw [← Fin.sum_univ_eq_sum_range (lamNat lam) n]
  exact Finset.sum_congr rfl (fun i _ => lamNat_of_lt i.isLt)

theorem leftEnd_add_blockMass {n : ℕ} {lam : Fin n → ℝ≥0} {k l : ℕ} (hkl : k < l) (hln : l ≤ n) :
    leftEnd lam ⟨k, by omega⟩ + blockMass lam k hln = ∑ m ∈ Finset.range l, lamNat lam m := by
  have hsub : k + (l - k) = l := Nat.add_sub_of_le (le_of_lt hkl)
  have hsplit : ∑ m ∈ Finset.range l, lamNat lam m
      = ∑ m ∈ Finset.range k, lamNat lam m
        + ∑ t ∈ Finset.range (l - k), lamNat lam (k + t) := by
    conv_lhs => rw [← hsub]
    rw [Finset.sum_range_add]
  rw [hsplit, leftEnd_eq_sum_range lam ⟨k, by omega⟩]
  congr 1
  rw [blockMass, ← Fin.sum_univ_eq_sum_range (fun t => lamNat lam (k + t)) (l - k)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (lamNat_of_lt (by have := i.isLt; omega)).symm

/-- **The cell of the rescaled point is the shifted cell of the original point**, for a block `I`
of `n` cells (the instance `NeZero (I.l - I.k)` comes from the structure, so no statement about a
block carries it).  Auxiliary form without the unused ambient hypothesis `hl`. -/
theorem idx_rescaleMap_aux {n : ℕ} [NeZero n] {lam : Fin n → ℝ≥0}
    (I : BlockIdx n) (hpos : Positive lam) (x : ℝ) (hx0 : 0 ≤ x)
    (hx : x ∈ Set.Ico (leftEnd lam I.kFin)
      (leftEnd lam I.kFin + blockMass lam I.k I.hln))
    (hj : 0 ≤ rescaleMap (leftEnd lam I.kFin)
      (leftEnd lam I.kFin + blockMass lam I.k I.hln) x) :
    (idx (blockLam lam I.k I.hkl I.hln hpos)
        (rescaleMap (leftEnd lam I.kFin)
          (leftEnd lam I.kFin + blockMass lam I.k I.hln) x) hj).val
      = (idx lam x hx0).val - I.k := by
  -- the numeric indices of the block, for the computation below
  set k := I.k
  set l := I.l
  have hkl : k < l := I.hkl
  have hln : l ≤ n := I.hln
  classical
  set M := blockMass lam k hln with hMdef
  set L := leftEnd lam ⟨k, by omega⟩ with hLdef
  have hM : 0 < M := by rw [hMdef]; exact blockMass_pos hpos k hkl hln
  have hLM : L + M = ∑ m ∈ Finset.range l, lamNat lam m := by
    rw [hLdef, hMdef]; exact leftEnd_add_blockMass hkl hln
  -- `x` lies in the total interval
  have hx_tot : x ∈ Set.Ico (0 : ℝ) (∑ i, (lam i : ℝ)) := by
    refine ⟨hx0, lt_of_lt_of_le hx.2 ?_⟩
    rw [hLM, ← sum_range_lamNat_eq_total lam]
    exact sum_range_lamNat_mono lam hln
  -- the cell of `x` is a cell of the block, and `j` is its index in the block
  have hik : k ≤ (idx lam x hx0).val := by
    have h := le_idx lam x hx0 (i := ⟨k, by omega⟩) (by rw [hLdef] at *; exact hx.1)
    simpa only [Fin.le_def, Fin.val_mk] using h
  have hilt : (idx lam x hx0).val < l := by
    by_contra hcon
    have hmono : (∑ m ∈ Finset.range l, lamNat lam m)
        ≤ ∑ m ∈ Finset.range (idx lam x hx0).val, lamNat lam m :=
      sum_range_lamNat_mono lam (by omega)
    have h3 : leftEnd lam (idx lam x hx0) ≤ x := idx_mem lam x hx0
    rw [leftEnd_eq_sum_range] at h3
    linarith [hx.2]
  set j : Fin (l - k) := ⟨(idx lam x hx0).val - k, by omega⟩ with hjdef
  have hjeq : (idx lam x hx0).val = k + j.val := by
    rw [hjdef]; simp only [Fin.val_mk]; omega
  -- the two inequalities locating the rescaled point in the `j`-th cell of the block
  have hle1 : leftEnd (blockLam lam k hkl hln hpos) j ≤ rescaleMap L (L + M) x := by
    have h1 : leftEnd lam (idx lam x hx0) = L + M * leftEnd (blockLam lam k hkl hln hpos) j := by
      rw [show (idx lam x hx0) = (⟨k + j.val, by omega⟩ : Fin n) from
        Fin.ext (by simp only [Fin.val_mk]; omega),
        hLdef, hMdef]
      exact leftEnd_blockLam hpos hkl hln j
    have h2 : M * leftEnd (blockLam lam k hkl hln hpos) j ≤ x - L := by
      have := idx_mem lam x hx0
      rw [h1] at this
      linarith
    rw [rescaleMap, show L + M - L = M from by ring, le_div_iff₀ hM]
    linarith
  have hlt2 : rescaleMap L (L + M) x < upperEnd (blockLam lam k hkl hln hpos) j := by
    have h1 : leftEnd lam (idx lam x hx0) = L + M * leftEnd (blockLam lam k hkl hln hpos) j := by
      rw [show (idx lam x hx0) = (⟨k + j.val, by omega⟩ : Fin n) from
        Fin.ext (by simp only [Fin.val_mk]; omega),
        hLdef, hMdef]
      exact leftEnd_blockLam hpos hkl hln j
    have hlam : (lam (idx lam x hx0) : ℝ) = M * (blockLam lam k hkl hln hpos j : ℝ) := by
      rw [show (idx lam x hx0) = (⟨k + j.val, by omega⟩ : Fin n) from
        Fin.ext (by simp only [Fin.val_mk]; omega), hMdef]
      have hc := blockLam_coe lam k hkl hln hpos j
      have hMne : blockMass lam k hln ≠ 0 := by rw [← hMdef]; exact ne_of_gt hM
      rw [hc, mul_comm, div_mul_cancel₀ _ hMne]
    have h2 : x < L + M * leftEnd (blockLam lam k hkl hln hpos) j
        + M * (blockLam lam k hkl hln hpos j : ℝ) := by
      have := lt_upperEnd_idx lam hx_tot
      rw [upperEnd_eq, h1, hlam] at this
      exact this
    rw [upperEnd_eq, rescaleMap, show L + M - L = M from by ring, div_lt_iff₀ hM]
    linarith
  -- conclude by uniqueness of the index
  have hsum : (∑ t, ((blockLam lam k hkl hln hpos) t : ℝ)) = 1 := by
    rw [← NNReal.coe_sum, blockLam_sum lam k hkl hln hpos, NNReal.coe_one]
  have hx'tot : rescaleMap L (L + M) x ∈
      Set.Ico (0 : ℝ) (∑ t, ((blockLam lam k hkl hln hpos) t : ℝ)) := by
    rw [hsum]
    exact (rescaleMap_mem (by linarith : L < L + M)).mpr hx
  have hkey := idx_eq (blockLam lam k hkl hln hpos) hx'tot hle1 hlt2
  rw [hkey, hjdef]

/-- **The restriction of an exchange to an invariant block is the rescaled exchange**, for a block
`I` of `n` cells: on `[leftEnd lam I.kFin, leftEnd lam I.kFin + blockMass lam I.k)` the exchange of
`lam` and `π`, rescaled to `[0, 1)`, is the exchange of the rescaled block lengths and of the block
permutation. -/
theorem mkIET1_rescale_subinterval {n : ℕ} [NeZero n] {lam : Fin n → ℝ≥0}
    {π : Equiv.Perm (Fin n)} (I : BlockIdx n) (hl : (∑ i, lam i) = 1) (hpos : Positive lam)
    (hstab : ∀ i : Fin n, (i.val < I.k ↔ (π i).val < I.k) ∧ (i.val < I.l ↔ (π i).val < I.l)) :
    ∀ x ∈ Set.Ico (leftEnd lam I.kFin)
      (leftEnd lam I.kFin + blockMass lam I.k I.hln),
      rescaleMap (leftEnd lam I.kFin)
          (leftEnd lam I.kFin + blockMass lam I.k I.hln) (mkIET1 lam π hl x)
        = mkIET1 (blockLam lam I.k I.hkl I.hln hpos) (blockPerm π I.k I.hkl I.hln hstab)
            (blockLam_sum lam I.k I.hkl I.hln hpos)
            (rescaleMap (leftEnd lam I.kFin)
              (leftEnd lam I.kFin + blockMass lam I.k I.hln) x) := by
  set k := I.k
  set l := I.l
  have hkl : k < l := I.hkl
  have hln : l ≤ n := I.hln
  intro x hx
  classical
  set M := blockMass lam k hln with hMdef
  set L := leftEnd lam ⟨k, by omega⟩ with hLdef
  have hM : 0 < M := by rw [hMdef]; exact blockMass_pos hpos k hkl hln
  have hMne : M ≠ 0 := ne_of_gt hM
  have hLM : L + M = ∑ m ∈ Finset.range l, lamNat lam m := by
    rw [hLdef, hMdef]; exact leftEnd_add_blockMass hkl hln
  -- `x` and its rescaling lie in the right intervals
  have hx0 : 0 ≤ x := le_trans (leftEnd_nonneg lam ⟨k, by omega⟩) hx.1
  have hx_tot : x ∈ Set.Ico (0 : ℝ) (∑ i, (lam i : ℝ)) := by
    refine ⟨hx0, lt_of_lt_of_le hx.2 ?_⟩
    rw [hLM, ← sum_range_lamNat_eq_total lam]
    exact sum_range_lamNat_mono lam hln
  have hsum : (∑ t, ((blockLam lam k hkl hln hpos) t : ℝ)) = 1 := by
    rw [← NNReal.coe_sum, blockLam_sum lam k hkl hln hpos, NNReal.coe_one]
  have hx'mem : rescaleMap L (L + M) x ∈ Set.Ico (0 : ℝ) 1 :=
    (rescaleMap_mem (by linarith : L < L + M)).mpr hx
  have hj : 0 ≤ rescaleMap L (L + M) x := hx'mem.1
  have hx'tot : rescaleMap L (L + M) x ∈
      Set.Ico (0 : ℝ) (∑ t, ((blockLam lam k hkl hln hpos) t : ℝ)) := by
    rw [hsum]; exact hx'mem
  -- rewrite both exchanges at the point
  rw [mkIET1_apply lam π hl hx_tot,
    mkIET1_apply (blockLam lam k hkl hln hpos) (blockPerm π k hkl hln hstab)
      (blockLam_sum lam k hkl hln hpos) hx'tot]
  set j : Fin (l - k) := idx (blockLam lam k hkl hln hpos) (rescaleMap L (L + M) x) hx'tot.1
    with hjdef
  have hjval : j.val = (idx lam x hx_tot.1).val - k := by
    rw [hjdef]
    exact idx_rescaleMap_aux ⟨k, l, hkl, hln⟩ hpos x hx0 hx hj
  have hik : k ≤ (idx lam x hx_tot.1).val := by
    have h := le_idx lam x hx_tot.1 (i := ⟨k, by omega⟩) (by rw [hLdef] at *; exact hx.1)
    simpa only [Fin.le_def, Fin.val_mk] using h
  have hieq : idx lam x hx_tot.1 = (⟨k + j.val, by omega⟩ : Fin n) :=
    Fin.ext (by simp only [Fin.val_mk]; omega)
  have hleft : leftEnd lam (idx lam x hx_tot.1)
      = L + M * leftEnd (blockLam lam k hkl hln hpos) j := by
    rw [hieq, hLdef, hMdef]
    exact _root_.leftEnd_blockLam hpos hkl hln j
  have himg : imageLeft π lam (idx lam x hx_tot.1) - L
      = M * imageLeft (blockPerm π k hkl hln hstab) (blockLam lam k hkl hln hpos) j := by
    rw [hieq, hLdef, hMdef]
    exact imageLeft_blockPerm_aux hpos hkl hln hstab j
  have himg' : imageLeft π lam (idx lam x hx_tot.1)
      = L + M * imageLeft (blockPerm π k hkl hln hstab) (blockLam lam k hkl hln hpos) j := by
    linarith
  -- the final computation
  have hx'r : rescaleMap L (L + M) x = (x - L) / M := by
    rw [rescaleMap, show L + M - L = M from by ring]
  rw [himg', hleft, hx'r, rescaleMap, show L + M - L = M from by ring]
  field_simp
  ring

end RescaleBlock

section LeftEndBounds

variable {n : ℕ} [NeZero n] {lam : Fin n → ℝ≥0} {k l : ℕ}

omit [NeZero n] in
/-- The rescaled lengths of a block are positive. -/
theorem blockLam_pos (hpos : Positive lam) (hkl : k < l) (hln : l ≤ n) (j : Fin (l - k)) :
    0 < blockLam lam k hkl hln hpos j := by
  rw [← NNReal.coe_pos, blockLam_coe]
  exact div_pos (hpos _) (blockMass_pos hpos k hkl hln)

variable {π : Equiv.Perm (Fin n)}
/-- The left end of any cell is strictly smaller than the total length. -/
theorem leftEnd_lt_total (hpos : Positive lam) (i : Fin n) :
    leftEnd lam i < ∑ j, (lam j : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_one_add_one (NeZero.ne n)).symm⟩
  have hle : leftEnd lam i ≤ leftEnd lam (Fin.last m) := leftEnd_le_leftEnd (Fin.le_last i)
  have hu : upperEnd lam (Fin.last m) = ∑ j, (lam j : ℝ) :=
    upperEnd_of_max lam (fun j => Fin.le_last j)
  have h2 : upperEnd lam (Fin.last m) = leftEnd lam (Fin.last m) + (lam (Fin.last m) : ℝ) :=
    upperEnd_eq lam _
  have h3 : (0 : ℝ) < (lam (Fin.last m) : ℝ) := by exact_mod_cast hpos _
  linarith

/-- A cut at a non-zero index is positive. -/
theorem leftEnd_pos_of_ne_zero (hpos : Positive lam) {i : Fin n} (hi : i ≠ 0) :
    0 < leftEnd lam i := by
  have hval : i.val ≠ 0 := fun h => hi (Fin.ext (by simp [h]))
  have h0 : (0 : Fin n) < i := by
    rw [Fin.lt_def, Fin.val_zero]
    omega
  rw [← leftEnd_zero lam]
  exact leftEnd_lt_leftEnd hpos h0

end LeftEndBounds

/-! ### `IsCompPresentation` as a datum: the composition is the exchange of the marked list -/

section CompDatum

variable {n : ℕ} {s : Fin (n + 1) → ℝ}

/-- The left ends of the list are the left ends of `compLen`. -/
theorem listLeftEnd_eq_leftEnd (hmono : StrictMono s) (i : Fin n) :
    listLeftEnd s i = leftEnd (compLen hmono) i := rfl

/-- The image starts of the list are the image starts of `compLen`. -/
theorem listImageLeft_eq_imageLeft (hmono : StrictMono s) (ρ : Equiv.Perm (Fin n)) (i : Fin n) :
    listImageLeft ρ s i = imageLeft ρ (compLen hmono) i := rfl

/-- The `ℕ`-indexed extension of the list. -/
noncomputable def sExt (s : Fin (n + 1) → ℝ) (m : ℕ) : ℝ :=
  if h : m ≤ n then s ⟨m, by omega⟩ else 0

theorem sExt_of_le {m : ℕ} (h : m ≤ n) : sExt s m = s ⟨m, by omega⟩ := dif_pos h

/-- **The left end of the `i`-th cell of the list is the `i`-th marked point.** -/
theorem leftEnd_compLen (hmono : StrictMono s) (h0 : s 0 = 0) (i : Fin n) :
    leftEnd (compLen hmono) i = s i.castSucc := by
  have hle : i.val ≤ n := by have := i.isLt; omega
  have hsum : leftEnd (compLen hmono) i
      = ∑ m ∈ Finset.range i.val, (sExt s (m + 1) - sExt s m) := by
    rw [leftEnd_eq_sum_range]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mem_range] at hm
    rw [lamNat_of_lt (by omega), sExt_of_le (by omega), sExt_of_le (by omega)]
    rfl
  rw [hsum, Finset.sum_range_sub (sExt s) i.val, sExt_of_le hle]
  have hzero : sExt s 0 = 0 := by rw [sExt_of_le (by omega)]; simpa using h0
  rw [hzero, sub_zero]
  exact congrArg s (Fin.ext rfl)

end CompDatum

section Endpoints

variable {n : ℕ} {s : Fin (n + 1) → ℝ}

/-- The right end of the `i`-th cell of the list is the `(i+1)`-th marked point. -/
theorem upperEnd_compLen (hmono : StrictMono s) (h0 : s 0 = 0) (i : Fin n) :
    upperEnd (compLen hmono) i = s i.succ := by
  rw [upperEnd_eq, leftEnd_compLen hmono h0 i]
  have hc : (compLen hmono i : ℝ) = s i.succ - s i.castSucc := rfl
  rw [hc]
  ring

/-- **The lengths of the list add up to `1`.** -/
theorem compLen_sum (hmono : StrictMono s) (h0 : s 0 = 0) (h1 : s (Fin.last n) = 1) :
    (∑ i, compLen hmono i) = 1 := by
  rw [← NNReal.coe_inj, NNReal.coe_sum, NNReal.coe_one]
  have hterm : ∀ i : Fin n, (compLen hmono i : ℝ) = sExt s (i.val + 1) - sExt s i.val := by
    intro i
    rw [show (compLen hmono i : ℝ) = s i.succ - s i.castSucc from rfl,
      sExt_of_le (by have := i.isLt; omega), sExt_of_le (by have := i.isLt; omega)]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => hterm i),
    Fin.sum_univ_eq_sum_range (fun m => sExt s (m + 1) - sExt s m) n,
    Finset.sum_range_sub (sExt s) n]
  have hz : sExt s 0 = 0 := by rw [sExt_of_le (by omega)]; simpa using h0
  have hn : sExt s n = 1 := by
    have : n ≤ n := le_refl n
    rw [sExt_of_le this]
    have hlast : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext rfl
    rw [hlast, h1]
  rw [hn, hz]
  ring

end Endpoints

section Presentation

variable {d e : ℕ} [NeZero d] [NeZero e] {lam : Fin d → ℝ≥0} {π : Equiv.Perm (Fin d)}
  {mu : Fin e → ℝ≥0} {σ : Equiv.Perm (Fin e)} {hl : (∑ i, lam i) = 1} {hm : (∑ j, mu j) = 1}
  {n : ℕ} [NeZero n] {s : Fin (n + 1) → ℝ} {ρ : Equiv.Perm (Fin n)}

/-- **`IsCompPresentation` presents the composition as the datum `(compLen, ρ)`**: the composition
`g ∘ f` is the exchange whose cells are the pieces of the marked list `s` and whose permutation is
`ρ`.  This is what turns Lemma 3.2's statement about the pair into a statement about the datum of
the presentation. -/
theorem IsCompPresentation.eq_mkIET1 (P : IsCompPresentation lam π mu σ hl hm n s ρ) :
    mkIET1 mu σ hm * mkIET1 lam π hl
      = mkIET1 (compLen P.mono) ρ (compLen_sum P.mono P.zero P.top) := by
  have hsumR : (∑ i, (compLen P.mono i : ℝ)) = 1 := by
    rw [← NNReal.coe_sum, compLen_sum P.mono P.zero P.top, NNReal.coe_one]
  refine IET.ext (fun x => ?_)
  by_cases hx : x ∈ Set.Ico (0 : ℝ) 1
  · have hx' : x ∈ Set.Ico (0 : ℝ) (∑ i, (compLen P.mono i : ℝ)) := by rw [hsumR]; exact hx
    obtain ⟨i, hi⟩ : ∃ i : Fin n, i = idx (compLen P.mono) x hx'.1 := ⟨_, rfl⟩
    have hmem : s i.castSucc ≤ x ∧ x < s i.succ := by
      constructor
      · rw [← leftEnd_compLen P.mono P.zero i]
        rw [hi]
        exact idx_mem _ x hx'.1
      · rw [← upperEnd_compLen P.mono P.zero i]
        rw [hi]
        exact lt_upperEnd_idx _ hx'
    rw [P.cell i x hmem.1 hmem.2, hi, mkIET1_apply (compLen P.mono) ρ _ hx',
      listImageLeft_eq_imageLeft, listLeftEnd_eq_leftEnd]
  · have hlt : x < 0 ∨ 1 ≤ x := by
      rcases not_and_or.mp hx with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_lt.mp h)
    have hg : (mkIET1 lam π hl) x = x := by
      rcases hlt with h | h
      · exact (mkIET1 lam π hl).isIET.apply_eq_self_of_lt h
      · exact (mkIET1 lam π hl).isIET.apply_eq_self_of_le h
    have hf : (mkIET1 mu σ hm) x = x := by
      rcases hlt with h | h
      · exact (mkIET1 mu σ hm).isIET.apply_eq_self_of_lt h
      · exact (mkIET1 mu σ hm).isIET.apply_eq_self_of_le h
    have hc : (mkIET1 (compLen P.mono) ρ (compLen_sum P.mono P.zero P.top)) x = x := by
      rcases hlt with h | h
      · exact (mkIET1 (compLen P.mono) ρ _).isIET.apply_eq_self_of_lt h
      · exact (mkIET1 (compLen P.mono) ρ _).isIET.apply_eq_self_of_le h
    rw [IET.mul_apply, hg, hf, hc]

end Presentation

/-! ### The images of the marked cells -/

section CellImage

variable {n : ℕ} {S : Fin (n + 1) → ℝ}

/-- **The left end of an entry of the list is that entry.** -/
theorem listLeftEnd_eq (hmono : StrictMono S) (h0 : S 0 = 0) (i : Fin n) :
    listLeftEnd S i = S i.castSucc := by
  rw [listLeftEnd_eq_leftEnd hmono i, leftEnd_compLen hmono h0 i]

/-- **The cell length is positive.** -/
theorem listLen_pos (hmono : StrictMono S) (i : Fin n) :
    0 < S i.succ - S i.castSucc :=
  sub_pos.mpr (hmono (Fin.castSucc_lt_succ (i := i)))

/-- **The image of the `i`-th cell under the exchange of the presentation.** -/
theorem comp_image_cell {d e : ℕ} [NeZero d] [NeZero e] {lam : Fin d → ℝ≥0}
    {π : Equiv.Perm (Fin d)} {mu : Fin e → ℝ≥0} {σ : Equiv.Perm (Fin e)}
    {hl : (∑ i, lam i) = 1} {hm : (∑ j, mu j) = 1} {S : Fin (n + 1) → ℝ}
    {ρ : Equiv.Perm (Fin n)} (P : IsCompPresentation lam π mu σ hl hm n S ρ) (i : Fin n) :
    (mkIET1 mu σ hm * mkIET1 lam π hl) '' Set.Ico (S i.castSucc) (S i.succ)
      = Set.Ico (listImageLeft ρ S i) (listImageLeft ρ S i + (S i.succ - S i.castSucc)) := by
  have hab : S i.castSucc < S i.succ := P.mono (Fin.castSucc_lt_succ (i := i))
  rw [image_Ico_add hab (fun x hx1 hx2 => P.cell i x hx1 hx2), listLeftEnd_eq P.mono P.zero i]
  congr 1
  · ring
  · ring

end CellImage

section Starts

variable {n : ℕ} {S : Fin (n + 1) → ℝ} {ρ : Equiv.Perm (Fin n)}

/-- The entries of a strictly increasing list with endpoints `0` and `1` lie in `[0, 1]`. -/
theorem list_mem_Icc (hmono : StrictMono S) (h0 : S 0 = 0) (h1 : S (Fin.last n) = 1)
    (k : Fin (n + 1)) : S k ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rw [← h0]
    exact hmono.monotone (Fin.zero_le k)
  · rw [← h1]
    exact hmono.monotone (Fin.le_last k)

/-- The number of elements of `Fin n` below `m`. -/
theorem card_fin_lt {n m : ℕ} (hm : m ≤ n) :
    (Finset.univ.filter (fun j : Fin n => j.val < m)).card = m := by
  rw [← Fintype.card_subtype (fun j : Fin n => j.val < m)]
  have heq : Fintype.card {j : Fin n // j.val < m} = Fintype.card (Fin m) :=
    Fintype.card_congr
      { toFun := fun j => ⟨j.val.val, j.property⟩
        invFun := fun t => ⟨⟨t.val, by omega⟩, t.isLt⟩
        left_inv := fun j => Subtype.ext (Fin.ext rfl)
        right_inv := fun t => Fin.ext rfl }
  rw [heq, Fintype.card_fin]

/-- The number of cells with `ρ`-value below a given one. -/
theorem card_rho_lt (i : Fin n) :
    (Finset.univ.filter (fun j : Fin n => ρ j < ρ i)).card = (ρ i).val := by
  have h1 : (Finset.univ.filter (fun j : Fin n => ρ j < ρ i))
      = (Finset.univ.filter (fun k : Fin n => k.val < (ρ i).val)).image ρ.symm := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨ρ j, h, Equiv.symm_apply_apply ρ j⟩
    · rintro ⟨k, hk, rfl⟩
      simpa using hk
  rw [h1, Finset.card_image_of_injective _ ρ.symm.injective]
  exact card_fin_lt (le_of_lt (ρ i).isLt)

end Starts

/-- **The left end plus the mass of a block is the right end of the block**, for the length vector
`compLen` of a list: no case distinction on `l = n` is needed here, because the right end is read
off the list. -/
theorem leftEnd_add_blockMass_compLen {n : ℕ} {s : Fin (n + 1) → ℝ} (hmono : StrictMono s)
    (h0 : s 0 = 0) {k l : ℕ} (hkl : k < l) (hln : l ≤ n) :
    leftEnd (compLen hmono) ⟨k, by omega⟩ + blockMass (compLen hmono) k hln = s ⟨l, by omega⟩ := by
  have hsum : leftEnd (compLen hmono) ⟨k, by omega⟩
      = ∑ m ∈ Finset.range k, (sExt s (m + 1) - sExt s m) := by
    rw [leftEnd_eq_sum_range]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mem_range] at hm
    rw [lamNat_of_lt (by omega), sExt_of_le (by omega), sExt_of_le (by omega)]
    rfl
  have hbm : blockMass (compLen hmono) k hln
      = ∑ x ∈ Finset.range (l - k), (sExt s (k + x + 1) - sExt s (k + x)) := by
    rw [blockMass, ← Fin.sum_univ_eq_sum_range
      (fun x => sExt s (k + x + 1) - sExt s (k + x)) (l - k)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [sExt_of_le (by have := x.isLt; omega), sExt_of_le (by have := x.isLt; omega)]
    rfl
  rw [hsum, hbm,
    ← Finset.sum_range_add (fun m => sExt s (m + 1) - sExt s m) k (l - k),
    show k + (l - k) = l from by omega, Finset.sum_range_sub (sExt s) l, sExt_of_le hln]
  have hzero : sExt s 0 = 0 := by rw [sExt_of_le (by omega)]; simpa using h0
  rw [hzero, sub_zero]
