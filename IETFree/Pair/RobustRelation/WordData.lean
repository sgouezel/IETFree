/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.Pair.RobustRelation.FreeParams
public import IETFree.Pair.RobustRelation.GoodParams
public import IETFree.Pair.Singularity.List

/-!
# The symbolic data of a word, piece by piece

`w(f_q, g_q)` is a piecewise translation whose cuts are finitely many candidate positions, each an
affine function of the parameter `q`; this file builds that data as a certificate `WordData` and
proves it exists for every word, by induction.

The proof follows the word letter by letter.  At a reference point `q₀` the candidate cuts — the
cuts of the letters pushed forward by the partial products, and the preimages of the cuts of the
prefix
under the displacement of the last letter — are bounded integer-affine functions of the parameter
(`IsFullLat`, `IsFreeLat`, the passage to the free coordinates `IsFullLat.isFreeLat` doubling the
coefficient bound); they can be sorted by their values at `q₀` (`exists_sorted_cuts`), and the
displacement of the word on each resulting piece is again such a function.  Two distinct candidates
take distinct values at `q₀` as soon as no nontrivial relation vanishes there
(`IsFreeLat.eq_of_eq_at_omega`), so the pieces listed are the genuine ones on a ball.

If the word is the identity at `q₀`, every displacement vanishes at `q₀` (`VanishesAt`, the
hypothesis of `evalWord_eventually_eq_one_of_wordData`), hence — being a bounded integer-affine
function — vanishes identically, and the word is the identity on the ball.  That is the step the
theorem is made of; the four one-letter cases the induction starts from are in `LetterData.lean`,
and the theorem itself in `Robustness.lean`.

The parameter is `PReal d e`: the `d - 1` and `e - 1` free lengths of the two exchanges, the last
length of each being `1` minus the sum of the others.
-/


@[expose] public section
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace IntervalExchange.Pair
/-! ## 2. Lattice functions of the lengths

A displacement of a word `w` on one of its pieces is a sum of `|w|` translation vectors of the two
exchanges, so it is `∑ aᵢ λᵢ + ∑ bⱼ μⱼ` with `|aᵢ|, |bⱼ| ≤ |w|`.  `IsFullLat K f` says exactly
that, with `K` the bound; the lengths are the affine functions `imageLenAffine` and
`imageLenAffineRight` of the free parameters, which agree with `simplexMap` on the open region. -/

/-- **A lattice function of the lengths**: a function of the free parameters that is an integer
combination `∑ aᵢ λᵢ + ∑ bⱼ μⱼ` of the two length vectors, with all coefficients bounded by `K` in
absolute value.

The lengths are the affine functions `imageLenAffine`/`imageLenAffineRight` of the free parameters
rather than `simplexMap` itself: the latter is clamped at `0` outside the region and is therefore
not affine.  The two agree on the open region (`imageLenAffine_eq`), which is where the functions
are evaluated. -/
def IsFullLat {d e : ℕ} [NeZero d] [NeZero e] (K : ℤ) (f : ParamAffine d e) : Prop :=
  ∃ a : Fin d → ℤ, ∃ b : Fin e → ℤ,
    (∀ i, |a i| ≤ K) ∧ (∀ j, |b j| ≤ K) ∧
      ∀ q : PReal d e,
        f q = (∑ i, (a i : ℝ) * (imageLenAffine (e := e) i q))
          + ∑ j, (b j : ℝ) * (imageLenAffineRight (d := d) j q)

/-! ### The translation vector of an exchange, as a lattice function -/

/-! ### Passing to the free coordinates -/

/-- **The lengths of a `Fin (m+1)`-vector, in the free coordinates**: the sum
`∑ aᵢ λᵢ` is `a_d + ∑_{i<m} (aᵢ - a_d) λᵢ`, the last coordinate being `1 - ∑_{i<m} λᵢ`. -/
theorem sum_imageLenAffine_split {e m : ℕ} (A : Fin (m + 1) → ℤ) (q : PReal (m + 1) e) :
    (∑ i : Fin (m + 1), (A i : ℝ) * (imageLenAffine (e := e) i q))
      = (A (Fin.last m) : ℝ)
        + ∑ i : Fin m, ((A i.castSucc - A (Fin.last m) : ℤ) : ℝ) * q.1 i := by
  rw [Fin.sum_univ_castSucc]
  have hlast : imageLenAffine (e := e) (Fin.last m) q = 1 - ∑ i : Fin m, q.1 i :=
    imageLenAffine_apply_last (by simp) q
  have hfree (i : Fin m) : imageLenAffine (e := e) (Fin.castSucc i) q = q.1 i := by
    rw [imageLenAffine_apply_free (by simp only [Fin.val_castSucc]; omega)]
    rfl
  rw [hlast, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by rw [hfree i])]
  have hsplit : (∑ i : Fin m, ((A i.castSucc - A (Fin.last m) : ℤ) : ℝ) * q.1 i)
      = (∑ i : Fin m, (A i.castSucc : ℝ) * q.1 i)
        - (A (Fin.last m) : ℝ) * ∑ i : Fin m, q.1 i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by push_cast; ring)
  rw [hsplit]
  ring

/-- The same splitting for the second length vector. -/
theorem sum_imageLenAffineRight_split {d n : ℕ} (B : Fin (n + 1) → ℤ) (q : PReal d (n + 1)) :
    (∑ j : Fin (n + 1), (B j : ℝ) * (imageLenAffineRight (d := d) j q))
      = (B (Fin.last n) : ℝ)
        + ∑ j : Fin n, ((B j.castSucc - B (Fin.last n) : ℤ) : ℝ) * q.2 j := by
  rw [Fin.sum_univ_castSucc]
  have hlast : imageLenAffineRight (d := d) (Fin.last n) q = 1 - ∑ j : Fin n, q.2 j :=
    imageLenAffineRight_apply_last (by simp) q
  have hfree (j : Fin n) : imageLenAffineRight (d := d) (Fin.castSucc j) q = q.2 j := by
    rw [imageLenAffineRight_apply_free (by simp only [Fin.val_castSucc]; omega)]
    rfl
  rw [hlast, Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => by rw [hfree j])]
  have hsplit : (∑ j : Fin n, ((B j.castSucc - B (Fin.last n) : ℤ) : ℝ) * q.2 j)
      = (∑ j : Fin n, (B j.castSucc : ℝ) * q.2 j)
        - (B (Fin.last n) : ℝ) * ∑ j : Fin n, q.2 j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by push_cast; ring)
  rw [hsplit]
  ring

/-! ## 2'. Bounded integer-affine functions in the free coordinates

The free coordinates are `q.1 : Fin (d - 1) → ℝ` and `q.2 : Fin (e - 1) → ℝ`, and an affine
function of them is determined by its constant term and its coefficients.  `IsFreeLat K f` says that
these data are integers bounded by `K`, which is the form in which goodness is consumed
(`coeffs_zero_of_good_with_const_at`), and the form in which the distinctness of two candidate
cuts is a nontrivial relation. -/

/-- **A bounded integer-affine function of the free parameters**: an integer constant plus an
integer combination of the free coordinates, all coefficients bounded by `K`. -/
def IsFreeLat {d e : ℕ} (K : ℤ) (f : ParamAffine d e) : Prop :=
  ∃ (c : ℤ) (a : Fin (d - 1) → ℤ) (b : Fin (e - 1) → ℤ),
    |c| ≤ K ∧ (∀ i, |a i| ≤ K) ∧ (∀ j, |b j| ≤ K) ∧
      ∀ q : PReal d e,
        f q = (c : ℝ) + (∑ i, (a i : ℝ) * q.1 i) + ∑ j, (b j : ℝ) * q.2 j

theorem IsFreeLat.mono {d e : ℕ} {K L : ℤ} (hKL : K ≤ L) {f : ParamAffine d e}
    (hf : IsFreeLat K f) : IsFreeLat L f := by
  obtain ⟨c, a, b, hc, ha, hb, hrep⟩ := hf
  exact ⟨c, a, b, le_trans hc hKL, fun i => le_trans (ha i) hKL, fun j => le_trans (hb j) hKL, hrep⟩

theorem IsFreeLat.zero {d e : ℕ} {K : ℤ} (hK : 0 ≤ K) :
    IsFreeLat (d := d) (e := e) K (0 : ParamAffine d e) := by
  refine ⟨0, 0, 0, ?_, fun i => ?_, fun j => ?_, fun q => ?_⟩
  · simpa using hK
  · simpa using hK
  · simpa using hK
  · simp

/-- The sum of two bounded integer-affine functions. -/
theorem IsFreeLat.add {d e : ℕ} {K L : ℤ} {f g : ParamAffine d e} (hf : IsFreeLat K f)
    (hg : IsFreeLat L g) : IsFreeLat (K + L) (f + g) := by
  obtain ⟨c1, a1, b1, hc1, ha1, hb1, h1⟩ := hf
  obtain ⟨c2, a2, b2, hc2, ha2, hb2, h2⟩ := hg
  refine ⟨c1 + c2, a1 + a2, b1 + b2, ?_, ?_, ?_, fun q => ?_⟩
  · have := abs_add_le c1 c2
    omega
  · intro i
    have := abs_add_le (a1 i) (a2 i)
    have h1' := ha1 i
    have h2' := ha2 i
    change |a1 i + a2 i| ≤ K + L
    omega
  · intro j
    have := abs_add_le (b1 j) (b2 j)
    have h1' := hb1 j
    have h2' := hb2 j
    change |b1 j + b2 j| ≤ K + L
    omega
  · change f q + g q = _
    rw [h1 q, h2 q]
    have e1 : (∑ i, (((a1 + a2) i : ℤ) : ℝ) * q.1 i)
        = (∑ i, (a1 i : ℝ) * q.1 i) + ∑ i, (a2 i : ℝ) * q.1 i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by rw [Pi.add_apply]; push_cast; ring)
    have e2 : (∑ j, (((b1 + b2) j : ℤ) : ℝ) * q.2 j)
        = (∑ j, (b1 j : ℝ) * q.2 j) + ∑ j, (b2 j : ℝ) * q.2 j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by rw [Pi.add_apply]; push_cast; ring)
    rw [Int.cast_add, e1, e2]
    ring

theorem IsFreeLat.neg {d e : ℕ} {K : ℤ} {f : ParamAffine d e} (hf : IsFreeLat K f) :
    IsFreeLat K (-f) := by
  obtain ⟨c, a, b, hc, ha, hb, hrep⟩ := hf
  refine ⟨-c, -a, -b, ?_, ?_, ?_, fun q => ?_⟩
  · simpa using hc
  · intro i; simpa using ha i
  · intro j; simpa using hb j
  · change -(f q) = _
    rw [hrep q]
    have e1 : (∑ i, ((-a) i : ℝ) * q.1 i) = -(∑ i, (a i : ℝ) * q.1 i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.neg_apply]; push_cast; ring)
    have e2 : (∑ j, ((-b) j : ℝ) * q.2 j) = -(∑ j, (b j : ℝ) * q.2 j) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j _ => by simp only [Pi.neg_apply]; push_cast; ring)
    rw [Int.cast_neg, e1, e2]
    ring

theorem IsFreeLat.sub {d e : ℕ} {K L : ℤ} {f g : ParamAffine d e} (hf : IsFreeLat K f)
    (hg : IsFreeLat L g) : IsFreeLat (K + L) (f - g) := by
  have h : f - g = f + (-g) := by
    ext q
    change f q - g q = f q + -(g q)
    ring
  rw [h]
  exact hf.add hg.neg

/-- **Distinct values at a point of `Ω'` force equal affine functions.**  This is the paper's
hypothesis: at `q₀` *no* nontrivial integer relation vanishes (`∀ N, q₀ ∈ goodParamsAt N`).  The
difference of two bounded integer-affine functions is bounded integer-affine; it vanishes at `q₀`,
so its coefficient vector is a relation vanishing there; were it nontrivial it would be a bad
relation at some threshold `N`, contradiction.  Hence all the coefficients of the difference are
zero and the two functions agree. -/
theorem IsFreeLat.eq_of_eq_at_omega {d e : ℕ} {q₀ : PReal d e}
    (hq : ∀ N, q₀ ∈ goodParamsAt N (d := d) (e := e)) {K L : ℤ} {f g : ParamAffine d e}
    (hf : IsFreeLat K f) (hg : IsFreeLat L g) (h : f q₀ = g q₀) : f = g := by
  obtain ⟨c, a, b, -, -, -, hrep⟩ := hf.sub hg
  have hrel : relReal (ofCoeffs c a b) q₀ = 0 := by
    rw [relReal_ofCoeffs, ← hrep q₀]
    change f q₀ - g q₀ = 0
    rw [h, sub_self]
  have hS1 : (0 : ℤ) ≤ ∑ i : Fin (d - 1), |a i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hS2 : (0 : ℤ) ≤ ∑ j : Fin (e - 1), |b j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hcnn : (0 : ℤ) ≤ |c| := abs_nonneg _
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = |c| + ∑ i : Fin (d - 1), |a i|
      + ∑ j : Fin (e - 1), |b j| + 1 := by
    refine ⟨( |c| + ∑ i : Fin (d - 1), |a i| + ∑ j : Fin (e - 1), |b j| + 1).toNat, ?_⟩
    exact Int.toNat_of_nonneg (by linarith)
  have hsuma : ∀ i : Fin (d - 1), |a i| ≤ ∑ i : Fin (d - 1), |a i| := fun i =>
    Finset.single_le_sum (f := fun i => |a i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  have hsumb : ∀ j : Fin (e - 1), |b j| ≤ ∑ j : Fin (e - 1), |b j| := fun j =>
    Finset.single_le_sum (f := fun j => |b j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  have htriv : ¬ NontrivialCoeff (ofCoeffs c a b) := by
    intro hcon
    refine hq N ⟨ofCoeffs c a b, ?_, hcon, hrel⟩
    rw [mem_smallCoeffsAt]
    rintro (⟨i | j⟩ | u)
    · simpa [ofCoeffs] using (show |a i| ≤ (N : ℤ) by rw [hN]; have := hsuma i; linarith)
    · simpa [ofCoeffs] using (show |b j| ≤ (N : ℤ) by rw [hN]; have := hsumb j; linarith)
    · simpa [ofCoeffs] using (show |c| ≤ (N : ℤ) by rw [hN]; linarith)
  have hzero : c = 0 ∧ a = 0 ∧ b = 0 := by
    by_contra hne
    apply htriv
    simp only [NontrivialCoeff, constCoeff, ofCoeffs]
    by_contra hcon
    push Not at hcon
    exact hne ⟨hcon.1, funext hcon.2.1, funext hcon.2.2⟩
  ext q
  have hsub := hrep q
  rw [hzero.1, hzero.2.1, hzero.2.2] at hsub
  simp only [Int.cast_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at hsub
  have h0 : f q - g q = 0 := hsub
  linarith

/-- A bounded integer-affine function that vanishes at a good point is identically zero. -/
theorem IsFreeLat.eq_zero_of_vanishes {d e N : ℕ} {q₀ : PReal d e}
    (hq : q₀ ∈ goodParamsAt N (d := d) (e := e)) {K : ℤ} (hKN : K ≤ (N : ℤ)) {f : ParamAffine d e}
    (hf : IsFreeLat K f) (h0 : f q₀ = 0) : f = 0 := by
  obtain ⟨c, a, b, hc, ha, hb, hrep⟩ := hf
  have hvanish : (c : ℝ) + (∑ i, (a i : ℝ) * q₀.1 i) + (∑ j, (b j : ℝ) * q₀.2 j) = 0 := by
    rw [← hrep q₀]
    exact h0
  obtain ⟨hc0, ha0, hb0⟩ := coeffs_zero_of_good_with_const_at hq (fun i => le_trans (ha i) hKN)
    (fun j => le_trans (hb j) hKN) (le_trans hc hKN) hvanish
  ext q
  rw [hrep q]
  simp [hc0, ha0, hb0]

/-- A bounded integer-affine function vanishing at a point of `Ω'` is identically zero. -/
theorem IsFreeLat.eq_zero_of_vanishes_of_forall {d e : ℕ} {q₀ : PReal d e}
    (hq : ∀ N, q₀ ∈ goodParamsAt N (d := d) (e := e)) {K : ℤ}
    {f : ParamAffine d e} (hf : IsFreeLat K f) (h0 : f q₀ = 0) : f = 0 :=
  IsFreeLat.eq_of_eq_at_omega hq hf (IsFreeLat.zero (d := d) (e := e) (K := 0) le_rfl) h0

/-- A lattice function of the lengths is a bounded integer-affine function of the free parameters,
with the bound doubled. -/
theorem IsFullLat.isFreeLat {d e : ℕ} [NeZero d] [NeZero e] {K : ℤ} {f : ParamAffine d e}
    (hf : IsFullLat K f) : IsFreeLat (2 * K) f := by
  obtain ⟨A, B, hA, hB, hrep⟩ := hf
  obtain ⟨m, hm⟩ : ∃ m, d = m + 1 := ⟨d - 1, (Nat.sub_one_add_one (NeZero.ne d)).symm⟩
  obtain ⟨n, hn⟩ : ∃ n, e = n + 1 := ⟨e - 1, (Nat.sub_one_add_one (NeZero.ne e)).symm⟩
  subst hm
  subst hn
  refine ⟨A (Fin.last m) + B (Fin.last n), fun i => A i.castSucc - A (Fin.last m),
    fun j => B j.castSucc - B (Fin.last n), ?_, ?_, ?_, ?_⟩
  · have h1 := abs_le.mp (hA (Fin.last m))
    have h2 := abs_le.mp (hB (Fin.last n))
    rw [abs_le]
    constructor <;> omega
  · intro i
    have h1 := abs_le.mp (hA i.castSucc)
    have h2 := abs_le.mp (hA (Fin.last m))
    change |A i.castSucc - A (Fin.last m)| ≤ 2 * K
    rw [abs_le]
    constructor <;> omega
  · intro j
    have h1 := abs_le.mp (hB j.castSucc)
    have h2 := abs_le.mp (hB (Fin.last n))
    change |B j.castSucc - B (Fin.last n)| ≤ 2 * K
    rw [abs_le]
    constructor <;> omega
  · intro q
    rw [hrep q, sum_imageLenAffine_split A q, sum_imageLenAffineRight_split B q]
    simp only [Int.cast_add, Int.cast_sub]
    have key (a b c d : ℝ) : a + b + (c + d) = a + c + b + d := by ring
    exact key _ _ _ _

/-! ## 3. The two exchanges at a free parameter, and the letters of a word -/

/-- **A letter of the word at the parameter `q`**: `f`, `g`, `f⁻¹` or `g⁻¹`.  The index `p.1 ∈
Fin 2` chooses the generator (`0` is `f`, `1` is `g`) and `p.2` chooses whether it is inverted, in
the encoding of `FreeGroup.toWord`. -/
noncomputable def ltrQ {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) (p : Fin 2 × Bool) (q : PReal d e) : IET 0 1 :=
  cond p.2 (if p.1 = 0 then fOf π q else gOf σ q)
    ((if p.1 = 0 then fOf π q else gOf σ q))⁻¹

/-- **The value of a word at a parameter is the product of its letters.** -/
theorem evalWord_eq_list_prod {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) (w : FreeGroup Gen) (q : PReal d e) :
    evalWord w (fOf π q) (gOf σ q) = ((w.toWord).map (fun p => ltrQ π σ p q)).prod := by
  have h : FreeGroup.lift (fun i : Gen => if i = 0 then fOf π q else gOf σ q) w
      = ((FreeGroup.toWord w).map (fun p => ltrQ π σ p q)).prod := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := w)]
    rw [FreeGroup.lift_mk]
    rfl
  exact h

/-! ## 4. The piece of `[0,1)` containing a point -/

/-- The set of pieces of `[0,1)` whose left end is `≤ y` is nonempty: `s` has a zero, which cannot
be its last value (that one is `1`). -/
theorem pieceSet_nonempty {d e m : ℕ} {s : Fin (m + 1) → ParamAffine d e} {q : PReal d e}
    (hmono : Monotone fun l => s l q) (h0 : ∃ l, s l q = 0) (h1 : ∃ l, s l q = 1)
    {y : ℝ} (hy : 0 ≤ y) :
    (Finset.univ.filter (fun k : Fin m => s k.castSucc q ≤ y)).Nonempty := by
  obtain ⟨l, hl⟩ := h0
  have hlval : l.val < m := by
    rcases Nat.lt_or_ge l.val m with h | h
    · exact h
    · exfalso
      have hlm : l = Fin.last m := Fin.ext (by simp; omega)
      rw [hlm] at hl
      obtain ⟨l', hl'⟩ := h1
      have hle : l' ≤ Fin.last m := Fin.le_last _
      have h2 := hmono hle
      simp only [hl', hl] at h2
      linarith
  refine ⟨⟨l.val, hlval⟩, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hc : ((⟨l.val, hlval⟩ : Fin m).castSucc : Fin (m + 1)) = l := Fin.ext rfl
  rw [hc, hl]
  exact hy

/-- The index of the pieces `[s k.castSucc, s (k+1))` that contain `y`.  Built as the largest `k`
with `s k.castSucc q ≤ y`. -/
noncomputable def pieceIndex {d e m : ℕ} {s : Fin (m + 1) → ParamAffine d e} {q : PReal d e}
    (hmono : Monotone fun l => s l q) (h0 : ∃ l, s l q = 0) (h1 : ∃ l, s l q = 1)
    {y : ℝ} (hy : 0 ≤ y) : Fin m :=
  (Finset.univ.filter (fun k : Fin m => s k.castSucc q ≤ y)).max'
    (pieceSet_nonempty hmono h0 h1 hy)

theorem pieceIndex_mem {d e m : ℕ} {s : Fin (m + 1) → ParamAffine d e} {q : PReal d e}
    (hmono : Monotone fun l => s l q) (h0 : ∃ l, s l q = 0) (h1 : ∃ l, s l q = 1)
    {y : ℝ} (hy : 0 ≤ y) :
    s (pieceIndex hmono h0 h1 hy).castSucc q ≤ y := by
  have h := Finset.max'_mem (Finset.univ.filter (fun k : Fin m => s k.castSucc q ≤ y))
    (pieceSet_nonempty hmono h0 h1 hy)
  rw [Finset.mem_filter] at h
  exact h.2

theorem pieceIndex_max {d e m : ℕ} {s : Fin (m + 1) → ParamAffine d e} {q : PReal d e}
    (hmono : Monotone fun l => s l q) (h0 : ∃ l, s l q = 0) (h1 : ∃ l, s l q = 1)
    {y : ℝ} (hy : 0 ≤ y) {l : Fin m} (hl : s l.castSucc q ≤ y) :
    l ≤ pieceIndex hmono h0 h1 hy := by
  refine Finset.le_max' _ l ?_
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hl⟩

/-- **The pieces cover `[0,1)`**: for a monotone family of cut functions with `0` and `1` among its
values, every `y ∈ [0,1)` lies in one of the half-open pieces. -/
theorem pieceIndex_lt_succ {d e m : ℕ} {s : Fin (m + 1) → ParamAffine d e} {q : PReal d e}
    (hmono : Monotone fun l => s l q) (h0 : ∃ l, s l q = 0) (h1 : ∃ l, s l q = 1)
    {y : ℝ} (hy : y < 1) (hy0 : 0 ≤ y) :
    y < s (pieceIndex hmono h0 h1 hy0).succ q := by
  by_contra hcon
  rw [not_lt] at hcon
  set K := pieceIndex hmono h0 h1 hy0 with hK
  have hKs : s K.succ q ≤ y := hcon
  rcases Nat.lt_or_ge (K.val + 1) m with hlt | hge
  · set K' : Fin m := ⟨K.val + 1, hlt⟩ with hK'
    have hcast : (K'.castSucc : Fin (m + 1)) = K.succ := Fin.ext (by simp [hK', Fin.val_succ])
    have hle : s K'.castSucc q ≤ y := by rw [hcast]; exact hKs
    have hlt2 : K < K' := Fin.lt_def.mpr (by simp [hK'])
    have := pieceIndex_max hmono h0 h1 hy0 hle
    omega
  · -- the last index also starts below `y`, contradicting `s (last) = 1 > y`
    obtain ⟨l', hl'⟩ := h1
    have hKm : K.val + 1 = m := by have := K.isLt; omega
    have hlast : K.succ = Fin.last m := Fin.ext (by simp [Fin.val_succ, hKm])
    rw [hlast] at hKs
    have hle : l' ≤ Fin.last m := Fin.le_last _
    have h2 := hmono hle
    simp only [hl'] at h2
    linarith

/-- **The comparison with any cut**: `y` is above the `l`-th cut exactly when `l` is at most the
index of the piece containing `y`. -/
theorem le_pieceIndex_iff {d e m : ℕ} {s : Fin (m + 1) → ParamAffine d e} {q : PReal d e}
    (hmono : Monotone fun l => s l q) (h0 : ∃ l, s l q = 0) (h1 : ∃ l, s l q = 1)
    {y : ℝ} (hy : y < 1) (hy0 : 0 ≤ y) (l : Fin (m + 1)) :
    s l q ≤ y ↔ l ≤ (pieceIndex hmono h0 h1 hy0).castSucc := by
  constructor
  · intro hl
    by_contra hcon
    rw [not_le] at hcon
    have h2 : (pieceIndex hmono h0 h1 hy0).succ ≤ l := by
      rw [Fin.le_def]
      have hlt := Fin.lt_def.mp hcon
      simp only [Fin.val_succ, Fin.val_castSucc] at hlt ⊢
      omega
    have h3 : s (pieceIndex hmono h0 h1 hy0).succ q ≤ s l q := hmono h2
    exact absurd (le_trans h3 hl) (not_le.mpr (pieceIndex_lt_succ hmono h0 h1 hy hy0))
  · intro hl
    exact le_trans (hmono hl) (pieceIndex_mem hmono h0 h1 hy0)

/-- **The piece containing a point of `[0,1)` never leaves the range between the zero and the one
of the cut list**: if `s lz = 0` and `s lo = 1` and `x ∈ [0,1)` lies in the `k`-th piece, then
`lz ≤ k.castSucc` and `k.succ ≤ lo`.  Hence only the pieces in that range matter. -/
theorem pieceIndex_range {d e m : ℕ} {s : Fin (m + 1) → ParamAffine d e} {q : PReal d e}
    (hmono : Monotone fun l => s l q) {lz lo : Fin (m + 1)} (hlz : s lz q = 0) (hlo : s lo q = 1)
    {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) (k : Fin m)
    (h1 : s k.castSucc q ≤ x) (h2 : x < s k.succ q) :
    lz ≤ k.castSucc ∧ k.succ ≤ lo := by
  constructor
  · by_contra hcon
    rw [not_le] at hcon
    have hle : k.succ ≤ lz := by
      rw [Fin.le_def]
      have hlt := Fin.lt_def.mp hcon
      simp only [Fin.val_succ, Fin.val_castSucc] at hlt ⊢
      omega
    have h3 := hmono hle
    simp only [hlz] at h3
    linarith [hx.1]
  · by_contra hcon
    rw [not_le] at hcon
    have hle : lo ≤ k.castSucc := by
      rw [Fin.le_def]
      have hlt := Fin.lt_def.mp hcon
      simp only [Fin.val_succ, Fin.val_castSucc] at hlt ⊢
      omega
    have h3 := hmono hle
    simp only [hlo] at h3
    linarith [hx.2]

/-- **`Ω'` is the set of points at which no nontrivial integer relation vanishes**: the
intersection of the good sets over all thresholds.  This is the paper's hypothesis, and the form in
which the robustness theorem below is stated. -/
theorem forall_goodParams_iff {d e : ℕ} {q : PReal d e} :
    (∀ N, q ∈ goodParamsAt N (d := d) (e := e)) ↔
      ∀ t : CoeffData d e, NontrivialCoeff t → relReal t q ≠ 0 := by
  constructor
  · intro h t hnt hrel
    have hS : ∀ ix : CoeffIndex d e, |t ix| ≤ ∑ ix : CoeffIndex d e, |t ix| := fun ix =>
      Finset.single_le_sum (f := fun ix => |t ix|) (fun ix _ => abs_nonneg _) (Finset.mem_univ ix)
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = ∑ ix : CoeffIndex d e, |t ix| + 1 := by
      refine ⟨((∑ ix : CoeffIndex d e, |t ix|) + 1).toNat, ?_⟩
      exact Int.toNat_of_nonneg (by
        have h0 : (0 : ℤ) ≤ ∑ ix : CoeffIndex d e, |t ix| :=
          Finset.sum_nonneg (fun ix _ => abs_nonneg _)
        linarith)
    exact (h N) ⟨t, by
      rw [mem_smallCoeffsAt]
      intro ix
      rw [hN]
      have := hS ix
      linarith, hnt, hrel⟩
  · rintro h N ⟨t, -, hnt, hrel⟩
    exact h t hnt hrel

/-- **The vanishing property at a bound**: every bounded integer-affine function of the free
parameters, with coefficient bound `≤ N`, that vanishes at `q₀` is identically zero.

This is the only consequence of goodness that the robustness proof uses, and it has two sources:
the paper's hypothesis `q₀ ∈ Ω'` (no bound at all, `vanishesAt_of_omega`) and the single threshold
`q₀ ∈ goodParamsAt N` (`vanishesAt_of_goodParams`). -/
def VanishesAt {d e : ℕ} (N : ℕ) (q₀ : PReal d e) : Prop :=
  ∀ (K : ℤ) (f : ParamAffine d e), K ≤ (N : ℤ) → IsFreeLat K f → f q₀ = 0 → f = 0

/-- The vanishing property at every bound follows from `q₀ ∈ Ω'`. -/
theorem vanishesAt_of_omega {d e : ℕ} {q₀ : PReal d e}
    (hq : ∀ N, q₀ ∈ goodParamsAt N (d := d) (e := e)) :
    ∀ N, VanishesAt N q₀ := by
  intro N K f _ hf h0
  exact IsFreeLat.eq_zero_of_vanishes_of_forall hq hf h0

/-- The vanishing property at `N` follows from `q₀ ∈ goodParamsAt N`. -/
theorem vanishesAt_of_goodParams {d e N : ℕ} {q₀ : PReal d e}
    (hq : q₀ ∈ goodParamsAt N (d := d) (e := e)) :
    VanishesAt N q₀ :=
  fun _ _ hK hf h0 => IsFreeLat.eq_zero_of_vanishes hq hK hf h0

/-! ## 5. The symbolic data of a word, and the robustness theorem -/

/-- **The symbolic data of a word at a reference point**: an ordered list
`s` of affine cut functions which is strictly increasing at `q₀` and monotone on a ball, contains
`0` and `1` among its values (at the indices `lz` and `lo`), and an affine displacement `D k` on
each piece `[s k, s (k+1))`.  The cuts are bounded integer-affine functions with free-coordinate
bound `2 * |w| + 2` and the displacements with bound `2 * |w|`.

Only the pieces `k` with `lz ≤ k.castSucc` and `k.succ ≤ lo` can contain points of `[0,1)`, and
those are the ones the argument uses. -/
structure WordData {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) (L : List (Fin 2 × Bool)) (q₀ : PReal d e) where
  /-- The radius of the ball on which the data hold -/
  ε : ℝ
  hε : 0 < ε
  /-- The number of pieces -/
  m : ℕ
  hm : 0 < m
  /-- The cut functions, in increasing order -/
  s : Fin (m + 1) → ParamAffine d e
  /-- The displacement on each piece -/
  D : Fin m → ParamAffine d e
  /-- The index of the cut `0` -/
  lz : Fin (m + 1)
  /-- The index of the cut `1` -/
  lo : Fin (m + 1)
  hlz : s lz = 0
  hlo : s lo = AffineMap.const ℝ (PReal d e) 1
  /-- The cuts are strictly increasing at the reference point -/
  hstrict : StrictMono fun l => s l q₀
  /-- The cuts are increasing on the ball -/
  hmono : ∀ q ∈ Metric.ball q₀ ε, Monotone fun l => s l q
  /-- The ball lies in the open region -/
  hregion : Metric.ball q₀ ε ⊆ {q | q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e}
  /-- The word translates by `D k` on the `k`-th piece -/
  hpiece : ∀ q ∈ Metric.ball q₀ ε, ∀ k : Fin m, ∀ y ∈ Set.Ico (0 : ℝ) 1,
    s k.castSucc q ≤ y → y < s k.succ q →
      ((L.map (fun p => ltrQ π σ p q)).prod) y = y + D k q
  /-- The cuts are bounded integer-affine functions -/
  hsLat : ∀ k, IsFreeLat (2 * (L.length : ℤ) + 2) (s k)
  /-- The displacements are bounded integer-affine functions -/
  hD : ∀ k, IsFreeLat (2 * (L.length : ℤ)) (D k)

/-- **The robustness of a trivial word, from the symbolic data**: if the word is trivial at the
reference point and every bounded integer-affine function vanishing there is identically zero
(`VanishesAt N₀ q₀`, with `N₀ ≥ 2 * |w|` for the coefficient bound), then the word is trivial on a
neighbourhood.

Step 1: every displacement vanishes at `q₀`, because the word is the identity there and every piece
in the range `[lz, lo]` contains a point of `[0,1)`.  Step 2: `VanishesAt N₀ q₀` kills them
identically, the coefficient bound being `2 * |w| ≤ N₀`.  Step 3: the word is the identity on the
ball. -/
theorem evalWord_eventually_eq_one_of_wordData {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) (w : FreeGroup Gen) {q₀ : PReal d e}
    (N₀ : ℕ) (hgood : VanishesAt N₀ q₀) (hN₀ : 2 * ((w.toWord).length : ℤ) ≤ (N₀ : ℤ))
    (h1 : evalWord w (fOf π q₀) (gOf σ q₀) = 1)
    (W : WordData π σ (w.toWord) q₀) :
    ∀ᶠ q in 𝓝 q₀, evalWord w (fOf π q) (gOf σ q) = 1 := by
  have hid : ((w.toWord).map (fun p => ltrQ π σ p q₀)).prod = 1 := by
    rw [← evalWord_eq_list_prod]
    exact h1
  -- steps 1 and 2: every displacement in the active range vanishes identically
  have hD0 : ∀ k : Fin W.m, W.lz ≤ k.castSucc → k.succ ≤ W.lo → W.D k = 0 := by
    intro k hk1 hk2
    have hmono : Monotone fun l => W.s l q₀ := W.hstrict.monotone
    have hball : q₀ ∈ Metric.ball q₀ W.ε := by
      rw [Metric.mem_ball, dist_self]
      exact W.hε
    have hlzq : W.s W.lz q₀ = 0 := by rw [W.hlz]; rfl
    have hloq : W.s W.lo q₀ = 1 := by rw [W.hlo]; rfl
    have hlt : W.s k.castSucc q₀ < W.s k.succ q₀ := by
      apply W.hstrict
      rw [Fin.lt_def]
      simp [Fin.val_succ, Fin.val_castSucc]
    set y : ℝ := (W.s k.castSucc q₀ + W.s k.succ q₀) / 2 with hy_def
    have hle : W.s k.castSucc q₀ ≤ y := by rw [hy_def]; linarith
    have hylt : y < W.s k.succ q₀ := by rw [hy_def]; linarith
    have hmem : y ∈ Set.Ico (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · have hge := hmono hk1
        simp only [hlzq] at hge
        linarith
      · have hle' := hmono hk2
        simp only [hloq] at hle'
        linarith
    have hdisp := W.hpiece q₀ hball k y hmem hle hylt
    have hyid : ((w.toWord).map (fun p => ltrQ π σ p q₀)).prod y = y := by rw [hid]; rfl
    have hzero : W.D k q₀ = 0 := by linarith
    exact hgood (2 * ((w.toWord).length : ℤ)) (W.D k) hN₀ (W.hD k) hzero
  -- step 3: the word is the identity on the ball
  have hone : ∀ q ∈ Metric.ball q₀ W.ε, evalWord w (fOf π q) (gOf σ q) = 1 := by
    intro q hq
    rw [evalWord_eq_list_prod]
    refine IET.ext (fun x => ?_)
    have hmonoq : Monotone fun l => W.s l q := W.hmono q hq
    have hlzq : W.s W.lz q = 0 := by rw [W.hlz]; rfl
    have hloq : W.s W.lo q = 1 := by rw [W.hlo]; rfl
    by_cases hx : x ∈ Set.Ico (0 : ℝ) 1
    · set k := pieceIndex hmonoq ⟨W.lz, hlzq⟩ ⟨W.lo, hloq⟩ hx.1 with hk
      have hp1 : W.s k.castSucc q ≤ x := pieceIndex_mem hmonoq _ _ hx.1
      have hp2 : x < W.s k.succ q :=
        pieceIndex_lt_succ hmonoq ⟨W.lz, hlzq⟩ ⟨W.lo, hloq⟩ hx.2 hx.1
      obtain ⟨hk1, hk2⟩ :=
        pieceIndex_range hmonoq hlzq hloq hx k hp1 hp2
      have hdisp := W.hpiece q hq k x hx hp1 hp2
      have hDq : W.D k q = 0 := by
        rw [hD0 k hk1 hk2]
        rfl
      rw [hdisp, hDq, add_zero]
      rfl
    · rw [IsIET.eq_of_notMem (IET.isIET _) hx]
      rfl
  exact Filter.Eventually.mono (Metric.ball_mem_nhds q₀ W.hε) hone

/-! ## 6. Sorting the cut candidates, and the one-letter step -/

/-- **Sorting a finite family of affine functions by their values at `q₀`**, keeping one
representative for each distinct value.  If distinct values at `q₀` force equal functions (`hval`,
which goodness provides), the resulting list contains *every* function of the family. -/
theorem exists_sorted_cuts {ι : Type*} [Fintype ι] [Nonempty ι] {d e : ℕ}
    (C : ι → ParamAffine d e) {q₀ : PReal d e}
    (hval : ∀ i j : ι, C i q₀ = C j q₀ → C i = C j)
    (hlt : ∃ i j : ι, C i q₀ < C j q₀) :
    ∃ (m : ℕ) (_ : 0 < m) (_ : m ≤ Fintype.card ι)
      (s : Fin (m + 1) → ParamAffine d e),
      (∀ i, ∃ k, s k = C i) ∧ (∀ k, ∃ i, s k = C i) ∧ StrictMono fun k => s k q₀ := by
  classical
  set V : Finset ℝ := Finset.univ.image (fun i => C i q₀) with hV
  have hVmem : ∀ y, y ∈ V ↔ ∃ i, C i q₀ = y := by
    intro y
    rw [hV, Finset.mem_image]
    exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, Finset.mem_univ _, h⟩⟩
  have hVne : V.Nonempty :=
    ⟨C (Classical.arbitrary ι) q₀, (hVmem _).mpr ⟨Classical.arbitrary ι, rfl⟩⟩
  have h2card : 2 ≤ V.card := by
    obtain ⟨i, j, hij⟩ := hlt
    have hi : C i q₀ ∈ V := (hVmem _).mpr ⟨i, rfl⟩
    have hj : C j q₀ ∈ V := (hVmem _).mpr ⟨j, rfl⟩
    have hss : ({C i q₀, C j q₀} : Finset ℝ) ⊆ V := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hi
      · rw [Finset.mem_singleton] at hy
        exact hy ▸ hj
    have hc := Finset.card_le_card hss
    rw [Finset.card_pair (ne_of_lt hij)] at hc
    omega
  set g := V.orderEmbOfFin rfl with hg
  have hgmono : StrictMono g := g.strictMono
  have hgmem : ∀ k, g k ∈ V := by
    intro k
    rw [hg]
    exact Finset.orderEmbOfFin_mem _ _ k
  have hrange : ∀ y ∈ V, ∃ k, g k = y := by
    intro y hy
    have hsub : Finset.univ.image g ⊆ V := by
      intro z hz
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
      exact hgmem k
    have hcard' : V.card ≤ (Finset.univ.image g).card := by
      rw [Finset.card_image_of_injective _ g.injective, Finset.card_univ, Fintype.card_fin]
    have heq := Finset.eq_of_subset_of_card_le hsub hcard'
    have hy' : y ∈ Finset.univ.image g := by rw [heq]; exact hy
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hy'
    exact ⟨k, hk⟩
  have hsurj : ∀ k : Fin V.card, ∃ i, C i q₀ = g k := fun k => (hVmem _).mp (hgmem k)
  have hgrange : ∀ i, ∃ k : Fin V.card, C i q₀ = g k := by
    intro i
    obtain ⟨k, hk⟩ := hrange _ ((hVmem _).mpr ⟨i, rfl⟩)
    exact ⟨k, hk.symm⟩
  have hcardι : V.card ≤ Fintype.card ι := by
    rw [hV]
    exact Finset.card_image_le
  refine ⟨V.card - 1, by omega, by omega,
    fun k => C (Classical.choose (hsurj ⟨k.val, by have := k.isLt; omega⟩)), ?_, ?_, ?_⟩
  · intro i
    obtain ⟨k, hk⟩ := hgrange i
    refine ⟨⟨k.val, by have := k.isLt; omega⟩, ?_⟩
    have hspec := Classical.choose_spec (hsurj ⟨k.val, by have := k.isLt; omega⟩)
    exact (hval _ i (by rw [hspec, hk])).symm ▸ rfl
  · intro k
    exact ⟨_, rfl⟩
  · intro k l hkl
    have hk := Classical.choose_spec (hsurj ⟨k.val, by have := k.isLt; omega⟩)
    have hl := Classical.choose_spec (hsurj ⟨l.val, by have := l.isLt; omega⟩)
    have hlt' : (⟨k.val, by have := k.isLt; omega⟩ : Fin V.card)
        < ⟨l.val, by have := l.isLt; omega⟩ := by
      rw [Fin.lt_def]
      rw [Fin.lt_def] at hkl
      exact hkl
    have hmono := hgmono hlt'
    rw [← hk, ← hl] at hmono
    exact hmono

/-- **The comparison with any cut, for a piece given by its two bounds**: a point `x ∈ [0,1)` in
the piece `[s k, s (k+1))` is above the `l`-th cut exactly when `l ≤ k.castSucc`. -/
theorem le_iff_of_mem_piece {d e m : ℕ} {s : Fin (m + 1) → ParamAffine d e} {q : PReal d e}
    (hmono : Monotone fun l => s l q) (h0 : ∃ l, s l q = 0) (h1 : ∃ l, s l q = 1)
    {x : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1) {k : Fin m}
    (hk1 : s k.castSucc q ≤ x) (hk2 : x < s k.succ q) (l : Fin (m + 1)) :
    s l q ≤ x ↔ l ≤ k.castSucc := by
  have hKle : pieceIndex hmono h0 h1 hx1 ≤ k := by
    by_contra hcon
    rw [not_le] at hcon
    have h2 : k.succ ≤ (pieceIndex hmono h0 h1 hx1).castSucc := by
      rw [Fin.le_def]
      have hlt := Fin.lt_def.mp hcon
      simp only [Fin.val_succ, Fin.val_castSucc] at hlt ⊢
      omega
    have h3 := hmono h2
    have h4 := pieceIndex_mem hmono h0 h1 hx1
    linarith
  have hKle' : k ≤ pieceIndex hmono h0 h1 hx1 := pieceIndex_max hmono h0 h1 hx1 hk1
  have hK : pieceIndex hmono h0 h1 hx1 = k := le_antisymm hKle hKle'
  have := le_pieceIndex_iff hmono h0 h1 hx2 hx1 l
  rwa [hK] at this

/-- **The cell of a single letter that contains a piece**: the unique `i` with
`lU i.castSucc ≤ k.castSucc < lU i.succ`, where `lU` gives the positions of the letter's cuts in
the sorted list.  Defined with a default, which is used only for pieces that are empty. -/
noncomputable def letterCellIndex {p m' : ℕ} (lU : Fin (p + 1) → Fin (m' + 1)) (hp : 0 < p)
    (k : Fin m') : Fin p :=
  if h : ∃ i : Fin p, lU i.castSucc ≤ k.castSucc ∧ k.castSucc < lU i.succ then
    Classical.choose h else ⟨0, hp⟩

theorem letterCellIndex_spec {p m' : ℕ} {lU : Fin (p + 1) → Fin (m' + 1)} {hp : 0 < p}
    {k : Fin m'}
    (h : ∃ i : Fin p, lU i.castSucc ≤ k.castSucc ∧ k.castSucc < lU i.succ) :
    lU (letterCellIndex lU hp k).castSucc ≤ k.castSucc ∧
      k.castSucc < lU (letterCellIndex lU hp k).succ := by
  rw [letterCellIndex, dite_eq_left h]
  exact Classical.choose_spec h

/-- **The old piece that a piece of the composite falls into**: the unique `l` with
`lP l.castSucc i ≤ k.castSucc < lP l.succ i`, where `lP` gives the positions of the preimages of
the old cuts. -/
noncomputable def oldPieceIndex {m m' p : ℕ} (lP : Fin (m + 1) → Fin p → Fin (m' + 1))
    (hm : 0 < m) (i : Fin p) (k : Fin m') : Fin m :=
  if h : ∃ l : Fin m, lP l.castSucc i ≤ k.castSucc ∧ k.castSucc < lP l.succ i then
    Classical.choose h else ⟨0, hm⟩

theorem oldPieceIndex_spec {m m' p : ℕ} {lP : Fin (m + 1) → Fin p → Fin (m' + 1)} {hm : 0 < m}
    {i : Fin p} {k : Fin m'}
    (h : ∃ l : Fin m, lP l.castSucc i ≤ k.castSucc ∧ k.castSucc < lP l.succ i) :
    lP (oldPieceIndex lP hm i k).castSucc i ≤ k.castSucc ∧
      k.castSucc < lP (oldPieceIndex lP hm i k).succ i := by
  rw [oldPieceIndex, dite_eq_left h]
  exact Classical.choose_spec h

/-! ## 7. The one-letter step -/

/-- **Appending a letter to the word**: the symbolic data of `L` and of the one-letter word `[p]`
combine into the symbolic data of `L ++ [p]`.

The candidate cuts of the composite are the cuts of the letter and the preimages of the cuts of `L`
under the letter, the latter being `W.s l - V.D i`.  Sorting them at `q₀` gives the new list, and
the displacement of a piece is the sum of the old displacement and the letter's displacement. -/
theorem wordData_append_singleton {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) {L : List (Fin 2 × Bool)} {b : Fin 2 × Bool}
    {q₀ : PReal d e}
    (N₀ : ℕ) (hgood : VanishesAt N₀ q₀) (hN₀ : 4 * (L ++ [b]).length + 4 ≤ N₀)
    (W : WordData π σ L q₀) (V : WordData π σ [b] q₀) :
    Nonempty (WordData π σ (L ++ [b]) q₀) := by
  classical
  -- the coefficient bounds of the candidates
  have hlen : ((L ++ [b]).length : ℤ) = (L.length : ℤ) + 1 := by
    rw [List.length_append, List.length_singleton]
    push_cast
    ring
  have hlen1 : (([b] : List (Fin 2 × Bool)).length : ℤ) = 1 := by
    rw [List.length_singleton]
    rfl
  have hLnn : (0 : ℤ) ≤ (L.length : ℤ) := Int.natCast_nonneg _
  -- the candidate cut family: the letter's cuts and the preimages of the old cuts
  set C : Fin (V.m + 1) ⊕ (Fin (W.m + 1) × Fin V.m) → ParamAffine d e := fun i =>
    match i with
    | Sum.inl j => V.s j
    | Sum.inr li => W.s li.1 - V.D li.2 with hCdef
  have hlat : ∀ i, IsFreeLat (2 * ((L ++ [b]).length : ℤ) + 2) (C i) := by
    rintro (j | ⟨l, i'⟩)
    · change IsFreeLat (2 * ((L ++ [b]).length : ℤ) + 2) (V.s j)
      refine (V.hsLat j).mono ?_
      rw [hlen, hlen1]
      linarith
    · change IsFreeLat (2 * ((L ++ [b]).length : ℤ) + 2) (W.s l - V.D i')
      refine ((W.hsLat l).sub (V.hD i')).mono ?_
      rw [hlen, hlen1]
      linarith
  have hlt : ∃ i j : (Fin (V.m + 1) ⊕ (Fin (W.m + 1) × Fin V.m)), C i q₀ < C j q₀ := by
    refine ⟨Sum.inl V.lz, Sum.inl V.lo, ?_⟩
    change V.s V.lz q₀ < V.s V.lo q₀
    rw [V.hlz, V.hlo]
    norm_num
  have hval : ∀ i j, C i q₀ = C j q₀ → C i = C j := by
    intro i j hij
    have hsub : IsFreeLat (2 * ((L ++ [b]).length : ℤ) + 2
        + (2 * ((L ++ [b]).length : ℤ) + 2)) (C i - C j) := (hlat i).sub (hlat j)
    have hb : 2 * ((L ++ [b]).length : ℤ) + 2 + (2 * ((L ++ [b]).length : ℤ) + 2) ≤ (N₀ : ℤ) := by
      have hcast : ((4 * (L ++ [b]).length + 4 : ℕ) : ℤ) ≤ (N₀ : ℤ) := by exact_mod_cast hN₀
      push_cast at hcast ⊢
      linarith
    have hz : C i - C j = 0 := by
      refine hgood _ _ hb hsub ?_
      change C i q₀ - C j q₀ = 0
      rw [hij, sub_self]
    exact sub_eq_zero.mp hz
  obtain ⟨m', hm', -, s', hcov, hcov', hstrict'⟩ := exists_sorted_cuts C hval hlt
  -- the positions of the letter's cuts and of the preimages in the sorted list
  set lU : Fin (V.m + 1) → Fin (m' + 1) := fun j => Classical.choose (hcov (Sum.inl j)) with hlUdef
  have hlU : ∀ j, s' (lU j) = V.s j := fun j => Classical.choose_spec (hcov (Sum.inl j))
  set lP : Fin (W.m + 1) → Fin V.m → Fin (m' + 1) :=
    fun l i => Classical.choose (hcov (Sum.inr (l, i))) with hlPdef
  have hlP : ∀ l i, s' (lP l i) = W.s l - V.D i :=
    fun l i => Classical.choose_spec (hcov (Sum.inr (l, i)))
  -- both are strictly increasing at `q₀`
  have hlUmono : StrictMono lU := by
    intro a c hac
    have h3 : s' (lU a) q₀ < s' (lU c) q₀ := by
      rw [hlU a, hlU c]
      exact V.hstrict hac
    by_contra hcon
    rw [not_lt] at hcon
    have h1 : s' (lU c) q₀ ≤ s' (lU a) q₀ := hstrict'.monotone hcon
    linarith
  have hlPmono : ∀ i, StrictMono fun l => lP l i := by
    intro i a c hac
    have h3 : s' (lP a i) q₀ < s' (lP c i) q₀ := by
      rw [hlP a i, hlP c i]
      exact sub_lt_sub_right (W.hstrict hac) _
    by_contra hcon
    rw [not_lt] at hcon
    have h1 : s' (lP c i) q₀ ≤ s' (lP a i) q₀ := hstrict'.monotone hcon
    linarith
  -- the new ball
  obtain ⟨εs, hεs, hstrictball⟩ := exists_ball_strictMono s' hstrict'
  refine ⟨?_⟩
  refine
    { ε := min W.ε (min V.ε εs)
      hε := lt_min W.hε (lt_min V.hε hεs)
      m := m'
      hm := hm'
      s := s'
      D := fun k => W.D (oldPieceIndex lP W.hm (letterCellIndex lU V.hm k) k)
        + V.D (letterCellIndex lU V.hm k)
      lz := lU V.lz
      lo := lU V.lo
      hlz := ?_
      hlo := ?_
      hstrict := hstrict'
      hmono := ?_
      hregion := ?_
      hpiece := ?_
      hsLat := ?_
      hD := ?_ }
  · rw [hlU V.lz, V.hlz]
  · rw [hlU V.lo, V.hlo]
  · intro q hq
    have hsubS : Metric.ball q₀ (min W.ε (min V.ε εs)) ⊆ Metric.ball q₀ εs :=
      Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _))
    exact (hstrictball q (hsubS hq)).monotone
  · intro q hq
    exact W.hregion (Metric.ball_subset_ball (min_le_left _ _) hq)
  · -- the piece statement
    intro q hq k x hx h1 h2
    have hqW : q ∈ Metric.ball q₀ W.ε := Metric.ball_subset_ball (min_le_left _ _) hq
    have hqV : q ∈ Metric.ball q₀ V.ε :=
      Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _)) hq
    have hsubS : Metric.ball q₀ (min W.ε (min V.ε εs)) ⊆ Metric.ball q₀ εs :=
      Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _))
    have hmono' : Monotone fun l => s' l q := (hstrictball q (hsubS hq)).monotone
    have hlzq : s' (lU V.lz) q = 0 := by rw [hlU V.lz, V.hlz]; rfl
    have hloq : s' (lU V.lo) q = 1 := by rw [hlU V.lo, V.hlo]; rfl
    have hcmp : ∀ l : Fin (m' + 1), s' l q ≤ x ↔ l ≤ k.castSucc :=
      fun l => le_iff_of_mem_piece hmono' ⟨_, hlzq⟩ ⟨_, hloq⟩ hx.1 hx.2 h1 h2 l
    set iO : Fin V.m := letterCellIndex lU V.hm k with hiO
    set lO : Fin W.m := oldPieceIndex lP W.hm iO k with hlO
    -- the letter's cell containing `x`
    have hmonoV : Monotone fun l => V.s l q := V.hmono q hqV
    have hex_i : ∃ i : Fin V.m, V.s i.castSucc q ≤ x ∧ x < V.s i.succ q :=
      ⟨pieceIndex hmonoV ⟨V.lz, by rw [V.hlz]; rfl⟩ ⟨V.lo, by rw [V.hlo]; rfl⟩ hx.1,
        pieceIndex_mem hmonoV _ _ hx.1,
        pieceIndex_lt_succ hmonoV _ _ hx.2 hx.1⟩
    have hex_idx : ∃ i : Fin V.m, lU i.castSucc ≤ k.castSucc ∧ k.castSucc < lU i.succ := by
      obtain ⟨i, hi1, hi2⟩ := hex_i
      refine ⟨i, ?_, ?_⟩
      · rw [← hcmp (lU i.castSucc), hlU]
        exact hi1
      · by_contra hcon
        rw [not_lt] at hcon
        have hge : s' (lU i.succ) q ≤ x := (hcmp (lU i.succ)).mpr hcon
        rw [hlU] at hge
        exact absurd hge (not_le.mpr hi2)
    obtain ⟨hi1, hi2⟩ := letterCellIndex_spec (lU := lU) (hp := V.hm) (k := k) hex_idx
    have hcell1 : V.s iO.castSucc q ≤ x := by
      have := (hcmp (lU iO.castSucc)).mpr hi1
      rwa [hlU] at this
    have hcell2 : x < V.s iO.succ q := by
      by_contra hcon
      rw [not_lt] at hcon
      have hge : lU iO.succ ≤ k.castSucc := by
        rw [← hcmp (lU iO.succ), hlU]
        exact hcon
      exact absurd hge (not_le.mpr hi2)
    have hletter : ltrQ π σ b q x = x + V.D iO q := by
      have h := V.hpiece q hqV iO x hx hcell1 hcell2
      simpa using h
    -- the old piece containing the image
    have hy : ltrQ π σ b q x ∈ Set.Ico (0 : ℝ) 1 :=
      IsIET.mapsTo (IET.isIET (ltrQ π σ b q)) hx
    have hy1 : (0 : ℝ) ≤ ltrQ π σ b q x := hy.1
    have hy2 : ltrQ π σ b q x < 1 := hy.2
    have hmonoW : Monotone fun l => W.s l q := W.hmono q hqW
    set lu : Fin W.m := pieceIndex hmonoW ⟨W.lz, by rw [W.hlz]; rfl⟩
      ⟨W.lo, by rw [W.hlo]; rfl⟩ hy1 with hlu
    have hlu1 : W.s lu.castSucc q ≤ ltrQ π σ b q x := pieceIndex_mem hmonoW _ _ hy1
    have hlu2 : ltrQ π σ b q x < W.s lu.succ q := pieceIndex_lt_succ hmonoW _ _ hy2 hy1
    have hex_l : ∃ l : Fin W.m, lP l.castSucc iO ≤ k.castSucc ∧ k.castSucc < lP l.succ iO := by
      refine ⟨lu, ?_, ?_⟩
      · rw [← hcmp (lP lu.castSucc iO), hlP]
        change W.s lu.castSucc q - V.D iO q ≤ x
        linarith [hletter]
      · by_contra hcon
        rw [not_lt] at hcon
        have hge : s' (lP lu.succ iO) q ≤ x := (hcmp (lP lu.succ iO)).mpr hcon
        rw [hlP] at hge
        have hge' : W.s lu.succ q - V.D iO q ≤ x := hge
        linarith [hletter]
    obtain ⟨hl1, hl2⟩ := oldPieceIndex_spec (lP := lP) (hm := W.hm) (i := iO) (k := k) hex_l
    have hold1 : W.s lO.castSucc q ≤ ltrQ π σ b q x := by
      have hthis : (W.s lO.castSucc - V.D iO) q ≤ x := by
        rw [← hlP]
        exact (hcmp (lP lO.castSucc iO)).mpr hl1
      have hthis' : W.s lO.castSucc q - V.D iO q ≤ x := hthis
      linarith [hletter]
    have hold2 : ltrQ π σ b q x < W.s lO.succ q := by
      by_contra hcon
      rw [not_lt] at hcon
      have h1 : (W.s lO.succ - V.D iO) q ≤ x := by
        have h := hcon
        rw [hletter] at h
        change W.s lO.succ q - V.D iO q ≤ x
        linarith
      have h2 : lP lO.succ iO ≤ k.castSucc :=
        (hcmp (lP lO.succ iO)).mp (by rw [hlP]; exact h1)
      exact absurd h2 (not_le.mpr hl2)
    have hold := W.hpiece q hqW lO (ltrQ π σ b q x) ⟨hy1, hy2⟩ hold1 hold2
    calc ((L ++ [b]).map (fun r => ltrQ π σ r q)).prod x
        = (L.map (fun r => ltrQ π σ r q)).prod ((fun r => ltrQ π σ r q) b x) := by
          rw [List.map_append, List.prod_append]
          rfl
      _ = ltrQ π σ b q x + W.D lO q := hold
      _ = x + (W.D lO + V.D iO) q := by
          rw [hletter]
          change x + V.D iO q + W.D lO q = x + (W.D lO q + V.D iO q)
          ring
  · -- the cut bounds
    intro k
    obtain ⟨i, hi⟩ := hcov' k
    rw [hi]
    exact hlat i
  · -- the displacement bounds
    intro k
    have h := (W.hD (oldPieceIndex lP W.hm (letterCellIndex lU V.hm k) k)).add
      (V.hD (letterCellIndex lU V.hm k))
    refine h.mono ?_
    rw [hlen, hlen1]
    linarith

/-! ## 8. Assembling the word by induction -/

/-- **The symbolic data of any nonempty list of letters**, by induction from the one-letter case.
Each step drops the vanishing threshold to the length of the prefix, using `VanishesAt` at the
smaller bound. -/
theorem exists_wordData_ne_nil {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) {q₀ : PReal d e}
    (hsingle : ∀ b : Fin 2 × Bool, Nonempty (WordData π σ [b] q₀)) (N₀ : ℕ)
    (hgood : VanishesAt N₀ q₀) :
    ∀ (L : List (Fin 2 × Bool)), L ≠ [] → 4 * L.length + 4 ≤ N₀ →
      Nonempty (WordData π σ L q₀) := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro hne; exact absurd rfl hne
  | append_singleton L b ih =>
    intro _ hbound
    rcases L with _ | ⟨c, L'⟩
    · exact hsingle b
    · have hne' : (c :: L') ≠ [] := List.cons_ne_nil _ _
      have hlen : 4 * (c :: L').length + 4 ≤ N₀ := by
        rw [List.length_append, List.length_singleton] at hbound
        omega
      exact wordData_append_singleton π σ N₀ hgood hbound (Classical.choice (ih hne' hlen))
        (Classical.choice (hsingle b))

/-- **The robustness of a trivial word, at a numerical threshold**: for a word `w` of length `n`,
if `w` is trivial at a reference point `q₀` of the open region which is good at threshold
`4 * n + 4`, then `w` is trivial on a neighbourhood of `q₀`.

The threshold is the one that makes the *cut candidates* pairwise distinct at `q₀`: their
coefficient bound is `2 * (n + 1)`, so differences of two of them are bounded by `4 * n + 4`.  The
displacements themselves only need `2 * n`.  A smaller threshold does not support this argument,
which is why the statement with the paper's hypothesis `Ω'` (`evalWord_eventually_eq_one`) is the
one to use. -/
theorem evalWord_eventually_eq_one_of_vanishesAt {d e : ℕ} [NeZero d] [NeZero e]
    (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) (w : FreeGroup Gen) {q₀ : PReal d e}
    (N₀ : ℕ) (hgood : VanishesAt N₀ q₀) (hN₀ : 4 * (w.toWord).length + 4 ≤ N₀)
    (h1 : evalWord w (fOf π q₀) (gOf σ q₀) = 1)
    (hsingle : ∀ b : Fin 2 × Bool, Nonempty (WordData π σ [b] q₀)) :
    ∀ᶠ q in 𝓝 q₀, evalWord w (fOf π q) (gOf σ q) = 1 := by
  rcases hlst : (w.toWord) with _ | ⟨c, L'⟩
  · have hw : w = 1 := by
      conv_lhs => rw [← FreeGroup.mk_toWord (x := w)]
      rw [hlst]
      rfl
    subst hw
    simp
  · have hne : w.toWord ≠ [] := by rw [hlst]; exact List.cons_ne_nil _ _
    have h2 : 2 * ((w.toWord).length : ℤ) ≤ (N₀ : ℤ) := by
      have hcast : ((4 * (w.toWord).length + 4 : ℕ) : ℤ) ≤ (N₀ : ℤ) := by exact_mod_cast hN₀
      have hnn : (0 : ℤ) ≤ ((w.toWord).length : ℤ) := Int.natCast_nonneg _
      push_cast at hcast
      linarith
    exact evalWord_eventually_eq_one_of_wordData π σ w N₀ hgood h2 h1
      (Classical.choice (exists_wordData_ne_nil π σ hsingle N₀ hgood (w.toWord) hne hN₀))

end IntervalExchange.Pair
