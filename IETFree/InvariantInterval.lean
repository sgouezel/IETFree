/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.BlockRescaling

/-!
# The restriction of an exchange to an invariant interval

This module has no counterpart in the numbering of the paper: it is the lemma by which Lemma 3.4
turns the *second* generator `g` into an exchange of `[0,1)` on a block, exactly as
`RescaleBlock.mkIET1_rescale_subinterval` does for the composition.

## The restriction of an exchange to an invariant interval is an exchange

Let `g = mkIET1 mu σ hl` be an exchange of `[0, 1)` with all lengths positive, and let
`[u, v) ⊆ [0, 1)` be invariant: `x ∈ [u, v) → g x ∈ [u, v)`.  Then the rescaled restriction
of `g` to `[u, v)` is again an exchange of `[0, 1)`, with the **same** permutation `σ` and with
lengths `mu' j = max 0 (min v (upperEnd mu j) - max u (leftEnd mu j)) / (v - u)`.

The workhorse is the clamping function `clamp u v t = min v (max u t)`: the difference of the clamp
at the two ends of a cell is the length of the part of that cell inside `[u, v)`, and it telescopes.
-/

open Finset

open scoped BigOperators NNReal

namespace RestrictIET

variable {u v : ℝ}

/-! ### The clamping function -/

/-- Clamping to `[u, v]`: `t ↦ min v (max u t)`. -/
def clamp (u v t : ℝ) : ℝ := min v (max u t)

theorem clamp_zero (h0u : 0 ≤ u) (huv : u ≤ v) : clamp u v 0 = u := by
  rw [clamp, max_eq_left h0u, min_eq_right huv]

theorem clamp_one (huv : u < v) (hv1 : v ≤ 1) : clamp u v 1 = v := by
  rw [clamp, max_eq_right (le_of_lt (lt_of_lt_of_le huv hv1)), min_eq_left hv1]

/-- **The clamped length of an interval.**  The part of `[l, r)` inside `[u, v)` has length
`max 0 (min v r - max u l)`, which is also `clamp u v r - clamp u v l`. -/
theorem clamp_sub_clamp (huv : u < v) {l r : ℝ} (hlr : l ≤ r) :
    clamp u v r - clamp u v l = max 0 (min v r - max u l) := by
  rw [clamp, clamp]
  rcases le_or_gt v l with hvl | hvl
  · -- the interval is at or beyond `v`: both sides vanish
    have h1 : min v (max u l) = v :=
      min_eq_left (le_trans hvl (le_max_right u l))
    have h2 : min v (max u r) = v :=
      min_eq_left (le_trans (le_trans hvl hlr) (le_max_right u r))
    have h3 : min v r = v := min_eq_left (le_trans hvl hlr)
    rw [h1, h2, h3, sub_self,
      max_eq_left (by linarith [le_max_right u l] : v - max u l ≤ 0)]
  · have hcl : min v (max u l) = max u l :=
      min_eq_right (max_le (le_of_lt huv) (le_of_lt hvl))
    rw [hcl]
    rcases le_or_gt v r with hvr | hvr
    · have h1 : min v (max u r) = v :=
        min_eq_left (le_trans hvr (le_max_right u r))
      have h2 : min v r = v := min_eq_left hvr
      have h3 : 0 ≤ v - max u l := by
        linarith [max_lt huv hvl]
      rw [h1, h2, max_eq_right h3]
    · have h1 : min v (max u r) = max u r :=
        min_eq_right (max_le (le_of_lt huv) (le_of_lt hvr))
      have h2 : min v r = r := min_eq_right (le_of_lt hvr)
      rw [h1, h2]
      rcases le_or_gt u l with hul | hul
      · have h3 : max u l = l := max_eq_right hul
        have h4 : max u r = r := max_eq_right (le_trans hul hlr)
        rw [h3, h4, max_eq_right (by linarith : (0 : ℝ) ≤ r - l)]
      · have h3 : max u l = u := max_eq_left (le_of_lt hul)
        rw [h3]
        rcases le_or_gt u r with hur | hur
        · have h4 : max u r = r := max_eq_right hur
          rw [h4, max_eq_right (by linarith : (0 : ℝ) ≤ r - u)]
        · have h4 : max u r = u := max_eq_left (le_of_lt hur)
          rw [h4, sub_self, max_eq_left (by linarith : r - u ≤ 0)]

/-! ### The telescoping of the clamped lengths

For a length vector `lam` with total mass `1`, the clamped lengths of all the cells add up to the
length of `[u, v)`. -/

section Telescope

variable {n : ℕ}

/-- The prefix mass of `lam` up to `k`, as a sum over `Finset.range`. -/
noncomputable def prefixMass (lam : Fin n → ℝ≥0) (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.range k, lamNat lam m

theorem prefixMass_zero (lam : Fin n → ℝ≥0) : prefixMass lam 0 = 0 := by
  simp [prefixMass]

theorem prefixMass_succ (lam : Fin n → ℝ≥0) (k : ℕ) :
    prefixMass lam (k + 1) = prefixMass lam k + lamNat lam k := by
  rw [prefixMass, prefixMass, Finset.sum_range_succ]

theorem prefixMass_eq_leftEnd (lam : Fin n → ℝ≥0) {k : ℕ} (hk : k < n) :
    prefixMass lam k = leftEnd lam ⟨k, hk⟩ := by
  rw [prefixMass, leftEnd_eq_sum_range]

theorem prefixMass_eq_upperEnd (lam : Fin n → ℝ≥0) {k : ℕ} (hk : k < n) :
    prefixMass lam (k + 1) = upperEnd lam ⟨k, hk⟩ := by
  rw [prefixMass_succ, prefixMass_eq_leftEnd lam hk, lamNat_of_lt hk, upperEnd_eq]

theorem prefixMass_eq_total (lam : Fin n → ℝ≥0) :
    prefixMass lam n = ∑ i, (lam i : ℝ) := by
  rw [prefixMass, RescaleBlock.sum_range_lamNat_eq_total]

/-- **The clamped lengths telescope.** -/
theorem sum_clamp_sub (lam : Fin n → ℝ≥0) (hlam : (∑ i, (lam i : ℝ)) = 1)
    (h0u : 0 ≤ u) (huv : u < v) (hv1 : v ≤ 1) :
    ∑ i : Fin n, (clamp u v (upperEnd lam i) - clamp u v (leftEnd lam i)) = v - u := by
  have hstep : ∀ i : Fin n,
      clamp u v (upperEnd lam i) - clamp u v (leftEnd lam i)
        = clamp u v (prefixMass lam ((i : ℕ) + 1)) - clamp u v (prefixMass lam (i : ℕ)) := by
    intro i
    rw [prefixMass_eq_upperEnd lam i.isLt, prefixMass_eq_leftEnd lam i.isLt]
  calc ∑ i : Fin n, (clamp u v (upperEnd lam i) - clamp u v (leftEnd lam i))
      = ∑ i : Fin n,
          (clamp u v (prefixMass lam ((i : ℕ) + 1)) - clamp u v (prefixMass lam (i : ℕ))) :=
        Finset.sum_congr rfl (fun i _ => hstep i)
    _ = ∑ k ∈ Finset.range n,
          (clamp u v (prefixMass lam (k + 1)) - clamp u v (prefixMass lam k)) :=
        Fin.sum_univ_eq_sum_range
          (fun k => clamp u v (prefixMass lam (k + 1)) - clamp u v (prefixMass lam k)) n
    _ = clamp u v (prefixMass lam n) - clamp u v (prefixMass lam 0) :=
        Finset.sum_range_sub (fun k => clamp u v (prefixMass lam k)) n
    _ = v - u := by
        rw [prefixMass_eq_total, prefixMass_zero, hlam, clamp_one huv hv1,
          clamp_zero h0u (le_of_lt huv)]

/-- **The prefix sums of the clamped lengths are the clamped prefix sums.** -/
theorem leftEnd_of_clamp_sub {lam lam' : Fin n → ℝ≥0}
    (h : ∀ i, (lam' i : ℝ)
      = (clamp u v (upperEnd lam i) - clamp u v (leftEnd lam i)) / (v - u))
    (huv : u < v) (h0u : 0 ≤ u) (i : Fin n) :
    leftEnd lam' i = (clamp u v (leftEnd lam i) - u) / (v - u) := by
  have hvu : v - u ≠ 0 := by linarith
  have hstep : ∀ k : ℕ, k < i.val →
      (lamNat lam' k)
        = (clamp u v (prefixMass lam (k + 1)) - clamp u v (prefixMass lam k)) / (v - u) := by
    intro k hk
    rw [lamNat_of_lt (by omega : k < n), h ⟨k, by omega⟩,
      prefixMass_eq_upperEnd lam (by omega : k < n), prefixMass_eq_leftEnd lam (by omega : k < n)]
  calc leftEnd lam' i = ∑ k ∈ Finset.range i.val, lamNat lam' k := leftEnd_eq_sum_range lam' i
    _ = ∑ k ∈ Finset.range i.val, (clamp u v (prefixMass lam (k + 1))
          - clamp u v (prefixMass lam k)) / (v - u) := by
        refine Finset.sum_congr rfl (fun k hk => hstep k (Finset.mem_range.mp hk))
    _ = (∑ k ∈ Finset.range i.val, (clamp u v (prefixMass lam (k + 1))
          - clamp u v (prefixMass lam k))) / (v - u) := (Finset.sum_div _ _ _).symm
    _ = (clamp u v (prefixMass lam i.val) - clamp u v (prefixMass lam 0)) / (v - u) := by
        rw [Finset.sum_range_sub (fun k => clamp u v (prefixMass lam k)) i.val]
    _ = (clamp u v (leftEnd lam i) - u) / (v - u) := by
        rw [prefixMass_eq_leftEnd lam i.isLt, prefixMass_zero,
          clamp_zero h0u (le_of_lt huv)]

end Telescope

section Main

variable {e : ℕ} [NeZero e] {mu : Fin e → ℝ≥0} {σ : Equiv.Perm (Fin e)}

/-- **The truncated cell is mapped into the truncated image.**  For a point of the cell `i` of `mu`
that lies in `[u, v)`, the translated point lies in `[u, v)` (by invariance) and in the image of the
cell, whence it lies in the part of the image that is inside `[u, v)`. -/
theorem image_truncation_subset (hl : (∑ j, mu j) = 1) {u v : ℝ} (h0u : 0 ≤ u) (_huv : u < v)
    (_hv1 : v ≤ 1)
    (hinv : ∀ x ∈ Set.Ico u v, (mkIET1 mu σ hl x ∈ Set.Ico u v ↔ x ∈ Set.Ico u v))
    (i : Fin e) :
    ∀ z : ℝ, max u (leftEnd mu i) ≤ z → z < min v (upperEnd mu i) →
      (max u (imageLeft σ mu i) ≤ z + (imageLeft σ mu i - leftEnd mu i) ∧
        z + (imageLeft σ mu i - leftEnd mu i)
          < min v (imageLeft σ mu i + (mu i : ℝ))) := by
  have htot : (∑ j, (mu j : ℝ)) = 1 := by
    rw [← NNReal.coe_sum, hl, NNReal.coe_one]
  intro z hz1 hz2
  have hzl : leftEnd mu i ≤ z := le_trans (le_max_right u _) hz1
  have hzu : u ≤ z := le_trans (le_max_left u _) hz1
  have hzr : z < upperEnd mu i := lt_of_lt_of_le hz2 (min_le_right _ _)
  have hzv : z < v := lt_of_lt_of_le hz2 (min_le_left _ _)
  have hz0 : 0 ≤ z := le_trans h0u hzu
  have hztot : z ∈ Set.Ico (0 : ℝ) (∑ j, (mu j : ℝ)) := by
    refine ⟨hz0, ?_⟩
    rw [htot]
    exact lt_of_lt_of_le hzr (by rw [← htot]; exact upperEnd_le_total mu i)
  have hidx : idx mu z hztot.1 = i := idx_eq mu hztot hzl hzr
  have hg : mkIET1 mu σ hl z = z + (imageLeft σ mu i - leftEnd mu i) := by
    rw [mkIET1_apply mu σ hl hztot, hidx]
  have hmem : mkIET1 mu σ hl z ∈ Set.Ico u v :=
    (hinv z ⟨hzu, hzv⟩).mpr ⟨hzu, hzv⟩
  rw [hg] at hmem
  obtain ⟨hm1, hm2⟩ := hmem
  constructor
  · exact max_le hm1 (by linarith)
  · have h2 : z < leftEnd mu i + (mu i : ℝ) := by
      rw [upperEnd_eq] at hzr; exact hzr
    exact lt_min hm2 (by linarith)

omit [NeZero e] in
/-- The translate of a truncated cell is contained in the truncated image, so the lower end of the
truncated image is at most the translated lower end. -/
theorem min_add_translation_le {u v Y : ℝ} (i : Fin e)
    (hne : max u (leftEnd mu i) < min v (upperEnd mu i))
    (hpt : ∀ z : ℝ, max u (leftEnd mu i) ≤ z → z < min v (upperEnd mu i) →
      (max u (imageLeft σ mu i) ≤ z + (imageLeft σ mu i - leftEnd mu i) ∧
        z + (imageLeft σ mu i - leftEnd mu i) < Y)) :
    min v (upperEnd mu i) + (imageLeft σ mu i - leftEnd mu i) ≤ Y := by
  refine le_of_forall_lt (fun y hy => ?_)
  rcases le_or_gt (max u (leftEnd mu i) + (imageLeft σ mu i - leftEnd mu i)) y with hy1 | hy1
  · have hz1 : max u (leftEnd mu i) ≤ y - (imageLeft σ mu i - leftEnd mu i) := by linarith
    have hz2 : y - (imageLeft σ mu i - leftEnd mu i) < min v (upperEnd mu i) := by linarith
    have := (hpt _ hz1 hz2).2
    linarith
  · exact hy1.trans (hpt _ le_rfl hne).2

/-- **The clamped length of the image of a cell is the clamped length of the cell.**  This is where
the invariance of `[u, v)` enters: the invariance gives that each truncated cell is mapped into its
truncated image, and the two families of truncated intervals have total length `v - u`, once for the
cells of `mu` and once for the cells of `imageLengths σ mu`. -/
theorem clamp_imageLengths_eq (hl : (∑ j, mu j) = 1) {u v : ℝ} (h0u : 0 ≤ u) (huv : u < v)
    (hv1 : v ≤ 1)
    (hinv : ∀ x ∈ Set.Ico u v, (mkIET1 mu σ hl x ∈ Set.Ico u v ↔ x ∈ Set.Ico u v))
    (i : Fin e) :
    clamp u v (upperEnd (imageLengths σ mu) (σ i))
        - clamp u v (leftEnd (imageLengths σ mu) (σ i))
      = clamp u v (upperEnd mu i) - clamp u v (leftEnd mu i) := by
  classical
  have htot : (∑ j, (mu j : ℝ)) = 1 := by
    rw [← NNReal.coe_sum, hl, NNReal.coe_one]
  have hnu : (∑ k, (imageLengths σ mu k : ℝ)) = 1 := by
    rw [sum_imageLengths, htot]
  have hLI : ∀ j : Fin e, leftEnd mu j ≤ upperEnd mu j := fun j => by
    rw [upperEnd_eq]; linarith [(mu j).coe_nonneg]
  have hLI' : ∀ m : Fin e, leftEnd (imageLengths σ mu) m ≤ upperEnd (imageLengths σ mu) m :=
    fun m => by rw [upperEnd_eq]; linarith [((imageLengths σ mu) m).coe_nonneg]
  -- the termwise inequality
  have hle : ∀ i : Fin e, clamp u v (upperEnd mu i) - clamp u v (leftEnd mu i)
      ≤ clamp u v (upperEnd (imageLengths σ mu) (σ i))
        - clamp u v (leftEnd (imageLengths σ mu) (σ i)) := by
    intro i
    have hLν : leftEnd (imageLengths σ mu) (σ i) = imageLeft σ mu i :=
      (imageLeft_eq_leftEnd σ mu i).symm
    have hUν : upperEnd (imageLengths σ mu) (σ i) = imageLeft σ mu i + (mu i : ℝ) := by
      rw [upperEnd_eq, hLν]
      simp [imageLengths]
    rw [clamp_sub_clamp huv (hLI i), clamp_sub_clamp huv (hLI' (σ i)), hLν, hUν]
    rcases le_or_gt (min v (upperEnd mu i)) (max u (leftEnd mu i)) with hemp | hne
    · rw [max_eq_left (by linarith :
        min v (upperEnd mu i) - max u (leftEnd mu i) ≤ 0)]
      exact le_max_left _ _
    · have h1 := (image_truncation_subset hl h0u huv hv1 hinv i _ le_rfl hne).1
      have h2 := min_add_translation_le (u := u) (v := v) i hne
        (image_truncation_subset hl h0u huv hv1 hinv i)
      have h3 : (0 : ℝ) ≤ min v (imageLeft σ mu i + (mu i : ℝ))
          - max u (imageLeft σ mu i) := by
        linarith
      rw [max_eq_right h3,
        max_eq_right (by linarith : (0 : ℝ) ≤ min v (upperEnd mu i) - max u (leftEnd mu i))]
      linarith
  -- the two total sums agree
  have hsum1 : ∑ j : Fin e, (clamp u v (upperEnd mu j) - clamp u v (leftEnd mu j)) = v - u :=
    sum_clamp_sub mu htot h0u huv hv1
  have hsum2 : ∑ j : Fin e, (clamp u v (upperEnd (imageLengths σ mu) (σ j))
      - clamp u v (leftEnd (imageLengths σ mu) (σ j))) = v - u := by
    rw [Equiv.sum_comp σ
      (fun m => clamp u v (upperEnd (imageLengths σ mu) m)
        - clamp u v (leftEnd (imageLengths σ mu) m))]
    exact sum_clamp_sub (imageLengths σ mu) hnu h0u huv hv1
  have hsum0 : ∑ j : Fin e, ((clamp u v (upperEnd (imageLengths σ mu) (σ j))
      - clamp u v (leftEnd (imageLengths σ mu) (σ j)))
        - (clamp u v (upperEnd mu j) - clamp u v (leftEnd mu j))) = 0 := by
    rw [Finset.sum_sub_distrib, hsum2, hsum1, sub_self]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (fun j _ => sub_nonneg.mpr (hle j))).mp hsum0 i (Finset.mem_univ i)
  linarith

/-- **T4**: an exchange restricted to an invariant interval, rescaled to `[0, 1)`, is the exchange
with the truncated lengths and the same permutation. -/
theorem mkIET1_restrict_invariant (hl : (∑ j, mu j) = 1) (_hpos : Positive mu) {u v : ℝ}
    (h0u : 0 ≤ u) (huv : u < v) (hv1 : v ≤ 1)
    (hinv : ∀ x ∈ Set.Ico u v, (mkIET1 mu σ hl x ∈ Set.Ico u v ↔ x ∈ Set.Ico u v)) :
    ∃ (mu' : Fin e → ℝ≥0) (hl' : (∑ j, mu' j) = 1),
      (∀ j, (mu' j : ℝ)
        = max 0 (min v (upperEnd mu j) - max u (leftEnd mu j)) / (v - u)) ∧
      ∀ y ∈ Set.Ico (0 : ℝ) 1, rescaleFun u v (mkIET1 mu σ hl) y = mkIET1 mu' σ hl' y := by
  classical
  have htot : (∑ j, (mu j : ℝ)) = 1 := by rw [← NNReal.coe_sum, hl, NNReal.coe_one]
  have hvu : (0 : ℝ) < v - u := by linarith
  have hvune : v - u ≠ 0 := ne_of_gt hvu
  have hLI : ∀ j : Fin e, leftEnd mu j ≤ upperEnd mu j := fun j => by
    rw [upperEnd_eq]; linarith [(mu j).coe_nonneg]
  -- the truncated lengths
  set mu' : Fin e → ℝ≥0 := fun j =>
    ⟨max 0 (min v (upperEnd mu j) - max u (leftEnd mu j)) / (v - u),
      div_nonneg (le_max_left _ _) hvu.le⟩ with hmu'def
  have hmu'max : ∀ j, (mu' j : ℝ)
      = max 0 (min v (upperEnd mu j) - max u (leftEnd mu j)) / (v - u) := fun j => rfl
  have hmu'coe : ∀ j, (mu' j : ℝ)
      = (clamp u v (upperEnd mu j) - clamp u v (leftEnd mu j)) / (v - u) := by
    intro j
    rw [hmu'max j, clamp_sub_clamp huv (hLI j)]
  have hleftEnd' : ∀ j, leftEnd mu' j = (clamp u v (leftEnd mu j) - u) / (v - u) :=
    leftEnd_of_clamp_sub hmu'coe huv h0u
  have hl' : (∑ j, mu' j) = 1 := by
    refine NNReal.coe_injective ?_
    have h1 : ((∑ j, mu' j : ℝ≥0) : ℝ) = ∑ j, (mu' j : ℝ) := by push_cast; ring
    rw [h1]
    calc ∑ j, (mu' j : ℝ)
        = ∑ j, (clamp u v (upperEnd mu j) - clamp u v (leftEnd mu j)) / (v - u) :=
          Finset.sum_congr rfl (fun j _ => hmu'coe j)
      _ = (∑ j, (clamp u v (upperEnd mu j) - clamp u v (leftEnd mu j))) / (v - u) :=
          (Finset.sum_div _ _ _).symm
      _ = (v - u) / (v - u) := by rw [sum_clamp_sub mu htot h0u huv hv1]
      _ = ((1 : ℝ≥0) : ℝ) := by rw [div_self hvune]; simp
  -- the same for the image lengths
  have hnu : (∑ k, (imageLengths σ mu k : ℝ)) = 1 := by rw [sum_imageLengths, htot]
  have hnu'coe : ∀ m, ((imageLengths σ mu') m : ℝ)
      = (clamp u v (upperEnd (imageLengths σ mu) m)
          - clamp u v (leftEnd (imageLengths σ mu) m)) / (v - u) := by
    intro m
    obtain ⟨i, rfl⟩ : ∃ i, σ i = m := ⟨σ.symm m, σ.apply_symm_apply m⟩
    have h1 : (imageLengths σ mu') (σ i) = mu' i := by simp [imageLengths]
    rw [h1, hmu'coe i, clamp_imageLengths_eq hl h0u huv hv1 hinv i]
  have hleftEnd_nu' : ∀ m, leftEnd (imageLengths σ mu') m
      = (clamp u v (leftEnd (imageLengths σ mu) m) - u) / (v - u) :=
    leftEnd_of_clamp_sub hnu'coe huv h0u
  refine ⟨mu', hl', fun j => hmu'max j, ?_⟩
  intro y hy
  set x := rescaleMapInv u v y with hxdef
  have hxmap : rescaleMap u v x = y := rescaleMap_rescaleMapInv huv y
  have hxI : x ∈ Set.Ico u v := (rescaleMap_mem huv).mp (by rw [hxmap]; exact hy)
  obtain ⟨hxu, hxv⟩ := hxI
  have hx0 : 0 ≤ x := le_trans h0u hxu
  have hxtot : x ∈ Set.Ico (0 : ℝ) (∑ j, (mu j : ℝ)) := by
    refine ⟨hx0, ?_⟩
    rw [htot]; linarith
  set i := idx mu x hxtot.1 with hidef
  have hixl : leftEnd mu i ≤ x := idx_mem mu x hxtot.1
  have hixr : x < upperEnd mu i := lt_upperEnd_idx mu hxtot
  have hixll : max u (leftEnd mu i) ≤ x := max_le hxu hixl
  have hixmin : x < min v (upperEnd mu i) := lt_min hxv hixr
  have hne : max u (leftEnd mu i) < min v (upperEnd mu i) := lt_of_le_of_lt hixll hixmin
  have hgx : mkIET1 mu σ hl x = x + (imageLeft σ mu i - leftEnd mu i) := by
    rw [mkIET1_apply mu σ hl hxtot, ← hidef]
  have hgmem : mkIET1 mu σ hl x ∈ Set.Ico u v := (hinv x ⟨hxu, hxv⟩).mpr ⟨hxu, hxv⟩
  rw [hgx] at hgmem
  have hyx : y = (x - u) / (v - u) := by rw [← hxmap, rescaleMap]
  -- the key computation: the translation at the cell of `x`
  have hclamp_a : clamp u v (imageLeft σ mu i)
      = clamp u v (leftEnd mu i) + (imageLeft σ mu i - leftEnd mu i) := by
    have hpt := image_truncation_subset hl h0u huv hv1 hinv i
    have hlo := (hpt _ le_rfl hne).1
    have hsup := min_add_translation_le (u := u) (v := v) i hne hpt
    have hlen := clamp_imageLengths_eq hl h0u huv hv1 hinv i
    have hLν : leftEnd (imageLengths σ mu) (σ i) = imageLeft σ mu i :=
      (imageLeft_eq_leftEnd σ mu i).symm
    have hUν : upperEnd (imageLengths σ mu) (σ i) = imageLeft σ mu i + (mu i : ℝ) := by
      rw [upperEnd_eq, hLν]; simp [imageLengths]
    have hLI' : leftEnd (imageLengths σ mu) (σ i) ≤ upperEnd (imageLengths σ mu) (σ i) := by
      rw [upperEnd_eq]; linarith [((imageLengths σ mu) (σ i)).coe_nonneg]
    rw [clamp_sub_clamp huv hLI', clamp_sub_clamp huv (hLI i), hLν, hUν] at hlen
    have hpos1 : (0 : ℝ) < min v (upperEnd mu i) - max u (leftEnd mu i) := by linarith
    have hpos2 : (0 : ℝ) < min v (imageLeft σ mu i + (mu i : ℝ))
        - max u (imageLeft σ mu i) := by
      linarith
    rw [max_eq_right (le_of_lt hpos1), max_eq_right (le_of_lt hpos2)] at hlen
    have hMeq : max u (imageLeft σ mu i)
        = max u (leftEnd mu i) + (imageLeft σ mu i - leftEnd mu i) := by linarith
    have hva : max u (imageLeft σ mu i) ≤ v := by linarith [hgmem.2]
    have hvl : max u (leftEnd mu i) ≤ v := by linarith
    rw [clamp, min_eq_right hva, clamp, min_eq_right hvl, hMeq]
  have hle_l : leftEnd mu' i ≤ y := by
    rw [hleftEnd' i, hyx, div_le_div_iff_of_pos_right hvu]
    have h2 : clamp u v (leftEnd mu i) = max u (leftEnd mu i) := by
      rw [clamp, min_eq_right (by linarith : max u (leftEnd mu i) ≤ v)]
    rw [h2]; linarith
  have hlt_r : y < upperEnd mu' i := by
    have h2 : upperEnd mu' i = (clamp u v (upperEnd mu i) - u) / (v - u) := by
      rw [upperEnd_eq, hleftEnd' i, hmu'coe i, ← add_div]
      congr 1
      ring
    rw [h2, hyx, div_lt_div_iff_of_pos_right hvu]
    have h3 : clamp u v (upperEnd mu i) = min v (max u (upperEnd mu i)) := rfl
    rw [h3]
    have h4 : x < min v (max u (upperEnd mu i)) :=
      lt_min hxv (lt_of_lt_of_le hixr (le_max_right _ _))
    linarith
  have hy' : y ∈ Set.Ico (0 : ℝ) (∑ j, (mu' j : ℝ)) := by
    refine ⟨hy.1, ?_⟩
    have h1 : (∑ j, (mu' j : ℝ)) = 1 := by rw [← NNReal.coe_sum, hl', NNReal.coe_one]
    rw [h1]; exact hy.2
  set i' := idx mu' y hy'.1 with hi'def
  have hidx : i' = i := by
    rw [hi'def]
    exact idx_eq mu' hy' hle_l hlt_r
  have ht' : imageLeft σ mu' i - leftEnd mu' i
      = (imageLeft σ mu i - leftEnd mu i) / (v - u) := by
    have h1 : imageLeft σ mu' i = leftEnd (imageLengths σ mu') (σ i) :=
      imageLeft_eq_leftEnd σ mu' i
    have h2 : leftEnd (imageLengths σ mu') (σ i)
        = (clamp u v (leftEnd (imageLengths σ mu) (σ i)) - u) / (v - u) := hleftEnd_nu' (σ i)
    have h3 : leftEnd (imageLengths σ mu) (σ i) = imageLeft σ mu i :=
      (imageLeft_eq_leftEnd σ mu i).symm
    rw [h1, h2, h3, hleftEnd' i, div_sub_div_same]
    congr 1
    linarith [hclamp_a]
  have hLHS : rescaleFun u v (mkIET1 mu σ hl) y
      = y + (imageLeft σ mu i - leftEnd mu i) / (v - u) := by
    rw [rescaleFun, ← hxdef, hgx, rescaleMap, hyx]
    field_simp
    ring
  have hRHS : mkIET1 mu' σ hl' y = y + (imageLeft σ mu' i' - leftEnd mu' i') := by
    rw [mkIET1_apply mu' σ hl' hy', ← hi'def]
  rw [hLHS, hRHS, hidx, ht']

/-- The truncated lengths of an exchange on an interval, as a named function. -/
noncomputable def truncatedLengths (mu : Fin e → ℝ≥0) (u v : ℝ) (huv : u < v) :
    Fin e → ℝ≥0 :=
  fun j => ⟨max 0 (min v (upperEnd mu j) - max u (leftEnd mu j)) / (v - u),
    div_nonneg (le_max_left _ _) (by linarith : (0 : ℝ) ≤ v - u)⟩

omit [NeZero e] in
theorem truncatedLengths_coe (mu : Fin e → ℝ≥0) {u v : ℝ} (huv : u < v) (j : Fin e) :
    (truncatedLengths mu u v huv j : ℝ)
      = max 0 (min v (upperEnd mu j) - max u (leftEnd mu j)) / (v - u) := rfl

omit [NeZero e] in
theorem truncatedLengths_clamp (mu : Fin e → ℝ≥0) {u v : ℝ} (huv : u < v) (j : Fin e) :
    (truncatedLengths mu u v huv j : ℝ)
      = (clamp u v (upperEnd mu j) - clamp u v (leftEnd mu j)) / (v - u) := by
  rw [truncatedLengths_coe, clamp_sub_clamp huv]
  rw [upperEnd_eq]; linarith [(mu j).coe_nonneg]

omit [NeZero e] in
/-- **The total mass of the truncated lengths is `1`.** -/
theorem sum_truncatedLengths (mu : Fin e → ℝ≥0) (hl : (∑ j, mu j) = 1) {u v : ℝ}
    (h0u : 0 ≤ u) (huv : u < v) (hv1 : v ≤ 1) :
    (∑ j, truncatedLengths mu u v huv j) = 1 := by
  have htot : (∑ j, (mu j : ℝ)) = 1 := by rw [← NNReal.coe_sum, hl, NNReal.coe_one]
  have hvu : (0 : ℝ) < v - u := by linarith
  have hvune : v - u ≠ 0 := ne_of_gt hvu
  refine NNReal.coe_injective ?_
  have h1 : ((∑ j, truncatedLengths mu u v huv j : ℝ≥0) : ℝ)
      = ∑ j, (truncatedLengths mu u v huv j : ℝ) := by push_cast; ring
  rw [h1]
  calc ∑ j, (truncatedLengths mu u v huv j : ℝ)
      = ∑ j, (clamp u v (upperEnd mu j) - clamp u v (leftEnd mu j)) / (v - u) :=
        Finset.sum_congr rfl (fun j _ => truncatedLengths_clamp mu huv j)
    _ = (∑ j, (clamp u v (upperEnd mu j) - clamp u v (leftEnd mu j))) / (v - u) :=
        (Finset.sum_div _ _ _).symm
    _ = (v - u) / (v - u) := by rw [sum_clamp_sub mu htot h0u huv hv1]
    _ = ((1 : ℝ≥0) : ℝ) := by rw [div_self hvune]; simp

omit [NeZero e] in
/-- **Companion: the prefix sums of the truncated lengths are the clamped prefix sums.**

Note the `clamp`.  For a cell that starts at or after `v` the truncated length is `0`, so the prefix
sum is `1`, while `(leftEnd mu j - u)/(v - u) > 1`: the literal form
`leftEnd mu' j = (max u (leftEnd mu j) - u)/(v - u)` of the task statement is false once a cell
starts beyond `v`.  The correct statement is the clamped one below; it specialises to the literal
one for the cells that start before `v` (`leftEnd_truncatedLengths_of_le`). -/
theorem leftEnd_truncatedLengths (mu : Fin e → ℝ≥0) {u v : ℝ} (h0u : 0 ≤ u) (huv : u < v)
    (j : Fin e) :
    leftEnd (truncatedLengths mu u v huv) j = (clamp u v (leftEnd mu j) - u) / (v - u) :=
  leftEnd_of_clamp_sub (fun j => truncatedLengths_clamp mu huv j) huv h0u j

omit [NeZero e] in
/-- The companion in the literal form of the task statement, for a cell starting before `v`. -/
theorem leftEnd_truncatedLengths_of_le (mu : Fin e → ℝ≥0) {u v : ℝ} (h0u : 0 ≤ u)
    (huv : u < v) {j : Fin e} (hj : leftEnd mu j ≤ v) :
    leftEnd (truncatedLengths mu u v huv) j = (max u (leftEnd mu j) - u) / (v - u) := by
  rw [leftEnd_truncatedLengths mu h0u huv, clamp, min_eq_right (max_le (le_of_lt huv) hj)]

end Main

end RestrictIET
