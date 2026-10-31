/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.BlockEndpoints
import IETFree.SubintervalTransfer

/-!
The almost-sure transfer of Masur–Veech and Veech's rigidity to a block.

Lemma 3.4 applies Theorem 2.6 to the rescaled pair `(g̃f̃, g̃)` on a block of marked cells.  The two
external hypotheses are about the a.e. length vector of an irreducible permutation; the content of
this module is that they transfer to the *block* length vector of the composition, which is an
absolutely continuous image of the parameters:

* `cellLen_eq_coe_simplexMap`, `blockMass_simplexMap`, `blockLam_eq_simplexMap_rescaleSub`: the
  rescaled block length vector is `simplexMap (l - k)` of `rescaleSub k (l - k)` applied to the free
  coordinates of the composition;
* `absolutelyContinuous_map_blockFree` and `ae_blockFree_of_ae_simplexVolume`: the pushforward of
  `simplexVolume n` under the block rescaling is absolutely continuous, so an a.e. statement about
  the free coordinates of the block holds a.e. on the parameters.

The transfer is assembled in `IETFree.BlockData` (`ae_block_of_ae_simplexVolume`, then
`ae_blockGood_free` and `ae_blockGood` for the block exchange `mkIET1 (blockLam …) (blockPerm …)`);
the earlier version of this file stated that transfer for the *global* monotonicity hypothesis
`∀ q, StrictMono fun k => s k q`, which `GoodRegion` cannot supply, so those statements are gone.
-/

-- `NeZero (l - k)` is needed as an *instance* by `mkIET1`, so `haveI` is the right binder; the
-- style linter only sees that its value is a `Prop`.
set_option linter.style.haveILetI false

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-! ## The abstract measure-theoretic step -/

/-! ## The rescaled block length vector as a `simplexMap` -/

section Ident

/-- On the open simplex region, the `m`-th cell length of the free coordinates is the `m`-th length
of the point of the simplex they parametrise. -/
theorem cellLen_eq_coe_simplexMap {n : ℕ} [NeZero n] {x : Fin (n - 1) → ℝ}
    (hx : x ∈ simplexRegion n) (m : ℕ) (hm : m < n) :
    cellLen x m = ((simplexMap n x ⟨m, hm⟩ : ℝ≥0) : ℝ) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, (Nat.sub_one_add_one (NeZero.ne n)).symm⟩
  have hm' : m ≤ p := by simpa using hm
  rcases lt_or_eq_of_le hm' with hlt | heq
  · rw [cellLen_of_lt x (n := p + 1) (m := m) (by omega)]
    have hidx : (⟨m, hm⟩ : Fin (p + 1)) = (⟨m, hlt⟩ : Fin p).castSucc := Fin.ext rfl
    rw [hidx]
    exact (simplexMap_castSucc_coe hx.1 ⟨m, hlt⟩).symm
  · subst heq
    rw [cellLen_of_not_lt x (n := m + 1) (m := m) (by omega)]
    have hidx : (⟨m, hm⟩ : Fin (m + 1)) = Fin.last m := Fin.ext rfl
    rw [hidx]
    exact (simplexMap_last_coe hx.2).symm

/-- The mass of the block `k, …, l - 1` of the point of the simplex with free coordinates `x` is the
sum of the corresponding `cellLen`s. -/
theorem blockMass_simplexMap {n : ℕ} [NeZero n] {x : Fin (n - 1) → ℝ}
    (hx : x ∈ simplexRegion n) (k l : ℕ) (hln : l ≤ n) :
    blockMass (simplexMap n x) k hln = ∑ j : Fin (l - k), blockLen k (l - k) x j := by
  rw [blockMass]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  show ((simplexMap n x ⟨k + j.val, _⟩ : ℝ≥0) : ℝ) = blockLen k (l - k) x j
  rw [← cellLen_eq_coe_simplexMap hx (k + j.val) (by omega)]
  rfl

end Ident

section IdentMain

/-- **Two length vectors of `Fin r` that agree away from the last coordinate and both sum to `1`
agree everywhere.**  This is how the last coordinate of `blockLam` (a quotient by the block mass)
is identified with the last coordinate of `simplexMap` (the complement `1 - ∑`), without any
case split on whether the block reaches the last cell. -/
theorem eq_of_forall_lt_last_eq_of_sum_eq {r : ℕ} (hr : 0 < r) {f g : Fin r → ℝ}
    (h : ∀ i : Fin r, i.val < r - 1 → f i = g i)
    (hf : (∑ i, f i) = 1) (hg : (∑ i, g i) = 1) : ∀ i, f i = g i := by
  have hr' : r - 1 < r := by omega
  set last : Fin r := ⟨r - 1, hr'⟩ with hlastdef
  set T : Finset (Fin r) := Finset.univ.filter (fun i => i.val < r - 1) with hTdef
  have hTcompl : Tᶜ = {last} := by
    ext i
    simp only [hTdef, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, hlastdef, Fin.ext_iff]
    constructor
    · intro hge
      have hlt := i.isLt
      omega
    · intro heq hlt
      omega
  have hsplit : ∀ (φ : Fin r → ℝ), (∑ i ∈ T, φ i) + φ last = ∑ i, φ i := by
    intro φ
    have hlast' : φ last = ∑ i ∈ Tᶜ, φ i := by rw [hTcompl, Finset.sum_singleton]
    rw [hlast']
    exact Finset.sum_add_sum_compl T φ
  have hTeq : (∑ i ∈ T, f i) = ∑ i ∈ T, g i := Finset.sum_congr rfl (fun i hi => h i (by
    simpa only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and] using hi))
  have hlast : f last = g last := by
    have h1 := hsplit f
    have h2 := hsplit g
    rw [hf] at h1
    rw [hg] at h2
    linarith
  intro i
  by_cases hi : i.val < r - 1
  · exact h i hi
  · have hval : i.val = r - 1 := by have := i.isLt; omega
    have hie : i = last := Fin.ext (by simp only [hlastdef, Fin.val_mk]; omega)
    rw [hie]
    exact hlast

/-- The mass of the block `k, …, l - 1` of a point of the simplex is a sum of block lengths. -/
theorem blockLam_eq_simplexMap_rescaleSub {n : ℕ} [NeZero n] {k l : ℕ} (hkl : k < l) (hln : l ≤ n)
    {x : Fin (n - 1) → ℝ} (hx : x ∈ simplexRegion n) (hpos : Positive (simplexMap n x)) :
    blockLam (simplexMap n x) k hkl hln hpos = simplexMap (l - k) (rescaleSub k (l - k) x) := by
  haveI : NeZero (l - k) := ⟨by omega⟩
  have hy : rescaleSub k (l - k) x ∈ simplexRegion (l - k) := by
    have h := rescaleSub_mem_simplexRegion (n := n) (k := k) (m := l - k - 1) (x := x) hx
    have h' : l - k - 1 + 1 = l - k := by omega
    rw [h'] at h
    exact h
  have hmass : blockMass (simplexMap n x) k hln = ∑ j : Fin (l - k), blockLen k (l - k) x j :=
    blockMass_simplexMap hx k l hln
  have hmasspos : 0 < ∑ j : Fin (l - k), blockLen k (l - k) x j := by
    rw [← hmass]
    exact blockMass_pos hpos k hkl hln
  have hcoord : ∀ i : Fin (l - k), i.val < l - k - 1 →
      ((blockLam (simplexMap n x) k hkl hln hpos i : ℝ≥0) : ℝ)
        = ((simplexMap (l - k) (rescaleSub k (l - k) x) i : ℝ≥0) : ℝ) := by
    intro i hi
    rw [blockLam_coe, simplexMap_of_lt hy hi]
    change (simplexMap n x ⟨k + i.val, by omega⟩ : ℝ) / blockMass (simplexMap n x) k hln
      = blockLen k (l - k) x ⟨i.val, by omega⟩ / ∑ j, blockLen k (l - k) x j
    rw [← cellLen_eq_coe_simplexMap hx (k + i.val) (by omega), hmass]
    rfl
  have hf : (∑ i : Fin (l - k),
      ((blockLam (simplexMap n x) k hkl hln hpos i : ℝ≥0) : ℝ)) = 1 := by
    rw [← NNReal.coe_sum, blockLam_sum, NNReal.coe_one]
  have hg : (∑ i : Fin (l - k),
      ((simplexMap (l - k) (rescaleSub k (l - k) x) i : ℝ≥0) : ℝ)) = 1 := by
    rw [← NNReal.coe_sum, simplexMap_mem_simplex_fin hy.1 hy.2, NNReal.coe_one]
  funext i
  exact NNReal.coe_injective
    (eq_of_forall_lt_last_eq_of_sum_eq (by omega) hcoord hf hg i)

end IdentMain

section AETransport

/-- **The block length vector in terms of the free coordinates of the whole length vector**: the
projective formula.  This is the function of the parameters whose absolute continuity is Lemma 3.1
for the rescaled block. -/
noncomputable def blockFree {n : ℕ} (k l : ℕ) (ν : Fin n → ℝ≥0) : Fin (l - k - 1) → ℝ :=
  rescaleSub k (l - k) fun i : Fin (n - 1) => (ν ⟨i.val, by have := i.isLt; omega⟩ : ℝ)

theorem measurable_blockFree {n k l : ℕ} : Measurable (blockFree (n := n) k l) :=
  measurable_rescaleSub.comp
    (measurable_pi_iff.mpr fun i =>
      measurable_coe_nnreal_real.comp (measurable_pi_apply (⟨i.val, by omega⟩ : Fin n)))

/-- On the open simplex region, `blockFree` of the length vector is `rescaleSub` of the free
coordinates. -/
theorem blockFree_simplexMap {n : ℕ} {k l : ℕ} {x : Fin (n - 1) → ℝ}
    (hx : x ∈ simplexRegion n) :
    blockFree k l (simplexMap n x) = rescaleSub k (l - k) x := by
  unfold blockFree
  congr 1
  funext i
  have hj : (⟨i.val, by omega⟩ : Fin n).val < n - 1 := i.isLt
  exact simplexMap_of_lt (v := x) hx hj

/-- **The projective formula for the rescaled block length vector is absolutely continuous**: the
pushforward of `simplexVolume n` under `ν ↦ simplexMap (l - k) (blockFree k l ν)` is absolutely
continuous with respect to `simplexVolume (l - k)`.  This is Lemma 3.1 composed with
`absolutelyContinuous_map_rescaleSub`. -/
theorem absolutelyContinuous_map_blockFree {n : ℕ} [NeZero n] {k l : ℕ} (hkl : k < l)
    (hln : l ≤ n) :
    (simplexVolume n).map (fun ν => simplexMap (l - k) (blockFree k l ν))
      ≪ simplexVolume (l - k) := by
  haveI : NeZero (l - k) := ⟨by omega⟩
  have hmeas : Measurable fun ν : Fin n → ℝ≥0 => simplexMap (l - k) (blockFree k l ν) :=
    (measurable_simplexMap (l - k)).comp measurable_blockFree
  have hcongr : ((fun ν : Fin n → ℝ≥0 => simplexMap (l - k) (blockFree k l ν)) ∘ simplexMap n)
      =ᵐ[volume.restrict (simplexRegion n)]
        ((simplexMap (l - k)) ∘ (rescaleSub k (l - k))) := by
    filter_upwards [ae_restrict_mem (measurableSet_simplexRegion n)] with x hx
    simp only [Function.comp_apply, blockFree_simplexMap hx]
  have hstep : (volume.restrict (simplexRegion n)).map
      ((fun ν : Fin n → ℝ≥0 => simplexMap (l - k) (blockFree k l ν)) ∘ simplexMap n)
      ≪ simplexVolume (l - k) := by
    rw [Measure.map_congr hcongr]
    rw [← Measure.map_map (measurable_simplexMap (l - k)) measurable_rescaleSub]
    exact Measure.AbsolutelyContinuous.map
      (absolutelyContinuous_map_rescaleSub (NeZero.pos n) (k := k) (r := l - k) (by omega))
      (measurable_simplexMap (l - k))
  calc (simplexVolume n).map (fun ν => simplexMap (l - k) (blockFree k l ν))
      = ((volume.restrict (simplexRegion n)).map (simplexMap n)).map
          (fun ν => simplexMap (l - k) (blockFree k l ν)) := rfl
    _ = (volume.restrict (simplexRegion n)).map
          ((fun ν => simplexMap (l - k) (blockFree k l ν)) ∘ simplexMap n) :=
        Measure.map_map hmeas (measurable_simplexMap n)
    _ ≪ simplexVolume (l - k) := hstep

/-- **An almost-sure statement about the rescaled block length vector, pulled back to
`simplexVolume n`.** -/
theorem ae_blockFree_of_ae_simplexVolume {n : ℕ} [NeZero n] {k l : ℕ} (hkl : k < l) (hln : l ≤ n)
    {Q : (Fin (l - k) → ℝ≥0) → Prop} (hQ : ∀ᵐ ν ∂(simplexVolume (l - k)), Q ν) :
    ∀ᵐ ν ∂(simplexVolume n), Q (simplexMap (l - k) (blockFree k l ν)) :=
  MeasureTheory.ae_of_ae_map
    ((measurable_simplexMap (l - k)).comp measurable_blockFree).aemeasurable
    ((absolutelyContinuous_map_blockFree hkl hln).ae_le hQ)

end AETransport
