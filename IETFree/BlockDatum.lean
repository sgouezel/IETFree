/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.BlockEndpoints
import IETFree.BlockIrreducibility
import IETFree.BlockRescaling
import IETFree.BlockData
import IETFree.GoodRegion
import IETFree.LengthMap
import IETFree.InvariantInterval

/-!
The presentation of `g ∘ f` on a block: the datum, the invariance of the block, and the rescaled
composition.

The datum of a good region at a parameter `q` is the `IETDatum` presented by the marked list
(`GoodRegion.datum`), with its API (`datum_lam`, `datum_markCuts`, `datum_hcuts`, `datum_toFun`) and
Lemma 3.2 read on it (`irreducibleOn_datum`, `irreduciblePerm_blockPerm`).  Then, for a block
`[s i₀, s i₁)` of marked cells whose ends are pair-splitting:

* its initial segments are invariant, so the block permutation is stable (`blockPerm_stab`); the
  block itself is `GoodRegion.blockOf` (a `GoodRegion.Block`, whose `perm` and `lam` are what the
  a.e. statements use) and the packaged permutation is `GoodRegion.blockPermOf`;
* the composition restricted to the block and rescaled to `[0, 1)` is `GoodRegion.blockRescaled`,
  and the two halves of the pointwise conjugacy are `comp_conj_rescale` (composition side) and
  `restrict_rescale` (`g` side);
* the degenerate case of a single cell is dealt with by `mkIET1_of_all_one` and `blockLam_of_one`,
  with the words `genX` and `genY * genX` (`genX_ne_one`, `genY_mul_genX_ne_one`).

Nothing here takes a *global* monotonicity hypothesis `∀ q, StrictMono fun k => s k q`: a
`GoodRegion` only knows that its list increases at the points of `O`, so every lemma takes
`{q} (hq : q ∈ G.O)` and uses `monoAt G hq` and the pointwise length vector
`G.cellLen hq`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

-- `NeZero (l - k)` is an *instance* (`mkIET1` and `simplex` need it as such), so `haveI` is the
-- right binder when it is derived from `k < l`; the style linter only sees that its value is a
-- `Prop`.
set_option linter.style.haveILetI false

section BlockIrreducibleTransport

variable {n : ℕ} [NeZero n] {k l : ℕ}

/-- **Irreducibility of the block permutation**, transported through
`mkIET1_rescale_subinterval`.  The input is the *datum*: if the exchange presented by `D` has no
invariant initial union of cells `[leftEnd D.lam k, c)` inside the block
`[leftEnd D.lam k, leftEnd D.lam k + blockMass)`, at any marked point `c` of `D`, then the rescaled
block exchange is irreducible, i.e. `blockPerm D.π k hkl hln hstab` is. -/
theorem irreduciblePerm_blockPerm (D : IETDatum n) (hkl : k < l) (hln : l ≤ n)
    (hstab : ∀ i : Fin n, (i.val < k ↔ (D.π i).val < k) ∧ (i.val < l ↔ (D.π i).val < l))
    (hirr : IsIrreducibleOn D (leftEnd D.lam ⟨k, by omega⟩)
      (leftEnd D.lam ⟨k, by omega⟩ + blockMass D.lam k hln)) :
    IsIrreduciblePerm (blockPerm D.π k hkl hln hstab) := by
  classical
  haveI : NeZero (l - k) := ⟨by omega⟩
  have hpos : ∀ i, 0 < (D.lam i : ℝ) := D.lam_pos
  have hMpos : 0 < blockMass D.lam k hln := blockMass_pos hpos k hkl hln
  have hlNN : (∑ i, D.lam i) = 1 := by
    rw [← NNReal.coe_inj, NNReal.coe_sum, D.sum_lam, NNReal.coe_one]
  have hlev : (∑ i : Fin (l - k), (blockLam D.lam k hkl hln hpos i : ℝ)) = 1 := by
    have h2 : (∑ i : Fin (l - k), blockLam D.lam k hkl hln hpos i) = 1 :=
      blockLam_sum D.lam k hkl hln hpos
    rw [← NNReal.coe_sum, h2, NNReal.coe_one]
  refine irreduciblePerm_of_no_invariant_cut (hpos := blockLam_pos hpos hkl hln)
    (hl := blockLam_sum D.lam k hkl hln hpos) (π := blockPerm D.π k hkl hln hstab) ?_
  intro j hj0 hinv
  have hjpos : 0 < leftEnd (blockLam D.lam k hkl hln hpos) j :=
    leftEnd_pos_of_ne_zero (blockLam_pos hpos hkl hln) hj0
  have hjlt : leftEnd (blockLam D.lam k hkl hln hpos) j < 1 := by
    have h1 := leftEnd_lt_total (blockLam_pos hpos hkl hln) j
    rw [hlev] at h1
    exact h1
  have hjval : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj0 (Fin.ext (by simpa using h)))
  have hkjl : k + j.val < l := by have := j.isLt; omega
  have hkj0 : k < k + j.val := by omega
  -- the corresponding marked point of the datum
  have hcS : leftEnd D.lam ⟨k + j.val, by omega⟩ ∈ D.markCuts := by
    have h := D.mark_mem_markCuts (⟨k + j.val, by omega⟩ : Fin n)
    rwa [D.mark_castSucc] at h
  have hkey : leftEnd D.lam ⟨k + j.val, by omega⟩
      = leftEnd D.lam ⟨k, by omega⟩
        + blockMass D.lam k hln * leftEnd (blockLam D.lam k hkl hln hpos) j :=
    leftEnd_blockLam hpos hkl hln j
  have hcu : leftEnd D.lam ⟨k, by omega⟩ < leftEnd D.lam ⟨k + j.val, by omega⟩ := by
    rw [hkey]; linarith [mul_pos hMpos hjpos]
  have hcv : leftEnd D.lam ⟨k + j.val, by omega⟩
      < leftEnd D.lam ⟨k, by omega⟩ + blockMass D.lam k hln := by
    rw [hkey]; linarith [mul_lt_mul_of_pos_left hjlt hMpos]
  refine hirr _ hcS hcu hcv ?_
  intro x hx01 hux hxc
  have hxI : x ∈ Set.Ico (leftEnd D.lam ⟨k, by omega⟩)
      (leftEnd D.lam ⟨k, by omega⟩ + blockMass D.lam k hln) := ⟨hux, lt_trans hxc hcv⟩
  have huv : leftEnd D.lam ⟨k, by omega⟩
      < leftEnd D.lam ⟨k, by omega⟩ + blockMass D.lam k hln := lt_of_le_of_lt hxI.1 hxI.2
  have hx'mem : rescaleMap (leftEnd D.lam ⟨k, by omega⟩)
      (leftEnd D.lam ⟨k, by omega⟩ + blockMass D.lam k hln) x ∈ Set.Ico (0 : ℝ) 1 :=
    (rescaleMap_mem huv).mpr hxI
  have hx'lt : rescaleMap (leftEnd D.lam ⟨k, by omega⟩)
      (leftEnd D.lam ⟨k, by omega⟩ + blockMass D.lam k hln) x
      < leftEnd (blockLam D.lam k hkl hln hpos) j := by
    have hrw : rescaleMap (leftEnd D.lam ⟨k, by omega⟩)
        (leftEnd D.lam ⟨k, by omega⟩ + blockMass D.lam k hln) x
        = (x - leftEnd D.lam ⟨k, by omega⟩) / blockMass D.lam k hln := by
      rw [rescaleMap, add_sub_cancel_left]
    rw [hrw, div_lt_iff₀ hMpos]
    linarith [hxc, hkey]
  have hinv' := hinv _ hx'mem hx'lt
  have hmapmem := (mkIET1 (blockLam D.lam k hkl hln hpos) (blockPerm D.π k hkl hln hstab)
    (blockLam_sum D.lam k hkl hln hpos)).isIET.mapsTo hx'mem
  have hres := RescaleBlock.mkIET1_rescale_subinterval ⟨k, l, hkl, hln⟩ hlNN hpos hstab x hxI
  have hfx : mkIET1 D.lam D.π D.mem_simplex x
      = rescaleMapInv (leftEnd D.lam ⟨k, by omega⟩)
        (leftEnd D.lam ⟨k, by omega⟩ + blockMass D.lam k hln)
        (mkIET1 (blockLam D.lam k hkl hln hpos) (blockPerm D.π k hkl hln hstab)
          (blockLam_sum D.lam k hkl hln hpos)
          (rescaleMap (leftEnd D.lam ⟨k, by omega⟩)
            (leftEnd D.lam ⟨k, by omega⟩ + blockMass D.lam k hln) x)) := by
    rw [← hres, rescaleMapInv_rescaleMap huv]
  have hval : rescaleMapInv (leftEnd D.lam ⟨k, by omega⟩)
      (leftEnd D.lam ⟨k, by omega⟩ + blockMass D.lam k hln)
      (mkIET1 (blockLam D.lam k hkl hln hpos) (blockPerm D.π k hkl hln hstab)
        (blockLam_sum D.lam k hkl hln hpos)
        (rescaleMap (leftEnd D.lam ⟨k, by omega⟩)
          (leftEnd D.lam ⟨k, by omega⟩ + blockMass D.lam k hln) x))
      = leftEnd D.lam ⟨k, by omega⟩ + blockMass D.lam k hln
        * mkIET1 (blockLam D.lam k hkl hln hpos) (blockPerm D.π k hkl hln hstab)
            (blockLam_sum D.lam k hkl hln hpos)
            (rescaleMap (leftEnd D.lam ⟨k, by omega⟩)
              (leftEnd D.lam ⟨k, by omega⟩ + blockMass D.lam k hln) x) := by
    rw [rescaleMapInv, add_sub_cancel_left, mul_comm]
  change D.toFun x ∈ Set.Ico (leftEnd D.lam ⟨k, by omega⟩) (leftEnd D.lam ⟨k + j.val, by omega⟩)
  rw [show D.toFun x = mkIET1 D.lam D.π D.mem_simplex x from rfl, hfx, hval]
  set y : ℝ := (mkIET1 (blockLam D.lam k hkl hln hpos) (blockPerm D.π k hkl hln hstab)
      (blockLam_sum D.lam k hkl hln hpos)
      (rescaleMap (leftEnd D.lam ⟨k, by omega⟩)
        (leftEnd D.lam ⟨k, by omega⟩ + blockMass D.lam k hln) x)) with hy
  have hy0 : 0 ≤ y := hmapmem.1
  have hylt : y < leftEnd (blockLam D.lam k hkl hln hpos) j := hinv'
  refine ⟨?_, ?_⟩
  · change leftEnd D.lam ⟨k, by omega⟩ ≤ leftEnd D.lam ⟨k, by omega⟩ + blockMass D.lam k hln * y
    exact le_add_of_nonneg_right (mul_nonneg hMpos.le hy0)
  · change leftEnd D.lam ⟨k, by omega⟩ + blockMass D.lam k hln * y
      < leftEnd D.lam ⟨k + j.val, by omega⟩
    rw [hkey]
    have := mul_lt_mul_of_pos_left hylt hMpos
    linarith

end BlockIrreducibleTransport

section GoodRegionDatum

/-! ### The datum of a good region

Lemma 3.2 is stated on the pair `(D, E)`, while `IsIrreducibleOn` is stated on a single datum: the
chain is `IsCompIrreducibleOn D E u v → IsIrreducibleOn F u v`, where `F` is the datum of the
composition presented by its marked list.  `F` is `IETDatum.ofMem G.ρ (compLenAffine G.s q)`: the
lengths of the marked cells, in free coordinates, and the permutation `ρ` of the list. -/

variable {d e : ℕ} [NeZero d] [NeZero e] {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
  {q₀ : PReal d e}

/-- **The datum of a good region at a parameter**: the composition `g ∘ f`, presented by its marked
list. -/
noncomputable def GoodRegion.datum (G : GoodRegion d e π σ q₀) [NeZero G.n]
    {q : PReal d e} (hq : q ∈ G.O) :
    IETDatum G.n :=
  IETDatum.ofMem G.ρ
    (compLenAffine_mem_regionAt G hq)

theorem GoodRegion.datum_lam (G : GoodRegion d e π σ q₀) [NeZero G.n]
    {q : PReal d e} (hq : q ∈ G.O) :
    (G.datum hq).lam = G.cellLen hq := by
  change simplexMap G.n (compLenAffine G.s q) = G.cellLen hq
  exact (BlockData.compLenVec_eq_simplexMap G hq).symm

/-- **The marked points of the datum are the entries of the list.** -/
theorem GoodRegion.datum_markCuts (G : GoodRegion d e π σ q₀) [NeZero G.n]
    {q : PReal d e} (hq : q ∈ G.O) :
    (G.datum hq).markCuts
      = Finset.univ.image (fun i : Fin G.n => G.s i.castSucc q) := by
  have P := G.pres q hq
  change Finset.univ.image (fun i : Fin G.n => (G.datum hq).mark i.castSucc)
      = Finset.univ.image (fun i : Fin G.n => G.s i.castSucc q)
  congr 1
  funext i
  rw [IETDatum.mark_castSucc, G.datum_lam hq]
  exact leftEnd_compLen (monoAt G hq) P.zero i

/-- **Every marked point of the datum is a cut of the composition.**  The list is exhausted by `0`,
`1`, the cuts of `f` and the `f⁻¹` of the cuts of `g` (`GoodRegion.surj`), and each of these is a
marked point of `D` or a preimage of a marked point of `E`. -/
theorem GoodRegion.datum_hcuts (G : GoodRegion d e π σ q₀) [NeZero G.n]
    {q : PReal d e} (hq : q ∈ G.O)
    {D : IETDatum d} {E : IETDatum e} (h : G.Fits q D E) :
    ∀ c ∈ (G.datum hq).markCuts,
      c ∈ D.markCuts ∪ D.isCutSet_markCuts.preimage E.markCuts := by
  obtain ⟨hp, hw⟩ := G.subset_region q hq
  have hl : simplexMap d q.1 ∈ simplex d := simplexMap_mem_simplex_fin hp.1 hp.2
  have hm : simplexMap e q.2 ∈ simplex e := simplexMap_mem_simplex_fin hw.1 hw.2
  have P := G.pres q hq
  have hDlam : D.lam = simplexMap d q.1 := by rw [IETDatum.lam, h.hDv]
  have hElam : E.lam = simplexMap e q.2 := by rw [IETDatum.lam, h.hEv]
  have hDcut : ∀ k : Fin d, D.mark k.castSucc = leftEnd (simplexMap d q.1) k := by
    intro k
    rw [IETDatum.mark_castSucc, hDlam]
  have hEcut : ∀ k : Fin e, E.mark k.castSucc = leftEnd (simplexMap e q.2) k := by
    intro k
    rw [IETDatum.mark_castSucc, hElam]
  have hDfun : D.toFun = fun x => mkIET1 (simplexMap d q.1) π hl x := by
    funext x
    change mkIETFun D.lam D.π 0 x = _
    rw [hDlam, h.hDπ]
    rfl
  intro c hc
  rw [G.datum_markCuts hq] at hc
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
  have hiv : i.castSucc ≠ Fin.last G.n := Fin.castSucc_ne_last i
  rcases G.surj i.castSucc with h0 | hlast | ⟨i', hi'⟩ | ⟨j', hj'⟩
  · -- the entry `0`
    have hi0 : i = 0 := by
      have h : (i.castSucc : ℕ) = ((0 : Fin (G.n + 1)) : ℕ) := congrArg Fin.val h0
      simp only [Fin.val_castSucc, Fin.val_zero] at h
      exact Fin.ext h
    subst hi0
    refine Finset.mem_union_left _ ?_
    rw [show ((0 : Fin G.n).castSucc : Fin (G.n + 1)) = 0 from Fin.ext rfl, P.zero]
    exact D.mark_zero ▸ D.mark_mem_markCuts (0 : Fin d)
  · exact absurd hlast hiv
  · -- a cut of `f`
    refine Finset.mem_union_left _ ?_
    have h1 : G.s i.castSucc q
        = leftEnd (simplexMap d q.1) ⟨i'.val + 1, by have := i'.isLt; omega⟩ := by
      rw [← hi', G.shape.posF_spec q hq i', cutAffine_eq_leftEnd hp]
    rw [h1, ← hDcut ⟨i'.val + 1, by have := i'.isLt; omega⟩]
    exact D.mark_mem_markCuts _
  · -- the preimage of a cut of `g`
    refine Finset.mem_union_right _ ?_
    rw [IsCutSet.mem_preimage, hDfun]
    have h1 : G.s i.castSucc q
        = (mkIET1 (simplexMap d q.1) π hl)⁻¹
            (leftEnd (simplexMap e q.2) ⟨j'.val + 1, by have := j'.isLt; omega⟩) := by
      rw [← hj', G.shape.posG_pre q hq j' hl]
    rw [h1]
    beta_reduce
    rw [IET.apply_symm_apply', ← hEcut ⟨j'.val + 1, by have := j'.isLt; omega⟩]
    exact E.mark_mem_markCuts _

/-- **The datum of the presentation is the composition.** -/
theorem GoodRegion.datum_toFun (G : GoodRegion d e π σ q₀) [NeZero G.n]
    {q : PReal d e} (hq : q ∈ G.O)
    {D : IETDatum d} {E : IETDatum e} (h : G.Fits q D E) :
    ∀ x, (G.datum hq).toFun x = E.toFun (D.toFun x) := by
  obtain ⟨hp, hw⟩ := G.subset_region q hq
  have hl : simplexMap d q.1 ∈ simplex d := simplexMap_mem_simplex_fin hp.1 hp.2
  have hm : simplexMap e q.2 ∈ simplex e := simplexMap_mem_simplex_fin hw.1 hw.2
  have P := G.pres q hq
  have hDlam : D.lam = simplexMap d q.1 := by rw [IETDatum.lam, h.hDv]
  have hElam : E.lam = simplexMap e q.2 := by rw [IETDatum.lam, h.hEv]
  intro x
  have hF : (G.datum hq).toFun x
      = mkIET1 (G.cellLen hq) G.ρ (compLen_sum P.mono P.zero P.top) x := by
    change mkIETFun (G.datum hq).lam G.ρ 0 x = _
    rw [G.datum_lam hq]
    rfl
  have hDE : E.toFun (D.toFun x)
      = (mkIET1 (simplexMap e q.2) σ hm * mkIET1 (simplexMap d q.1) π hl) x := by
    rw [IET.mul_apply]
    change mkIETFun E.lam E.π 0 (mkIETFun D.lam D.π 0 x)
      = (mkIET1 (simplexMap e q.2) σ hm)
        ((mkIET1 (simplexMap d q.1) π hl) x)
    rw [hDlam, hElam, h.hDπ, h.hEπ]
    rfl
  rw [hF, hDE, P.eq_mkIET1]
  rfl

/-- **Lemma 3.2, read on the datum of the presentation.** -/
theorem GoodRegion.irreducibleOn_datum (G : GoodRegion d e π σ q₀) [NeZero G.n]
    {q : PReal d e} (hq : q ∈ G.O)
    {D : IETDatum d} {E : IETDatum e} (h : G.Fits q D E)
    {u v : ℝ} (hirr : IsCompIrreducibleOn D E u v) :
    IsIrreducibleOn (G.datum hq) u v :=
  hirr.toDatum (G.datum_toFun hq h)
    (fun c hc => G.datum_hcuts hq h c hc)

end GoodRegionDatum

/-! ### The tiling of a block and the invariance of its initial segments -/

section Invariance

variable {d e : ℕ} [NeZero d] [NeZero e] {D : IETDatum d} {E : IETDatum e}

/-- **A pair-splitting point cuts the composition two-sidedly.** -/
theorem comp_lt_iff_of_pairSplitting {x : ℝ} (h : IsPairSplitting D E x) {y : ℝ}
    (hy : y ∈ Set.Ico (0 : ℝ) 1) : (E.toFun (D.toFun y) < x ↔ y < x) := by
  obtain ⟨h1, h2, h3, h4⟩ := h.invariant
  have hDy : D.toFun y ∈ Set.Ico (0 : ℝ) 1 := D.mapsTo hy
  constructor
  · intro hlt
    by_contra hcon
    rw [not_lt] at hcon
    have h5 : x ≤ E.toFun (D.toFun y) := h4 _ hDy (h2 y hy hcon)
    exact absurd hlt (not_lt.mpr h5)
  · intro hlt
    exact h3 _ hDy (h1 y hy hlt)

/-- **The composition maps `[0, x)` into itself** when `x` is pair-splitting. -/
theorem comp_image_Ico_zero {x : ℝ} (h : IsPairSplitting D E x) (hx1 : x ≤ 1) {F : IET 0 1}
    (hF : ∀ y, F y = E.toFun (D.toFun y)) :
    F '' Set.Ico (0 : ℝ) x = Set.Ico (0 : ℝ) x := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy1 : y ∈ Set.Ico (0 : ℝ) 1 := ⟨hy.1, lt_of_lt_of_le hy.2 hx1⟩
    rw [hF]
    exact ⟨(E.mapsTo (D.mapsTo hy1)).1, (comp_lt_iff_of_pairSplitting h hy1).mpr hy.2⟩
  · intro hz
    have hz1 : z ∈ Set.Ico (0 : ℝ) 1 := ⟨hz.1, lt_of_lt_of_le hz.2 hx1⟩
    refine ⟨F⁻¹ z, ?_, ?_⟩
    · have hmem : F⁻¹ z ∈ Set.Ico (0 : ℝ) 1 := (F⁻¹).isIET.mapsTo hz1
      refine ⟨hmem.1, ?_⟩
      have hlink := hF (F⁻¹ z)
      rw [IET.apply_symm_apply'] at hlink
      have hlt : E.toFun (D.toFun (F⁻¹ z)) < x := by rw [← hlink]; exact hz.2
      exact (comp_lt_iff_of_pairSplitting h hmem).mp hlt
    · exact IET.apply_symm_apply' F z

end Invariance

section Upper

variable {d e : ℕ} [NeZero d] [NeZero e] {D : IETDatum d} {E : IETDatum e}

/-- **The composition maps `[x, 1)` onto itself** when `x` is pair-splitting and `x ≥ 0`. -/
theorem comp_image_Ico_one {x : ℝ} (h : IsPairSplitting D E x) (hx0 : 0 ≤ x) {F : IET 0 1}
    (hF : ∀ y, F y = E.toFun (D.toFun y)) :
    F '' Set.Ico x 1 = Set.Ico x 1 := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy1 : y ∈ Set.Ico (0 : ℝ) 1 := ⟨le_trans hx0 hy.1, hy.2⟩
    rw [hF]
    refine ⟨?_, (E.mapsTo (D.mapsTo hy1)).2⟩
    by_contra hcon
    rw [not_le] at hcon
    exact absurd ((comp_lt_iff_of_pairSplitting h hy1).mp hcon) (not_lt.mpr hy.1)
  · intro hz
    refine ⟨F⁻¹ z, ?_, ?_⟩
    · have hmem : F⁻¹ z ∈ Set.Ico (0 : ℝ) 1 :=
        (F⁻¹).isIET.mapsTo ⟨le_trans hx0 hz.1, hz.2⟩
      refine ⟨?_, hmem.2⟩
      by_contra hcon
      rw [not_le] at hcon
      have hlink := hF (F⁻¹ z)
      rw [IET.apply_symm_apply'] at hlink
      have hlt : E.toFun (D.toFun (F⁻¹ z)) < x :=
        (comp_lt_iff_of_pairSplitting h hmem).mpr hcon
      rw [← hlink] at hlt
      linarith [hz.1]
    · exact IET.apply_symm_apply' F z

end Upper

section BlockStarts

variable {d e : ℕ} [NeZero d] [NeZero e] {lam : Fin d → ℝ≥0} {π : Equiv.Perm (Fin d)}
  {mu : Fin e → ℝ≥0} {σ : Equiv.Perm (Fin e)} {hl : (∑ i, lam i) = 1} {hm : (∑ j, mu j) = 1}
  {n : ℕ} {S : Fin (n + 1) → ℝ} {ρ : Equiv.Perm (Fin n)}

/-- **A cell below the `k`-th entry has its image start below that entry.** -/
theorem listImageLeft_lt_of_lt {D : IETDatum d} {E : IETDatum e}
    (P : IsCompPresentation lam π mu σ hl hm n S ρ)
    (hF : ∀ y, (mkIET1 mu σ hm * mkIET1 lam π hl) y = E.toFun (D.toFun y))
    {k : Fin (n + 1)} (hu : IsPairSplitting D E (S k)) {i : Fin n} (hik : i.val < k.val) :
    listImageLeft ρ S i < S k := by
  have hSk : S k ∈ Set.Icc (0 : ℝ) 1 := list_mem_Icc P.mono P.zero P.top k
  have hcell : Set.Ico (S i.castSucc) (S i.succ) ⊆ Set.Ico (0 : ℝ) (S k) := by
    intro x hx
    refine ⟨le_trans (list_mem_Icc P.mono P.zero P.top i.castSucc).1 hx.1, ?_⟩
    refine lt_of_lt_of_le hx.2 (P.mono.monotone ?_)
    rw [Fin.le_def, Fin.val_succ]
    exact hik
  have himg : Set.Ico (listImageLeft ρ S i) (listImageLeft ρ S i + (S i.succ - S i.castSucc))
      ⊆ Set.Ico (0 : ℝ) (S k) := by
    rw [← comp_image_cell P i]
    refine (Set.image_mono hcell).trans (le_of_eq ?_)
    exact comp_image_Ico_zero hu hSk.2 hF
  have hmem : listImageLeft ρ S i
      ∈ Set.Ico (listImageLeft ρ S i) (listImageLeft ρ S i + (S i.succ - S i.castSucc)) :=
    ⟨le_refl _, by linarith [listLen_pos P.mono i]⟩
  exact (himg hmem).2

/-- **A cell at or above the `k`-th entry has its image start at or above that entry.** -/
theorem listImageLeft_ge_of_le {D : IETDatum d} {E : IETDatum e}
    (P : IsCompPresentation lam π mu σ hl hm n S ρ)
    (hF : ∀ y, (mkIET1 mu σ hm * mkIET1 lam π hl) y = E.toFun (D.toFun y))
    {k : Fin (n + 1)} (hu : IsPairSplitting D E (S k)) {i : Fin n} (hki : k.val ≤ i.val) :
    S k ≤ listImageLeft ρ S i := by
  have hSk : S k ∈ Set.Icc (0 : ℝ) 1 := list_mem_Icc P.mono P.zero P.top k
  have hcell : Set.Ico (S i.castSucc) (S i.succ) ⊆ Set.Ico (S k) 1 := by
    intro x hx
    refine ⟨le_trans (P.mono.monotone ?_) hx.1, ?_⟩
    · rw [Fin.le_def]
      exact hki
    · exact lt_of_lt_of_le hx.2 (list_mem_Icc P.mono P.zero P.top i.succ).2
  have himg : Set.Ico (listImageLeft ρ S i) (listImageLeft ρ S i + (S i.succ - S i.castSucc))
      ⊆ Set.Ico (S k) 1 := by
    rw [← comp_image_cell P i]
    refine (Set.image_mono hcell).trans (le_of_eq ?_)
    exact comp_image_Ico_one hu hSk.1 hF
  have hmem : listImageLeft ρ S i
      ∈ Set.Ico (listImageLeft ρ S i) (listImageLeft ρ S i + (S i.succ - S i.castSucc)) :=
    ⟨le_refl _, by linarith [listLen_pos P.mono i]⟩
  exact (himg hmem).1

end BlockStarts

section Stab

variable {d e : ℕ} [NeZero d] [NeZero e] {lam : Fin d → ℝ≥0} {π : Equiv.Perm (Fin d)}
  {mu : Fin e → ℝ≥0} {σ : Equiv.Perm (Fin e)} {hl : (∑ i, lam i) = 1} {hm : (∑ j, mu j) = 1}
  {n : ℕ} {S : Fin (n + 1) → ℝ} {ρ : Equiv.Perm (Fin n)}

/-- **The block permutation preserves the initial segment at a pair-splitting entry.** -/
theorem rho_lt_iff {D : IETDatum d} {E : IETDatum e}
    (P : IsCompPresentation lam π mu σ hl hm n S ρ)
    (hF : ∀ y, (mkIET1 mu σ hm * mkIET1 lam π hl) y = E.toFun (D.toFun y))
    {k : Fin (n + 1)} (hu : IsPairSplitting D E (S k)) (i : Fin n) :
    (i.val < k.val ↔ (ρ i).val < k.val) := by
  have hpos : ∀ j : Fin n, 0 < S j.succ - S j.castSucc := listLen_pos P.mono
  have himg : ∀ j : Fin n, listImageLeft ρ S j < listImageLeft ρ S i ↔ ρ j < ρ i := by
    intro j
    constructor
    · intro h
      by_contra hcon
      rw [not_lt] at hcon
      rcases lt_or_eq_of_le hcon with hlt | heq
      · exact absurd h (not_lt.mpr (le_of_lt (listImageLeft_lt hpos hlt)))
      · have hji : i = j := ρ.injective heq
        rw [hji] at h
        exact absurd h (lt_irrefl _)
    · intro h
      exact listImageLeft_lt hpos h
  have hcell : ∀ j : Fin n, listImageLeft ρ S j < S k ↔ j.val < k.val := by
    intro j
    exact ⟨fun h => by_contra fun hcon =>
        absurd h (not_lt.mpr (listImageLeft_ge_of_le P hF hu (not_lt.mp hcon))),
      fun h => listImageLeft_lt_of_lt P hF hu h⟩
  set A := Finset.univ.filter (fun j : Fin n => listImageLeft ρ S j < listImageLeft ρ S i) with hA
  set B := Finset.univ.filter (fun j : Fin n => listImageLeft ρ S j < S k) with hB
  have hAcard : A.card = (ρ i).val := by
    rw [hA]
    have h1 : (Finset.univ.filter (fun j : Fin n => listImageLeft ρ S j < listImageLeft ρ S i))
        = Finset.univ.filter (fun j : Fin n => ρ j < ρ i) := by
      exact Finset.filter_congr (fun j _ => himg j)
    rw [h1]
    exact card_rho_lt i
  have hBcard : B.card = k.val := by
    rw [hB]
    have h1 : (Finset.univ.filter (fun j : Fin n => listImageLeft ρ S j < S k))
        = Finset.univ.filter (fun j : Fin n => j.val < k.val) := by
      exact Finset.filter_congr (fun j _ => hcell j)
    rw [h1]
    exact card_fin_lt (show k.val ≤ n by have := k.isLt; omega)
  constructor
  · intro hik
    have hsub : A ⊆ B := by
      intro j hj
      rw [hA] at hj
      rw [hB]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact lt_trans hj (listImageLeft_lt_of_lt P hF hu hik)
    have hssub : A ⊂ B := by
      refine ⟨hsub, ?_⟩
      intro hBA
      have hiB : i ∈ B := by
        rw [hB]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact listImageLeft_lt_of_lt P hF hu hik
      have hiA : i ∈ A := hBA hiB
      rw [hA] at hiA
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiA
      exact absurd hiA (lt_irrefl _)
    rw [← hAcard, ← hBcard]
    exact Finset.card_lt_card hssub
  · intro hcon'
    by_contra hcon
    rw [not_lt] at hcon
    have hsub : B ⊆ A := by
      intro j hj
      rw [hB] at hj
      rw [hA]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact lt_of_lt_of_le hj (listImageLeft_ge_of_le P hF hu hcon)
    have hle := Finset.card_le_card hsub
    rw [hBcard, hAcard] at hle
    omega

end Stab

section StabTwo

variable {d e : ℕ} [NeZero d] [NeZero e] {lam : Fin d → ℝ≥0} {π : Equiv.Perm (Fin d)}
  {mu : Fin e → ℝ≥0} {σ : Equiv.Perm (Fin e)} {hl : (∑ i, lam i) = 1} {hm : (∑ j, mu j) = 1}
  {n : ℕ} {S : Fin (n + 1) → ℝ} {ρ : Equiv.Perm (Fin n)}

/-- **The block permutation preserves the initial segments at the block's ends.** -/
theorem blockPerm_stab {D : IETDatum d} {E : IETDatum e}
    (P : IsCompPresentation lam π mu σ hl hm n S ρ)
    (hF : ∀ y, (mkIET1 mu σ hm * mkIET1 lam π hl) y = E.toFun (D.toFun y))
    {k l : Fin (n + 1)} (hk : IsPairSplitting D E (S k)) (hl' : IsPairSplitting D E (S l))
    (i : Fin n) :
    (i.val < k.val ↔ (ρ i).val < k.val) ∧ (i.val < l.val ↔ (ρ i).val < l.val) :=
  ⟨rho_lt_iff P hF hk i, rho_lt_iff P hF hl' i⟩

end StabTwo

section BlockApplication

variable {d e : ℕ} [NeZero d] [NeZero e] {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
  {q₀ : PReal d e}

/-- **The composition, as the exchange of the presentation.** -/
theorem GoodRegion.comp_eq_toFun (G : GoodRegion d e π σ q₀) [NeZero G.n]
    {q : PReal d e} (hq : q ∈ G.O)
    {D : IETDatum d} {E : IETDatum e} (h : G.Fits q D E) :
    ∀ y, (mkIET1 (simplexMap e q.2) σ (G.simplexMap_mem_simplex_snd hq)
        * mkIET1 (simplexMap d q.1) π (G.simplexMap_mem_simplex_fst hq)) y
      = E.toFun (D.toFun y) := by
  have P := G.pres q hq
  intro y
  rw [P.eq_mkIET1, ← G.datum_toFun hq h y]
  change (mkIET1 (compLen P.mono) G.ρ _) y
      = mkIETFun (G.datum hq).lam G.ρ 0 y
  rw [G.datum_lam hq]
  rfl

/-- **The block permutation of the marked cells**, packaged: `ρ` restricted to the block
`[i₀, i₁)`, as a permutation of `Fin (i₁ - i₀)`.  Its `hstab` is *derived* from the pair-splitting
property of the block's ends (`blockPerm_stab`). -/
noncomputable def GoodRegion.blockOf (G : GoodRegion d e π σ q₀) [NeZero G.n]
    {q : PReal d e} (hq : q ∈ G.O)
    {D : IETDatum d} {E : IETDatum e} (h : G.Fits q D E)
    {i₀ i₁ : Fin (G.n + 1)} (hi : i₀ < i₁) (hk : IsPairSplitting D E (G.s i₀ q))
    (hl' : IsPairSplitting D E (G.s i₁ q)) : Block G :=
  ⟨⟨i₀.val, i₁.val, hi, by have := i₁.isLt; omega⟩,
    blockPerm_stab (G.pres q hq) (G.comp_eq_toFun hq h) hk hl'⟩

/-- **The block permutation on its own**: the `perm` of `G.blockOf`, as a permutation of
`Fin (i₁ - i₀)`. -/
noncomputable def GoodRegion.blockPermOf (G : GoodRegion d e π σ q₀) [NeZero G.n]
    {q : PReal d e} (hq : q ∈ G.O)
    {D : IETDatum d} {E : IETDatum e} (h : G.Fits q D E)
    {i₀ i₁ : Fin (G.n + 1)} (hi : i₀ < i₁) (hk : IsPairSplitting D E (G.s i₀ q))
    (hl' : IsPairSplitting D E (G.s i₁ q)) :
    Equiv.Perm (Fin (i₁.val - i₀.val)) :=
  (G.blockOf hq h hi hk hl').perm

/-- **Lemma 3.2 gives the irreducibility of the block permutation.**  For a good region, a parameter
`q`, two data with those parameters and permutations, and a block `[s i₀, s i₁)` whose ends are
pair-splitting: the permutation `ρ` of the presentation preserves the two initial segments
(`blockPerm_stab`, from the invariance of the block), and Lemma 3.2 read on the datum of the
presentation (`irreducibleOn_datum`) feeds `irreduciblePerm_blockPerm`. -/
theorem GoodRegion.irreduciblePerm_blockPerm (G : GoodRegion d e π σ q₀) [NeZero G.n]
    {q : PReal d e} (hq : q ∈ G.O)
    {D : IETDatum d} {E : IETDatum e} (h : G.Fits q D E)
    {i₀ i₁ : Fin (G.n + 1)} (hi : i₀ < i₁) (hk : IsPairSplitting D E (G.s i₀ q))
    (hl' : IsPairSplitting D E (G.s i₁ q))
    (hirr : IsCompIrreducibleOn D E (G.s i₀ q) (G.s i₁ q)) :
    IsIrreduciblePerm (blockPerm G.ρ i₀.val (l := i₁.val) hi
      (by have := i₁.isLt; omega) (blockPerm_stab (G.pres q hq)
        (G.comp_eq_toFun hq h) hk hl')) := by
  have hln : i₁.val ≤ G.n := by have := i₁.isLt; omega
  have P := G.pres q hq
  -- the block, in the coordinates of the datum
  have hleft : leftEnd (G.datum hq).lam ⟨i₀.val, by omega⟩ = G.s i₀ q := by
    rw [G.datum_lam hq]
    exact leftEnd_compLen (monoAt G hq) P.zero ⟨i₀.val, by omega⟩
  have hright : leftEnd (G.datum hq).lam ⟨i₀.val, by omega⟩
      + blockMass (G.datum hq).lam i₀.val hln = G.s i₁ q := by
    rw [G.datum_lam hq]
    exact leftEnd_add_blockMass_compLen (monoAt G hq) P.zero hi hln
  have hirr' : IsCompIrreducibleOn D E
      (leftEnd (G.datum hq).lam ⟨i₀.val, by omega⟩)
      (leftEnd (G.datum hq).lam ⟨i₀.val, by omega⟩
        + blockMass (G.datum hq).lam i₀.val hln) := by
    rw [hright, hleft]
    exact hirr
  exact @_root_.irreduciblePerm_blockPerm G.n inferInstance i₀.val i₁.val (G.datum hq)
    hi hln
    (blockPerm_stab (G.pres q hq)
      (G.comp_eq_toFun hq h) hk hl')
    (G.irreducibleOn_datum hq h hirr')

end BlockApplication

section BlockApplicationAE

variable {d e : ℕ} [NeZero d] [NeZero e] {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
  {q₀ : PReal d e}

/-- **Lemma 3.2 gives the irreducibility of the packaged block permutation.** -/
theorem GoodRegion.isIrreduciblePerm_blockPermOf (G : GoodRegion d e π σ q₀) [NeZero G.n]
    {q : PReal d e} (hq : q ∈ G.O)
    {D : IETDatum d} {E : IETDatum e} (h : G.Fits q D E)
    {i₀ i₁ : Fin (G.n + 1)} (hi : i₀ < i₁) (hk : IsPairSplitting D E (G.s i₀ q))
    (hl' : IsPairSplitting D E (G.s i₁ q))
    (hirr : IsCompIrreducibleOn D E (G.s i₀ q) (G.s i₁ q)) :
    IsIrreduciblePerm (G.blockOf hq h hi hk hl').perm :=
  G.irreduciblePerm_blockPerm hq h hi hk hl' hirr

end BlockApplicationAE

-- `NeZero (i₁ - i₀)` is an *instance* here (`mkIET1` and `mkIET1_rescale_subinterval` need it as
-- such), so `haveI` is the right binder; the style linter only sees that its value is a `Prop`.
set_option linter.style.haveILetI false

/-! ### The rescaled composition on a block of marked cells

Lemma 3.4 applies Theorem 2.6 to the pair `(g ∘ f, g)` restricted to the block `[u,v)` and rescaled
to `[0,1)`.  This section defines the rescaled *composition* `GoodRegion.blockRescaled` and proves
the pointwise conjugacy `GoodRegion.comp_conj_rescale` by which the composition on the block is its
rescaled version: the input of `exists_word_trivial_on_block_of_rescaled`. -/

variable {d e : ℕ} [NeZero d] [NeZero e] {π : Equiv.Perm (Fin d)} {σ : Equiv.Perm (Fin e)}
  {q₀ : PReal d e}

namespace GoodRegion

/-- **The rescaled composition on a block of marked cells**: the exchange of `[0,1)` obtained by
restricting `g ∘ f` to `[s i₀, s i₁)` and rescaling. -/
noncomputable def blockRescaled (G : GoodRegion d e π σ q₀) [NeZero G.n]
    {q : PReal d e} (hq : q ∈ G.O)
    {D : IETDatum d} {E : IETDatum e} (h : G.Fits q D E)
    {i₀ i₁ : Fin (G.n + 1)} (hi : i₀ < i₁) (hk : IsPairSplitting D E (G.s i₀ q))
    (hk' : IsPairSplitting D E (G.s i₁ q)) : IET 0 1 := by
  haveI : NeZero (i₁.val - i₀.val) := ⟨by omega⟩
  exact mkIET1 (G.blockLam hq i₀.val (l := i₁.val) hi (by omega))
    (G.blockPermOf hq h hi hk hk')
    (G.blockLam_sum hq i₀.val hi (by omega))

/-- **The composition on the block is the rescaled composition**: the pointwise conjugacy by
`rescaleMapInv u v`, for `u = s i₀`, `v = s i₁`. -/
theorem comp_conj_rescale (G : GoodRegion d e π σ q₀) [NeZero G.n]
    {q : PReal d e} (hq : q ∈ G.O)
    {D : IETDatum d} {E : IETDatum e} (h : G.Fits q D E)
    {i₀ i₁ : Fin (G.n + 1)} (hi : i₀ < i₁) (hk : IsPairSplitting D E (G.s i₀ q))
    (hk' : IsPairSplitting D E (G.s i₁ q)) {y : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    (E.toIET * D.toIET) (rescaleMapInv (G.s i₀ q) (G.s i₁ q) y)
      = rescaleMapInv (G.s i₀ q) (G.s i₁ q)
          (G.blockRescaled hq h hi hk hk' y) := by
  classical
  have hln : i₁.val ≤ G.n := by have := i₁.isLt; omega
  have hne : NeZero (i₁.val - i₀.val) := ⟨by omega⟩
  have P := G.pres q hq
  have hpos := G.cellLen_pos hq
  have hsum : (∑ i, G.cellLen hq i) = 1 := G.cellLen_sum hq
  set L := leftEnd (G.cellLen hq) ⟨i₀.val, by omega⟩ with hLdef
  set M := blockMass (G.cellLen hq) i₀.val hln with hMdef
  have hMpos : 0 < M := by rw [hMdef]; exact blockMass_pos hpos i₀.val hi hln
  have hLval : L = G.s i₀ q := by
    rw [hLdef]
    exact leftEnd_compLen (monoAt G hq) P.zero ⟨i₀.val, by omega⟩
  have hLM : L + M = G.s i₁ q := by
    rw [hLdef, hMdef]
    exact leftEnd_add_blockMass_compLen (monoAt G hq) P.zero hi hln
  -- the composition, as the exchange of the presentation
  have hcomp : ∀ z, (mkIET1 (G.cellLen hq) G.ρ hsum) z
      = (E.toIET * D.toIET) z := by
    intro z
    have h1 : mkIET1 (G.cellLen hq) G.ρ hsum
        = mkIET1 (compLen P.mono) G.ρ (compLen_sum P.mono P.zero P.top) := rfl
    have h2 : mkIET1 (compLen P.mono) G.ρ (compLen_sum P.mono P.zero P.top)
        = E.toIET * D.toIET := by
      rw [← P.eq_mkIET1]
      refine IET.ext fun z => ?_
      rw [IET.mul_apply, IET.mul_apply, IETDatum.toIET_apply, IETDatum.toIET_apply]
      exact G.comp_eq_toFun hq h z
    rw [h1, h2]
  -- the point in the block and the rescaled restriction
  haveI := hne
  set x := rescaleMapInv L (L + M) y with hxdef
  have hLlt : L < L + M := by linarith
  have hx : x ∈ Set.Ico L (L + M) := by
    rw [hxdef, rescaleMapInv]
    have hpos2 : 0 < L + M - L := by linarith
    have hnn : 0 ≤ y * (L + M - L) := mul_nonneg hy.1 hpos2.le
    refine ⟨by linarith, ?_⟩
    have h1 : y * (L + M - L) < 1 * (L + M - L) := mul_lt_mul_of_pos_right hy.2 hpos2
    nlinarith [h1]
  have hxy : rescaleMap L (L + M) x = y := by
    rw [hxdef]
    exact rescaleMap_rescaleMapInv hLlt y
  have hstab := blockPerm_stab P (G.comp_eq_toFun hq h) hk hk'
  have hres := RescaleBlock.mkIET1_rescale_subinterval (n := G.n)
    (lam := G.cellLen hq) (π := G.ρ) ⟨i₀.val, i₁.val, hi, hln⟩ hsum hpos hstab x hx
  rw [hxy] at hres
  -- identify the two rescalings
  have hφ : ∀ z, rescaleMapInv (G.s i₀ q) (G.s i₁ q) z = rescaleMapInv L (L + M) z := by
    intro z
    rw [rescaleMapInv, rescaleMapInv, ← hLval, ← hLM]
  simp only [hφ]
  rw [← hxdef]
  rw [← hcomp x]
  rw [show G.blockRescaled hq h hi hk hk'
      = mkIET1 (G.blockLam hq i₀.val (l := i₁.val) hi (by omega))
          (blockPerm G.ρ i₀.val (l := i₁.val) hi (by omega) hstab)
          (G.blockLam_sum hq i₀.val hi (by omega)) from rfl]
  simp only [GoodRegion.blockLam_def]
  rw [← hres, rescaleMapInv_rescaleMap hLlt]

/-- **The `g`-side of the transport**: on a block of marked cells, the exchange `E` is its own
rescaled restriction, with the truncated lengths `μ'` and the *same* permutation `σ`. -/
theorem restrict_rescale (G : GoodRegion d e π σ q₀)
    {q : PReal d e} (hq : q ∈ G.O)
    {D : IETDatum d} {E : IETDatum e} (h : G.Fits q D E)
    {i₀ i₁ : Fin (G.n + 1)} (hi : i₀ < i₁) (hk : IsPairSplitting D E (G.s i₀ q))
    (hk' : IsPairSplitting D E (G.s i₁ q)) {y : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    E.toIET (rescaleMapInv (G.s i₀ q) (G.s i₁ q) y)
      = rescaleMapInv (G.s i₀ q) (G.s i₁ q)
        (mkIET1 (RestrictIET.truncatedLengths (simplexMap e q.2) (G.s i₀ q) (G.s i₁ q)
            (by have _h := hk.mem_Icc; have _h' := hk'.mem_Icc
                have hlt : G.s i₀ q < G.s i₁ q := monoAt G hq hi
                linarith))
          σ (RestrictIET.sum_truncatedLengths (simplexMap e q.2) (G.simplexMap_mem_simplex_snd hq)
            (by exact (hk.mem_Icc).1)
            (by have _h := hk.mem_Icc; have _h' := hk'.mem_Icc
                have hlt : G.s i₀ q < G.s i₁ q := monoAt G hq hi
                linarith)
            (by exact (hk'.mem_Icc).2)) y) := by
  classical
  have hm : simplexMap e q.2 ∈ simplex e := G.simplexMap_mem_simplex_snd hq
  have hr := G.subset_region q hq
  have hpos : ∀ j, 0 < simplexMap e q.2 j := pos_simplexMap hr.2
  have h0u : 0 ≤ G.s i₀ q := (hk.mem_Icc).1
  have h0v : (0 : ℝ) ≤ G.s i₁ q := (hk'.mem_Icc).1
  have h1v : G.s i₁ q ≤ 1 := (hk'.mem_Icc).2
  have huv : G.s i₀ q < G.s i₁ q := by
    have hlt : i₀ < i₁ := hi
    exact monoAt G hq (by simpa using hlt)
  have htot : (∑ j, (simplexMap e q.2 j : ℝ)) = 1 := by
    rw [← NNReal.coe_sum]; exact_mod_cast hm
  -- the exchange `E` is `mkIET1` of its own length vector
  have hE : E.toIET = mkIET1 (simplexMap e q.2) σ hm := by
    refine IET.ext fun x => ?_
    change mkIETFun E.lam E.π 0 x = mkIETFun (simplexMap e q.2) σ 0 x
    rw [show E.lam = simplexMap e q.2 from by rw [IETDatum.lam, h.hEv], h.hEπ]
  -- the invariance of the block under `g`
  have hinv : ∀ x ∈ Set.Ico (G.s i₀ q) (G.s i₁ q),
      (mkIET1 (simplexMap e q.2) σ hm x ∈ Set.Ico (G.s i₀ q) (G.s i₁ q) ↔
        x ∈ Set.Ico (G.s i₀ q) (G.s i₁ q)) := by
    intro x hx
    have hx01 : x ∈ Set.Ico (0 : ℝ) 1 := ⟨le_trans h0u hx.1, lt_of_lt_of_le hx.2 h1v⟩
    rw [← hE]
    exact (IsPairSplitting.iff_mem hk hk' hx01).2.symm
  obtain ⟨mu', hl', hmu'form, hmu'eq⟩ :=
    RestrictIET.mkIET1_restrict_invariant hm hpos h0u huv h1v hinv
  -- rewrite `mu'` as the named family
  have hcoe : mu' = RestrictIET.truncatedLengths (simplexMap e q.2) (G.s i₀ q) (G.s i₁ q) huv := by
    funext j
    exact NNReal.coe_injective (by rw [hmu'form j, RestrictIET.truncatedLengths_coe])
  subst hcoe
  -- the pointwise identity
  have hkey := hmu'eq y hy
  rw [rescaleFun] at hkey
  have hφ : rescaleMapInv (G.s i₀ q) (G.s i₁ q) (rescaleMap (G.s i₀ q) (G.s i₁ q)
      (mkIET1 (simplexMap e q.2) σ hm (rescaleMapInv (G.s i₀ q) (G.s i₁ q) y)))
      = mkIET1 (simplexMap e q.2) σ hm (rescaleMapInv (G.s i₀ q) (G.s i₁ q) y) :=
    rescaleMapInv_rescaleMap huv _
  rw [hkey] at hφ
  rw [hE]
  exact hφ.symm

/-! ### The degenerate block: one composition cell

A block that consists of a single marked cell of `g ∘ f` carries the word `genY * genX`, since the
composition is the identity there.  This is the `r = 1` case of Lemma 3.4's case analysis: the
rescaled composition is a one-cell exchange, hence the identity, and `genX` is the corresponding
word in the rescaled generators. -/

/-- **The block length vector of a single composition cell is the constant `1`.** -/
theorem blockLam_of_one {n : ℕ} {lam : Fin n → ℝ≥0} {k l : ℕ} (hkl : k < l)
    (hln : l ≤ n) (hpos : Positive lam) (h1 : l - k = 1) :
    _root_.blockLam lam k hkl hln hpos = fun _ => 1 := by
  funext j
  have hj : j.val = 0 := by have := j.isLt; omega
  have hidx : (⟨k + j.val, by omega⟩ : Fin n) = ⟨k, by omega⟩ := Fin.ext (by simp only; omega)
  have hmass : blockMass lam k hln = (lam ⟨k, by omega⟩ : ℝ) := by
    rw [blockMass]
    refine Finset.sum_eq_single (⟨0, by omega⟩ : Fin (l - k)) ?_ ?_
    · intro b _ hb
      exact absurd (Fin.ext (by have := b.isLt; omega)) hb
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine NNReal.coe_injective ?_
  rw [_root_.blockLam_coe, hmass, hidx]
  have hne : ((lam ⟨k, by omega⟩ : ℝ≥0) : ℝ) ≠ 0 := by
    simp only [ne_eq, NNReal.coe_eq_zero]
    exact ne_of_gt (hpos _)
  change (lam ⟨k, by omega⟩ : ℝ) / (lam ⟨k, by omega⟩ : ℝ) = ((1 : ℝ≥0) : ℝ)
  rw [div_self hne]
  simp

/-- **`genY * genX` is a nontrivial word**: it evaluates to the composition `g ∘ f`. -/
theorem genY_mul_genX_ne_one : genY * genX ≠ 1 := by
  intro h
  have h2 := congrArg FreeGroup.toWord h
  rw [FreeGroup.toWord_one] at h2
  exact absurd h2 (by decide)

end GoodRegion

/-! ### Lemma 3.4, the pointwise conclusion

`GoodRegion.exists_word_trivial_of_region` is the heart of Lemma 3.4: at a point `q` of a good
region, given the almost-sure block data *at that point* — unique ergodicity and rigidity for every
block permutation, and the Diophantine condition for every block — every block `[u,v)` carries a
nontrivial word which is the identity on it.  The block is a run of marked cells
(`GoodRegion.block_endpoints`), and the two cases are the one-cell case (the rescaled composition is
the identity, `mkIET1_of_all_one`, and the word is `genX`) and Theorem 2.6
(`irreducible_case`) followed by the word transport
(`exists_word_trivial_on_block_of_rescaled`, fed by `GoodRegion.comp_conj_rescale` and
`GoodRegion.restrict_rescale`). -/

-- `NeZero (i₁ - i₀)` is an instance here (`mkIET1` needs it), so `haveI` is the right binder.
set_option linter.style.haveILetI false

/-! ## Two helper lemmas for the single-cell case -/

/-- A generator of the free group is nontrivial. -/
theorem genX_ne_one : (genX : FreeGroup Gen) ≠ 1 := by
  intro h
  have h2 : FreeGroup.toWord genX = [] := by rw [h, FreeGroup.toWord_one]
  have h3 : FreeGroup.toWord genX = [(0, true)] := FreeGroup.toWord_of 0
  rw [h3] at h2
  exact absurd h2 (by decide)

/-- **An exchange all of whose lengths are `1` is the identity.**  The hypothesis `∑ lam = 1` forces
`Fin r` to be a subsingleton, and then every translation vector vanishes. -/
theorem mkIET1_of_all_one {r : ℕ} [NeZero r] {lam : Fin r → ℝ≥0} (π : Equiv.Perm (Fin r))
    (hl : (∑ i, lam i) = 1) (hlam : ∀ i, lam i = 1) : mkIET1 lam π hl = 1 := by
  have hcard : r = 1 := by
    have h1 : (∑ i : Fin r, lam i) = ∑ _i : Fin r, (1 : ℝ≥0) :=
      Finset.sum_congr rfl (fun i _ => hlam i)
    rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hl
    have h2 : ((r : ℝ≥0)) = 1 := by simpa using hl
    exact_mod_cast h2
  haveI : Subsingleton (Fin r) := by rw [hcard]; infer_instance
  have hzero : ∀ i : Fin r, i = 0 := fun i => Subsingleton.elim i 0
  refine IET.ext fun x => ?_
  rw [IET.one_apply]
  change mkIETFun lam π 0 x = x
  rw [mkIETFun]
  by_cases hx : x ∈ Set.Ico (0 : ℝ) (0 + ∑ i, (lam i : ℝ))
  · rw [dif_pos hx]
    have htv : translationVector π lam (idx lam (x - 0) (by linarith [hx.1])) = 0 := by
      rw [translationVector, imageLeft, leftEnd]
      have h1 : Finset.univ.filter (fun j : Fin r => π j < π (idx lam (x - 0) (by linarith [hx.1])))
          = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr (fun j hj => ?_)
        have h2 : π j = π (idx lam (x - 0) (by linarith [hx.1])) := by
          rw [hzero j, hzero (idx lam (x - 0) (by linarith [hx.1]))]
        rw [Finset.mem_filter] at hj
        rw [h2] at hj
        exact absurd hj.2 (lt_irrefl _)
      have h3 : Finset.univ.filter (fun j : Fin r => j < idx lam (x - 0) (by linarith [hx.1]))
          = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr (fun j hj => ?_)
        rw [Finset.mem_filter] at hj
        rw [hzero j, hzero (idx lam (x - 0) (by linarith [hx.1]))] at hj
        exact absurd hj.2 (lt_irrefl _)
      rw [h1, h3]
      simp
    rw [htv, add_zero]
  · rw [dif_neg hx]
