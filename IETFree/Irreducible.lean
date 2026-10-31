/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.Diophantine
import IETFree.MeasureTools
import IETFree.Centralizer
import IETFree.SingularityBound

/-!
Section 2 of the paper: the irreducible case.

The ambient interval is `[0, 1)`, and the two conditions of the paper (unique ergodicity, rigidity
by translations) plus the Diophantine condition are stated for exchanges in the sense of `IET 0 1`.

The measure-theoretic tools (`unitMeas` and its API, the words in two generators, the toolbox for
Lemma 2.10) are in `MeasureTools.lean`; Proposition 2.5 and the Diophantine definitions are in
`Diophantine.lean`.  Both are imported below.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal commutatorElement

/-! ## The two conditions of the paper (Definitions 2.1 and 2.2) -/

/-- Definition 2.1, in the strong form: the Birkhoff averages of every continuous test function
converge to their integral, uniformly. -/
def UniqueErgodic (f : IET 0 1) : Prop :=
  ∀ ψ : ℝ → ℝ, Continuous ψ → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
    ∀ n ≥ N, ∀ x ∈ Set.Ico (0 : ℝ) 1,
      |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ψ ((f ^ i) x) - ∫ y, ψ y ∂unitMeas| ≤ ε

/-- Definition 2.2: rigid by translations. -/
def IsRigidByTranslations (f : IET 0 1) : Prop :=
  ∃ q : ℕ → ℕ, ∃ t : ℕ → ℝ, ∃ B : ℕ → Set ℝ,
    Tendsto q atTop atTop ∧ Tendsto t atTop (nhds 0) ∧
      (∀ n, B n ⊆ Set.Ico (0 : ℝ) 1) ∧ (∀ n, MeasurableSet (B n)) ∧
        Tendsto (fun n => unitMeas.real (B n)) atTop (nhds 1) ∧
          ∀ (n : ℕ) (x : ℝ), x ∈ B n → ((f ^ q n) x) = x + t n

/-- The paper's irreducibility of a permutation. -/
def IsIrreduciblePerm {d : ℕ} (π : Equiv.Perm (Fin d)) : Prop :=
  ∀ k : Fin d, (∀ i : Fin d, i ≤ k → π i ≤ k) → ∀ i : Fin d, i ≤ k

/-! ## The two external hypotheses -/

/-- **Masur–Veech**: for `d ≥ 2` and every irreducible permutation, almost every length vector
gives a uniquely ergodic exchange.

The restriction `2 ≤ d` is needed: on one cell the exchange is the identity for every length vector
(`translationVector` vanishes), and the identity is not uniquely ergodic (its Birkhoff averages of
`y ↦ y` are constantly `y`), while `IsIrreduciblePerm` holds on `Fin 1`.  For `d ≥ 2`,
`IsIrreduciblePerm π` already excludes the identity and every permutation with a fixed cell: it says
that the only initial segment `{i | i ≤ k}` mapped into itself by `π` is the whole of `Fin d`, which
for `k = 0` forbids `π 0 = 0` — the paper's "no splitting singularity" condition. -/
def MasurVeech : Prop :=
  ∀ (d : ℕ) (_ : 2 ≤ d) [NeZero d] (π : Equiv.Perm (Fin d)), IsIrreduciblePerm π →
    ∀ᵐ lam ∂(simplexVolume d),
      ∀ (h : lam ∈ simplex d), UniqueErgodic (mkIET1 lam π h)

/-- **Veech rigidity**: for every irreducible permutation, almost every length vector gives an
exchange rigid by translations. -/
def VeechRigidity : Prop :=
  ∀ (d : ℕ) [NeZero d] (π : Equiv.Perm (Fin d)), IsIrreduciblePerm π →
    ∀ᵐ lam ∂(simplexVolume d),
      ∀ (h : lam ∈ simplex d), IsRigidByTranslations (mkIET1 lam π h)

/-! ## The statements of Section 2 -/

/-- **Lemma 2.7**: for nontrivial words `u`, `v` in `F_2`, one of `[u,v]`, `[x⁻¹ux,v]`,
`[y⁻¹uy,v]` is nontrivial.  The statement below uses Mathlib's commutator
`⁅u, v⁆ = u * v * u⁻¹ * v⁻¹`; the paper's `[u,v] = u⁻¹v⁻¹uv` is `⁅u⁻¹, v⁻¹⁆`, and the two vanish
together (`commutatorElement_inv_inv_eq_one_iff`), so the lemma holds in either convention.

Proof: if all three commutators are trivial, then `u`, `genX⁻¹ * u * genX` and
`genY⁻¹ * u * genY` all lie in the cyclic group `C(v) = ⟨r⟩` (LS Prop. 2.19,
`FreeGroup.exists_zpow_eq_of_mul_comm`); writing `u = r ^ a` and `genX⁻¹ * u * genX = r ^ b` with
`a ≠ 0`, conjugate powers have equal exponents up to sign (`FreeGroup.natAbs_eq_of_conj_zpow`), so
`genX⁻¹ * u * genX = u ^ ±1` and hence `genX ^ 2` centralises `u`, likewise `genY ^ 2`.  Then
`C(u)` is cyclic too, so `genX ^ 2` and `genY ^ 2` commute, contradicting
`FreeGroup.pow_two_mul_pow_two_of_ne` (as `genX ≠ genY`).  No cyclic-length or conjugate-to-inverse
theory is needed. -/
theorem exists_nontrivial_commutator (u v : FreeGroup Gen) (hu : u ≠ 1) (hv : v ≠ 1) :
    ⁅u, v⁆ ≠ 1 ∨ ⁅genX⁻¹ * u * genX, v⁆ ≠ 1 ∨ ⁅genY⁻¹ * u * genY, v⁆ ≠ 1 := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3⟩ := h
  -- the three conjugates all commute with `v`
  have huv : u * v = v * u := (commutatorElement_eq_one_iff_mul_comm ..).mp h1
  have hxv : (genX⁻¹ * u * genX) * v = v * (genX⁻¹ * u * genX) :=
    (commutatorElement_eq_one_iff_mul_comm ..).mp h2
  have hyv : (genY⁻¹ * u * genY) * v = v * (genY⁻¹ * u * genY) :=
    (commutatorElement_eq_one_iff_mul_comm ..).mp h3
  -- the centralizer of `v` is cyclic
  obtain ⟨r, hr⟩ := FreeGroup.exists_zpow_eq_of_mul_comm hv
  obtain ⟨k, hk⟩ := hr v rfl
  have hrne : r ≠ 1 := by
    rintro rfl
    simp only [one_zpow] at hk
    exact hv hk
  obtain ⟨a, ha⟩ := hr u huv
  obtain ⟨b, hb⟩ := hr (genX⁻¹ * u * genX) hxv
  obtain ⟨c, hc⟩ := hr (genY⁻¹ * u * genY) hyv
  have hux : genX⁻¹ * u * genX ≠ 1 := by
    intro hconj
    apply hu
    have := congrArg (fun t => genX * t * genX⁻¹) hconj
    simpa [mul_assoc] using this
  have huy : genY⁻¹ * u * genY ≠ 1 := by
    intro hconj
    apply hu
    have := congrArg (fun t => genY * t * genY⁻¹) hconj
    simpa [mul_assoc] using this
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zpow_zero] at ha
    exact hu ha
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zpow_zero] at hb
    exact hux hb
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zpow_zero] at hc
    exact huy hc
  -- conjugate powers have equal exponents up to sign
  have hab : a.natAbs = b.natAbs := by
    refine FreeGroup.natAbs_eq_of_conj_zpow (g := genX⁻¹) hrne ha0 hb0 ?_
    rw [inv_inv]
    calc genX⁻¹ * r ^ a * genX = genX⁻¹ * u * genX := by rw [ha]
      _ = r ^ b := hb
  have hac : a.natAbs = c.natAbs := by
    refine FreeGroup.natAbs_eq_of_conj_zpow (g := genY⁻¹) hrne ha0 hc0 ?_
    rw [inv_inv]
    calc genY⁻¹ * r ^ a * genY = genY⁻¹ * u * genY := by rw [ha]
      _ = r ^ c := hc
  -- hence each conjugate is `u` or `u⁻¹`
  have hxu : genX⁻¹ * u * genX = u ∨ genX⁻¹ * u * genX = u⁻¹ := by
    have hba : a = b ∨ a = -b := Int.natAbs_eq_natAbs_iff.mp hab
    rcases hba with hba | hba
    · left; rw [hb, ← hba, ← ha]
    · right
      have hb' : b = -a := by omega
      rw [hb, hb', zpow_neg, ← ha]
  have hyu : genY⁻¹ * u * genY = u ∨ genY⁻¹ * u * genY = u⁻¹ := by
    have hca : a = c ∨ a = -c := Int.natAbs_eq_natAbs_iff.mp hac
    rcases hca with hca | hca
    · left; rw [hc, ← hca, ← ha]
    · right
      have hc' : c = -a := by omega
      rw [hc, hc', zpow_neg, ← ha]
  -- squaring kills the sign, so the squares centralize `u`
  have hX2 : (genX ^ 2)⁻¹ * u * genX ^ 2 = u := by
    rcases hxu with h | h
    · calc (genX ^ 2)⁻¹ * u * genX ^ 2
          = genX⁻¹ * (genX⁻¹ * u * genX) * genX := by rw [pow_two, mul_inv_rev]; group
        _ = genX⁻¹ * u * genX := by conv_lhs => rw [h]
        _ = u := h
    · calc (genX ^ 2)⁻¹ * u * genX ^ 2
          = genX⁻¹ * (genX⁻¹ * u * genX) * genX := by rw [pow_two, mul_inv_rev]; group
        _ = genX⁻¹ * u⁻¹ * genX := by rw [h]
        _ = (genX⁻¹ * u * genX)⁻¹ := by group
        _ = u := by rw [h, inv_inv]
  have hY2 : (genY ^ 2)⁻¹ * u * genY ^ 2 = u := by
    rcases hyu with h | h
    · calc (genY ^ 2)⁻¹ * u * genY ^ 2
          = genY⁻¹ * (genY⁻¹ * u * genY) * genY := by rw [pow_two, mul_inv_rev]; group
        _ = genY⁻¹ * u * genY := by conv_lhs => rw [h]
        _ = u := h
    · calc (genY ^ 2)⁻¹ * u * genY ^ 2
          = genY⁻¹ * (genY⁻¹ * u * genY) * genY := by rw [pow_two, mul_inv_rev]; group
        _ = genY⁻¹ * u⁻¹ * genY := by rw [h]
        _ = (genY⁻¹ * u * genY)⁻¹ := by group
        _ = u := by rw [h, inv_inv]
  have hX2' : u * genX ^ 2 = genX ^ 2 * u := by
    have := congrArg (fun t => genX ^ 2 * t) hX2
    simpa [mul_assoc] using this
  have hY2' : u * genY ^ 2 = genY ^ 2 * u := by
    have := congrArg (fun t => genY ^ 2 * t) hY2
    simpa [mul_assoc] using this
  -- the centralizer of `u` is cyclic as well
  obtain ⟨r', hr'⟩ := FreeGroup.exists_zpow_eq_of_mul_comm hu
  obtain ⟨p, hp⟩ := hr' (genX ^ 2) hX2'.symm
  obtain ⟨q, hq⟩ := hr' (genY ^ 2) hY2'.symm
  have hfin : genX ^ 2 * genY ^ 2 = genY ^ 2 * genX ^ 2 := by
    calc genX ^ 2 * genY ^ 2 = r' ^ p * r' ^ q := by rw [hp, hq]
      _ = r' ^ (p + q) := (zpow_add r' p q).symm
      _ = r' ^ (q + p) := by rw [add_comm]
      _ = r' ^ q * r' ^ p := zpow_add r' q p
      _ = genY ^ 2 * genX ^ 2 := by rw [hp, hq]
  exact FreeGroup.pow_two_mul_pow_two_of_ne (x := (0 : Gen)) (y := 1) (by decide) hfin

/-- **Lemma 2.8**: if `f` is rigid by translations, some nontrivial word has support of measure at
most `ε`. -/
theorem exists_word_small_support (f g : IET 0 1) (hrig : IsRigidByTranslations f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ w : FreeGroup Gen, w ≠ 1 ∧ unitMeas.real (wordSupp w f g) ≤ ε := by
  classical
  obtain ⟨q, t, B, hq, ht, hBsub, hBmeas, hBμ, hBmap⟩ := hrig
  obtain ⟨sg, hsg⟩ := g.isIET.exists_isCutSet zero_lt_one
  have hfmap : ∀ y ∈ Set.Ico (0 : ℝ) 1, f y ∈ Set.Ico (0 : ℝ) 1 :=
    fun y hy => f.isIET.mapsTo hy
  -- the neighbourhood size
  set δ : ℝ := ε / (6 * ((sg.card : ℝ) + 1)) with hδdef
  have hδpos : 0 < δ := by
    have h6 : (0 : ℝ) < 6 * ((sg.card : ℝ) + 1) := by positivity
    exact div_pos hε h6
  -- choose `n` with `q n ≥ 1`, `|t n| ≤ δ` and `unitMeas.real (B n) ≥ 1 - ε/3`
  have hev : ∀ᶠ n in atTop, 1 ≤ q n ∧ |t n| ≤ δ ∧ 1 - ε / 3 ≤ unitMeas.real (B n) := by
    have h1 : ∀ᶠ n in atTop, 1 ≤ q n := hq.eventually (eventually_ge_atTop 1)
    have h2 : ∀ᶠ n in atTop, |t n| ≤ δ := by
      have hlt : ∀ᶠ n in atTop, |t n| < δ := by
        filter_upwards [ht.eventually (Metric.ball_mem_nhds (0 : ℝ) hδpos)] with m hm
        simpa [Real.dist_eq] using hm
      exact hlt.mono (fun m hm => le_of_lt hm)
    have h3 : ∀ᶠ n in atTop, 1 - ε / 3 ≤ unitMeas.real (B n) := by
      have hlt : ∀ᶠ n in atTop, 1 - ε / 3 < unitMeas.real (B n) :=
        hBμ.eventually (eventually_gt_nhds (by linarith))
      exact hlt.mono (fun m hm => le_of_lt hm)
    exact h1.and (h2.and h3)
  obtain ⟨n, hn⟩ := eventually_atTop.1 hev
  obtain ⟨hn1, hn2, hn3⟩ := hn n le_rfl
  set tt : ℝ := t n with htt
  set bb : Set ℝ := B n with hbb
  set qq : ℕ := q n with hqqdef
  have hqq : qq ≠ 0 := by omega
  have hbbmeas : MeasurableSet bb := hBmeas n
  -- the paper's word: the commutator `[g, f^q] = g⁻¹(f^q)⁻¹gf^q = ⁅g⁻¹, (f^q)⁻¹⁆`
  refine ⟨⁅genY⁻¹, (genX ^ qq)⁻¹⁆, commutator_inv_genY_genX_pow_ne_one hqq, ?_⟩
  -- the exceptional set: `x` is `t`-separated from a cut of `g`
  set U : Set ℝ := {x : ℝ | Separated sg x (x + tt)} with hU
  -- off `bbᶜ ∪ U ∪ g ⁻¹' bbᶜ` the commutator fixes `x`: the rigidity gives `f^q x = x + t`, no cut
  -- separates `x` from `x + t` so `g (x + t) = g x + t`, and `g x` is again in the rigidity set
  have hsupp : wordSupp ⁅genY⁻¹, (genX ^ qq)⁻¹⁆ f g ⊆ bbᶜ ∪ U ∪ (⇑g ⁻¹' bbᶜ) := by
    intro x hxsupp
    rw [Set.mem_union, Set.mem_union, Set.mem_compl_iff, Set.mem_preimage, Set.mem_compl_iff]
    by_cases hxbb : x ∈ bb
    · by_cases hxU : x ∈ U
      · exact Or.inl (Or.inr hxU)
      · by_cases hxg : ⇑g x ∈ bb
        · -- on this set the word fixes `x`
          have hxmem : x ∈ Set.Ico (0 : ℝ) 1 := hBsub n hxbb
          have hxq : ⇑(f ^ qq) x = x + tt := by simpa using hBmap n x hxbb
          have hpowmem : ∀ k : ℕ, (f ^ k) x ∈ Set.Ico (0 : ℝ) 1 := by
            intro k
            induction k with
            | zero => simpa using hxmem
            | succ m ih =>
              rw [pow_succ']
              exact hfmap _ ih
          have hxUm : ¬ Separated sg x (x + tt) := by
            intro hsep
            exact hxU (by rw [hU]; exact hsep)
          have hnoSep : ¬ Separated sg x (⇑(f ^ qq) x) := by
            rw [hxq]
            exact hxUm
          have hgt : ⇑g (⇑(f ^ qq) x) = ⇑g x + tt := by
            have htrans := hsg.transl_of_not_separated x (⇑(f ^ qq) x) hxmem (hpowmem qq) hnoSep
            rw [hxq] at htrans ⊢
            linarith
          have hfix : ⇑(f ^ qq) (⇑g x) = ⇑g x + tt := by simpa using hBmap n (⇑g x) hxg
          have hinv : ⇑((f ^ qq)⁻¹) (⇑g x + tt) = ⇑g x := by
            rw [← hfix]
            exact IET.symm_apply_apply (f ^ qq) (⇑g x)
          have hword : evalWord ⁅genY⁻¹, (genX ^ qq)⁻¹⁆ f g
              = g⁻¹ * (f ^ qq)⁻¹ * g * (f ^ qq) := by
            have hgenX : (FreeGroup.lift (fun i : Gen => if i = 0 then f else g)) genX = f := by
              simp [genX]
            have hgenY : (FreeGroup.lift (fun i : Gen => if i = 0 then f else g)) genY = g := by
              simp [genY]
            simp only [commutatorElement_def, evalWord, map_mul, map_inv, inv_inv, map_pow,
              hgenX, hgenY]
          have hone : (evalWord ⁅genY⁻¹, (genX ^ qq)⁻¹⁆ f g) x = x := by
            rw [hword]
            simp only [IET.mul_apply]
            rw [hgt, hinv]
            exact IET.symm_apply_apply g x
          exact absurd hone hxsupp
        · exact Or.inr hxg
    · exact Or.inl (Or.inl hxbb)
  -- each of the three pieces has measure at most `ε / 3`
  have hbbc : unitMeas.real bbᶜ ≤ ε / 3 := by
    rw [unitMeas_real_compl bb hbbmeas]
    linarith
  have hUbound : unitMeas.real U ≤ ε / 3 := by
    have hsub : U ⊆ ⋃ c ∈ sg, Set.Icc (c - |tt|) (c + |tt|) := by
      intro x hx
      rw [hU] at hx
      obtain ⟨c, hc, hci⟩ := hx
      refine Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hc, ?_⟩⟩
      have h1 : min x (x + tt) < c := hci.1
      have h2 : c ≤ max x (x + tt) := hci.2
      rcases le_or_gt 0 tt with h | h
      · rw [min_eq_left (by linarith : x ≤ x + tt)] at h1
        rw [max_eq_right (by linarith : x ≤ x + tt)] at h2
        rw [abs_of_nonneg h]
        exact ⟨by linarith, by linarith⟩
      · rw [min_eq_right (by linarith : x + tt ≤ x)] at h1
        rw [max_eq_left (by linarith : x + tt ≤ x)] at h2
        rw [abs_of_neg h]
        exact ⟨by linarith, by linarith⟩
    calc unitMeas.real U ≤ unitMeas.real (⋃ c ∈ sg, Set.Icc (c - |tt|) (c + |tt|)) :=
          unitMeas_real_mono hsub
      _ ≤ ∑ c ∈ sg, unitMeas.real (Set.Icc (c - |tt|) (c + |tt|)) :=
          unitMeas_real_biUnion_finset_le sg _
      _ ≤ ∑ _c ∈ sg, 2 * |tt| := by
          refine Finset.sum_le_sum (fun c _ => ?_)
          refine le_trans (unitMeas_real_Icc_le (c - |tt|) (c + |tt|)) ?_
          rw [max_eq_left (by linarith [abs_nonneg tt] : (0 : ℝ) ≤ c + |tt| - (c - |tt|))]
          linarith [abs_nonneg tt]
      _ = (sg.card : ℝ) * (2 * |tt|) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ε / 3 := by
          have hcard : (0 : ℝ) < (sg.card : ℝ) + 1 := by positivity
          have hstep : (sg.card : ℝ) * (2 * |tt|) ≤ (sg.card : ℝ) * (2 * δ) := by
            have := abs_nonneg tt
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          refine le_trans hstep ?_
          rw [hδdef]
          have hkey : (sg.card : ℝ) * (2 * (ε / (6 * ((sg.card : ℝ) + 1))))
              = ε * ((sg.card : ℝ) / (3 * ((sg.card : ℝ) + 1))) := by
            field_simp
            ring
          rw [hkey]
          have hfrac : (sg.card : ℝ) / (3 * ((sg.card : ℝ) + 1)) ≤ 1 / 3 := by
            rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 3 * ((sg.card : ℝ) + 1))
              (by norm_num : (0 : ℝ) < 3)]
            linarith
          nlinarith [hε.le]
  have hgc : unitMeas.real (⇑g ⁻¹' bbᶜ) = unitMeas.real bbᶜ :=
    IET.unitMeas_real_preimage g hbbmeas.compl
  calc unitMeas.real (wordSupp ⁅genY⁻¹, (genX ^ qq)⁻¹⁆ f g)
      ≤ unitMeas.real (bbᶜ ∪ U ∪ (⇑g ⁻¹' bbᶜ)) := unitMeas_real_mono hsupp
    _ ≤ unitMeas.real (bbᶜ ∪ U) + unitMeas.real (⇑g ⁻¹' bbᶜ) := unitMeas_real_union_le _ _
    _ ≤ (unitMeas.real bbᶜ + unitMeas.real U) + unitMeas.real (⇑g ⁻¹' bbᶜ) := by
        have := unitMeas_real_union_le bbᶜ U
        linarith
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        rw [hgc]
        linarith
    _ = ε := by ring

/-- **Lemma 2.9** (display (2.2)).  Get a continuous function `ψ ≥ 1_S` with `∫ ψ ≤ Leb S + ε/2`
from the closure-plus-Urysohn route (no re-presentation of `S` by disjoint pieces is needed: the
open set comes from outer regularity applied to the closure, whose measure is that of `S` because
`S` is a finite union of half-open intervals), then apply unique ergodicity of `f` to `ψ`. -/
theorem exists_uniform_birkhoff (f : IET 0 1) (hue : UniqueErgodic f) (S : Set ℝ)
    (hS : IsFiniteUnionIntervals S) (ε : ℝ) (hε : 0 < ε) (hvol : unitMeas.real S ≤ ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Set.Ico (0 : ℝ) 1,
      (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, S.indicator (fun _ => (1 : ℝ)) ((f ^ i) x) ≤ 2 * ε := by
  classical
  -- `S` is given as a finite union of half-open intervals
  obtain ⟨P, hP⟩ := hS
  have hS_eq : S = ⋃ p ∈ P, Set.Ico p.1 p.2 := by
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    exact hP x
  have hSmeas : MeasurableSet S := by
    rw [hS_eq]
    exact Finset.measurableSet_biUnion _ (fun p _ => measurableSet_Ico)
  -- only the part of `S` inside `[0, 1)` matters
  set T : Set ℝ := S ∩ Set.Ico (0 : ℝ) 1 with hT
  have hunitS : unitMeas.real S = volume.real T := by
    rw [hT, unitMeas, Measure.real, Measure.real, Measure.restrict_apply hSmeas,
      Set.inter_comm S]
  have hTsub : T ⊆ Set.Ico (0 : ℝ) 1 := Set.inter_subset_right
  have hT_eq : T = ⋃ p ∈ P, Set.Ico (max p.1 0) (min p.2 1) := by
    rw [hT, hS_eq]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop, Set.mem_Ico]
    constructor
    · rintro ⟨⟨p, hp, hxp⟩, h0, h1⟩
      exact ⟨p, hp, max_le hxp.1 h0, lt_min hxp.2 h1⟩
    · rintro ⟨p, hp, hmax, hmin⟩
      exact ⟨⟨p, hp, ⟨le_trans (le_max_left _ _) hmax, lt_of_lt_of_le hmin (min_le_left _ _)⟩⟩,
        le_trans (le_max_right _ _) hmax, lt_of_lt_of_le hmin (min_le_right _ _)⟩
  -- the closed over-approximation `⋃ [max a 0, min b 1]` of `T`
  have hclosed : IsClosed (⋃ p ∈ P, Set.Icc (max p.1 0) (min p.2 1)) := by
    have h : IsClosed (⋃ p : {p : ℝ × ℝ // p ∈ P}, Set.Icc (max (p.1).1 0) (min (p.1).2 1)) :=
      isClosed_iUnion_of_finite (fun p => isClosed_Icc)
    have heq : (⋃ p ∈ P, Set.Icc (max p.1 0) (min p.2 1))
        = ⋃ p : {p : ℝ × ℝ // p ∈ P}, Set.Icc (max (p.1).1 0) (min (p.1).2 1) := by
      ext x
      simp only [Set.mem_iUnion, Subtype.exists, exists_prop]
    rw [heq]
    exact h
  have hcl_sub : closure T ⊆ ⋃ p ∈ P, Set.Icc (max p.1 0) (min p.2 1) := by
    rw [IsClosed.closure_subset_iff hclosed]
    intro x hx
    rw [hT_eq] at hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨p, hp, ⟨hxp.1, le_of_lt hxp.2⟩⟩
  -- `closure T \ T` consists of right endpoints, hence is null
  have hdiff : closure T \ T ⊆ ⋃ p ∈ P, ({min p.2 1} : Set ℝ) := by
    rintro x ⟨hxcl, hxT⟩
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hcl_sub hxcl)
    have hxa : max p.1 0 ≤ x := hxp.1
    have hxb : x ≤ min p.2 1 := hxp.2
    have hne : x = min p.2 1 := by
      by_contra hne'
      have hlt : x < min p.2 1 := lt_of_le_of_ne hxb hne'
      refine hxT ?_
      rw [hT_eq]
      exact Set.mem_iUnion₂.mpr ⟨p, hp, ⟨hxa, hlt⟩⟩
    exact Set.mem_iUnion₂.mpr ⟨p, hp, by simp [hne]⟩
  have hcl_le : volume (closure T) ≤ volume T := by
    have h1 : closure T ⊆ T ∪ ⋃ p ∈ P, ({min p.2 1} : Set ℝ) := by
      intro x hx
      by_cases h : x ∈ T
      · exact Or.inl h
      · exact Or.inr (hdiff ⟨hx, h⟩)
    have h3 : volume (⋃ p ∈ P, ({min p.2 1} : Set ℝ)) = 0 := by
      refine le_bot_iff.mp (le_trans (measure_biUnion_finset_le P (fun p => ({min p.2 1} : Set ℝ)))
        ?_)
      simp
    calc volume (closure T) ≤ volume (T ∪ ⋃ p ∈ P, ({min p.2 1} : Set ℝ)) := measure_mono h1
      _ ≤ volume T + volume (⋃ p ∈ P, ({min p.2 1} : Set ℝ)) := measure_union_le _ _
      _ = volume T := by rw [h3, add_zero]
  have hTfin : volume T ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hTsub)
    rw [Real.volume_Ico]
    norm_num
  have hcl_fin : volume (closure T) ≠ ⊤ := ne_top_of_le_ne_top hTfin hcl_le
  -- an open set above the closure, of almost the same measure
  have hcl_meas : MeasurableSet (closure T) := isClosed_closure.measurableSet
  obtain ⟨U, hTU, hUopen, hUfin, hUdiff⟩ :=
    hcl_meas.exists_isOpen_sdiff_lt hcl_fin
      (ε := ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  -- Urysohn: a continuous function that is `1` on `closure T` and `0` off `U`
  obtain ⟨ψ, hψ0, hψ1, hψrange⟩ :=
    exists_continuous_zero_one_of_isClosed hUopen.isClosed_compl isClosed_closure
      (Set.disjoint_left.mpr (fun x hx hx' => hx (hTU hx')))
  have hψcont : Continuous (⇑ψ) := ψ.continuous
  have hψ_ge : ∀ x ∈ T, (1 : ℝ) ≤ ψ x := by
    intro x hx
    have h := hψ1 (subset_closure hx)
    simp only [Pi.one_apply] at h
    rw [h]
  have hψ_nonneg : ∀ x, 0 ≤ ψ x := fun x => (hψrange x).1
  have hψ_01 : ∀ x, ψ x ≤ 1 := fun x => (hψrange x).2
  have hψ_le_ind : ∀ x, ψ x ≤ U.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx]; exact hψ_01 x
    · have h0 := hψ0 (by simpa using hx)
      simp only [Pi.zero_apply] at h0
      rw [Set.indicator_of_notMem hx, h0]
  -- the integral of `ψ` is at most `ε + ε/2`
  have hInt : ∫ y, ψ y ∂unitMeas ≤ unitMeas.real S + ε / 2 := by
    have hψ_int : Integrable (⇑ψ) unitMeas := by
      refine Integrable.of_bound hψcont.aestronglyMeasurable 1 ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hψ_nonneg x], hψ_01 x⟩
    have hind_int : Integrable (fun x => U.indicator (fun _ => (1 : ℝ)) x) unitMeas :=
      Integrable.indicator (integrable_const 1) hUmeas
    have h1 : ∫ y, ψ y ∂unitMeas ≤ ∫ y, U.indicator (fun _ => (1 : ℝ)) y ∂unitMeas :=
      integral_mono hψ_int hind_int hψ_le_ind
    have h2 : ∫ y, U.indicator (fun _ => (1 : ℝ)) y ∂unitMeas = unitMeas.real U :=
      integral_indicator_one hUmeas
    have h3 : unitMeas.real U ≤ volume.real U := by
      rw [unitMeas, Measure.real, Measure.real, Measure.restrict_apply hUmeas]
      exact ENNReal.toReal_mono hUfin.ne (measure_mono Set.inter_subset_left)
    have h4 : volume.real U ≤ volume.real (closure T) + ε / 2 := by
      have hun : closure T ∪ (U \ closure T) = U := by
        ext x
        simp only [Set.mem_union, Set.mem_sdiff]
        constructor
        · rintro (h | ⟨h, -⟩)
          · exact hTU h
          · exact h
        · intro h
          by_cases hc : x ∈ closure T
          · exact Or.inl hc
          · exact Or.inr ⟨h, hc⟩
      have hle : volume U ≤ volume (closure T) + volume (U \ closure T) := by
        have h := measure_union_le (μ := volume) (closure T) (U \ closure T)
        rwa [hun] at h
      have hfin2 : volume (U \ closure T) ≠ ⊤ :=
        ne_top_of_le_ne_top hUfin.ne (measure_mono Set.sdiff_subset)
      have hsmall : (volume (U \ closure T)).toReal ≤ ε / 2 := by
        have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (le_of_lt hUdiff)
        rwa [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ ε / 2)] at h
      calc volume.real U ≤ (volume (closure T) + volume (U \ closure T)).toReal := by
            rw [Measure.real]; exact ENNReal.toReal_mono (by simp [hcl_fin, hfin2]) hle
        _ = volume.real (closure T) + (volume (U \ closure T)).toReal :=
            ENNReal.toReal_add hcl_fin hfin2
        _ ≤ volume.real (closure T) + ε / 2 := by linarith
    have h5 : volume.real (closure T) ≤ volume.real T := by
      rw [Measure.real, Measure.real]
      exact ENNReal.toReal_mono hTfin hcl_le
    have h6 : volume.real T = unitMeas.real S := hunitS.symm
    linarith
  -- unique ergodicity of `f` for the continuous test function `ψ`
  obtain ⟨N, hNpos, hN⟩ := hue (⇑ψ) hψcont (ε / 2) (by linarith)
  refine ⟨N, hNpos, fun x hx => ?_⟩
  have hbirk := hN N le_rfl x hx
  have h2 : (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, ψ ((f ^ i) x) ≤ 2 * ε := by
    have h3 : (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, ψ ((f ^ i) x) - ∫ y, ψ y ∂unitMeas ≤ ε / 2 :=
      (abs_le.mp hbirk).2
    linarith
  -- pointwise comparison of the two Birkhoff sums
  have hfmap : ∀ y ∈ Set.Ico (0 : ℝ) 1, f y ∈ Set.Ico (0 : ℝ) 1 :=
    fun y hy => f.isIET.mapsTo hy
  have hpow : ∀ i : ℕ, (f ^ i) x ∈ Set.Ico (0 : ℝ) 1 := by
    intro i
    induction i with
    | zero => simpa using hx
    | succ k ih => rw [pow_succ']; exact hfmap _ ih
  have hsum : ∑ i ∈ Finset.range N, S.indicator (fun _ => (1 : ℝ)) ((f ^ i) x)
      ≤ ∑ i ∈ Finset.range N, ψ ((f ^ i) x) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hmem := hpow i
    by_cases h : (f ^ i) x ∈ S
    · rw [Set.indicator_of_mem h]
      exact hψ_ge _ ⟨h, hmem⟩
    · rw [Set.indicator_of_notMem h]
      exact hψ_nonneg _
  have h4 : (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, S.indicator (fun _ => (1 : ℝ)) ((f ^ i) x)
      ≤ (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, ψ ((f ^ i) x) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  linarith


/-! ## Lemma 2.10: one commutator step -/

/-- The evaluation of a commutator of words. -/
theorem evalWord_commutatorElement (u₁ u₂ : FreeGroup Gen) (f g : IET 0 1) :
    evalWord ⁅u₁, u₂⁆ f g = ⁅evalWord u₁ f g, evalWord u₂ f g⁆ := by
  simp only [commutatorElement_def, evalWord, map_mul, map_inv]

/-- **Lemma 2.10**: one commutator step.  (`hε` and `hsmall` belong to the standing assumptions
of the
section, where they are used to start the iteration; this step itself does not need them.) -/
theorem iterate_word (f g : IET 0 1) (ε : ℝ) (_hε : 0 < ε) (N : ℕ) (hN : 0 < N)
    (w₀ : FreeGroup Gen) (hw₀ : w₀ ≠ 1) (_hsmall : unitMeas.real (wordSupp w₀ f g) ≤ ε)
    (hbirk : ∀ x ∈ Set.Ico (0 : ℝ) 1, (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N,
      (wordSupp w₀ f g).indicator (fun _ => (1 : ℝ)) ((f ^ i) x) ≤ 2 * ε)
    (w : FreeGroup Gen) (hw : w ≠ 1) :
    ∃ w' : FreeGroup Gen, w' ≠ 1 ∧
      wordLength w' ≤ 2 * wordLength w + 4 * N + 2 * wordLength w₀ ∧
        unitMeas.real (wordSupp w' f g) ≤ 18 * ε * unitMeas.real (wordSupp w f g) := by
  classical
  set S : Set ℝ := wordSupp w f g with hS
  set S₀ : Set ℝ := wordSupp w₀ f g with hS₀
  have hSmeas : MeasurableSet S := measurableSet_wordSupp w f g
  have hS₀meas : MeasurableSet S₀ := measurableSet_wordSupp w₀ f g
  -- the index `i` of display (2.3)
  obtain ⟨i, hiN, hib⟩ := exists_small_intersection f g hSmeas hS₀meas hN hbirk
  -- the conjugate `x^{-i} w₀ x^i` and its support
  set v : FreeGroup Gen := (genX ^ i)⁻¹ * w₀ * (genX ^ i) with hv
  have hvne : v ≠ 1 := conj_ne_one hw₀ _
  have hvSupp : {x : ℝ | (evalWord v f g) x ≠ x} = ⇑(f ^ i) ⁻¹' S₀ := by
    rw [hv]
    exact wordSupp_conj_pow w₀ i f g
  have hvlen : wordLength v ≤ wordLength w₀ + 2 * i := by
    rw [hv]; exact wordLength_conj_pow_le w₀ i
  -- supports of the two conjugates of `w`
  have hwX : {x : ℝ | (evalWord (genX⁻¹ * w * genX) f g) x ≠ x} = ⇑f ⁻¹' S := by
    rw [evalWord_conjX]
    exact supp_conj f (evalWord w f g)
  have hwY : {x : ℝ | (evalWord (genY⁻¹ * w * genY) f g) x ≠ x} = ⇑g ⁻¹' S := by
    rw [evalWord_conjY]
    exact supp_conj g (evalWord w f g)
  -- the common measure estimate
  have key : ∀ (φ ψ : IET 0 1) (T : Set ℝ), {x : ℝ | φ x ≠ x} = T →
      {x : ℝ | ψ x ≠ x} = ⇑(f ^ i) ⁻¹' S₀ →
      unitMeas.real (T ∩ ⇑(f ^ i) ⁻¹' S₀) ≤ 6 * ε * unitMeas.real S →
      unitMeas.real {x : ℝ | (⁅φ⁻¹, ψ⁻¹⁆) x ≠ x} ≤ 18 * ε * unitMeas.real S := by
    intro φ ψ T hφ hψ hT
    have h1 := unitMeas_real_supp_commutator_inv_le φ ψ
    rw [hφ, hψ] at h1
    linarith
  have hwS : {x : ℝ | (evalWord w f g) x ≠ x} = S := by rw [hS]; rfl
  have hnn1 : 0 ≤ unitMeas.real (S ∩ ⇑(f ^ i) ⁻¹' S₀) := unitMeas_real_nonneg _
  have hnn2 : 0 ≤ unitMeas.real (⇑f ⁻¹' S ∩ ⇑(f ^ i) ⁻¹' S₀) := unitMeas_real_nonneg _
  have hnn3 : 0 ≤ unitMeas.real (⇑g ⁻¹' S ∩ ⇑(f ^ i) ⁻¹' S₀) := unitMeas_real_nonneg _
  -- Lemma 2.7 gives one of the three words
  -- Lemma 2.7 gives one of the three commutators, and the step uses `[·, v] = ⁅·⁻¹, v⁻¹⁆`
  rcases exists_nontrivial_commutator w v hw hvne with h1 | h2 | h3
  · refine ⟨⁅w⁻¹, v⁻¹⁆,
      fun hc => h1 ((commutatorElement_inv_inv_eq_one_iff w v).mp hc), ?_, ?_⟩
    · have h := wordLength_commutatorElement_le w⁻¹ v⁻¹
      rw [wordLength_inv, wordLength_inv] at h
      omega
    · rw [wordSupp, evalWord_commutatorElement, evalWord_inv, evalWord_inv]
      exact key _ _ S hwS hvSupp (by linarith)
  · refine ⟨⁅(genX⁻¹ * w * genX)⁻¹, v⁻¹⁆,
      fun hc => h2 ((commutatorElement_inv_inv_eq_one_iff (genX⁻¹ * w * genX) v).mp hc), ?_, ?_⟩
    · have h := wordLength_commutatorElement_le (genX⁻¹ * w * genX)⁻¹ v⁻¹
      rw [wordLength_inv, wordLength_inv] at h
      have hc := wordLength_conj_le w
      omega
    · rw [wordSupp, evalWord_commutatorElement, evalWord_inv, evalWord_inv]
      exact key _ _ (⇑f ⁻¹' S) hwX hvSupp (by linarith)
  · refine ⟨⁅(genY⁻¹ * w * genY)⁻¹, v⁻¹⁆,
      fun hc => h3 ((commutatorElement_inv_inv_eq_one_iff (genY⁻¹ * w * genY) v).mp hc), ?_, ?_⟩
    · have h := wordLength_commutatorElement_le (genY⁻¹ * w * genY)⁻¹ v⁻¹
      rw [wordLength_inv, wordLength_inv] at h
      have hc := wordLength_conj_le_of genY wordLength_genY w
      omega
    · rw [wordSupp, evalWord_commutatorElement, evalWord_inv, evalWord_inv]
      exact key _ _ (⇑g ⁻¹' S) hwY hvSupp (by linarith)

/-- **Theorem 2.6** (the irreducible case): if `f` is uniquely ergodic and rigid by translations,
and `(lam, mu)` is Diophantine, then some nontrivial word evaluates to the identity.

Proof: pick `ε` with `18 * ε * 2 ^ c < 1` and, by Lemma 2.8, a nontrivial `w₀` whose support has
measure at most `ε`; Lemma 2.9 then gives `N` with the uniform Birkhoff estimate for that support.
Lemma 2.10 produces a sequence `W n` of nontrivial words with `|W n| + K ≤ 2 ^ n * (|w₀| + K)` and
support measure at most `ε * (18 * ε) ^ n`, where `K = 4 * N + 2 * |w₀|`.  If no `W n` evaluated to
the identity, `exists_lattice_cell` would give, for every `n`, a nonzero lattice combination `ℓ` of
the two length vectors with coefficients at most `2 * |W n| + 2` in absolute value and
`0 < ℓ ≤ ε * (18 * ε) ^ n`; the Diophantine condition bounds `ℓ` below by `C / (2|W n| + 2) ^ c`,
while `2 * |W n| + 2 ≤ 2 ^ (n+1) * M₀` makes the upper bound decay geometrically like
`(18 * ε * 2 ^ c) ^ n`, so the two are incompatible for large `n`. -/
theorem irreducible_case {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) (lam : Fin d → ℝ≥0) (mu : Fin e → ℝ≥0)
    (hlam : lam ∈ simplex d) (hmu : mu ∈ simplex e)
    (hue : UniqueErgodic (mkIET1 lam π hlam)) (hrig : IsRigidByTranslations (mkIET1 lam π hlam))
    (hdio : IsDiophantine lam mu) :
    ∃ w : FreeGroup Gen, w ≠ 1 ∧ evalWord w (mkIET1 lam π hlam) (mkIET1 mu σ hmu) = 1 := by
  classical
  obtain ⟨C, hCpos, cexp, hcexp, hdio'⟩ := hdio
  -- the two exchanges and their total lengths
  have hl : (∑ i, lam i) = 1 := hlam
  have hm : (∑ j, mu j) = 1 := hmu
  -- the small parameter
  set ε : ℝ := 1 / (4 * 18 * (2:ℝ) ^ cexp) with hεdef
  have h2c : (0:ℝ) < (2:ℝ) ^ cexp := Real.rpow_pos_of_pos (by norm_num) _
  have hε : 0 < ε := by
    rw [hεdef]; positivity
  have hερ : 18 * ε * (2:ℝ) ^ cexp < 1 := by
    rw [hεdef]
    have h : (0:ℝ) < 4 * 18 * (2:ℝ) ^ cexp := by positivity
    have h2cne : (2:ℝ) ^ cexp ≠ 0 := ne_of_gt h2c
    field_simp
    norm_num
  -- Lemma 2.8: a word with small support
  obtain ⟨w₀, hw₀, hsmall⟩ := exists_word_small_support (mkIET1 lam π hlam)
    (mkIET1 mu σ hmu) hrig ε hε
  -- Lemma 2.9: the uniform Birkhoff estimate for its support
  obtain ⟨N, hN, hbirk⟩ := exists_uniform_birkhoff (mkIET1 lam π hlam) hue
    (wordSupp w₀ (mkIET1 lam π hlam) (mkIET1 mu σ hmu))
    (isFiniteUnionIntervals_wordSupp lam π mu σ hl hm w₀) ε hε hsmall
  -- the one-step map
  set K : ℕ := 4 * N + 2 * wordLength w₀ with hKdef
  let next : FreeGroup Gen → FreeGroup Gen := fun w =>
    if h : w ≠ 1 then
      (iterate_word (mkIET1 lam π hlam) (mkIET1 mu σ hmu) ε hε N hN w₀ hw₀ hsmall hbirk w h).choose
    else w₀
  have next_spec : ∀ w : FreeGroup Gen, w ≠ 1 →
      next w ≠ 1 ∧ wordLength (next w) ≤ 2 * wordLength w + K ∧
        unitMeas.real (wordSupp (next w) (mkIET1 lam π hlam) (mkIET1 mu σ hmu))
          ≤ 18 * ε * unitMeas.real (wordSupp w (mkIET1 lam π hlam) (mkIET1 mu σ hmu)) := by
    intro w hw
    have hmain := (iterate_word (mkIET1 lam π hlam) (mkIET1 mu σ hmu) ε hε N hN w₀ hw₀ hsmall
      hbirk w hw).choose_spec
    rw [show next w = (iterate_word (mkIET1 lam π hlam) (mkIET1 mu σ hmu) ε hε N hN w₀ hw₀
      hsmall hbirk w hw).choose from dif_pos hw]
    refine ⟨hmain.1, ?_, hmain.2.2⟩
    rw [hKdef]
    omega
  -- the sequence of words
  let W : ℕ → FreeGroup Gen := fun n => next^[n] w₀
  have hW0 : W 0 = w₀ := rfl
  have hWsucc : ∀ n, W (n + 1) = next (W n) := fun n => Function.iterate_succ_apply' next n w₀
  have hWne : ∀ n, W n ≠ 1 := by
    intro n
    induction n with
    | zero => rw [hW0]; exact hw₀
    | succ m ih => rw [hWsucc]; exact (next_spec (W m) ih).1
  have hWlen : ∀ n, wordLength (W n) + K ≤ 2 ^ n * (wordLength w₀ + K) := by
    intro n
    induction n with
    | zero => rw [hW0]; simp
    | succ m ih =>
      have h1 : wordLength (W (m+1)) ≤ 2 * wordLength (W m) + K := by
        rw [hWsucc]; exact (next_spec (W m) (hWne m)).2.1
      have h2 : wordLength (W (m+1)) + K ≤ 2 * wordLength (W m) + K + K := by omega
      have h3 : 2 * wordLength (W m) + K + K = 2 * (wordLength (W m) + K) := by omega
      calc wordLength (W (m+1)) + K ≤ 2 * (wordLength (W m) + K) := by omega
        _ ≤ 2 * (2 ^ m * (wordLength w₀ + K)) := by omega
        _ = 2 ^ (m+1) * (wordLength w₀ + K) := by ring
  have hWsupp : ∀ n, unitMeas.real (wordSupp (W n) (mkIET1 lam π hlam) (mkIET1 mu σ hmu))
      ≤ ε * (18 * ε) ^ n := by
    intro n
    induction n with
    | zero => rw [hW0]; simpa using hsmall
    | succ m ih =>
      have h1 := (next_spec (W m) (hWne m)).2.2
      calc unitMeas.real (wordSupp (W (m+1)) (mkIET1 lam π hlam) (mkIET1 mu σ hmu))
          ≤ 18 * ε * unitMeas.real (wordSupp (W m) (mkIET1 lam π hlam) (mkIET1 mu σ hmu)) := by
            rw [hWsucc]; exact h1
        _ ≤ 18 * ε * (ε * (18 * ε) ^ m) := by
            have h2 : 0 ≤ 18 * ε := by positivity
            exact mul_le_mul_of_nonneg_left ih h2
        _ = ε * (18 * ε) ^ (m+1) := by ring
  -- the geometric decay of the lower bound
  set M₀ : ℝ := (wordLength w₀ : ℝ) + (K : ℝ) + 1 with hM₀def
  have hM₀pos : 0 < M₀ := by rw [hM₀def]; positivity
  have hden : ∀ n, 2 * (wordLength (W n) : ℝ) + 2 ≤ 2 ^ (n+1) * M₀ := by
    intro n
    have h1 : (wordLength (W n) : ℝ) + (K : ℝ) ≤ (2:ℝ) ^ n * ((wordLength w₀ : ℝ) + (K : ℝ)) := by
      have h := hWlen n
      have h' : ((wordLength (W n) + K : ℕ) : ℝ)
          ≤ ((2 ^ n * (wordLength w₀ + K) : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      simpa using h'
    have h2 : (1:ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have h3 : (2:ℝ) ^ (n+1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    rw [h3, hM₀def]
    nlinarith [h1, h2]
  -- assume for contradiction that no `W n` is trivial as an exchange
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  -- the geometric rate of the bound
  set ρ : ℝ := 18 * ε * (2:ℝ) ^ cexp with hρdef
  -- pick `n` so that the decay beats the Diophantine constant
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (x := C / (ε * M₀ ^ cexp * (2:ℝ) ^ cexp)) (by positivity) hερ
  -- the exchange `(2:ℝ) ^ (n+1)` as a power of `(2:ℝ) ^ cexp`
  have hkey : (((2:ℝ) ^ (n+1) : ℝ) ^ cexp) = ((2:ℝ) ^ cexp) ^ (n+1) := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) (n+1) cexp,
      ← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2) cexp (n+1), mul_comm]
  -- the upper bound at this `n`
  have hpow : (2 * (wordLength (W n) : ℝ) + 2) ^ cexp
      ≤ ((2:ℝ) ^ cexp) ^ (n+1) * M₀ ^ cexp := by
    have h2 : (2 * (wordLength (W n) : ℝ) + 2) ^ cexp
        ≤ ((2:ℝ) ^ (n+1) * M₀) ^ cexp :=
      Real.rpow_le_rpow (by positivity) (hden n) (le_of_lt hcexp)
    rwa [Real.mul_rpow (by positivity) (le_of_lt hM₀pos), hkey] at h2
  have hn2 : ε * (18 * ε) ^ n * (2 * (wordLength (W n) : ℝ) + 2) ^ cexp < C := by
    have h2 : ε * (18 * ε) ^ n * (2 * (wordLength (W n) : ℝ) + 2) ^ cexp
        ≤ ε * (18 * ε) ^ n * (((2:ℝ) ^ cexp) ^ (n+1) * M₀ ^ cexp) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have h3 : ε * (18 * ε) ^ n * (((2:ℝ) ^ cexp) ^ (n+1) * M₀ ^ cexp)
        = (ε * M₀ ^ cexp * (2:ℝ) ^ cexp) * ρ ^ n := by
      rw [hρdef, mul_pow (18 * ε) ((2:ℝ) ^ cexp) n, pow_succ ((2:ℝ) ^ cexp) n]
      ring
    have h4 : (ε * M₀ ^ cexp * (2:ℝ) ^ cexp) * ρ ^ n < C := by
      have hdpos : (0:ℝ) < ε * M₀ ^ cexp * (2:ℝ) ^ cexp := by positivity
      have h5 := mul_lt_mul_of_pos_left hn hdpos
      rwa [mul_div_cancel₀ _ (ne_of_gt hdpos)] at h5
    calc ε * (18 * ε) ^ n * (2 * (wordLength (W n) : ℝ) + 2) ^ cexp
        ≤ ε * (18 * ε) ^ n * (((2:ℝ) ^ cexp) ^ (n+1) * M₀ ^ cexp) := h2
      _ = (ε * M₀ ^ cexp * (2:ℝ) ^ cexp) * ρ ^ n := h3
      _ < C := h4
  -- the lattice cell attached to `W n`
  obtain ⟨a, b, ha, hb, hpos, hle⟩ :=
    exists_lattice_cell lam π mu σ hl hm (W n) (hcon (W n) (hWne n))
  set T : ℕ := max (coeffMax a) (coeffMax b) with hTdef
  -- the coefficients are bounded by `2 |W n| + 2`
  have hTa : coeffMax a ≤ 2 * wordLength (W n) + 2 := by
    rw [coeffMax]
    refine Finset.sup_le fun i _ => ?_
    have h3 : ((a i).natAbs : ℤ) ≤ ((2 * wordLength (W n) + 2 : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      have h := ha i
      push_cast
      exact h
    exact_mod_cast h3
  have hTb : coeffMax b ≤ 2 * wordLength (W n) + 2 := by
    rw [coeffMax]
    refine Finset.sup_le fun j _ => ?_
    have h3 : ((b j).natAbs : ℤ) ≤ ((2 * wordLength (W n) + 2 : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      have h := hb j
      push_cast
      exact h
    exact_mod_cast h3
  have hTle : T ≤ 2 * wordLength (W n) + 2 := by
    rw [hTdef]
    exact max_le hTa hTb
  -- the combination is nonzero, so some coefficient is
  have hT1 : 1 ≤ T := by
    rw [Nat.one_le_iff_ne_zero]
    intro hT0
    apply hpos.ne'
    have hmax : max (coeffMax a) (coeffMax b) = 0 := by rw [← hTdef]; exact hT0
    have ha0 : Finset.univ.sup (fun i => (a i).natAbs) = 0 := by
      have h1 : coeffMax a ≤ 0 := hmax ▸ le_max_left _ _
      rw [coeffMax] at h1
      exact le_antisymm h1 (Nat.zero_le _)
    have hb0 : Finset.univ.sup (fun j => (b j).natAbs) = 0 := by
      have h1 : coeffMax b ≤ 0 := hmax ▸ le_max_right _ _
      rw [coeffMax] at h1
      exact le_antisymm h1 (Nat.zero_le _)
    have haz : ∀ i, a i = 0 := by
      intro i
      have hle' := Finset.le_sup (f := fun i => (a i).natAbs) (Finset.mem_univ i)
      rw [ha0] at hle'
      exact Int.natAbs_eq_zero.mp (Nat.le_zero.mp hle')
    have hbz : ∀ j, b j = 0 := by
      intro j
      have hle' := Finset.le_sup (f := fun j => (b j).natAbs) (Finset.mem_univ j)
      rw [hb0] at hle'
      exact Int.natAbs_eq_zero.mp (Nat.le_zero.mp hle')
    simp only [haz, hbz, Int.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]
  have hTpos : (0:ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT1
  -- the Diophantine lower bound
  have hC_le : C ≤ ((∑ i, (a i : ℝ) * (lam i : ℝ)) + (∑ j, (b j : ℝ) * (mu j : ℝ)))
      * (T : ℝ) ^ cexp := by
    have hd := hdio' a b hpos.ne'
    have hmax : max (coeffMax a) (coeffMax b) = T := hTdef.symm
    rw [hmax, abs_of_pos hpos] at hd
    have hTp : (0:ℝ) < (T:ℝ) ^ cexp := Real.rpow_pos_of_pos hTpos _
    calc C = C / (T:ℝ) ^ cexp * (T:ℝ) ^ cexp := (div_mul_cancel₀ C (ne_of_gt hTp)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hd (le_of_lt hTp)
  -- and the comparison with the support
  have hstep : ((∑ i, (a i : ℝ) * (lam i : ℝ)) + (∑ j, (b j : ℝ) * (mu j : ℝ)))
        * (T : ℝ) ^ cexp
      ≤ unitMeas.real (wordSupp (W n) (mkIET1 lam π hlam) (mkIET1 mu σ hmu))
        * (2 * (wordLength (W n) : ℝ) + 2) ^ cexp := by
    have hTb' : (T:ℝ) ^ cexp ≤ (2 * (wordLength (W n) : ℝ) + 2) ^ cexp := by
      refine Real.rpow_le_rpow (by positivity) ?_ (le_of_lt hcexp)
      exact_mod_cast hTle
    have hTp : (0:ℝ) < (T:ℝ) ^ cexp := Real.rpow_pos_of_pos hTpos _
    exact mul_le_mul hle hTb' (le_of_lt hTp) (unitMeas_real_nonneg _)
  -- contradiction
  have hupper : C ≤ ε * (18 * ε) ^ n * (2 * (wordLength (W n) : ℝ) + 2) ^ cexp := by
    have hsupp := hWsupp n
    have hnn : (0:ℝ) ≤ (2 * (wordLength (W n) : ℝ) + 2) ^ cexp := by positivity
    calc C ≤ ((∑ i, (a i : ℝ) * (lam i : ℝ)) + (∑ j, (b j : ℝ) * (mu j : ℝ)))
          * (T : ℝ) ^ cexp := hC_le
      _ ≤ unitMeas.real (wordSupp (W n) (mkIET1 lam π hlam) (mkIET1 mu σ hmu))
          * (2 * (wordLength (W n) : ℝ) + 2) ^ cexp := hstep
      _ ≤ (ε * (18 * ε) ^ n) * (2 * (wordLength (W n) : ℝ) + 2) ^ cexp :=
          mul_le_mul_of_nonneg_right hsupp hnn
      _ = ε * (18 * ε) ^ n * (2 * (wordLength (W n) : ℝ) + 2) ^ cexp := by ring
  linarith [hn2, hupper]

/-! **Proposition 2.5** (`ae_diophantine`) is proved in `Diophantine.lean`, which this file imports;
its statement and the definitions `coeffMax`, `IsDiophantine`, `simplex` used above live there. -/
