/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.IET

/-!
Proposition 2.5 of the paper (`ae_diophantine`): almost every pair of length vectors is Diophantine.

This file is separate from `Irreducible.lean` only to keep that file to a reasonable length; it is
imported there, and it carries the Section-2 definitions (`coeffMax`, `IsDiophantine`, `simplex`)
that both files need, next to the proof that uses them.

**Provenance.** The proof was produced by the discovery run `ae-diophantine` (worker `t000002`, 926
lines, no `sorry`, checked by the run's Lean before being reported solved) and is ported here
unchanged; only the inlined copies of `coeffMax`, `IsDiophantine`, `simplex`, `simplexRegion`,
`simplexMap` and `simplexVolume` were deleted in favour of the library's.

**Route.** Working in the free coordinates `(v, w) ∈ simplexRegion (p+1) × simplexRegion (q+1)`
(where `d = p + 1`, `e = q + 1` and `simplexMap` is affine), for each integer vector
`(a, b, k)` with coefficients bounded by `N` the set where the affine form is smaller than
`(N+1)^{-(p+q+3)}` is a tube around a hyperplane; there are at most `(2N+1)^{p+q+1}` such vectors
  and
each tube has measure at most `2 (N+1)^{-(p+q+3)}`, so the total measure of the "bad" set at scale
`N` is summable in `N`.  Borel-Cantelli then gives, almost everywhere, a *uniform-in-scale*
Diophantine condition `IsDiophC … (expo p q)` with `expo p q = p + q + 3`, which implies
`IsDiophantine`.  Finally the a.e. statement is transported through the measurable parametrisation
`simplexMap (p+1) × simplexMap (q+1)` by `Measure.map_prod_map`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

/-! ## The Section-2 definitions the statement needs -/

/-- The largest absolute value of the coefficients. -/
def coeffMax {d : ℕ} (a : Fin d → ℤ) : ℕ := Finset.univ.sup fun i => (a i).natAbs

/-- Definition 2.3: the pair `(lam, μ)` is Diophantine. -/
def IsDiophantine {d e : ℕ} (lam : Fin d → ℝ≥0) (mu : Fin e → ℝ≥0) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (a : Fin d → ℤ) (b : Fin e → ℤ),
    (∑ i, (a i : ℝ) * (lam i : ℝ) + ∑ j, (b j : ℝ) * (mu j : ℝ)) ≠ 0 →
      C / ((max (coeffMax a) (coeffMax b) : ℕ) : ℝ) ^ c ≤
        |∑ i, (a i : ℝ) * (lam i : ℝ) + ∑ j, (b j : ℝ) * (mu j : ℝ)|

/-- The simplex of length vectors of total mass `1`. -/
def simplex (d : ℕ) : Set (Fin d → ℝ≥0) := {lam | ∑ i, lam i = 1}

/-- The open unit box `(0, 1)^n` in the `n` coordinates: the domain on which the tubes of the
Diophantine condition are cut. -/
def ubox (n : ℕ) : Set (Fin n → ℝ) := Set.univ.pi fun _ => Set.Ioo (0 : ℝ) 1

lemma measurableSet_ubox (n : ℕ) : MeasurableSet (ubox n) :=
  MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ioo

lemma volume_ubox (n : ℕ) : volume (ubox n) = 1 := by
  rw [ubox, Real.volume_pi_Ioo]
  simp

lemma insertNthEquiv_apply_pair {n : ℕ} {α : Fin (n + 1) → Type*} (i : Fin (n + 1))
    (x : α i) (s : (j : Fin n) → α (i.succAbove j)) :
    (Fin.insertNthEquiv α i) (x, s) = Fin.insertNth i x s := by
  funext j
  exact Fin.insertNthEquiv_apply _ i (x, s) j

lemma sum_insertNth {n : ℕ} (f : Fin (n + 1) → ℤ) (i : Fin (n + 1)) (t : ℝ) (s : Fin n → ℝ) :
    (∑ j, (f j : ℝ) * (Fin.insertNth i t s : Fin (n + 1) → ℝ) j)
      = (f i : ℝ) * t + ∑ j : Fin n, (f (i.succAbove j) : ℝ) * s j := by
  rw [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same]
  simp [Fin.insertNth_apply_succAbove]

/-- One dimensional interval estimate: if `|c| ≥ 1` then the set where `|c*t + K| < ε`
has measure at most `2ε`. -/
lemma volume_abs_lt_le {c K ε : ℝ} (hc : 1 ≤ |c|) (hε : 0 ≤ ε) :
    volume {t : ℝ | |c * t + K| < ε} ≤ ENNReal.ofReal (2 * ε) := by
  have hc0 : c ≠ 0 := by rintro rfl; norm_num at hc
  have hcpos : 0 < |c| := lt_of_lt_of_le zero_lt_one hc
  have hsub : {t : ℝ | |c * t + K| < ε} ⊆ Metric.ball (-K / c) (ε / |c|) := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : t - -K / c = (c * t + K) / c := by field_simp; ring
    rw [h1, abs_div]
    exact div_lt_div_of_pos_right ht hcpos
  calc volume {t : ℝ | |c * t + K| < ε}
      ≤ volume (Metric.ball (-K / c) (ε / |c|)) := measure_mono hsub
    _ = ENNReal.ofReal (2 * (ε / |c|)) := Real.volume_ball _ _
    _ ≤ ENNReal.ofReal (2 * ε) := by
        apply ENNReal.ofReal_le_ofReal
        have h2 : ε / |c| ≤ ε := div_le_self hε hc
        linarith

/-- Single factor estimate: the set of points of the unit box in `Fin (n+1) → ℝ` where a
nontrivial integer affine form is small has measure at most `2ε`. -/
lemma volume_ubox_affine {n : ℕ} (f : Fin (n + 1) → ℤ) (k : ℝ) (i : Fin (n + 1))
    (hi : f i ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) :
    volume (ubox (n + 1) ∩
        {x : Fin (n + 1) → ℝ | |(∑ j, (f j : ℝ) * x j) + k| < ε})
      ≤ ENNReal.ofReal (2 * ε) := by
  classical
  set S : Set (Fin (n + 1) → ℝ) :=
    ubox (n + 1) ∩ {x : Fin (n + 1) → ℝ | |(∑ j, (f j : ℝ) * x j) + k| < ε} with hS
  have hcont : Continuous fun x : Fin (n + 1) → ℝ => |(∑ j, (f j : ℝ) * x j) + (k : ℝ)| := by
    have h1 : Continuous fun x : Fin (n + 1) → ℝ => (∑ j, (f j : ℝ) * x j) :=
      continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
    exact (h1.add continuous_const).abs
  have hSmeas : MeasurableSet S :=
    MeasurableSet.inter (measurableSet_ubox _) (measurableSet_lt hcont.measurable measurable_const)
  have hi1 : (1 : ℝ) ≤ |(f i : ℝ)| := by
    have h2 : (1 : ℤ) ≤ |f i| := Int.one_le_abs hi
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by simp
      _ ≤ ((|f i| : ℤ) : ℝ) := by exact_mod_cast h2
      _ = |(f i : ℝ)| := Int.cast_abs
  set ee : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with hee
  have hpres : MeasurePreserving ee volume volume := volume_preserving_piFinSuccAbove _ i
  have key : ∀ (t : ℝ) (s : Fin n → ℝ), ((t, s) ∈ ee '' S) ↔ (ee.symm (t, s) ∈ S) := by
    intro t s
    rw [Set.mem_image]
    constructor
    · rintro ⟨x, hxS, hx⟩
      have h1 : ee.symm (t, s) = x := by
        rw [← hx]
        simp
      rwa [h1]
    · rintro h
      exact ⟨ee.symm (t, s), h, by simp⟩
  have himg : volume S = volume (ee '' S) := by
    have h := hpres.measure_preimage_equiv (ee '' S)
    rwa [Set.preimage_image_eq S ee.injective] at h
  have hfib : volume (ee '' S) = ∫⁻ s : Fin n → ℝ, volume {t : ℝ | (t, s) ∈ ee '' S} :=
    Measure.prod_apply_symm ((MeasurableEquiv.measurableSet_image ee).mpr hSmeas)
  have hslice_zero : ∀ s : Fin n → ℝ, s ∉ ubox n → volume {t : ℝ | (t, s) ∈ ee '' S} = 0 := by
    intro s hs
    have hempty : {t : ℝ | (t, s) ∈ ee '' S} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro t ht
      simp only [Set.mem_ofPred_eq] at ht
      rw [key t s, MeasurableEquiv.piFinSuccAbove_symm_apply, insertNthEquiv_apply_pair] at ht
      rw [hS] at ht
      obtain ⟨hubox, -⟩ := ht
      simp only [ubox, Set.mem_pi, Set.mem_univ, true_implies] at hubox hs
      exact hs fun j => by
        have := hubox (i.succAbove j)
        rwa [Fin.insertNth_apply_succAbove] at this
    rw [hempty, measure_empty]
  have hslice_le : ∀ s : Fin n → ℝ, volume {t : ℝ | (t, s) ∈ ee '' S} ≤ ENNReal.ofReal (2 * ε) := by
    intro s
    have hsub : {t : ℝ | (t, s) ∈ ee '' S} ⊆
        {t : ℝ | |(f i : ℝ) * t + ((∑ j : Fin n, (f (i.succAbove j) : ℝ) * s j) + k)| < ε} := by
      intro t ht
      simp only [Set.mem_ofPred_eq] at ht
      rw [key t s, MeasurableEquiv.piFinSuccAbove_symm_apply, insertNthEquiv_apply_pair] at ht
      rw [hS] at ht
      obtain ⟨-, hlt⟩ := ht
      simp only [Set.mem_ofPred_eq] at hlt
      simp only [Set.mem_ofPred_eq]
      rw [sum_insertNth f i t s] at hlt
      convert hlt using 2
      ring
    calc volume {t : ℝ | (t, s) ∈ ee '' S}
        ≤ volume {t : ℝ | |(f i : ℝ) * t + ((∑ j : Fin n, (f (i.succAbove j) : ℝ) * s j) + k)| < ε}
          := measure_mono hsub
      _ ≤ ENNReal.ofReal (2 * ε) := volume_abs_lt_le hi1 hε
  have hcongr : ∫⁻ s : Fin n → ℝ, volume {t : ℝ | (t, s) ∈ ee '' S}
      = ∫⁻ s : Fin n → ℝ,
          (ubox n).indicator (fun s => volume {t : ℝ | (t, s) ∈ ee '' S}) s := by
    apply lintegral_congr
    intro s
    by_cases hs : s ∈ ubox n
    · rw [Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs, hslice_zero s hs]
  have hbound : ∫⁻ s : Fin n → ℝ,
        (ubox n).indicator (fun s => volume {t : ℝ | (t, s) ∈ ee '' S}) s
      ≤ ENNReal.ofReal (2 * ε) := by
    rw [lintegral_indicator (measurableSet_ubox n)]
    calc ∫⁻ s in ubox n, volume {t : ℝ | (t, s) ∈ ee '' S}
        ≤ ∫⁻ _s in ubox n, ENNReal.ofReal (2 * ε) := lintegral_mono fun s => hslice_le s
      _ = ENNReal.ofReal (2 * ε) * volume (ubox n) := by
          rw [lintegral_const]
          congr 1
          rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      _ = ENNReal.ofReal (2 * ε) := by rw [volume_ubox]; simp
  calc volume S = volume (ee '' S) := himg
    _ = ∫⁻ s : Fin n → ℝ, volume {t : ℝ | (t, s) ∈ ee '' S} := hfib
    _ = ∫⁻ s : Fin n → ℝ, (ubox n).indicator
          (fun s => volume {t : ℝ | (t, s) ∈ ee '' S}) s := hcongr
    _ ≤ ENNReal.ofReal (2 * ε) := hbound

/-- Integrals of a function vanishing off `B` and bounded by `C` are at most `C * μ B`. -/
lemma lintegral_le_of_indicator {β : Type*} [MeasurableSpace β] {μ : Measure β} (B : Set β)
    (hB : MeasurableSet B) (F : β → ℝ≥0∞) (C : ℝ≥0∞) (hle : ∀ x, F x ≤ C)
    (hzero : ∀ x ∉ B, F x = 0) :
    ∫⁻ x, F x ∂μ ≤ C * μ B := by
  have h1 : ∫⁻ x, F x ∂μ = ∫⁻ x, B.indicator F x ∂μ := by
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hzero x hx]
  rw [h1, lintegral_indicator hB]
  calc ∫⁻ x in B, F x ∂μ ≤ ∫⁻ _x in B, C ∂μ := lintegral_mono fun x => hle x
    _ = C * μ B := by
        rw [lintegral_const]
        congr 1
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

/-- Two factor estimate: the set in the product of two unit boxes where a nontrivial integer
affine form is small has measure at most `2ε`. -/
lemma volume_prod_ubox_affine {p q : ℕ} (f : Fin p → ℤ) (g : Fin q → ℤ) (K : ℝ)
    (h : f ≠ 0 ∨ g ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) :
    (volume.prod volume) ((ubox p ×ˢ ubox q) ∩
        {z : (Fin p → ℝ) × (Fin q → ℝ) |
          |(∑ i, (f i : ℝ) * z.1 i) + (∑ j, (g j : ℝ) * z.2 j) + K| < ε})
      ≤ ENNReal.ofReal (2 * ε) := by
  classical
  set T : Set ((Fin p → ℝ) × (Fin q → ℝ)) :=
    (ubox p ×ˢ ubox q) ∩
      {z : (Fin p → ℝ) × (Fin q → ℝ) |
        |(∑ i, (f i : ℝ) * z.1 i) + (∑ j, (g j : ℝ) * z.2 j) + K| < ε} with hT
  have hcont : Continuous fun z : (Fin p → ℝ) × (Fin q → ℝ) =>
      |(∑ i, (f i : ℝ) * z.1 i) + (∑ j, (g j : ℝ) * z.2 j) + K| := by
    have h1 : Continuous fun z : (Fin p → ℝ) × (Fin q → ℝ) => (∑ i, (f i : ℝ) * z.1 i) :=
      continuous_finsetSum _ fun i _ =>
        continuous_const.mul ((continuous_apply i).comp continuous_fst)
    have h2 : Continuous fun z : (Fin p → ℝ) × (Fin q → ℝ) => (∑ j, (g j : ℝ) * z.2 j) :=
      continuous_finsetSum _ fun j _ =>
        continuous_const.mul ((continuous_apply j).comp continuous_snd)
    exact ((h1.add h2).add continuous_const).abs
  have hTmeas : MeasurableSet T :=
    MeasurableSet.inter (MeasurableSet.prod (measurableSet_ubox _) (measurableSet_ubox _))
      (measurableSet_lt hcont.measurable measurable_const)
  rcases h with hf | hg
  · obtain ⟨n, hp⟩ : ∃ n, p = n + 1 := by
      rcases Nat.eq_zero_or_pos p with h0 | hpos
      · subst h0
        exact absurd (funext fun i => i.elim0) hf
      · exact ⟨p - 1, by omega⟩
    subst hp
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hf
    rw [Measure.prod_apply_symm hTmeas]
    have hslice : ∀ w : Fin q → ℝ,
        volume {v : Fin (n + 1) → ℝ | (v, w) ∈ T} ≤ ENNReal.ofReal (2 * ε) := by
      intro w
      have hsub : {v : Fin (n + 1) → ℝ | (v, w) ∈ T} ⊆
          ubox (n + 1) ∩
            {v : Fin (n + 1) → ℝ |
              |(∑ i, (f i : ℝ) * v i) + (K + ∑ j, (g j : ℝ) * w j)| < ε} := by
        intro v hv
        rw [hT] at hv
        obtain ⟨hbox, hineq⟩ := hv
        refine ⟨hbox.1, ?_⟩
        simp only [Set.mem_ofPred_eq] at hineq ⊢
        convert hineq using 2
        ring
      exact (measure_mono hsub).trans (volume_ubox_affine f _ _ hi hε)
    have hzero : ∀ w : Fin q → ℝ, w ∉ ubox q → volume {v : Fin (n + 1) → ℝ | (v, w) ∈ T} = 0 := by
      intro w hw
      have hempty : {v : Fin (n + 1) → ℝ | (v, w) ∈ T} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro v hv
        rw [hT] at hv
        obtain ⟨hbox, -⟩ := hv
        exact hw hbox.2
      rw [hempty, measure_empty]
    calc ∫⁻ w : Fin q → ℝ, volume {v : Fin (n + 1) → ℝ | (v, w) ∈ T}
        ≤ ENNReal.ofReal (2 * ε) * volume (ubox q) :=
          lintegral_le_of_indicator (ubox q) (measurableSet_ubox q) _ _ hslice hzero
      _ = ENNReal.ofReal (2 * ε) := by rw [volume_ubox, mul_one]
  · obtain ⟨m, hq⟩ : ∃ m, q = m + 1 := by
      rcases Nat.eq_zero_or_pos q with h0 | hpos
      · subst h0
        exact absurd (funext fun j => j.elim0) hg
      · exact ⟨q - 1, by omega⟩
    subst hq
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hg
    rw [Measure.prod_apply hTmeas]
    have hslice : ∀ v : Fin p → ℝ,
        volume {w : Fin (m + 1) → ℝ | (v, w) ∈ T} ≤ ENNReal.ofReal (2 * ε) := by
      intro v
      have hsub : {w : Fin (m + 1) → ℝ | (v, w) ∈ T} ⊆
          ubox (m + 1) ∩
            {w : Fin (m + 1) → ℝ |
              |(∑ j, (g j : ℝ) * w j) + (K + ∑ i, (f i : ℝ) * v i)| < ε} := by
        intro w hw
        rw [hT] at hw
        obtain ⟨hbox, hineq⟩ := hw
        refine ⟨hbox.2, ?_⟩
        simp only [Set.mem_ofPred_eq] at hineq ⊢
        convert hineq using 2
        ring
      exact (measure_mono hsub).trans (volume_ubox_affine g _ _ hj hε)
    have hzero : ∀ v : Fin p → ℝ, v ∉ ubox p → volume {w : Fin (m + 1) → ℝ | (v, w) ∈ T} = 0 := by
      intro v hv
      have hempty : {w : Fin (m + 1) → ℝ | (v, w) ∈ T} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro w hw
        rw [hT] at hw
        obtain ⟨hbox, -⟩ := hw
        exact hv hbox.1
      rw [hempty, measure_empty]
    calc ∫⁻ v : Fin p → ℝ, volume {w : Fin (m + 1) → ℝ | (v, w) ∈ T}
        ≤ ENNReal.ofReal (2 * ε) * volume (ubox p) :=
          lintegral_le_of_indicator (ubox p) (measurableSet_ubox p) _ _ hslice hzero
      _ = ENNReal.ofReal (2 * ε) := by rw [volume_ubox, mul_one]

/-- The surjection `Fin (2N+1) → [-N, N]`, `z ↦ z - N`. -/
def toInt (N : ℕ) (z : Fin (2 * N + 1)) : ℤ := (z : ℤ) - N

lemma abs_toInt_le (N : ℕ) (z : Fin (2 * N + 1)) : |toInt N z| ≤ (N : ℤ) := by
  rw [toInt, abs_le]
  constructor <;> simp
  all_goals omega

lemma exists_toInt_eq (N : ℕ) {k : ℤ} (hk : |k| ≤ (N : ℤ)) : ∃ z : Fin (2 * N + 1), toInt N z = k :=
  by
  obtain ⟨h1, h2⟩ := abs_le.mp hk
  have h3 : (0 : ℤ) ≤ k + N := by omega
  have h4 : k + N ≤ 2 * N := by omega
  refine ⟨⟨(k + N).toNat, by omega⟩, ?_⟩
  rw [toInt, Int.toNat_of_nonneg h3]
  ring

/-- The exponent of polynomial decay used in the proof (any value `> p+q+2` works). -/
def expo (p q : ℕ) : ℕ := p + q + 3

/-- The finite set of integer affine forms with coefficients bounded by `N`. -/
noncomputable def formBox (p q N : ℕ) : Finset ((Fin p → ℤ) × (Fin q → ℤ) × ℤ) :=
  (Finset.univ : Finset ((Fin p → Fin (2 * N + 1)) × (Fin q → Fin (2 * N + 1)) × Fin (2 * N +
    1))).image
    (fun x => (fun i => toInt N (x.1 i), fun j => toInt N (x.2.1 j), toInt N x.2.2))

lemma formBox_card_le (p q N : ℕ) : (formBox p q N).card ≤ (2 * N + 1) ^ (p + q + 1) := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
    show p + q + 1 = (p + q) + 1 from rfl, pow_add, pow_add, pow_one, mul_assoc]

lemma mem_formBox {p q N : ℕ} {f : Fin p → ℤ} {g : Fin q → ℤ} {k : ℤ} :
    ((f, g, k) ∈ formBox p q N) ↔
      (∀ i, |f i| ≤ (N : ℤ)) ∧ (∀ j, |g j| ≤ (N : ℤ)) ∧ |k| ≤ (N : ℤ) := by
  constructor
  · intro hx
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hx
    have h1 : (fun i => toInt N (y.1 i)) = f := congrArg Prod.fst hy
    have h2 : (fun j => toInt N (y.2.1 j)) = g := congrArg (fun t => t.2.1) hy
    have h3 : toInt N y.2.2 = k := congrArg (fun t => t.2.2) hy
    refine ⟨fun i => ?_, fun j => ?_, ?_⟩
    · rw [← congrFun h1 i]
      exact abs_toInt_le N (y.1 i)
    · rw [← congrFun h2 j]
      exact abs_toInt_le N (y.2.1 j)
    · rw [← h3]
      exact abs_toInt_le N y.2.2
  · rintro ⟨h1, h2, h3⟩
    refine Finset.mem_image.mpr ⟨(fun i => Classical.choose (exists_toInt_eq N (h1 i)),
      fun j => Classical.choose (exists_toInt_eq N (h2 j)),
      Classical.choose (exists_toInt_eq N h3)), Finset.mem_univ _, ?_⟩
    simp only [Prod.mk.injEq]
    refine ⟨funext fun i => Classical.choose_spec (exists_toInt_eq N (h1 i)),
      funext fun j => Classical.choose_spec (exists_toInt_eq N (h2 j)),
      Classical.choose_spec (exists_toInt_eq N h3)⟩

/-- The tube around the zero set of an integer affine form, inside the product of unit boxes. -/
noncomputable def tube (p q N : ℕ) (x : (Fin p → ℤ) × (Fin q → ℤ) × ℤ) :
    Set ((Fin p → ℝ) × (Fin q → ℝ)) :=
  (ubox p ×ˢ ubox q) ∩
    {z : (Fin p → ℝ) × (Fin q → ℝ) |
      |(∑ i, (x.1 i : ℝ) * z.1 i) + (∑ j, (x.2.1 j : ℝ) * z.2 j) + (x.2.2 : ℝ)|
        < ((N : ℝ) + 1) ^ (-(expo p q : ℝ))}

/-- The set of "bad" points at scale `N`. -/
noncomputable def badSet (p q N : ℕ) : Set ((Fin p → ℝ) × (Fin q → ℝ)) :=
  ⋃ x ∈ (formBox p q N).filter (fun x => x.1 ≠ 0 ∨ x.2.1 ≠ 0), tube p q N x

/-- The real valued bound for the measure of `badSet`. -/
noncomputable def badBound (p q N : ℕ) : ℝ :=
  ((2 * N + 1 : ℕ) : ℝ) ^ (p + q + 1) * (2 * ((N : ℝ) + 1) ^ (-(expo p q : ℝ)))

lemma measure_badSet_le (p q N : ℕ) :
    (volume.prod volume) (badSet p q N) ≤ ENNReal.ofReal (badBound p q N) := by
  have hε : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ (-(expo p q : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hterm : ∀ x ∈ (formBox p q N).filter (fun x => x.1 ≠ 0 ∨ x.2.1 ≠ 0),
      (volume.prod volume) (tube p q N x) ≤ ENNReal.ofReal (2 * ((N : ℝ) + 1) ^ (-(expo p q : ℝ)))
        := by
    intro x hx
    rw [Finset.mem_filter] at hx
    exact volume_prod_ubox_affine x.1 x.2.1 _ hx.2 hε
  have h1 : (volume.prod volume) (badSet p q N)
      ≤ ∑ x ∈ (formBox p q N).filter (fun x => x.1 ≠ 0 ∨ x.2.1 ≠ 0),
          (volume.prod volume) (tube p q N x) :=
    measure_biUnion_finset_le _ _
  refine h1.trans ?_
  refine (Finset.sum_le_sum hterm).trans ?_
  have h2 : ∑ _x ∈ (formBox p q N).filter (fun x => x.1 ≠ 0 ∨ x.2.1 ≠ 0),
      ENNReal.ofReal (2 * ((N : ℝ) + 1) ^ (-(expo p q : ℝ)))
      = (((formBox p q N).filter (fun x => x.1 ≠ 0 ∨ x.2.1 ≠ 0)).card : ℝ≥0∞) *
          ENNReal.ofReal (2 * ((N : ℝ) + 1) ^ (-(expo p q : ℝ))) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (((formBox p q N).filter (fun x => x.1 ≠ 0 ∨ x.2.1 ≠ 0)).card : ℝ≥0∞)
      ≤ (((2 * N + 1) ^ (p + q + 1) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast (Finset.card_filter_le (formBox p q N) _).trans (formBox_card_le p q N)
  have hstep := mul_le_mul_left hcard (ENNReal.ofReal (2 * ((N : ℝ) + 1) ^ (-(expo p q : ℝ))))
  rw [h2]
  refine hstep.trans_eq ?_
  rw [badBound, ← Nat.cast_pow, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_mul (by positivity)]

lemma badBound_nonneg (p q N : ℕ) : 0 ≤ badBound p q N := by
  unfold badBound
  positivity

/-- Summability of the measure bounds. -/
lemma summable_badBound (p q : ℕ) : Summable (badBound p q) := by
  have hbase : Summable fun N : ℕ => ((N : ℝ) + 1) ^ (-(2 : ℝ)) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) 1).mpr
      ((Real.summable_nat_rpow).mpr (by norm_num))
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hC : Summable fun N : ℕ => (2 * (3 : ℝ) ^ (p + q + 1)) * ((N : ℝ) + 1) ^ (-(2 : ℝ)) :=
    hbase.mul_left _
  refine Summable.of_nonneg_of_le (fun N => badBound_nonneg p q N) (fun N => ?_) hC
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : ((2 * N + 1 : ℕ) : ℝ) ≤ 3 * ((N : ℝ) + 1) := by
    push_cast
    linarith
  have h2 : ((2 * N + 1 : ℕ) : ℝ) ^ (p + q + 1) ≤ (3 * ((N : ℝ) + 1)) ^ (p + q + 1) :=
    pow_le_pow_left₀ (by positivity) h1 _
  have key : ((N : ℝ) + 1) ^ (p + q + 1) * ((N : ℝ) + 1) ^ (-(expo p q : ℝ))
      = ((N : ℝ) + 1) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast ((N : ℝ) + 1) (p + q + 1), ← Real.rpow_add hpos]
    congr 1
    unfold expo
    push_cast
    ring
  calc badBound p q N
      = ((2 * N + 1 : ℕ) : ℝ) ^ (p + q + 1) * (2 * ((N : ℝ) + 1) ^ (-(expo p q : ℝ))) := rfl
    _ ≤ ((3 : ℝ) ^ (p + q + 1) * ((N : ℝ) + 1) ^ (p + q + 1)) *
          (2 * ((N : ℝ) + 1) ^ (-(expo p q : ℝ))) := by
        rw [← mul_pow]
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = (2 * (3 : ℝ) ^ (p + q + 1)) *
          (((N : ℝ) + 1) ^ (p + q + 1) * ((N : ℝ) + 1) ^ (-(expo p q : ℝ))) := by ring
    _ = (2 * (3 : ℝ) ^ (p + q + 1)) * ((N : ℝ) + 1) ^ (-(2 : ℝ)) := by rw [key]

/-- Borel–Cantelli: almost every point is outside `badSet N` for all large `N`. -/
lemma ae_eventually_notMem_badSet {p q : ℕ} (R : Set (Fin p → ℝ)) (R' : Set (Fin q → ℝ)) :
    ∀ᵐ z ∂((volume.restrict R).prod (volume.restrict R')), ∀ᶠ N in atTop, z ∉ badSet p q N := by
  apply MeasureTheory.ae_eventually_notMem
  have hle : ∀ N, ((volume.restrict R).prod (volume.restrict R')) (badSet p q N)
      ≤ ENNReal.ofReal (badBound p q N) := by
    intro N
    rw [Measure.prod_restrict]
    exact (Measure.restrict_apply_le _ _).trans (measure_badSet_le p q N)
  have hsum : (∑' N, ENNReal.ofReal (badBound p q N)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun N => badBound_nonneg p q N) (summable_badBound p q)]
    exact ENNReal.ofReal_ne_top
  intro htop
  exact hsum (top_unique (htop ▸ ENNReal.tsum_le_tsum hle))

/-! ### Measurability and algebra of the simplex parametrisation -/

lemma measurable_simplexMap (d : ℕ) : Measurable (simplexMap d) := by
  rw [measurable_pi_iff]
  intro i
  by_cases h : i.val + 1 = d
  · simp only [simplexMap, dif_pos h]
    exact (measurable_const.sub (Finset.measurable_sum _ fun j _ => measurable_pi_apply
      j)).real_toNNReal
  · simp only [simplexMap, dif_neg h]
    exact (measurable_pi_apply _).real_toNNReal

lemma measurableSet_simplexRegion (d : ℕ) : MeasurableSet (simplexRegion d) := by
  have h1 : MeasurableSet {v : Fin (d - 1) → ℝ | ∀ i, 0 < v i} := by
    rw [show {v : Fin (d - 1) → ℝ | ∀ i, 0 < v i} = ⋂ i, {v : Fin (d - 1) → ℝ | 0 < v i} by
      ext v
      simp]
    exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)
  have h2 : MeasurableSet {v : Fin (d - 1) → ℝ | ∑ i, v i < 1} := by
    exact measurableSet_lt (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
      measurable_const
  exact h1.inter h2

lemma simplexRegion_subset_ubox (d : ℕ) : simplexRegion d ⊆ ubox (d - 1) := by
  intro v hv
  obtain ⟨hpos, hsum⟩ := hv
  simp only [ubox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
  intro i
  refine ⟨hpos i, ?_⟩
  have hle : v i ≤ ∑ j, v j :=
    Finset.single_le_sum (f := v) (fun j _ => le_of_lt (hpos j)) (Finset.mem_univ i)
  linarith

lemma simplexMap_castSucc {p : ℕ} (v : Fin p → ℝ) (i : Fin p) :
    simplexMap (p + 1) v i.castSucc = (v i).toNNReal := by
  simp only [simplexMap, dif_neg (by simp only [Fin.val_castSucc]; omega : ¬ ((i.castSucc).val + 1 =
    p + 1))]
  congr 2

lemma simplexMap_last {p : ℕ} (v : Fin p → ℝ) :
    simplexMap (p + 1) v (Fin.last p) = (1 - ∑ j, v j).toNNReal := by
  simp only [simplexMap, dif_pos (by simp : (Fin.last p).val + 1 = p + 1)]
  congr 2

lemma simplexMap_castSucc_coe {p : ℕ} {v : Fin p → ℝ} (hpos : ∀ i, 0 < v i) (i : Fin p) :
    ((simplexMap (p + 1) v i.castSucc : ℝ≥0) : ℝ) = v i := by
  rw [simplexMap_castSucc, Real.coe_toNNReal _ (le_of_lt (hpos i))]

lemma simplexMap_last_coe {p : ℕ} {v : Fin p → ℝ} (hsum : ∑ j, v j < 1) :
    ((simplexMap (p + 1) v (Fin.last p) : ℝ≥0) : ℝ) = 1 - ∑ j, v j := by
  rw [simplexMap_last, Real.coe_toNNReal _ (by linarith)]

/-- The key identity: an integer linear form evaluated at the simplex point is an affine form in
the free coordinates. -/
lemma sum_simplexMap_mul {p : ℕ} {v : Fin p → ℝ} (hpos : ∀ i, 0 < v i) (hsum : ∑ j, v j < 1)
    (a : Fin (p + 1) → ℤ) :
    (∑ i : Fin (p + 1), (a i : ℝ) * ((simplexMap (p + 1) v i : ℝ≥0) : ℝ))
      = (∑ i : Fin p, ((a i.castSucc - a (Fin.last p) : ℤ) : ℝ) * v i) + (a (Fin.last p) : ℝ) := by
  rw [Fin.sum_univ_castSucc, simplexMap_last_coe hsum]
  simp only [simplexMap_castSucc_coe hpos]
  have h1 : ∀ i : Fin p, ((a i.castSucc - a (Fin.last p) : ℤ) : ℝ)
      = (a i.castSucc : ℝ) - (a (Fin.last p) : ℝ) := fun i => by push_cast; ring
  simp only [h1, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-! ### The countable form of the Diophantine condition -/

/-- The countable form of the Diophantine condition: the constant is `1/(m+1)`. -/
def IsDiophC {d e : ℕ} (lam : Fin d → ℝ≥0) (mu : Fin e → ℝ≥0) (E : ℕ) : Prop :=
  ∃ m : ℕ, ∀ (a : Fin d → ℤ) (b : Fin e → ℤ),
    (∑ i, (a i : ℝ) * (lam i : ℝ) + ∑ j, (b j : ℝ) * (mu j : ℝ)) ≠ 0 →
      (1 / ((m : ℝ) + 1)) / ((max (coeffMax a) (coeffMax b) : ℕ) : ℝ) ^ (E : ℝ) ≤
        |∑ i, (a i : ℝ) * (lam i : ℝ) + ∑ j, (b j : ℝ) * (mu j : ℝ)|

lemma IsDiophC.isDiophantine {d e : ℕ} {lam : Fin d → ℝ≥0} {mu : Fin e → ℝ≥0} {E : ℕ}
    (h : IsDiophC lam mu E) (hE : 0 < E) : IsDiophantine lam mu := by
  obtain ⟨m, hm⟩ := h
  exact ⟨1 / ((m : ℝ) + 1), by positivity, (E : ℝ), by exact_mod_cast hE, hm⟩

/-- The good condition in free coordinates. -/
def GoodFree (p q : ℕ) (z : (Fin p → ℝ) × (Fin q → ℝ)) : Prop :=
  ∃ m : ℕ, ∀ (f : Fin p → ℤ) (g : Fin q → ℤ) (k : ℤ), (f ≠ 0 ∨ g ≠ 0) →
    ((∑ i, (f i : ℝ) * z.1 i) + (∑ j, (g j : ℝ) * z.2 j) + (k : ℝ)) ≠ 0 →
      (1 / ((m : ℝ) + 1)) /
        (((max (coeffMax f) (max (coeffMax g) k.natAbs) : ℕ) : ℝ) + 1) ^ (expo p q : ℝ) ≤
        |(∑ i, (f i : ℝ) * z.1 i) + (∑ j, (g j : ℝ) * z.2 j) + (k : ℝ)|

/-- From Borel–Cantelli (finitely many bad scales) inside the box, we get the good condition. -/
lemma goodFree_of_eventually {p q : ℕ} {z : (Fin p → ℝ) × (Fin q → ℝ)}
    (hz : z.1 ∈ ubox p ∧ z.2 ∈ ubox q) (hev : ∀ᶠ N in atTop, z ∉ badSet p q N) :
    GoodFree p q z := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  set N₁ := max N₀ 1 with hN₁def
  have hN₁ : ∀ N ≥ N₁, z ∉ badSet p q N := fun N hN => hN₀ N (le_trans (le_max_left _ _) hN)
  have hN₁pos : 1 ≤ N₁ := le_max_right _ _
  obtain ⟨n, hn⟩ := exists_nat_gt (((N₁ : ℝ) + 1) ^ (expo p q : ℝ))
  have hNpos : (0 : ℝ) < (N₁ : ℝ) + 1 := by positivity
  have hkey : ((N₁ : ℝ) + 1) ^ (-(expo p q : ℝ)) * ((N₁ : ℝ) + 1) ^ (expo p q : ℝ) = 1 := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hn' : ((N₁ : ℝ) + 1) ^ (expo p q : ℝ) < (n : ℝ) + 1 := by
    have : (n : ℝ) < (n : ℝ) + 1 := by linarith
    linarith
  have hC : 1 / ((n : ℝ) + 1) ≤ ((N₁ : ℝ) + 1) ^ (-(expo p q : ℝ)) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    calc (1 : ℝ) = ((N₁ : ℝ) + 1) ^ (-(expo p q : ℝ)) * ((N₁ : ℝ) + 1) ^ (expo p q : ℝ) := hkey.symm
      _ ≤ ((N₁ : ℝ) + 1) ^ (-(expo p q : ℝ)) * ((n : ℝ) + 1) := by
          exact mul_le_mul_of_nonneg_left (le_of_lt hn') (by positivity)
  refine ⟨n, fun f g k hne haff => ?_⟩
  set M := max (coeffMax f) (max (coeffMax g) k.natAbs) with hMdef
  have hcoeff : (∀ i, |f i| ≤ (M : ℤ)) ∧ (∀ j, |g j| ≤ (M : ℤ)) ∧ |k| ≤ (M : ℤ) := by
    have h1 : ∀ i, (f i).natAbs ≤ M := fun i =>
      le_trans (Finset.le_sup (f := fun i => (f i).natAbs) (Finset.mem_univ i)) (le_max_left _ _)
    have h2 : ∀ j, (g j).natAbs ≤ M := fun j =>
      le_trans (Finset.le_sup (f := fun j => (g j).natAbs) (Finset.mem_univ j))
        (le_trans (le_max_left _ _) (le_max_right _ _))
    have h3 : k.natAbs ≤ M :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    refine ⟨fun i => ?_, fun j => ?_, ?_⟩
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast h1 i
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast h2 j
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast h3
  -- membership in the box at scale `N`
  have hmem : ∀ N : ℕ, M ≤ N → ((f, g, k) ∈ (formBox p q N).filter (fun x => x.1 ≠ 0 ∨ x.2.1 ≠ 0))
    := by
    intro N hN
    refine Finset.mem_filter.mpr ⟨mem_formBox.mpr ⟨fun i => ?_, fun j => ?_, ?_⟩, hne⟩
    · exact (hcoeff.1 i).trans (by exact_mod_cast hN)
    · exact (hcoeff.2.1 j).trans (by exact_mod_cast hN)
    · exact (hcoeff.2.2).trans (by exact_mod_cast hN)
  -- the value of the form is bounded below
  have hbound : ∀ N : ℕ, M ≤ N → N₁ ≤ N →
      ((N : ℝ) + 1) ^ (-(expo p q : ℝ)) ≤
        |(∑ i, (f i : ℝ) * z.1 i) + (∑ j, (g j : ℝ) * z.2 j) + (k : ℝ)| := by
    intro N hMN hNN
    have hzN := hN₁ N hNN
    have hzt : z ∉ tube p q N (f, g, k) := fun hzt => hzN (Set.mem_biUnion (hmem N hMN) hzt)
    exact not_lt.mp (fun hlt => hzt ⟨hz, hlt⟩)
  by_cases hNM : N₁ ≤ M
  · -- case `M ≥ N₁`: use the box at scale `M`
    have hb := hbound M le_rfl hNM
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      rw [div_le_one (by positivity)]
      linarith
    have h2 : (0 : ℝ) < ((M : ℝ) + 1) ^ (expo p q : ℝ) := by positivity
    have h3 : (1 / ((n : ℝ) + 1)) / (((M : ℝ) + 1) ^ (expo p q : ℝ))
        = (1 / ((n : ℝ) + 1)) * (((M : ℝ) + 1) ^ (expo p q : ℝ))⁻¹ := by ring
    have h4 : (((M : ℝ) + 1) ^ (expo p q : ℝ))⁻¹ = ((M : ℝ) + 1) ^ (-(expo p q : ℝ)) := by
      rw [Real.rpow_neg (by positivity)]
    rw [h3, h4]
    calc (1 / ((n : ℝ) + 1)) * ((M : ℝ) + 1) ^ (-(expo p q : ℝ))
        ≤ 1 * ((M : ℝ) + 1) ^ (-(expo p q : ℝ)) := by
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ((M : ℝ) + 1) ^ (-(expo p q : ℝ)) := one_mul _
      _ ≤ _ := hb
  · -- case `M < N₁`: use the box at scale `N₁`
    have hMN : M < N₁ := not_le.mp hNM
    have hb := hbound N₁ (le_of_lt hMN) le_rfl
    have h1 : (1 / ((n : ℝ) + 1)) / (((M : ℝ) + 1) ^ (expo p q : ℝ)) ≤ 1 / ((n : ℝ) + 1) := by
      have h2 : (1 : ℝ) ≤ ((M : ℝ) + 1) ^ (expo p q : ℝ) := by
        have h3 : (1 : ℝ) ≤ (M : ℝ) + 1 := by
          have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
          linarith
        calc (1 : ℝ) = 1 ^ (expo p q : ℝ) := by norm_num
          _ ≤ ((M : ℝ) + 1) ^ (expo p q : ℝ) := Real.rpow_le_rpow (by norm_num) h3 (by positivity)
      calc (1 / ((n : ℝ) + 1)) / (((M : ℝ) + 1) ^ (expo p q : ℝ))
          ≤ (1 / ((n : ℝ) + 1)) / 1 := by
            apply div_le_div_of_nonneg_left (by positivity) one_pos h2
        _ = 1 / ((n : ℝ) + 1) := by ring
    exact le_trans h1 (le_trans hC hb)

/-! ### The a.e. good condition and the reduction to the countable Diophantine condition -/

lemma ae_mem_fst_region (p q : ℕ) :
    ∀ᵐ z ∂((volume.restrict (simplexRegion (p + 1))).prod (volume.restrict (simplexRegion (q +
      1)))),
      z.1 ∈ simplexRegion (p + 1) := by
  rw [MeasureTheory.ae_iff]
  have hzero : ((volume.restrict (simplexRegion (p + 1))).prod
      (volume.restrict (simplexRegion (q + 1))))
      {z : (Fin p → ℝ) × (Fin q → ℝ) | ¬ z.1 ∈ simplexRegion (p + 1)} = 0 := by
    have hset : {z : (Fin p → ℝ) × (Fin q → ℝ) | ¬ z.1 ∈ simplexRegion (p + 1)}
        = (simplexRegion (p + 1))ᶜ ×ˢ (Set.univ : Set (Fin q → ℝ)) := by
      ext z
      simp
    rw [hset, Measure.prod_prod,
      Measure.restrict_apply (measurableSet_simplexRegion (p + 1)).compl,
      Set.compl_inter_self, measure_empty, zero_mul]
  refine measure_mono_null (fun z hz => hz) hzero

lemma ae_mem_snd_region (p q : ℕ) :
    ∀ᵐ z ∂((volume.restrict (simplexRegion (p + 1))).prod (volume.restrict (simplexRegion (q +
      1)))),
      z.2 ∈ simplexRegion (q + 1) := by
  rw [MeasureTheory.ae_iff]
  have hzero : ((volume.restrict (simplexRegion (p + 1))).prod
      (volume.restrict (simplexRegion (q + 1))))
      {z : (Fin p → ℝ) × (Fin q → ℝ) | ¬ z.2 ∈ simplexRegion (q + 1)} = 0 := by
    have hset : {z : (Fin p → ℝ) × (Fin q → ℝ) | ¬ z.2 ∈ simplexRegion (q + 1)}
        = (Set.univ : Set (Fin p → ℝ)) ×ˢ (simplexRegion (q + 1))ᶜ := by
      ext z
      simp
    rw [hset, Measure.prod_prod,
      Measure.restrict_apply (measurableSet_simplexRegion (q + 1)).compl,
      Set.compl_inter_self, measure_empty, mul_zero]
  refine measure_mono_null (fun z hz => hz) hzero

lemma ae_goodFree (p q : ℕ) :
    ∀ᵐ z ∂((volume.restrict (simplexRegion (p + 1))).prod (volume.restrict (simplexRegion (q +
      1)))),
      GoodFree p q z := by
  have h1 := ae_eventually_notMem_badSet (p := p) (q := q)
    (simplexRegion (p + 1)) (simplexRegion (q + 1))
  have h2 := (ae_mem_fst_region p q).and (ae_mem_snd_region p q)
  filter_upwards [h1, h2] with z hz1 hz2
  exact goodFree_of_eventually
    ⟨simplexRegion_subset_ubox _ hz2.1, simplexRegion_subset_ubox _ hz2.2⟩ hz1

/-- The identity between the integer form at the simplex point and the free affine form. -/
lemma aff_simplexMap {p q : ℕ} {v : Fin p → ℝ} {w : Fin q → ℝ}
    (hposv : ∀ i, 0 < v i) (hsumv : ∑ j, v j < 1)
    (hposw : ∀ j, 0 < w j) (hsumw : ∑ j, w j < 1)
    (a : Fin (p + 1) → ℤ) (b : Fin (q + 1) → ℤ) :
    (∑ i, (a i : ℝ) * ((simplexMap (p + 1) v i : ℝ≥0) : ℝ)
        + ∑ j, (b j : ℝ) * ((simplexMap (q + 1) w j : ℝ≥0) : ℝ))
      = (∑ i : Fin p, (((a i.castSucc - a (Fin.last p)) : ℤ) : ℝ) * v i)
        + (∑ j : Fin q, (((b j.castSucc - b (Fin.last q)) : ℤ) : ℝ) * w j)
        + ((a (Fin.last p) + b (Fin.last q) : ℤ) : ℝ) := by
  rw [sum_simplexMap_mul hposv hsumv, sum_simplexMap_mul hposw hsumw]
  push_cast
  ring

/-- The main reduction: the good free condition implies the countable Diophantine condition at the
corresponding simplex point. -/
lemma isDiophC_of_goodFree {p q : ℕ} {v : Fin p → ℝ} {w : Fin q → ℝ}
    (hposv : ∀ i, 0 < v i) (hsumv : ∑ j, v j < 1)
    (hposw : ∀ j, 0 < w j) (hsumw : ∑ j, w j < 1)
    (h : GoodFree p q (v, w)) :
    IsDiophC (simplexMap (p + 1) v) (simplexMap (q + 1) w) (expo p q) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨(m + 1) * 3 ^ (expo p q), ?_⟩
  intro a b hL
  set f : Fin p → ℤ := fun i => a i.castSucc - a (Fin.last p) with hf
  set g : Fin q → ℤ := fun j => b j.castSucc - b (Fin.last q) with hg
  set k : ℤ := a (Fin.last p) + b (Fin.last q) with hk
  set N : ℕ := max (coeffMax a) (coeffMax b) with hN
  set M : ℕ := max (coeffMax f) (max (coeffMax g) k.natAbs) with hM
  have hL' : (∑ i, (a i : ℝ) * ((simplexMap (p + 1) v i : ℝ≥0) : ℝ)
        + ∑ j, (b j : ℝ) * ((simplexMap (q + 1) w j : ℝ≥0) : ℝ))
      = (∑ i, (f i : ℝ) * v i) + (∑ j, (g j : ℝ) * w j) + (k : ℝ) :=
    aff_simplexMap hposv hsumv hposw hsumw a b
  rw [hL']
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · exfalso
      have hca : coeffMax a = 0 := le_antisymm (h0 ▸ le_max_left (coeffMax a) (coeffMax b))
        (Nat.zero_le _)
      have hcb : coeffMax b = 0 := le_antisymm (h0 ▸ le_max_right (coeffMax a) (coeffMax b))
        (Nat.zero_le _)
      have ha : a = 0 := funext fun i => Int.natAbs_eq_zero.mp (by
        have h3 := Finset.le_sup (f := fun i => (a i).natAbs) (Finset.mem_univ i)
        have h4 : (a i).natAbs ≤ N := le_trans h3 (le_max_left _ _)
        rw [h0] at h4
        exact Nat.le_zero.mp h4)
      have hb : b = 0 := funext fun j => Int.natAbs_eq_zero.mp (by
        have h3 := Finset.le_sup (f := fun j => (b j).natAbs) (Finset.mem_univ j)
        have h4 : (b j).natAbs ≤ N := le_trans h3 (le_max_right _ _)
        rw [h0] at h4
        exact Nat.le_zero.mp h4)
      apply hL
      simp [ha, hb]
    · exact hpos
  have hMle : M ≤ 2 * N := by
    have h1 : ∀ i, (f i).natAbs ≤ 2 * N := by
      intro i
      simp only [hf]
      have h2 := Int.natAbs_sub_le (a i.castSucc) (a (Fin.last p))
      have h3 : (a i.castSucc).natAbs ≤ N :=
        le_trans (Finset.le_sup (f := fun i => (a i).natAbs) (Finset.mem_univ _)) (le_max_left _ _)
      have h4 : (a (Fin.last p)).natAbs ≤ N :=
        le_trans (Finset.le_sup (f := fun i => (a i).natAbs) (Finset.mem_univ _)) (le_max_left _ _)
      omega
    have h2 : ∀ j, (g j).natAbs ≤ 2 * N := by
      intro j
      simp only [hg]
      have h3 := Int.natAbs_sub_le (b j.castSucc) (b (Fin.last q))
      have h4 : (b j.castSucc).natAbs ≤ N :=
        le_trans (Finset.le_sup (f := fun j => (b j).natAbs) (Finset.mem_univ _)) (le_max_right _ _)
      have h5 : (b (Fin.last q)).natAbs ≤ N :=
        le_trans (Finset.le_sup (f := fun j => (b j).natAbs) (Finset.mem_univ _)) (le_max_right _ _)
      omega
    have h6 : k.natAbs ≤ 2 * N := by
      simp only [hk]
      have h7 := Int.natAbs_add_le (a (Fin.last p)) (b (Fin.last q))
      have h8 : (a (Fin.last p)).natAbs ≤ N :=
        le_trans (Finset.le_sup (f := fun i => (a i).natAbs) (Finset.mem_univ _)) (le_max_left _ _)
      have h9 : (b (Fin.last q)).natAbs ≤ N :=
        le_trans (Finset.le_sup (f := fun j => (b j).natAbs) (Finset.mem_univ _)) (le_max_right _ _)
      omega
    have h10 : coeffMax f ≤ 2 * N := Finset.sup_le fun i _ => h1 i
    have h11 : coeffMax g ≤ 2 * N := Finset.sup_le fun j _ => h2 j
    exact max_le h10 (max_le h11 h6)
  by_cases hne : f ≠ 0 ∨ g ≠ 0
  · have haff : ((∑ i, (f i : ℝ) * v i) + (∑ j, (g j : ℝ) * w j) + (k : ℝ)) ≠ 0 := by
      rw [← hL']
      exact hL
    have hb := hm f g k hne haff
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hM3 : (M : ℝ) + 1 ≤ 3 * (N : ℝ) := by
      have h1 : (M : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hMle
      have h2 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
      linarith
    have hpow : ((M : ℝ) + 1) ^ (expo p q : ℝ) ≤ 3 ^ (expo p q : ℝ) * (N : ℝ) ^ (expo p q : ℝ) := by
      calc ((M : ℝ) + 1) ^ (expo p q : ℝ) ≤ (3 * (N : ℝ)) ^ (expo p q : ℝ) :=
            Real.rpow_le_rpow (by positivity) hM3 (by positivity)
        _ = 3 ^ (expo p q : ℝ) * (N : ℝ) ^ (expo p q : ℝ) :=
            Real.mul_rpow (by norm_num) (by positivity)
    have hm' : 1 / ((↑((m + 1) * 3 ^ (expo p q)) : ℝ) + 1) ≤
        (1 / ((m : ℝ) + 1)) * (3 : ℝ) ^ (-(expo p q : ℝ)) := by
      have hcast : (↑((m + 1) * 3 ^ (expo p q)) : ℝ) = ((m : ℝ) + 1) * 3 ^ (expo p q : ℝ) := by
        push_cast [Nat.cast_pow]
        rw [Real.rpow_natCast]
      have hpos3 : (0 : ℝ) < 3 ^ (expo p q : ℝ) := by positivity
      have hkey : (1 / ((m : ℝ) + 1)) * (3 : ℝ) ^ (-(expo p q : ℝ))
          = 1 / (((m : ℝ) + 1) * 3 ^ (expo p q : ℝ)) := by
        rw [Real.rpow_neg (by norm_num)]
        field_simp
      rw [hkey, hcast]
      apply one_div_le_one_div_of_le (by positivity)
      have : (0 : ℝ) < ((m : ℝ) + 1) * 3 ^ (expo p q : ℝ) := by positivity
      linarith
    have hmid : ((1 / ((m : ℝ) + 1)) * (3 : ℝ) ^ (-(expo p q : ℝ))) / (N : ℝ) ^ (expo p q : ℝ)
        = (1 / ((m : ℝ) + 1)) / (3 ^ (expo p q : ℝ) * (N : ℝ) ^ (expo p q : ℝ)) := by
      rw [Real.rpow_neg (by norm_num)]
      field_simp
    calc (1 / ((↑((m + 1) * 3 ^ (expo p q)) : ℝ) + 1)) / (N : ℝ) ^ (expo p q : ℝ)
        ≤ ((1 / ((m : ℝ) + 1)) * (3 : ℝ) ^ (-(expo p q : ℝ))) / (N : ℝ) ^ (expo p q : ℝ) := by
          apply div_le_div_of_nonneg_right hm' (by positivity)
      _ = (1 / ((m : ℝ) + 1)) / (3 ^ (expo p q : ℝ) * (N : ℝ) ^ (expo p q : ℝ)) := hmid
      _ ≤ (1 / ((m : ℝ) + 1)) / ((M : ℝ) + 1) ^ (expo p q : ℝ) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
      _ ≤ |(∑ i, (f i : ℝ) * v i) + (∑ j, (g j : ℝ) * w j) + (k : ℝ)| := hb
  · -- degenerate case: the gradient vanishes, so the form is a nonzero constant
    rw [not_or] at hne
    obtain ⟨hf0, hg0⟩ := hne
    rw [not_not] at hf0 hg0
    have haff : ((∑ i, (f i : ℝ) * v i) + (∑ j, (g j : ℝ) * w j) + (k : ℝ)) = (k : ℝ) := by
      simp [hf0, hg0]
    rw [haff]
    have hk0 : k ≠ 0 := by
      intro h0
      apply hL
      rw [hL', haff, h0]
      simp
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have h2 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by simp
        _ ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast h2
        _ = |(k : ℝ)| := Int.cast_abs
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have h2 : (1 : ℝ) ≤ (N : ℝ) ^ (expo p q : ℝ) := by
      calc (1 : ℝ) = (1 : ℝ) ^ (expo p q : ℝ) := by simp
        _ ≤ (N : ℝ) ^ (expo p q : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hN1) (by positivity)
    have h3 : 1 / ((↑((m + 1) * 3 ^ (expo p q)) : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (↑((m + 1) * 3 ^ (expo p q)) : ℝ) := Nat.cast_nonneg _
      linarith
    calc (1 / ((↑((m + 1) * 3 ^ (expo p q)) : ℝ) + 1)) / (N : ℝ) ^ (expo p q : ℝ)
        ≤ 1 / (N : ℝ) ^ (expo p q : ℝ) := by
          apply div_le_div_of_nonneg_right h3 (by positivity)
      _ ≤ 1 / 1 := by
          apply div_le_div_of_nonneg_left (by norm_num) one_pos h2
      _ ≤ |(k : ℝ)| := by simpa using hk1

/-! ### Measurability of the bad set and the final assembly -/

lemma continuous_form (d e : ℕ) (a : Fin d → ℤ) (b : Fin e → ℤ) :
    Continuous fun x : (Fin d → ℝ≥0) × (Fin e → ℝ≥0) =>
      (∑ i, (a i : ℝ) * ((x.1 i : ℝ≥0) : ℝ) + ∑ j, (b j : ℝ) * ((x.2 j : ℝ≥0) : ℝ)) := by
  apply Continuous.add
  · exact continuous_finsetSum _ fun i _ => continuous_const.mul
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst))
  · exact continuous_finsetSum _ fun j _ => continuous_const.mul
      (continuous_subtype_val.comp ((continuous_apply j).comp continuous_snd))

lemma measurableSet_not_isDiophC (d e : ℕ) (E : ℕ) :
    MeasurableSet {x : (Fin d → ℝ≥0) × (Fin e → ℝ≥0) | ¬ IsDiophC x.1 x.2 E} := by
  have hset : {x : (Fin d → ℝ≥0) × (Fin e → ℝ≥0) | ¬ IsDiophC x.1 x.2 E}
      = ⋂ m : ℕ, ⋃ (a : Fin d → ℤ) (b : Fin e → ℤ),
          {x : (Fin d → ℝ≥0) × (Fin e → ℝ≥0) |
            (∑ i, (a i : ℝ) * ((x.1 i : ℝ≥0) : ℝ)
              + ∑ j, (b j : ℝ) * ((x.2 j : ℝ≥0) : ℝ)) ≠ 0 ∧
            |(∑ i, (a i : ℝ) * ((x.1 i : ℝ≥0) : ℝ)
              + ∑ j, (b j : ℝ) * ((x.2 j : ℝ≥0) : ℝ))|
              < (1 / ((m : ℝ) + 1)) / ((max (coeffMax a) (coeffMax b) : ℕ) : ℝ) ^ (E : ℝ)} := by
    ext x
    simp only [IsDiophC, not_exists, not_forall, not_le, Set.mem_iInter,
      Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro h m
      obtain ⟨a, b, h1, h2⟩ := h m
      exact ⟨a, b, h1, h2⟩
    · intro h m
      obtain ⟨a, b, h1, h2⟩ := h m
      exact ⟨a, b, h1, h2⟩
  rw [hset]
  refine MeasurableSet.iInter fun m => MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
    ?_
  exact MeasurableSet.inter
    ((measurableSet_singleton (0 : ℝ)).compl.preimage (continuous_form d e a b).measurable)
    (measurableSet_lt (continuous_form d e a b).abs.measurable measurable_const)

/-- **Proposition 2.5**, in the form proved by the run `ae-diophantine` (membership in the
simplex is
an explicit hypothesis; see `ae_diophantine` below for the hypothesis-free form). -/
theorem ae_diophantine_of_mem {d e : ℕ} (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
      p.1 ∈ simplex d → p.2 ∈ simplex e → IsDiophantine p.1 p.2 := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    simp [simplex]
  rcases Nat.eq_zero_or_pos e with he0 | he
  · subst he0
    simp [simplex]
  obtain ⟨p, rfl⟩ : ∃ p, d = p + 1 := ⟨d - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, e = q + 1 := ⟨e - 1, by omega⟩
  have hmap : (simplexVolume (p + 1)).prod (simplexVolume (q + 1))
      = Measure.map (fun z : (Fin p → ℝ) × (Fin q → ℝ) =>
            (simplexMap (p + 1) z.1, simplexMap (q + 1) z.2))
          ((volume.restrict (simplexRegion (p + 1))).prod
            (volume.restrict (simplexRegion (q + 1)))) := by
    rw [simplexVolume, simplexVolume,
      Measure.map_prod_map _ _ (measurable_simplexMap _) (measurable_simplexMap _)]
    rfl
  have hmeasF : Measurable fun z : (Fin p → ℝ) × (Fin q → ℝ) =>
      (simplexMap (p + 1) z.1, simplexMap (q + 1) z.2) :=
    Measurable.prod ((measurable_simplexMap _).comp measurable_fst)
      ((measurable_simplexMap _).comp measurable_snd)
  have hgood : ∀ᵐ z ∂((volume.restrict (simplexRegion (p + 1))).prod
        (volume.restrict (simplexRegion (q + 1)))),
      IsDiophC (simplexMap (p + 1) z.1) (simplexMap (q + 1) z.2) (expo p q) := by
    filter_upwards [ae_goodFree (p := p) (q := q), ae_mem_fst_region p q, ae_mem_snd_region p q]
      with z hz hzv hzw
    exact isDiophC_of_goodFree (fun i => hzv.1 i) hzv.2 (fun j => hzw.1 j) hzw.2 hz
  have hnull : ((volume.restrict (simplexRegion (p + 1))).prod
      (volume.restrict (simplexRegion (q + 1))))
      {z | ¬ IsDiophC (simplexMap (p + 1) z.1) (simplexMap (q + 1) z.2) (expo p q)} = 0 := by
    rw [MeasureTheory.ae_iff] at hgood
    exact hgood
  rw [hmap, MeasureTheory.ae_iff]
  have hsubset : {x : (Fin (p + 1) → ℝ≥0) × (Fin (q + 1) → ℝ≥0) |
        ¬ (x.1 ∈ simplex (p + 1) → x.2 ∈ simplex (q + 1) → IsDiophantine x.1 x.2)}
      ⊆ {x : (Fin (p + 1) → ℝ≥0) × (Fin (q + 1) → ℝ≥0) | ¬ IsDiophC x.1 x.2 (expo p q)} := by
    intro x hx hD
    exact hx fun _ _ => hD.isDiophantine (by unfold expo; omega)
  refine measure_mono_null hsubset ?_
  rw [Measure.map_apply hmeasF (measurableSet_not_isDiophC _ _ _)]
  exact hnull

/-! ## The measure is supported on the simplex, and Proposition 2.5 without hypotheses

`simplexVolume d` is the pushforward of Lebesgue measure on `simplexRegion d`, and `simplexMap`
  sends
that region into `simplex d` (the coordinates are `v` and `1 - ∑ v`, which sum to `1`).  So the
membership hypotheses of `ae_diophantine_of_mem` are redundant, for `d, e ≥ 1` as in the paper.

For `d = 0` the hypothesis-free form is *false*: `simplex 0 = ∅` (the empty sum is `0 ≠ 1`) while
`simplexVolume 0` is a probability measure on the one-point space `Fin 0 → ℝ≥0`.  That is why the
statement below carries `[NeZero d] [NeZero e]`, matching the paper's `d, e ∈ ℕ*`.
-/

/-- The simplex is closed, hence measurable: it is the preimage of `{1}` under the sum. -/
theorem isClosed_simplex (d : ℕ) : IsClosed (simplex d) := by
  have hcont : Continuous fun lam : Fin d → ℝ≥0 => ∑ i, lam i :=
    continuous_finsetSum _ (fun i _ => continuous_apply i)
  have h : simplex d = (fun lam : Fin d → ℝ≥0 => ∑ i, lam i) ⁻¹' {1} := rfl
  rw [h]
  exact isClosed_singleton.preimage hcont

theorem measurableSet_simplex (d : ℕ) : MeasurableSet (simplex d) :=
  (isClosed_simplex d).measurableSet

/-- `simplexMap` sends the free region into the simplex: the coordinates are `v i` and `1 - ∑ v`,
which sum to `1`. -/
theorem simplexMap_mem_simplex {p : ℕ} {v : Fin p → ℝ} (hpos : ∀ i, 0 < v i)
    (hsum : ∑ i, v i < 1) : simplexMap (p + 1) v ∈ simplex (p + 1) := by
  change ∑ i, simplexMap (p + 1) v i = 1
  refine NNReal.coe_injective ?_
  rw [NNReal.coe_sum, NNReal.coe_one, Fin.sum_univ_castSucc,
    simplexMap_last_coe hsum]
  simp only [simplexMap_castSucc_coe hpos]
  ring

/-- **The measure `simplexVolume d` is supported on the simplex** (for `d ≥ 1`). -/
theorem simplexVolume_compl_simplex {d : ℕ} [NeZero d] : simplexVolume d (simplex d)ᶜ = 0 := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨p, rfl⟩ : ∃ p, d = p + 1 := ⟨d - 1, by omega⟩
  have hempty : (simplexMap (p + 1)) ⁻¹' (simplex (p + 1))ᶜ ∩ simplexRegion (p + 1) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr (fun v hv => ?_)
    exact hv.1 (simplexMap_mem_simplex hv.2.1 hv.2.2)
  rw [simplexVolume,
    Measure.map_apply (measurable_simplexMap _) (measurableSet_simplex _).compl,
    Measure.restrict_apply ((measurableSet_simplex _).compl.preimage (measurable_simplexMap _)),
    hempty, measure_empty]

/-- The free region has finite volume: it sits inside the unit box `ubox`. -/
theorem volume_simplexRegion_ne_top (d : ℕ) : volume (simplexRegion d) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (simplexRegion_subset_ubox d))
  rw [volume_ubox]
  exact ENNReal.one_ne_top

instance instFiniteRestrictSimplexRegion (d : ℕ) :
    IsFiniteMeasure (volume.restrict (simplexRegion d)) :=
  ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr (volume_simplexRegion_ne_top d)⟩

/-- `simplexVolume d` is a finite measure. -/
instance instFiniteSimplexVolume (d : ℕ) : IsFiniteMeasure (simplexVolume d) := by
  unfold simplexVolume
  infer_instance

/-- Almost every pair lies in the product of the simplices. -/
theorem ae_mem_simplex_prod {d e : ℕ} [NeZero d] [NeZero e] :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)), p.1 ∈ simplex d ∧ p.2 ∈ simplex e := by
  have h1 : ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)), p.1 ∈ simplex d := by
    rw [MeasureTheory.ae_iff]
    have hset : {p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0) | p.1 ∉ simplex d}
        = (simplex d)ᶜ ×ˢ Set.univ := by
      ext p
      simp
    rw [hset, Measure.prod_prod, simplexVolume_compl_simplex, zero_mul]
  have h2 : ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)), p.2 ∈ simplex e := by
    rw [MeasureTheory.ae_iff]
    have hset : {p : (Fin d → ℝ≥0) × (Fin e → ℝ≥0) | p.2 ∉ simplex e}
        = Set.univ ×ˢ (simplex e)ᶜ := by
      ext p
      simp
    rw [hset, Measure.prod_prod, simplexVolume_compl_simplex, mul_zero]
  exact h1.and h2

/-- **Proposition 2.5** in the paper's form: almost every pair of length vectors is
Diophantine, with
no membership hypothesis — the measure is supported on the product of the simplices. -/
theorem ae_diophantine {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d))
    (σ : Equiv.Perm (Fin e)) :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)), IsDiophantine p.1 p.2 := by
  filter_upwards [ae_diophantine_of_mem π σ, ae_mem_simplex_prod] with p hp hmem
  exact hp hmem.1 hmem.2

/-! ### The Diophantine transfer used in Lemma 3.4 -/

section IntCombination

variable {d e r n : ℕ} {lam : Fin d → ℝ≥0} {mu : Fin e → ℝ≥0}

/-- A bound on the absolute value of a sum of products. -/
theorem natAbs_sum_mul_le {ι : Type*} [Fintype ι] (f g : ι → ℤ) (N K : ℕ)
    (hf : ∀ i, (f i).natAbs ≤ N) (hg : ∀ i, (g i).natAbs ≤ K) :
    (∑ i, f i * g i).natAbs ≤ Fintype.card ι * (N * K) := by
  refine (Int.natAbs_sum_le _ _).trans ?_
  have h1 : ∀ i, (f i * g i).natAbs ≤ N * K := by
    intro i
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (hf i) (hg i)
  calc (∑ i, (f i * g i).natAbs) ≤ ∑ _i : ι, N * K := Finset.sum_le_sum (fun i _ => h1 i)
    _ = Fintype.card ι * (N * K) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **Integer combinations of a Diophantine pair are Diophantine after rescaling.** -/
theorem IsDiophantine.of_int_combination (hdio : IsDiophantine lam mu) {K : ℕ} (hK : 0 < K)
    (w : Fin r → ℝ≥0) (w' : Fin n → ℝ≥0) (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (A : Fin r → Fin d → ℤ) (B : Fin r → Fin e → ℤ)
    (A' : Fin n → Fin d → ℤ) (B' : Fin n → Fin e → ℤ)
    (hrn : 0 < r + n)
    (hA : ∀ i k, (A i k).natAbs ≤ K) (hB : ∀ i l, (B i l).natAbs ≤ K)
    (hA' : ∀ j k, (A' j k).natAbs ≤ K) (hB' : ∀ j l, (B' j l).natAbs ≤ K)
    (hw : ∀ i, (w i : ℝ) = ∑ k, (A i k : ℝ) * (lam k : ℝ) + ∑ l, (B i l : ℝ) * (mu l : ℝ))
    (hw' : ∀ j, (w' j : ℝ) = ∑ k, (A' j k : ℝ) * (lam k : ℝ) + ∑ l, (B' j l : ℝ) * (mu l : ℝ)) :
    IsDiophantine (fun i => ⟨(w i : ℝ) / u, div_nonneg (w i).coe_nonneg hu0.le⟩)
      (fun j => ⟨(w' j : ℝ) / u, div_nonneg (w' j).coe_nonneg hu0.le⟩) := by
  obtain ⟨C, hCpos, c, hcpos, hC⟩ := hdio
  classical
  set Acomb : (Fin r → ℤ) → (Fin n → ℤ) → Fin d → ℤ := fun a b k =>
    ∑ i, a i * A i k + ∑ j, b j * A' j k with hAcombdef
  set Bcomb : (Fin r → ℤ) → (Fin n → ℤ) → Fin e → ℤ := fun a b l =>
    ∑ i, a i * B i l + ∑ j, b j * B' j l with hBcombdef
  set Ktot : ℕ := (r + n) * K with hKtotdef
  have hKtotpos : 0 < Ktot := by rw [hKtotdef]; exact Nat.mul_pos hrn hK
  have hKtotR : (0 : ℝ) < (Ktot : ℝ) := by exact_mod_cast hKtotpos
  have hAbound : ∀ (a : Fin r → ℤ) (b : Fin n → ℤ) (k : Fin d),
      (Acomb a b k).natAbs ≤ Ktot * max (coeffMax a) (coeffMax b) := by
    intro a b k
    set N : ℕ := max (coeffMax a) (coeffMax b) with hNdef
    have ha : ∀ i, (a i).natAbs ≤ N := fun i =>
      le_trans (Finset.le_sup (f := fun i => (a i).natAbs) (Finset.mem_univ i)) (le_max_left _ _)
    have hb : ∀ j, (b j).natAbs ≤ N := fun j =>
      le_trans (Finset.le_sup (f := fun j => (b j).natAbs) (Finset.mem_univ j)) (le_max_right _ _)
    have h1 : (∑ i, a i * A i k).natAbs ≤ Fintype.card (Fin r) * (N * K) :=
      natAbs_sum_mul_le a (fun i => A i k) N K ha (fun i => hA i k)
    have h2 : (∑ j, b j * A' j k).natAbs ≤ Fintype.card (Fin n) * (N * K) :=
      natAbs_sum_mul_le b (fun j => A' j k) N K hb (fun j => hA' j k)
    have h3 := Int.natAbs_add_le (∑ i, a i * A i k) (∑ j, b j * A' j k)
    simp only [Fintype.card_fin] at h1 h2
    have he : r * (N * K) + n * (N * K) = Ktot * N := by rw [hKtotdef]; ring
    rw [hAcombdef]
    simp only
    omega
  have hBbound : ∀ (a : Fin r → ℤ) (b : Fin n → ℤ) (l : Fin e),
      (Bcomb a b l).natAbs ≤ Ktot * max (coeffMax a) (coeffMax b) := by
    intro a b l
    set N : ℕ := max (coeffMax a) (coeffMax b) with hNdef
    have ha : ∀ i, (a i).natAbs ≤ N := fun i =>
      le_trans (Finset.le_sup (f := fun i => (a i).natAbs) (Finset.mem_univ i)) (le_max_left _ _)
    have hb : ∀ j, (b j).natAbs ≤ N := fun j =>
      le_trans (Finset.le_sup (f := fun j => (b j).natAbs) (Finset.mem_univ j)) (le_max_right _ _)
    have h1 : (∑ i, a i * B i l).natAbs ≤ Fintype.card (Fin r) * (N * K) :=
      natAbs_sum_mul_le a (fun i => B i l) N K ha (fun i => hB i l)
    have h2 : (∑ j, b j * B' j l).natAbs ≤ Fintype.card (Fin n) * (N * K) :=
      natAbs_sum_mul_le b (fun j => B' j l) N K hb (fun j => hB' j l)
    have h3 := Int.natAbs_add_le (∑ i, a i * B i l) (∑ j, b j * B' j l)
    simp only [Fintype.card_fin] at h1 h2
    have he : r * (N * K) + n * (N * K) = Ktot * N := by rw [hKtotdef]; ring
    rw [hBcombdef]
    simp only
    omega
  refine ⟨C / (Ktot : ℝ) ^ c, ?_, c, hcpos, ?_⟩
  · exact div_pos hCpos (Real.rpow_pos_of_pos hKtotR c)
  · intro a b hne
    change C / (Ktot : ℝ) ^ c / ((max (coeffMax a) (coeffMax b) : ℕ) : ℝ) ^ c
      ≤ |∑ i, (a i : ℝ) * ((w i : ℝ) / u) + ∑ j, (b j : ℝ) * ((w' j : ℝ) / u)|
    have hsub1 : ∀ i, (a i : ℝ) * (w i : ℝ)
        = (∑ k, ((a i : ℝ) * (A i k : ℝ)) * (lam k : ℝ))
          + ∑ l, ((a i : ℝ) * (B i l : ℝ)) * (mu l : ℝ) := by
      intro i
      rw [hw i, mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl (fun j _ => ?_) <;> ring
    have hsub2 : ∀ j, (b j : ℝ) * (w' j : ℝ)
        = (∑ k, ((b j : ℝ) * (A' j k : ℝ)) * (lam k : ℝ))
          + ∑ l, ((b j : ℝ) * (B' j l : ℝ)) * (mu l : ℝ) := by
      intro j
      rw [hw' j, mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl (fun j' _ => ?_) <;> ring
    have hsum1 : (∑ i, (a i : ℝ) * (w i : ℝ))
        = (∑ k, (∑ i, (a i : ℝ) * (A i k : ℝ)) * (lam k : ℝ))
          + ∑ l, (∑ i, (a i : ℝ) * (B i l : ℝ)) * (mu l : ℝ) := by
      calc (∑ i, (a i : ℝ) * (w i : ℝ))
          = ∑ i, ((∑ k, ((a i : ℝ) * (A i k : ℝ)) * (lam k : ℝ))
              + ∑ l, ((a i : ℝ) * (B i l : ℝ)) * (mu l : ℝ)) :=
            Finset.sum_congr rfl (fun i _ => hsub1 i)
        _ = (∑ i, ∑ k, ((a i : ℝ) * (A i k : ℝ)) * (lam k : ℝ))
              + ∑ i, ∑ l, ((a i : ℝ) * (B i l : ℝ)) * (mu l : ℝ) :=
            Finset.sum_add_distrib
        _ = (∑ k, (∑ i, (a i : ℝ) * (A i k : ℝ)) * (lam k : ℝ))
              + ∑ l, (∑ i, (a i : ℝ) * (B i l : ℝ)) * (mu l : ℝ) := by
            congr 1
            · rw [Finset.sum_comm]; simp only [Finset.sum_mul]
            · rw [Finset.sum_comm]; simp only [Finset.sum_mul]
    have hsum2 : (∑ j, (b j : ℝ) * (w' j : ℝ))
        = (∑ k, (∑ j, (b j : ℝ) * (A' j k : ℝ)) * (lam k : ℝ))
          + ∑ l, (∑ j, (b j : ℝ) * (B' j l : ℝ)) * (mu l : ℝ) := by
      calc (∑ j, (b j : ℝ) * (w' j : ℝ))
          = ∑ j, ((∑ k, ((b j : ℝ) * (A' j k : ℝ)) * (lam k : ℝ))
              + ∑ l, ((b j : ℝ) * (B' j l : ℝ)) * (mu l : ℝ)) :=
            Finset.sum_congr rfl (fun j _ => hsub2 j)
        _ = (∑ j, ∑ k, ((b j : ℝ) * (A' j k : ℝ)) * (lam k : ℝ))
              + ∑ j, ∑ l, ((b j : ℝ) * (B' j l : ℝ)) * (mu l : ℝ) :=
            Finset.sum_add_distrib
        _ = (∑ k, (∑ j, (b j : ℝ) * (A' j k : ℝ)) * (lam k : ℝ))
              + ∑ l, (∑ j, (b j : ℝ) * (B' j l : ℝ)) * (mu l : ℝ) := by
            congr 1
            · rw [Finset.sum_comm]; simp only [Finset.sum_mul]
            · rw [Finset.sum_comm]; simp only [Finset.sum_mul]
    have hL : (∑ k, (Acomb a b k : ℝ) * (lam k : ℝ))
        = (∑ k, (∑ i, (a i : ℝ) * (A i k : ℝ)) * (lam k : ℝ))
          + ∑ k, (∑ j, (b j : ℝ) * (A' j k : ℝ)) * (lam k : ℝ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hk : (Acomb a b k : ℝ)
          = (∑ i, (a i : ℝ) * (A i k : ℝ)) + ∑ j, (b j : ℝ) * (A' j k : ℝ) := by
        rw [hAcombdef]
        push_cast
        rfl
      rw [hk, add_mul]
    have hM : (∑ l, (Bcomb a b l : ℝ) * (mu l : ℝ))
        = (∑ l, (∑ i, (a i : ℝ) * (B i l : ℝ)) * (mu l : ℝ))
          + ∑ l, (∑ j, (b j : ℝ) * (B' j l : ℝ)) * (mu l : ℝ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      have hl : (Bcomb a b l : ℝ)
          = (∑ i, (a i : ℝ) * (B i l : ℝ)) + ∑ j, (b j : ℝ) * (B' j l : ℝ) := by
        rw [hBcombdef]
        push_cast
        rfl
      rw [hl, add_mul]
    set T : ℝ := (∑ k, (Acomb a b k : ℝ) * (lam k : ℝ))
      + ∑ l, (Bcomb a b l : ℝ) * (mu l : ℝ) with hTdef
    have hT : (∑ i, (a i : ℝ) * ((w i : ℝ) / u)) + ∑ j, (b j : ℝ) * ((w' j : ℝ) / u)
        = T / u := by
      have h1 : (∑ i, (a i : ℝ) * ((w i : ℝ) / u)) + ∑ j, (b j : ℝ) * ((w' j : ℝ) / u)
          = ((∑ i, (a i : ℝ) * (w i : ℝ)) + ∑ j, (b j : ℝ) * (w' j : ℝ)) / u := by
        rw [add_div, Finset.sum_div, Finset.sum_div]
        congr 1
        · exact Finset.sum_congr rfl (fun i _ => (mul_div_assoc _ _ _).symm)
        · exact Finset.sum_congr rfl (fun j _ => (mul_div_assoc _ _ _).symm)
      rw [h1]
      congr 1
      rw [hsum1, hsum2]
      rw [show (∑ k, (∑ i, (a i : ℝ) * (A i k : ℝ)) * (lam k : ℝ))
            + (∑ l, (∑ i, (a i : ℝ) * (B i l : ℝ)) * (mu l : ℝ))
            + ((∑ k, (∑ j, (b j : ℝ) * (A' j k : ℝ)) * (lam k : ℝ))
              + ∑ l, (∑ j, (b j : ℝ) * (B' j l : ℝ)) * (mu l : ℝ))
          = ((∑ k, (∑ i, (a i : ℝ) * (A i k : ℝ)) * (lam k : ℝ))
              + ∑ k, (∑ j, (b j : ℝ) * (A' j k : ℝ)) * (lam k : ℝ))
            + ((∑ l, (∑ i, (a i : ℝ) * (B i l : ℝ)) * (mu l : ℝ))
              + ∑ l, (∑ j, (b j : ℝ) * (B' j l : ℝ)) * (mu l : ℝ)) from by ring]
      rw [← hL, ← hM, ← hTdef]
    have hTne : T ≠ 0 := by
      intro h0
      apply hne
      change (∑ i, (a i : ℝ) * ((w i : ℝ) / u)) + ∑ j, (b j : ℝ) * ((w' j : ℝ) / u) = 0
      rw [hT, h0, zero_div]
    have hmaxApos : (0 : ℝ)
        < ((max (coeffMax (Acomb a b)) (coeffMax (Bcomb a b)) : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos (max (coeffMax (Acomb a b)) (coeffMax (Bcomb a b))) with h | h
      · exfalso
        have hA0 : ∀ k, Acomb a b k = 0 := by
          intro k
          have h1 : (Acomb a b k).natAbs
              ≤ max (coeffMax (Acomb a b)) (coeffMax (Bcomb a b)) :=
            le_trans (Finset.le_sup (f := fun k => (Acomb a b k).natAbs) (Finset.mem_univ k))
              (le_max_left _ _)
          rw [h] at h1
          exact Int.natAbs_eq_zero.mp (Nat.le_zero.mp h1)
        have hB0 : ∀ l, Bcomb a b l = 0 := by
          intro l
          have h1 : (Bcomb a b l).natAbs
              ≤ max (coeffMax (Acomb a b)) (coeffMax (Bcomb a b)) :=
            le_trans (Finset.le_sup (f := fun l => (Bcomb a b l).natAbs) (Finset.mem_univ l))
              (le_max_right _ _)
          rw [h] at h1
          exact Int.natAbs_eq_zero.mp (Nat.le_zero.mp h1)
        apply hTne
        rw [hTdef]
        simp only [hA0, hB0, Int.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]
      · exact_mod_cast h
    have hdio' := hC (Acomb a b) (Bcomb a b) hTne
    have hmax : ((max (coeffMax (Acomb a b)) (coeffMax (Bcomb a b)) : ℕ) : ℝ)
        ≤ (Ktot : ℝ) * ((max (coeffMax a) (coeffMax b) : ℕ) : ℝ) := by
      have h1 : max (coeffMax (Acomb a b)) (coeffMax (Bcomb a b))
          ≤ Ktot * max (coeffMax a) (coeffMax b) := by
        refine max_le ?_ ?_
        · exact Finset.sup_le (fun k _ => hAbound a b k)
        · exact Finset.sup_le (fun l _ => hBbound a b l)
      calc ((max (coeffMax (Acomb a b)) (coeffMax (Bcomb a b)) : ℕ) : ℝ)
          ≤ ((Ktot * max (coeffMax a) (coeffMax b) : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (Ktot : ℝ) * ((max (coeffMax a) (coeffMax b) : ℕ) : ℝ) := by push_cast; ring
    rw [hT, abs_div, abs_of_pos hu0, le_div_iff₀ hu0]
    set N : ℝ := ((max (coeffMax a) (coeffMax b) : ℕ) : ℝ) with hNdef
    have hN0 : 0 ≤ N := by positivity
    have hkey : C / (Ktot : ℝ) ^ c / N ^ c
        ≤ C / ((max (coeffMax (Acomb a b)) (coeffMax (Bcomb a b)) : ℕ) : ℝ) ^ c := by
      have h1 : ((max (coeffMax (Acomb a b)) (coeffMax (Bcomb a b)) : ℕ) : ℝ) ^ c
          ≤ ((Ktot : ℝ) * N) ^ c :=
        Real.rpow_le_rpow (le_of_lt hmaxApos) hmax (le_of_lt hcpos)
      have h2 : (0 : ℝ) < ((max (coeffMax (Acomb a b)) (coeffMax (Bcomb a b)) : ℕ) : ℝ) ^ c :=
        Real.rpow_pos_of_pos hmaxApos c
      have h3 : C / ((Ktot : ℝ) * N) ^ c
          ≤ C / ((max (coeffMax (Acomb a b)) (coeffMax (Bcomb a b)) : ℕ) : ℝ) ^ c :=
        div_le_div_of_nonneg_left hCpos.le h2 h1
      have h4 : ((Ktot : ℝ) * N) ^ c = (Ktot : ℝ) ^ c * N ^ c :=
        Real.mul_rpow (le_of_lt hKtotR) hN0
      calc C / (Ktot : ℝ) ^ c / N ^ c = C / ((Ktot : ℝ) * N) ^ c := by
            rw [h4, div_div]
        _ ≤ _ := h3
    have hfin : C / (Ktot : ℝ) ^ c / N ^ c ≤ |T| := le_trans hkey hdio'
    have hnonneg : (0 : ℝ) ≤ C / (Ktot : ℝ) ^ c / N ^ c := by positivity
    have hmul : C / (Ktot : ℝ) ^ c / N ^ c * u ≤ C / (Ktot : ℝ) ^ c / N ^ c := by
      nlinarith [hu1, hnonneg]
    exact le_trans hmul hfin

end IntCombination
