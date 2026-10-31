/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import IETFree.TranslationVector

/-!
# The singularity bound: the cuts of a word are lattice points of bounded size

Let `f` and `g` be permutations of `ℝ` that are **piecewise translations** with finite cut sets
  `Sf`,
`Sg`: on the pieces cut by `Sf` the displacement of `f` is constant and is an integer combination of
the reals `lam i` with coefficients in `{-1, 0, 1}` (and likewise `g` with `mu`), and the elements
  of
`Sf`, `Sg` are themselves such lattice combinations.  Preimages of cuts are always taken under a
  *single* letter, so no
translation-vector bound is needed as a hypothesis here.

Then for every word `w` there is a finite set `C` cutting `w(f, g)` into translation pieces, all of
whose elements are lattice combinations with coefficients `≤ |w| + 1`.

This is the paper's step, in the proof of Theorem 2.6, that "all singularities of `h_n` are of the
form `∑ a_i λ_i + ∑ b_j μ_j` … the numbers `a_i` and `b_j` … are all bounded linearly in terms of
  the
word length".  It gives the cell-length lemma `exists_lattice_cell` at the end of this file,
which is
instantiated for the exchanges `mkIET1 lam π` and `mkIET1 mu σ`: a nontrivial `w(f, g)` has a
translation interval whose length is a *nonzero* lattice combination with coefficients
`≤ 2|w| + 3` and at most the measure of the support of `w(f, g)` — exactly the input the Diophantine
condition bounds below by `C / |w| ^ c`.

The bound is proved by the run `singularity-bound-2` (`Tasks/singularity_bound.lean`) and ported
  here;
the pieces are `step` (the cut set of `A * e'` is `Ce ∪ C.image e'.symm`, with the preimage of a cut
computed by subtracting the displacement of `e'`) and `inv_translate_aux` (the cuts of `f⁻¹` are
`Sf.image f`).
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace CutBound

/-- **`CutSep` is `IET.lean`'s `Separated`**, kept under its old name: some cut lies in
`(min x y, max x y]`. -/
abbrev CutSep (S : Finset ℝ) (x y : ℝ) : Prop := Separated S x y

lemma cutSep_comm (S : Finset ℝ) (x y : ℝ) : CutSep S x y ↔ CutSep S y x :=
  Separated.comm

lemma cutSep_mono {S T : Finset ℝ} (hST : S ⊆ T) {x y : ℝ} (h : CutSep S x y) :
    CutSep T x y :=
  Separated.mono h hST

lemma ioc_subset_of_mem {x y z : ℝ} (h : z ∈ Set.Ioc (min x y) (max x y)) :
    Set.Ioc (min x z) (max x z) ⊆ Set.Ioc (min x y) (max x y) := by
  have hmin : min x y ≤ min x z := by
    by_cases hxz : x ≤ z
    · rw [min_eq_left hxz]; exact min_le_left x y
    · rw [min_eq_right (le_of_lt (not_le.mp hxz))]; exact le_of_lt h.1
  have hmax : max x z ≤ max x y := by
    by_cases hxz : x ≤ z
    · rw [max_eq_right hxz]; exact h.2
    · rw [max_eq_left (le_of_lt (not_le.mp hxz))]; exact le_max_left x y
  intro w hw
  simp only [Set.mem_Ioc] at hw ⊢
  exact ⟨lt_of_le_of_lt hmin hw.1, le_trans hw.2 hmax⟩

lemma cutSep_mono_ioc {S : Finset ℝ} {x y z : ℝ}
    (hz : z ∈ Set.Ioc (min x y) (max x y)) (h : CutSep S x z) : CutSep S x y := by
  obtain ⟨c, hcS, hcI⟩ := h
  exact ⟨c, hcS, ioc_subset_of_mem hz hcI⟩


section Lattice
variable {d e : ℕ} (lam : Fin d → ℝ) (mu : Fin e → ℝ)

/-- The lattice combination `∑ aᵢ λᵢ + ∑ bⱼ μⱼ`. -/
def comb (a : Fin d → ℤ) (b : Fin e → ℤ) : ℝ :=
  (∑ i, (a i : ℝ) * lam i) + ∑ j, (b j : ℝ) * mu j

/-- `x` is a lattice combination of `lam`, `mu` with all coefficients `≤ k` in absolute value. -/
def IsLat (k : ℤ) (x : ℝ) : Prop :=
  ∃ a : Fin d → ℤ, ∃ b : Fin e → ℤ,
    (∀ i, |a i| ≤ k) ∧ (∀ j, |b j| ≤ k) ∧ x = comb lam mu a b

lemma isLat_mono {k l : ℤ} (hkl : k ≤ l) {x : ℝ} (hx : IsLat lam mu k x) :
    IsLat lam mu l x := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  exact ⟨a, b, fun i => le_trans (ha i) hkl, fun j => le_trans (hb j) hkl, rfl⟩

lemma int_abs_sub_le (a b : ℤ) : |a - b| ≤ |a| + |b| := by
  calc |a - b| = |a + -b| := by ring_nf
    _ ≤ |a| + |-b| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

lemma sum_sub_mul {n : ℕ} {lam : Fin n → ℝ} (a1 a2 : Fin n → ℤ) :
    (∑ i, ((a1 i : ℝ) - (a2 i : ℝ)) * lam i)
      = (∑ i, (a1 i : ℝ) * lam i) - ∑ i, (a2 i : ℝ) * lam i := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma sum_add_mul {n : ℕ} {lam : Fin n → ℝ} (a1 a2 : Fin n → ℤ) :
    (∑ i, ((a1 i : ℝ) + (a2 i : ℝ)) * lam i)
      = (∑ i, (a1 i : ℝ) * lam i) + ∑ i, (a2 i : ℝ) * lam i := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma isLat_sub {k l : ℤ} {x y : ℝ} (hx : IsLat lam mu k x) (hy : IsLat lam mu l y) :
    IsLat lam mu (k + l) (x - y) := by
  obtain ⟨a1, b1, ha1, hb1, rfl⟩ := hx
  obtain ⟨a2, b2, ha2, hb2, rfl⟩ := hy
  refine ⟨fun i => a1 i - a2 i, fun j => b1 j - b2 j, ?_, ?_, ?_⟩
  · intro i
    change |a1 i - a2 i| ≤ k + l
    have h := int_abs_sub_le (a1 i) (a2 i)
    have := ha1 i
    have := ha2 i
    omega
  · intro j
    change |b1 j - b2 j| ≤ k + l
    have h := int_abs_sub_le (b1 j) (b2 j)
    have := hb1 j
    have := hb2 j
    omega
  · simp only [comb]
    push_cast
    rw [sum_sub_mul a1 a2, sum_sub_mul b1 b2]
    ring

lemma isLat_add {k l : ℤ} {x y : ℝ} (hx : IsLat lam mu k x) (hy : IsLat lam mu l y) :
    IsLat lam mu (k + l) (x + y) := by
  obtain ⟨a1, b1, ha1, hb1, rfl⟩ := hx
  obtain ⟨a2, b2, ha2, hb2, rfl⟩ := hy
  refine ⟨fun i => a1 i + a2 i, fun j => b1 j + b2 j, ?_, ?_, ?_⟩
  · intro i
    change |a1 i + a2 i| ≤ k + l
    have h := abs_add_le (a1 i) (a2 i)
    have := ha1 i
    have := ha2 i
    omega
  · intro j
    change |b1 j + b2 j| ≤ k + l
    have h := abs_add_le (b1 j) (b2 j)
    have := hb1 j
    have := hb2 j
    omega
  · simp only [comb]
    push_cast
    rw [sum_add_mul a1 a2, sum_add_mul b1 b2]
    ring

lemma isLat_neg {k : ℤ} {x : ℝ} (hx : IsLat lam mu k x) : IsLat lam mu k (-x) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  refine ⟨fun i => -a i, fun j => -b j, ?_, ?_, ?_⟩
  · intro i; simpa using ha i
  · intro j; simpa using hb j
  · simp only [comb]
    rw [show (∑ i, ((-a i : ℤ) : ℝ) * lam i) = -∑ i, (a i : ℝ) * lam i from ?_,
        show (∑ j, ((-b j : ℤ) : ℝ) * mu j) = -∑ j, (b j : ℝ) * mu j from ?_]
    · ring
    · rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; push_cast; ring
    · rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; push_cast; ring

lemma isLat_lambda {k : ℤ} (hk : 0 ≤ k) {a : Fin d → ℤ} (ha : ∀ i, |a i| ≤ k) :
    IsLat lam mu k (∑ i, (a i : ℝ) * lam i) :=
  ⟨a, 0, ha, fun j => by simpa using hk, by simp [comb]⟩

lemma isLat_mu {k : ℤ} (hk : 0 ≤ k) {b : Fin e → ℤ} (hb : ∀ j, |b j| ≤ k) :
    IsLat lam mu k (∑ j, (b j : ℝ) * mu j) :=
  ⟨0, b, fun i => by simpa using hk, hb, by simp [comb]⟩

end Lattice

set_option maxHeartbeats 400000 in
-- recovering the pieces of `f⁻¹` from those of `f` needs more than the default 200000 heartbeats
lemma inv_translate_aux {S : Finset ℝ} {f : Equiv.Perm ℝ}
    (hS : ∀ y y', ¬ CutSep S y y' → f y - y = f y' - y') :
    ∀ y y', ¬ CutSep (S.image f) y y' → f.symm y - y = f.symm y' - y' := by
  have key : ∀ a b : ℝ, a < b → f a - a ≠ f b - b → CutSep (S.image f) (f a) (f b) := by
    intro a b hab hne
    have hcut : ∃ c ∈ S, a < c ∧ c ≤ b := by
      by_contra hcon
      push Not at hcon
      apply hne
      apply hS a b
      rintro ⟨c, hcS, hcI⟩
      have hc : a < c ∧ c ≤ b := (mem_Ioc_min_max a b hab.le).mp hcI
      exact absurd hc.2 (not_le.mpr (hcon c hcS hc.1))
    obtain ⟨c₀, hc₀S, hac₀, hc₀b⟩ := hcut
    set T := S.filter (fun s => a < s ∧ s ≤ b) with hT
    have hTne : T.Nonempty := ⟨c₀, by simp [hT, hc₀S, hac₀, hc₀b]⟩
    set c := T.max' hTne with hc
    have hcT : c ∈ T := Finset.max'_mem T hTne
    have hcT' : c ∈ S ∧ a < c ∧ c ≤ b := by simpa [hT] using hcT
    have hcS : c ∈ S := hcT'.1
    have hcprop : a < c ∧ c ≤ b := hcT'.2
    have hcmax : ∀ s ∈ S, a < s → s ≤ b → s ≤ c := by
      intro s hsS has hsb
      exact Finset.le_max' T s (by simp [hT, hsS, has, hsb])
    have hnocut : ∀ s ∈ S, c < s → b < s := by
      intro s hsS hcs
      by_contra hsb
      push Not at hsb
      exact absurd (hcmax s hsS (lt_trans hcprop.1 hcs) hsb) (not_le.mpr hcs)
    have hDcb : f c - c = f b - b := by
      apply hS c b
      rintro ⟨s, hsS, hsI⟩
      have hcs : c < s ∧ s ≤ b := (mem_Ioc_min_max c b hcprop.2).mp hsI
      exact absurd hcs.2 (not_le.mpr (hnocut s hsS hcs.1))
    rcases lt_trichotomy (f a) (f b) with hfab | hfab | hfab
    · have hfc_le : f c ≤ f b := by linarith
      have hfc_gt : f a < f c := by
        by_contra hle
        push Not at hle
        set z := f a - (f b - b) with hz
        have hcz : c ≤ z := by linarith
        have hzb : z ≤ b := by linarith
        have hno : ¬ CutSep S c z := by
          rintro ⟨s, hsS, hsI⟩
          have hcs : c < s ∧ s ≤ z := (mem_Ioc_min_max c z hcz).mp hsI
          have := hnocut s hsS hcs.1
          linarith
        have hD := hS c z hno
        have hfz : f z = f a := by linarith
        have hza : z = a := f.injective hfz
        linarith
      refine ⟨f c, Finset.mem_image.mpr ⟨c, hcS, rfl⟩, ?_⟩
      rw [mem_Ioc_min_max (f a) (f b) hfab.le]
      exact ⟨hfc_gt, hfc_le⟩
    · exact absurd (f.injective hfab) (ne_of_lt hab)
    · by_cases hUne : (S.filter (fun s => s ≤ a)).Nonempty
      · set U := S.filter (fun s => s ≤ a) with hU
        have hUne' : U.Nonempty := by simpa [hU] using hUne
        set dd := U.max' hUne' with hd
        have hdU : dd ∈ U := Finset.max'_mem U hUne'
        have hdU' : dd ∈ S ∧ dd ≤ a := by simpa [hU] using hdU
        have hdS : dd ∈ S := hdU'.1
        have hda : dd ≤ a := hdU'.2
        have hdmax : ∀ s ∈ S, s ≤ a → s ≤ dd := by
          intro s hsS hsa
          exact Finset.le_max' U s (by simp [hU, hsS, hsa])
        have hno_da : ¬ CutSep S dd a := by
          rintro ⟨s, hsS, hsI⟩
          have hds : dd < s ∧ s ≤ a := (mem_Ioc_min_max dd a hda).mp hsI
          exact absurd (hdmax s hsS hds.2) (not_le.mpr hds.1)
        have hDda : f dd - dd = f a - a := hS dd a hno_da
        have hfd_le' : f dd ≤ f a := by linarith
        have hfd_gt : f b < f dd := by
          by_contra hle
          push Not at hle
          set z := f b - (f a - a) with hz
          have hdz : dd ≤ z := by linarith
          have hza : z ≤ a := by linarith
          have hno : ¬ CutSep S dd z := by
            rintro ⟨s, hsS, hsI⟩
            have hds : dd < s ∧ s ≤ z := (mem_Ioc_min_max dd z hdz).mp hsI
            have := hdmax s hsS (le_trans hds.2 hza)
            linarith
          have hD := hS dd z hno
          have hfz : f z = f b := by linarith
          have hzb : z = b := f.injective hfz
          linarith
        refine ⟨f dd, Finset.mem_image.mpr ⟨dd, hdS, rfl⟩, ?_⟩
        rw [mem_Ioc_min_max_of_le hfab.le]
        exact ⟨hfd_gt, hfd_le'⟩
      · have hno : ∀ s ∈ S, a < s := by
          intro s hsS
          by_contra h
          push Not at h
          exact hUne ⟨s, by simp [hsS, h]⟩
        set z := f b - (f a - a) with hz
        have hza : z < a := by linarith
        have hnoza : ¬ CutSep S z a := by
          rintro ⟨s, hsS, hsI⟩
          have hzs : z < s ∧ s ≤ a := (mem_Ioc_min_max z a hza.le).mp hsI
          exact absurd hzs.2 (not_le.mpr (hno s hsS))
        have hD := hS z a hnoza
        have hfz : f z = f b := by linarith
        have hzb : z = b := f.injective hfz
        linarith
  intro y y' hy
  set a := f.symm y with ha
  set b := f.symm y' with hb
  have hfa : f a = y := by simp [a]
  have hfb : f b = y' := by simp [b]
  rcases lt_trichotomy a b with hab | hab | hab
  · by_contra hne
    have hne' : f a - a ≠ f b - b := by
      intro h
      apply hne
      linarith
    have := key a b hab hne'
    exact hy (by simpa [hfa, hfb] using this)
  · rw [show y = y' by rw [← hfa, ← hfb, hab], hab]
  · by_contra hne
    have hne' : f b - b ≠ f a - a := by
      intro h
      apply hne
      linarith
    have := key b a hab hne'
    have hcomm : CutSep (S.image f) (f a) (f b) := (cutSep_comm _ _ _).mpr this
    exact hy (by simpa [hfa, hfb] using hcomm)

section Step
open Classical in
lemma step {d e : ℕ} {lam : Fin d → ℝ} {mu : Fin e → ℝ}
    {e' : Equiv.Perm ℝ} {Ce C : Finset ℝ} {A : Equiv.Perm ℝ} {n : ℤ}
    (hn : 2 ≤ n + 1)
    (hCe_trans : ∀ y y', ¬ CutSep Ce y y' → e' y - y = e' y' - y')
    (hCe_lat : ∀ c ∈ Ce, IsLat lam mu 2 c)
    (hdisp : ∀ x, IsLat lam mu 1 (e' x - x))
    (hC_lat : ∀ c ∈ C, IsLat lam mu n c)
    (hC_trans : ∀ y y', ¬ CutSep C y y' → A y - y = A y' - y') :
    ∃ C' : Finset ℝ,
      (∀ c ∈ C', IsLat lam mu (n + 1) c) ∧
      (∀ y y', ¬ CutSep C' y y' → (A * e') y - y = (A * e') y' - y') := by
  refine ⟨Ce ∪ C.image e'.symm, ?_, ?_⟩
  · intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact isLat_mono lam mu (by omega) (hCe_lat c hc)
    · rw [Finset.mem_image] at hc
      obtain ⟨dd, hdC, rfl⟩ := hc
      have hd : IsLat lam mu n dd := hC_lat dd hdC
      have hdisp' : IsLat lam mu 1 (dd - e'.symm dd) := by
        simpa using hdisp (e'.symm dd)
      have heq : e'.symm dd = dd - (dd - e'.symm dd) := by ring
      rw [heq]
      exact isLat_mono lam mu (by omega) (isLat_sub lam mu hd hdisp')
  · intro y y' hy
    have hyCe : ¬ CutSep Ce y y' := fun h => hy (cutSep_mono Finset.subset_union_left h)
    have hdy : e' y - y = e' y' - y' := hCe_trans y y' hyCe
    have hC : ¬ CutSep C (e' y) (e' y') := by
      rintro ⟨dd, hdC, hdI⟩
      set z := y + (dd - e' y) with hz
      have hzI : z ∈ Set.Ioc (min y y') (max y y') := by
        have hz' : z = dd - (e' y - y) := by rw [hz]; ring
        rw [Set.mem_Ioc] at hdI ⊢
        rcases le_total y y' with hle | hle
        · have hle' : e' y ≤ e' y' := by linarith
          simp only [min_eq_left hle, max_eq_right hle, min_eq_left hle',
            max_eq_right hle'] at hdI ⊢
          rw [hz']
          constructor <;> linarith
        · have hle' : e' y' ≤ e' y := by linarith
          simp only [min_eq_right hle, max_eq_left hle, min_eq_right hle',
            max_eq_left hle'] at hdI ⊢
          rw [hz']
          constructor <;> linarith
      have hnoz : ¬ CutSep Ce y z := fun h => hyCe (cutSep_mono_ioc hzI h)
      have hez : e' z = dd := by
        have h := hCe_trans y z hnoz
        linarith
      have hzmem : z ∈ C.image e'.symm := by
        rw [Finset.mem_image]
        exact ⟨dd, hdC, by rw [Equiv.symm_apply_eq]; exact hez.symm⟩
      exact hy ⟨z, Finset.mem_union_right _ hzmem, hzI⟩
    have hA := hC_trans (e' y) (e' y') hC
    change A (e' y) - y = A (e' y') - y'
    linarith
end Step

section Letters
variable (f g : Equiv.Perm ℝ)

/-- The generator map `0 ↦ f`, `1 ↦ g`. -/
noncomputable def gen (i : Fin 2) : Equiv.Perm ℝ := if i = 0 then f else g

/-- The permutation attached to a letter `(i, true) = i`, `(i, false) = i⁻¹`. -/
noncomputable def ltr (p : Fin 2 × Bool) : Equiv.Perm ℝ :=
  cond p.2 (gen f g p.1) (gen f g p.1)⁻¹

/-- The cut set of a single letter: `Sf`, `Sg` for generators, their `f`/`g`-images for inverses. -/
noncomputable def lcut (Sf Sg : Finset ℝ) (p : Fin 2 × Bool) : Finset ℝ :=
  if p.2 then (if p.1 = 0 then Sf else Sg)
  else (if p.1 = 0 then Sf.image f else Sg.image g)

end Letters

section LetterLemmas
variable {d e : ℕ} {lam : Fin d → ℝ} {mu : Fin e → ℝ}
  {f g : Equiv.Perm ℝ} {Sf Sg : Finset ℝ} {Df : ℝ → Fin d → ℤ} {Dg : ℝ → Fin e → ℤ}

lemma letter_trans
    (hSf : ∀ y y', ¬ CutSep Sf y y' → f y - y = f y' - y')
    (hSg : ∀ y y', ¬ CutSep Sg y y' → g y - y = g y' - y')
    (p : Fin 2 × Bool) :
    ∀ y y', ¬ CutSep (lcut f g Sf Sg p) y y' →
      ltr f g p y - y = ltr f g p y' - y' := by
  rintro y y' h
  obtain ⟨i, b⟩ := p
  cases b with
  | false =>
    by_cases hi : i = 0
    · have h' : ¬ CutSep (Sf.image f) y y' := by simpa [lcut, hi] using h
      simpa [ltr, gen, hi] using inv_translate_aux hSf y y' h'
    · have h' : ¬ CutSep (Sg.image g) y y' := by simpa [lcut, hi] using h
      simpa [ltr, gen, hi] using inv_translate_aux hSg y y' h'
  | true =>
    by_cases hi : i = 0
    · have h' : ¬ CutSep Sf y y' := by simpa [lcut, hi] using h
      simpa [ltr, gen, hi] using hSf y y' h'
    · have h' : ¬ CutSep Sg y y' := by simpa [lcut, hi] using h
      simpa [ltr, gen, hi] using hSg y y' h'

lemma letter_lat
    (hf : ∀ y, f y = y + ∑ i, (Df y i : ℝ) * lam i) (hfb : ∀ y i, |Df y i| ≤ 1)
    (hg : ∀ y, g y = y + ∑ j, (Dg y j : ℝ) * mu j) (hgb : ∀ y j, |Dg y j| ≤ 1)
    (hSf_lat : ∀ c ∈ Sf, ∃ a : Fin d → ℤ, (∀ i, |a i| ≤ 1) ∧
      c = ∑ i, (a i : ℝ) * lam i)
    (hSg_lat : ∀ c ∈ Sg, ∃ b : Fin e → ℤ, (∀ j, |b j| ≤ 1) ∧
      c = ∑ j, (b j : ℝ) * mu j)
    (p : Fin 2 × Bool) :
    ∀ c ∈ lcut f g Sf Sg p, IsLat lam mu 2 c := by
  rintro c hc
  obtain ⟨i, b⟩ := p
  cases b with
  | false =>
    by_cases hi : i = 0
    · have h' : c ∈ Sf.image f := by simpa [lcut, hi] using hc
      rw [Finset.mem_image] at h'
      obtain ⟨c₀, hc₀, rfl⟩ := h'
      obtain ⟨a₀, ha₀, rfl⟩ := hSf_lat c₀ hc₀
      set x₀ : ℝ := ∑ i, (a₀ i : ℝ) * lam i with hx₀
      have hx₀lat : IsLat lam mu 1 x₀ := isLat_lambda lam mu (by norm_num) ha₀
      have hdisp : IsLat lam mu 1 (f x₀ - x₀) := by
        have h := hf x₀
        have h' : f x₀ - x₀ = ∑ i, (Df x₀ i : ℝ) * lam i := by linarith
        rw [h']
        exact isLat_lambda lam mu (by norm_num) (hfb x₀)
      have heq : f x₀ = x₀ + (f x₀ - x₀) := by ring
      rw [heq]
      simpa using isLat_add lam mu hx₀lat hdisp
    · have h' : c ∈ Sg.image g := by simpa [lcut, hi] using hc
      rw [Finset.mem_image] at h'
      obtain ⟨c₀, hc₀, rfl⟩ := h'
      obtain ⟨b₀, hb₀, rfl⟩ := hSg_lat c₀ hc₀
      set x₀ : ℝ := ∑ j, (b₀ j : ℝ) * mu j with hx₀
      have hx₀lat : IsLat lam mu 1 x₀ := isLat_mu lam mu (by norm_num) hb₀
      have hdisp : IsLat lam mu 1 (g x₀ - x₀) := by
        have h := hg x₀
        have h' : g x₀ - x₀ = ∑ j, (Dg x₀ j : ℝ) * mu j := by linarith
        rw [h']
        exact isLat_mu lam mu (by norm_num) (hgb x₀)
      have heq : g x₀ = x₀ + (g x₀ - x₀) := by ring
      rw [heq]
      simpa using isLat_add lam mu hx₀lat hdisp
  | true =>
    by_cases hi : i = 0
    · have h' : c ∈ Sf := by simpa [lcut, hi] using hc
      obtain ⟨a, ha, rfl⟩ := hSf_lat c h'
      exact isLat_mono lam mu (by norm_num) (isLat_lambda lam mu (by norm_num) ha)
    · have h' : c ∈ Sg := by simpa [lcut, hi] using hc
      obtain ⟨b, hb, rfl⟩ := hSg_lat c h'
      exact isLat_mono lam mu (by norm_num) (isLat_mu lam mu (by norm_num) hb)

lemma isLat_fwd_disp {lam : Fin d → ℝ} {mu : Fin e → ℝ} {ee : Equiv.Perm ℝ}
    {D : ℝ → Fin d → ℤ} (he : ∀ y, ee y = y + ∑ i, (D y i : ℝ) * lam i)
    (hDb : ∀ y i, |D y i| ≤ 1) (x : ℝ) : IsLat lam mu 1 (ee x - x) := by
  have h : ee x - x = ∑ i, (D x i : ℝ) * lam i := by linarith [he x]
  rw [h]
  exact isLat_lambda lam mu (by norm_num) (hDb x)

lemma isLat_inv_disp {lam : Fin d → ℝ} {mu : Fin e → ℝ} {ee : Equiv.Perm ℝ}
    {D : ℝ → Fin d → ℤ} (he : ∀ y, ee y = y + ∑ i, (D y i : ℝ) * lam i)
    (hDb : ∀ y i, |D y i| ≤ 1) (x : ℝ) : IsLat lam mu 1 (ee.symm x - x) := by
  have h1 : ee (ee.symm x) = x := by simp
  have h : ee.symm x - x = -∑ i, (D (ee.symm x) i : ℝ) * lam i := by
    linarith [he (ee.symm x)]
  rw [h]
  exact isLat_neg lam mu (isLat_lambda lam mu (by norm_num) (hDb (ee.symm x)))

lemma isLat_fwd_disp_mu {lam : Fin d → ℝ} {mu : Fin e → ℝ} {ee : Equiv.Perm ℝ}
    {D : ℝ → Fin e → ℤ} (he : ∀ y, ee y = y + ∑ j, (D y j : ℝ) * mu j)
    (hDb : ∀ y j, |D y j| ≤ 1) (x : ℝ) : IsLat lam mu 1 (ee x - x) := by
  have h : ee x - x = ∑ j, (D x j : ℝ) * mu j := by linarith [he x]
  rw [h]
  exact isLat_mu lam mu (by norm_num) (hDb x)

lemma isLat_inv_disp_mu {lam : Fin d → ℝ} {mu : Fin e → ℝ} {ee : Equiv.Perm ℝ}
    {D : ℝ → Fin e → ℤ} (he : ∀ y, ee y = y + ∑ j, (D y j : ℝ) * mu j)
    (hDb : ∀ y j, |D y j| ≤ 1) (x : ℝ) : IsLat lam mu 1 (ee.symm x - x) := by
  have h1 : ee (ee.symm x) = x := by simp
  have h : ee.symm x - x = -∑ j, (D (ee.symm x) j : ℝ) * mu j := by
    linarith [he (ee.symm x)]
  rw [h]
  exact isLat_neg lam mu (isLat_mu lam mu (by norm_num) (hDb (ee.symm x)))

lemma letter_disp
    (hf : ∀ y, f y = y + ∑ i, (Df y i : ℝ) * lam i) (hfb : ∀ y i, |Df y i| ≤ 1)
    (hg : ∀ y, g y = y + ∑ j, (Dg y j : ℝ) * mu j) (hgb : ∀ y j, |Dg y j| ≤ 1)
    (p : Fin 2 × Bool) :
    ∀ x, IsLat lam mu 1 (ltr f g p x - x) := by
  intro x
  obtain ⟨i, b⟩ := p
  cases b with
  | false =>
    by_cases hi : i = 0
    · simpa [ltr, gen, hi] using isLat_inv_disp (mu := mu) hf hfb x
    · simpa [ltr, gen, hi] using isLat_inv_disp_mu (lam := lam) hg hgb x
  | true =>
    by_cases hi : i = 0
    · simpa [ltr, gen, hi] using isLat_fwd_disp (mu := mu) hf hfb x
    · simpa [ltr, gen, hi] using isLat_fwd_disp_mu (lam := lam) hg hgb x
end LetterLemmas

section ListMain
variable {d e : ℕ} {lam : Fin d → ℝ} {mu : Fin e → ℝ}
  {f g : Equiv.Perm ℝ} {Sf Sg : Finset ℝ} {Df : ℝ → Fin d → ℤ} {Dg : ℝ → Fin e → ℤ}

set_option maxHeartbeats 800000 in
-- the list induction over `step` needs more than the default 200000 heartbeats
lemma list_main
    (hf : ∀ y, f y = y + ∑ i, (Df y i : ℝ) * lam i) (hfb : ∀ y i, |Df y i| ≤ 1)
    (hg : ∀ y, g y = y + ∑ j, (Dg y j : ℝ) * mu j) (hgb : ∀ y j, |Dg y j| ≤ 1)
    (hSf : ∀ y y', ¬ CutSep Sf y y' → f y - y = f y' - y')
    (hSg : ∀ y y', ¬ CutSep Sg y y' → g y - y = g y' - y')
    (hSf_lat : ∀ c ∈ Sf, ∃ a : Fin d → ℤ, (∀ i, |a i| ≤ 1) ∧
      c = ∑ i, (a i : ℝ) * lam i)
    (hSg_lat : ∀ c ∈ Sg, ∃ b : Fin e → ℤ, (∀ j, |b j| ≤ 1) ∧
      c = ∑ j, (b j : ℝ) * mu j) :
    ∀ L : List (Fin 2 × Bool),
      ∃ C : Finset ℝ,
        (∀ c ∈ C, IsLat lam mu ((L.length : ℤ) + 1) c) ∧
        (∀ y y', ¬ CutSep C y y' →
          ((L.map (ltr f g)).prod) y - y = ((L.map (ltr f g)).prod) y' - y') := by
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    refine ⟨∅, ?_, ?_⟩
    · intro c hc; simp at hc
    · intro y y' _; simp
  | append_singleton L p ih =>
    obtain ⟨C, hC_lat, hC_trans⟩ := ih
    have hstep := step (lam := lam) (mu := mu) (e' := ltr f g p)
      (Ce := lcut f g Sf Sg p) (C := C) (A := (L.map (ltr f g)).prod)
      (n := (L.length : ℤ) + 1) (by omega)
      (letter_trans hSf hSg p) (letter_lat hf hfb hg hgb hSf_lat hSg_lat p)
      (letter_disp hf hfb hg hgb p) hC_lat hC_trans
    obtain ⟨C', hC'_lat, hC'_trans⟩ := hstep
    refine ⟨C', ?_, ?_⟩
    · intro c hc
      have hlen : (((L ++ [p]).length : ℤ) + 1) = ((L.length : ℤ) + 1 + 1) := by
        simp [List.length_append]
      rw [hlen]
      exact hC'_lat c hc
    · intro y y' hy
      have h := hC'_trans y y' hy
      simpa [List.map_append, List.prod_append] using h
end ListMain

/-- **The singularity bound.**  For two piecewise-translation permutations of `ℝ` whose cuts and
displacements are lattice combinations of `lam` and `mu` with coefficients in `{-1, 0, 1}`, and for
any word `w`, there is a finite set cutting `w(f, g)` into translation pieces, all of whose elements
are lattice combinations with coefficients bounded by `|w| + 1`. -/
theorem exists_lattice_cuts {d e : ℕ} (lam : Fin d → ℝ) (mu : Fin e → ℝ)
    (f g : Equiv.Perm ℝ) (Sf Sg : Finset ℝ)
    (Df : ℝ → Fin d → ℤ) (Dg : ℝ → Fin e → ℤ)
    (hf : ∀ y, f y = y + ∑ i, (Df y i : ℝ) * lam i) (hfb : ∀ y i, |Df y i| ≤ 1)
    (hg : ∀ y, g y = y + ∑ j, (Dg y j : ℝ) * mu j) (hgb : ∀ y j, |Dg y j| ≤ 1)
    (hSf : ∀ y y', ¬ CutSep Sf y y' → f y - y = f y' - y')
    (hSg : ∀ y y', ¬ CutSep Sg y y' → g y - y = g y' - y')
    (hSf_lat : ∀ c ∈ Sf, ∃ a : Fin d → ℤ, (∀ i, |a i| ≤ 1) ∧ c = ∑ i, (a i : ℝ) * lam i)
    (hSg_lat : ∀ c ∈ Sg, ∃ b : Fin e → ℤ, (∀ j, |b j| ≤ 1) ∧ c = ∑ j, (b j : ℝ) * mu j)
    (w : FreeGroup (Fin 2)) :
    ∃ C : Finset ℝ,
      (∀ c ∈ C, ∃ a : Fin d → ℤ, ∃ b : Fin e → ℤ,
        (∀ i, |a i| ≤ ((FreeGroup.toWord w).length : ℤ) + 1) ∧
          (∀ j, |b j| ≤ ((FreeGroup.toWord w).length : ℤ) + 1) ∧
          c = (∑ i, (a i : ℝ) * lam i) + (∑ j, (b j : ℝ) * mu j)) ∧
      (∀ y y', ¬ CutSep C y y' →
        FreeGroup.lift (fun i : Fin 2 => if i = 0 then f else g) w y - y
          = FreeGroup.lift (fun i : Fin 2 => if i = 0 then f else g) w y' - y') := by
  obtain ⟨C, hC_lat, hC_trans⟩ :=
    list_main (d := d) (e := e) (lam := lam) (mu := mu) (f := f) (g := g)
      (Sf := Sf) (Sg := Sg) (Df := Df) (Dg := Dg)
      hf hfb hg hgb hSf hSg hSf_lat hSg_lat (FreeGroup.toWord w)
  refine ⟨C, ?_, ?_⟩
  · intro c hc
    obtain ⟨a, b, ha, hb, hc⟩ := hC_lat c hc
    exact ⟨a, b, ha, hb, hc⟩
  · intro y y' hy
    have h := hC_trans y y' hy
    have hlift : FreeGroup.lift (fun i : Fin 2 => if i = 0 then f else g) w
        = ((FreeGroup.toWord w).map (ltr f g)).prod := by
      conv_lhs => rw [← FreeGroup.mk_toWord (x := w)]
      rw [FreeGroup.lift_mk]
      rfl
    rw [hlift]
    exact h

end CutBound

open CutBound

/-! ## The cut set of an exchange `mkIET1 lam π` -/

/-- **The cut set of `mkIET1 lam π`**: its cell starts, together with `1`.

`1` is needed because the displacement of the exchange is *not* constant across `1` (it drops from
the translation vector of the last cell to `0`), and `cellCuts` deliberately excludes `1`. -/
noncomputable def ietCuts {d : ℕ} (lam : Fin d → ℝ≥0) : Finset ℝ := insert 1 (cellCuts lam)

theorem mem_ietCuts {d : ℕ} (lam : Fin d → ℝ≥0) {c : ℝ} :
    c ∈ ietCuts lam ↔ c = 1 ∨ c ∈ cellCuts lam := Finset.mem_insert

/-- **The cuts of `mkIET1` are lattice vectors with coefficients in `{0, 1}`.** -/
theorem ietCuts_lat {d : ℕ} (lam : Fin d → ℝ≥0) (hl : (∑ i, lam i) = 1) {c : ℝ}
    (hc : c ∈ ietCuts lam) :
    ∃ a : Fin d → ℤ, (∀ i, |a i| ≤ 1) ∧ c = ∑ i, (a i : ℝ) * (lam i : ℝ) := by
  rcases (mem_ietCuts lam).mp hc with rfl | hc
  · refine ⟨fun _ => 1, fun i => by simp, ?_⟩
    have h1 : (∑ i, (((1 : ℤ) : ℝ)) * (lam i : ℝ)) = ∑ i, (lam i : ℝ) := by simp
    rw [h1]
    exact_mod_cast hl.symm
  · exact cellCuts_lattice lam hc

/-- The displacement of `mkIET1` at a point of `[0, 1)`. -/
theorem mkIET1_sub_eq_dispCoeff {d : ℕ} [NeZero d] (lam : Fin d → ℝ≥0)
    (π : Equiv.Perm (Fin d)) (hl : (∑ i, lam i) = 1) (y : ℝ) :
    (mkIET1 lam π hl).toEquiv y - y
      = ∑ i, (dispCoeff lam π 0 y i : ℝ) * (lam i : ℝ) := by
  have h2 : (mkIET1 lam π hl).toEquiv y = mkIETFun lam π 0 y := rfl
  have h := mkIETFun_sub_eq_sum_dispCoeff lam π 0 y
  rw [h2]
  linarith

/-- **Points of `[0, 1)` separated by a cell start have different cell indices.** -/
theorem cutSep_of_idx_lt {d : ℕ} [NeZero d] (lam : Fin d → ℝ≥0) (hl : (∑ i, lam i) = 1)
    {u v : ℝ} (hu : u ∈ Set.Ico (0 : ℝ) 1) (hv : v ∈ Set.Ico (0 : ℝ) 1)
    (hlt : idx lam u hu.1 < idx lam v hv.1) : CutSep (cellCuts lam) u v := by
  have hl' : (∑ i, (lam i : ℝ)) = 1 := by exact_mod_cast hl
  have hu' : u < upperEnd lam (idx lam u hu.1) :=
    lt_upperEnd_idx lam ⟨hu.1, by rw [hl']; exact hu.2⟩
  have hstep : upperEnd lam (idx lam u hu.1) ≤ leftEnd lam (idx lam v hv.1) :=
    upperEnd_le_leftEnd lam hlt
  have hmem : leftEnd lam (idx lam v hv.1) ∈ cellCuts lam := by
    refine (mem_cellCuts lam).mpr ⟨idx lam v hv.1, rfl, leftEnd_nonneg lam _, ?_⟩
    exact lt_of_le_of_lt (idx_mem lam v hv.1) hv.2
  have hle : leftEnd lam (idx lam v hv.1) ≤ v := idx_mem lam v hv.1
  have huv : u < v := by linarith
  exact Separated.of_lt_le hmem (by linarith) hle

/-- **Points of `[0, 1)` not separated by a cell start lie in the same cell.** -/
theorem idx_eq_of_not_sep {d : ℕ} [NeZero d] (lam : Fin d → ℝ≥0) (hl : (∑ i, lam i) = 1)
    {y y' : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 1) (hy' : y' ∈ Set.Ico (0 : ℝ) 1)
    (h : ¬ CutSep (cellCuts lam) y y') : idx lam y hy.1 = idx lam y' hy'.1 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h (cutSep_of_idx_lt lam hl hy hy' hlt)
  · exact h ((cutSep_comm (cellCuts lam) y' y).mp (cutSep_of_idx_lt lam hl hy' hy hlt))

/-- **`mkIET1` translates between points not separated by its cell starts** (within `[0, 1)`). -/
theorem mkIETFun_sub_eq_of_not_sep {d : ℕ} [NeZero d] (lam : Fin d → ℝ≥0)
    (π : Equiv.Perm (Fin d)) (hl : (∑ i, lam i) = 1) {y y' : ℝ}
    (hy : y ∈ Set.Ico (0 : ℝ) 1) (hy' : y' ∈ Set.Ico (0 : ℝ) 1)
    (h : ¬ CutSep (cellCuts lam) y y') :
    mkIETFun lam π 0 y - y = mkIETFun lam π 0 y' - y' := by
  have hl' : (∑ i, (lam i : ℝ)) = 1 := by exact_mod_cast hl
  have hyT : y ∈ Set.Ico (0 : ℝ) (0 + ∑ i, (lam i : ℝ)) := ⟨hy.1, by rw [hl']; simpa using hy.2⟩
  have hy'T : y' ∈ Set.Ico (0 : ℝ) (0 + ∑ i, (lam i : ℝ)) := ⟨hy'.1, by rw [hl']; simpa using hy'.2⟩
  have hidx : idx lam y hy.1 = idx lam y' hy'.1 := idx_eq_of_not_sep lam hl hy hy' h
  rw [mkIETFun_of_mem lam π 0 hyT, mkIETFun_of_mem lam π 0 hy'T]
  simp only [sub_zero, hidx]
  ring

/-- **The displacement of `mkIET1` is constant on the pieces cut by `ietCuts lam`.** -/
theorem ietCuts_trans {d : ℕ} [NeZero d] (lam : Fin d → ℝ≥0) (π : Equiv.Perm (Fin d))
    (hl : (∑ i, lam i) = 1) :
    ∀ y y' : ℝ, ¬ CutSep (ietCuts lam) y y' →
      (mkIET1 lam π hl).toEquiv y - y = (mkIET1 lam π hl).toEquiv y' - y' := by
  have hl' : (∑ i, (lam i : ℝ)) = 1 := by exact_mod_cast hl
  have hsub : cellCuts lam ⊆ ietCuts lam := fun c hc => Finset.mem_insert_of_mem hc
  intro y y' h
  have hcell : ¬ CutSep (cellCuts lam) y y' := fun hh => h (cutSep_mono hsub hh)
  have h0mem : (0 : ℝ) ∈ cellCuts lam := by
    refine (mem_cellCuts lam).mpr ⟨0, leftEnd_zero lam, le_refl 0, zero_lt_one⟩
  -- both points outside `[0, 1)`: the exchange is the identity
  have hleft : ∀ z : ℝ, z < 0 → (mkIET1 lam π hl).toEquiv z = z := by
    intro z hz
    have h2 : (mkIET1 lam π hl).toEquiv z = mkIETFun lam π 0 z := rfl
    rw [h2]
    exact mkIETFun_of_notMem lam π 0 (fun hcon => absurd hcon.1 (not_le.mpr hz))
  have hright : ∀ z : ℝ, 1 ≤ z → (mkIET1 lam π hl).toEquiv z = z := by
    intro z hz
    have h2 : (mkIET1 lam π hl).toEquiv z = mkIETFun lam π 0 z := rfl
    rw [h2]
    exact mkIETFun_of_notMem lam π 0 (fun hcon => absurd hcon.2 (by rw [hl']; simpa using hz))
  rcases lt_or_ge y 0 with hy | hy
  · rcases lt_or_ge y' 0 with hy' | hy'
    · rw [hleft y hy, hleft y' hy']; ring
    · exfalso
      have hyy' : y ≤ y' := by linarith
      exact h (Separated.of_lt_le (hsub h0mem) hy hy')
  · rcases lt_or_ge y 1 with hy1 | hy1
    · rcases lt_or_ge y' 0 with hy' | hy'
      · exfalso
        have hy'y : y' ≤ y := by linarith
        exact h (Separated.of_lt_le (hsub h0mem) hy' hy).symm
      · rcases lt_or_ge y' 1 with hy1' | hy1'
        · -- both in `[0, 1)`
          have h2 : (mkIET1 lam π hl).toEquiv y = mkIETFun lam π 0 y := rfl
          have h3 : (mkIET1 lam π hl).toEquiv y' = mkIETFun lam π 0 y' := rfl
          rw [h2, h3]
          exact mkIETFun_sub_eq_of_not_sep lam π hl ⟨hy, hy1⟩ ⟨hy', hy1'⟩ hcell
        · exfalso
          have hyy' : y ≤ y' := by linarith
          exact h (Separated.of_lt_le (Finset.mem_insert_self (1:ℝ) (cellCuts lam)) hy1 hy1')
    · rcases lt_or_ge y' 1 with hy1' | hy1'
      · exfalso
        have hy'y : y' ≤ y := by linarith
        exact h (Separated.of_lt_le (Finset.mem_insert_self (1:ℝ) (cellCuts lam)) hy1' hy1).symm
      · rw [hright y hy1, hright y' hy1']; ring

/-! ## Instantiation for the exchanges `mkIET1 lam π` and `mkIET1 mu σ` -/

/-- **The singularity bound for the paper's exchanges**: the cuts of `w(f, g)`, where
`f = mkIET1 lam π` and `g = mkIET1 mu σ`, are lattice combinations of the lengths with coefficients
`≤ |w| + 1`, and `w(f, g)` translates on the pieces they cut. -/
theorem evalWord_cuts {d e : ℕ} [NeZero d] [NeZero e] (lam : Fin d → ℝ≥0)
    (π : Equiv.Perm (Fin d)) (mu : Fin e → ℝ≥0) (σ : Equiv.Perm (Fin e))
    (hl : (∑ i, lam i) = 1) (hm : (∑ j, mu j) = 1) (w : FreeGroup Gen) :
    ∃ C : Finset ℝ,
      (∀ c ∈ C, ∃ a : Fin d → ℤ, ∃ b : Fin e → ℤ,
        (∀ i, |a i| ≤ ((FreeGroup.toWord w).length : ℤ) + 1) ∧
          (∀ j, |b j| ≤ ((FreeGroup.toWord w).length : ℤ) + 1) ∧
          c = (∑ i, (a i : ℝ) * (lam i : ℝ)) + (∑ j, (b j : ℝ) * (mu j : ℝ))) ∧
      (∀ y y', ¬ CutSep C y y' →
        (evalWord w (mkIET1 lam π hl) (mkIET1 mu σ hm)) y - y
          = (evalWord w (mkIET1 lam π hl) (mkIET1 mu σ hm)) y' - y') := by
  have hf : ∀ y, (mkIET1 lam π hl).toEquiv y
      = y + ∑ i, (dispCoeff lam π 0 y i : ℝ) * (lam i : ℝ) := by
    intro y
    have h := mkIET1_sub_eq_dispCoeff lam π hl y
    linarith
  have hg : ∀ y, (mkIET1 mu σ hm).toEquiv y
      = y + ∑ j, (dispCoeff mu σ 0 y j : ℝ) * (mu j : ℝ) := by
    intro y
    have h := mkIET1_sub_eq_dispCoeff mu σ hm y
    linarith
  obtain ⟨C, hC, hC'⟩ := CutBound.exists_lattice_cuts (d := d) (e := e)
    (fun i => (lam i : ℝ)) (fun j => (mu j : ℝ))
    (mkIET1 lam π hl).toEquiv (mkIET1 mu σ hm).toEquiv (ietCuts lam) (ietCuts mu)
    (dispCoeff lam π 0) (dispCoeff mu σ 0)
    hf (dispCoeff_abs_le_one lam π 0) hg (dispCoeff_abs_le_one mu σ 0)
    (fun y y' h => ietCuts_trans lam π hl y y' h) (fun y y' h => ietCuts_trans mu σ hm y y' h)
    (fun c hc => ietCuts_lat lam hl hc) (fun c hc => ietCuts_lat mu hm hc) w
  refine ⟨C, ?_, ?_⟩
  · intro c hc
    obtain ⟨a, b, ha, hb, hcab⟩ := hC c hc
    exact ⟨a, b, ha, hb, hcab⟩
  · intro y y' hy
    have h := hC' y y' hy
    rw [← evalWord_apply_coe] at h
    exact h

/-! ## The cell-length lemma

If `w(f, g)` is not the identity, then it moves some point of `[0, 1)`, and on the cell containing
that point it translates by a nonzero amount.  The cell's length is a difference of two cuts,
hence a nonzero lattice combination of the lengths with coefficients `≤ 2 |w| + 2`, and it is at
most the measure of the support.  This is the input of the Diophantine lower bound `C / |w| ^ c`. -/

/-- The point where `h` first differs from the identity, inside `[0, 1)`. -/
theorem exists_moved_point {d e : ℕ} [NeZero d] [NeZero e] (lam : Fin d → ℝ≥0)
    (π : Equiv.Perm (Fin d)) (mu : Fin e → ℝ≥0) (σ : Equiv.Perm (Fin e))
    (hl : (∑ i, lam i) = 1) (hm : (∑ j, mu j) = 1) (w : FreeGroup Gen)
    (hw : evalWord w (mkIET1 lam π hl) (mkIET1 mu σ hm) ≠ 1) :
    ∃ x ∈ Set.Ico (0 : ℝ) 1, (evalWord w (mkIET1 lam π hl) (mkIET1 mu σ hm)) x ≠ x := by
  by_contra hcon
  push Not at hcon
  apply hw
  refine IET.ext (fun x => ?_)
  by_cases hx : x ∈ Set.Ico (0 : ℝ) 1
  · exact hcon x hx
  · rw [(evalWord w (mkIET1 lam π hl) (mkIET1 mu σ hm)).isIET.eq_of_notMem hx]
    rfl

/-- **The cell-length lemma**: a nontrivial word has a translation cell whose length is a nonzero
lattice combination of the lengths with coefficients `≤ 2 |w| + 2`, and which is no longer than the
measure of the support of the word.

This is the input of the Diophantine lower bound: for a nontrivial `w` the length `ℓ` of the cell
satisfies `C / |w| ^ c ≤ ℓ ≤ Leb (supp w(f, g))`, which for small `ε` contradicts the decay of the
support obtained by iterating Lemma 2.10. -/
theorem exists_lattice_cell {d e : ℕ} [NeZero d] [NeZero e] (lam : Fin d → ℝ≥0)
    (π : Equiv.Perm (Fin d)) (mu : Fin e → ℝ≥0) (σ : Equiv.Perm (Fin e))
    (hl : (∑ i, lam i) = 1) (hm : (∑ j, mu j) = 1) (w : FreeGroup Gen)
    (hw : evalWord w (mkIET1 lam π hl) (mkIET1 mu σ hm) ≠ 1) :
    ∃ a : Fin d → ℤ, ∃ b : Fin e → ℤ,
      (∀ i, |a i| ≤ 2 * ((FreeGroup.toWord w).length : ℤ) + 2) ∧
        (∀ j, |b j| ≤ 2 * ((FreeGroup.toWord w).length : ℤ) + 2) ∧
        0 < (∑ i, (a i : ℝ) * (lam i : ℝ)) + (∑ j, (b j : ℝ) * (mu j : ℝ)) ∧
        (∑ i, (a i : ℝ) * (lam i : ℝ)) + (∑ j, (b j : ℝ) * (mu j : ℝ))
          ≤ unitMeas.real (wordSupp w (mkIET1 lam π hl) (mkIET1 mu σ hm)) := by
  classical
  set f := mkIET1 lam π hl with hfdef
  set g := mkIET1 mu σ hm with hgdef
  set h := evalWord w f g with hhdef
  obtain ⟨x, hx, hxne⟩ := exists_moved_point lam π mu σ hl hm w hw
  obtain ⟨C₀, hC₀_lat, hC₀_trans⟩ := evalWord_cuts lam π mu σ hl hm w
  -- add the two endpoints to the cut set
  set C : Finset ℝ := insert 0 (insert 1 C₀) with hCdef
  have h0C : (0 : ℝ) ∈ C := Finset.mem_insert_self _ _
  have h1C : (1:ℝ) ∈ C := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hC_lat : ∀ c ∈ C, ∃ a : Fin d → ℤ, ∃ b : Fin e → ℤ,
      (∀ i, |a i| ≤ ((FreeGroup.toWord w).length : ℤ) + 1) ∧
        (∀ j, |b j| ≤ ((FreeGroup.toWord w).length : ℤ) + 1) ∧
        c = (∑ i, (a i : ℝ) * (lam i : ℝ)) + (∑ j, (b j : ℝ) * (mu j : ℝ)) := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact ⟨0, 0, fun i => by simp only [Pi.zero_apply, abs_zero]; omega,
        fun j => by simp only [Pi.zero_apply, abs_zero]; omega, by simp⟩
    · rcases Finset.mem_insert.mp hc with rfl | hc
      · refine ⟨fun _ => 1, 0, fun i => by rw [abs_one]; omega,
          fun j => by simp only [Pi.zero_apply, abs_zero]; omega, ?_⟩
        have h1 : (∑ i, (lam i : ℝ)) = 1 := by exact_mod_cast hl
        simp only [Int.cast_one, one_mul, Pi.zero_apply, Int.cast_zero, zero_mul,
          Finset.sum_const_zero, add_zero]
        exact h1.symm
      · exact hC₀_lat c hc
  have hC_trans : ∀ y y' : ℝ, ¬ CutSep C y y' → h y - y = h y' - y' := by
    intro y y' hy'
    refine hC₀_trans y y' (fun hh => hy' ?_)
    obtain ⟨c, hc, hci⟩ := hh
    exact ⟨c, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc), hci⟩
  -- the two cuts around `x`, in the `Ioc` convention: the piece is `(c₁, c₂]`
  have hne₁ : (C.filter (fun c => c ≤ x)).Nonempty := ⟨0, by simp [h0C, hx.1]⟩
  set c₁ : ℝ := (C.filter (fun c => c ≤ x)).max' hne₁ with hc₁
  have hc₁mem : c₁ ∈ C.filter (fun c => c ≤ x) := by
    rw [hc₁]; exact Finset.max'_mem _ hne₁
  have hc₁C : c₁ ∈ C := (Finset.mem_filter.mp hc₁mem).1
  have hc₁_le : c₁ ≤ x := (Finset.mem_filter.mp hc₁mem).2
  have hc₁_nonneg : 0 ≤ c₁ := Finset.le_max' _ 0 (by simp [h0C, hx.1])
  have hne₂ : (C.filter (fun c => x < c)).Nonempty := ⟨1, by simp [h1C, hx.2]⟩
  set c₂ : ℝ := (C.filter (fun c => x < c)).min' hne₂ with hc₂
  have hc₂mem : c₂ ∈ C.filter (fun c => x < c) := by
    rw [hc₂]; exact Finset.min'_mem _ hne₂
  have hc₂C : c₂ ∈ C := (Finset.mem_filter.mp hc₂mem).1
  have hx_lt : x < c₂ := (Finset.mem_filter.mp hc₂mem).2
  have hc₂_le_one : c₂ ≤ 1 := by
    have hmem : (1:ℝ) ∈ C.filter (fun c => x < c) := Finset.mem_filter.mpr ⟨h1C, hx.2⟩
    have := Finset.min'_le _ _ hmem
    rwa [← hc₂] at this
  -- no cut lies strictly between the two
  have hno_cut : ∀ c ∈ C, ¬ (c₁ < c ∧ c < c₂) := by
    intro c hcC hlt
    rcases lt_or_ge x c with hxc | hxc
    · have hmem : c ∈ C.filter (fun c => x < c) := Finset.mem_filter.mpr ⟨hcC, hxc⟩
      have hle := Finset.min'_le _ _ hmem
      rw [← hc₂] at hle
      linarith [hlt.2]
    · have hmem : c ∈ C.filter (fun c => c ≤ x) := Finset.mem_filter.mpr ⟨hcC, hxc⟩
      have hle := Finset.le_max' _ _ hmem
      rw [← hc₁] at hle
      linarith [hlt.1]
  -- every point of `(c₁, c₂)` shares the displacement of `x`, which is nonzero
  have hδ : h x - x ≠ 0 := sub_ne_zero.mpr hxne
  have htrans : ∀ y ∈ Set.Ioo c₁ c₂, h y - y = h x - x := by
    intro y hy
    refine hC_trans y x (fun hsep => ?_)
    obtain ⟨c, hcC, hci⟩ := hsep
    rw [Set.mem_Ioc] at hci
    obtain ⟨h1, h2⟩ := hci
    have hy1 : c₁ < y := hy.1
    have hy2 : y < c₂ := hy.2
    -- `c` would lie strictly between `c₁` and `c₂`
    have hcl : c₁ < c := by
      have h1' : c₁ ≤ min y x := le_min (le_of_lt hy1) hc₁_le
      linarith
    have hcr : c < c₂ := by
      have h2' : max y x < c₂ := max_lt hy2 hx_lt
      linarith
    exact hno_cut c hcC ⟨hcl, hcr⟩
  have hsub : Set.Ioo c₁ c₂ ⊆ wordSupp w f g := by
    intro y hy
    have hyx : h y - y = h x - x := htrans y hy
    simp only [wordSupp, Set.mem_ofPred_eq]
    intro hcon
    exact hδ (by linarith)
  have hsplit : Set.Ioo c₁ c₂ ⊆ Set.Ico (0 : ℝ) 1 := fun y hy =>
    ⟨le_of_lt (lt_of_le_of_lt hc₁_nonneg hy.1), lt_of_lt_of_le hy.2 hc₂_le_one⟩
  -- the length is at most the measure of the support
  have hmono : unitMeas.real (wordSupp w f g) ≥ c₂ - c₁ := by
    have hfin : volume (wordSupp w f g ∩ Set.Ico (0 : ℝ) 1) ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
        (measure_mono Set.inter_subset_right)
    have h1 : unitMeas.real (wordSupp w f g)
        = volume.real (wordSupp w f g ∩ Set.Ico (0 : ℝ) 1) := by
      rw [unitMeas, Measure.real, Measure.real,
        Measure.restrict_apply (measurableSet_wordSupp w f g)]
    have h2 : volume.real (Set.Ioo c₁ c₂) = c₂ - c₁ := by
      rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
    have hsub' : Set.Ioo c₁ c₂ ⊆ wordSupp w f g ∩ Set.Ico (0 : ℝ) 1 :=
      fun y hy => ⟨hsub hy, hsplit hy⟩
    rw [h1, ← h2]
    exact ENNReal.toReal_mono hfin (measure_mono hsub')
  -- `c₂ - c₁` is the required lattice combination
  obtain ⟨a₂, b₂, ha₂, hb₂, hc₂eq⟩ := hC_lat c₂ hc₂C
  obtain ⟨a₁, b₁, ha₁, hb₁, hc₁eq⟩ := hC_lat c₁ hc₁C
  have hsum : (∑ i, ((a₂ i - a₁ i : ℤ) : ℝ) * (lam i : ℝ))
      + (∑ j, ((b₂ j - b₁ j : ℤ) : ℝ) * (mu j : ℝ)) = c₂ - c₁ := by
    rw [hc₂eq, hc₁eq]
    simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  refine ⟨fun i => a₂ i - a₁ i, fun j => b₂ j - b₁ j, ?_, ?_, ?_, ?_⟩
  · intro i
    have := ha₂ i
    have := ha₁ i
    have := abs_sub (a₂ i) (a₁ i)
    have := abs_nonneg (a₂ i)
    have := abs_nonneg (a₁ i)
    linarith
  · intro j
    have := hb₂ j
    have := hb₁ j
    have := abs_sub (b₂ j) (b₁ j)
    have := abs_nonneg (b₂ j)
    have := abs_nonneg (b₁ j)
    linarith
  · rw [hsum]; linarith
  · rw [hsum]; exact hmono

/-! ## The support of a word is a finite union of intervals

Lemma 2.9 (`exists_uniform_birkhoff`) needs the support of `w(f, g)` presented as a finite union of
half-open intervals. -/

/-- **The support of `w(f, g)` is a finite union of half-open intervals**, with endpoints among the
cuts of the singularity bound together with `0` and `1`. -/
theorem isFiniteUnionIntervals_wordSupp {d e : ℕ} [NeZero d] [NeZero e] (lam : Fin d → ℝ≥0)
    (π : Equiv.Perm (Fin d)) (mu : Fin e → ℝ≥0) (σ : Equiv.Perm (Fin e))
    (hl : (∑ i, lam i) = 1) (hm : (∑ j, mu j) = 1) (w : FreeGroup Gen) :
    IsFiniteUnionIntervals (wordSupp w (mkIET1 lam π hl) (mkIET1 mu σ hm)) := by
  classical
  obtain ⟨C₀, -, hC₀⟩ := evalWord_cuts lam π mu σ hl hm w
  refine isFiniteUnionIntervals_ne_id (h := evalWord w (mkIET1 lam π hl) (mkIET1 mu σ hm))
    (C := insert 0 (insert 1 C₀)) ?_ (by simp) (by simp)
  intro y y' hy'
  refine hC₀ y y' (fun hsep => hy' ?_)
  obtain ⟨c, hc, hci⟩ := hsep
  exact ⟨c, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc), hci⟩
