/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.FreeGroup.Commensurable
public import IETFree.IET

/-!
# Measure-theoretic tools for Section 2

Lebesgue measure on `[0, 1)`, its behaviour under exchanges, the words in two generators used to
build small supports, and the toolbox for Lemma 2.10.

It is imported by `Irreducible.lean`, where it keeps that file to a readable length (the definitions
and lemmas that the statements and proofs there use, including `unitMeas` and its API,
`evalWord`/`wordSupp` and the supports of commutators, and the averaged Birkhoff estimate
`sum_inter_le` behind display
(2.3) of the paper).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal commutatorElement
open IntervalExchange.IET

namespace IntervalExchange.Pair

/-! ## Words in two generators -/

-- `⁅a, b⁆` is Mathlib's commutator `a * b * a⁻¹ * b⁻¹` (`commutatorElement`).  The paper's
-- `[a, b] = a⁻¹ * b⁻¹ * a * b` is `⁅a⁻¹, b⁻¹⁆`; see `commutatorElement_inv_inv_eq_one_iff` and the
-- support lemmas below.

/-- The two generators. -/
abbrev Gen : Type := Fin 2

/-- The first generator `x`. -/
def genX : FreeGroup Gen := FreeGroup.of 0

/-- The second generator `y`. -/
def genY : FreeGroup Gen := FreeGroup.of 1

/-- Evaluation of a word in the two generators at a pair of exchanges. -/
def evalWord (w : FreeGroup Gen) (f g : IET 0 1) : IET 0 1 :=
  (FreeGroup.lift (fun i : Gen => if i = 0 then f else g)) w

/-- **The evaluation is a homomorphism** in the word. -/
@[simp] theorem evalWord_one (f g : IET 0 1) : evalWord 1 f g = 1 := (rfl)

@[simp] theorem evalWord_mul (u v : FreeGroup Gen) (f g : IET 0 1) :
    evalWord (u * v) f g = evalWord u f g * evalWord v f g :=
  map_mul _ u v

@[simp] theorem evalWord_inv (u : FreeGroup Gen) (f g : IET 0 1) :
    evalWord u⁻¹ f g = (evalWord u f g)⁻¹ :=
  map_inv _ u

@[simp] theorem evalWord_pow (u : FreeGroup Gen) (n : ℕ) (f g : IET 0 1) :
    evalWord (u ^ n) f g = evalWord u f g ^ n :=
  map_pow _ u n

/-- **The two generators evaluate to the two exchanges.** -/
@[simp] theorem evalWord_genX (f g : IET 0 1) : evalWord genX f g = f := (rfl)

@[simp] theorem evalWord_genY (f g : IET 0 1) : evalWord genY f g = g := (rfl)

/-- The evaluation of a conjugate by `f`. -/
theorem evalWord_conjX (u : FreeGroup Gen) (f g : IET 0 1) :
    evalWord (genX⁻¹ * u * genX) f g = f⁻¹ * evalWord u f g * f := by
  rw [evalWord_mul, evalWord_mul, evalWord_inv, evalWord_genX]

/-- The evaluation of a conjugate by `g`. -/
theorem evalWord_conjY (u : FreeGroup Gen) (f g : IET 0 1) :
    evalWord (genY⁻¹ * u * genY) f g = g⁻¹ * evalWord u f g * g := by
  rw [evalWord_mul, evalWord_mul, evalWord_inv, evalWord_genY]

/-- **The support of `w(f,g)`, as a subset of `ℝ`.** -/
def wordSupp (w : FreeGroup Gen) (f g : IET 0 1) : Set ℝ := {x : ℝ | (evalWord w f g) x ≠ x}

/-! ## Nontriviality of `[y, x^q]`

The word `[y, x^q]` is nontrivial for `q ≠ 0`.  This is not the centralizer theorem behind Lemma
  2.7:
a single representation of `F_2` suffices, namely `x ↦ (t ↦ t + 1)` and `y ↦ (t ↦ 2t)` on `ℝ`,
under which `[y, x^q]` acts as the translation `t ↦ t + q/2`. -/

/-- The translation `x ↦ x + 1` of `ℝ`, Mathlib's `Equiv.addRight`. -/
def shiftPerm : Equiv.Perm ℝ := Equiv.addRight 1

/-- The dilation `x ↦ 2 * x` of `ℝ`, Mathlib's `Equiv.mulLeft₀`. -/
noncomputable def scalePerm : Equiv.Perm ℝ := Equiv.mulLeft₀ 2 (by norm_num)

theorem shiftPerm_apply (x : ℝ) : shiftPerm x = x + 1 := by
  rw [shiftPerm, Equiv.coe_addRight]

theorem scalePerm_apply (x : ℝ) : scalePerm x = 2 * x := by
  rw [scalePerm, Equiv.mulLeft₀_apply]

theorem scalePerm_symm_apply (x : ℝ) : scalePerm⁻¹ x = x / 2 := by
  simp [scalePerm]
  ring

theorem shiftPerm_pow (k : ℕ) (x : ℝ) : ((shiftPerm ^ k : Equiv.Perm ℝ)) x = x + k := by
  induction k generalizing x with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, shiftPerm_apply]
    push_cast
    ring

/-- `⁅a⁻¹, b⁻¹⁆ = 1` exactly when `⁅a, b⁆ = 1`, i.e. when `a` and `b` commute.  This is the
bridge between Mathlib's commutator and the paper's `[a, b] = a⁻¹b⁻¹ab = ⁅a⁻¹, b⁻¹⁆`. -/
theorem commutatorElement_inv_inv_eq_one_iff {G : Type*} [Group G] (a b : G) :
    ⁅a⁻¹, b⁻¹⁆ = 1 ↔ ⁅a, b⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm, commutatorElement_eq_one_iff_mul_comm]
  constructor
  · intro h
    have h2 : (a⁻¹ * b⁻¹)⁻¹ = (b⁻¹ * a⁻¹)⁻¹ := by rw [h]
    rw [mul_inv_rev, mul_inv_rev, inv_inv, inv_inv] at h2
    exact h2.symm
  · intro h
    have h2 : (a * b)⁻¹ = (b * a)⁻¹ := by rw [h]
    rw [mul_inv_rev, mul_inv_rev] at h2
    exact h2.symm

/-- **The word of Lemma 2.8 is nontrivial**: the paper's commutator of `g` with the `q`-th iterate
of `f`, `[g, f^q] = g⁻¹(f^q)⁻¹gf^q = ⁅g⁻¹, (f^q)⁻¹⁆`.  It is checked on the two model permutations
`x ↦ x + 1` and `y ↦ 2x`, where it is the translation by `q/2`. -/
theorem commutator_inv_genY_genX_pow_ne_one {q : ℕ} (hq : q ≠ 0) :
    ⁅genY⁻¹, (genX ^ q)⁻¹⁆ ≠ 1 := by
  intro hcon
  set φ : FreeGroup Gen →* Equiv.Perm ℝ :=
    FreeGroup.lift (fun i : Gen => if i = 0 then shiftPerm else scalePerm) with hφ
  have hX : φ genX = shiftPerm := by
    rw [hφ, genX]
    simp
  have hY : φ genY = scalePerm := by
    rw [hφ, genY]
    simp
  -- the conjugate of the iterate fixes each point up to `q / 2`
  have hfun (x : ℝ) :
      ((scalePerm⁻¹ * (shiftPerm ^ q)⁻¹ * scalePerm * (shiftPerm ^ q) : Equiv.Perm ℝ)) x
        = x + (q : ℝ) / 2 := by
    have hi (k : ℕ) (y : ℝ) : ((shiftPerm ^ k : Equiv.Perm ℝ))⁻¹ y = y - k := by
      have h1 : ((shiftPerm ^ k : Equiv.Perm ℝ)) (y - k) = y := by
        rw [shiftPerm_pow]
        ring
      calc ((shiftPerm ^ k : Equiv.Perm ℝ))⁻¹ y
          = ((shiftPerm ^ k : Equiv.Perm ℝ))⁻¹ (((shiftPerm ^ k : Equiv.Perm ℝ)) (y - k)) := by
            rw [h1]
        _ = y - k := Equiv.symm_apply_apply _ _
    simp only [Equiv.Perm.mul_apply, shiftPerm_pow, hi, scalePerm_apply, scalePerm_symm_apply]
    ring
  have hval : ((φ ⁅genY⁻¹, (genX ^ q)⁻¹⁆) : Equiv.Perm ℝ) 0 = (q : ℝ) / 2 := by
    simp only [commutatorElement_def, map_mul, map_inv, inv_inv, map_pow, hX, hY]
    simpa using hfun 0
  rw [hcon, map_one] at hval
  simp only [Equiv.Perm.coe_one, id_eq] at hval
  exact hq (Nat.cast_eq_zero.mp (by linarith : (q : ℝ) = 0))

/-- **The support of a piecewise-translation bijection of `ℝ` is a finite union of half-open
intervals.**  If `h` is an exchange on `[0, 1)` that translates between points not separated by the
finite set `C`, and `C` contains `0` and `1`, then `{x | h x ≠ x}` is a finite union of intervals
`[a, b)` with `a, b ∈ C`.

The cells are the *left-closed* ones `[c₁, c₂)` with `c₁` the largest element of `C` that is `≤ x`
and `c₂` the least element of `C` that is `> x`: two points in such a cell are never separated (the
right endpoint is excluded), so they share `h`'s displacement, which is therefore the displacement
at `c₁`. -/
theorem isFiniteUnionIntervals_ne_id {h : IET 0 1} {C : Finset ℝ}
    (hC : ∀ y y', ¬ Separated C y y' → h y - y = h y' - y')
    (h0C : (0 : ℝ) ∈ C) (h1C : (1 : ℝ) ∈ C) :
    IsFiniteUnionIntervals {x : ℝ | h x ≠ x} := by
  refine ⟨(C ×ˢ C).filter (fun p : ℝ × ℝ => p.1 < p.2 ∧
    (∀ c ∈ C, ¬ (p.1 < c ∧ c < p.2)) ∧ h p.1 - p.1 ≠ 0), fun x => ?_⟩
  constructor
  · -- a moved point lies in a displaced cell, and `[0, 1)` contains it
    intro hx
    have hxI : x ∈ Set.Ico (0:ℝ) 1 := by
      by_contra hcon
      exact hx (h.isIET.eq_of_notMem hcon)
    have hne1 : (C.filter (fun c => c ≤ x)).Nonempty :=
      ⟨0, Finset.mem_filter.mpr ⟨h0C, hxI.1⟩⟩
    set c₁ : ℝ := (C.filter (fun c => c ≤ x)).max' hne1 with hc₁def
    have hc₁mem : c₁ ∈ C.filter (fun c => c ≤ x) := by
      rw [hc₁def]; exact Finset.max'_mem _ hne1
    have hc₁C : c₁ ∈ C := (Finset.mem_filter.mp hc₁mem).1
    have hc₁le : c₁ ≤ x := (Finset.mem_filter.mp hc₁mem).2
    have hne2 : (C.filter (fun c => x < c)).Nonempty :=
      ⟨1, Finset.mem_filter.mpr ⟨h1C, hxI.2⟩⟩
    set c₂ : ℝ := (C.filter (fun c => x < c)).min' hne2 with hc₂def
    have hc₂mem : c₂ ∈ C.filter (fun c => x < c) := by
      rw [hc₂def]; exact Finset.min'_mem _ hne2
    have hc₂C : c₂ ∈ C := (Finset.mem_filter.mp hc₂mem).1
    have hxc₂ : x < c₂ := (Finset.mem_filter.mp hc₂mem).2
    -- the displacement at `x` is that of the left end of its cell
    have hdisp : h x - x = h c₁ - c₁ := by
      refine hC x c₁ (fun hsep => ?_)
      obtain ⟨c, hcC, hci⟩ := hsep
      obtain ⟨-, hci2⟩ := (mem_Ioc_min_max_of_le hc₁le).mp hci
      have hle : c ≤ c₁ :=
        Finset.le_max' _ c (Finset.mem_filter.mpr ⟨hcC, hci2⟩)
      exact absurd ((mem_Ioc_min_max_of_le hc₁le).mp hci).1 (not_lt.mpr hle)
    refine ⟨(c₁, c₂), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc₁C, hc₂C⟩, ?_, ?_, ?_⟩
      · exact lt_of_le_of_lt hc₁le hxc₂
      · rintro c hcC ⟨h1, h2⟩
        rcases lt_or_ge x c with hxc | hxc
        · have hle : c₂ ≤ c := by
            rw [hc₂def]
            exact Finset.min'_le _ c (Finset.mem_filter.mpr ⟨hcC, hxc⟩)
          linarith
        · have hle : c ≤ c₁ := by
            rw [hc₁def]
            exact Finset.le_max' _ c (Finset.mem_filter.mpr ⟨hcC, hxc⟩)
          linarith
      · change h c₁ - c₁ ≠ 0
        rw [← hdisp]
        exact sub_ne_zero.mpr hx
    · exact ⟨hc₁le, hxc₂⟩
  · -- conversely, a point of a displaced cell is moved
    intro hx
    obtain ⟨⟨p₁, p₂⟩, hp, hxp⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_product, Set.mem_Ico] at hp hxp
    obtain ⟨⟨hp₁C, hp₂C⟩, hp₁₂, hcons, hdisp⟩ := hp
    obtain ⟨hx₁, hx₂⟩ := hxp
    have hsame : h x - x = h p₁ - p₁ := by
      refine hC x p₁ (fun hsep => ?_)
      obtain ⟨c, hcC, hci⟩ := hsep
      obtain ⟨hci1, hci2⟩ := (mem_Ioc_min_max_of_le hx₁).mp hci
      exact hcons c hcC ⟨hci1, lt_of_le_of_lt hci2 hx₂⟩
    simp only [Set.mem_ofPred_eq]
    intro hone
    have hzero : h x - x = 0 := by rw [hone]; ring
    rw [hsame] at hzero
    exact hdisp hzero

/-! ## Tools for Lemma 2.10

The support of a commutator, the length of the words produced, and the averaged Birkhoff estimate of
the paper's display (2.3).
-/

/-- The set where a measurable function differs from the identity is measurable. -/
theorem measurableSet_ne_id {f : ℝ → ℝ} (hf : Measurable f) : MeasurableSet {x | f x ≠ x} := by
  have hclosed : IsClosed {p : ℝ × ℝ | p.1 = p.2} := isClosed_eq continuous_fst continuous_snd
  have h : {x | f x ≠ x} = (fun x => (f x, x)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2}ᶜ := by
    ext x
    simp
  rw [h]
  exact hclosed.isOpen_compl.measurableSet.preimage (hf.prod measurable_id)

/-- The support of a word is measurable. -/
theorem measurableSet_wordSupp (u : FreeGroup Gen) (f g : IET 0 1) :
    MeasurableSet (wordSupp u f g) :=
  measurableSet_ne_id (measurable (evalWord u f g))

end IntervalExchange.Pair

-- the free-group lemmas below are outside `IntervalExchange.Pair` but use its two generators
open IntervalExchange.Pair

namespace FreeGroup

/-- The length of a commutator is at most twice the sum of the lengths. -/
theorem norm_commutatorElement_le (a b : FreeGroup Gen) :
    norm ⁅a, b⁆ ≤ 2 * norm a + 2 * norm b := by
  rw [commutatorElement_def]
  have h1 : norm (a * b * a⁻¹ * b⁻¹) ≤ norm (a * b * a⁻¹) + norm b⁻¹ :=
    norm_mul_le _ _
  have h2 : norm (a * b * a⁻¹) ≤ norm (a * b) + norm a⁻¹ :=
    norm_mul_le _ _
  have h3 : norm (a * b) ≤ norm a + norm b :=
    norm_mul_le _ _
  simp only [norm_inv_eq] at h1 h2
  omega

/-- The length of a conjugate `x⁻¹ * u * x` by `genX` is at most `norm u + 2`. -/
theorem norm_conjX_le (u : FreeGroup Gen) :
    norm (genX⁻¹ * u * genX) ≤ norm u + 2 := by
  have h := norm_conj_le (g := genX⁻¹) u
  have hx : norm genX⁻¹ = 1 := by
    rw [norm_inv_eq]
    exact norm_of 0
  rw [inv_inv, hx] at h
  simpa using h

/-- The length of a conjugate `y⁻¹ * u * y` by `genY` is at most `norm u + 2`. -/
theorem norm_conjY_le (u : FreeGroup Gen) :
    norm (genY⁻¹ * u * genY) ≤ norm u + 2 := by
  have h := norm_conj_le (g := genY⁻¹) u
  have hy : norm genY⁻¹ = 1 := by
    rw [norm_inv_eq]
    exact norm_of 1
  rw [inv_inv, hy] at h
  simpa using h

/-- The length of a conjugate of `u` by a power of `genX`. -/
theorem norm_conjX_pow_le (u : FreeGroup Gen) (i : ℕ) :
    norm ((genX ^ i)⁻¹ * u * (genX ^ i)) ≤ norm u + 2 * i := by
  have h := norm_conj_le (g := (genX ^ i)⁻¹) u
  have hx : norm (genX ^ i)⁻¹ = i := by
    rw [norm_inv_eq]
    exact norm_of_pow 0 i
  rw [inv_inv, hx] at h
  simpa using h

end FreeGroup

namespace IntervalExchange.Pair

/-- A conjugate of a nontrivial word is nontrivial. -/
theorem conj_ne_one {u : FreeGroup Gen} (hu : u ≠ 1) (a : FreeGroup Gen) : a⁻¹ * u * a ≠ 1 := by
  intro h
  apply hu
  have h' := congrArg (fun t => a * t * a⁻¹) h
  simpa [mul_assoc] using h'

/-! ## Supports of conjugates and of commutators -/

/-- The evaluation of a conjugate. -/
theorem evalWord_conj_pow (u : FreeGroup Gen) (i : ℕ) (f g : IET 0 1) :
    evalWord ((genX ^ i)⁻¹ * u * (genX ^ i)) f g
      = (f ^ i)⁻¹ * evalWord u f g * (f ^ i) := by
  rw [evalWord_mul, evalWord_mul, evalWord_inv, evalWord_pow, evalWord_genX]

/-- **The support of a conjugate by `f^i` is the preimage of the support.** -/
theorem wordSupp_conj_pow (u : FreeGroup Gen) (i : ℕ) (f g : IET 0 1) :
    wordSupp ((genX ^ i)⁻¹ * u * (genX ^ i)) f g = ⇑(f ^ i) ⁻¹' wordSupp u f g := by
  ext x
  simp only [wordSupp, Set.mem_ofPred_eq, Set.mem_preimage, evalWord_conj_pow, mul_apply]
  constructor
  · intro h hx
    exact h (by rw [hx, symm_apply_apply])
  · intro h hx
    exact h (by simpa using congrArg (⇑(f ^ i)) hx)

/-- If `x` is outside `A ∪ φ⁻¹A ∪ ψ⁻¹A` (with `A` the intersection of the supports), the paper's
commutator `[φ, ψ] = φ⁻¹ψ⁻¹φψ = ⁅φ⁻¹, ψ⁻¹⁆` fixes `x`. -/
theorem commutator_inv_apply_eq (φ ψ : IET 0 1) {x : ℝ}
    (h₁ : φ x = x ∨ ψ x = x) (h₂ : φ (φ x) = φ x ∨ ψ (φ x) = φ x)
    (h₃ : φ (ψ x) = ψ x ∨ ψ (ψ x) = ψ x) : (⁅φ⁻¹, ψ⁻¹⁆) x = x := by
  have key (θ : IET 0 1) (z : ℝ) (h : θ z = z) : θ⁻¹ z = z := by
    have h1 : θ⁻¹ (θ z) = z := symm_apply_apply θ z
    rwa [h] at h1
  simp only [commutatorElement_def, inv_inv, mul_apply]
  rcases h₁ with hφ | hψ
  · rcases h₃ with h | h
    · calc φ⁻¹ (ψ⁻¹ (φ (ψ x))) = φ⁻¹ (ψ⁻¹ (ψ x)) := by rw [h]
        _ = φ⁻¹ x := by rw [symm_apply_apply]
        _ = x := key φ x hφ
    · have hψx : ψ x = x := ψ.injective h
      calc φ⁻¹ (ψ⁻¹ (φ (ψ x))) = φ⁻¹ (ψ⁻¹ (φ x)) := by rw [hψx]
        _ = φ⁻¹ (ψ⁻¹ x) := by rw [hφ]
        _ = φ⁻¹ x := by rw [key ψ x hψx]
        _ = x := key φ x hφ
  · rcases h₂ with h | h
    · have hφx : φ x = x := φ.injective h
      calc φ⁻¹ (ψ⁻¹ (φ (ψ x))) = φ⁻¹ (ψ⁻¹ (φ x)) := by rw [hψ]
        _ = φ⁻¹ (ψ⁻¹ x) := by rw [hφx]
        _ = φ⁻¹ x := by rw [key ψ x hψ]
        _ = x := key φ x hφx
    · calc φ⁻¹ (ψ⁻¹ (φ (ψ x))) = φ⁻¹ (ψ⁻¹ (φ x)) := by rw [hψ]
        _ = φ⁻¹ (φ x) := by rw [key ψ (φ x) h]
        _ = x := symm_apply_apply φ x

/-- **The support of `[φ, ψ] = ⁅φ⁻¹, ψ⁻¹⁆` is contained in `A ∪ φ⁻¹A ∪ ψ⁻¹A`**, where `A` is the
intersection of the two supports. -/
theorem commutator_inv_supp_subset (φ ψ : IET 0 1) :
    {x : ℝ | (⁅φ⁻¹, ψ⁻¹⁆) x ≠ x} ⊆
      ({x | φ x ≠ x} ∩ {x | ψ x ≠ x}) ∪ (⇑φ ⁻¹' ({x | φ x ≠ x} ∩ {x | ψ x ≠ x}))
        ∪ (⇑ψ ⁻¹' ({x | φ x ≠ x} ∩ {x | ψ x ≠ x})) := by
  intro x hx
  set A : Set ℝ := {x | φ x ≠ x} ∩ {x | ψ x ≠ x} with hA
  by_cases h1 : x ∈ A
  · exact Or.inl (Or.inl h1)
  · by_cases h2 : φ x ∈ A
    · exact Or.inl (Or.inr h2)
    · by_cases h3 : ψ x ∈ A
      · exact Or.inr h3
      · have e1 : φ x = x ∨ ψ x = x := by
          by_contra h
          push Not at h
          exact h1 ⟨h.1, h.2⟩
        have e2 : φ (φ x) = φ x ∨ ψ (φ x) = φ x := by
          by_contra h
          push Not at h
          exact h2 ⟨h.1, h.2⟩
        have e3 : φ (ψ x) = ψ x ∨ ψ (ψ x) = ψ x := by
          by_contra h
          push Not at h
          exact h3 ⟨h.1, h.2⟩
        exact absurd (commutator_inv_apply_eq φ ψ e1 e2 e3) hx

/-! ## The averaged Birkhoff estimate -/

/-- The support of a conjugate `θ⁻¹ h θ` is the preimage of the support of `h`. -/
theorem supp_conj (θ h : IET 0 1) :
    {x : ℝ | (θ⁻¹ * h * θ) x ≠ x} = ⇑θ ⁻¹' {x : ℝ | h x ≠ x} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, mul_apply]
  constructor
  · intro hx hc
    exact hx (by rw [hc, symm_apply_apply])
  · intro hx hc
    exact hx (by simpa using congrArg (⇑θ) hc)

/-- **The measure of the support of a commutator**: three times the measure of the intersection of
the supports. -/
theorem unitMeas_real_supp_commutator_inv_le (φ ψ : IET 0 1) :
    unitMeas.real {x : ℝ | (⁅φ⁻¹, ψ⁻¹⁆) x ≠ x}
      ≤ 3 * unitMeas.real ({x | φ x ≠ x} ∩ {x | ψ x ≠ x}) := by
  set A : Set ℝ := {x | φ x ≠ x} ∩ {x | ψ x ≠ x} with hAdef
  have hA : MeasurableSet A :=
    (measurableSet_ne_id (measurable φ)).inter (measurableSet_ne_id (measurable ψ))
  have h1 : unitMeas.real {x : ℝ | (⁅φ⁻¹, ψ⁻¹⁆) x ≠ x}
      ≤ unitMeas.real (A ∪ ⇑φ ⁻¹' A ∪ ⇑ψ ⁻¹' A) :=
    measureReal_mono (commutator_inv_supp_subset φ ψ)
  have h2 : unitMeas.real (A ∪ ⇑φ ⁻¹' A ∪ ⇑ψ ⁻¹' A)
      ≤ unitMeas.real A + unitMeas.real (⇑φ ⁻¹' A) + unitMeas.real (⇑ψ ⁻¹' A) := by
    have h := measureReal_union_le (μ := unitMeas) (A ∪ ⇑φ ⁻¹' A) (⇑ψ ⁻¹' A)
    have h' := measureReal_union_le (μ := unitMeas) A (⇑φ ⁻¹' A)
    linarith
  have h3 : unitMeas.real (⇑φ ⁻¹' A) = unitMeas.real A := unitMeas_real_preimage φ hA
  have h4 : unitMeas.real (⇑ψ ⁻¹' A) = unitMeas.real A := unitMeas_real_preimage ψ hA
  linarith

/-- **The averaged Birkhoff estimate**: the sum over `i < N` of the measures of `A ∩ f^{-i} S₀`
is at
most `2 ε N μ(A)`.  This is the paper's integration of the display (2.2) over `A`. -/
theorem sum_inter_le (f : IET 0 1) {A S₀ : Set ℝ} (hA : MeasurableSet A) (hS₀ : MeasurableSet S₀)
    {N : ℕ} (hN : 0 < N) {ε : ℝ}
    (hbirk : ∀ x ∈ Set.Ico (0 : ℝ) 1, (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N,
      S₀.indicator (fun _ => (1 : ℝ)) ((f ^ i) x) ≤ 2 * ε) :
    ∑ i ∈ Finset.range N, unitMeas.real (A ∩ ⇑(f ^ i) ⁻¹' S₀) ≤ 2 * ε * N * unitMeas.real A := by
  set ν : Measure ℝ := unitMeas.restrict A with hν
  have hνreal (B : Set ℝ) (hB : MeasurableSet B) : ν.real B = unitMeas.real (B ∩ A) := by
    rw [hν, Measure.real, Measure.real, Measure.restrict_apply hB]
  -- `ν`-a.e. point lies in `[0, 1)`
  have hνnull : ν (Set.Ico (0 : ℝ) 1)ᶜ = 0 := by
    rw [hν, unitMeas, Measure.restrict_apply measurableSet_Ico.compl,
      Measure.restrict_apply (measurableSet_Ico.compl.inter hA)]
    have hempty : ((Set.Ico (0 : ℝ) 1)ᶜ ∩ A) ∩ Set.Ico (0 : ℝ) 1 = ∅ := by
      rw [Set.inter_assoc, Set.inter_comm A, ← Set.inter_assoc, Set.compl_inter_self,
        Set.empty_inter]
    rw [hempty, measure_empty]
  have hAe : ∀ᵐ x ∂ν, x ∈ Set.Ico (0 : ℝ) 1 := by
    rw [MeasureTheory.ae_iff]
    rwa [← Set.compl]
  have hterm (i) (_ : i ∈ Finset.range N) :
      unitMeas.real (A ∩ ⇑(f ^ i) ⁻¹' S₀)
        = ∫ x, (⇑(f ^ i) ⁻¹' S₀).indicator (fun _ => (1 : ℝ)) x ∂ν := by
    have hm : MeasurableSet (⇑(f ^ i) ⁻¹' S₀) := hS₀.preimage (measurable_pow f i)
    have hone : (⇑(f ^ i) ⁻¹' S₀).indicator (fun _ => (1 : ℝ)) = (⇑(f ^ i) ⁻¹' S₀).indicator 1 :=
      rfl
    rw [hone, integral_indicator_one hm, hνreal _ hm, Set.inter_comm]
  have hInt (i) (hi : i ∈ Finset.range N) :
      Integrable (fun x => (⇑(f ^ i) ⁻¹' S₀).indicator (fun _ => (1 : ℝ)) x) ν :=
          Integrable.indicator (integrable_const 1) (hS₀.preimage (measurable_pow f i))
  calc ∑ i ∈ Finset.range N, unitMeas.real (A ∩ ⇑(f ^ i) ⁻¹' S₀)
      = ∑ i ∈ Finset.range N, ∫ x, (⇑(f ^ i) ⁻¹' S₀).indicator (fun _ => (1 : ℝ)) x ∂ν :=
        Finset.sum_congr rfl hterm
    _ = ∫ x, ∑ i ∈ Finset.range N, (⇑(f ^ i) ⁻¹' S₀).indicator (fun _ => (1 : ℝ)) x ∂ν := by
        rw [integral_finsetSum]
        exact hInt
    _ ≤ ∫ x, (2 * ε * N) ∂ν := by
        refine integral_mono_ae (integrable_finsetSum _ hInt) (integrable_const _) ?_
        filter_upwards [hAe] with x hx
        have hb := hbirk x hx
        have hid : ∑ i ∈ Finset.range N, (⇑(f ^ i) ⁻¹' S₀).indicator (fun _ => (1 : ℝ)) x
            = ∑ i ∈ Finset.range N, S₀.indicator (fun _ => (1 : ℝ)) ((f ^ i) x) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          by_cases hmem : (f ^ i) x ∈ S₀ <;>
            simp [Set.indicator, Set.mem_preimage, hmem]
        rw [hid]
        have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        calc ∑ i ∈ Finset.range N, S₀.indicator (fun _ => (1 : ℝ)) ((f ^ i) x)
            = (N : ℝ) * ((N : ℝ)⁻¹ * ∑ i ∈ Finset.range N,
                S₀.indicator (fun _ => (1 : ℝ)) ((f ^ i) x)) := by
              rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hNpos), one_mul]
          _ ≤ (N : ℝ) * (2 * ε) := mul_le_mul_of_nonneg_left hb (le_of_lt hNpos)
          _ = 2 * ε * N := by ring
    _ = 2 * ε * N * unitMeas.real A := by
        have huniv : ν Set.univ = unitMeas A := by
          rw [hν, Measure.restrict_apply_univ]
        rw [integral_const, smul_eq_mul, Measure.real, huniv, Measure.real]
        ring

/-- **Display (2.3)**: some `i < N` works simultaneously for `S`, `f⁻¹S` and `g⁻¹S`. -/
theorem exists_small_intersection (f g : IET 0 1) {S S₀ : Set ℝ} (hS : MeasurableSet S)
    (hS₀ : MeasurableSet S₀) {N : ℕ} (hN : 0 < N) {ε : ℝ}
    (hbirk : ∀ x ∈ Set.Ico (0 : ℝ) 1, (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N,
      S₀.indicator (fun _ => (1 : ℝ)) ((f ^ i) x) ≤ 2 * ε) :
    ∃ i, i < N ∧ unitMeas.real (S ∩ ⇑(f ^ i) ⁻¹' S₀)
        + unitMeas.real (⇑f ⁻¹' S ∩ ⇑(f ^ i) ⁻¹' S₀)
        + unitMeas.real (⇑g ⁻¹' S ∩ ⇑(f ^ i) ⁻¹' S₀) ≤ 6 * ε * unitMeas.real S := by
  by_contra hcon
  push Not at hcon
  have b1 := sum_inter_le f hS hS₀ hN hbirk
  have b2 := sum_inter_le f (hS.preimage (measurable f)) hS₀ hN hbirk
  have b3 := sum_inter_le f (hS.preimage (measurable g)) hS₀ hN hbirk
  have hf : unitMeas.real (⇑f ⁻¹' S) = unitMeas.real S := unitMeas_real_preimage f hS
  have hg : unitMeas.real (⇑g ⁻¹' S) = unitMeas.real S := unitMeas_real_preimage g hS
  have hlow : 6 * ε * N * unitMeas.real S < ∑ i ∈ Finset.range N,
      (unitMeas.real (S ∩ ⇑(f ^ i) ⁻¹' S₀) + unitMeas.real (⇑f ⁻¹' S ∩ ⇑(f ^ i) ⁻¹' S₀)
        + unitMeas.real (⇑g ⁻¹' S ∩ ⇑(f ^ i) ⁻¹' S₀)) := by
    have hconst : ∑ _i ∈ Finset.range N, (6 * ε * unitMeas.real S) = 6 * ε * N * unitMeas.real S :=
      by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [← hconst]
    refine Finset.sum_lt_sum (fun i hi => le_of_lt (hcon i (Finset.mem_range.mp hi))) ?_
    exact ⟨0, Finset.mem_range.mpr hN, hcon 0 hN⟩
  have b2' : ∑ i ∈ Finset.range N, unitMeas.real (⇑f ⁻¹' S ∩ ⇑(f ^ i) ⁻¹' S₀)
      ≤ 2 * ε * N * unitMeas.real S := by
    rw [← hf]; exact b2
  have b3' : ∑ i ∈ Finset.range N, unitMeas.real (⇑g ⁻¹' S ∩ ⇑(f ^ i) ⁻¹' S₀)
      ≤ 2 * ε * N * unitMeas.real S := by
    rw [← hg]; exact b3
  have hup : ∑ i ∈ Finset.range N,
      (unitMeas.real (S ∩ ⇑(f ^ i) ⁻¹' S₀) + unitMeas.real (⇑f ⁻¹' S ∩ ⇑(f ^ i) ⁻¹' S₀)
        + unitMeas.real (⇑g ⁻¹' S ∩ ⇑(f ^ i) ⁻¹' S₀)) ≤ 6 * ε * N * unitMeas.real S := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    linarith
  linarith

end IntervalExchange.Pair

namespace IntervalExchange

/-! ## The bridges between `evalWord` and `evalWordEquiv`

`evalWord` evaluates a word in two *exchanges* (`IET 0 1`), which is what the Section 3 development
uses, while `evalWordEquiv` — the `Equiv`-valued evaluation the challenge speaks of — is stated for
the underlying permutations of `ℝ` and lives in `IETFree/IET.lean`, beside `mkIETEquiv`.  The two
bridges are here, because they are about `evalWord`: `evalWord_toEquiv` says the evaluations agree,
and `evalWord_toEquiv_eq_one` passes a trivial word from one to the other. -/

/-- `evalWord` of `IET`s is `evalWordEquiv` of the underlying equivs: the two evaluations agree. -/
theorem evalWord_toEquiv (F G : IET 0 1) (w : FreeGroup (Fin 2)) :
    (evalWord w F G).toEquiv = evalWordEquiv w F.toEquiv G.toEquiv := by
  induction w using FreeGroup.induction_on with
  | one => rfl
  | of x => fin_cases x <;> rfl
  | inv_of x ih =>
      have h1 : ((evalWord (FreeGroup.of x) F G)⁻¹).toEquiv
          = ((evalWord (FreeGroup.of x) F G).toEquiv)⁻¹ := (rfl)
      simp only [evalWord_inv, map_inv, evalWordEquiv, h1, ih]
  | mul x y ihx ihy =>
      have h1 : (evalWord x F G * evalWord y F G).toEquiv
          = (evalWord x F G).toEquiv * (evalWord y F G).toEquiv := (rfl)
      simp only [evalWord_mul, map_mul, evalWordEquiv, h1, ihx, ihy]

/-! ## A word trivial for an exchange is trivial for the permutation -/

/-- A word which is trivial for the library's exchanges is trivial for their permutations of `ℝ`. -/
theorem evalWord_toEquiv_eq_one {w : FreeGroup (Fin 2)} {F G : IET 0 1}
    (h : evalWord w F G = 1) : evalWordEquiv w F.toEquiv G.toEquiv = 1 := by
  have hone : (1 : IET 0 1).toEquiv = (1 : Equiv ℝ ℝ) := (rfl)
  have h1 : (evalWord w F G).toEquiv = (1 : Equiv ℝ ℝ) := by rw [h, hone]
  rwa [evalWord_toEquiv] at h1

end IntervalExchange

end
