/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.BlockRescaling

/-!
The change of generators `(f, g) ↦ (g ∘ f, g)`, and the transport of a word back from the rescaled
block.

Lemma 3.4 produces its word for the pair `(g ∘ f, g)` on the rescaled block, while the conclusion of
Theorem 1.1 is a word in the two generators `(f, g)`.  The two pairs generate the same subgroup
(`f = g⁻¹ ∘ (g ∘ f)`), so the substitution `genX ↦ genY * genX`, `genY ↦ genY` turns a word in the
first pair into a word in the second; it is injective, with inverse `genX ↦ genY⁻¹ * genX`, so it
preserves nontriviality (`substGen_ne_one`), and it is compatible with evaluation
(`evalWord_substGen`).  From a word trivial for the rescaled pair the file returns a word trivial on
the original block, `exists_word_trivial_on_block_of_rescaled`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

-- `simp only [Fin.val_mk]` is needed in the pure `Fin`-index goals below (removing it breaks the
-- following `omega`/`rw`), but this version of the `unusedSimpArgs` linter reports it as unused.
set_option linter.unusedSimpArgs false
/-! ### The change of generators `(f, g) ↦ (g ∘ f, g)`

Lemma 3.4 produces its word for the pair `(g ∘ f, g)` on the rescaled block, while the conclusion
of Theorem 1.1 is a word in the two generators `(f, g)`.  The two pairs generate the same subgroup
(`f = g⁻¹ ∘ (g ∘ f)`), so the substitution `genX ↦ genY * genX`, `genY ↦ genY` turns a word in the
first pair into a word in the second; it is injective, with inverse `genX ↦ genY⁻¹ * genX`, so it
preserves nontriviality. -/

/-- The substitution of words sending the first generator to `g ∘ f` (that is, `genY * genX` in the
generators `(f, g)`) and fixing the second. -/
noncomputable def substGen : FreeGroup Gen →* FreeGroup Gen :=
  FreeGroup.lift (fun i : Gen => if i = 0 then genY * genX else genY)

/-- The inverse substitution: it sends `g ∘ f` back to `f`, i.e. `genX ↦ genY⁻¹ * genX`. -/
noncomputable def invSubstGen : FreeGroup Gen →* FreeGroup Gen :=
  FreeGroup.lift (fun i : Gen => if i = 0 then genY⁻¹ * genX else genY)

theorem invSubstGen_substGen_apply (i : Gen) : invSubstGen (substGen (FreeGroup.of i))
    = FreeGroup.of i := by
  fin_cases i
  · change (FreeGroup.lift (fun i : Gen => if i = 0 then genY⁻¹ * genX else genY))
      ((FreeGroup.lift (fun i : Gen => if i = 0 then genY * genX else genY)) (FreeGroup.of 0))
      = FreeGroup.of 0
    rw [FreeGroup.lift_apply_of]
    simp only [FreeGroup.lift_apply_of, genX, genY]
    norm_num
  · change (FreeGroup.lift (fun i : Gen => if i = 0 then genY⁻¹ * genX else genY))
      ((FreeGroup.lift (fun i : Gen => if i = 0 then genY * genX else genY)) (FreeGroup.of 1))
      = FreeGroup.of 1
    rw [FreeGroup.lift_apply_of]
    simp only [if_neg (by norm_num : ¬ ((1 : Gen) = 0)), FreeGroup.lift_apply_of, genY]

/-- **The substitution is injective**, because `invSubstGen` is a left inverse. -/
theorem invSubstGen_substGen (w : FreeGroup Gen) : invSubstGen (substGen w) = w := by
  induction w using FreeGroup.induction_on with
  | C1 => rw [map_one, map_one]
  | of i => exact invSubstGen_substGen_apply i
  | inv_of i ih => rw [map_inv, map_inv, ih]
  | mul u v hu hv => rw [map_mul, map_mul, hu, hv]

theorem substGen_ne_one {w : FreeGroup Gen} (hw : w ≠ 1) : substGen w ≠ 1 := by
  intro h
  apply hw
  have hh := invSubstGen_substGen w
  rw [h, map_one] at hh
  exact hh.symm

/-- **The substitution evaluates to the same exchange**: a word in the generators `(g ∘ f, g)`
becomes a word in `(f, g)`. -/
theorem evalWord_substGen (w : FreeGroup Gen) (f g : IET 0 1) :
    evalWord (substGen w) f g = evalWord w (g * f) g := by
  have hgen : ∀ i : Gen, FreeGroup.lift (fun i : Gen => if i = 0 then f else g)
      (substGen (FreeGroup.of i)) = (if i = 0 then g * f else g) := by
    intro i
    fin_cases i
    · change (FreeGroup.lift (fun i : Gen => if i = 0 then f else g))
        ((FreeGroup.lift (fun i : Gen => if i = 0 then genY * genX else genY)) (FreeGroup.of 0))
        = if (0 : Gen) = 0 then g * f else g
      rw [FreeGroup.lift_apply_of]
      simp only [FreeGroup.lift_apply_of, genX, genY]
      norm_num
    · change (FreeGroup.lift (fun i : Gen => if i = 0 then f else g))
        ((FreeGroup.lift (fun i : Gen => if i = 0 then genY * genX else genY)) (FreeGroup.of 1))
        = if (1 : Gen) = 0 then g * f else g
      rw [FreeGroup.lift_apply_of]
      simp only [if_neg (by norm_num : ¬ ((1 : Gen) = 0)), FreeGroup.lift_apply_of, genY]
  have h := FreeGroup.lift_unique ((FreeGroup.lift (fun i : Gen => if i = 0 then f else g)).comp
    substGen) hgen (x := w)
  simp only [MonoidHom.comp_apply] at h
  change FreeGroup.lift (fun i : Gen => if i = 0 then f else g) (substGen w)
    = FreeGroup.lift (fun i : Gen => if i = 0 then g * f else g) w
  rw [h]

/-! ### The transport of a word from the rescaled block back to the block -/

/-- If `φ` conjugates an exchange forwards, it conjugates its inverse as well: the point at which
the forward identity is read is again in `[0,1)`, because an exchange maps `[0,1)` to itself. -/
theorem conj_inv_of_conj {B B' : IET 0 1} {φ : ℝ → ℝ}
    (h : ∀ y ∈ Set.Ico (0 : ℝ) 1, B (φ y) = φ (B' y)) :
    ∀ y ∈ Set.Ico (0 : ℝ) 1, B⁻¹ (φ y) = φ (B'⁻¹ y) := by
  intro y hy
  have hmem : B'⁻¹ y ∈ Set.Ico (0 : ℝ) 1 := (B'⁻¹).isIET.mapsTo hy
  have h1 : B (φ (B'⁻¹ y)) = φ y := by
    rw [h _ hmem, IET.apply_symm_apply']
  rw [← h1, IET.symm_apply_apply]

/-- **The word transport for Lemma 3.4.**  If `φ = rescaleMapInv u v` conjugates `G ∘ F` to `F'` and
`G` to `G'` on `[0,1)` — that is, if `(F', G')` is the pair `(G ∘ F, G)` rescaled to the block
`[u,v)` — then a nontrivial word which is the identity for `(F', G')` becomes a nontrivial word in
the generators `(F, G)` which is the identity on the block. -/
theorem exists_word_trivial_on_block_of_rescaled {F G F' G' : IET 0 1} {u v : ℝ} (huv : u < v)
    (hF : ∀ y ∈ Set.Ico (0 : ℝ) 1, (G * F) (rescaleMapInv u v y) = rescaleMapInv u v (F' y))
    (hG : ∀ y ∈ Set.Ico (0 : ℝ) 1, G (rescaleMapInv u v y) = rescaleMapInv u v (G' y))
    (hex : ∃ w : FreeGroup Gen, w ≠ 1 ∧ evalWord w F' G' = 1) :
    ∃ w : FreeGroup Gen, w ≠ 1 ∧ ∀ x : ℝ, u ≤ x → x < v → (evalWord w F G) x = x := by
  obtain ⟨w, hw, hw1⟩ := hex
  refine ⟨substGen w, substGen_ne_one hw, fun x hx1 hx2 => ?_⟩
  have hφ : rescaleMapInv u v (rescaleMap u v x) = x := rescaleMapInv_rescaleMap huv x
  have hy : rescaleMap u v x ∈ Set.Ico (0 : ℝ) 1 := (rescaleMap_mem huv).mpr ⟨hx1, hx2⟩
  have hconj := evalWord_conj_apply (F := G * F) (G := G) (F' := F') (G' := G')
    hF (conj_inv_of_conj hF) hG (conj_inv_of_conj hG) w (rescaleMap u v x) hy
  simp only [hw1, IET.one_apply] at hconj
  rw [hφ] at hconj
  rw [evalWord_substGen]
  exact hconj
