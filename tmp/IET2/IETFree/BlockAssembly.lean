/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.BlockIrreducibility

/-!
From per-block words to a single word trivial on `[0, 1)`.

Given a finite family of blocks `[u i, v i)` covering `[0, 1)`, each invariant under both exchanges,
and a nontrivial word trivial on each of them, the file builds **one** nontrivial word trivial on
the whole of `[0, 1)` (`exists_word_trivial_on_all_of_blocks`).  The words of the blocks are
combined with commutators and conjugates (`commutator_apply_eq_self_left`,
`commutator_apply_eq_self_right`, `conj_apply_eq_self`, `evalWord_mapsTo_of_invariant`), which act
as the identity on a set invariant under the two generators.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal commutatorElement
/-- A marked point of a datum is `0`, `1`, or one of the cut points. -/
theorem mark_mem_insert {n : ℕ} [NeZero n] (F : IETDatum n) (k : Fin (n + 1)) :
    F.mark k ∈ insert (0 : ℝ) (insert (1 : ℝ) F.markCuts) := by
  rcases eq_or_ne k 0 with hk | hk
  · rw [hk, IETDatum.mark_zero]
    exact Finset.mem_insert_self _ _
  · rcases eq_or_ne k (Fin.last n) with hk' | hk'
    · rw [hk', IETDatum.mark_last]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · have hklt : k.val < n := by
        have h1 := k.isLt
        have h2 : k.val ≠ n := fun h => hk' (Fin.ext (by simpa using h))
        omega
      refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨⟨k.val, hklt⟩, Finset.mem_univ _, ?_⟩))
      exact (congrArg F.mark (Fin.ext rfl)).symm

/-- **A commutator is the identity where its first factor is** (`⁅a, b⁆ = a b a⁻¹ b⁻¹`, so the
second factor only has to come back to the set). -/
theorem commutator_apply_eq_self_left {a b : IET 0 1} {S : Set ℝ} {x : ℝ} (hx : x ∈ S)
    (ha : ∀ y ∈ S, a y = y) (hb : ∀ y ∈ S, b⁻¹ y ∈ S) : (⁅a, b⁆) x = x := by
  have h1 : b⁻¹ x ∈ S := hb x hx
  have h2 : a⁻¹ (b⁻¹ x) = b⁻¹ x := by
    conv_lhs => rw [← ha _ h1]
    rw [IET.symm_apply_apply]
  have h3 : b (b⁻¹ x) = x := IET.apply_symm_apply' b x
  have h4 : a x = x := ha x hx
  rw [commutatorElement_def, IET.mul_apply, IET.mul_apply, IET.mul_apply, h2, h3, h4]

/-- **A commutator is the identity where its second factor is.** -/
theorem commutator_apply_eq_self_right {a b : IET 0 1} {S : Set ℝ} {x : ℝ} (hx : x ∈ S)
    (hb : ∀ y ∈ S, b y = y) (ha : ∀ y ∈ S, a⁻¹ y ∈ S) : (⁅a, b⁆) x = x := by
  have h1 : a⁻¹ x ∈ S := ha x hx
  have h2 : b⁻¹ (a⁻¹ x) = a⁻¹ x := by
    conv_lhs => rw [← hb _ h1]
    rw [IET.symm_apply_apply]
  have key : (⁅b, a⁆) x = x := by
    rw [commutatorElement_def, IET.mul_apply, IET.mul_apply, IET.mul_apply, h2,
      IET.apply_symm_apply', hb x hx]
  calc (⁅a, b⁆) x = ((⁅b, a⁆)⁻¹) x := by rw [commutatorElement_inv]
    _ = ((⁅b, a⁆)⁻¹) ((⁅b, a⁆) x) := by rw [key]
    _ = x := IET.symm_apply_apply (⁅b, a⁆) x

/-- **A conjugate is the identity where the conjugated factor is.** -/
theorem conj_apply_eq_self {f g : IET 0 1} {S : Set ℝ} {x : ℝ} (hx : x ∈ S)
    (hfS : ∀ y ∈ S, f y ∈ S) (hg : ∀ y ∈ S, g y = y) : (f⁻¹ * g * f) x = x := by
  have h1 : f x ∈ S := hfS x hx
  have h2 : g (f x) = f x := hg _ h1
  rw [IET.mul_apply, IET.mul_apply, h2, IET.symm_apply_apply]

/-- **Every word preserves a set invariant under the two generators, in both directions.** -/
theorem evalWord_mapsTo_of_invariant {d e : ℕ} [NeZero d] [NeZero e] (D : IETDatum d)
    (E : IETDatum e) {T : Set ℝ}
    (hD : ∀ x ∈ T, D.toIET x ∈ T) (hDi : ∀ x ∈ T, D.toIET⁻¹ x ∈ T)
    (hE : ∀ x ∈ T, E.toIET x ∈ T) (hEi : ∀ x ∈ T, E.toIET⁻¹ x ∈ T) (w : FreeGroup Gen) :
    ∀ x ∈ T, (evalWord w D.toIET E.toIET) x ∈ T := by
  revert w
  refine fun w =>
    FreeGroup.induction_on (C := fun w => ∀ x ∈ T, (evalWord w D.toIET E.toIET) x ∈ T)
      w ?_ ?_ ?_ ?_
  · intro x hx
    rwa [evalWord_one, IET.one_apply]
  · intro i x hx
    fin_cases i
    · exact hD x hx
    · exact hE x hx
  · intro i hi x hx
    rw [evalWord_inv]
    fin_cases i
    · exact hDi x hx
    · exact hEi x hx
  · intro u v hu hv x hx
    rw [evalWord_mul, IET.mul_apply]
    exact hu _ (hv x hx)

/-- The part of the `i`-th block inside `[0, 1)`. -/
private def BlockIn {n : ℕ} (u v : Fin n → ℝ) (i : Fin n) : Set ℝ :=
  {x | x ∈ Set.Ico (0 : ℝ) 1 ∧ u i ≤ x ∧ x < v i}

/-- The part of the union of the blocks of `J` inside `[0, 1)`. -/
private def BlocksIn {n : ℕ} (u v : Fin n → ℝ) (J : Finset (Fin n)) : Set ℝ :=
  {x | x ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ i ∈ J, u i ≤ x ∧ x < v i}

/-- **The assembly of Theorem 1.1.**  If `[0, 1)` is covered by finitely many intervals, each of
which is *mapped onto itself* by both `D` and `E` (which is what a block between pair-splitting
points does, see `IsPairSplitting.iff_mem`) and each of which carries a nontrivial word that is
trivial on it, then some nontrivial word is trivial on all of `[0, 1)`, hence — an exchange being
the identity outside `[0, 1)` — the identity of `IET 0 1`. -/
theorem exists_word_trivial_on_all_of_blocks {d e : ℕ} [NeZero d] [NeZero e] (D : IETDatum d)
    (E : IETDatum e) {n : ℕ} (u v : Fin n → ℝ)
    (hcover : ∀ x ∈ Set.Ico (0 : ℝ) 1, ∃ i, u i ≤ x ∧ x < v i)
    (hfu : ∀ (i : Fin n) (x : ℝ), x ∈ Set.Ico (0 : ℝ) 1 →
      (u i ≤ x ∧ x < v i ↔ u i ≤ D.toFun x ∧ D.toFun x < v i))
    (hgu : ∀ (i : Fin n) (x : ℝ), x ∈ Set.Ico (0 : ℝ) 1 →
      (u i ≤ x ∧ x < v i ↔ u i ≤ E.toFun x ∧ E.toFun x < v i))
    (hw : ∀ i : Fin n, ∃ w : FreeGroup Gen, w ≠ 1 ∧
      ∀ x : ℝ, u i ≤ x → x < v i → (evalWord w D.toIET E.toIET) x = x) :
    ∃ w : FreeGroup Gen, w ≠ 1 ∧ evalWord w D.toIET E.toIET = 1 := by
  classical
  -- the `i`-th block and the union of the blocks of `J` are invariant under both generators
  have hDB : ∀ (J : Finset (Fin n)) (x : ℝ), x ∈ BlocksIn u v J → D.toFun x ∈ BlocksIn u v J := by
    rintro J x ⟨hx, j, hj, h1, h2⟩
    exact ⟨D.mapsTo hx, j, hj, (hfu j x hx).mp ⟨h1, h2⟩⟩
  have hEB : ∀ (J : Finset (Fin n)) (x : ℝ), x ∈ BlocksIn u v J → E.toFun x ∈ BlocksIn u v J := by
    rintro J x ⟨hx, j, hj, h1, h2⟩
    exact ⟨E.mapsTo hx, j, hj, (hgu j x hx).mp ⟨h1, h2⟩⟩
  have hDBi : ∀ (J : Finset (Fin n)) (x : ℝ), x ∈ BlocksIn u v J →
      D.toIET⁻¹ x ∈ BlocksIn u v J := by
    rintro J x ⟨hx, j, hj, h1, h2⟩
    have hy1 : D.toIET⁻¹ x ∈ Set.Ico (0 : ℝ) 1 := (D.toIET⁻¹).isIET.mapsTo hx
    have hyx : D.toFun (D.toIET⁻¹ x) = x := by
      rw [← IETDatum.toIET_apply, IET.apply_symm_apply']
    refine ⟨hy1, j, hj, ?_, ?_⟩
    · have h := (hfu j (D.toIET⁻¹ x) hy1).mpr ⟨by rw [hyx]; exact h1, by rw [hyx]; exact h2⟩
      exact h.1
    · have h := (hfu j (D.toIET⁻¹ x) hy1).mpr ⟨by rw [hyx]; exact h1, by rw [hyx]; exact h2⟩
      exact h.2
  have hEBi : ∀ (J : Finset (Fin n)) (x : ℝ), x ∈ BlocksIn u v J →
      E.toIET⁻¹ x ∈ BlocksIn u v J := by
    rintro J x ⟨hx, j, hj, h1, h2⟩
    have hy1 : E.toIET⁻¹ x ∈ Set.Ico (0 : ℝ) 1 := (E.toIET⁻¹).isIET.mapsTo hx
    have hyx : E.toFun (E.toIET⁻¹ x) = x := by
      rw [← IETDatum.toIET_apply, IET.apply_symm_apply']
    refine ⟨hy1, j, hj, ?_, ?_⟩
    · have h := (hgu j (E.toIET⁻¹ x) hy1).mpr ⟨by rw [hyx]; exact h1, by rw [hyx]; exact h2⟩
      exact h.1
    · have h := (hgu j (E.toIET⁻¹ x) hy1).mpr ⟨by rw [hyx]; exact h1, by rw [hyx]; exact h2⟩
      exact h.2
  -- every word preserves every block and every union of blocks
  have hpres : ∀ (w : FreeGroup Gen) (S : Set ℝ),
      (∀ x ∈ S, D.toIET x ∈ S) → (∀ x ∈ S, D.toIET⁻¹ x ∈ S) →
      (∀ x ∈ S, E.toIET x ∈ S) → (∀ x ∈ S, E.toIET⁻¹ x ∈ S) →
      ∀ x ∈ S, (evalWord w D.toIET E.toIET) x ∈ S :=
    fun w S h1 h2 h3 h4 => evalWord_mapsTo_of_invariant D E h1 h2 h3 h4 w
  -- the same for the inverse of a word
  have hpres' : ∀ (u : FreeGroup Gen) (S : Set ℝ),
      (∀ x ∈ S, D.toIET x ∈ S) → (∀ x ∈ S, D.toIET⁻¹ x ∈ S) →
      (∀ x ∈ S, E.toIET x ∈ S) → (∀ x ∈ S, E.toIET⁻¹ x ∈ S) →
      ∀ x ∈ S, (evalWord u D.toIET E.toIET)⁻¹ x ∈ S := by
    intro u S h1 h2 h3 h4
    simpa only [evalWord_inv] using hpres u⁻¹ S h1 h2 h3 h4
  -- the induction over the blocks
  have key : ∀ J : Finset (Fin n), ∃ w : FreeGroup Gen, w ≠ 1 ∧
      ∀ x : ℝ, x ∈ BlocksIn u v J → (evalWord w D.toIET E.toIET) x = x := by
    intro J
    induction J using Finset.induction with
    | empty =>
        refine ⟨genX, FreeGroup.of_ne_one 0, ?_⟩
        rintro x ⟨-, i, hi, -⟩
        exact absurd hi (by simp)
    | insert i J hi ih =>
        obtain ⟨w, hwne, hwt⟩ := ih
        obtain ⟨wi, hwine, hwit⟩ := hw i
        -- `wi` is trivial on the `i`-th block, `w` on the union of the blocks of `J`
        have hwit' : ∀ x ∈ BlocksIn u v {i}, (evalWord wi D.toIET E.toIET) x = x := by
          rintro x ⟨-, j, hj, h1, h2⟩
          rw [Finset.mem_singleton] at hj
          subst hj
          exact hwit x h1 h2
        have hwT : ∀ x ∈ BlocksIn u v {i}, (evalWord w D.toIET E.toIET)⁻¹ x ∈ BlocksIn u v {i} :=
          hpres' w _ (hDB {i}) (hDBi {i}) (hEB {i}) (hEBi {i})
        have hwS : ∀ x ∈ BlocksIn u v J, (evalWord wi D.toIET E.toIET)⁻¹ x ∈ BlocksIn u v J :=
          hpres' wi _ (hDB J) (hDBi J) (hEB J) (hEBi J)
        have hwTcD : ∀ x ∈ BlocksIn u v {i},
            (D.toIET⁻¹ * evalWord w D.toIET E.toIET * D.toIET)⁻¹ x ∈ BlocksIn u v {i} := by
          have hcoe : (D.toIET⁻¹ * evalWord w D.toIET E.toIET * D.toIET)⁻¹
              = D.toIET⁻¹ * (evalWord w D.toIET E.toIET)⁻¹ * D.toIET := by group
          intro x hx
          rw [hcoe, IET.mul_apply, IET.mul_apply]
          exact hDBi {i} _ (hpres' w (BlocksIn u v {i}) (hDB {i}) (hDBi {i}) (hEB {i}) (hEBi {i}) _
            (hDB {i} _ hx))
        have hwTcE : ∀ x ∈ BlocksIn u v {i},
            (E.toIET⁻¹ * evalWord w D.toIET E.toIET * E.toIET)⁻¹ x ∈ BlocksIn u v {i} := by
          have hcoe : (E.toIET⁻¹ * evalWord w D.toIET E.toIET * E.toIET)⁻¹
              = E.toIET⁻¹ * (evalWord w D.toIET E.toIET)⁻¹ * E.toIET := by group
          intro x hx
          rw [hcoe, IET.mul_apply, IET.mul_apply]
          exact hEBi {i} _ (hpres' w (BlocksIn u v {i}) (hDB {i}) (hDBi {i}) (hEB {i}) (hEBi {i}) _
            (hEB {i} _ hx))
        -- a point of the enlarged union is in the old union or in the `i`-th block
        have hsplit : ∀ x ∈ BlocksIn u v (insert i J),
            x ∈ BlocksIn u v J ∨ x ∈ BlocksIn u v {i} := by
          rintro x ⟨hx, j, hj, h1, h2⟩
          rcases Finset.mem_insert.mp hj with rfl | hjJ
          · exact Or.inr ⟨hx, j, Finset.mem_singleton_self j, h1, h2⟩
          · exact Or.inl ⟨hx, j, hjJ, h1, h2⟩
        rcases exists_nontrivial_commutator w wi hwne hwine with h1 | h2 | h3
        · refine ⟨⁅w, wi⁆, h1, ?_⟩
          rw [evalWord_commutatorElement]
          intro x hx
          rcases hsplit x hx with hxJ | hxi
          · exact commutator_apply_eq_self_left (S := BlocksIn u v J) hxJ hwt hwS
          · exact commutator_apply_eq_self_right (S := BlocksIn u v {i}) hxi hwit' hwT
        · refine ⟨⁅genX⁻¹ * w * genX, wi⁆, h2, ?_⟩
          rw [evalWord_commutatorElement, evalWord_conjX]
          intro x hx
          rcases hsplit x hx with hxJ | hxi
          · exact commutator_apply_eq_self_left (S := BlocksIn u v J) hxJ
              (fun y hy => conj_apply_eq_self hy (hDB J) hwt) hwS
          · exact commutator_apply_eq_self_right (S := BlocksIn u v {i}) hxi hwit' hwTcD
        · refine ⟨⁅genY⁻¹ * w * genY, wi⁆, h3, ?_⟩
          rw [evalWord_commutatorElement, evalWord_conjY]
          intro x hx
          rcases hsplit x hx with hxJ | hxi
          · exact commutator_apply_eq_self_left (S := BlocksIn u v J) hxJ
              (fun y hy => conj_apply_eq_self hy (hEB J) hwt) hwS
          · exact commutator_apply_eq_self_right (S := BlocksIn u v {i}) hxi hwit' hwTcE
  obtain ⟨w, hwne, hwt⟩ := key Finset.univ
  refine ⟨w, hwne, ?_⟩
  refine IET.ext fun x => ?_
  rw [IET.one_apply]
  by_cases hx : x ∈ Set.Ico (0 : ℝ) 1
  · obtain ⟨i, hi⟩ := hcover x hx
    exact hwt x ⟨hx, i, Finset.mem_univ i, hi⟩
  · exact (evalWord w D.toIET E.toIET).isIET.eq_of_notMem hx
