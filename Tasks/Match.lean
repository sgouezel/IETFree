/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.Diophantine
import IETFree.Commensurable
import IETFree.Centralizer
import IETFree.TranslationVector
import IETFree.SingularityBound

/-!
Statement-match checks: the statements given to the discovery runs, written out verbatim, proved by
the corresponding declarations of the library.  A failure here means that the library statement has
drifted from the task file, so the recorded run no longer evidences the library lemma.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

/-- The statement of `disp_of_locally` given to the run `iet-lemmas` (now `transl_of_locally`). -/
example : ∀ {f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}, IsCutSet f a b s → ∀ {x y : ℝ},
    x ∈ Set.Ico a b → y ∈ Set.Ico a b →
    (∀ c ∈ s, min x y < c → c ≤ max x y → IsLocallyTranslationAt f a b c) →
    f y - y = f x - x := by
  intro f a b s _hs x y _hx _hy h
  exact IsCutSet.transl_of_locally _hs _hx _hy h

/-- The statement of `cutset_comp`, in the form of the run `iet-lemmas`. -/
example : ∀ {s t : Finset ℝ} {f g : ℝ → ℝ} {a b : ℝ} (hf : IsCutSet f a b s),
    IsCutSet g a b t → IsCutSet (g ∘ f) a b (s ∪ hf.preimage t) := by
  intro s t f g a b hf _hg
  exact IsCutSet.comp hf _hg

/-- The statement of `mkiet_is_iet`, in the form of the run `iet-lemmas-2`. -/
example : ∀ {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n)) (a : ℝ) {t : ℝ},
    (∑ i, (lam i : ℝ)) ≤ t → IsIET a (a + t) (mkIETFun lam π a) := by
  intro n _ lam _π a t ht
  exact isIET_mkIETFun lam _π a ht

/-- The statement of `exists_mkiet_equiv_eq` (with the hypothesis `a ≤ b` that the run's statement
lacked — see the note in `Tasks/README.md`). -/
example : ∀ {a b : ℝ} {e : Equiv ℝ ℝ}, a ≤ b → IsIET a b e →
    ∃ (n : ℕ) (hn : NeZero n) (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin n)),
      (∑ i, (lam i : ℝ)) = b - a ∧ e = @mkIETEquiv n hn lam π a := by
  intro a b e hab h
  exact exists_mkIETEquiv_eq hab h

/-- The statement of the run `ae-diophantine` (Proposition 2.5), proved by `ae_diophantine_of_mem`:
the library declaration that keeps the run's membership hypotheses. -/
example : ∀ {d e : ℕ}, Equiv.Perm (Fin d) → Equiv.Perm (Fin e) →
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
      p.1 ∈ simplex d → p.2 ∈ simplex e → IsDiophantine p.1 p.2 := by
  intro d e π σ
  exact ae_diophantine_of_mem π σ

/-- The strengthened form now in the library: for `d, e ≥ 1` (the paper's `d, e ∈ ℕ*`) the
membership hypotheses are redundant, because `simplexVolume` is supported on the simplex. -/
example : ∀ {d e : ℕ} [NeZero d] [NeZero e], Equiv.Perm (Fin d) → Equiv.Perm (Fin e) →
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)), IsDiophantine p.1 p.2 := by
  intro d e _ _ _π _σ
  exact ae_diophantine _π _σ

/-- The statement of the run `commensurable-commute`, proved by `FreeGroup.commute_of_zpow_eq`. -/
example : ∀ {α : Type*} [DecidableEq α] {a b : FreeGroup α} {m n : ℤ},
    m ≠ 0 → n ≠ 0 → a ^ m = b ^ n → a * b = b * a := by
  intro α _ a b m n hm hn h
  exact FreeGroup.commute_of_zpow_eq hm hn h

/-- The statement of `Tasks/centralizer_cyclic.lean` (LS Prop. 2.19 for `F₂`), proved by
`FreeGroup.exists_zpow_eq_of_mul_comm`. -/
example : ∀ {v : FreeGroup (Fin 2)}, v ≠ 1 →
    ∃ r : FreeGroup (Fin 2), ∀ z : FreeGroup (Fin 2), z * v = v * z → ∃ n : ℤ, z = r ^ n := by
  intro v hv
  exact FreeGroup.exists_zpow_eq_of_mul_comm hv

/-- The statement of the run `translation-vector-bound`, proved by `exists_lattice_displacement`. -/
example : ∀ {d e : ℕ} (lam : Fin d → ℝ) (mu : Fin e → ℝ) (f g : Equiv.Perm ℝ)
    (Df : ℝ → Fin d → ℤ) (Dg : ℝ → Fin e → ℤ),
    (∀ y, f y = y + ∑ i, (Df y i : ℝ) * lam i) → (∀ y i, |Df y i| ≤ 1) →
    (∀ y, g y = y + ∑ j, (Dg y j : ℝ) * mu j) → (∀ y j, |Dg y j| ≤ 1) →
    ∀ (w : FreeGroup (Fin 2)) (x : ℝ),
      ∃ a : Fin d → ℤ, ∃ b : Fin e → ℤ,
        (∀ i, |a i| ≤ ((FreeGroup.toWord w).length : ℤ)) ∧
          (∀ j, |b j| ≤ ((FreeGroup.toWord w).length : ℤ)) ∧
          FreeGroup.lift (fun i : Fin 2 => if i = 0 then f else g) w x
            = x + (∑ i, (a i : ℝ) * lam i) + (∑ j, (b j : ℝ) * mu j) := by
  intro d e lam mu f g Df Dg hf hfb hg hgb w x
  exact exists_lattice_displacement lam mu f g Df Dg hf hfb hg hgb w x

/-- The statement of the run `singularity-bound-2` (`Tasks/singularity_bound.lean`), proved by the
library's `exists_lattice_cuts`, which is *stronger*: the translation-vector hypothesis `hTV` of the
run's statement turned out to be unused, so it is simply discarded here. -/
example : ∀ {d e : ℕ} (lam : Fin d → ℝ) (mu : Fin e → ℝ) (f g : Equiv.Perm ℝ) (Sf Sg : Finset ℝ)
    (Df : ℝ → Fin d → ℤ) (Dg : ℝ → Fin e → ℤ),
    (∀ y, f y = y + ∑ i, (Df y i : ℝ) * lam i) → (∀ y i, |Df y i| ≤ 1) →
    (∀ y, g y = y + ∑ j, (Dg y j : ℝ) * mu j) → (∀ y j, |Dg y j| ≤ 1) →
    (∀ y y', ¬ CutBound.CutSep Sf y y' → f y - y = f y' - y') →
    (∀ y y', ¬ CutBound.CutSep Sg y y' → g y - y = g y' - y') →
    (∀ c ∈ Sf, ∃ a : Fin d → ℤ, (∀ i, |a i| ≤ 1) ∧ c = ∑ i, (a i : ℝ) * lam i) →
    (∀ c ∈ Sg, ∃ b : Fin e → ℤ, (∀ j, |b j| ≤ 1) ∧ c = ∑ j, (b j : ℝ) * mu j) →
    (∀ (u : FreeGroup (Fin 2)) (x : ℝ), ∃ a : Fin d → ℤ, ∃ b : Fin e → ℤ,
      (∀ i, |a i| ≤ ((FreeGroup.toWord u).length : ℤ)) ∧
        (∀ j, |b j| ≤ ((FreeGroup.toWord u).length : ℤ)) ∧
        FreeGroup.lift (fun i : Fin 2 => if i = 0 then f else g) u x
          = x + (∑ i, (a i : ℝ) * lam i) + (∑ j, (b j : ℝ) * mu j)) →
    ∀ (w : FreeGroup (Fin 2)),
      ∃ C : Finset ℝ,
        (∀ c ∈ C, ∃ a : Fin d → ℤ, ∃ b : Fin e → ℤ,
          (∀ i, |a i| ≤ ((FreeGroup.toWord w).length : ℤ) + 1) ∧
            (∀ j, |b j| ≤ ((FreeGroup.toWord w).length : ℤ) + 1) ∧
            c = (∑ i, (a i : ℝ) * lam i) + (∑ j, (b j : ℝ) * mu j)) ∧
        (∀ y y', ¬ CutBound.CutSep C y y' →
          FreeGroup.lift (fun i : Fin 2 => if i = 0 then f else g) w y - y
            = FreeGroup.lift (fun i : Fin 2 => if i = 0 then f else g) w y' - y') := by
  intro d e lam mu f g Sf Sg Df Dg hf hfb hg hgb hSf hSg hSf_lat hSg_lat _hTV w
  exact CutBound.exists_lattice_cuts lam mu f g Sf Sg Df Dg hf hfb hg hgb hSf hSg hSf_lat hSg_lat w
