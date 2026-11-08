/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.RichPath.NodeHeight

/-!
# The graded induction of AGY

The source proves, by induction on `k`, the graded statement `(c+2)_k`:

```
P_q(𝔐(B_γ q) < C · min{𝔪_k(B_γ q), 𝔐(q)} | π) > C^{-1}          (c+2)_k
```

for `k = 1, …, d = #𝒜`, and `(c+2)_d` *is* the full statement because `𝔪_d = 𝔪`.

This file delivers the **skeleton** of that induction, in the cylinder-mass language of
`NodeHeight` and `CylinderMass` (`colSum`, `mkMass`, `cond`,
`PrefixFree`):

* §1 `Graded P k C` is `(c+2)_k` with the single constant `C`; `graded_iff_gradedStep` identifies
  it with the level-`k` statement `GradedStep`.  (`mkMass_card` rewrites `mkMass (#α)`
  as `mmin univ`, i.e. as AGY's `𝔪`, so the level `#α` is the full statement.)
* §2 `graded_one`: the base case `(c+2)_1` at *every* node, with `C = 2` and the family `{[]}`.
* §3 `graded_min`: AGY's `Γ₁`, i.e. the sub-family on which `𝔪_k` is attained on one fixed
  `A'` — the mass loses exactly the factor `C(d,k)`.
* §4 AGY's RichPath step, i.e. the family of *minimal* continuations: it is prefix-free, and
  `exists_prefixFree_mass` replaces a covering family by its minimal elements without
  losing mass.
* §5 `InductionStep P` — the `k → k+1` step of AGY (its `Γ₁`--`Γ₄`) — and
  `exists_gradedStep_card_of_inductionStep`: `InductionStep P` gives the level-`#α` statement, in
  the form the analysis of `RichPathAssembly.lean` consumes.
* §6 `InductionStep P` is not a weakening: `inductionStep_of_balance` derives it from
  `BalanceStep P K` (whose content is `Γ₂`--`Γ₄`), and it is proved unconditionally in
  `IETFree/RauzyVeech/RichPath/RichGreedyPath.lean`.
-/

open Finset IntervalExchange.IETDatum₂
open scoped BigOperators

@[expose] public section

namespace IntervalExchange.RauzyVeech.RichPath

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. The graded statement `(c+2)_k` -/

/-- **`(c+2)_k` at a single constant** (AGY's display `(c+2)` with `Cb = Cm = C`): at every
node `w` there is a prefix-free family `Γ` of continuations of `w` of `cond`-mass `> 1/C` at the end
of each of which the state at `w ++ δ` has maximum `< C · min{𝔪_k, 𝔐(q_w)}`.  `mkMass 1` is
AGY's `𝔐`, `mkMass k` its `𝔪_k = max_{#𝒜' = k} m_{𝒜'}`, the state `colSum P w`
is `q_w = B_w·1`, and `cond P w δ` is the path mass `P_{q_w}(δ | w)`.

This is `GradedStep` at `Cb = Cm = C`; it is kept as a name because that is the form the induction
of this file is stated in. -/
def Graded (P : IETDatum₂ α n) (k : ℕ) (C : ℝ) : Prop :=
  GradedStep P k C C

/-- `Graded P k C` is the level-`k` statement `GradedStep` with the two constants identified. -/
theorem graded_iff_gradedStep (P : IETDatum₂ α n) (k : ℕ) (C : ℝ) :
    Graded P k C ↔ GradedStep P k C C :=
  Iff.rfl

/-! ## 2. The base case `k = 1`, with the family `{[]}`  `mkMass 1` is the maximum
(`Mk_one_le_iff`), so at the node itself `𝔐(q_w) < 2 · min{𝔪_1(q_w), 𝔐(q_w)} = 2 ·
𝔐(q_w)`.  The empty word has mass `1` (`cond_nil`). -/

/-- **The base case.**  `(c+2)_1` holds at every node with `C = 2`: take `Γ = {[]}`. -/
theorem graded_one (P : IETDatum₂ α n) : Graded P 1 2 := by
  intro w
  -- `GradedStep` lists the pointwise bound before the mass, so the two goals come in that order
  refine ⟨{[]}, prefixFree_singleton [], ?_, ?_⟩
  · intro δ hδ
    rw [Finset.mem_singleton] at hδ
    subst hδ
    simp only [List.append_nil, min_self]
    have hpos : 0 < mkMass 1 (colSum P w) :=
      mkMass_colSum_pos P w le_rfl (P.card_pos)
    nlinarith
  · rw [Finset.sum_singleton, cond_nil]
    norm_num

/-! ## 3. Pigeonhole over the finitely many `k`-subsets `𝒜'`  `𝔪_k(q) = max_{#𝒜' = k} m_{𝒜'}(q)`,
and the maximum is attained on one of the finitely many `k`-subsets.  Splitting a family of mass `>
1/C₀` according to *a* subset attaining the maximum, the heaviest piece carries `> 1/(C₀ ·
#{k-subsets})`. -/

/-- **The pigeonhole, in AGY's form (its family `Γ₁`)**: from `(c+2)_k` with constant `C`
one gets a family of mass `> 1/(C · #{k-subsets})` on which `𝔪_k` *is* `m_{𝒜'}` for one fixed
`k`-subset `𝒜'`.  (The source's `Γ₁ ⊆ Γ` with `P_q(Γ₁) > C_1^{-1}`, `C_1 = C₀ · C(d,k)`.) -/
theorem graded_min (P : IETDatum₂ α n) {k : ℕ} {C : ℝ} (hk : k ≤ Fintype.card α)
    (hC : 0 < C) (h : Graded P k C) :
    GradedStepMin P k C
      (C * (((Finset.univ : Finset α).powersetCard k).card : ℝ)) :=
  gradedStep_min ((graded_iff_gradedStep P k C).mp h) hk hC

/-! ## 4. The induction step, and the end of the induction -/

/-- **The `k → k+1` step of AGY** (its `Γ₁`--`Γ₄` at level `k`): from `(c+2)_k` with some
constant `C > 1` one gets `(c+2)_{k+1}` with some constant `C' > 1`.  This is what the minimal
extension to a row end outside `𝒜'` and the Kerckhoff dichotomy supply together; §6 derives it from
`BalanceStep`, which is the form of `Γ₂`--`Γ₄` proved in this library. -/
def InductionStep (P : IETDatum₂ α n) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < Fintype.card α → ∀ C : ℝ, 1 < C → Graded P k C →
    ∃ C' : ℝ, 1 < C' ∧ Graded P (k + 1) C'

/-- **The induction**: `(c+2)_k` for every `k ≤ #α`, from the base case and the step. -/
theorem graded_exists (P : IETDatum₂ α n) (hstep : InductionStep P)
    (k : ℕ) (hk1 : 1 ≤ k) (hkcard : k ≤ Fintype.card α) :
    ∃ C : ℝ, 1 < C ∧ Graded P k C := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hk1 with h1 | h1
    · have hk0 : k = 0 := by omega
      subst hk0
      exact ⟨2, by norm_num, graded_one P⟩
    · obtain ⟨C, hC, hgr⟩ := ih (by omega) (by omega)
      exact hstep k (by omega) (by omega) C hC hgr

/-- **The induction, assembled.**  `InductionStep P` implies the level-`#α` statement
`GradedStep P (#α) C C` for some `C > 1`: the induction starts at `k = 1` (`graded_one`,
`C = 2`) and runs up to `k = #α`, where `𝔪_{#α} = 𝔪` (`mkMass_card`) and, at a single
constant, `Graded` is `GradedStep` (`graded_iff_gradedStep`). -/
theorem exists_gradedStep_card_of_inductionStep (P : IETDatum₂ α n) (hstep : InductionStep P) :
    ∃ C : ℝ, 1 < C ∧ GradedStep P (Fintype.card α) C C := by
  obtain ⟨C, hC, hgr⟩ := graded_exists P hstep (Fintype.card α) (P.card_pos) le_rfl
  exact ⟨C, hC, (graded_iff_gradedStep P _ _).mp hgr⟩

/-! ## 5. The hypothesis is what the rest of the repository supplies -/

/-- **`InductionStep` from `BalanceStep`.**  The constants: the `k`-statement at `A'`
(`GradedStepMin`, `graded_min`, mass `1/(C·C(d,k))`), the balance step (mass `1/(K C)`, bound
`K C`), and `gradedStep_succ`, whose output is the `(k+1)`-statement with constants
`(2 · K C · C, C · C(d,k) · K C)`; the single constant `max` of the two is the `InductionStep`
constant.  So `InductionStep` is *implied by* the `Γ₂`--`Γ₄` interface of `NodeHeight`. -/
theorem inductionStep_of_balance (P : IETDatum₂ α n) {K : ℝ → ℝ}
    (hbal : BalanceStep P K) (hK : ∀ Cb : ℝ, 1 ≤ Cb → 1 ≤ K Cb) : InductionStep P := by
  intro k hk1 hkcard C hC hgr
  have hkN : 0 < (((Finset.univ : Finset α).powersetCard k).card : ℝ) :=
    powersetCard_univ_card_pos (by omega)
  have hCpos : (0 : ℝ) < C := by linarith
  have hCm : 0 < C * (((Finset.univ : Finset α).powersetCard k).card : ℝ) := mul_pos hCpos hkN
  have hCb1 : (1 : ℝ) ≤ C := le_of_lt hC
  have hKC : 1 ≤ K C := hK C hCb1
  have hmin := graded_min P (k := k) (C := C) (by omega) hCpos hgr
  have hsucc := gradedStep_succ hbal hmin hkcard hCb1 hCm hKC
  have hCmpos : 0 < C * (((Finset.univ : Finset α).powersetCard k).card : ℝ) * K C :=
    mul_pos hCm (by linarith)
  refine ⟨max (2 * K C * C)
    (C * (((Finset.univ : Finset α).powersetCard k).card : ℝ) * K C), ?_, ?_⟩
  · refine lt_of_lt_of_le ?_ (le_max_left _ _)
    have h1 : (1 : ℝ) < K C * C := by
      have h2 : (1 : ℝ) * C ≤ K C * C := mul_le_mul_of_nonneg_right hKC hCpos.le
      linarith
    nlinarith
  · exact (graded_iff_gradedStep P (k + 1) _).mpr
      (gradedStep_const_mono hsucc (by omega) (by omega) (le_max_left _ _) hCmpos
        (le_max_right _ _))

end IntervalExchange.RauzyVeech.RichPath

end
