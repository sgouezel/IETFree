/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.RichPath.RichGreedyPath
public import IETFree.Rigidity.Combinatorics
public import IETFree.Rigidity.Hit
public import IETFree.Rigidity.Matrix
public import IETFree.Rigidity.RigidStep

/-!
# The hitting lemma, and the a.e. rigidity statement

The assembly of the a.e. rigidity statement from two ingredients:

* `Rigidity/Hit.lean` — the hitting lemma, used below in the strengthened form `ae_exists_hit_base`
  (proved here privately, bounding the base length at `w` itself rather than at the *deeper* node
  `w ++ γ₀`);
* `Rigidity/RigidStep.lean` — the rigid step `IETFree.Rigidity.Internal.rigid_step`.

The good node is assembled here as well, as the private `exists_good_node_uniform`: it is the
form the rigid step needs, and it is stated with `M` before `δ` (see below).

For a.e. length vector and every `ε > 0` and `N₀`, an exact small translation on a set of measure
`≥ 1 - ε` after `q ≥ N₀` steps.

Three points of care:

* `rigid_step` needs `BigCell` at the precision `deltaOf ε M` where `M` is the comparability
  constant of the heights *of the same node*, so `M` must be quantified **before** `δ`
  (`exists_good_node_uniform`): the vertex, the cycle and `M` never depend on `δ`, only the length
  `K` of the run of `true`s does.  Without this the composition is circular — `deltaOf ε M` would
  be needed before `M` is known.
* the hitting lemma must bound the base length at `w` itself, not at the deeper node `w ++ γ₀`:
  the base length *decreases* along the word (`baseLen_append_le`), so a bound at the deeper node
  gives nothing at `w ++ Bw` where the rigid step is run.  `ae_exists_hit_base` is the form that
  bounds at `w`;
* at `N₀ = 0` the precision `1/(2N₀)` vanishes, so the assembly uses the target time
  `N₁ = max N₀ 1` and weakens `N₁ ≤ q` to `N₀ ≤ q` (the rigid step happens to be total at
  `N₀ = 0` as well, so this is belt-and-braces).

The quantifier order is `∀ᵐ lam, ∀ ε > 0, ∀ N₀, ∃ …`: the conclusion is proved for the countably
many precisions `ε = 1/(k+1)` (`ae_all_iff`) and transported to every `ε > 0` by monotonicity in
`ε`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

namespace IETFree.Rigidity
namespace Internal

/-! ## 1. The precision `deltaOf` -/

/-- `deltaOf ε M` is positive. -/
private theorem deltaOf_pos {ε : ℝ} (hε : 0 < ε) (M : ℕ) : 0 < deltaOf ε M := by
  rw [deltaOf]
  exact lt_min (by norm_num) (div_pos hε (by positivity))

/-! ## 2. From cylinder membership to the type rule

The next five lemmas are the tree of BLUEPRINT §4.4: they say that a point of the cylinder of a word
follows the Rauzy type rule along it, and they are what makes the good node independent of the
precision `δ`. -/

/-- Membership in a cylinder is monotone under appending letters to the word. -/
private theorem mem_simplexCyl_of_append {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    [NeZero n] {P : IETDatum₂ α n} (hP : P.Irreducible) (hn : 2 ≤ n) (γ δ : List Bool)
    {x : α → ℝ≥0} (h : x ∈ IETDatum₂.simplexCyl P (γ ++ δ)) :
    x ∈ IETDatum₂.simplexCyl P γ := by
  induction δ generalizing γ with
  | nil => simpa using h
  | cons e es ih =>
    have h' : x ∈ IETDatum₂.simplexCyl P ((γ ++ [e]) ++ es) := by
      rwa [List.append_assoc, List.singleton_append]
    exact IETDatum₂.simplexCyl_append_subset P hP hn γ e (ih (γ ++ [e]) h')

/-- A Rauzy step keeps the length vector strictly positive. -/
private theorem hatLam_pos {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hpos : ∀ a, 0 < lam a) {e : Bool}
    (hstep : TowerTrue.StepOK P lam e) : ∀ a, 0 < Tower.hatLam P e lam a := by
  intro a
  rw [Tower.hatLam]
  by_cases ha : a = P.last e
  · rw [if_pos ha]
    subst ha
    cases e with
    | false =>
      rw [TowerTrue.stepOK_false_iff] at hstep
      exact tsub_pos_of_lt hstep
    | true =>
      rw [TowerTrue.stepOK_true_iff] at hstep
      exact tsub_pos_of_lt hstep
  · rw [if_neg ha]
    exact hpos a

/-- The renormalised length vector stays strictly positive along an `IterOK` word. -/
private theorem lamAfter_pos_of_iterOK {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    [NeZero n] {P : IETDatum₂ α n} {lam : α → ℝ≥0} (hpos : ∀ a, 0 < lam a) {γ : List Bool}
    (hOK : TowerTrue.IterOK P lam γ) : ∀ a, 0 < Tower.lamAfter P γ lam a := by
  induction γ generalizing P lam with
  | nil => exact hpos
  | cons e es ih =>
    have h1 : TowerTrue.StepOK P lam e := by
      have h := hOK
      rw [TowerTrue.IterOK] at h
      exact h.1
    have h2 : TowerTrue.IterOK (P.rvStep e) (Tower.hatLam P e lam) es := by
      have h := hOK
      rw [TowerTrue.IterOK] at h
      exact h.2
    rw [Tower.lamAfter_cons]
    exact ih (hatLam_pos hpos h1) h2

/-- **A point of a cylinder follows the word**: membership of `lam` in the cylinder of `γ` forces
the Rauzy type rule along `γ`. -/
private theorem iterOK_of_mem_simplexCyl {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    [NeZero n] {P : IETDatum₂ α n} (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∀ (γ : List Bool) {lam : α → ℝ≥0}, lam ∈ IETDatum₂.simplexCyl P γ →
      TowerTrue.IterOK P lam γ := by
  intro γ
  induction γ using List.reverseRecOn with
  | nil => intro lam _; trivial
  | append_singleton γ e ih =>
    intro lam hmem
    obtain ⟨hmemγ, w, hw, hlt⟩ :=
      (IETDatum₂.mem_simplexCyl_append_iff P hP hn γ e lam).mp hmem
    have hOKγ : TowerTrue.IterOK P lam γ := ih hmemγ
    have hnil : lam ∈ IETDatum₂.simplexCyl P ([] : List Bool) := by
      simpa using mem_simplexCyl_of_append hP hn ([] : List Bool) γ hmemγ
    have hpos : ∀ a, 0 < lam a := ((IETDatum₂.mem_simplexCyl_nil_iff P lam).mp hnil).2
    have hposA : ∀ a, 0 < Tower.lamAfter P γ lam a := lamAfter_pos_of_iterOK hpos hOKγ
    have hren : IETDatum₂.IsRenorm P γ lam (fun a => (Tower.lamAfter P γ lam a : ℝ)) :=
      (IETDatum₂.isRenorm_iff P γ lam _).mpr
        ⟨hposA, (IterGlue.qApply_lamAfter P hP hn γ lam hOKγ).symm⟩
    have hw_eq : w = fun a => (Tower.lamAfter P γ lam a : ℝ) :=
      IETDatum₂.IsRenorm.unique hP hn hw hren
    have hcmp : Tower.lamAfter P γ lam ((IETDatum₂.vertex P γ).last (!e))
        < Tower.lamAfter P γ lam ((IETDatum₂.vertex P γ).last e) := by
      have h1 : ((Tower.lamAfter P γ lam ((IETDatum₂.vertex P γ).last (!e)) : ℝ))
          < ((Tower.lamAfter P γ lam ((IETDatum₂.vertex P γ).last e) : ℝ)) := by
        have h1a := congrFun hw_eq ((IETDatum₂.vertex P γ).last (!e))
        have h1b := congrFun hw_eq ((IETDatum₂.vertex P γ).last e)
        rw [← h1a, ← h1b]
        exact hlt
      exact_mod_cast h1
    exact (IterGlue2.iterOK_append_singleton P lam γ e).mpr
      ⟨hOKγ, (IterGlue2.stepOK_last_iff (IETDatum₂.vertex P γ)
        (Tower.lamAfter P γ lam) e).mpr hcmp⟩

/-- The sum of the natural-number parts of a family of nonnegative integers is the natural-number
part of the sum. -/
private theorem sum_toNat {ι : Type*} [Fintype ι] (f : ι → ℤ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i, (f i).toNat) = (∑ i, f i).toNat := by
  have h : ((∑ i, (f i).toNat : ℕ) : ℤ) = ∑ i, f i := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hf i)
  rw [← h, Int.toNat_natCast]

/-! ## 3. The good node, with the comparability constant fixed first -/

/-- **The good node, uniform in the precision.**  There is a vertex `π₁` reachable from `P`, a
positive cycle `Bw` at it, a letter `b` and a bound `M ≥ 2`, such that the node `w ++ Bw` has
heights dominated by the `b`-th one with constant `M`, and such that for every precision `δ > 0` a
run `true^K` of length `K = K(δ)` forces the `b`-cell of `w ++ Bw` to occupy `1 - δ` of the base.

This is BLUEPRINT §4.4 with the quantifier on `δ` inside the one on `M`: in the proof of §4.4 the
vertex, the positive cycle and the constant `M` come from
`exists_vertex_last_true_eq_piBottom_zero` and `exists_pos_cycle` and do not depend on the
precision, while the length of the run is `Nat.ceil ((1 - δ)/δ) * (Fintype.card α - 1)`.  The
naive quantifier order (`M` after `δ`) cannot compose with `Internal.rigid_step`, which needs
`BigCell` at `deltaOf ε M` for the very `M` it dominates the heights with — that is why the node is
stated this way round. -/
private theorem exists_good_node_uniform {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    [NeZero n] (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∃ (π₁ : IETDatum₂ α n) (_hπ₁ : ∃ u : List Bool, IETDatum₂.vertex P u = π₁)
      (Bw : List Bool) (b : α) (M : ℕ),
      1 < M ∧
      (∀ (w : List Bool), IETDatum₂.vertex P w = π₁ → ∀ c : α,
        height P (w ++ Bw) c ≤ M * height P (w ++ Bw) b) ∧
      ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ (w : List Bool), IETDatum₂.vertex P w = π₁ →
        ∀ {lam : α → ℝ≥0},
          lam ∈ IETDatum₂.simplexCyl P (w ++ Bw ++ List.replicate K true) →
          BigCell P (w ++ Bw) lam δ b := by
  classical
  obtain ⟨π₁, u, hu, hx⟩ := exists_vertex_last_true_eq_piBottom_zero P hP hn
  have hπ₁ : π₁.Irreducible := by
    rw [← hu]
    exact IETDatum₂.vertex_irreducible P u hP
  obtain ⟨Bw, Mℤ, hMℤ, hcyc, hbounded⟩ := exists_pos_cycle π₁ hπ₁ hn
  set b : α := π₁.piBottom.symm 0 with hb
  have hlast : π₁.last true = b := by rw [hb]; exact hx
  set M : ℕ := Mℤ.natAbs with hMset
  have hMℤ0 : (0 : ℤ) ≤ Mℤ := by linarith
  have hMeq : ((M : ℕ) : ℤ) = Mℤ := by
    rw [hMset]
    exact Int.natAbs_of_nonneg hMℤ0
  have htoNat : Mℤ.toNat = M := by
    rw [hMset]
    have h1 : ((Mℤ.toNat : ℕ) : ℤ) = Mℤ := Int.toNat_of_nonneg hMℤ0
    have h2 : ((Mℤ.natAbs : ℕ) : ℤ) = Mℤ := Int.natAbs_of_nonneg hMℤ0
    exact_mod_cast h1.trans h2.symm
  have hM1 : 1 < M := by
    rw [hMset]
    have h := Int.natAbs_lt_natAbs_of_nonneg_of_lt (a := (1 : ℤ)) (b := Mℤ) (by norm_num) hMℤ
    simpa using h
  -- the comparability of the heights, uniform in the prefix
  have hdom (w : List Bool) (hw : IETDatum₂.vertex P w = π₁) (c : α) :
    height P (w ++ Bw) c ≤ M * height P (w ++ Bw) b := by
    have hQw : IETDatum₂.Path.Q P (w ++ Bw)
        = IETDatum₂.Path.Q P w * IETDatum₂.Path.Q π₁ Bw := by
      rw [IETDatum₂.Path.Q_append, hw]
    have hcol := colsum_le_of_one_le (IETDatum₂.Path.Q P w) (IETDatum₂.Path.Q π₁ Bw) Mℤ
      (fun a c => IETDatum₂.Path.Q_nonneg P w a c)
      (fun a c => (hbounded a c).1) (fun a c => (hbounded a c).2) c b
    rw [← hQw] at hcol
    have hSb : (0 : ℤ) ≤ ∑ a, IETDatum₂.Path.Q P (w ++ Bw) a b :=
      Finset.sum_nonneg (fun a _ => IETDatum₂.Path.Q_nonneg P (w ++ Bw) a b)
    have hc : height P (w ++ Bw) c
        = (∑ a, IETDatum₂.Path.Q P (w ++ Bw) a c).toNat :=
      sum_toNat _ (fun a => IETDatum₂.Path.Q_nonneg P (w ++ Bw) a c)
    have hb' : height P (w ++ Bw) b
        = (∑ a, IETDatum₂.Path.Q P (w ++ Bw) a b).toNat :=
      sum_toNat _ (fun a => IETDatum₂.Path.Q_nonneg P (w ++ Bw) a b)
    calc height P (w ++ Bw) c
        = (∑ a, IETDatum₂.Path.Q P (w ++ Bw) a c).toNat := hc
      _ ≤ (Mℤ * ∑ a, IETDatum₂.Path.Q P (w ++ Bw) a b).toNat := Int.toNat_le_toNat hcol
      _ = Mℤ.toNat * (∑ a, IETDatum₂.Path.Q P (w ++ Bw) a b).toNat :=
            Int.toNat_mul hMℤ0 hSb
      _ = M * height P (w ++ Bw) b := by rw [htoNat, hb']
  -- the big cell at the node `w ++ Bw`, from a run long enough for the prescribed `δ`
  have hbig : ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ (w : List Bool), IETDatum₂.vertex P w = π₁ →
      ∀ {lam : α → ℝ≥0},
        lam ∈ IETDatum₂.simplexCyl P (w ++ Bw ++ List.replicate K true) →
        BigCell P (w ++ Bw) lam δ b := by
    intro δ hδ
    by_cases hδ1 : δ ≤ 1
    · -- the cone computation, with the strictly positive vector at the end of the run
      have hcard : Fintype.card α = n := by
        rw [← Fintype.card_fin n]
        exact Fintype.card_congr π₁.piTop
      have hcard1 : 0 < Fintype.card α - 1 := by
        rw [hcard]
        omega
      set K : ℕ := Nat.ceil ((1 - δ) / δ) * (Fintype.card α - 1) with hKset
      have hKdef : K / (Fintype.card α - 1) = Nat.ceil ((1 - δ) / δ) := by
        rw [hKset]
        exact Nat.mul_div_cancel _ hcard1
      have hK : (1 - δ) / δ ≤ (K / (Fintype.card α - 1) : ℕ) := by
        rw [hKdef]
        exact Nat.le_ceil _
      refine ⟨K, fun w hw lam hmem => ?_⟩
      obtain ⟨-, σ', hpos', hσ'eq⟩ := (IETDatum₂.mem_simplexCyl_iff P
        (w ++ Bw ++ List.replicate K true) lam).mp hmem
      have hmemγ : lam ∈ IETDatum₂.simplexCyl P (w ++ Bw) :=
        mem_simplexCyl_of_append hP hn (w ++ Bw) (List.replicate K true) hmem
      have hOKγ : TowerTrue.IterOK P lam (w ++ Bw) :=
        iterOK_of_mem_simplexCyl hP hn (w ++ Bw) hmemγ
      have hσ : (fun a => (Tower.lamAfter P (w ++ Bw) lam a : ℝ))
          = IETDatum₂.qApply (IETDatum₂.Path.Q π₁ (List.replicate K true)) σ' := by
        refine IETDatum₂.injective_qApply_Q P hP hn (w ++ Bw) ?_
        have h1 : IETDatum₂.qApply (IETDatum₂.Path.Q P (w ++ Bw))
            (fun a => (Tower.lamAfter P (w ++ Bw) lam a : ℝ)) = fun a => (lam a : ℝ) :=
          IterGlue.qApply_lamAfter P hP hn (w ++ Bw) lam hOKγ
        have h2 : IETDatum₂.qApply (IETDatum₂.Path.Q P (w ++ Bw))
            (IETDatum₂.qApply (IETDatum₂.Path.Q π₁ (List.replicate K true)) σ')
              = fun a => (lam a : ℝ) := by
          have hv : IETDatum₂.vertex P (w ++ Bw) = π₁ := by
            rw [IETDatum₂.vertex_append, hw, hcyc]
          rw [← IETDatum₂.qApply_mul, ← hv, ← IETDatum₂.Path.Q_append]
          exact hσ'eq.symm
        exact h1.trans h2.symm
      have hcone := bigCell_of_mem_cone π₁ hπ₁ hn hx hδ hδ1 hK hpos' hσ
      change (1 - δ) * baseLen P (w ++ Bw) lam ≤ (Tower.lamAfter P (w ++ Bw) lam b : ℝ)
      rw [← hlast]
      simpa [baseLen] using hcone
    · -- for `δ > 1` the big-cell inequality is trivial
      have hδ1' : 1 < δ := not_le.mp hδ1
      refine ⟨0, fun w _hw lam _hmem => ?_⟩
      have h1 : 1 - δ < 0 := by linarith
      have h2 : (0 : ℝ) ≤ baseLen P (w ++ Bw) lam :=
        Finset.sum_nonneg (fun a _ => (Tower.lamAfter P (w ++ Bw) lam a).coe_nonneg)
      have h3 : (0 : ℝ) ≤ (Tower.lamAfter P (w ++ Bw) lam b : ℝ) :=
        (Tower.lamAfter P (w ++ Bw) lam b).coe_nonneg
      change (1 - δ) * baseLen P (w ++ Bw) lam ≤ (Tower.lamAfter P (w ++ Bw) lam b : ℝ)
      nlinarith
  exact ⟨π₁, ⟨u, hu⟩, Bw, b, M, hM1, hdom, hbig⟩

/-! ## 4. Monotonicity of `IterOK` under prefixes -/

/-- A prefix of an `IterOK` word is `IterOK`. -/
private theorem iterOK_of_append_left {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    {P : IETDatum₂ α n} {lam : α → ℝ≥0} {γ δ : List Bool}
    (h : TowerTrue.IterOK P lam (γ ++ δ)) : TowerTrue.IterOK P lam γ := by
  induction γ generalizing P lam with
  | nil => trivial
  | cons e es ih => exact ⟨h.1, ih h.2⟩

/-! ## 5. The hitting lemma with the base length at the vertex -/

/-- **The hitting lemma, with the base length at the node `w`.**  The base length decreases along
the word, so a bound at the deeper node `w ++ γ₀` gives nothing at `w ++ Bw`, where the rigid
step is run; this form bounds it at `w` itself, as §6 needs. -/
private theorem ae_exists_hit_base {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (π₁ : IETDatum₂ α n) (hπ₁ : ∃ u : List Bool, IETDatum₂.vertex P u = π₁)
    (γ₀ : List Bool) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ lam ∂(simplexVolumeOn α), ∀ N₀ : ℕ, ∃ m : ℕ,
      N₀ ≤ m ∧ ∃ w : List Bool, w.length = m ∧ IETDatum₂.vertex P w = π₁ ∧
      lam ∈ IETDatum₂.simplexCyl P (w ++ γ₀) ∧ baseLen P w lam ≤ η := by
  obtain ⟨u, hu⟩ := hπ₁
  have hrich := RichPath.richGreedyPath P hP hn π₁ u hu γ₀
  have htend := tendsto_baseLen_pathWord P hP hn
  have haeN : ∀ᵐ lam ∂(simplexVolumeOn α), lam ∉ CylRec.Nbad P := by
    rw [← measure_eq_zero_iff_ae_notMem]
    exact CylRec.measure_Nbad P hP hn
  filter_upwards [hrich, htend, haeN] with lam hlam hlim hN
  intro N₀
  have hev : ∀ᶠ k : ℕ in atTop, baseLen P (IETDatum₂.pathWord P lam k) lam < η :=
    (tendsto_order.mp hlim).2 η hη
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  obtain ⟨m, hm, w, hwlen, hwvert, hwmem⟩ := hlam (max K N₀)
  have hmK : K ≤ m := le_trans (le_max_left K N₀) hm
  refine ⟨m, le_trans (le_max_right K N₀) hm, w, hwlen, hwvert, hwmem, ?_⟩
  have hcyl : IETDatum₂.pathWord P lam (w ++ γ₀).length = w ++ γ₀ :=
    pathWord_of_mem_simplexCyl P hP hn hN hwmem
  have hlen : (w ++ γ₀).length = m + γ₀.length := by rw [List.length_append, hwlen]
  have hword : w = IETDatum₂.pathWord P lam m := by
    have h1 : (IETDatum₂.pathWord P lam (m + γ₀.length)).take m
        = IETDatum₂.pathWord P lam m :=
      RichPath.take_pathWord_le P lam (Nat.le_add_right m γ₀.length)
    have h2 : (IETDatum₂.pathWord P lam (m + γ₀.length)).take m = w := by
      rw [← hlen, hcyl, ← hwlen, List.take_left]
    rw [h2] at h1
    exact h1
  rw [hword]
  exact le_of_lt (hK m hmK)

/-! ## 6. The assembly -/

/-- **Veech's Theorem 1.4, improved**: the return time may be taken arbitrarily large. -/
theorem ae_rigid_step {α : Type*} [Fintype α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∀ᵐ lam ∂(simplexVolumeOn α), ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ,
      ∃ (q : ℕ) (t : ℝ) (B : Set ℝ),
        N₀ ≤ q ∧ |t| ≤ ε ∧ B ⊆ Set.Ico (0:ℝ) 1 ∧ MeasurableSet B ∧
        1 - ε ≤ (volume B).toReal ∧
        ∀ x ∈ B, (⇑(P.toIET lam))^[q] x = x + t := by
  classical
  have hcard : Fintype.card α ≠ 0 := by
    rw [Fintype.card_congr P.piTop, Fintype.card_fin]
    exact NeZero.ne n
  have hmem : ∀ᵐ lam ∂(simplexVolumeOn α), lam ∈ simplexOn α :=
    ae_mem_simplexOn_of_card_ne_zero hcard
  have hNbad : ∀ᵐ lam ∂(simplexVolumeOn α), lam ∉ CylRec.Nbad P := by
    rw [← measure_eq_zero_iff_ae_notMem]
    exact CylRec.measure_Nbad P hP hn
  have step (ε : ℝ) (N₀ : ℕ) (hε : 0 < ε) :
    ∀ᵐ lam ∂(simplexVolumeOn α),
      ∃ (q : ℕ) (t : ℝ) (B : Set ℝ),
        N₀ ≤ q ∧ |t| ≤ ε ∧ B ⊆ Set.Ico (0:ℝ) 1 ∧ MeasurableSet B ∧
        1 - ε ≤ (volume B).toReal ∧
        ∀ x ∈ B, (⇑(P.toIET lam))^[q] x = x + t := by
    -- the good node, whose constant `M` is fixed before the precision `deltaOf ε M`
    obtain ⟨π₁, hπ₁, Bw, b, M, hM, hdom, hbig⟩ := exists_good_node_uniform P hP hn
    obtain ⟨K, hK⟩ := hbig (deltaOf ε M) (deltaOf_pos hε M)
    -- the target time, at least `1` so that the precision `1/(2N₀)` is positive
    set N₁ : ℕ := max N₀ 1 with hN₁def
    have hN₁pos : 1 ≤ N₁ := le_max_right N₀ 1
    have hN₁ge : N₀ ≤ N₁ := le_max_left N₀ 1
    have hηpos : 0 < min ε (1 / (2 * (N₁ : ℝ))) := by
      refine lt_min hε ?_
      have hN₁ : (0 : ℝ) < (N₁ : ℝ) := by exact_mod_cast hN₁pos
      positivity
    filter_upwards [ae_exists_hit_base P hP hn π₁ hπ₁ (Bw ++ List.replicate K true) hηpos,
      hmem, hNbad] with lam hhit hlamS hN
    obtain ⟨m, _hm, w, _hwlen, hwvert, hwmem, hbasew⟩ := hhit N₁
    have hroot : lam ∈ IETDatum₂.simplexCyl P [] := by
      have h := not_or.mp ((CylRec.mem_Nbad_iff P lam).not.mp hN)
      exact not_not.mp h.2
    have hstop : ∀ γ : List Bool, lam ∉ IETDatum₂.cylStop P γ := by
      have h := not_or.mp ((CylRec.mem_Nbad_iff P lam).not.mp hN)
      exact fun γ hγ => h.1 ⟨γ, hγ⟩
    have hcyl : IETDatum₂.pathWord P lam (w ++ (Bw ++ List.replicate K true)).length
        = w ++ (Bw ++ List.replicate K true) :=
      pathWord_of_mem_simplexCyl P hP hn hN hwmem
    have hOKfull : TowerTrue.IterOK P lam (w ++ Bw ++ List.replicate K true) := by
      have h := (IterGlue2.iterOK_pathWord P hP hn hroot hstop
        (w ++ (Bw ++ List.replicate K true)).length).1
      rw [hcyl, ← List.append_assoc] at h
      exact h
    have hOKγ : TowerTrue.IterOK P lam (w ++ Bw) :=
      iterOK_of_append_left (δ := List.replicate K true) hOKfull
    have hΛ : baseLen P (w ++ Bw) lam ≤ min ε (1 / (2 * (N₁ : ℝ))) :=
      le_trans (baseLen_append_le (γ := w) (δ := Bw) hOKγ) hbasew
    have hmemrun : lam ∈ IETDatum₂.simplexCyl P (w ++ Bw ++ List.replicate K true) := by
      rw [List.append_assoc]
      exact hwmem
    have hbignode : BigCell P (w ++ Bw) lam (deltaOf ε M) b := hK w hwvert hmemrun
    obtain ⟨q, t, B, hq, ht, hsub, hmeas, hvol, hex⟩ :=
      rigid_step (N₀ := N₁) (lam := lam) (γ := w ++ Bw) (b := b) (M := M)
        P hP hn hε hlamS hstop hM hOKγ hbignode (hdom w hwvert) hΛ
    exact ⟨q, t, B, le_trans hN₁ge hq, ht, hsub, hmeas, hvol, hex⟩
  -- the countably many precisions `1/(k+1)` give every `ε > 0`
  have hfam : ∀ᵐ lam ∂(simplexVolumeOn α), ∀ p : ℕ × ℕ,
      ∃ (q : ℕ) (t : ℝ) (B : Set ℝ),
        p.2 ≤ q ∧ |t| ≤ 1 / ((p.1 : ℝ) + 1) ∧ B ⊆ Set.Ico (0:ℝ) 1 ∧ MeasurableSet B ∧
        1 - 1 / ((p.1 : ℝ) + 1) ≤ (volume B).toReal ∧
        ∀ x ∈ B, (⇑(P.toIET lam))^[q] x = x + t := by
    rw [ae_all_iff]
    rintro ⟨k, N₀⟩
    exact step (1 / ((k : ℝ) + 1)) N₀ (by positivity)
  filter_upwards [hfam] with lam hlam ε hε N₀
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨q, t, B, hq, ht, hsub, hmeas, hvol, hex⟩ := hlam (k, N₀)
  exact ⟨q, t, B, hq, le_trans ht hk.le, hsub, hmeas, le_trans (by linarith) hvol, hex⟩

end Internal
end IETFree.Rigidity

end
