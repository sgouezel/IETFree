/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.Path

/-!
# Corollary 4 of Yoccoz: a strictly positive `Q`-matrix out of every vertex

Corollary 4 of Yoccoz, p. 14: for each `m` there is `n > m` with `Q(m+1..n)` strictly positive.
What Lemmas 2 and 5 of Yoccoz actually consume is the *vertex* form: from every vertex of the
Rauzy diagram there is a finite path whose matrix `Q = Path.Q` has all entries `≥ 1`.
 This file contains

* monotonicity of `Q` under appending letters (`Q_le_append_singleton`); the diagonal bound
  `one_le_Q_diag` and the nonnegativity `Path.Q_nonneg` — the formal content of Yoccoz's remark
  "the diagonal terms of the `V` matrices are equal to `1`" — are in `RauzyVeech/Path.lean`;
* the **growth step** `Q_growth`: if `1 ≤ Q(γ) a c` where `c = last e` at the vertex reached
  by `γ`, then `1 ≤ Q(γ[e]) a (last (!e))` — a step whose *name* is `c` adds the *secondary*
  name to the positive set of row `a`;
* the predicate `PairReach`, the purely combinatorial content of Cor. 4 used by Yoccoz's proof:
  from every vertex, every ordered pair `(a,b)` of distinct letters occurs as `(last e, last (!e))`
  at some reachable vertex;
* `exists_pos_word`: `PairReach` implies that from every vertex some word has `Q`-matrix with all
  entries `≥ 1` (Yoccoz's induction on the size of the positive set, with `PairReach` replacing
  Prop. 4.3);
* `exists_pos_word`: `PairReach` gives, from every irreducible vertex, a word whose `Q`-matrix has
  all entries `≥ 1`, and `exists_uniform_bound`: the uniform constant `C₁` of Lemma 2.

`PairReach` itself is proved in `IETFree/RauzyVeech/PairReach.lean`. -/

@[expose] public section

open scoped BigOperators

namespace IntervalExchange

namespace IETDatum₂
namespace Path

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Elementary structure of `rvMat` and of `Q` -/

/-- The diagonal of `V` is `1`. -/
@[simp] theorem rvMat_self (P : IETDatum₂ α n) (e : Bool) (i : α) : P.rvMat e i i = 1 := by
  simp [IETDatum₂.rvMat]

/-- The `(name, secondary)` entry of `V` is `1`. -/
theorem rvMat_name_secondary (P : IETDatum₂ α n) (e : Bool) :
    P.rvMat e (P.last e) (P.last (!e)) = 1 := by
  rw [IETDatum₂.rvMat]
  by_cases h : P.last e = P.last (!e)
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_left ⟨rfl, rfl⟩]

/-- **`Q(γ[e]) = Q(γ) · V`**: appending a letter multiplies on the right by the elementary
matrix of the vertex reached by `γ`. -/
theorem Q_append_singleton (P : IETDatum₂ α n) (γ : List Bool) (e : Bool) :
    Path.Q P (γ ++ [e]) = Path.Q P γ * (vertex P γ).rvMat e := by
  rw [Path.Q_append]
  simp

/-- **Monotonicity of `Q` in the word**: appending a letter never decreases an entry. -/
theorem Q_le_append_singleton (P : IETDatum₂ α n) (γ : List Bool) (e : Bool) (a b : α) :
    Path.Q P γ a b ≤ Path.Q P (γ ++ [e]) a b := by
  rw [Q_append_singleton, Matrix.mul_apply]
  have h := Finset.single_le_sum (f := fun c => Path.Q P γ a c *
    (vertex P γ).rvMat e c b) (fun c _ => mul_nonneg (Q_nonneg P γ a c)
    (rvMat_nonneg (vertex P γ) e c b)) (Finset.mem_univ b)
  simpa using h

/-- Monotonicity of `Q` for an arbitrary extension of the word. -/
theorem Q_le_append (P : IETDatum₂ α n) (γ δ : List Bool) (a b : α) :
    Path.Q P γ a b ≤ Path.Q P (γ ++ δ) a b := by
  induction δ generalizing γ with
  | nil => simp
  | cons e es ih =>
    rw [← List.singleton_append, ← List.append_assoc]
    exact le_trans (Q_le_append_singleton P γ e a b) (ih (γ ++ [e]))

/-- **The growth step of Cor. 4.**  If the `(a, c)` entry of `Q(γ)` is positive, where `c` is the
*name* of the next arrow (the letter last in the order `e`), then appending that arrow makes the
`(a, b)` entry positive for `b` the *secondary* name of the arrow. -/
theorem Q_growth (P : IETDatum₂ α n) (γ : List Bool) (e : Bool) (a : α)
    (h : 1 ≤ Path.Q P γ a ((vertex P γ).last e)) :
    1 ≤ Path.Q P (γ ++ [e]) a ((vertex P γ).last (!e)) := by
  rw [Q_append_singleton, Matrix.mul_apply]
  refine le_trans h ?_
  have h2 := Finset.single_le_sum (f := fun c => Path.Q P γ a c *
    (vertex P γ).rvMat e c ((vertex P γ).last (!e))) (fun c _ => mul_nonneg (Q_nonneg P γ a c)
    (rvMat_nonneg (vertex P γ) e c _)) (Finset.mem_univ ((vertex P γ).last e))
  simpa [rvMat_name_secondary] using h2

/-! ## 2. The combinatorial input: every pair of letters becomes the pair of names -/

/-- **The combinatorial content of Cor. 4.**  From every irreducible vertex, every ordered pair
`(a, b)` of *distinct* letters occurs, at some vertex reachable from it, as the pair
`(last e, last (!e))` — i.e. as the name and the secondary name of one of the two arrows. -/
def PairReach : Prop :=
  ∀ (v : IETDatum₂ α n), v.Irreducible → ∀ a b : α, a ≠ b →
    ∃ w : List Bool, ∃ e : Bool, (vertex v w).last e = a ∧ (vertex v w).last (!e) = b

omit [DecidableEq α] in
/-- If `A ≥ 0` with diagonal `≥ 1` and row `a` of `B` is positive, then row `a` of `A * B`
is positive. -/
theorem one_le_mul_of_one_le (A B : Matrix α α ℤ) (hA : ∀ i j, 0 ≤ A i j)
    (hB : ∀ i j, 0 ≤ B i j) (hAdiag : ∀ i, 1 ≤ A i i) (a : α) (hrow : ∀ b, 1 ≤ B a b)
    (b : α) :
    1 ≤ (A * B) a b := by
  rw [Matrix.mul_apply]
  have h01 : (0 : ℤ) ≤ 1 := zero_le_one
  have h1 : (1 : ℤ) ≤ A a a * B a b := by
    have h := mul_le_mul (hAdiag a) (hrow b) h01 (le_trans h01 (hAdiag a))
    simpa using h
  refine le_trans h1 (Finset.single_le_sum (f := fun c => A a c * B c b) (fun c _ => ?_)
    (Finset.mem_univ a))
  exact mul_nonneg (hA a c) (hB c b)

omit [DecidableEq α] in
/-- If `A, B ≥ 0`, the diagonal of `B` is `≥ 1` and `1 ≤ A a b`, then `1 ≤ (A * B) a b`. -/
theorem one_le_mul_of_one_le_right (A B : Matrix α α ℤ) (hA : ∀ i j, 0 ≤ A i j)
    (hB : ∀ i j, 0 ≤ B i j) (hdiag : ∀ i, 1 ≤ B i i) (a b : α) (h : 1 ≤ A a b) :
    1 ≤ (A * B) a b := by
  rw [Matrix.mul_apply]
  have h01 : (0 : ℤ) ≤ 1 := zero_le_one
  have h1 : (1 : ℤ) ≤ A a b * B b b := by
    have hm : (1 : ℤ) * 1 ≤ A a b * B b b := mul_le_mul h (hdiag b) h01 (le_trans h01 h)
    simpa using hm
  refine le_trans h1 (Finset.single_le_sum (f := fun c => A a c * B c b) (fun c _ => ?_)
    (Finset.mem_univ b))
  exact mul_nonneg (hA a c) (hB c b)

/-- **One row can be made positive**: if `PairReach` holds at `P`, then some word has `1 ≤ Q a b`
for all `b`, for a fixed row `a`.  This is Yoccoz's induction on the size of the set of letters
whose `Q`-entry in row `a` is already positive. -/
theorem exists_pos_row (P : IETDatum₂ α n) (h : PairReach (α := α) (n := n))
    (hP : P.Irreducible) (a : α) :
    ∃ w : List Bool, ∀ b, 1 ≤ Path.Q P w a b := by
  have key (m) : 1 ≤ m → m ≤ Fintype.card α →
      ∃ (w : List Bool) (S : Finset α), S.card = m ∧ a ∈ S ∧
        ∀ b ∈ S, 1 ≤ Path.Q P w a b := by
    induction m with
    | zero => intro h1; omega
    | succ k ih =>
      intro _ hm
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        refine ⟨[], {a}, by simp, by simp, ?_⟩
        intro b hb
        rw [Finset.mem_singleton] at hb
        subst hb
        rw [Path.Q_nil]
        simp
      · obtain ⟨w, S, hcard, haS, hpos⟩ := ih hk (by omega)
        have hproper : S ≠ Finset.univ := by
          intro hSu
          have hc : S.card = Fintype.card α := by rw [hSu, Finset.card_univ]
          omega
        have hex : ∃ b, b ∉ S := by
          by_contra hcon
          push Not at hcon
          exact hproper (Finset.eq_univ_of_forall hcon)
        obtain ⟨b, hbS⟩ := hex
        have hne : a ≠ b := fun hh => hbS (hh ▸ haS)
        obtain ⟨w₁, e, hlast1, hlast2⟩ := h (vertex P w) (vertex_irreducible P w hP) a b hne
        have hlast1' : (vertex P (w ++ w₁)).last e = a := by rw [vertex_append, hlast1]
        have hlast2' : (vertex P (w ++ w₁)).last (!e) = b := by rw [vertex_append, hlast2]
        refine ⟨w ++ (w₁ ++ [e]), insert b S, ?_, Finset.mem_insert_of_mem haS, ?_⟩
        · rw [Finset.card_insert_of_notMem hbS, hcard]
        · intro s hs
          rcases Finset.mem_insert.mp hs with rfl | hsS
          · have h1 : 1 ≤ Path.Q P (w ++ w₁) a ((vertex P (w ++ w₁)).last e) := by
              rw [hlast1']
              exact le_trans (hpos a haS) (Q_le_append P w w₁ a a)
            have h2 := Q_growth P (w ++ w₁) e a h1
            rw [hlast2'] at h2
            rwa [← List.append_assoc w w₁ [e]]
          · exact le_trans (hpos s hsS) (Q_le_append P w (w₁ ++ [e]) a s)
  obtain ⟨w, S, hcard, -, hpos⟩ :=
    key (Fintype.card α) (Fintype.card_pos_iff.mpr ⟨a⟩) le_rfl
  refine ⟨w, fun b => hpos b ?_⟩
  rw [Finset.eq_univ_of_card S hcard]
  exact Finset.mem_univ b

/-- **`Q` can be made strictly positive from every vertex**, given `PairReach`. -/
theorem exists_pos_word (P : IETDatum₂ α n) (h : PairReach (α := α) (n := n)) (hP : P.Irreducible) :
    ∃ w : List Bool, ∀ a b, 1 ≤ Path.Q P w a b := by
  have key (T : Finset α) : ∃ w : List Bool, ∀ a ∈ T, ∀ b, 1 ≤ Path.Q P w a b := by
    refine Finset.induction_on T ?_ ?_
    · exact ⟨[], by simp⟩
    · intro a T ha ih
      obtain ⟨w, hw⟩ := ih
      obtain ⟨w', hw'⟩ := exists_pos_row (vertex P w) h (vertex_irreducible P w hP) a
      refine ⟨w ++ w', ?_⟩
      intro s hs b
      rw [Path.Q_append]
      rcases Finset.mem_insert.mp hs with rfl | hsT
      · exact one_le_mul_of_one_le (Path.Q P w) (Path.Q (vertex P w) w') (Q_nonneg P w)
          (Q_nonneg (vertex P w) w') (one_le_Q_diag P w) s (fun j => hw' j) b
      · exact one_le_mul_of_one_le_right (Path.Q P w) (Path.Q (vertex P w) w')
          (Q_nonneg P w) (Q_nonneg (vertex P w) w') (one_le_Q_diag (vertex P w) w')
          s b (hw s hsT b)
  obtain ⟨w, hw⟩ := key Finset.univ
  exact ⟨w, fun a b => hw a (Finset.mem_univ a) b⟩

/-! ## 3. The positive-matrix statement -/

/-- **The uniform bound `C₁` of Lemma 2** (the blueprint's §10.1): given `PairReach`, one constant
bounds, for
every irreducible vertex, the entries of a positive `Q`-matrix reachable from it — Yoccoz's
`C₁ = max over the finitely many vertices of max_{a,b} Q_{ab}(γ̃_v) < ∞`. -/
theorem exists_uniform_bound (h : PairReach (α := α) (n := n)) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ (P : IETDatum₂ α n), P.Irreducible →
      ∃ w : List Bool, ∀ a b, 1 ≤ Path.Q P w a b ∧ (Path.Q P w a b : ℝ) ≤ C₁ := by
  classical
  -- the diagram is finite: `IETDatum₂ α n` is a pair of bijections `α ≃ Fin n`
  let _ : Fintype (IETDatum₂ α n) :=
    Fintype.ofEquiv ((α ≃ Fin n) × (α ≃ Fin n))
      { toFun := fun p => ⟨p.1, p.2⟩
        invFun := fun P => (P.piTop, P.piBottom)
        left_inv := fun P => rfl
        right_inv := fun p => rfl }
  set W : IETDatum₂ α n → List Bool := fun P =>
    if hP : P.Irreducible then Classical.choose (exists_pos_word P h hP) else [] with hW
  have hWspec (P : IETDatum₂ α n) (hP : P.Irreducible) : ∀ a b, 1 ≤ Path.Q P (W P) a b := by
    intro a b
    have hEq : W P = Classical.choose (exists_pos_word P h hP) := by
      simp only [hW, dite_eq_left hP]
    rw [hEq]
    exact Classical.choose_spec (exists_pos_word P h hP) a b
  have hnonneg (P : IETDatum₂ α n) (a b : α) : 0 ≤ ((Path.Q P (W P) a b : ℤ) : ℝ) := by
    have h0 := Q_nonneg P (W P) a b
    exact_mod_cast h0
  refine ⟨max 1 (∑ P : IETDatum₂ α n, ∑ a : α, ∑ b : α,
    ((Path.Q P (W P) a b : ℤ) : ℝ)), le_max_left 1 _, ?_⟩
  intro P hP
  refine ⟨W P, ?_⟩
  intro a b
  refine ⟨hWspec P hP a b, ?_⟩
  have step1 : ((Path.Q P (W P) a b : ℤ) : ℝ) ≤
      ∑ c : α, ((Path.Q P (W P) a c : ℤ) : ℝ) :=
    Finset.single_le_sum (f := fun c : α => ((Path.Q P (W P) a c : ℤ) : ℝ))
      (fun c _ => hnonneg P a c) (Finset.mem_univ b)
  have step2 : (∑ c : α, ((Path.Q P (W P) a c : ℤ) : ℝ)) ≤
      ∑ a' : α, ∑ c : α, ((Path.Q P (W P) a' c : ℤ) : ℝ) :=
    Finset.single_le_sum (f := fun a' : α => ∑ c : α, ((Path.Q P (W P) a' c : ℤ) : ℝ))
      (fun a' _ => Finset.sum_nonneg (fun c _ => hnonneg P a' c)) (Finset.mem_univ a)
  have step3 : (∑ a' : α, ∑ c : α, ((Path.Q P (W P) a' c : ℤ) : ℝ)) ≤
      ∑ P' : IETDatum₂ α n, ∑ a' : α, ∑ c : α, ((Path.Q P' (W P') a' c : ℤ) : ℝ) :=
    Finset.single_le_sum (f := fun P' : IETDatum₂ α n =>
      ∑ a' : α, ∑ c : α, ((Path.Q P' (W P') a' c : ℤ) : ℝ))
      (fun P' _ => Finset.sum_nonneg (fun a' _ => Finset.sum_nonneg (fun c _ => hnonneg P' a' c)))
      (Finset.mem_univ P)
  linarith [step1, step2, step3,
    le_max_right (1 : ℝ) (∑ P' : IETDatum₂ α n, ∑ a' : α, ∑ c : α,
      ((Path.Q P' (W P') a' c : ℤ) : ℝ))]

end Path
end IETDatum₂

namespace IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 4. The letter at position `0` never moves -/

omit [DecidableEq α] in
/-- A single step leaves the letter at bottom position `0` at position `0`. -/
theorem rvStep_zero_letter (P : IETDatum₂ α n) (e : Bool) :
    (P.rvStep e).piBottom.symm (0 : Fin n) = P.piBottom.symm 0 := by
  cases e with
  | false => rfl
  | true =>
    have h1 : (P.rvStep true).piBottom (P.piBottom.symm 0) = 0 := by
      rw [rvStep_piBottom_true_apply_le P (a := P.piBottom.symm 0) (by simp)]
      simp
    refine (P.rvStep true).piBottom.injective ?_
    rw [Equiv.apply_symm_apply, h1]

omit [DecidableEq α] in
/-- A single step leaves the letter at top position `0` at position `0`. -/
theorem rvStep_zero_letter_top (P : IETDatum₂ α n) (e : Bool) :
    (P.rvStep e).piTop.symm (0 : Fin n) = P.piTop.symm 0 := by
  cases e with
  | true => rfl
  | false =>
    have h1 : (P.rvStep false).piTop (P.piTop.symm 0) = 0 := by
      rw [rvStep_piTop_false_apply_le P (a := P.piTop.symm 0) (by simp)]
      simp
    refine (P.rvStep false).piTop.injective ?_
    rw [Equiv.apply_symm_apply, h1]

omit [DecidableEq α] in
/-- The letter at bottom position `0` is invariant along a path. -/
theorem piBottom_zero_letter (P : IETDatum₂ α n) (w : List Bool) :
    (vertex P w).piBottom.symm (0 : Fin n) = P.piBottom.symm 0 := by
  induction w generalizing P with
  | nil => simp
  | cons e es ih => rw [vertex_cons, ih (P.rvStep e), rvStep_zero_letter P e]

omit [DecidableEq α] in
/-- The letter at top position `0` is invariant along a path. -/
theorem piTop_zero_letter (P : IETDatum₂ α n) (w : List Bool) :
    (vertex P w).piTop.symm (0 : Fin n) = P.piTop.symm 0 := by
  induction w generalizing P with
  | nil => simp
  | cons e es ih => rw [vertex_cons, ih (P.rvStep e), rvStep_zero_letter_top P e]

omit [DecidableEq α] in
/-- Irreducibility gives that the two letters at position `0` differ. -/
theorem first_ne (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    P.piBottom.symm (0 : Fin n) ≠ P.piTop.symm 0 := by
  intro h
  have hperm : P.perm (0 : Fin n) = 0 := by
    rw [IETDatum₂.perm_apply]
    rw [h, Equiv.apply_symm_apply]
  have hall : ∀ i : Fin n, i ≤ (0 : Fin n) := by
    refine hP 0 (fun i hi => ?_)
    have hi0 : i = 0 := Fin.ext (by simp at hi; omega)
    rw [hi0, hperm]
  have h1 : (⟨1, by omega⟩ : Fin n).val ≤ (0 : Fin n).val := hall _
  simp at h1

/-! ## 5. Blocks of steps of a single type: the suffix rotates -/

omit [DecidableEq α] in
/-- `vertex` of a reindexed repetition: one more step of the same type. -/
theorem vertex_replicate_succ (P : IETDatum₂ α n) (j : ℕ) (e : Bool) :
    vertex P (List.replicate (j + 1) e) = rvStep (vertex P (List.replicate j e)) e := by
  rw [List.replicate_succ', vertex_append_singleton]

omit [DecidableEq α] in
/-- The last letters of the inverse datum. -/
@[simp] theorem inv_last_true (P : IETDatum₂ α n) : P.inv.last true = P.last false := (rfl)

omit [DecidableEq α] in
/-- The pivot of a block of `true` steps does not move. -/
theorem true_block_pivot (P : IETDatum₂ α n) (j : ℕ) :
    (vertex P (List.replicate j true)).piBottom ((vertex P (List.replicate j true)).last true)
      = P.piBottom (P.last true) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [vertex_replicate_succ, rvStep_last_self]
    exact (rvStep_piBottom_true_apply_le _ (le_refl _)).trans ih

omit [DecidableEq α] in
/-- Letters at positions `≤ pivot` do not move during a block of `true` steps. -/
theorem true_block_prefix (P : IETDatum₂ α n) (j : ℕ) (a : α)
    (ha : (P.piBottom a).val ≤ (P.piBottom (P.last true)).val) :
    (vertex P (List.replicate j true)).piBottom a = P.piBottom a := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [vertex_replicate_succ]
    have hpiv := true_block_pivot P j
    have h : (vertex P (List.replicate j true)).piBottom a
        ≤ (vertex P (List.replicate j true)).piBottom
          ((vertex P (List.replicate j true)).last true) := by
      rw [hpiv, ih]
      exact Fin.le_def.mpr ha
    exact (rvStep_piBottom_true_apply_le _ h).trans ih

omit [DecidableEq α] in
/-- Letters strictly after the pivot move forward by `j` during a block of `j` `true` steps
(as long as they do not run past the last position). -/
theorem true_block_suffix_val (P : IETDatum₂ α n) (j : ℕ) (i : Fin n)
    (hi : (P.piBottom (P.last true)).val < i.val) (hj : i.val + j ≤ n - 1) :
    ((vertex P (List.replicate j true)).piBottom (P.piBottom.symm i)).val = i.val + j := by
      classical
  induction j with
  | zero => simp
  | succ j ih =>
    rw [vertex_replicate_succ]
    have hpiv := true_block_pivot P j
    have hih := ih (by omega)
    rw [rvStep_piBottom_true_apply]
    have h1 : ¬ ((vertex P (List.replicate j true)).piBottom (P.piBottom.symm i)
        ≤ (vertex P (List.replicate j true)).piBottom
          ((vertex P (List.replicate j true)).last true)) := by
      intro hle
      rw [Fin.le_iff_val_le_val, hpiv, hih] at hle
      omega
    rw [ite_eq_right h1]
    have h2 : ¬ (P.piBottom.symm i = (vertex P (List.replicate j true)).last false) := by
      intro hcon
      have h3 : ((vertex P (List.replicate j true)).piBottom (P.piBottom.symm i)).val = n - 1 := by
        rw [hcon, (vertex P (List.replicate j true)).last_bottom, lastPos_val]
      omega
    rw [ite_eq_right h2]
    rw [fin_add_one_val (p := (vertex P (List.replicate j true)).piBottom (P.piBottom.symm i))
      (by omega)]
    omega

omit [DecidableEq α] in
/-- A block of `true` steps brings any letter after the pivot to the last position. -/
theorem exists_true_block (P : IETDatum₂ α n) (i : Fin n)
    (hi : (P.piBottom (P.last true)).val < i.val) :
    (vertex P (List.replicate (n - 1 - i.val) true)).piBottom (P.piBottom.symm i)
      = lastPos n := by
  refine Fin.ext ?_
  rw [true_block_suffix_val P (n - 1 - i.val) i hi (by omega), lastPos_val]
  omega

omit [DecidableEq α] in
/-- A block of `false` steps is a block of `true` steps of the inverse datum. -/
theorem vertex_replicate_false_eq (P : IETDatum₂ α n) (j : ℕ) :
    vertex P (List.replicate j false) = (vertex P.inv (List.replicate j true)).inv := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hL : vertex P (List.replicate (j + 1) false)
        = rvStep (vertex P (List.replicate j false)) false := vertex_replicate_succ P j false
    have hR : vertex P.inv (List.replicate (j + 1) true)
        = rvStep (vertex P.inv (List.replicate j true)) true :=
      vertex_replicate_succ P.inv j true
    rw [hL, hR, ih]
    exact (rvStep_inv _ true).symm

omit [DecidableEq α] in
/-- A block of `false` steps brings any letter after the pivot to the last position. -/
theorem exists_false_block (P : IETDatum₂ α n) (i : Fin n)
    (hi : (P.piTop (P.last false)).val < i.val) :
    (vertex P (List.replicate (n - 1 - i.val) false)).piTop (P.piTop.symm i)
      = lastPos n := by
  have hi' : ((P.inv).piBottom ((P.inv).last true)).val < i.val := by simpa using hi
  rw [vertex_replicate_false_eq]
  simpa using exists_true_block P.inv i hi'

end IETDatum₂

end IntervalExchange

end
