/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.PosBlock
public import IETFree.RauzyVeech.MainComponents

/-!
# The peeling: bounded positive blocks along a greedy path make the columns coalesce

Given length vector `lam` whose greedy Rauzy–Veech path runs through entrywise positive path
matrices with entries in a *fixed* range `[1, M]` at unbounded times, the spread of the
normalised columns of `Q(pathWord P lam k)` tends to `0`:

  `PosBlock.peel … : ∀ ε > 0, ∀ᶠ k in atTop, ∀ b b' a, |ncol … b a - ncol … b' a| ≤ ε`

The proof chooses a chain of pairwise disjoint blocks (`Blk`, `exists_chain`) whose words are the
actual segments of the greedy path (`pathWord_eq_of_mem`: a cylinder determines the greedy word),
and multiplies the contraction of `PosBlock.spread_append_contract` along the chain
(`spread_pow_bound`), using that the spread is antitone under appending letters.  The uniform `M`
is essential: the factor of a block is `1 - 1/(d·M_block)`, so only a bound common to all the
blocks makes the product tend to `0`.

No measure theory is involved.  The dictionary to the geometry is `ColShrink.diam_le_of_cols_close`
read through the spread of `PosBlock.lean`; the passage to the ray condition is
`IETFree/RauzyVeech/RayPointwise.lean`. -/

@[expose] public section


open Filter
open scoped NNReal BigOperators

namespace PosBlock

open IETDatum₂

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ} [NeZero n]

/-! ## 0. Elementary bounds on the normalised columns -/

omit [Nonempty α] in
theorem ncol_nonneg_aux (P : IETDatum₂ α n) (γ : List Bool) (b a : α) :
    0 ≤ ColShrink.ncol P γ b a := by
  simp only [ColShrink.ncol]
  exact div_nonneg (by exact_mod_cast IETDatum₂.Path.Q_nonneg P γ a b)
    (le_of_lt (ColShrink.cs_pos P γ b))

omit [Nonempty α] in
theorem ncol_le_one_aux (P : IETDatum₂ α n) (γ : List Bool) (b a : α) :
    ColShrink.ncol P γ b a ≤ 1 := by
  have hle : (IETDatum₂.Path.Q P γ a b : ℝ) ≤ ColShrink.cs P γ b := by
    rw [ColShrink.cs]
    refine Finset.single_le_sum (f := fun a' => (IETDatum₂.Path.Q P γ a' b : ℝ)) ?_
      (Finset.mem_univ a)
    intro a' _
    exact_mod_cast IETDatum₂.Path.Q_nonneg P γ a' b
  simp only [ColShrink.ncol]
  rw [div_le_one (ColShrink.cs_pos P γ b)]
  exact hle

/-- The spread is at most one, at every word. -/
theorem spread_le_one_aux (P : IETDatum₂ α n) (γ : List Bool) : spread P γ ≤ 1 := by
  refine Finset.sup'_le _ _ fun p _ => ?_
  refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;>
    linarith [ncol_nonneg_aux P γ p.1 p.2.2, ncol_le_one_aux P γ p.1 p.2.2,
      ncol_nonneg_aux P γ p.2.1 p.2.2, ncol_le_one_aux P γ p.2.1 p.2.2]

/-! ## 2. Prefixes of the greedy word -/

omit [Nonempty α] in
/-- The greedy words are nested: a later one extends an earlier one. -/
theorem pathWord_eq_append_drop (P : IETDatum₂ α n) (x : α → ℝ≥0) {k l : ℕ} (h : k ≤ l) :
    IETDatum₂.pathWord P x l =
      IETDatum₂.pathWord P x k ++ (IETDatum₂.pathWord P x l).drop k := by
  induction l, h using Nat.le_induction with
  | base => rw [List.drop_eq_nil_of_le (by rw [IETDatum₂.pathWord_length]), List.append_nil]
  | succ l hl ih =>
    have hlen : k ≤ (IETDatum₂.pathWord P x l).length := by
      rw [IETDatum₂.pathWord_length]; exact hl
    rw [IETDatum₂.pathWord_succ, List.drop_append_of_le_length hlen, ← List.append_assoc, ← ih]

/-- The spread is antitone along the greedy word, assuming it is antitone under appending. -/
theorem spread_pathWord_le (P : IETDatum₂ α n) {lam : α → ℝ≥0}
    (hmono : ∀ (γ δ : List Bool), spread P (γ ++ δ) ≤ spread P γ)
    {k l : ℕ} (h : k ≤ l) :
    spread P (IETDatum₂.pathWord P lam l) ≤ spread P (IETDatum₂.pathWord P lam k) := by
  rw [pathWord_eq_append_drop P lam h]
  exact hmono _ _

omit [Nonempty α] in
/-- A cylinder is contained in the cylinder of any prefix of its word. -/
theorem simplexCyl_append_left (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    (γ δ : List Bool) : IETDatum₂.simplexCyl P (γ ++ δ) ⊆ IETDatum₂.simplexCyl P γ := by
  induction δ using List.reverseRecOn with
  | nil => rw [List.append_nil]
  | append_singleton δ d ih =>
    intro x hx
    rw [← List.append_assoc] at hx
    exact ih (IETDatum₂.simplexCyl_append_subset P hP hn (γ ++ δ) d hx)

omit [Nonempty α] in
/-- **The greedy word is determined by any cylinder containing the point**: if `x` lies in the
cylinder of the word `σ`, the first `|σ|` steps of the greedy algorithm are `σ`. -/
theorem pathWord_eq_of_mem (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {x : α → ℝ≥0} (σ : List Bool) (hx : x ∈ IETDatum₂.simplexCyl P σ) :
    IETDatum₂.pathWord P x σ.length = σ := by
  induction σ using List.reverseRecOn with
  | nil => rfl
  | append_singleton γ e ih =>
    have hpar : x ∈ IETDatum₂.simplexCyl P γ :=
      IETDatum₂.simplexCyl_append_subset P hP hn γ e hx
    have h1 : IETDatum₂.pathWord P x γ.length = γ := ih hpar
    have hbr : IETDatum₂.pathBranch P x γ = e := by
      cases e with
      | true => exact (IETDatum₂.pathBranch_eq_true_iff P x γ).mpr hx
      | false =>
        rw [IETDatum₂.pathBranch_eq_false_iff]
        intro hcon
        exact Set.disjoint_left.mp (IETDatum₂.disjoint_simplexCyl_true_false P hP hn γ) hcon hx
    rw [List.length_append, List.length_singleton, IETDatum₂.pathWord_succ, h1,
      IETDatum₂.pathStep, h1, hbr]

/-! ## 3. Blocks and chains of blocks -/

/-- A positive block at a given time, with all the Rauzy–Veech entries between `1` and `M`. -/
structure Blk (P : IETDatum₂ α n) (lam : α → ℝ≥0) (M : ℕ) where
  /-- the time (length of the preceding word) -/
  m : ℕ
  /-- the word leading to the block -/
  w : List Bool
  /-- the word of the block -/
  v : List Bool
  hlen : w.length = m
  hmem : lam ∈ IETDatum₂.simplexCyl P (w ++ v)
  hlo : ∀ a b, 1 ≤ IETDatum₂.Path.Q (IETDatum₂.vertex P w) v a b
  hup : ∀ a b, IETDatum₂.Path.Q (IETDatum₂.vertex P w) v a b ≤ (M : ℤ)

omit [Nonempty α] in
theorem exists_blk (P : IETDatum₂ α n) (lam : α → ℝ≥0) (M : ℕ)
    (hbl : HasPositiveBlocks P lam M) :
    ∀ k : ℕ, ∃ B : Blk P lam M, k ≤ B.m := by
  intro k
  obtain ⟨m, hm, w, v, hlen, hmem, hQ⟩ := hbl k
  exact ⟨⟨m, w, v, hlen, hmem, fun a b => (hQ a b).1, fun a b => (hQ a b).2⟩, hm⟩

omit [Nonempty α] in
/-- **A chain of blocks**: blocks whose supports are disjoint and go to infinity. -/
theorem exists_chain (P : IETDatum₂ α n) (lam : α → ℝ≥0) (M : ℕ)
    (hb : ∀ k : ℕ, ∃ B : Blk P lam M, k ≤ B.m) :
    ∃ B : ℕ → Blk P lam M, ∀ j, (B j).m + (B j).v.length ≤ (B (j + 1)).m := by
  classical
  choose B hB using hb
  exact ⟨fun j => B (Nat.rec 0 (fun _ e => (B e).m + (B e).v.length) j), fun j => hB _⟩

omit [Nonempty α] in
/-- The greedy word at the start of a block is the word of the block. -/
theorem blk_pathWord_start (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {lam : α → ℝ≥0} {M : ℕ} (B : Blk P lam M) :
    IETDatum₂.pathWord P lam B.m = B.w := by
  have h := pathWord_eq_of_mem P hP hn B.w (simplexCyl_append_left P hP hn B.w B.v B.hmem)
  rwa [B.hlen] at h

omit [Nonempty α] in
/-- The greedy word at the end of a block is the word of the block followed by its word. -/
theorem blk_pathWord_end (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {lam : α → ℝ≥0} {M : ℕ} (B : Blk P lam M) :
    IETDatum₂.pathWord P lam (B.m + B.v.length) = B.w ++ B.v := by
  have h := pathWord_eq_of_mem P hP hn (B.w ++ B.v) B.hmem
  rwa [List.length_append, B.hlen] at h

/-- The contraction at a block. -/
theorem blk_contract (P : IETDatum₂ α n) {lam : α → ℝ≥0} {M : ℕ}
    (hcontr : ∀ (γ δ : List Bool),
      (∀ a b, 1 ≤ IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ a b ∧
        IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ a b ≤ (M : ℤ)) →
      spread P (γ ++ δ) ≤
        (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) * spread P γ)
    (B : Blk P lam M) :
    spread P (B.w ++ B.v) ≤
      (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) * spread P B.w :=
  hcontr B.w B.v fun a b => ⟨B.hlo a b, B.hup a b⟩

/-- The spread bound obtained by consuming one block. -/
theorem spread_le_blk (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {lam : α → ℝ≥0} {M : ℕ}
    (hmono : ∀ (γ δ : List Bool), spread P (γ ++ δ) ≤ spread P γ)
    (hcontr : ∀ (γ δ : List Bool),
      (∀ a b, 1 ≤ IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ a b ∧
        IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ a b ≤ (M : ℤ)) →
      spread P (γ ++ δ) ≤
        (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) * spread P γ)
    (B : Blk P lam M) {k : ℕ} (hk : B.m + B.v.length ≤ k) :
    spread P (IETDatum₂.pathWord P lam k) ≤
      (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) *
        spread P (IETDatum₂.pathWord P lam B.m) := by
  calc spread P (IETDatum₂.pathWord P lam k)
      ≤ spread P (IETDatum₂.pathWord P lam (B.m + B.v.length)) := spread_pathWord_le P hmono hk
    _ = spread P (B.w ++ B.v) := by rw [blk_pathWord_end P hP hn B]
    _ ≤ (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) * spread P B.w := blk_contract P hcontr B
    _ = (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) *
          spread P (IETDatum₂.pathWord P lam B.m) := by rw [blk_pathWord_start P hP hn B]

/-! ## 4. The geometric decay of the spread along a chain of blocks -/

/-- **The spread decays geometrically**: after `N` complete blocks the spread is at most `(1 - 1/(d
M)) ^ (N+1)`. -/
theorem spread_pow_bound (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {lam : α → ℝ≥0} {M : ℕ}
    (hmono : ∀ (γ δ : List Bool), spread P (γ ++ δ) ≤ spread P γ)
    (hcontr : ∀ (γ δ : List Bool),
      (∀ a b, 1 ≤ IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ a b ∧
        IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ a b ≤ (M : ℤ)) →
      spread P (γ ++ δ) ≤
        (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) * spread P γ)
    (B : ℕ → Blk P lam M) (hB : ∀ j, (B j).m + (B j).v.length ≤ (B (j + 1)).m)
    (hc0 : 0 ≤ 1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) :
    ∀ (N k : ℕ), (B N).m + (B N).v.length ≤ k →
      spread P (IETDatum₂.pathWord P lam k) ≤
        (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) ^ (N + 1) := by
  intro N
  induction N with
  | zero =>
    intro k hk
    have h6 : spread P (IETDatum₂.pathWord P lam 0) ≤ 1 := by
      have h0 : IETDatum₂.pathWord P lam 0 = ([] : List Bool) := rfl
      rw [h0]
      exact spread_le_one_aux P []
    have h5 : spread P (IETDatum₂.pathWord P lam ((B 0).m)) ≤ 1 :=
      le_trans (spread_pathWord_le P hmono (Nat.zero_le _)) h6
    calc spread P (IETDatum₂.pathWord P lam k)
        ≤ (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) *
            spread P (IETDatum₂.pathWord P lam ((B 0).m)) :=
          spread_le_blk P hP hn hmono hcontr (B 0) hk
      _ ≤ (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) * 1 :=
          mul_le_mul_of_nonneg_left h5 hc0
      _ = (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) ^ (0 + 1) := by
          rw [pow_one, mul_one]
  | succ N ih =>
    intro k hk
    have hNK : (B N).m + (B N).v.length ≤ (B (N + 1)).m := hB N
    calc spread P (IETDatum₂.pathWord P lam k)
        ≤ (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) *
            spread P (IETDatum₂.pathWord P lam ((B (N + 1)).m)) :=
          spread_le_blk P hP hn hmono hcontr (B (N + 1)) hk
      _ ≤ (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) *
            (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) ^ (N + 1) :=
          mul_le_mul_of_nonneg_left (ih ((B (N + 1)).m) hNK) hc0
      _ = (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) ^ (N + 2) := by
          rw [pow_succ]
          ring

/-! ## 5. The peeling -/

/-- **The peeling of the greedy path at uniformly bounded positive blocks**: if the length vector
`lam` meets positive blocks whose Rauzy–Veech matrices all have entries in `[1, M]` for a single
`M`, at arbitrarily large times, then the normalised columns of `Q(pathWord P lam k)` coalesce: the
spread tends to `0`.  The two `spread` inequalities are taken as hypotheses. -/
theorem peel (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {M : ℕ} (hM : 0 < M)
    {lam : α → ℝ≥0}
    (hstop : ∀ k, lam ∉ IETDatum₂.cylStop P (IETDatum₂.pathWord P lam k))
    (hbl : HasPositiveBlocks P lam M)
    (hmono : ∀ (γ δ : List Bool), spread P (γ ++ δ) ≤ spread P γ)
    (hcontr : ∀ (γ δ : List Bool),
      (∀ a b, 1 ≤ IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ a b ∧
        IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ a b ≤ (M : ℤ)) →
      spread P (γ ++ δ) ≤
        (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) * spread P γ) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ b b' a,
      |ColShrink.ncol P (IETDatum₂.pathWord P lam k) b a
        - ColShrink.ncol P (IETDatum₂.pathWord P lam k) b' a| ≤ ε := by
  classical
  -- `hstop` is not needed by the peelling: by `pathWord_eq_of_mem` membership in a child cylinder
  -- already determines the branch, and the two children are disjoint.
  have hstop' : ∀ k, lam ∉ IETDatum₂.cylStop P (IETDatum₂.pathWord P lam k) := hstop
  intro ε hε
  have hcard : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by
    have h : 1 ≤ Fintype.card α := Fintype.card_pos
    exact_mod_cast h
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hden : (0 : ℝ) < (Fintype.card α : ℝ) * (M : ℝ) := by positivity
  have hden1 : (1 : ℝ) ≤ (Fintype.card α : ℝ) * (M : ℝ) := by
    have h := mul_le_mul hcard hM1 (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
    simpa using h
  have hcinv_le : 1 / ((Fintype.card α : ℝ) * (M : ℝ)) ≤ 1 := by
    rw [div_le_one hden]
    exact hden1
  have hcpos : (0 : ℝ) < 1 / ((Fintype.card α : ℝ) * (M : ℝ)) := by positivity
  have hc0 : 0 ≤ 1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ)) := by linarith
  have hclt : 1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ)) < 1 := by linarith
  obtain ⟨B, hB⟩ := exists_chain P lam M (exists_blk P lam M hbl)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (x := ε)
    (y := 1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) hε hclt
  have hpow : (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) ^ (N + 1) ≤
      (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) ^ N := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hc0 N) (by linarith)
  refine Filter.eventually_atTop.mpr ⟨(B N).m + (B N).v.length, fun k hk => ?_⟩
  have hbnd := spread_pow_bound P hP hn hmono hcontr B hB hc0 N k hk
  intro b b' a
  exact le_trans (le_spread P _ b b' a)
    (le_trans hbnd (le_trans hpow hN.le))

/-! ## 6. Integration form: the contraction given by its two separate bounds  `peel` above takes the
contraction with the two bounds on the entries of `Q` combined in a single conjunction, which is the
shape asked for.  The version below is the same result with the two bounds separated, i.e. exactly
the hypotheses of `spread_append_contract` of the algebra file, so that the latter can be plugged in
without further adaptation. -/

/-- **The peeling, in the shape of the two separate bounds** of the contraction lemma. -/
theorem peel_of_contract (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) {M : ℕ}
    (hM : 0 < M) {lam : α → ℝ≥0}
    (hstop : ∀ k, lam ∉ IETDatum₂.cylStop P (IETDatum₂.pathWord P lam k))
    (hbl : HasPositiveBlocks P lam M)
    (hmono : ∀ (γ δ : List Bool), spread P (γ ++ δ) ≤ spread P γ)
    (hcontr : ∀ (γ δ : List Bool),
      (∀ a b, 1 ≤ IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ a b) →
      (∀ a b, IETDatum₂.Path.Q (IETDatum₂.vertex P γ) δ a b ≤ (M : ℤ)) →
      spread P (γ ++ δ) ≤
        (1 - 1 / ((Fintype.card α : ℝ) * (M : ℝ))) * spread P γ) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ b b' a,
      |ColShrink.ncol P (IETDatum₂.pathWord P lam k) b a
        - ColShrink.ncol P (IETDatum₂.pathWord P lam k) b' a| ≤ ε :=
  peel P hP hn hM hstop hbl hmono fun γ δ h =>
    hcontr γ δ (fun a b => (h a b).1) (fun a b => (h a b).2)

end PosBlock

end
