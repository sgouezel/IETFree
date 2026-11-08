/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.RauzyReach
public import IETFree.RauzyVeech.RichPath.CylinderMass

/-!
# Bounded lag at a balanced node

For a base vertex `P` and a `C`-balanced node `w` (all heights `colSum P w b` within a factor `C` of
each other), a definite fraction of the cylinder `Δ(w)` consists of points which, at some time `m`
with `|w| < m ≤ |w| + K`, sit at the base vertex `P` and lie in the cylinder of a *fixed* word `γ₀`
read from `P`.

Constants: `K = lagBound P γ₀ + 1 + |γ₀|` and `δ = (1 / (C * d * M))^d`, where `d = card α` and
`M` bounds the entries of `Path.Q Q (pad Q ++ γ₀)` uniformly over all vertices `Q` (a finite sup,
the `matBound` inside `lagBound`).
 Structure of the file:
* §1 `Bal` and the Kerckhoff-type lower bound `cond_ge_of_balanced` (the only use of balance);
* §2 the nonempty return word `padWord` and its three properties;
* §3 the uniform matrix bound `lagBound`.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal
open IntervalExchange.IETDatum₂

namespace IntervalExchange.RauzyVeech.RichPath

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Balanced nodes and the Kerckhoff-type lower bound on `cond` -/

/-- **`C`-balanced node**: all heights `colSum P w b` of the tower at the node `w` are within a
factor `C` of each other (AGY's `𝔐(h) ≤ C · 𝔪(h)`). -/
def Bal (P : IETDatum₂ α n) (w : List Bool) (C : ℝ) : Prop :=
  ∀ b b', colSum P w b ≤ C * colSum P w b'

/-- **Kerckhoff's Corollary 1.2 in cylinder-mass form.**  At a `C`-balanced node `w`, the relative
mass `cond P w η` of any child cylinder is bounded below by `(1/(C·d·M))^d`, where `d = card α` and
`M` bounds the entries of the transfer matrix of the continuation `η`.  This is the only place where
the balance hypothesis is used.  Proof: let `b₀` be a letter of minimal height.  Each height of the
child is `∑_c Q(η)_{c b} h_c ≤ d · M · C · h_{b₀}`, while `h_b ≥ h_{b₀}`; hence each of the `d`
factors `h_b / h'_b` is at least `1/(C·d·M)`. -/
theorem cond_ge_of_balanced (P : IETDatum₂ α n) {C : ℝ} (hC : 1 ≤ C) {w : List Bool}
    (hbal : Bal P w C) {η : List Bool} {M : ℝ} (hM : 1 ≤ M)
    (hQ : ∀ a b, (IETDatum₂.Path.Q (IETDatum₂.vertex P w) η a b : ℝ) ≤ M) :
    (1 / (C * (Fintype.card α : ℝ) * M)) ^ (Fintype.card α) ≤ cond P w η := by
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hMnn : (0 : ℝ) ≤ M := le_of_lt hMpos
  have hd : (0 : ℝ) < (Fintype.card α : ℝ) := P.card_pos_cast
  have hden : (0 : ℝ) < C * (Fintype.card α : ℝ) * M := by positivity
  -- a letter of minimal height
  obtain ⟨b₀, -, hb₀⟩ := Finset.exists_min_image (Finset.univ : Finset α)
    (fun b => colSum P w b)
    (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp P.card_pos))
  -- the height of the child at any letter
  have hbound (b) : colSum P (w ++ η) b ≤
      (Fintype.card α : ℝ) * (M * (C * colSum P w b₀)) := by
    rw [colSum_append_eq_sum]
    have hterm (c) (_ : c ∈ (Finset.univ : Finset α)) :
        (IETDatum₂.Path.Q (IETDatum₂.vertex P w) η c b : ℝ) * colSum P w c
          ≤ M * (C * colSum P w b₀) := by
      exact mul_le_mul (hQ c b) (hbal c b₀) (le_of_lt (colSum_pos P w c)) hMnn
    calc ∑ c, (IETDatum₂.Path.Q (IETDatum₂.vertex P w) η c b : ℝ) * colSum P w c
        ≤ ∑ _c : α, M * (C * colSum P w b₀) := Finset.sum_le_sum hterm
      _ = (Fintype.card α : ℝ) * (M * (C * colSum P w b₀)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- the child height is at most `C · d · M` times the parent height
  have hstep (b) : colSum P (w ++ η) b ≤
      C * (Fintype.card α : ℝ) * M * colSum P w b := by
    have h2 : (0 : ℝ) ≤ C * (Fintype.card α : ℝ) * M := le_of_lt hden
    calc colSum P (w ++ η) b
        ≤ (Fintype.card α : ℝ) * (M * (C * colSum P w b₀)) := hbound b
      _ = C * (Fintype.card α : ℝ) * M * colSum P w b₀ := by ring
      _ ≤ C * (Fintype.card α : ℝ) * M * colSum P w b :=
          mul_le_mul_of_nonneg_left (hb₀ b (Finset.mem_univ b)) h2
  -- each factor of the product is at least `1/(C·d·M)`
  have hfac (b) : 1 / (C * (Fintype.card α : ℝ) * M) ≤
      colSum P w b / colSum P (w ++ η) b := by
    rw [div_le_div_iff₀ hden (colSum_pos P (w ++ η) b), one_mul,
      mul_comm (colSum P w b) (C * (Fintype.card α : ℝ) * M)]
    exact hstep b
  have hsplit : cond P w η =
      ∏ b, (colSum P w b / colSum P (w ++ η) b) := by
    rw [cond, Finset.prod_div_distrib]
  rw [hsplit]
  calc (1 / (C * (Fintype.card α : ℝ) * M)) ^ (Fintype.card α)
      = ∏ _b : α, 1 / (C * (Fintype.card α : ℝ) * M) := by
        rw [Finset.prod_const, Finset.card_univ]
    _ ≤ ∏ b, (colSum P w b / colSum P (w ++ η) b) :=
        Finset.prod_le_prod₀ (fun b _ => by positivity) (fun b _ => hfac b)

/-! ## 2. A nonempty return word -/

/-- The chosen return word from `Q` to `P`, made **nonempty** by prefixing one arrow when the
chosen word is empty.  (Lemma 4.1 needs the hitting time `m` to satisfy `|w| < m`, so the pad
must have positive length.) -/
noncomputable def padWord (P Q : IETDatum₂ α n) : List Bool :=
  if returnWord P Q = [] then [true] ++ returnWord P (Q.rvStep true)
  else returnWord P Q

omit [DecidableEq α] in
/-- The padded word still returns to the base vertex. -/
theorem padWord_spec {P Q : IETDatum₂ α n} (h : Reach P Q) :
    IETDatum₂.vertex Q (padWord P Q) = P := by
  unfold padWord
  by_cases hnil : returnWord P Q = []
  · rw [ite_eq_left hnil, List.singleton_append, IETDatum₂.vertex_cons]
    exact returnWord_spec (reach_step h true)
  · rw [ite_eq_right hnil]
    exact returnWord_spec h

/-! ## 3. A uniform bound on the entries of the transfer matrix of the pad -/

/-- A bound (as a natural number) on the entries of `Path.Q Q (padWord P Q ++ γ₀)`, uniform over
the *finite* set of all vertices `Q` of the diagram.  This replaces AGY's supremum over all
words of length `≤ K`: here the relevant word is always the pad of the current vertex followed by
the fixed `γ₀`, so only finitely many words occur. -/
noncomputable def matBound (P : IETDatum₂ α n) (γ₀ : List Bool) : ℕ :=
  Finset.univ.sup fun p : IETDatum₂ α n × α × α =>
    (IETDatum₂.Path.Q p.1 (padWord P p.1 ++ γ₀) p.2.1 p.2.2).toNat

/-- The resulting real constant, at least `1`. -/
noncomputable def lagBound (P : IETDatum₂ α n) (γ₀ : List Bool) : ℝ :=
  max 1 ((matBound P γ₀ : ℕ) : ℝ)

theorem one_le_lagBound (P : IETDatum₂ α n) (γ₀ : List Bool) : 1 ≤ lagBound P γ₀ :=
  le_max_left _ _

theorem lagBound_pos (P : IETDatum₂ α n) (γ₀ : List Bool) : 0 < lagBound P γ₀ :=
  lt_of_lt_of_le zero_lt_one (one_le_lagBound P γ₀)

/-- Every entry of the transfer matrix of the pad of every vertex is bounded by `lagBound`. -/
theorem pathQ_padWord_le (P : IETDatum₂ α n) (γ₀ : List Bool) (Q : IETDatum₂ α n) (a b : α) :
    (IETDatum₂.Path.Q Q (padWord P Q ++ γ₀) a b : ℝ) ≤ lagBound P γ₀ := by
  have hnn : 0 ≤ IETDatum₂.Path.Q Q (padWord P Q ++ γ₀) a b :=
    IETDatum₂.Path.Q_nonneg Q (padWord P Q ++ γ₀) a b
  have hmem : (Q, a, b) ∈ (Finset.univ : Finset (IETDatum₂ α n × α × α)) := Finset.mem_univ _
  have h1 : (IETDatum₂.Path.Q Q (padWord P Q ++ γ₀) a b).toNat ≤ matBound P γ₀ :=
    Finset.le_sup (s := Finset.univ)
      (f := fun p : IETDatum₂ α n × α × α =>
        (IETDatum₂.Path.Q p.1 (padWord P p.1 ++ γ₀) p.2.1 p.2.2).toNat) hmem
  have hcast : ((IETDatum₂.Path.Q Q (padWord P Q ++ γ₀) a b : ℤ) : ℝ)
      = (((IETDatum₂.Path.Q Q (padWord P Q ++ γ₀) a b).toNat : ℕ) : ℝ) := by
    rw [← Int.toNat_of_nonneg hnn]
    norm_cast
  rw [hcast]
  exact le_trans (by exact_mod_cast h1) (le_max_right _ _)

end IntervalExchange.RauzyVeech.RichPath

end
