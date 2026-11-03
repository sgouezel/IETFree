/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.Rigidity.Defs
import IETFree.RauzyVeech.IterGlue2
import IETFree.RauzyVeech.MeshShrink
import IETFree.RauzyVeech.RichPath.RichPathAssembly

/-!
# Hitting a fixed word at arbitrarily late times

This module collects the glue lemmas that turn the richness of the greedy Rauzy path
(`RichPath.richGreedyPath`) into the statement consumed by the rigid step, namely that for a.e.
length vector the base interval at a suitable level along the greedy path is arbitrarily short and
the path passes through a prescribed vertex followed by a prescribed word.

* `pathWord_of_mem_simplexCyl` — off the exceptional null set, membership of `lam` in the cylinder
  of `γ` says that `γ` is the greedy word of `lam` of length `|γ|`; this is
  `CylRec.mem_cyl_iff_pathWord` read in the direction needed here.
* `baseLen_append_le` — the base length is monotone under appending letters to a node.
* `tendsto_baseLen_pathWord` — for a.e. `lam`, the base length along the greedy path tends to `0`
  (`MeshShrink.tendsto_total` applied to the greedy path).
The hitting lemma of §3.3 itself is assembled in `Veech.lean` (`ae_exists_hit_base`, private): it
needs, besides these three, the richness of the greedy path, and it states the bound at the node `w`
rather than at `w ++ γ₀`, which is the node the rigid step is run at.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace IETFree.Rigidity

/-! ## 1. From cylinder membership to the greedy word -/

/-- Off the exceptional null set `CylRec.Nbad P`, membership of `lam` in the cylinder of `γ` says
that the greedy path of `lam` reads `γ` in its first `γ.length` steps. -/
theorem pathWord_of_mem_simplexCyl {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n)
    {lam : α → ℝ≥0} (hN : lam ∉ CylRec.Nbad P) {γ : List Bool}
    (h : lam ∈ IETDatum₂.simplexCyl P γ) :
    IETDatum₂.pathWord P lam γ.length = γ :=
  (CylRec.mem_cyl_iff_pathWord P hP hn hN).mp h

/-! ## 2. Monotonicity of the base length -/

/-- A single Rauzy step never increases a length: `Tower.hatLam` only subtracts (with truncated
subtraction). -/
private theorem hatLam_apply_le {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (lam : α → ℝ≥0) (e : Bool) (a : α) :
    Tower.hatLam P e lam a ≤ lam a := by
  simp only [Tower.hatLam]
  split_ifs with h
  · exact tsub_le_self
  · exact le_rfl

/-- **One step of monotonicity**: appending a single letter never increases the base length. -/
private theorem baseLen_append_singleton_le {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    [NeZero n] (P : IETDatum₂ α n) (lam : α → ℝ≥0) (γ : List Bool) (e : Bool) :
    baseLen P (γ ++ [e]) lam ≤ baseLen P γ lam := by
  simp only [baseLen, IterGlue2.lamAfter_append_singleton]
  exact Finset.sum_le_sum fun a _ => by
    exact_mod_cast hatLam_apply_le (IETDatum₂.vertex P γ) (Tower.lamAfter P γ lam) e a

/-- **The base length is monotone under appending a word**: the base at the deeper node `γ ++ δ` is
at most the base at `γ`. -/
theorem baseLen_append_le {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    {P : IETDatum₂ α n} {lam : α → ℝ≥0} {γ δ : List Bool}
    (hOK : TowerTrue.IterOK P lam (γ ++ δ)) :
    baseLen P (γ ++ δ) lam ≤ baseLen P γ lam := by
  induction δ generalizing γ with
  | nil => simp
  | cons e es ih =>
    have h1 : TowerTrue.IterOK P lam ((γ ++ [e]) ++ es) := by
      rw [List.append_assoc, List.singleton_append]
      exact hOK
    have h2 : baseLen P ((γ ++ [e]) ++ es) lam ≤ baseLen P (γ ++ [e]) lam := ih h1
    have h3 : baseLen P (γ ++ [e]) lam ≤ baseLen P γ lam :=
      baseLen_append_singleton_le P lam γ e
    rw [show γ ++ (e :: es) = (γ ++ [e]) ++ es from by
      rw [← List.singleton_append, ← List.append_assoc]]
    exact le_trans h2 h3

/-! ## 3. The base shrinks to a point along the greedy path -/

/-- **For a.e. `lam`, the base length of the greedy path tends to `0`.** -/
theorem tendsto_baseLen_pathWord {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]
    (P : IETDatum₂ α n) (hP : P.Irreducible) (hn : 2 ≤ n) :
    ∀ᵐ lam ∂(simplexVolumeOn α),
      Tendsto (fun k => baseLen P (IETDatum₂.pathWord P lam k) lam) atTop (𝓝 0) := by
  filter_upwards [IETDatum₂.ae_mem_simplexCyl_nil P,
    IETDatum₂.ae_notMem_cylStop_all P hP hn] with lam h0 hstop
  have hiter := IterGlue2.iterOK_pathWord P hP hn h0 hstop
  set p : ℕ → Bool := IETDatum₂.pathStep P lam with hp
  have hw : ∀ k, IETDatum₂.IsRenorm P (PrefixWord.pfx p k) lam
      (fun a => (Tower.lamAfter P (PrefixWord.pfx p k) lam a : ℝ)) := by
    intro k
    rw [hp, IETDatum₂.pfx_pathStep P lam k]
    exact (IETDatum₂.isRenorm_iff P _ lam _).mpr
      ⟨(hiter k).2, (IterGlue.qApply_lamAfter P hP hn _ lam (hiter k).1).symm⟩
  have hlim := MeshShrink.tendsto_total P p lam
    (fun k a => (Tower.lamAfter P (PrefixWord.pfx p k) lam a : ℝ)) hP hn hw
  simpa only [MeshShrink.total, baseLen, hp, IETDatum₂.pfx_pathStep] using hlim

/-! ## 4. The hitting lemma -/


end IETFree.Rigidity
