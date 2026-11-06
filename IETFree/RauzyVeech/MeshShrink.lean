/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.NameInfinite
public import IETFree.RauzyVeech.RayPath

/-!
# Corollary 2: the base interval of the Rauzy induction shrinks to a point

For a.e. length vector `lam`, along any infinite Rauzy path the renormalised length vectors
`λ^{(k)}` have all coordinates tending to `0`: the level-`k` base interval
`[0, ∑_β λ^{(k)}_β)` shrinks to a point.  This is the mesh statement `hmesh` consumed by
`LengthInjective.measure_eq_of_floors`.

No hypothesis is needed beyond `P.Irreducible` and `2 ≤ n`: in particular the shrinking of the path
cylinders (`Metric.diam (simplexCyl P (pfx p k)) → 0`) is **not** used.

Write `γ_k = pfx p k`, `Q_k = Path.Q P γ_k`, `V_k = vertex P γ_k`, let `w k` be a renormalised
length vector at level `k` (`IsRenorm P γ_k lam (w k)`, i.e. `lam = Q_k · w k` with `w k > 0`),
`nm k = (V_k).last (p k)` the main name and `scd k = (V_k).last (!(p k))` the secondary name.

1. **Recursion.** `Q_{k+1} = Q_k · (V_k).rvMat (p k)` and `Q_k` is injective, so
   `w k = (V_k).rvMat (p k) · w (k+1)`, i.e. `w (k+1) a = w k a - [a = nm k] · w k (scd k)`.
   Positivity of `w (k+1)` at the main name gives the type rule `w k (scd k) < w k (nm k)`; this is
   exactly `MeshShrink.HType`, and the recursion is `MeshShrink.HNext`.
2. **Every letter is a secondary name infinitely often.**  `MeshShrink.name_infinite`
gives that every
   letter is a *main* name infinitely often.  The main name is constant along a maximal run of equal
   types (`rvStep_last_self`), and a change of type at the end of a run makes the previous main name
   the new secondary name (`secondary_eq_of_type_ne`).  Runs are finite because otherwise some other
   letter would be a main name only finitely often.
3. **Column sums grow.**  For `Cs k b = ∑_a (Q_k)_{ab}` the one-step formula
   `Cs (k+1) b = Cs k b + [b = scd k] · Cs k (nm k)` (from `colsum_mul_one_add_single`) and
   `Cs k b ≥ 1` give `Cs k b ≥ M` eventually, for every letter `b` and every `M`.
4. **Conclusion.**  `Λ := ∑_a lam a` satisfies
   `Λ = ∑_a ∑_c (Q_k)_{ac} w k c ≥ (Cs k b) · w k b`,
   so `w k b ≤ Λ / Cs k b → 0` for every letter, and `∑_b w k b → 0`, `max_b w k b → 0`.
-/

@[expose] public section


open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace MeshShrink

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 0. Notation -/

/-- The vertex of the path after `k` steps. -/
noncomputable def V (P : IETDatum₂ α n) (p : ℕ → Bool) (k : ℕ) : IETDatum₂ α n :=
  IETDatum₂.vertex P (PrefixWord.pfx p k)

/-- The path matrix at level `k`. -/
noncomputable def Qm (P : IETDatum₂ α n) (p : ℕ → Bool) (k : ℕ) : Matrix α α ℤ :=
  IETDatum₂.Path.Q P (PrefixWord.pfx p k)

/-- The main name at time `k`. -/
noncomputable def nm (P : IETDatum₂ α n) (p : ℕ → Bool) (k : ℕ) : α :=
  (V P p k).last (p k)

/-- The secondary name at time `k`. -/
noncomputable def scd (P : IETDatum₂ α n) (p : ℕ → Bool) (k : ℕ) : α :=
  (V P p k).last (!(p k))

/-- The sum of the renormalised lengths at level `k`: the length of the level-`k` base interval. -/
noncomputable def total (w : ℕ → α → ℝ) (k : ℕ) : ℝ :=
  ∑ b, w k b

/-- `Λ = ∑_a λ_a`. -/
noncomputable def Lam (lam : α → ℝ≥0) : ℝ :=
  ∑ a, (lam a : ℝ)

/-- The column sum `Cs k b = ∑_a (Q_k)_{ab}` of the path matrix: the number of level-`k` floors of
the tower over `b`. -/
noncomputable def Cs (P : IETDatum₂ α n) (p : ℕ → Bool) (k : ℕ) (b : α) : ℤ :=
  ∑ a, Qm P p k a b

omit [DecidableEq α] in
theorem V_succ (P : IETDatum₂ α n) (p : ℕ → Bool) (k : ℕ) :
    V P p (k + 1) = IETDatum₂.rvStep (V P p k) (p k) := by
  rw [V, PrefixWord.pfx_succ, IETDatum₂.vertex_append_singleton]
  rfl

theorem Qm_succ (P : IETDatum₂ α n) (p : ℕ → Bool) (k : ℕ) :
    Qm P p (k + 1) = Qm P p k * (V P p k).rvMat (p k) := by
  rw [Qm, PrefixWord.pfx_succ, IETDatum₂.Path.Q_append, IETDatum₂.Path.Q_singleton]
  rfl

omit [DecidableEq α] in
theorem nm_eq_mn (P : IETDatum₂ α n) (p : ℕ → Bool) (k : ℕ) :
    nm P p k = MeshShrink.mn P p k := by
  simp only [nm, MeshShrink.mn, MeshShrink.Vs]
  rw [IETDatum₂.vertexNat_eq_vertex_ofFn]
  rfl

omit [DecidableEq α] in
theorem scd_eq_sc (P : IETDatum₂ α n) (p : ℕ → Bool) (k : ℕ) :
    scd P p k = MeshShrink.sc P p k := by
  simp only [scd, MeshShrink.sc, MeshShrink.Vs]
  rw [IETDatum₂.vertexNat_eq_vertex_ofFn]
  rfl

/-! ## 1. The renormalisation recursion -/

section Recursion

variable (P : IETDatum₂ α n)
variable (p : ℕ → Bool) (lam : α → ℝ≥0) (w : ℕ → α → ℝ)

/-- The renormalised vectors, bundled as nonnegative reals (as `MeshShrink` wants them). -/
noncomputable def wnn (w : ℕ → α → ℝ) : ℕ → α → ℝ≥0 :=
  fun k a => Real.toNNReal (w k a)

omit [Fintype α] [DecidableEq α] in
theorem coe_wnn (hw : ∀ k a, 0 < w k a) (k : ℕ) (a : α) :
    ((wnn w k a : ℝ≥0) : ℝ) = w k a :=
  Real.coe_toNNReal _ (le_of_lt (hw k a))

/-- **One step of the recursion**: `Q_{k+1} = Q_k · V_k.rvMat (p k)` and `Q_k` is injective, so
`w k = V_k.rvMat (p k) · w (k+1)`. -/
theorem rvMat_mul_renorm (hP : P.Irreducible) (hn : 2 ≤ n)
    (hw : ∀ k, IETDatum₂.IsRenorm P (PrefixWord.pfx p k) lam (w k))
    (k : ℕ) : w k = IETDatum₂.qApply ((V P p k).rvMat (p k)) (w (k + 1)) := by
  have hinj : Function.Injective (IETDatum₂.qApply (Qm P p k)) :=
    IETDatum₂.injective_qApply_Q P hP hn (PrefixWord.pfx p k)
  refine hinj ?_
  have h1 : IETDatum₂.qApply (Qm P p k) (IETDatum₂.qApply ((V P p k).rvMat (p k)) (w (k + 1)))
      = IETDatum₂.qApply (Qm P p (k + 1)) (w (k + 1)) := by
    rw [← IETDatum₂.qApply_mul, ← Qm_succ]
  calc IETDatum₂.qApply (Qm P p k) (w k)
      = (fun a => (lam a : ℝ)) := ((hw k).2).symm
    _ = IETDatum₂.qApply (Qm P p (k + 1)) (w (k + 1)) := (hw (k + 1)).2
    _ = IETDatum₂.qApply (Qm P p k) (IETDatum₂.qApply ((V P p k).rvMat (p k)) (w (k + 1))) :=
        h1.symm

/-- **The renormalised vectors satisfy the subtraction recursion**: the coordinate of the main name
drops by the coordinate of the secondary name; all other coordinates are unchanged. -/
theorem renorm_sub (hP : P.Irreducible) (hn : 2 ≤ n)
    (hw : ∀ k, IETDatum₂.IsRenorm P (PrefixWord.pfx p k) lam (w k))
    (k : ℕ) (a : α) :
    w (k + 1) a = w k a - (if a = nm P p k then w k (scd P p k) else 0) := by
  have hne : (V P p k).last (p k) ≠ (V P p k).last (!(p k)) :=
    IETDatum₂.vertex_last_ne_not P hP hn (PrefixWord.pfx p k) (p k)
  have hstep : w (k + 1) = IETDatum₂.qApply ((V P p k).rvMatInv (p k)) (w k) := by
    rw [rvMat_mul_renorm P p lam w hP hn hw k]
    exact (IETDatum₂.qApply_rvMatInv_qApply_rvMat (V P p k) (p k) hne (w (k + 1))).symm
  rw [hstep, IETDatum₂.qApply_rvMatInv_apply (V P p k) (p k) hne (w k) a]
  rfl

/-- The type rule: the secondary length is strictly smaller than the main one.  This is the
positivity of `w (k+1)` at the main name. -/
theorem scd_lt_nm (hP : P.Irreducible) (hn : 2 ≤ n)
    (hw : ∀ k, IETDatum₂.IsRenorm P (PrefixWord.pfx p k) lam (w k)) (k : ℕ) :
    w k (scd P p k) < w k (nm P p k) := by
  have hpos : 0 < w (k + 1) (nm P p k) := (hw (k + 1)).1 (nm P p k)
  rw [renorm_sub P p lam w hP hn hw k (nm P p k), ite_eq_left rfl] at hpos
  linarith

/-- **`HType` of `MeshShrink`**, for the renormalised vectors. -/
theorem htype (hP : P.Irreducible) (hn : 2 ≤ n)
    (hw : ∀ k, IETDatum₂.IsRenorm P (PrefixWord.pfx p k) lam (w k)) :
    MeshShrink.HType P p (wnn w) := by
  intro k
  rw [← nm_eq_mn, ← scd_eq_sc]
  refine NNReal.coe_lt_coe.mp ?_
  rw [coe_wnn w (fun k => (hw k).1) k, coe_wnn w (fun k => (hw k).1) k]
  exact scd_lt_nm P p lam w hP hn hw k

/-- **`HNext` of `MeshShrink`**, for the renormalised vectors. -/
theorem hnext (hP : P.Irreducible) (hn : 2 ≤ n)
    (hw : ∀ k, IETDatum₂.IsRenorm P (PrefixWord.pfx p k) lam (w k)) :
    MeshShrink.HNext P p (wnn w) := by
  intro k
  funext a
  have h := renorm_sub P p lam w hP hn hw k a
  have harg : MeshShrink.nextR (wnn w) k (MeshShrink.mn P p k) (MeshShrink.sc P p k) a =
      w (k + 1) a := by
    rw [MeshShrink.nextR, ← nm_eq_mn, ← scd_eq_sc]
    by_cases ha : a = nm P p k
    · rw [ite_eq_left ha, coe_wnn w (fun k => (hw k).1) k, coe_wnn w (fun k => (hw k).1) k,
        h, ite_eq_left ha]
    · rw [ite_eq_right ha, coe_wnn w (fun k => (hw k).1) k, h, ite_eq_right ha, sub_zero]
  change Real.toNNReal (w (k + 1) a) = Real.toNNReal (MeshShrink.nextR (wnn w) k _ _ a)
  rw [harg]

/-- At level `0` the renormalised vector is the original one. -/
theorem lam_eq_w_zero (hw : ∀ k, IETDatum₂.IsRenorm P (PrefixWord.pfx p k) lam (w k))
    (a : α) : (lam a : ℝ) = w 0 a := by
  have h3 : (lam a : ℝ) = IETDatum₂.qApply (1 : Matrix α α ℤ) (w 0) a := congrFun (hw 0).2 a
  rw [IETDatum₂.qApply_apply] at h3
  rw [h3]
  simp [Matrix.one_apply]

end Recursion

/-! ## 2. Every letter is a secondary name infinitely often -/

section Secondary

variable (P : IETDatum₂ α n) (p : ℕ → Bool)

omit [DecidableEq α] in
/-- The main name is constant on a run of equal types: if `p` is constant on `[k, j]`, the main name
at time `j` is the main name at time `k`. -/
theorem nm_const_of_type_const (k : ℕ) :
    ∀ j, k ≤ j → (∀ i, k ≤ i → i ≤ j → p i = p k) → nm P p j = nm P p k := by
  intro j hkj
  induction j, hkj using Nat.le_induction with
  | base => intro _; rfl
  | succ j hkj ih =>
    intro hc
    have h1 : p (j + 1) = p j := by
      rw [hc (j + 1) (by omega) le_rfl, hc j hkj (by omega)]
    have h2 : nm P p (j + 1) = nm P p j := by
      simp only [nm]
      rw [V_succ, h1, IETDatum₂.rvStep_last_self]
    rw [h2, ih (fun i h1' h2' => hc i h1' (by omega))]

end Secondary

section SecondaryFrequently

variable (P : IETDatum₂ α n)
variable (p : ℕ → Bool) (lam : α → ℝ≥0) (w : ℕ → α → ℝ)

/-- **Every letter is a secondary name infinitely often.**  `MeshShrink.name_infinite` gives that
every letter is a *main* name infinitely often.  The main name is constant along a run of equal
types, and a run cannot be infinite (else some other letter would be a main name only finitely
often).  At the end of a run the type changes, and then the previous main name becomes the new
secondary name (`secondary_eq_of_type_ne`). -/
theorem scd_frequently (hP : P.Irreducible) (hn : 2 ≤ n)
    (hw : ∀ k, IETDatum₂.IsRenorm P (PrefixWord.pfx p k) lam (w k)) (b : α) :
    ∃ᶠ k in atTop, scd P p k = b := by
  have hpos (k : ℕ) (a : α) : 0 < wnn w k a :=
    Real.toNNReal_pos.mpr ((hw k).1 a)
  have hmn (a : α) : ∃ᶠ k in atTop, MeshShrink.mn P p k = a := MeshShrink.name_infinite P hP p (wnn
      w) hpos (htype P p lam w hP hn hw)
      (hnext P p lam w hP hn hw) a
  have hcard : 2 ≤ Fintype.card α := by
    rw [Fintype.card_congr P.piTop, Fintype.card_fin]
    exact hn
  obtain ⟨b', hb'⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card α) b
  by_contra hcon
  rw [not_frequently] at hcon
  obtain ⟨N, hN⟩ := eventually_atTop.mp hcon
  have key (k) (_ : N ≤ k) (hkb : nm P p k = b) : ∃ j, k ≤ j ∧ nm P p j = b ∧ scd P p
      (j + 1) = b := by
    by_cases hS : ∃ j, k ≤ j ∧ p j ≠ p k
    · have hfind := Nat.find_spec hS
      set j₀ := Nat.find hS with hj₀def
      have hj₀k : k ≤ j₀ := hfind.1
      have hj₀p : p j₀ ≠ p k := hfind.2
      have hne : j₀ ≠ k := fun h => hj₀p (by rw [h])
      obtain ⟨m, hm⟩ : ∃ m, j₀ = m + 1 := ⟨j₀ - 1, by omega⟩
      have hmk : k ≤ m := by omega
      have hconst (i) (hi1 : k ≤ i) (hi2 : i ≤ m) : p i = p k := by
        by_contra hpi
        have h1 : j₀ ≤ i := Nat.find_min' hS ⟨hi1, hpi⟩
        omega
      have hnm : nm P p m = b := by
        rw [nm_const_of_type_const P p k m hmk hconst]
        exact hkb
      refine ⟨m, hmk, hnm, ?_⟩
      have hsc : scd P p (m + 1) =
          (IETDatum₂.rvStep (V P p m) (p m)).last (!(p (m + 1))) := by
        simp only [scd]
        rw [V_succ]
      rw [hsc]
      have hne' : p (m + 1) ≠ p m := by
        intro hh
        have h2 : p (m + 1) = p k := hh.trans (hconst m hmk le_rfl)
        exact hj₀p (by rwa [← hm] at h2)
      rw [IETDatum₂.secondary_eq_of_type_ne (V P p m) (p m) (p (m + 1)) hne']
      exact hnm
    · exfalso
      push Not at hS
      have hall (j) (hj : k ≤ j) : nm P p j = b := by
        rw [nm_const_of_type_const P p k j hj (fun i h1 _ => hS i h1)]
        exact hkb
      have hfin : ∀ᶠ j in atTop, MeshShrink.mn P p j ≠ b' := by
        refine eventually_atTop.mpr ⟨k, fun j hj => ?_⟩
        rw [← nm_eq_mn, hall j hj]
        exact fun h => hb' h.symm
      exact absurd (hmn b') (not_frequently.mpr hfin)
  obtain ⟨k, hkb, hk⟩ := ((hmn b).and_eventually (eventually_ge_atTop N)).exists
  rw [← nm_eq_mn] at hkb
  obtain ⟨j, hj, _, hsc⟩ := key k hk hkb
  exact hN (j + 1) (le_trans hk (le_trans hj (Nat.le_succ j))) hsc

end SecondaryFrequently

/-! ## 3. The column sums of the path matrix grow without bound -/

section ColumnSums

variable (P : IETDatum₂ α n) (p : ℕ → Bool)

/-- `Cs k b ≥ 1`: the column sums of a path matrix are positive (`Path.Q_colsum_pos`). -/
theorem Cs_one_le (k : ℕ) (b : α) : 1 ≤ Cs P p k b :=
  IETDatum₂.Path.Q_colsum_pos P (PrefixWord.pfx p k) b

/-- The bound `Cs k b ≥ 0`. -/
theorem Cs_nonneg (k : ℕ) (b : α) : 0 ≤ Cs P p k b :=
  le_trans zero_le_one (Cs_one_le P p k b)

/-- **The one-step formula for the column sums**: only the column of the secondary name changes, and
it grows by the column of the main name. -/
theorem Cs_succ (hP : P.Irreducible) (hn : 2 ≤ n) (k : ℕ) (b : α) :
    Cs P p (k + 1) b = Cs P p k b +
      (if b = scd P p k then Cs P p k (nm P p k) else 0) := by
  have hne : (V P p k).last (p k) ≠ (V P p k).last (!(p k)) :=
    IETDatum₂.vertex_last_ne_not P hP hn (PrefixWord.pfx p k) (p k)
  rw [Cs, Cs, Cs, Qm_succ, IETDatum₂.rvMat_eq_one_add_single (V P p k) (p k) hne]
  exact RegionVolume.colsum_mul_one_add_single (Qm P p k) _ _ b

/-- The column sums are nondecreasing. -/
theorem Cs_succ_le (hP : P.Irreducible) (hn : 2 ≤ n) (k : ℕ) (b : α) :
    Cs P p k b ≤ Cs P p (k + 1) b := by
  rw [Cs_succ P p hP hn k b]
  by_cases h : b = scd P p k
  · rw [ite_eq_left h]
    exact le_add_of_nonneg_right (Cs_nonneg P p k (nm P p k))
  · rw [ite_eq_right h, add_zero]

/-- The column sums are monotone in time. -/
theorem Cs_mono (hP : P.Irreducible) (hn : 2 ≤ n) (b : α) {i j : ℕ} (hij : i ≤ j) :
    Cs P p i b ≤ Cs P p j b := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact le_trans ih (Cs_succ_le P p hP hn j b)

/-- **At a time when `b` is the secondary name the column sum grows by at least one.** -/
theorem Cs_succ_add (hP : P.Irreducible) (hn : 2 ≤ n) (k : ℕ) {b : α}
    (h : scd P p k = b) : Cs P p k b + 1 ≤ Cs P p (k + 1) b := by
  rw [Cs_succ P p hP hn k b, ite_eq_left h.symm]
  have := Cs_one_le P p k (nm P p k)
  linarith

/-- **Eventual lower bounds for the column sums** (in `ℕ` form). -/
theorem Cs_eventually_ge_nat (hP : P.Irreducible) (hn : 2 ≤ n) {b : α}
    (hf : ∃ᶠ k in atTop, scd P p k = b) (M : ℕ) :
    ∃ K, ∀ k ≥ K, (M : ℤ) ≤ Cs P p k b := by
  induction M with
  | zero => exact ⟨0, fun k _ => Cs_nonneg P p k b⟩
  | succ M ih =>
    obtain ⟨K, hK⟩ := ih
    obtain ⟨j, hfj, hjK⟩ := (hf.and_eventually (eventually_ge_atTop K)).exists
    refine ⟨j + 1, fun k hk => ?_⟩
    have h1 := Cs_succ_add P p hP hn j hfj
    have h2 : Cs P p (j + 1) b ≤ Cs P p k b := Cs_mono P p hP hn b (by omega)
    have h3 : (M : ℤ) ≤ Cs P p j b := hK j hjK
    push_cast
    linarith

/-- **Eventual lower bounds for the column sums** (in `ℤ` form). -/
theorem Cs_eventually_ge (hP : P.Irreducible) (hn : 2 ≤ n) {b : α}
    (hf : ∃ᶠ k in atTop, scd P p k = b) (M : ℤ) :
    ∃ K, ∀ k ≥ K, M ≤ Cs P p k b := by
  rcases le_or_gt M 0 with hM | hM
  · exact ⟨0, fun k _ => le_trans hM (Cs_nonneg P p k b)⟩
  · obtain ⟨M', hM'⟩ : ∃ M' : ℕ, M ≤ (M' : ℤ) := ⟨M.toNat, by omega⟩
    obtain ⟨K, hK⟩ := Cs_eventually_ge_nat P p hP hn hf M'
    exact ⟨K, fun k hk => le_trans hM' (hK k hk)⟩

end ColumnSums

/-! ## 4. The bound `Λ ≥ (Cs k b) · w k b` and the conclusion -/

section Bound

variable (P : IETDatum₂ α n)
variable (p : ℕ → Bool) (lam : α → ℝ≥0) (w : ℕ → α → ℝ)

/-- **`Λ` as a sum of the level-`k` lengths weighted by the path matrix.** -/
theorem Lam_eq (hw : ∀ k, IETDatum₂.IsRenorm P (PrefixWord.pfx p k) lam (w k)) (k : ℕ) :
    Lam lam = ∑ a, ∑ c, (Qm P p k a c : ℝ) * w k c := by
  rw [Lam]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := congrFun (hw k).2 a
  rw [IETDatum₂.qApply_apply] at h
  exact h

/-- **The key bound**: `Λ ≥ Cs k b · w k b`.  Every level-`k` length is at most `Λ` divided by
the corresponding column sum. -/
theorem Cs_mul_le_Lam (hw : ∀ k, IETDatum₂.IsRenorm P (PrefixWord.pfx p k) lam (w k))
    (k : ℕ) (b : α) : (Cs P p k b : ℝ) * w k b ≤ Lam lam := by
  have hnn (a c : α) : 0 ≤ (Qm P p k a c : ℝ) * w k c :=
    mul_nonneg (by exact_mod_cast IETDatum₂.Path.Q_nonneg P _ a c) (le_of_lt ((hw k).1 c))
  have hterm (a) (ha : a ∈ (Finset.univ : Finset α)) :
      (Qm P p k a b : ℝ) * w k b ≤ ∑ c, (Qm P p k a c : ℝ) * w k c := Finset.single_le_sum (f :=
          fun c => (Qm P p k a c : ℝ) * w k c)
      (fun c _ => hnn a c) (Finset.mem_univ b)
  have h1 : (∑ a, (Qm P p k a b : ℝ)) * w k b
      ≤ ∑ a, ∑ c, (Qm P p k a c : ℝ) * w k c := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hterm
  have h2 : ((Cs P p k b : ℤ) : ℝ) = ∑ a, (Qm P p k a b : ℝ) := by
    rw [Cs, Int.cast_sum]
  rw [Lam_eq P p lam w hw k, h2]
  exact h1

/-- **Each level-`k` length is at most `Λ / Cs k b`.** -/
theorem coord_le (hw : ∀ k, IETDatum₂.IsRenorm P (PrefixWord.pfx p k) lam (w k))
    (k : ℕ) (b : α) : w k b ≤ Lam lam / (Cs P p k b : ℝ) := by
  have hpos : (0 : ℝ) < (Cs P p k b : ℝ) := by
    have h := Cs_one_le P p k b
    have h'' : (1 : ℝ) ≤ (Cs P p k b : ℝ) := by exact_mod_cast h
    linarith
  rw [le_div_iff₀ hpos, mul_comm]
  exact Cs_mul_le_Lam P p lam w hw k b

omit [DecidableEq α] [NeZero n] in
/-- `α` is nonempty, since `2 ≤ n = card α`. -/
theorem card_pos (P : IETDatum₂ α n) (hn : 2 ≤ n) : 0 < Fintype.card α := by
  rw [Fintype.card_congr P.piTop, Fintype.card_fin]
  omega

/-- `Λ > 0`. -/
theorem Lam_pos (_hP : P.Irreducible) (hn : 2 ≤ n)
    (hw : ∀ k, IETDatum₂.IsRenorm P (PrefixWord.pfx p k) lam (w k)) : 0 < Lam lam := by
  have : Nonempty α := by
    rw [← Fintype.card_pos_iff]
    exact card_pos P hn
  rw [Lam]
  refine Finset.sum_pos (fun a _ => ?_) Finset.univ_nonempty
  rw [lam_eq_w_zero P p lam w hw a]
  exact (hw 0).1 a

/-- **The mesh statement**: all level-`k` lengths are eventually below `ε`. -/
theorem eventually_coord_lt (hP : P.Irreducible) (hn : 2 ≤ n)
    (hw : ∀ k, IETDatum₂.IsRenorm P (PrefixWord.pfx p k) lam (w k))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in atTop, ∀ b : α, w k b < ε := by
  have hLam := Lam_pos P p lam w hP hn hw
  obtain ⟨M, hM⟩ := exists_int_gt (Lam lam / ε)
  rw [Filter.eventually_all]
  intro b
  obtain ⟨K, hK⟩ := Cs_eventually_ge P p hP hn
    (scd_frequently P p lam w hP hn hw b) M
  filter_upwards [eventually_ge_atTop K] with k hk
  have h1 : Lam lam / ε < (Cs P p k b : ℝ) :=
    lt_of_lt_of_le hM (by exact_mod_cast hK k hk)
  have h2 : w k b ≤ Lam lam / (Cs P p k b : ℝ) := coord_le P p lam w hw k b
  have h3 : (0 : ℝ) < (Cs P p k b : ℝ) := by
    have h := Cs_one_le P p k b
    have h' : (1 : ℝ) ≤ (Cs P p k b : ℝ) := by exact_mod_cast h
    linarith
  have h4 : Lam lam / (Cs P p k b : ℝ) < ε := by
    rw [div_lt_iff₀ h3]
    have h5 : Lam lam < (Cs P p k b : ℝ) * ε := by
      rw [div_lt_iff₀ hε] at h1
      linarith
    linarith
  linarith

/-- **The total level-`k` length tends to `0`**: the base interval shrinks to a point. -/
theorem tendsto_total (hP : P.Irreducible) (hn : 2 ≤ n)
    (hw : ∀ k, IETDatum₂.IsRenorm P (PrefixWord.pfx p k) lam (w k)) :
    Tendsto (fun k => total w k) atTop (𝓝 0) := by
  have hnn (k) : (0 : ℝ) ≤ total w k := Finset.sum_nonneg fun b _ => le_of_lt ((hw k).1 b)
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [Filter.Eventually.of_forall hnn] with k hk
    linarith
  · have : Nonempty α := by
      rw [← Fintype.card_pos_iff]
      exact card_pos P hn
    have hc : (0 : ℝ) < (Fintype.card α : ℝ) := by
      have h := card_pos P hn
      exact_mod_cast h
    have hε : (0 : ℝ) < a / Fintype.card α := by positivity
    filter_upwards [eventually_coord_lt P p lam w hP hn hw hε] with k hk
    have hsum : total w k < ∑ _b : α, a / Fintype.card α := by
      refine Finset.sum_lt_sum (fun b _ => le_of_lt (hk b)) ⟨Classical.arbitrary α,
        Finset.mem_univ _, hk _⟩
    have hconst : (∑ _b : α, a / Fintype.card α) = a := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    rw [hconst] at hsum
    exact hsum

end Bound

end MeshShrink

end
