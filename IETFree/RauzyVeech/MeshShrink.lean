/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import IETFree.RauzyVeech.ChildVolume
public import IETFree.RauzyVeech.ColDiam
public import IETFree.RauzyVeech.NameInfinite
public import IETFree.RauzyVeech.PrefixWord

/-!
# Corollary 2: the base interval of the Rauzy induction shrinks to a point

For a.e. length vector `lam`, along any infinite Rauzy path the renormalised length vectors
`λ^{(k)}` have all coordinates tending to `0`: the level-`k` base interval
`[0, ∑_β λ^{(k)}_β)` shrinks to a point.  This is the mesh hypothesis `hmesh` that
`Measure.measure_eq_of_measurableSet_subset` consumes.

No hypothesis is needed beyond `P.Irreducible` and `2 ≤ n`: in particular the shrinking of the path
cylinders (`Metric.diam (simplexCyl P (pfx p k)) → 0`) is **not** used.

Write `γ_k = pfx p k`, `Q_k = Path.Q P γ_k`, `V_k = vertex P γ_k`, let `w k` be a renormalised
length vector at level `k` (`IsRenorm P γ_k lam (w k)`, i.e. `lam = Q_k · w k` with `w k > 0`),
`mainLetter k = (V_k).last (p k)` the main name and `secondLetter k = (V_k).last (!(p k))` the
secondary name.

1. **Recursion.** `Q_{k+1} = Q_k · (V_k).rvMat (p k)` and `Q_k` is injective, so
   `w k = (V_k).rvMat (p k) · w (k+1)`,
   i.e. `w (k+1) a = w k a - [a = mainLetter k] · w k (secondLetter k)`.
   Positivity of `w (k+1)` at the main name gives the type rule
   `w k (secondLetter k) < w k (mainLetter k)`; this is exactly `HTypeRule`, and the recursion is
   `HNextStep`.
2. **Every letter is a secondary name infinitely often.**  `name_infinite`
gives that every
   letter is a *main* name infinitely often.  The main name is constant along a maximal run of equal
   types (`rvStep_last_self`), and a change of type at the end of a run makes the previous main name
   the new secondary name (`secondary_eq_of_type_ne`).  Runs are finite because otherwise some other
   letter would be a main name only finitely often.
3. **Column sums grow.**  For `colSumInt k b = ∑_a (Q_k)_{ab}` the one-step formula
   `colSumInt (k+1) b = colSumInt k b + [b = secondLetter k] · colSumInt k (mainLetter k)`
   (from `colsum_mul_one_add_single`) and
   `colSumInt k b ≥ 1` give `colSumInt k b ≥ M` eventually, for every letter `b` and every `M`.
4. **Conclusion.**  `Λ := ∑_a lam a` satisfies
   `Λ = ∑_a ∑_c (Q_k)_{ac} w k c ≥ (colSumInt k b) · w k b`,
   so `w k b ≤ Λ / colSumInt k b → 0` for every letter, and `∑_b w k b → 0`, `max_b w k b → 0`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
open IntervalExchange.IETDatum₂

namespace IntervalExchange.RauzyVeech

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} [NeZero n]

/-! ## 1. Notation -/

/-- The vertex of the path after `k` steps, as the vertex of the prefix word `pfx p k` — the form in
which this file's recursions use it; it is `vertexNat` by `IETDatum₂.vertexNat_eq_vertex_ofFn`. -/
noncomputable def pathVertex (P : IETDatum₂ α n) (p : ℕ → Bool) (k : ℕ) : IETDatum₂ α n :=
  vertex P (pfx p k)

/-- The path matrix at level `k`. -/
noncomputable def Qm (P : IETDatum₂ α n) (p : ℕ → Bool) (k : ℕ) : Matrix α α ℤ :=
  IETDatum₂.Path.Q P (pfx p k)

/-- The sum of the renormalised lengths at level `k`: the length of the level-`k` base interval. -/
noncomputable def total (w : ℕ → α → ℝ) (k : ℕ) : ℝ :=
  ∑ b, w k b

/-- The column sum `colSumInt k b = ∑_a (Q_k)_{ab}` of the path matrix, as an integer: the number
of level-`k` floors of the tower over `b`.  Its real-valued form, at the word `pfx p k`, is
`colSum`; the two agree by `colSumInt_cast`. -/
noncomputable def colSumInt (P : IETDatum₂ α n) (p : ℕ → Bool) (k : ℕ) (b : α) : ℤ :=
  ∑ a, Qm P p k a b

/-- **The two column sums are one number**: the integer-valued `colSumInt` at the path `p` and the
real-valued `colSum` at the word `pfx p k` are the same sum. -/
theorem colSumInt_cast (P : IETDatum₂ α n) (p : ℕ → Bool) (k : ℕ) (b : α) :
    (colSumInt P p k b : ℝ) = colSum P (pfx p k) b := by
  rw [colSumInt, colSum, Int.cast_sum]
  rfl

theorem Qm_succ (P : IETDatum₂ α n) (p : ℕ → Bool) (k : ℕ) :
    Qm P p (k + 1) = Qm P p k * (pathVertex P p k).rvMat (p k) := by
  rw [Qm, pfx_succ, IETDatum₂.Path.Q_append, IETDatum₂.Path.Q_singleton]
  rfl

/-! ## 2. The renormalisation recursion -/

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
    (hw : ∀ k, IETDatum₂.IsRenorm P (pfx p k) lam (w k))
    (k : ℕ) : w k = qApply ((pathVertex P p k).rvMat (p k)) (w (k + 1)) := by
  have hinj : Function.Injective (qApply (Qm P p k)) :=
    IETDatum₂.injective_qApply_Q P hP hn (pfx p k)
  refine hinj ?_
  have h1 : qApply (Qm P p k) (qApply ((pathVertex P p k).rvMat (p k)) (w (k + 1)))
      = qApply (Qm P p (k + 1)) (w (k + 1)) := by
    rw [← qApply_mul, ← Qm_succ]
  calc qApply (Qm P p k) (w k)
      = (fun a => (lam a : ℝ)) := ((hw k).2).symm
    _ = qApply (Qm P p (k + 1)) (w (k + 1)) := (hw (k + 1)).2
    _ = qApply (Qm P p k) (qApply ((pathVertex P p k).rvMat (p k)) (w (k + 1))) :=
        h1.symm

omit [DecidableEq α] in
/-- `mainLetter` is the last letter of the vertex reached at time `k`. -/
theorem mainLetter_eq_last (P : IETDatum₂ α n) (p : ℕ → Bool) (k : ℕ) :
    mainLetter P p k = (pathVertex P p k).last (p k) := by
  rw [mainLetter, vertexNat_eq_vertex_ofFn, pathVertex, pfx]

omit [DecidableEq α] in
/-- `secondLetter` is the other letter of the vertex reached at time `k`. -/
theorem secondLetter_eq_last (P : IETDatum₂ α n) (p : ℕ → Bool) (k : ℕ) :
    secondLetter P p k = (pathVertex P p k).last (!(p k)) := by
  rw [secondLetter, vertexNat_eq_vertex_ofFn, pathVertex, pfx]

/-- **The renormalised vectors satisfy the subtraction recursion**: the coordinate of the main name
drops by the coordinate of the secondary name; all other coordinates are unchanged. -/
theorem renorm_sub (hP : P.Irreducible) (hn : 2 ≤ n)
    (hw : ∀ k, IETDatum₂.IsRenorm P (pfx p k) lam (w k))
    (k : ℕ) (a : α) :
    w (k + 1) a = w k a - (if a = mainLetter P p k then w k (secondLetter P p k) else 0) := by
  have hne : (pathVertex P p k).last (p k) ≠ (pathVertex P p k).last (!(p k)) :=
    IETDatum₂.vertex_last_ne_not P hP hn (pfx p k) (p k)
  have hstep : w (k + 1) = qApply ((pathVertex P p k).rvMatInv (p k)) (w k) := by
    rw [rvMat_mul_renorm P p lam w hP hn hw k]
    exact (IETDatum₂.qApply_rvMatInv_qApply_rvMat (pathVertex P p k) (p k) hne (w (k + 1))).symm
  rw [hstep, IETDatum₂.qApply_rvMatInv_apply (pathVertex P p k) (p k) hne (w k) a,
    mainLetter_eq_last, secondLetter_eq_last]

/-- The type rule: the secondary length is strictly smaller than the main one.  This is the
positivity of `w (k+1)` at the main name. -/
theorem secondLetter_lt_mainLetter (hP : P.Irreducible) (hn : 2 ≤ n)
    (hw : ∀ k, IETDatum₂.IsRenorm P (pfx p k) lam (w k)) (k : ℕ) :
    w k (secondLetter P p k) < w k (mainLetter P p k) := by
  have hpos : 0 < w (k + 1) (mainLetter P p k) := (hw (k + 1)).1 (mainLetter P p k)
  rw [renorm_sub P p lam w hP hn hw k (mainLetter P p k), ite_eq_left rfl] at hpos
  linarith

/-- **`HTypeRule` of `MeshShrink`**, for the renormalised vectors. -/
theorem htype (hP : P.Irreducible) (hn : 2 ≤ n)
    (hw : ∀ k, IETDatum₂.IsRenorm P (pfx p k) lam (w k)) :
    HTypeRule P p (wnn w) := by
  intro k
  refine NNReal.coe_lt_coe.mp ?_
  rw [coe_wnn w (fun k => (hw k).1) k, coe_wnn w (fun k => (hw k).1) k]
  exact secondLetter_lt_mainLetter P p lam w hP hn hw k

/-- **`HNextStep` of `MeshShrink`**, for the renormalised vectors. -/
theorem hnext (hP : P.Irreducible) (hn : 2 ≤ n)
    (hw : ∀ k, IETDatum₂.IsRenorm P (pfx p k) lam (w k)) :
    HNextStep P p (wnn w) := by
  intro k
  funext a
  have h := renorm_sub P p lam w hP hn hw k a
  have harg : nextR (wnn w) k (mainLetter P p k) (secondLetter P p k) a =
      w (k + 1) a := by
    rw [nextR]
    by_cases ha : a = mainLetter P p k
    · rw [ite_eq_left ha, coe_wnn w (fun k => (hw k).1) k, coe_wnn w (fun k => (hw k).1) k,
        h, ite_eq_left ha]
    · rw [ite_eq_right ha, coe_wnn w (fun k => (hw k).1) k, h, ite_eq_right ha, sub_zero]
  -- both sides are `Real.toNNReal` of the `nextR` argument definitionally
  change Real.toNNReal (w (k + 1) a) = Real.toNNReal (nextR (wnn w) k _ _ a)
  rw [harg]

/-- At level `0` the renormalised vector is the original one. -/
theorem lam_eq_w_zero (hw : ∀ k, IETDatum₂.IsRenorm P (pfx p k) lam (w k))
    (a : α) : (lam a : ℝ) = w 0 a := by
  have h3 : (lam a : ℝ) = qApply (1 : Matrix α α ℤ) (w 0) a := congrFun (hw 0).2 a
  rw [qApply_apply] at h3
  rw [h3]
  simp [Matrix.one_apply]

end Recursion

/-! ## 3. Every letter is a secondary name infinitely often -/

section Secondary

variable (P : IETDatum₂ α n) (p : ℕ → Bool)

omit [DecidableEq α] in
/-- The main name is constant on a run of equal types: if `p` is constant on `[k, j]`, the main name
at time `j` is the main name at time `k`. -/
theorem mainLetter_const_of_type_const (k : ℕ) (j : ℕ) (hkj : k ≤ j)
    (hc : ∀ i, k ≤ i → i ≤ j → p i = p k) : mainLetter P p j = mainLetter P p k := by
  induction j, hkj using Nat.le_induction with
  | base => rfl
  | succ j hkj ih =>
    have h1 : p (j + 1) = p j := by
      rw [hc (j + 1) (by omega) le_rfl, hc j hkj (by omega)]
    have h2 : mainLetter P p (j + 1) = mainLetter P p j := by
      simp only [mainLetter]
      rw [vertexNat_succ, h1, IETDatum₂.rvStep_last_self]
    rw [h2, ih (fun i h1' h2' => hc i h1' (by omega))]

end Secondary

section SecondaryFrequently

variable (P : IETDatum₂ α n)
variable (p : ℕ → Bool) (lam : α → ℝ≥0) (w : ℕ → α → ℝ)

/-- **Every letter is a secondary name infinitely often.**  `name_infinite` gives that
every letter is a *main* name infinitely often.  The main name is constant along a run of equal
types, and a run cannot be infinite (else some other letter would be a main name only finitely
often).  At the end of a run the type changes, and then the previous main name becomes the new
secondary name (`secondary_eq_of_type_ne`). -/
theorem secondLetter_frequently (hP : P.Irreducible) (hn : 2 ≤ n)
    (hw : ∀ k, IETDatum₂.IsRenorm P (pfx p k) lam (w k)) (b : α) :
    ∃ᶠ k in atTop, secondLetter P p k = b := by
  have hpos (k : ℕ) (a : α) : 0 < wnn w k a :=
    Real.toNNReal_pos.mpr ((hw k).1 a)
  have hmn (a : α) : ∃ᶠ k in atTop, mainLetter P p k = a := name_infinite P hP p (wnn
      w) hpos (htype P p lam w hP hn hw)
      (hnext P p lam w hP hn hw) a
  have hcard : 2 ≤ Fintype.card α := by
    rw [Fintype.card_congr P.piTop, Fintype.card_fin]
    exact hn
  obtain ⟨b', hb'⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card α) b
  by_contra hcon
  rw [not_frequently] at hcon
  obtain ⟨N, hN⟩ := eventually_atTop.mp hcon
  have key (k) (_ : N ≤ k) (hkb : mainLetter P p k = b) :
      ∃ j, k ≤ j ∧ mainLetter P p j = b ∧ secondLetter P p (j + 1) = b := by
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
      have hnm : mainLetter P p m = b := by
        rw [mainLetter_const_of_type_const P p k m hmk hconst]
        exact hkb
      refine ⟨m, hmk, hnm, ?_⟩
      have hsc : secondLetter P p (m + 1) =
          (IETDatum₂.rvStep (vertexNat P p m) (p m)).last (!(p (m + 1))) := by
        simp only [secondLetter]
        rw [vertexNat_succ]
      rw [hsc]
      have hne' : p (m + 1) ≠ p m := by
        intro hh
        have h2 : p (m + 1) = p k := hh.trans (hconst m hmk le_rfl)
        exact hj₀p (by rwa [← hm] at h2)
      rw [IETDatum₂.secondary_eq_of_type_ne (vertexNat P p m) (p m) (p (m + 1)) hne']
      exact hnm
    · exfalso
      push Not at hS
      have hall (j) (hj : k ≤ j) : mainLetter P p j = b := by
        rw [mainLetter_const_of_type_const P p k j hj (fun i h1 _ => hS i h1)]
        exact hkb
      have hfin : ∀ᶠ j in atTop, mainLetter P p j ≠ b' := by
        refine eventually_atTop.mpr ⟨k, fun j hj => ?_⟩
        rw [hall j hj]
        exact fun h => hb' h.symm
      exact absurd (hmn b') (not_frequently.mpr hfin)
  obtain ⟨k, hkb, hk⟩ := ((hmn b).and_eventually (eventually_ge_atTop N)).exists
  obtain ⟨j, hj, _, hsc⟩ := key k hk hkb
  exact hN (j + 1) (le_trans hk (le_trans hj (Nat.le_succ j))) hsc

end SecondaryFrequently

/-! ## 4. The column sums of the path matrix grow without bound -/

section ColumnSums

variable (P : IETDatum₂ α n) (p : ℕ → Bool)

/-- `colSumInt k b ≥ 1`: the column sums of a path matrix are positive (`Path.Q_colsum_pos`). -/
theorem colSumInt_one_le (k : ℕ) (b : α) : 1 ≤ colSumInt P p k b :=
  IETDatum₂.Path.Q_colsum_pos P (pfx p k) b

/-- The bound `colSumInt k b ≥ 0`. -/
theorem colSumInt_nonneg (k : ℕ) (b : α) : 0 ≤ colSumInt P p k b :=
  le_trans zero_le_one (colSumInt_one_le P p k b)

/-- **The one-step formula for the column sums**: only the column of the secondary name changes, and
it grows by the column of the main name. -/
theorem colSumInt_succ (hP : P.Irreducible) (hn : 2 ≤ n) (k : ℕ) (b : α) :
    colSumInt P p (k + 1) b = colSumInt P p k b +
      (if b = secondLetter P p k then colSumInt P p k (mainLetter P p k) else 0) := by
  have hne : (pathVertex P p k).last (p k) ≠ (pathVertex P p k).last (!(p k)) :=
    IETDatum₂.vertex_last_ne_not P hP hn (pfx p k) (p k)
  rw [colSumInt, colSumInt, colSumInt, Qm_succ,
    IETDatum₂.rvMat_eq_one_add_single (pathVertex P p k) (p k) hne,
    mainLetter_eq_last, secondLetter_eq_last]
  exact colsum_mul_one_add_single (Qm P p k) _ _ b

/-- The column sums are nondecreasing. -/
theorem colSumInt_succ_le (hP : P.Irreducible) (hn : 2 ≤ n) (k : ℕ) (b : α) :
    colSumInt P p k b ≤ colSumInt P p (k + 1) b := by
  rw [colSumInt_succ P p hP hn k b]
  by_cases h : b = secondLetter P p k
  · rw [ite_eq_left h]
    exact le_add_of_nonneg_right (colSumInt_nonneg P p k (mainLetter P p k))
  · rw [ite_eq_right h, add_zero]

/-- The column sums are monotone in time. -/
theorem colSumInt_mono (hP : P.Irreducible) (hn : 2 ≤ n) (b : α) {i j : ℕ} (hij : i ≤ j) :
    colSumInt P p i b ≤ colSumInt P p j b := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact le_trans ih (colSumInt_succ_le P p hP hn j b)

/-- **At a time when `b` is the secondary name the column sum grows by at least one.** -/
theorem colSumInt_succ_add (hP : P.Irreducible) (hn : 2 ≤ n) (k : ℕ) {b : α}
    (h : secondLetter P p k = b) : colSumInt P p k b + 1 ≤ colSumInt P p (k + 1) b := by
  rw [colSumInt_succ P p hP hn k b, ite_eq_left h.symm]
  have := colSumInt_one_le P p k (mainLetter P p k)
  linarith

/-- **Eventual lower bounds for the column sums** (in `ℕ` form). -/
theorem colSumInt_eventually_ge_nat (hP : P.Irreducible) (hn : 2 ≤ n) {b : α}
    (hf : ∃ᶠ k in atTop, secondLetter P p k = b) (M : ℕ) :
    ∃ K, ∀ k ≥ K, (M : ℤ) ≤ colSumInt P p k b := by
  induction M with
  | zero => exact ⟨0, fun k _ => colSumInt_nonneg P p k b⟩
  | succ M ih =>
    obtain ⟨K, hK⟩ := ih
    obtain ⟨j, hfj, hjK⟩ := (hf.and_eventually (eventually_ge_atTop K)).exists
    refine ⟨j + 1, fun k hk => ?_⟩
    have h1 := colSumInt_succ_add P p hP hn j hfj
    have h2 : colSumInt P p (j + 1) b ≤ colSumInt P p k b := colSumInt_mono P p hP hn b (by omega)
    have h3 : (M : ℤ) ≤ colSumInt P p j b := hK j hjK
    push_cast
    linarith

/-- **Eventual lower bounds for the column sums** (in `ℤ` form). -/
theorem colSumInt_eventually_ge (hP : P.Irreducible) (hn : 2 ≤ n) {b : α}
    (hf : ∃ᶠ k in atTop, secondLetter P p k = b) (M : ℤ) :
    ∃ K, ∀ k ≥ K, M ≤ colSumInt P p k b := by
  rcases le_or_gt M 0 with hM | hM
  · exact ⟨0, fun k _ => le_trans hM (colSumInt_nonneg P p k b)⟩
  · obtain ⟨M', hM'⟩ : ∃ M' : ℕ, M ≤ (M' : ℤ) := ⟨M.toNat, by omega⟩
    obtain ⟨K, hK⟩ := colSumInt_eventually_ge_nat P p hP hn hf M'
    exact ⟨K, fun k hk => le_trans hM' (hK k hk)⟩

end ColumnSums

/-! ## 5. The bound `Λ ≥ (colSumInt k b) · w k b` and the conclusion -/

section Bound

variable (P : IETDatum₂ α n)
variable (p : ℕ → Bool) (lam : α → ℝ≥0) (w : ℕ → α → ℝ)

/-- **`Λ` as a sum of the level-`k` lengths weighted by the path matrix.** -/
theorem totalLength_eq (hw : ∀ k, IETDatum₂.IsRenorm P (pfx p k) lam (w k)) (k : ℕ) :
    totalLength lam = ∑ a, ∑ c, (Qm P p k a c : ℝ) * w k c := by
  rw [totalLength]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := congrFun (hw k).2 a
  rw [qApply_apply] at h
  exact h

/-- **The key bound**: `Λ ≥ colSumInt k b · w k b`.  Every level-`k` length is at most `Λ` divided
by
the corresponding column sum. -/
theorem colSumInt_mul_le_totalLength (hw : ∀ k, IETDatum₂.IsRenorm P (pfx p k) lam (w k))
    (k : ℕ) (b : α) : (colSumInt P p k b : ℝ) * w k b ≤ totalLength lam := by
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
  have h2 : ((colSumInt P p k b : ℤ) : ℝ) = ∑ a, (Qm P p k a b : ℝ) := by
    rw [colSumInt, Int.cast_sum]
  rw [totalLength_eq P p lam w hw k, h2]
  exact h1

/-- **Each level-`k` length is at most `Λ / colSumInt k b`.** -/
theorem coord_le (hw : ∀ k, IETDatum₂.IsRenorm P (pfx p k) lam (w k))
    (k : ℕ) (b : α) : w k b ≤ totalLength lam / (colSumInt P p k b : ℝ) := by
  have hpos : (0 : ℝ) < (colSumInt P p k b : ℝ) := by
    have h := colSumInt_one_le P p k b
    have h'' : (1 : ℝ) ≤ (colSumInt P p k b : ℝ) := by exact_mod_cast h
    linarith
  rw [le_div_iff₀ hpos, mul_comm]
  exact colSumInt_mul_le_totalLength P p lam w hw k b

/-- `Λ > 0`. -/
theorem totalLength_pos (hw : ∀ k, IETDatum₂.IsRenorm P (pfx p k) lam (w k)) :
    0 < totalLength lam := by
  have : Nonempty α := by
    rw [← Fintype.card_pos_iff]
    exact P.card_pos
  rw [totalLength]
  refine Finset.sum_pos (fun a _ => ?_) Finset.univ_nonempty
  rw [lam_eq_w_zero P p lam w hw a]
  exact (hw 0).1 a

/-- **The mesh statement**: all level-`k` lengths are eventually below `ε`. -/
theorem eventually_coord_lt (hP : P.Irreducible) (hn : 2 ≤ n)
    (hw : ∀ k, IETDatum₂.IsRenorm P (pfx p k) lam (w k))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in atTop, ∀ b : α, w k b < ε := by
  have hLam := totalLength_pos P p lam w hw
  obtain ⟨M, hM⟩ := exists_int_gt (totalLength lam / ε)
  rw [Filter.eventually_all]
  intro b
  obtain ⟨K, hK⟩ := colSumInt_eventually_ge P p hP hn
    (secondLetter_frequently P p lam w hP hn hw b) M
  filter_upwards [eventually_ge_atTop K] with k hk
  have h1 : totalLength lam / ε < (colSumInt P p k b : ℝ) :=
    lt_of_lt_of_le hM (by exact_mod_cast hK k hk)
  have h2 : w k b ≤ totalLength lam / (colSumInt P p k b : ℝ) := coord_le P p lam w hw k b
  have h3 : (0 : ℝ) < (colSumInt P p k b : ℝ) := by
    have h := colSumInt_one_le P p k b
    have h' : (1 : ℝ) ≤ (colSumInt P p k b : ℝ) := by exact_mod_cast h
    linarith
  have h4 : totalLength lam / (colSumInt P p k b : ℝ) < ε := by
    rw [div_lt_iff₀ h3]
    have h5 : totalLength lam < (colSumInt P p k b : ℝ) * ε := by
      rw [div_lt_iff₀ hε] at h1
      linarith
    linarith
  linarith

/-- **The total level-`k` length tends to `0`**: the base interval shrinks to a point. -/
theorem tendsto_total (hP : P.Irreducible) (hn : 2 ≤ n)
    (hw : ∀ k, IETDatum₂.IsRenorm P (pfx p k) lam (w k)) :
    Tendsto (fun k => total w k) atTop (𝓝 0) := by
  have hnn (k) : (0 : ℝ) ≤ total w k := Finset.sum_nonneg fun b _ => le_of_lt ((hw k).1 b)
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [Filter.Eventually.of_forall hnn] with k hk
    linarith
  · have : Nonempty α := by
      rw [← Fintype.card_pos_iff]
      exact P.card_pos
    have hc : (0 : ℝ) < (Fintype.card α : ℝ) := P.card_pos_cast
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

end IntervalExchange.RauzyVeech

end
