# The `change` audit: why each surviving `change` is there

Every `change` in `IETFree/` was tried by deleting it and compiling the module.  For the 35
that survived, this file records the error the deletion produces — the exact reason it cannot
simply be removed — and, where a named replacement was attempted, what that gave instead.  The
campaign itself is recorded in `HISTORY.md`, Addenda 175–185.

Method: delete the statement, run `lake env lean` on the module, keep the first error.  *Did not
find an occurrence of the pattern* means a later `rw` no longer matches; *not definitionally
equal* means the goal is not the target; *unsolved goals* means the next tactic no longer
closes what is left.

- **`CutSetMeasure.lean:381`** — `change g (f y) - y = g (f x) - x`
  deleting it gives: linarith failed to find a contradiction; case refine_5.h1; s t : Finset ℝ
- **`Pair/BlockData.lean:204`** — `change Measure.map ((fun ν : Fin (G.n - 1) → ℝ => simplexMap G.n
        ν) ∘`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; Measure.map
  (simplexMap G.n ∘ ⇑(compLenAffine G.s)) ?m.105; in the target expression
- **`Pair/BlockData.lean:309`** — `change BlockGood (G.blockLam hq2 B.k B.hkl B.hln) B.perm`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; G.blockLam
  hq2 B.k ⋯ ⋯; in the target expression
- **`Pair/BlockEndpoints.lean:286`** — `change (IETDatum.ofMem π hr.1).toIET`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern;
  (IET.toEquiv ?f) (?f⁻¹.toEquiv ?x); in the target expression
- **`Pair/BlockLemma.lean:188`** — `change (Fs i) q / L = ((G.blockLam hq i₀.val (l := i₁.val) hi
        (by omega) i : ℝ≥0) : ℝ)`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; ↑(blockLam
  ?G ?hq ?k ?hkl ?hln ?j); in the target expression
- **`Pair/BlockLemma.lean:194`** — `change (Hs j) q / L`
  deleting it gives: Tactic `rewrite` failed: motive is not type correct:; fun _a => ↑⟨_a / L, ⋯⟩ =
  ↑(RestrictIET.truncatedLengths (simplexMap e q.2) ((G.s i₀) q) ((G.s i₁) q) ⋯ j); Error:
  Application type mismatch: The argument
- **`Pair/Diophantine.lean:1052`** — `change C / (Ktot : ℝ) ^ c / ((max (coeffMax a) (coeffMax b) :
        ℕ) : ℝ) ^ c`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; ∑ i, ↑(a i)
  * (↑(w i) / u) + ∑ j, ↑(b j) * (↑(w' j) / u); in the target expression
- **`Pair/Diophantine.lean:1143`** — `change (∑ i, (a i : ℝ) * ((w i : ℝ) / u)) + ∑ j, (b j : ℝ) *
        ((w' j : ℝ) / u) = 0`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; ∑ i, ↑(a i)
  * (↑(w i) / u) + ∑ j, ↑(b j) * (↑(w' j) / u); in the target expression
- **`Pair/GeneratorChange.lean:52`** — `· change (FreeGroup.lift (fun i : Gen => if i = 0 then
        genY⁻¹ * genX else genY))`
  deleting it gives: unsolved goals; case «1»; ⊢ invSubstGen (substGen (FreeGroup.of ((fun i => i)
  ⟨1, ⋯⟩))) = FreeGroup.of ((fun i => i) ⟨1, ⋯⟩)
  also tried (line 52): `simp only [invSubstGen, substGen]` leaves `if ⟨1, ⋯⟩ = 0` undecided, and
  the following `rw [FreeGroup.lift_apply_of]` then finds nothing (Addendum 180).
- **`Pair/GeneratorChange.lean:81`** — `· change (FreeGroup.lift (fun i : Gen => if i = 0 then f
        else g))`
  deleting it gives: unknown tactic; Type mismatch; FreeGroup.lift fun i => if i = 0 then f else g
  also tried (line 52): `simp only [invSubstGen, substGen]` leaves `if ⟨1, ⋯⟩ = 0` undecided, and
  the following `rw [FreeGroup.lift_apply_of]` then finds nothing (Addendum 180).
- **`Pair/GeneratorChange.lean:87`** — `· change (FreeGroup.lift (fun i : Gen => if i = 0 then f
        else g))`
  deleting it gives: Unknown identifier `hgen`; Unknown identifier `h`
  also tried (line 52): `simp only [invSubstGen, substGen]` leaves `if ⟨1, ⋯⟩ = 0` undecided, and
  the following `rw [FreeGroup.lift_apply_of]` then finds nothing (Addendum 180).
- **`Pair/GeneratorChange.lean:95`** — `change FreeGroup.lift (fun i : Gen => if i = 0 then f else
        g) (substGen w)`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern;
  (FreeGroup.lift fun i => if i = 0 then f else g) (substGen w); in the target expression
  also tried (line 52): `simp only [invSubstGen, substGen]` leaves `if ⟨1, ⋯⟩ = 0` undecided, and
  the following `rw [FreeGroup.lift_apply_of]` then finds nothing (Addendum 180).
- **`Pair/MeasureTools.lean:303`** — `· change h c₁ - c₁ ≠ 0`
  deleting it gives: Invalid `⟨...⟩` notation: The expected type; h.toEquiv (c₁, c₂).1 - (c₁, c₂).1
  = 0 → False; is not an inductive type
- **`Pair/SingularityList.lean:81`** — `change v (Classical.choose (hex k)) < v (Classical.choose
        (hex k'))`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; v
  (Classical.choose ⋯); in the target expression
- **`Pair/SubintervalTransfer.lean:111`** — `change (Fin.snoc z S ∘ Fin.castSucc : Fin r → ℝ) ∈ Z'`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; Fin.snoc z
  S ∘ Fin.castSucc; in the target expression
  note: the site at 486 shapes the goal for the one at 488, which is why deleting it makes *that*
  one fail.
- **`Pair/SubintervalTransfer.lean:486`** — `· change 0 < blockLen k (m + 1) x ⟨i.val, by omega⟩ /
        ∑ j, blockLen k (m + 1) x j`
  deleting it gives: 'change' tactic failed, pattern; ∑ i, blockLen k (m + 1) x ⟨↑i, ⋯⟩ / ∑ j,
  blockLen k (m + 1) x j < 1; is not definitionally equal to target
  note: the site at 486 shapes the goal for the one at 488, which is why deleting it makes *that*
  one fail.
- **`Pair/SubintervalTransfer.lean:488`** — `· change (∑ i : Fin m, blockLen k (m + 1) x ⟨i.val, by
        omega⟩`
  deleting it gives: unsolved goals; case refine_2; n k m : ℕ
  note: the site at 486 shapes the goal for the one at 488, which is why deleting it makes *that*
  one fail.
- **`Pair/SubintervalTransfer.lean:629`** — `change cellLen (n := m + 1) x (0 + j.val) = cellLen (n
        := m + 1) x j`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; 0 + ?n; in
  the target expression
  note: the site at 486 shapes the goal for the one at 488, which is why deleting it makes *that*
  one fail.
- **`RauzyVeech/CylinderVolume.lean:513`** — `change 0 ≤ (M *ᵥ z) a`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; (rvRealMat
  ?N *ᵥ ?z) ?a; in the target expression
- **`RauzyVeech/LevelN.lean:267`** — `change P.piTop (P.last false) = P.perm botCell`
  deleting it gives: unsolved goals; α : Type u_1; inst✝¹ : Fintype α
- **`RauzyVeech/LevelN.lean:269`** — `change P.piBottom.symm.trans (P.piTop.trans
        (IETDatum₂.insertEquiv (IETDatum₂.pivot P false)))`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; P.pivot
  false; in the target expression
- **`RauzyVeech/MeshShrink.lean:190`** — `change Real.toNNReal (w (k + 1) a) = Real.toNNReal
        (MeshShrink.nextR (wnn w) k _ _ a)`
  deleting it gives: unsolved goals; α : Type u_1; inst✝² : Fintype α
  also tried: `simp only [MeshShrink.nextR]` unfolds `nextR` on the right-hand side as well, and the
  following `rw [harg]` then finds nothing (Addendum 184).
- **`RauzyVeech/RauzyReach.lean:105`** — `change (P.rvStep true).piTop = (Q.rvStep true).piTop`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; P.rvStep
  true; in the target expression
  also tried: `rw [← IETDatum₂.rvStep_piTop_true]` (resp. `rvStep_piBottom_false`) rewrites the
  inner `rvStep` instead, giving `((Q.rvStep true).rvStep true).piTop` (Addendum 177).
- **`RauzyVeech/RauzyReach.lean:128`** — `change (P.rvStep false).piBottom = (Q.rvStep
        false).piBottom`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; P.rvStep
  false; in the target expression
  also tried: `rw [← IETDatum₂.rvStep_piTop_true]` (resp. `rvStep_piBottom_false`) rewrites the
  inner `rvStep` instead, giving `((Q.rvStep true).rvStep true).piTop` (Addendum 177).
- **`RauzyVeech/RichPath/LargeLetter.lean:302`** — `change ColShrink.cs P (w ++ δ.take (i + 1)) b`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern;
  ColShrink.cs P (w ++ List.take i δ ++ [ee i]) b; in the target expression
- **`RauzyVeech/TrueStep.lean:1156`** — `change (P.piBottom.trans (IETDatum₂.insertEquiv
        (IETDatum₂.pivot P true))).symm.trans P.piTop`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; P.pivot
  true; in the target expression
- **`RauzyVeech/TrueStep.lean:1165`** — `change (P.piBottom.trans (IETDatum₂.insertEquiv
        (IETDatum₂.pivot P true))) a`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern;
  (Equiv.trans ?f ?g) ?a; in the target expression
- **`Rigidity/Veech.lean:279`** — `change (1 - δ) * baseLen P (w ++ Bw) lam ≤ (Tower.lamAfter P (w
        ++ Bw) lam b : ℝ)`
  deleting it gives: Type mismatch: After simplification, term; hcone; has type
- **`Rigidity/Veech.lean:290`** — `change (1 - δ) * baseLen P (w ++ Bw) lam ≤ (Tower.lamAfter P (w
        ++ Bw) lam b : ℝ)`
  deleting it gives: linarith failed to find a contradiction; case neg; α : Type u_1
- **`UniqueErgodicity/Split.lean:150`** — `change decide ((d : ℝ) ≤ x) = decide ((d : ℝ) < x)`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; decide (↑d
  ≤ x); in the target expression
  also tried: the `decide`/`if` lemmas — the goal after `ext rfl (funext fun d => …)` is stated
  through `SplitI`'s constructor, so no equation matches it.
- **`UniqueErgodicity/Split.lean:167`** — `change z.1.2 d = decide ((d : ℝ) ≤ proj z)`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; decide (↑d
  ≤ z.proj); in the target expression
  also tried: the `decide`/`if` lemmas — the goal after `ext rfl (funext fun d => …)` is stated
  through `SplitI`'s constructor, so no equation matches it.
- **`UniqueErgodicity/Split.lean:179`** — `change z.1.2 d = decide ((d : ℝ) < proj z)`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; decide (↑d
  < z.proj); in the target expression
  also tried: the `decide`/`if` lemmas — the goal after `ext rfl (funext fun d => …)` is stated
  through `SplitI`'s constructor, so no equation matches it.
- **`UniqueErgodicity/Split.lean:187`** — `change z.1.2 d = decide ((d : ℝ) < proj z)`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; decide (↑d
  < z.proj); in the target expression
  also tried: the `decide`/`if` lemmas — the goal after `ext rfl (funext fun d => …)` is stated
  through `SplitI`'s constructor, so no equation matches it.
- **`UniqueErgodicity/Split.lean:199`** — `change z.1.2 d = decide ((d : ℝ) ≤ proj z)`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; decide (↑d
  ≤ z.proj); in the target expression
  also tried: the `decide`/`if` lemmas — the goal after `ext rfl (funext fun d => …)` is stated
  through `SplitI`'s constructor, so no equation matches it.
- **`UniqueErgodicity/Split.lean:212`** — `change z.1.2 d = decide ((d : ℝ) < proj z)`
  deleting it gives: Tactic `rewrite` failed: Did not find an occurrence of the pattern; decide (↑d
  < z.proj); in the target expression
  also tried: the `decide`/`if` lemmas — the goal after `ext rfl (funext fun d => …)` is stated
  through `SplitI`'s constructor, so no equation matches it.

