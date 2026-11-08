# Working notes: what is true about this tree now

This file is the **current** record: what is proved, what the build is, which decisions are in force,
and which traps still bite.  It is not a specification — the declarations in `IETFree/` are the truth,
and `README.md` is the reader-facing account.  The latest independent review of the whole library is
`../results/review-IET2-v3.md`: ten Tau Ceti angles, each re-run from scratch by its own agent
against `.scratch/tauceti/TauCetiReview/rubrics/` and the `.skill/` files, and every finding
reproduced before acceptance.  Read it before a large change; `../results/review-IET2-v2.md` is the
previous audit and its §35 the closure index of that round, which v3 partly reopens (§4).

The full development log is [`HISTORY.md`](HISTORY.md): the 246 addenda of the `IET2` campaign
(with the table that maps every declaration name that no longer exists), then everything the
Masur–Veech campaigns left in prose — their records, and the rigidity campaign's blueprint, plan and
two dependency-graph documents, plus the Birkhoff campaign's two blueprints.  Cite it for *why*
something is the way it is.

## What is proved

`IETFree/ChallengeSolved.lean` proves `main`, the unconditional form of Theorem 1.1: for almost every
pair of length vectors, the two interval exchanges satisfy a nontrivial relation in the group of
permutations of `ℝ`.  No hypothesis on the number of cells, on the permutations, or on
irreducibility.

```lean
theorem main {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
      ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧
        evalWordEquiv w (mkIETEquiv p.1 π 0) (mkIETEquiv p.2 σ 0) = 1
```

It is assembled in three layers, each a theorem of the library:

* `ChallengeSolved.main` — Sections 2 and 3 of the paper: the a.e. block data plus the
  assembly of the per-block words, which *applies* the two a.e. theorems below (`masurVeech`,
  `veechRigidity`, both in `Pair/Irreducible.lean`).
  `masurVeech` is `UniqueErgodicity.MainTheorem.masurVeech_ae_unique_invariant` under the name of the
  notion (`UniqueErgodic`, the weak form of Definition 2.1); the strong form it implies
  (`UniformBirkhoff`, uniform convergence of the Birkhoff averages) is
  `UniqueErgodicity.uniformBirkhoff_of_uniqueErgodic` and is not a hypothesis anywhere.
* `veechRigidity` (`Pair/Irreducible.lean`) — Veech's rigidity for a.e. irreducible exchange, proved
  in `Rigidity/` and applied by the same assembly.

Both are stated in the library's vocabulary, for the exchange `mkIET1 λ π : IET 0 1` and the
group power — the `…Fun` predicates of the conditional challenge are gone (see below).

The remark after the main theorem is proved too (Addendum 233), with its machinery in
`Pair/RobustRelation/` **below** `ChallengeSolved.lean` and its two conclusions inside that file
(Addendum 234):

* `evalWord_eventually_eq_one` — a word trivial at a point `q₀` of the open region at which no
  nontrivial integer relation between the free lengths vanishes (`∀ N, q₀ ∈ goodParamsAt N d e`, the
  paper's `Ω'`) is trivial on a neighbourhood of `q₀`; the threshold form `4 * |w| + 4` is
  `evalWord_eventually_eq_one_of_goodParams`;
* `Pair.ae_hasRelation` — the a.e. statement of the main theorem, transported to the free parameters;
* `Pair.exists_isOpen_subset_hasRelation` — the parameters carrying a nontrivial trivial word contain
  an open set of full measure for
  `(volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))` (the interior of the
  relation set, which need not be open itself);
* `Pair.exists_isOpen_ae_exists_nontrivial_evalWordEquiv_eq_one` — the same on the paper's `Δ_π × Δ_σ`, as an open set of
  the ambient space whose trace on the product of the simplices carries the relation.

The last three are in `ChallengeSolved.lean`, next to `main`; the assembly that produces them from an
almost-sure input is `Pair.RobustRelation.exists_isOpen_subset_hasRelation_of_ae`, below.

## Status — measured, not remembered

- **The build is `lake build`.** 120 modules in `IETFree/`, plus the umbrella `IETFree.lean` and
  `Challenge.lean`; the last build was **9170 jobs, exit 0, no warnings, no errors** (on Lean
  4.35.0 / Mathlib `v4.35.0`, Addendum 233; `lake build IETFree` alone is 3342 of them).
  The directory is
  **not** wiped to re-check warnings (see `## Commands`): after an
  edit, `lake build` reports the warnings of the modules it recompiles, and a full sweep is
  `./SlowBuild.sh`.  It is incremental and parallel (no-op ≈ 6 s, ordinary edit
  seconds, deep module one to two minutes).  It works in this VM because
  `.lake/packages/mathlib/.lake/build` already holds Mathlib's oleans (root-owned), so Lake never writes
  into the package; a change of Mathlib revision needs `lake exe cache get` first.
- **`SlowBuild.sh` is not the build**: plain `lean`, one process per module, everything recompiled,
  several minutes.  It is the thorough check — `sorry` count, `--strict` on `sorryAx`-reachability from
  `main`, and the comparator gate `lake comparator`.  **Run it only when the owner asks.**
- **Axioms**: `#print axioms IntervalExchange.main` → `[propext, Classical.choice, Quot.sound]`.  The `sorryAx` count is
  4, all in `Challenge.lean` and deliberate (the definition hole `mkIETEquiv`, the statements
  `coe_mkIETEquiv`, `main` and the remark's conclusion
  `Pair.exists_isOpen_ae_exists_nontrivial_evalWordEquiv_eq_one`); the library has none.  `lakefile.toml` sets `warn.sorry = false`, so
  `lake build` says nothing about them — the axiom report is the guard.  Beside it,
  `warningAsError = true` makes every other warning a build failure.
- **The toolchain is Lean 4.35.0 with Mathlib `v4.35.0`** (Addendum 192).  `lean-toolchain`,
  `lakefile.toml` and `lake-manifest.json` all say so, and `.lake/packages/*` are checked out at the
  matching revisions.  The dependency build directories used to be **symlinks into `/opt`**, which
  broke the day the VM's toolchain moved: Lake had to rebuild the dependencies and could not write
  there.  They are now ordinary writable copies of the same oleans; a `lake update` that changes a
  dependency keeps working, and nothing writes into `/opt`.
- **Deprecations are swept, not tolerated** (Addendum 192): the migration off 4.33.1 produced 563
  deprecation warnings in six families (`if_pos`, `if_neg`, `dif_pos`, `dif_neg`, `if_true`,
  `if_false`), and each was renamed everywhere in one pass — 57 files — rather than at the sites
  where the compiler happened to complain.  `lake build` is warning-free again.
- **The comparator gate is `lake comparator`**, the tool in Lean core: it reads the root
  `comparator.json`, builds and exports `Challenge` and `IETFree.ChallengeSolved` inside its `bwrap`
  sandbox, compares them declaration by declaration and replays the solution into Lean's kernel.
  **Run on this tree on the owner's request and passing** (Addendum 242): exit 0 in about 80 s, with
  the three targets of `comparator.json` (`coe_mkIETEquiv`, `main`, and the remark's conclusion),
  printing `Lean default kernel accepts the solution` and `Your solution is okay!`.  It compares
  *bodies*, not only statements — see the auxiliary-declaration trap below.  **`enable_nanoda` is
  `false` in the config**: `bwrap` cannot bind `/opt/lean/bin/nanoda_bin` here because `/opt/lean` is
  a symlink, so a run with the key on ends with `nanoda exited with 1` although the kernel accepted;
  set it back to `true` where the sandbox can bind it.  The gate is not part of `lake build`; run it
  by hand, or `./SlowBuild.sh` runs it at the end.
- **Declaration linters** (Batteries' `runLinter`, which `lake build` does not run): 0 findings for
  `IETFree` (including the six `Pair/RobustRelation/` modules) and 0 for `Challenge`, 15 linters
  (`runLinter` does not print its declaration count, so none is quoted here — re-run it with `-v` to
  see the linter list).
- **Size** (re-measured for Addendum 242): 120 modules, 47 234 lines
  (counted over `IETFree/**/*.lean`, of which 240 are import lines; the umbrella `IETFree.lean`
  adds 195).  The remark's machinery is 2 857 lines in the six modules of `Pair/RobustRelation/`,
  plus 130 lines in `Pair/ProductSimplex.lean` and the three `Equiv`-valued declarations that moved
  into `Pair/MeasureTools.lean`.  The
  declaration counts are the Addendum-232 measurement and are not re-derived here: 4 599 project
  declarations, compiler-generated ones included, 3 841 of them reachable from `main` by the
  `getUsedConstants` walk (`env.const2ModIdx` filtered to the project's modules; the walk itself is
  the one described in the last paragraph of Addendum 160); of the 4 599, 3 220 are not `_private`
  auxiliaries, the rest being equation lemmas, `_private` auxiliaries, `match_`/`_proof_`
  auxiliaries and structure projections.  Under the module system the generated declarations are
  named `_private.<Module>.0.…`, so the total moves with them; the hand-written count is the stable
  one — and the remark's modules are above `main`, so they are outside that reachability walk by
  construction.
- **The surviving `change`s are documented**: `CHANGE-AUDIT.md` records, for every `change` in
  `IETFree/`, the error that deleting it produces — the reason it is there — at the line it occupies
  now.  Do not delete one without reading its row.  The table is regenerated by running the
  experiment again, not by editing line numbers (Addenda 185, 232 and 246).
- **Docstrings and links are checked, not eyeballed**: a module docstring describes its module, not
  a stage of a campaign, and every declaration it names in backticks exists (Addendum 169 dumps
  `constNames` and joins it with Mathlib's names to check); the README's repository links and its
  declaration anchors were audited against the tree in the same pass and re-anchored after every
  move (`anchors.py --check`: 0 lines changed, 168 anchors, Addendum 233).

## Layout

`IETFree/` — the single-exchange API, at the root in `IET.lean` (`IsIET`/`mkIETFun`/`mkIETEquiv`/
`mkIET1` (total in `λ`) and `mkIET1'` (on the simplex), the simplex and `simplexVolume`, `unitMeas`,
the type `IET a b` and its group) and in `CutSet/` (`Basic`: cut sets and cells, `Measure`: the
tiling and measure preservation), then the subdirectories below.  Every sibling group is a directory
(Addendum 216): `CutSet/`, `Pair/Block/`, `Pair/Singularity/`, `RauzyVeech/{Tower,Cylinder,Ray}/`,
`UniqueErgodicity/{Germ,Transfer}/`, `Pair/RobustRelation/`:

* `FreeGroup/` (2 modules) — the free-group theory the two-exchange development uses: root
  uniqueness and the centralizer of two elements, over an arbitrary alphabet, with no exchange in
  sight (`Commensurable`, `Centralizer`).
* `Pair/` (29 modules: 13 here, 9 in `Block/`, 2 in `Singularity/`, 5 in `RobustRelation/`) — two
  exchanges: the free-group development.  Section 2 (centralizer, Lemmas 2.7–2.10, Theorem 2.6,
  Proposition 2.5 `ae_diophantine`) and Section 3 (the length map, the good regions, the block
  rescalings, Lemmas 3.2–3.4, the assembly of the per-block words).
* `Pair/RobustRelation/` (6 modules) — the remark after the main theorem: the bad set at a threshold
  and its conull good set (`GoodParams`), the transfer between the free coordinates and the length
  vectors (`FreeParams`), the symbolic data of an arbitrary word (`WordData`) with the cuts and
  displacements of a single letter (`LetterData`) and the robustness theorem (`Robustness`), and the
  assembly of the open set of full measure from an almost-sure input, in the free coordinates and on
  `Δ_π × Δ_σ` (`OpenSet`).  Below `ChallengeSolved.lean`, which feeds them `main`.
* `Pair/ProductSimplex.lean` — the product of the two simplices: its free-coordinate chart
  (`prodSimplexMap`, `toReal`'s inversion almost everywhere), the pushforward identity for the product
  measure, and the `Equiv`-valued word evaluation of the challenge (`evalWordEquiv`,
  `evalWord_toEquiv`).  Below everything that transports an a.e. statement.
* `RauzyVeech/` (60 modules: 18 in `RichPath/`, 7 in `Tower/`, 3 in `Cylinder/`, 3 in `Ray/`) — the
  Rauzy–Veech induction and the richness of the greedy path, and the invariant-measure side the
  induction steps use: `InvariantMeasure`
  (Lebesgue's measure on `[0, 1)`, the cells and the length vector of a measure, and the step from
  the ray condition and length-map injectivity to `∃! μ`) and `MainComponents` (the notions
  `HasPositiveBlockAt`, `HasPositiveBlocks`, `RayCondition`).
* `Rigidity/` (10) — Veech's rigidity: `veechRigidity` itself is stated in `Pair/Irreducible.lean`.
* `UniqueErgodicity/` (12, 2 in `Germ/` and 2 in `Transfer/`) — unique ergodicity of an exchange: `MainTheorem` (the assembly of the
  a.e. theorem, which needs the proofs of its two inputs and therefore sits above `PosBlocks` and
  `RichPath`, and `masurVeech_ae_unique_invariant`), then the strong form: `UniqueErgodicity/Basic`
  holds the predicate `UniformBirkhoff`, and `IET` proves Theorem 2 (`UniqueErgodic → UniformBirkhoff`, for
  `mkIET1` and then for every exchange) together with Lemma 2.9 (`exists_uniform_birkhoff`).  This
  directory sits above `RauzyVeech/`; `InvariantMeasure` and `MainComponents`, which the induction
  steps themselves use, are inside `RauzyVeech/`.

At the root of `IETFree/` only the shared layers are left: `CutSet/` (two modules), `IET` (one
exchange, with the three notions `Invariant`, `UniqueErgodic` and `IsRigidByTranslations`),
`ListPeriodicity` (periodic words: the `List` lemmas behind root uniqueness in a free group, used by
`Pair/`), `TopBotFormalism`
(the two-bijection datum of the Marmi–Moussa–Yoccoz framework, below `Pair/`, `Rigidity/` and
`UniqueErgodicity/`) and `ChallengeSolved`.
`IETFree.lean` is the umbrella (its import list is generated by `lake exe mk_all --lib IETFree`);
`Challenge.lean`, one directory above, is the comparator challenge (`import Mathlib` only, imported
by nothing).

**The prune has been done, and this is what it left** (Addenda 222 and 232).  The walk over the
environment — `getUsedConstants` from `IntervalExchange.main` — reports **29** declarations that no
proof term names: five `@[ext]` lemmas (`BlockIdx.ext`, `Pair.IETDatum.ext`, `GoodRegion.Block.ext`,
`SingularityShape.ext`, `Rkz.Blk.ext`), the `CoeFun (IET a b)` instance, five projections of
`IsSmallRelation` — deleted with that structure, which had no other consumer (Addendum 232, C33), so
the list is now five shorter — seventeen
`@[simp]` or `:= rfl` lemmas (`IET.coeHom_apply`, `IETDatum₂.inv_*`, `ofPerm_piTop`,
`ofPerm_piBottom`, `vertex_nil`, `vertex_singleton`, `Pair.scalePerm_apply`, `scalePerm_symm_apply`,
`RichPath.levelWords_zero`, `lamAfter_nil`, `lvl_coe`, `push_coe`, `GoodRegion.subset_good`,
`IsCompPresentation.g_transl`, …), and one API bridge that nothing internal uses,
`colSumInt_cast` (the equation between the integer and real column sums, cited by `colSumInt`'s
docstring).  The first twenty-eight are
applied definitionally and leave no trace in the term; **deleting any of them breaks the build**, which
is why they stay.  `colSumInt_cast` is kept on purpose: it is what makes the two column sums one
notion for a reader, and a proof-free statement relating two public definitions is API, not dead code.  The 43 declarations that the walk found dead and the build let go of have been
deleted — the `germSection`/`germSectionVal` API of `UniqueErgodicity/MeasPrep.lean`, the
`kerckhoff`/`NoWin`/singleton refinement of `RichPath/HeightDichotomy.lean`, `mkIET1_of_notMem`,
`isClosed_simplex`, and the rest — together with `RichPath/BadFirstStop.lean`, whose only theorem went.
The library is 120 modules and, by the Addendum-232 measurement, 4 599 declarations.

## The names of the three merged notions (Addendum 232)

The v3 review found four notions carrying two names each.  Three of them are now one name, and the
merges are what a reader should use:

* **`totalLength`** (`IET.lean`, general in the alphabet) is the total length `Λ = ∑ λ`; it replaces
  the `Fin n`-only `tot` (`RauzyVeech/FirstReturn.lean`) and the general `Lam`
  (`RauzyVeech/MeshShrink.lean`), whose two copies of the same formula were unreachable from each
  other because the modules are siblings.
* **`mainLetter` / `secondLetter`** (`RauzyVeech/NameInfinite.lean`) are the main and secondary
  letters of a step; they replace the `List Bool`-based `mn`/`sc` of the same file and the
  `vertex`-based `nm`/`scd` of `RauzyVeech/MeshShrink.lean`, whose two defining equations are the
  same up to `vertexNat_eq_vertex_ofFn` (the bridges `nm_eq_mn`, `scd_eq_sc` are gone, and
  `MeshShrink` converts through `mainLetter_eq_last`, `secondLetter_eq_last` where it works with
  its own vertex `V`).
* **`colSum` / `colSumInt`** (`colSum` in `RauzyVeech/ColDiam.lean`, `colSumInt` in
  `RauzyVeech/MeshShrink.lean`, where the path matrix `Qm` lives) replace the case-only pair
  `cs`/`Cs`.  This one keeps **two** declarations and that is deliberate: the same column sum is an
  integer count (`1 ≤ colSumInt`, used in the integrality step of the mesh argument) and a real
  number (in the cone and product expressions), and forcing one codomain would put `Int.toNat` or a
  floor in the middle of the growth argument.  What was missing is the relation, and it is now
  `colSumInt_cast : (colSumInt P p k b : ℝ) = colSum P (pfx p k) b`.

## No declaration carries a hypothesis its proof does not use (Addendum 232)

The v3 review's meta-program over proof terms found twenty hypotheses that no proof ever names —
invisible to `linter.unusedVariables` because every one of them was `_`-named.  They are gone, and so
are nine more that the removal made dead in the same proofs' callers, plus two the review's scan had
missed (`image_truncation_subset`): 31 binders in 26 declarations, including the parameter of
`removeFun`.  What that changed for callers:

* `totalLength_pos`, `exists_uniform_minimal_exit`, `tower_formula_level_pathQ_any`,
  `exists_stopfam_of_good`, `sign_congr_on_ball`, `iterate_word`, `defect_identity_meas`,
  `map_map_eq_self`, `lt_iff_lt_of_ne_on_ball`, `card_filter_gt`, `descent_subclaim`,
  `defect_identity_meas`, `exists_markedList`, `removeFun` — the hypothesis is gone from the
  statement, so every call passes one argument fewer (the statements are **stronger**, and no proof
  had to change);
* `mkIETFun_mem_cut_of_ne`, `mkIETFun_mem_Ico_cut_totalLength`, `filter_eT_lt_of_le`,
  `filter_eT_lt_of_gt`, `leftEnd_lamT_of_le`, `upperEnd_lamT_of_lt`,
  `translationVector_piHatT_of_lt`, `translationVector_piHatT_top`, `cellHatT_of_lt`,
  `cellHatL_of_lt` — the `hlt : lam botCell < lam (topCell π)` was only ever forwarded to the
  previous lemma; it is gone from all ten, and where a statement still needs it (`leftEnd_lamT_of_gt`,
  `cellHatT_top`, `cellHatT_succ`, `cellHatT_of_gt`, …) it stays;
* `translationVector_lamHat_of_ne` covers the `botCell` case too, so `translationVector_lamHat_botCell`
  and the case split that used it are deleted.

The rule for the next round: a hypothesis the proof does not use is not "kept for uniformity" — it
is deleted, and if the deletion makes a caller's hypothesis dead, that one goes in the same commit.

## The datum-less declarations do not live under `IETDatum₂` (Addendum 232)

Sixteen declarations whose statements mention no `IETDatum₂` were moved from
`IntervalExchange.IETDatum₂` up one level, to `IntervalExchange`: the matrix action `qMat`, `qApply`
and their lemmas (`qApply_apply`, `qApply_eq`, `qApply_mul`), the cone `cone` with `cone_eq`,
`cone_mul`, `sum_add_single_mul`, `volume_linear_eq_zero`, `det_one_add_single_of_ne`,
`colsum_one`, the counting lemmas `card_filter_lt`/`le`/`gt`, and `mem_cone_one_iff`.  The move is
free for readers of the code: Lean resolves a short name in the parent namespace, so every
unqualified use still elaborates, and only the qualified `IETDatum₂.qApply`-style spellings had to be
shortened (13 files).  What stays under `IETDatum₂` is what takes a datum — `qApply_rvMat`,
`cone_rvMat`, `cone_Q_append`, … — so the namespace now describes its members.

Still under `IETDatum₂` and datum-less: `fin_add_one_val` (inside `section Step`) and the
`hallLin`/`glin`/`delta` family of `Nesting.lean` (inside `section Null`/`NullVolume`, interleaved
with the datum-carrying `Acoef`), so moving them means cutting the declarations out of their
sections; and `pairReach`, `pairReach_all`, `exists_uniform_bound'`, whose names refer to the diagram
of a datum although their statements no longer mention one.

## The `deltaOf` API is public (Addendum 232)

`deltaOf ε M` is the precision the rigid step runs at (`Rigidity/Defs.lean`).  Its five bounds used to
be `private` in `Rigidity/RigidStep.lean`, which made `exists_rigid_set` — whose hypotheses are
exactly `0 < δ` and `δ ≤ 1/4` — impossible to instantiate from outside the namespace:
`IntervalExchange.Rigidity.deltaOf_le_quarter`, `deltaOf_le_div`, `deltaOf_mul_le`,
`deltaOf_mul_succ_le` and `deltaOf_mul_add_three_le` are now public, and
`deltaOf_pos_and_le_quarter` bundles the two facts a caller needs.  The rigid step's own call of
`exists_rigid_set` goes through the bundle.

The other half of §3.8 — an `EquivLike (IET a b) ℝ ℝ` instance — is **not** done: see the review's
record.  `IET a b` is a group whose `Inv` is the group inverse, and `EquivLike` brings its own
function-level inverse, so `f⁻¹ (f x)` becomes ambiguous between the two; the instance also changes
what `⇑f` elaborates through, and the structure's `isIET` field needs the injectivity proof
restructured.  It is a change to the `IET` API, not a local addition.

## Decisions in force — do not undo

- **`@[expose]` stays on every module** (owner's decision, after the audit's §5 A1 proposed narrowing
  it file by file).  The exposure is blanket on purpose: it keeps every definition as transparent to
  its clients as before, and narrowing it is not wanted.  Do not remove it, and do not ask for
  unfolding lemmas in place of it.
- **Every import line must be necessary** (owner's instruction; Addendum 224).  No module under
  `IETFree/` imports `Mathlib` as a whole, and a line that another import already supplies is a
  defect, not documentation: the criterion is that **deleting the line breaks the build**.  The
  greedy fixpoint of that test was computed in Addendum 224, on the 116 modules then present (224
  lines, at most 7 in one file, 51 modules with a single one); every line there was verified by
  removing it and rebuilding its module (`.scratch/tmp/verify_necessity.py`).  The renames, the
  splits and the remark's modules changed the figures — the tree now has **240 import lines over
  120 modules, at most 8 in one file** — and the fixpoint has **not** been recomputed on the final
  tree.  The cost is stated and accepted: a
  header names the one or two modules that *carry* what the file uses (`LevyRecurrence` imports
  `Mathlib.Probability.Martingale.Convergence` and nothing else), so it no longer lists every
  module the file touches.  To add an import, add it and then check it: delete it again, and if
  the module still builds it does not belong.  `Challenge.lean` is the one exception and stays
  `import Mathlib` only; the umbrella `IETFree.lean` keeps all 120 project imports because its job
  is coverage — a line there is not supposed to be necessary.
- `#min_imports` and `lake shake` answer **relative to the list a file already has**, so neither
  can decide this question on its own, and re-running either now reports almost everything as
  unneeded.  `lake shake` is not to be run at all: it wrote the same ~40 irrelevant Mathlib leaves
  into every file and deleted project imports the tree needs (Addendum 223).  The tools that do
  decide it are `lake build` on one module, once per candidate deletion.
- **`mkIETFun`'s formula is not a `simp` lemma** (owner's ruling, Addendum 231).
  `mkIETFun_of_mem` and `mkIETFun_of_notMem` are deliberately unannotated: the formula is an
  implementation detail and must not be unfolded by default, so every use names the lemma it wants
  (`rw [mkIETFun_of_mem lam π a hx]`), and a new `@[simp]` lemma about `mkIETFun` is not wanted.
  One consequence worth knowing: `simp` treats `mkIETFun lam π a x` as an atom everywhere.
- **`mmin` is `sInf` of the image** (Addendum 230): `mmin s q = sInf (q '' s)`, Mathlib's total
  infimum, whose junk value on the empty set is `ℝ`'s own `sInf ∅ = 0` (`Real.sInf_empty`).  It is
  total because the *statements* need it — `GradedStepMin` writes `min (mmin A' …)` in the same
  proposition that introduces `A'` with only `A'.card = k`, so no `Nonempty` proof is in reach — and
  `mmin_eq` gives `Finset.inf'` on a nonempty set.  Do not replace it by `Finset.inf'` (that would
  change that statement) and do not reintroduce a `dite` with an invented junk value.
- `IsIrreduciblePerm π` is the paper's condition: `∀ k, (∀ i, i ≤ k → π i ≤ k) → ∀ i, i ≤ k`
  (`IET.lean`).  `masurVeech` carries `2 ≤ d` (necessary: on one cell the exchange is the identity,
  which is not uniquely ergodic); `veechRigidity` does not need it.
- Do not turn these **`abbrev`s into `def`s** — a `def` is not unfolded during `rw`: `BlockIdx.kFin`
  (it must be seen as `⟨I.k, _⟩` when rewriting), `blockLam_coe` (rewritten by `rw [blockLam_coe]` in
  `BlockDatum` and `BlockLemma`), and `Positive` (the hypothesis of the whole block development).
- Everything is **pointwise**: a good region gives strict monotonicity of its singularity list only on
  its open set, so the length vector of a composition at a point is `G.cellLen hq`
  (=`compLenVec G.s q (monoAt G hq)`); there is no global `hmono` and no `compLenVecOf`.
- The repeated tuples are **structures**: `BlockIdx n` (with `hkl`, `hln`, and the derived instance
  `NeZero (I.l - I.k)`), `GoodRegion.Block`, `GoodRegion.Fits`; a point of a good region is read with
  `G.pres q hq` / `G.type q hq`.
- `unitMeas` is defined once, in `IET.lean`.  **`UniqueErgodic` is the weak form of Definition 2.1**
  and lives in `IET.lean` with `Invariant` (owner's instruction, 4 Nov; Addendum 161): exactly one
  invariant probability measure carried by `[0, 1)`, no convergence.  The strong form is the
  predicate `UniformBirkhoff` in `UniqueErgodicity/Basic.lean`, which is *proved* from it
  (`UniqueErgodicity.uniformBirkhoff_of_uniqueErgodic`) and assumed nowhere.
  `IsRigidByTranslations` (Definition 2.2) is in `IET.lean` as well, next to them.  All three are
  stated for the bundled
  exchange `mkIET1 lam π` and iterated with the group power.  The four `…Fun` predicates that
  `ChallengeWeak.lean` needed (the same conditions on a bare map `ℝ → ℝ`, iterated with `f^[n]`)
  **are gone** (owner's
  instruction, 3 Nov): the theorems are now proved in the library's own form
  (`Rigidity.veechRigidity`), and the two notions are related to `f^[n]` only where a proof needs
  it (`UniformBirkhoff` is stated with the iterate `f^[n]`).
- **A proved statement is never a hypothesis** (owner's instruction, 3 Nov; Addenda 155–160).  Where a
  `Prop`-valued definition named something the library then *proved*, the definition is gone and the
  formula is written out at the theorems that use it: `UniqueErgodicFun`,
  `IsRigidByTranslationsFun`, `MasurVeechFun`, `VeechRigidityFun`, `UniformPositivity`,
  `RichGreedyPath`, `PositiveBlocksRay`, `MasurVeech`, `VeechRigidity`, `StraddleMass`,
  `StraddleMassCard`, and `GradedFull` (both copies).  What remains as `Prop` definitions are the
  *notions* the statements are about (`UniqueErgodic`, `IsRigidByTranslations`, `HasPositiveBlocks`,
  `RayCondition`, `GoodAt`) and the states of the inductions that really run (`Graded`,
  `InductionStep`, `GradedStep`, `GradedStepMin`, `BalanceStep`).
- **Binders are left of the colon** in 630 `have`s; the six that still read `have h : ∀ …` cannot be
  converted, each for a recorded reason (three need a `by omega` term inside a `Fin` cast that the
  kernel rejects once the binder moves, one inducts before introducing its hypotheses, one binds its
  own `F` inside the statement, one refines a theorem that *is* the `∀`).  Addendum 191 lists them.
  A `have h : P → Q` with no `∀` was checked for and **there is none** — the fifteen candidates all
  put the arrow inside a `fun`, `∫⁻` or `∃` binder type — and no theorem or lemma states its
  hypotheses as an arrow either; the 75 declarations that do have a top-level arrow are 73 `def`s
  and 2 `abbrev`s *of functions*, which are left alone (Addendum 191).
- **`have h := <short term>` is gone where it only renamed** (Addendum 190): the 19 that remain in
  `IETFree/` all need the *name* — `omega` and `linarith` read the context, `rw … at h` needs a
  hypothesis rather than a projection, or the statement is a definitional restatement no tactic
  reproduces.  Do not delete one without re-reading its reason in Addendum 190.
- **No theorem carries a hypothesis its proof does not use** (Addendum 211): the three that did —
  `peel`, `peel_of_contract`, `Rigidity.Internal.rigid_step`, each taking an
  unused `hstop` and silencing the linter with `have _hstop := hstop` — have lost the hypothesis and
  the silencing line, and their three call sites are updated.  If you ever need to keep a hypothesis
  a proof cannot use, say why in the docstring instead of reaching for `have _h := h`; the linter is
  right.
- **Every file is a module** (Addendum 172): `module` after the copyright block, `public import`
  everywhere, and the file's API in a `@[expose] public section` closed by a final `end`.  The
  exposure is blanket on purpose — it keeps every definition as transparent to its clients as
  before — and narrowing it to the definitions that really must unfold is a separate pass.
  **Trap:** an *auxiliary* declaration in a proof term is named `_private.<Module>.0.<name>`, so a
  declaration copied verbatim into `Challenge.lean` whose proof mentions one elaborates to a
  different term than the library's, and the comparator reports
  `Const does not match between challenge and target '<name>'` (it compares the exported
  `ConstantInfo`, body included, for every constant the targets reach; a statement mismatch has its
  own message, `Challenge and solution theorem statement do not match`).  It is the auxiliary that
  is fatal, not the tactic style: `simp` and `omega` generate them (Addenda 172 and 174),
  `refine`/`exact` do not.  Hence `idxSet_nonempty`'s tactic proof avoids `simp` and
  `simplexMap_val_lt` avoids `omega`, and neither `simplexMap` nor `idx` has a `by` in its body.
  **The same holds for the body of a copied `def`**, and the easiest way in is an instance: an
  `if i = 0 then f else g` pulls in a `DecidableEq (Fin 2)` whose proof is an auxiliary, so the two
  copies differ although their source text agrees (Addendum 242).  A copied definition must not let
  a typeclass choose anything — write the case split with `Fin.cases`, as `evalWordEquiv` does.
- `Challenge.lean`'s declarations are **verbatim copies of the library's** wherever `main`,
  `coe_mkIETEquiv` or `mkIETEquiv` reaches them — a shorter equivalent body is a different
  `ConstantInfo`.  In particular the body of `idx` must stay identical in the two files: `idx` is
  reachable, so its proof term is compared.
- The **definition hole** in `Challenge.lean` is `mkIETEquiv` because the proof that it is a
  bijection is not completely trivial, and the challenge file is meant to stay short and easy to
  read (owner's ruling, Addendum 170).  The `private` core of `IETFree/IET.lean` makes a *verbatim copy* of
  the body impossible; that is a fact about the comparator, not the reason for the hole.
- In the correspondence table and in `formalization.yaml` a **definition is `implemented`, not
  `proved`**; `proved` is for theorems and lemmas.
- **Nothing is frozen any more.**  `Challenge.lean` is a challenge, not a frozen interface; the FROZEN
  paragraphs and the `FROZEN_ANCHOR_*` markers are gone.
- **The pre-merge project is gone** (owner's instruction, 2 Nov): the separate Lake project the two
  Masur–Veech campaigns were carried out in has been deleted, together with its blueprints, ABI,
  `frozen-anchors.json` and tools.  Its Lean content is `IETFree/`; its prose is reproduced in
  `HISTORY.md` Part II.  Nothing is lost that the deliverable needs, and nothing was frozen anyway.
- **`.scratch/` is emptied** (owner's instruction, 2 Nov): the caches, the comparator clone, the
  experiment copies and the build logs are gone, and freed ~3 GB.  What the ledger cites under
  `.scratch/…` therefore no longer exists; the inventory of what was there is kept in
  `.scratch/keep/scratch-evidence.list`.  Nothing of the *library* was lost with it: the outcome of
  every experiment is recorded in `HISTORY.md`, which is now the only copy of the campaigns' prose
  (the pre-merge project it was copied from was deleted the same day).
- **Packaging (owner's standing instruction)**: `IET2.zip` is sources only —
  `zip -r -q IET2.zip IET2 -x 'IET2/.lake/*' 'IET2/.scratch/*' '*.olean' '*.ilean'` from the
  repository root, then `unzip -tq` and a `diff -r` round trip against the tree.
- The repository is <https://github.com/sgouezel/IETFree> (`main`) and holds the contents of `IET2/` at
  its root, so module paths there are `IETFree/…`, not `IET2/IETFree/…`.

## Commands

```sh
lake build                                    # the build (incremental, parallel)
lake comparator                               # the gate, ~80 s; reads comparator.json
lake env lean --run .lake/packages/batteries/scripts/runLinter.lean --no-build IETFree   # ~10 s
lake env lean --run .lake/packages/batteries/scripts/runLinter.lean --no-build Challenge
./SlowBuild.sh --strict                       # the slow thorough check — only on request
```

**`.lake/build` is never deleted** (owner's instruction, 3 Nov): wiping it costs minutes and buys
little.  A claim of zero warnings therefore rests on warnings emitted while recompiling, and the way
to get a full warning sweep is `./SlowBuild.sh` — plain `lean`, every module, per-module logs in
`.scratch/tmp` — not `rm -rf .lake/build`.  Delete the directory only on an explicit request.

## The namespaces: `IntervalExchange`, and nothing at the root but Mathlib lemmas

Every library declaration — and the fifteen of `Challenge.lean` — is in `IntervalExchange`,
`IntervalExchange.Pair`, `IntervalExchange.RauzyVeech` (with `IntervalExchange.RauzyVeech.RichPath`),
`IntervalExchange.Rigidity` or `IntervalExchange.UniqueErgodicity`; the namespace follows the
**directory**, never the file name (Addenda 218–219).  There is **one namespace per directory**: the
43 per-file namespaces of the earlier tree (`Potential`, `Stopping`, `NodeHeight`, `CylinderMass`,
`TowerInjectivity`, `BlockData`, …) are dissolved, and their declarations sit directly in their
directory's namespace.  **No project declaration is at the root any more** (it holds only
`FreeGroup.*`, `List.*`, `Equiv.IsIET` and `AffineMap.sum_apply`): the type is
`IntervalExchange.IET`, and the challenge's own names are `IntervalExchange.main`,
`IntervalExchange.simplexVolume`, …, which is what `comparator.json` now lists.

Sub-namespaces remain only where a **declaration** gives them one, so that dot notation works:
`IntervalExchange.IET`, `IntervalExchange.IETDatum₂`, `IntervalExchange.IsCutSet`,
`IntervalExchange.BlockIdx`, `IntervalExchange.Pair.GoodRegion`,
`IntervalExchange.UniqueErgodicity.SplitI`, and the ~200
projections, instances and `rfl` lemmas Lean itself puts in the namespace of the object they are
about.  Four subject sub-namespaces have no declaration of their own and are kept anyway:
`IntervalExchange.IETDatum₂.Path` (the path matrices `Q`, `Qinv` and the heights),
`IntervalExchange.RauzyVeech.TowerStep` (the per-step data of the tower),
`IntervalExchange.RauzyVeech.RichPath` (the subject of its directory) and
`IntervalExchange.Rigidity.Internal` (a marker for two implementation lemmas); their declarations
are named (`Path.Q`, `TowerStep.VV`), which dot notation does not reach.  In the Mathlib
namespaces the library extends: `FreeGroup.*` (34) and `List.*` (21) — lemmas about free groups and
lists, not about exchanges — `Equiv.IsIET`, and `AffineMap.sum_apply`.

`IntervalExchange.IET.id` is gone: a `def id (a b : ℝ) : IET a b` shadows `_root_.id` for every
module below `IntervalExchange`.  The identity of the group is the `One` instance.

## The node-indexed tower theory is `RauzyVeech/Tower/Node.lean`

`RigidSet` used to re-prove, node by node, what the tower theory proves along an infinite sequence.
That development now lives in `RauzyVeech/Tower/Node.lean`, whose statements are the stronger ones:
they assume `IterOK P lam (γ ++ [e])` for one step, where the sequence statements need
`∀ k, IterOK P lam (γ k)` along a tower that continues forever, so the node form cannot be derived
from the sequence form.  `cover_step_false`/`cover_step_true` of `Node.lean` are the node form;
`cover_step_false_of_tower`/`cover_step_true_of_tower` of `Tower/Tiling.lean` are the five-line
derivations along a tower sequence.  Everything is in `IET.RauzyVeech`, so nothing has to be
`open`ed.

## The alphabet facts are `IETDatum₂.card_eq_n` and `IETDatum₂.card_pos`

Everything known about the size of the alphabet is in `TopBotFormalism.lean`, in `namespace
IET.IETDatum₂`: `card_eq_n` (`Fintype.card α = n`, from `P.piTop`) and `card_pos` (`1 ≤ Fintype.card α`,
from `card_eq_n` and `[NeZero n]`).  Dot notation is enough — `P.card_pos` — and `0 < Fintype.card α`
is the same proposition definitionally, so no strict-form variant is needed.  The `ℝ`-valued and
`2 ≤` forms (`one_le_card_cast`, `card_ge_two`) are different statements and stay;
`nonempty_alpha` is gone (Addendum 217) — its two uses write
`Fintype.card_pos_iff.mp P.card_pos`.  `RauzyVeech/MeshShrink.lean` cannot see
`RichPath/NodeHeight.lean`; that is how a second copy of `card_pos` grew there, and why the statement
belongs in `IETDatum₂` rather than in a `RichPath` module.

## Traps that still bite

- `warn.sorry = false` in `lakefile.toml`: a `sorry` is invisible in `lake build`'s output and the olean
  is still written.  Read the `#print axioms IntervalExchange.main` line, or run `SlowBuild.sh`.  `warningAsError = true`
  sits beside it: every other warning fails the build, a `sorry` does not.
- Stale in-tree `.olean` files (left by `SlowBuild.sh`) shadow moved or deleted modules; delete them
  before believing an error about a module that "still exists".
- `lake env lean <file>` does **not** apply the lakefile's `[leanOptions]`; pass
  `-DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3` for a single-file check,
  and `-DwarningAsError=true` if it should fail on a warning instead of printing it.
- Warnings are printed only for modules that actually recompile.
- One build at a time on the four cores.  `lake build` may run while editing (it re-checks hashes);
  `SlowBuild.sh` may **not** — its module list is a snapshot of `IETFree.lean`'s imports from start-up.
- Bulk text edits: a slice "between two declaration names" can swallow everything in between; two
  consecutive `/-- … -/` docstrings are a parse error; an `omit […] in` line directly above a
  declaration belongs to it and must go with it.  After any scripted pass, recompile and diff against a
  backup.
- `rw` under `Fin`-dependent terms fails — restructure with `obtain ⟨a, b, c⟩ := D` and `rfl`.  `omega`
  treats the `Fin` constructor as opaque: hoist index bounds into standalone lemmas, and read a false
  `ω` goal as a missing bound.  `∑ x in s, f x` does not parse; write `∑ x ∈ s, f x`.
  `IETDatum.toIET` is a plain `def`, so `rw [IETDatum.toIET]` fails — use `show`/`rfl`; and
  `IET.apply_symm_apply'` matches the `⁻¹` form of the inverse law, not the `toEquiv.symm` one.
