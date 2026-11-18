# Working notes: what is true about this tree now

This file is the **current** record: what is proved, what the build is, which decisions are in force,
and which traps still bite.  It is not a specification — the declarations in `IETFree/` are the truth,
and `README.md` is the reader-facing account.  The latest independent review of the whole library is
`../results/review-IET2-v3.md`: ten Tau Ceti angles, each re-run from scratch by its own agent
against `.scratch/tauceti/TauCetiReview/rubrics/` and the `.skill/` files, and every finding
reproduced before acceptance.  Read it before a large change; `../results/review-IET2-v2.md` is the
previous audit and its §35 the closure index of that round, which v3 partly reopens (§4).

The full development log is [`HISTORY.md`](HISTORY.md): the 248 addenda of the `IET2` campaign
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
`Pair/RobustRelation/` **below** `ChallengeSolved.lean` and its conclusion inside that file
(Addendum 234):

* `evalWord_eventually_eq_one` — a word trivial at a point `q₀` of the open region at which no
  nontrivial integer relation between the free lengths vanishes (`∀ N, q₀ ∈ goodParamsAt N d e`, the
  paper's `Ω'`) is trivial on a neighbourhood of `q₀`; the threshold form `4 * |w| + 4` is
  `evalWord_eventually_eq_one_of_goodParams`;
* `Pair.exists_isOpen_ae_exists_nontrivial_evalWordEquiv_eq_one` — the remark on the paper's
  `Δ_π × Δ_σ`: an open set of the ambient space, of null complement for
  `simplexVolume d × simplexVolume e`, whose points of total mass `1` carry a nontrivial trivial
  word (Addendum 247 states it directly from `main`; the a.e. step and the free-coordinate form are
  *not* statements of their own — they are the proof of that theorem, on top of
  `Pair.RobustRelation.exists_isOpen_subset_hasRelation_of_ae`, below).

## Status — measured, not remembered

- **The build is `lake build`.** 122 modules in `IETFree/`, plus the umbrella `IETFree.lean` and
  `Challenge.lean`; the last build was **9172 jobs, exit 0, no warnings, no errors** (on Lean
  4.35.0 / Mathlib `v4.35.0`, Addendum 252; `lake build IETFree` alone is 3347 of them).
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
- **The bodies of the fifteen declarations `Challenge.lean` states are an interface.**  The
  comparator compares a declaration it finds in both modules *whole* — a `def`'s body included — and
  the walk reaches them through `main`, `mkIETEquiv` and the remark's conclusion.  So no reuse or
  cleanup finding may change them: `simplexRegion`'s body is the literal
  `{v | (∀ i, 0 < v i) ∧ ∑ i, v i < 1}` even though `RauzyVeech.region (d - 1)` is the same set
  (`simplexRegion_eq_region` states the identity), because that is what `Challenge.lean` says
  (Addendum 248).  Anything else the challenge states — `leftEnd`, `idxSet`, `mkIETFun`, `simplexMap`,
  `simplexVolume`, `evalWordEquiv`, … — is frozen the same way.
- **Declaration linters** (Batteries' `runLinter`, which `lake build` does not run): 0 findings for
  `IETFree` (including the six `Pair/RobustRelation/` modules) and 0 for `Challenge`, 15 linters
  (`runLinter` does not print its declaration count, so none is quoted here — re-run it with `-v` to
  see the linter list).
- **Size** (re-measured for Addendum 253): 122 modules, 47 086 lines
  (counted over `IETFree/**/*.lean`, of which 262 are import lines; the umbrella `IETFree.lean`
  adds 207).  The remark's machinery is 2 661 lines in the six modules of `Pair/RobustRelation/`,
  plus 130 lines in `Pair/ProductSimplex.lean` and the three `Equiv`-valued declarations that moved
  into `Pair/MeasureTools.lean`.  The
  declaration counts are the measurement of `## The prune has been done` above (4 778 project
  declarations, compiler-generated ones included, 2 444 reached from the two roots by the
  `getUsedConstants` walk (`env.const2ModIdx` filtered to the project's modules; the walk itself is
  the one described in the last paragraph of Addendum 160).  The 4 778 includes Lean's generated
  companions — equation lemmas, `_private` auxiliaries, `match_`/`_proof_` helpers, structure
  projections — which is why the walk prints the count with and without `isInternalDetail`: that
  split moves with the toolchain and the module naming, so the hand-written counts are the stable
  ones, and the total is quoted only beside them.
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
* `Pair/` (30 modules: 13 here, 9 in `Block/`, 2 in `Singularity/`, 6 in `RobustRelation/`) — two
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

`IETFree/ForMathlib/` (two modules) holds the ten facts about `List`, sets, measures and affine maps
that Mathlib does not have, stated at the generality that makes them proposable upstream (Addendum
250); it imports Mathlib only, so any module can use it.

At the root of `IETFree/` only the shared layers are left: `CutSet/` (two modules), `IET` (one
exchange, with the three notions `Invariant`, `UniqueErgodic` and `IsRigidByTranslations`),
`ListPeriodicity` (periodic words: the `List` lemmas behind root uniqueness in a free group, used by
`Pair/`), `TopBotFormalism`
(the two-bijection datum of the Marmi–Moussa–Yoccoz framework, below `Pair/`, `Rigidity/` and
`UniqueErgodicity/`) and `ChallengeSolved`.
`IETFree.lean` is the umbrella (its import list is generated by `lake exe mk_all --lib IETFree`);
`Challenge.lean`, one directory above, is the comparator challenge (`import Mathlib` only, imported
by nothing).

**The prune has been done, and this is what it left** (Addenda 222, 232, 249, 251, 252 and 253).  The
walk over the environment — `getUsedConstants` from the two roots `IntervalExchange.main` and the
remark's conclusion `Pair.exists_isOpen_ae_exists_nontrivial_evalWordEquiv_eq_one` — is
`.scratch/review/Reach.lean`, and it re-measures, in one run:

| quantity | value |
|---|---|
| declarations in the project's modules, compiler-generated included | **4 778** |
| the same, `isInternalDetail` companions dropped | **2 679** |
| of those, reached by a term or a type from the two roots | 2 444 |
| not reached | **235** |
| not reached, once the `congr_simp`/`ext`/`casesOn`/`rec`/`eq_def` companions are dropped | **25** |

`Reach.lean` writes both lists (`.scratch/review/unreachable.tsv`, and `unreachable-hand.tsv` for
the 25) so the next session need not re-derive them.  The 235 split into two kinds:

* **applied definitionally** — the `@[ext]` lemmas, the `CoeFun (IET a b)` instance, the `@[simp]`
  and `:= rfl` lemmas (`IET.coeHom_apply`, `IETDatum₂.inv_*`, `Pair.scalePerm_apply`,
  `RichPath.levelWords_zero`, `lamAfter_nil`, `lvl_coe`, `push_coe`, …) and the `local instance`
  `DecidablePred` of `RichPath/`.  They leave no trace in any proof term while a live proof or the
  simplifier still needs them, so **deleting one breaks the build**; that is why they stay.
* **unreferenced API** — declarations nothing mentions at all.  The lesson: absence from the walk is
  not evidence of a definitional use, and the two are told apart by deleting the declaration and
  rebuilding, not by grepping.

**The 25 hand-written unreachable declarations, and what each is** (Addendum 252 decides them all in
favour of keeping, and says why; nothing here is silently dead):

* *interface, not dead* — `IET.instCoeFunForallReal` (the coercion instance),
  `IETDatum₂.ofPerm_piTop` (`@[simp]`, used by the simplifier), `Pair.GoodRegion.subset_good` and
  `Pair.IsCompPresentation.g_transl` (structure fields), `RichPath.{badDecidable, goodDecidable,
  stopEvDecidable}` (`local instance DecidablePred`).
* *deliberate API, quoted by the documents* — `RauzyVeech.colSumInt_cast` (the bridge that makes the
  two column sums one notion), `Pair.forall_goodParams_iff` (the identification of the paper's `Ω'`,
  quoted by the README and by `formalization.yaml`), `Pair.simplexVolume_ne_zero` (quoted by `main`'s
  docstring as the non-vacuity witness), `Pair.evalWord_eventually_eq_one_of_goodParams` (the
  numerical-threshold form of the remark, quoted by both documents).
* *the paper's `N = 4` notation, at `Pair/ReductionData.lean`* — `smallCoeffs`, `mem_smallCoeffs`,
  `isClosed_badParam`: the `N = 4` case of `smallCoeffsAt`/`isClosed_badParamAt`, which is where all
  three statements are proved.  The proofs run at `N`; the `N = 4` forms are what the paper states.
* *the threshold `2 n`, and the two lemmas under it* — the chain is
  `Pair.evalWord_eventually_eq_one_of_goodParams` → `Pair.vanishesAt_of_goodParams` →
  `IsFreeLat.eq_zero_of_vanishes`, and `Pair/GoodParams.lean`'s §4
  (`relation_of_good_at`, `relation_of_good_simplexMap_at`, `comb_simplexMap_eq_zero_of_good_at`).
  The statement of record is at `Ω'`; these are the machine-checked content of the `2 n` threshold
  the paper's Remark 1.2 raises, kept as a statement rather than consumed by a proof (§4's
  docstrings and the module docstring say so).
* *the paper's Remark 1.2, `Pair/GoodParams.lean` §2–§3* — `volume_eq_zero_intLinear_eq`,
  `volume_eq_zero_relReal`, `compl_iUnion_goodParamsAt_subset`, `volume_iUnion_relReal_eq_zero`,
  `volume_compl_iUnion_goodParamsAt`, `measure_compl_iUnion_goodParamsAt`: "countably many affine
  hyperplanes are null".  The tree's a.e. statement goes through the Diophantine tube estimates
  instead (`ae_goodParamsAt_all_large`, which *is* on the path); these are the paper's own argument.

What had accumulated without being used by anything and *was* deleted (Addenda 249, 251):
`Pair.exists_isOpen_subset_hasRelation_of_ae`, `Pair.hasRelation_iff_mkIET1'`, `ae_goodParamsAt_all`,
`mkIET1_of_notMem`, `IETDatum₂.toIET_of_notMem`, `isClosed_simplex`, and, before them, the 43
declarations of Addendum 232 — the `germSection`/`germSectionVal` API of
`UniqueErgodicity/MeasPrep.lean`, the `kerckhoff`/`NoWin`/singleton refinement of
`RichPath/HeightDichotomy.lean`, and `RichPath/BadFirstStop.lean`, whose only theorem went.
The library is 122 modules; the declaration count is the table above (the Addendum-232 figure of
4 599 counted a different filter and is superseded).

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
`cone_mul`, `sum_add_single_mul`, and `mem_cone_one_iff`.  Addendum 249 went one step further for
those whose first explicit argument is a Mathlib object: `Matrix.sum_one_apply`,
`Matrix.det_one_add_single_of_ne`, `MeasureTheory.volume_linear_eq_zero` and the counting lemmas
`IntervalExchange.card_filter_val_lt`/`_le`/`_gt` now sit in that object's namespace.  The move is
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

- **`@[simp]` is for a specific case, never for unfolding a definition** (owner's ruling, Addendum
  254).  A `rfl` lemma whose right-hand side is the definition's body does not get the attribute —
  "if we always wanted to unfold the definition we wouldn't have made the definition to start with".
  It stays when the left-hand side already commits: a constructor or literal argument (`[]`, `e :: es`,
  `k + 1`, `true`, `Sum.inl i`, `i.castSucc`), a projection (`.val`, `.inv`, `.piTop`), a specific
  datum (`ofPerm π`, `lebesgue`), or an instance field computed at a point (`IET.mul_apply`,
  `IET.one_apply` — the only way `simp` computes those).  Fifteen attributes were removed and
  thirty-six kept; the two lists are in Addendum 254.  Do not re-annotate a `*_def`/`*_apply` lemma
  because it is a `rfl` normal form.
- **`@[expose]` is decided per module, and the audit's A1 is in force** (owner's decision; the earlier
  "keep it on every module" is superseded).  A module whose clients never unfold or compute one of its
  definitions opens with a plain `public section`; the rest keep `@[expose] public section`.  The split
  was made one module at a time by dropping the attribute and rebuilding the whole library, and it is
  checked the same way — the tree has **89 modules exposed and 33 not**, the two `ForMathlib` modules
  and `ChallengeSolved` among the 33.  Do not blanket-restore it and do not blanket-remove it either:
  Addendum 249's table records what the exposed side is for — `IET` (destructured in
  `TopBotFormalism` and `Pair/MeasureTools`), `TopBotFormalism`, `RauzyVeech/Path` (used at
  `RauzyReach` and `TrueStep`) and `CutSet/Basic` (destructured in `CutSet/Measure`) all need their
  bodies visible to a client, which is why they are exposed.
- **Every import line must be necessary** (owner's instruction; Addendum 224).  No module under
  `IETFree/` imports `Mathlib` as a whole, and a line that another import already supplies is a
  defect, not documentation: the criterion is that **deleting the line breaks the build**.  The
  greedy fixpoint of that test was computed in Addendum 224, on the 116 modules then present (224
  lines, at most 7 in one file, 51 modules with a single one); every line there was verified by
  removing it and rebuilding its module (`.scratch/tmp/verify_necessity.py`).  The renames, the
  splits and the remark's modules changed the figures — the tree now has **262 import lines over
  122 modules, at most 8 in one file** (`Pair/Irreducible.lean`) — and the fixpoint has **not** been
  recomputed on the final tree.  The cost is stated and accepted: a
  header names the one or two modules that *carry* what the file uses
  (`Measure/LevyRecurrence.lean` imports `Mathlib.Probability.Martingale.Convergence` and nothing
  else), so it no longer lists every module the file touches.  To add an import, add it and then
  check it: delete it again, and if the module still builds it does not belong.  `Challenge.lean` is
  the one exception and stays `import Mathlib` only; the umbrella `IETFree.lean` keeps all 122
  project imports because its job is coverage — a line there is not supposed to be necessary.
- **`lake shake` may be run, read-only, with `--keep-public`**: `lake shake --keep-public --explain
  IETFree`.  It only reports unless `--fix` is passed, and `--fix` is what did the damage in Addendum
  223 — it wrote the same ~40 irrelevant Mathlib leaves into every file and deleted project imports the
  tree needs — so the rewriting mode stays banned while the read-only one is how Addenda 249–251 used
  it.  `--keep-public` because 252 of the tree's 262 import lines are `public import`s, part of the
  module's interface: without the flag shake proposes removing lines that a client's own statements
  need, and `--explain` names the constants each line is credited with.  It exits 1 when it has
  suggestions, which is not a build failure.  Its output is a candidate list, not a verdict — shake
  judges relative to the list a file already has — so each suggestion is verified by deleting the line
  and rebuilding: nine became deletions that way, and the eight `NNRealPreprocessor` ones (an instance
  that only fires inside `linarith`) and the nine `public import IETFree.ForMathlib.…` ones (kept on
  purpose, the dependency being recorded where it is used) were dismissed as false positives.
- `#min_imports` answers the same question relative to the list a file already has, so it cannot decide
  it either; the tool that does is `lake build` on one module, once per candidate deletion.
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
