# Working notes: what is true about this tree now

This file is the **current** record: what is proved, what the build is, which decisions are in force,
and which traps still bite.  It is not a specification — the declarations in `IETFree/` are the truth,
and `README.md` is the reader-facing account.

The full development log is [`HISTORY.md`](HISTORY.md): the 169 addenda of the `IET2` campaign (with the
table that maps every declaration name that no longer exists), then everything the two Masur–Veech
campaigns left in prose — their records, and the rigidity campaign's blueprint, plan and two
dependency-graph documents, plus the Birkhoff campaign's two blueprints.  Cite it for *why* something
is the way it is.

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
* `ChallengeSolved.veecheRigidity` — from `Rigidity.veechRigidity`.

Both are stated in the library's vocabulary, for the exchange `mkIET1 λ π : IET 0 1` and the
group power — the `…Fun` predicates of the conditional challenge are gone (see below).

## Status — measured, not remembered

- **The build is `lake build`.** 114 modules in `IETFree/`, plus the umbrella `IETFree.lean` and
  `Challenge.lean`; the last full build was **9164 jobs, exit 0, no warnings, no errors** (on Lean
  4.35.0 / Mathlib `v4.35.0`, Addendum 192; it was 8823 jobs on Lean 4.33.1).  The directory is
  **not** wiped to re-check warnings (see `## Commands`): after an
  edit, `lake build` reports the warnings of the modules it recompiles, and a full sweep is
  `./SlowBuild.sh`.  It is incremental and parallel (no-op ≈ 6 s, ordinary edit
  seconds, deep module one to two minutes).  It works in this VM because
  `.lake/packages/mathlib/.lake/build` already holds Mathlib's oleans (root-owned), so Lake never writes
  into the package; a change of Mathlib revision needs `lake exe cache get` first.
- **`SlowBuild.sh` is not the build**: plain `lean`, one process per module, everything recompiled,
  several minutes.  It is the thorough check — `sorry` count, `--strict` on `sorryAx`-reachability from
  `main`, and `Comparator/Check.lean`.  **Run it only when the owner asks.**
- **Axioms**: `#print axioms main` → `[propext, Classical.choice, Quot.sound]`.  The `sorryAx` count is
  3, all in `Challenge.lean` and deliberate (the definition hole `mkIETEquiv`, the statements
  `coe_mkIETEquiv` and `main`); the library has none.  `lakefile.toml` sets `warn.sorry = false`, so
  `lake build` says nothing about them — the axiom report is the guard.
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
- **Comparator, three ways, all green**: `lake comparator` (the tool in Lean core, which upstream
  now recommends) reads `comparator.json` and prints `Lean default kernel accepts the solution`;
  `Comparator/Check.lean` accepts the pair at 31 547 declarations; and the standalone comparator at
  `865edc1` — with nanoda and Lean's kernel — prints `== accepted`.  The core tool's nanoda step
  cannot run here (`bwrap` cannot bind `/opt/lean/bin/nanoda_bin`, `/opt/lean` being a symlink);
  Lean's kernel is unaffected and the standalone run covers nanoda.  See `Comparator/README.md`.
  Two mutations of the challenge are caught by `Check.lean`
  (`w ≠ 1` → `w = 1`: *the statement differs*; `0 < v i` → `0 ≤ v i`: *differs: simplexRegion*).
- **Declaration linters** (Batteries' `runLinter`, which `lake build` does not run): 0 findings for
  `IETFree` and 0 for `Challenge`, 14 linters (`runLinter` does not print its declaration count, so
  none is quoted here — re-run it with `-v` to see the linter list).
- **Size**: 114 modules, 45 739 lines (counted over `IETFree/**/*.lean` together with the umbrella
  `IETFree.lean`); 4 542 project declarations, of which 2 571 are written by
  hand (the rest are generated), and 3 974 reachable from `main` (re-measured after Addendum 172;
  the last paragraph of Addendum 160 states the walk — per-module `constNames.size`, generated
  declarations included, and the `getUsedConstants` closure of `main`).  Under the module system the
  generated declarations are named `_private.<Module>.0.…`, so the total moves with them; the
  hand-written count is the stable one.
- **The surviving `change`s are documented**: `CHANGE-AUDIT.md` records, for each of the 35,
  the error that deleting it produces — the reason it is there.  Do not delete one without
  reading its row (Addendum 185).
- **Docstrings and links are checked, not eyeballed**: a module docstring describes its module, not
  a stage of a campaign, and every declaration it names in backticks exists (Addendum 169 dumps
  `constNames` and joins it with Mathlib's names to check); the README's 218 repository links and
  its 162 declaration anchors were audited against the tree in the same pass (and re-anchored after
  the module conversion).

## Layout

`IETFree/` — three modules of single-exchange API at the root (`CutSet`, `CutSetMeasure`, `IET`: cut
sets and cells, `IsIET`/`mkIETFun`/`mkIETEquiv`/`mkIET1` (total in `λ`) and `mkIET1'` (on the
simplex), the simplex and `simplexVolume`, `unitMeas`,
the type `IET a b` and its group), then four subdirectories above them:

* `Pair/` (25 modules) — two exchanges: the free-group development.  Section 2 (centralizer, Lemmas
  2.7–2.10, Theorem 2.6, Proposition 2.5 `ae_diophantine`) and Section 3 (the length map, the good
  regions, the block rescalings, Lemmas 3.2–3.4, the assembly of the per-block words).
* `RauzyVeech/` (61 modules, 18 of them in `RichPath/`) — the Rauzy–Veech induction and the richness
  of the greedy path, and the invariant-measure side the induction steps use: `InvariantMeasure`
  (Lebesgue's measure on `[0, 1)`, the cells and the length vector of a measure, and the step from
  the ray condition and length-map injectivity to `∃! μ`) and `MainComponents` (the notions
  `HasPositiveBlockAt`, `HasPositiveBlocks`, `RayCondition`).
* `Rigidity/` (10) — Veech's rigidity: `veechRigidity` itself is stated in `Pair/Irreducible.lean`.
* `UniqueErgodicity/` (13) — unique ergodicity of an exchange: `MainTheorem` (the assembly of the
  a.e. theorem, which needs the proofs of its two inputs and therefore sits above `PosBlocks` and
  `RichPath`, and `masurVeech_ae_unique_invariant`), then the strong form: `UniqueErgodicity/Basic`
  holds the predicate `UniformBirkhoff`, and `IET` proves Theorem 2 (`UniqueErgodic → UniformBirkhoff`, for
  `mkIET1` and then for every exchange) together with Lemma 2.9 (`exists_uniform_birkhoff`).  This
  directory sits above `RauzyVeech/`; `InvariantMeasure` and `MainComponents`, which the induction
  steps themselves use, are inside `RauzyVeech/`.

At the root of `IETFree/` only the shared layers are left: `CutSet`, `CutSetMeasure`, `IET` (one
exchange, with the three notions `Invariant`, `UniqueErgodic` and `IsRigidByTranslations`), `TopBotFormalism`
(the two-bijection datum of the Marmi–Moussa–Yoccoz framework, below `Pair/`, `Rigidity/` and
`UniqueErgodicity/`) and `ChallengeSolved`.
`IETFree.lean` is the umbrella (its import list is generated by `lake exe mk_all --lib IETFree`);
`Challenge.lean`, one directory above, is the comparator challenge (`import Mathlib` only, imported
by nothing).

Every module is used in the proof of `main`, and so is every declaration except seventeen `rfl` lemmas
that `simp` applies definitionally (they never appear in a proof term, so the dependency graph calls
them dead while a live proof names them).  They are listed in `HISTORY.md`, Addendum 152; deleting them
breaks the build.

## Decisions in force — do not undo

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
  `RayCondition`, `GoodAt`) and the states of the inductions that really run (`Induction.Graded`,
  `InductionStep`, `NodeHeight.GradedStep`, `GradedStepMin`, `BalanceStep`).
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
- **`have _hstop := hstop` is deliberate**, in `RauzyVeech/Peel.lean` and
  `Rigidity/RigidStep.lean`: the statement carries a hypothesis (`hstop`) that the proof does not
  use, and the `have` is the only thing that keeps the unused-variable linter quiet.  Deleting it
  reintroduces a warning; the alternative — dropping the hypothesis from the statement — changes a
  public theorem (Addendum 190).
- **Every file is a module** (Addendum 172): `module` after the copyright block, `public import`
  everywhere, and the file's API in a `@[expose] public section` closed by a final `end`.  The
  exposure is blanket on purpose — it keeps every definition as transparent to its clients as
  before — and narrowing it to the definitions that really must unfold is a separate pass.
  **Trap:** an *auxiliary* declaration in a proof term is named `_private.<Module>.0.<name>`, so a
  declaration copied verbatim into `Challenge.lean` whose proof mentions one elaborates to a
  different term than the library's, and the comparator reports `differs: <name>`.  It is the
  auxiliary that is fatal, not the tactic style: `simp` and `omega` generate them (Addenda 172 and
  174), `refine`/`exact` do not.  Hence `idxSet_nonempty`'s tactic proof avoids `simp` and
  `simplexMap_val_lt` avoids `omega`, and neither `simplexMap` nor `idx` has a `by` in its body.
- `Challenge.lean`'s declarations are **verbatim copies of the library's** wherever `main`,
  `coe_mkIETEquiv` or `mkIETEquiv` reaches them — a shorter equivalent body is a different
  `ConstantInfo`.  In particular the body of `idx` must stay identical in the two files: `idx` is
  reachable, so its proof term is compared.
- The **definition hole** in `Challenge.lean` is `mkIETEquiv` because the proof that it is a
  bijection is not completely trivial, and the challenge file is meant to stay short and easy to
  read (owner's ruling, Addendum 170).  The `private` core of `IET.lean` makes a *verbatim copy* of
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
  `zip -r -q IET2.zip IET2 -x 'IET2/.lake/*' 'IET2/.scratch/*' '*.olean'` from the repository root.
- The repository is <https://github.com/sgouezel/IETFree> (`main`) and holds the contents of `IET2/` at
  its root, so module paths there are `IETFree/…`, not `IET2/IETFree/…`.

## Commands

```sh
lake build                                    # the build (incremental, parallel)
LEAN_PATH="$PWD/.lake/build/lib/lean:$PWD:$LEAN_PATH" \
  lake env lean --run Comparator/Check.lean   # comparator stand-in, ~40 s
lake env lean --run .lake/packages/batteries/scripts/runLinter.lean --no-build IETFree   # ~10 s
lake env lean --run .lake/packages/batteries/scripts/runLinter.lean --no-build Challenge
MATHLIB=/opt/mathlib ./Comparator/run.sh      # the genuine comparator, ~4 min
./SlowBuild.sh --strict                       # the slow thorough check — only on request
```

**`.lake/build` is never deleted** (owner's instruction, 3 Nov): wiping it costs minutes and buys
little.  A claim of zero warnings therefore rests on warnings emitted while recompiling, and the way
to get a full warning sweep is `./SlowBuild.sh` — plain `lean`, every module, per-module logs in
`.scratch/tmp` — not `rm -rf .lake/build`.  Delete the directory only on an explicit request.

## Traps that still bite

- `warn.sorry = false` in `lakefile.toml`: a `sorry` is invisible in `lake build`'s output and the olean
  is still written.  Read the `#print axioms main` line, or run `SlowBuild.sh`.
- Stale in-tree `.olean` files (left by `SlowBuild.sh`) shadow moved or deleted modules; delete them
  before believing an error about a module that "still exists".
- `lake env lean <file>` does **not** apply the lakefile's `[leanOptions]`; pass
  `-DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3` for a single-file check.
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
