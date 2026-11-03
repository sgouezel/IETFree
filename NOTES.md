# Working notes: what is true about this tree now

This file is the **current** record: what is proved, what the build is, which decisions are in force,
and which traps still bite.  It is not a specification — the declarations in `IETFree/` are the truth,
and `README.md` is the reader-facing account.

The full development log is [`HISTORY.md`](HISTORY.md): the 164 addenda of the `IET2` campaign (with the
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

* `ChallengeSolved.main_of_library` — Sections 2 and 3 of the paper: the a.e. block data plus the
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
  `Challenge.lean`; the last build from an empty `.lake/build` was 8825 jobs, exit 0, no warnings
  (8823 since Addendum 158 removed two modules), but that directory is **not** wiped to re-check
  warnings any more (see `## Commands`): after an
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
- **Comparator**: `Comparator/Check.lean` accepts the pair `Challenge` / `IETFree.ChallengeSolved`
  (30 899 declarations compared, only the permitted axioms); the genuine tool was run on it too
  (`Comparator/run.sh`, comparator `3927ad3`).  Two mutations of the challenge are caught
  (`w ≠ 1` → `w = 1`: *the statement differs*; `0 < v i` → `0 ≤ v i`: *differs: simplexRegion*).
- **Declaration linters** (Batteries' `runLinter`, which `lake build` does not run): 0 findings for
  `IETFree` and 0 for `Challenge`, 14 linters (`runLinter` does not print its declaration count, so
  none is quoted here — re-run it with `-v` to see the linter list).
- **Size**: 114 modules, 46 028 lines; 4 509 project declarations, of which 3 941 are reachable
  from `main` (re-measured after Addendum 161; the last paragraph of Addendum 160 states the walk —
  per-module `constNames.size`, generated declarations included, and the `getUsedConstants` closure
  of `main`).

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
  `RichPath`, and `masurVeech_ae_unique_invariant`), then the strong form: `Basic` holds the
  predicate `UniformBirkhoff`, and `IET` proves Theorem 2 (`UniqueErgodic → UniformBirkhoff`, for
  `mkIET1` and then for every exchange) together with Lemma 2.9 (`exists_uniform_birkhoff`).  This
  directory sits above `RauzyVeech/`; `InvariantMeasure` and `MainComponents`, which the induction
  steps themselves use, are inside `RauzyVeech/`.

At the root of `IETFree/` only the shared layers are left: `CutSet`, `CutSetMeasure`, `IET` (one
exchange, with `Invariant`/`UniqueErgodic`), `Basic` (the two-bijection datum and
`IsRigidByTranslations`, below `Pair/`, `Rigidity/` and `UniqueErgodicity/`) and `ChallengeSolved`.
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
  (`UniqueErgodicity.uniformBirkhoff_of_uniqueErgodic`) and assumed nowhere.  `IsRigidByTranslations`
  (Definition 2.2) stays in `Basic.lean`.  Both are stated for the bundled exchange `mkIET1 lam π`
  and iterated with the group power.  The four `…Fun` predicates that `ChallengeWeak.lean` needed
  (the same conditions on a bare map `ℝ → ℝ`, iterated with `f^[n]`) **are gone** (owner's
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
- `Challenge.lean`'s declarations are **verbatim copies of the library's** wherever `main`,
  `coe_mkIETEquiv` or `mkIETEquiv` reaches them — a shorter equivalent body is a different
  `ConstantInfo`.  In particular the body of `idx` must stay identical in the two files: `idx` is
  reachable, so its proof term is compared.
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
