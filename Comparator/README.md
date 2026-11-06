# The comparator pair

This directory holds the [comparator](https://github.com/leanprover/comparator) setup for
Theorem 1.1 — `main`, unconditionally.

| file | role |
|---|---|
| `../comparator.json` | the configuration: challenge module, solution module, the two theorem targets, the definition hole, `permitted_axioms` |
| `../Challenge.lean` | **the challenge**: one self-contained file, `import Mathlib` only |
| `../IETFree/ChallengeSolved.lean` | **the solution**: imports the library, proves the two targets and fills the hole |
| `Check.lean` | a stand-in for the comparator: runs its algorithm on the two compiled modules |

```json
{
  "challenge_module": "Challenge",
  "solution_module": "IETFree.ChallengeSolved",
  "theorem_names": ["coe_mkIETEquiv", "main"],
  "definition_names": ["mkIETEquiv"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
```

## What the challenge may and may not rename

Comparator compares the two statements declaration by declaration, **by name**, and then walks every
declaration they reach: everything except the targets and the definition holes must be the *same
constant* on both sides — same name, same type, same value, the proofs inside a definition included.
So the challenge file

* declares, verbatim, the declarations its statement uses — `leftEnd`, `imageLeft`,
  `translationVector`, `idxSet`, `idx`, `mkIETFun`, `simplexRegion`, `simplexMap`,
  `simplexVolume`, `evalWordEquiv`.  They are *copies of the library's own text*: a shorter equivalent
  body would be a different declaration, and the definitional height in `ReducibilityHints` is
  compared as well.  All of them are library declarations except `evalWordEquiv`, which is only the
  bridge to the statement (it evaluates a word in two permutations of `ℝ` instead of two exchanges)
  and therefore lives in `IETFree/ChallengeSolved.lean`, not in a library module — the challenge
  declares the same text;
* leaves `mkIETEquiv` as a **definition hole**.

Nothing is renamed: the unconditional statement mentions no `…Fun` predicate, so every declaration it
reaches is the library's.  (The earlier, conditional challenge `ChallengeWeak.lean` also had to
rename four `…Fun` predicates of its own; that file has been removed, and the predicates themselves
were deleted, and the library's two `Prop`s `MasurVeech`/`VeechRigidity` became the theorems
`masurVeech`/`veechRigidity`.)

## The definition hole

`mkIETEquiv` is `:= sorry` in the challenge, and listed in `definition_names`. Comparator then
compares only its name, statement and safety, and checks that the solution's version is accepted by
the kernel and uses no axiom outside the permitted list.

The challenge leaves it a hole to keep the file short and easy to read: `mkIETEquiv` packages the
exchange `mkIETFun lam π a` as an `Equiv ℝ ℝ`, whose inverse is the exchange of the inverse
permutation with the lengths reordered, and the two inverse laws behind that packaging are not
completely trivial. A verbatim copy is not open to the challenge either: the library proves the
right-inverse law from the `private` `mkIETFunCore_inv_right` in `IETFree/IET.lean`, a private name
lives in its own module only, so the same term cannot be written in `Challenge.lean`. Emptying
`definition_names` shows the mismatch directly — `Check.lean` then reports
`differs: mkIETEquiv._proof_1`.

The hole is pinned down by `coe_mkIETEquiv`, a *theorem target*: the solution has to prove that its
`mkIETEquiv` is the map of `mkIETFun`, which is exactly the property the proof uses.

## The solution

`IETFree/ChallengeSolved.lean` proves `coe_mkIETEquiv` from `mkIETEquiv_apply`, and proves `main`
directly — Theorem 1.1 for the library's own exchanges — by applying the two theorems of the
literature, `masurVeech` and `veechRigidity` (`IETFree/Pair/Irreducible.lean`); nothing is left
as a hypothesis.

## Checking the pair without the comparator

The comparator needs `landrun` and `lean4export`, and a Lake package it can build; none of that works
in this VM (`/opt/mathlib` is root-owned and read-only). `Check.lean` runs the comparator's own
algorithm (`Comparator/Compare.lean`, `Comparator/Axioms.lean`) on the two `.olean` environments
instead of on their exports, and `SlowBuild.sh` runs it (as does the reader, with the command below):

```sh
cd IET2 && lean --run Comparator/Check.lean
```

```text
theorem targets:   #[coe_mkIETEquiv, main]
definition holes:  #[mkIETEquiv]
declarations compared: 30899
axioms of the solution:    #[Classical.choice, Quot.sound, propext]
permitted by the config:   #[propext, Quot.sound, Classical.choice]
OK: ...
```

It is not the tool: it shares the algorithm, not the code. That it bites was checked by mutation —
changing a body in the challenge (`simplexRegion`) is reported as `differs: simplexRegion`, changing the
challenge's `main` (`w ≠ 1` to `w = 1`) as `the statement differs: main`, and dropping the definition
hole as `differs: mkIETEquiv._proof_1`.

## Running the real comparator

### One command

```sh
./Comparator/run.sh                        # Mathlib resolved by lakefile.toml
MATHLIB=/opt/mathlib ./Comparator/run.sh   # read-only prebuilt Mathlib (this VM)
```

`run.sh` does the whole recipe below: fetch and build the two tools if needed (it reuses
`.scratch/cmp`), create the Lake project, build `Challenge` and `IETFree.ChallengeSolved`, and
run the comparator; it exits 0 only if the pair is accepted.  `--rebuild` forces the tools to be
rebuilt, and `COMPARATOR_REV`, `COMPARATOR_WORK` and `COMPARATOR_LANDRUN` override the defaults
(see `--help`).

### On a machine with `landrun`

```sh
cd IET2
lake exe cache get                                    # once, if you trust the cache
lake build Challenge IETFree.ChallengeSolved
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory $(pwd) \
  -- bash -c 'lake env comparator comparator.json'
```

with `landrun` and `lean4export` in `PATH` (the comparator's README gives the version pairing;
`COMPARATOR_LANDRUN` and `COMPARATOR_LEAN4EXPORT` point at them explicitly).  Both modules are targets
of the repository's own Lake project (`lakefile.toml` declares a library for `IETFree/` and one for each
of the two statement files), so these `lake build` commands work as written once `lake exe cache get`
has been run.

### The core tool: `lake comparator` — the route to use

Comparator moved into Lean core at v4.35.0, and upstream's own README now deprecates the standalone
repository in favour of it.  The core tool reads the same `comparator.json` (the
`challenge_module`, `solution_module`, `theorem_names`, `definition_names` and `permitted_axioms`
fields are the ones this repository sets), builds and exports both modules inside a `bwrap` sandbox,
and replays the solution through Lean's kernel:

```sh
lake exe cache get      # once
lake build              # once, so that the manifest and the oleans are in place
lake comparator         # reads ./comparator.json
```

On this tree it prints `Lean default kernel accepts the solution` and `Your solution is okay!`.
Two caveats, both about this VM rather than the tool:

* `lake comparator` honours `enable_nanoda` from the config, but `bwrap` cannot bind
  `/opt/lean/bin/nanoda_bin` here, because `/opt/lean` is a **symlink** into
  `/opt/lean.4.35.0-56a005855ea1` and the sandbox cannot create the missing parent directories.  The
  run then ends with `nanoda exited with 1` although Lean's kernel accepted.  Dropping
  `enable_nanoda` (as in a scratch copy of the config) gives a clean pass; the standalone tool below
  is what exercises nanoda here.
* `bwrap` needs unprivileged user namespaces, which this VM provides.

### In this VM, with the repository's `fake-landrun` shim — done, and it accepts

`landrun` is not installed here, but the comparator ships `scripts/fake-landrun.sh`, which runs the
command unsandboxed.  That is enough to run the *genuine*
comparison (real exports, real declaration-by-declaration comparison, real axiom check, real kernel
replay); only the sandbox is shimmed.  What it took:

1. **The right revision.** Comparator moved into Lean core at v4.35.0 (`lake comparator`,
   `lake check`), and this library is on that toolchain.  The standalone repository still works;
   use the revision whose toolchain matches, `865edc1` for Lean 4.35.0, with whatever
   `lean4export` it pins:

   ```sh
   git clone https://github.com/leanprover/comparator && cd comparator
   git checkout 865edc1                                  # the revision on Lean 4.35.0
   lake build comparator lean4export                     # both build against Lean core only
   ```

   (`landrun` absent, so nothing else is needed; `Export.Parse`, `Comparator.Compare` and
   `Comparator.Axioms` compile unchanged.)

2. **A Lake project the comparator can build in.** The comparator runs `lake build <module>` itself,
   and this library is normally built by `SlowBuild.sh` with `LEAN_PATH` at a prebuilt, read-only
   `/opt/mathlib`.  A throw-away project resolves Mathlib *by path* instead of from the registry:

   ```sh
   # .scratch/lake/lakefile.toml
   name = "ietfree_lake"
   [[require]] name = "mathlib" path = "/opt/mathlib"
   [[lean_lib]] name = "Challenge"
   [[lean_lib]] name = "IETFree"
   ```

   with `Challenge.lean` and `IETFree/` symlinked in and `comparator.json` copied.  Lake then
   builds both modules from source in about a minute.

3. **The run.**

   ```sh
   cd .scratch/lake
   COMPARATOR_LANDRUN=../cmp/comparator/scripts/fake-landrun.sh \
   COMPARATOR_LEAN4EXPORT=../cmp/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export \
   LEAN_PATH=$PWD/.lake/build/lib/lean:$LEAN_PATH \
     ../cmp/comparator/.lake/build/bin/comparator comparator.json
   ```

   ```text
   Exporting #[coe_mkIETEquiv, main, …, mkIETEquiv] from Challenge
   Exporting #[coe_mkIETEquiv, main, …, mkIETEquiv] from IETFree.ChallengeSolved
   Running Lean default kernel on solution.
   Lean default kernel accepts the solution
   Your solution is okay!
   ```

   Exit status 0.  And it is not vacuous: with `w ≠ 1` changed to `w = 1` in `Challenge.lean`'s
   `main`, the same command exits 1 with

   ```text
   uncaught exception: Challenge and solution theorem statement do not match: 'main'
   ```

`SlowBuild.sh` runs `Check.lean` as part of its thorough check; for ordinary work the guard is the
one command above, and the genuine run is the one-off certificate.
