# The comparator pair

This directory holds the [comparator](https://github.com/leanprover/comparator) setup for
Theorem 1.1 — `main`, with Masur–Veech and Veech's rigidity as hypotheses.

| file | role |
|---|---|
| `../comparator.json` | the configuration: challenge module, solution module, the two theorem targets, the definition hole, `permitted_axioms` |
| `../ChallengeWeak.lean` | **the challenge**: one self-contained file, `import Mathlib` only |
| `../IETFree/ChallengeWeakSolved.lean` | **the solution**: imports the library, proves the two targets and fills the hole |
| `Check.lean` | a stand-in for the comparator: runs its algorithm on the two compiled modules |

```json
{
  "challenge_module": "ChallengeWeak",
  "solution_module": "IETFree.ChallengeWeakSolved",
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
  `translationVector`, `imageLengths`, `leftEnd_zero`, `idxSet`, `idx`, `mkIETFun`, `simplexRegion`,
  `simplexMap`, `simplexVolume`, `unitMeas`, `IsIrreduciblePerm`, `evalWordEquiv`.  They are *copies of
  the library's own text*: a shorter equivalent body would be a different declaration, and the
  definitional height in `ReducibilityHints` is compared as well.  All of them are library
  declarations except `evalWordEquiv`, which is only the bridge to the statement (it evaluates a word in
  two permutations of `ℝ` instead of two exchanges) and therefore lives in
  `IETFree/ChallengeWeakSolved.lean`, not in a library module — the challenge declares the same text;
* renames what cannot be the library's, and the solution declares the same renamed definitions —
  `UniqueErgodicFun`, `IsRigidByTranslationsFun` (the library's `UniqueErgodic` and
  `IsRigidByTranslations` are for `f : IET 0 1`, iterated by the group power), and
  `MasurVeechFun`, `VeechRigidityFun` (the two inputs in that form);
* leaves `mkIETEquiv` as a **definition hole**.

## The definition hole

`mkIETEquiv` is `:= sorry` in the challenge, and listed in `definition_names`. Comparator then
compares only its name, statement and safety, and checks that the solution's version is accepted by
the kernel and uses no axiom outside the permitted list. This is needed because the library proves
the two inverse laws of `mkIETEquiv` through the `private` core `mkIETFunCore` in
`IETFree/IET.lean`: a private name lives in its own module only, so no other module can ever declare
that constant, and the comparison of the body could not succeed. Emptying `definition_names` shows
this directly — `Check.lean` then reports `differs: mkIETEquiv._proof_1`.

The hole is pinned down by `coe_mkIETEquiv`, a *theorem target*: the solution has to prove that its
`mkIETEquiv` is the map of `mkIETFun`, which is exactly the property the proof uses.

## The solution

`IETFree/ChallengeWeakSolved.lean` declares the four `…Fun` predicates with the challenge's bodies,
proves `coe_mkIETEquiv` from `mkIETEquiv_apply`, and proves `main` by turning the challenge's
hypotheses into the library's (`uniqueErgodic_iff` and `isRigidByTranslations_iff`, both
`IET.pow_apply_iterate`; then `masurVeech_of_fun` and `veechRigidity_of_fun`, using that almost every
length vector is in the simplex, `simplexVolume_compl_simplex`), then quoting
`ChallengeWeakSolved.main_of_library` — the same theorem with the library's hypotheses, whose proof
is unchanged.

## Checking the pair without the comparator

The comparator needs `landrun` and `lean4export`, and a Lake package it can build; none of that works
in this VM (`/opt/mathlib` is root-owned and read-only). `Check.lean` runs the comparator's own
algorithm (`Comparator/Compare.lean`, `Comparator/Axioms.lean`) on the two `.olean` environments
instead of on their exports, and `Build.sh` runs it:

```sh
cd IET2 && lean --run Comparator/Check.lean
```

```text
theorem targets:   #[coe_mkIETEquiv, main]
definition holes:  #[mkIETEquiv]
declarations compared: 32661
axioms of the solution:    #[Classical.choice, Quot.sound, propext]
permitted by the config:   #[propext, Quot.sound, Classical.choice]
OK: ...
```

It is not the tool: it shares the algorithm, not the code. That it bites was checked by mutation —
changing a body in the challenge (`simplex`) is reported as `differs: simplex`, changing the
challenge's `main` (`w ≠ 1` to `w = 1`) as `the statement differs: main`, and dropping the definition
hole as `differs: mkIETEquiv._proof_1`.

## Running the real comparator

### One command

```sh
./Comparator/run.sh                        # Mathlib resolved by lakefile.toml
MATHLIB=/opt/mathlib ./Comparator/run.sh   # read-only prebuilt Mathlib (this VM)
```

`run.sh` does the whole recipe below: fetch and build the two tools if needed (it reuses
`.scratch/cmp`), create the Lake project, build `ChallengeWeak` and `IETFree.ChallengeWeakSolved`, and
run the comparator; it exits 0 only if the pair is accepted.  `--rebuild` forces the tools to be
rebuilt, and `COMPARATOR_REV`, `COMPARATOR_WORK` and `COMPARATOR_LANDRUN` override the defaults
(see `--help`).

### On a machine with `landrun`

```sh
cd IET2
lake exe cache get                                    # once, if you trust the cache
lake build ChallengeWeak IETFree.ChallengeWeakSolved
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory $(pwd) \
  -- bash -c 'lake env comparator comparator.json'
```

with `landrun` and `lean4export` in `PATH` (the comparator's README gives the version pairing;
`COMPARATOR_LANDRUN` and `COMPARATOR_LEAN4EXPORT` point at them explicitly).  Both modules are targets
of the repository's own Lake project (`lakefile.toml` declares a library for `IETFree/` and one for each
of the two statement files), so these `lake build` commands work as written once `lake exe cache get`
has been run.

### In this VM, with the repository's `fake-landrun` shim — done, and it accepts

`landrun` is not installed here, but the comparator ships `scripts/fake-landrun.sh`, which runs the
command unsandboxed.  That is enough to run the *genuine*
comparison (real exports, real declaration-by-declaration comparison, real axiom check, real kernel
replay); only the sandbox is shimmed.  What it took:

1. **The right revision.** Comparator's `master` and its `lean4export` are pinned to Lean v4.35.0,
   while this library is Lean 4.33.1 (its Mathlib is built for it; oleans are not portable across
   versions).  The last comparator commit with a v4.33 toolchain is `3927ad3`, and it pins
   `lean4export` at `15f6055` (the `v4.33.0` tag).  Build both with the local toolchain:

   ```sh
   git clone https://github.com/leanprover/comparator && cd comparator
   git checkout 3927ad3
   echo "leanprover/lean4:v4.33.1" > lean-toolchain     # the installed toolchain
   lake build comparator lean4export                    # both build against Lean core only
   ```

   (`landrun` absent, so nothing else is needed; `Export.Parse`, `Comparator.Compare` and
   `Comparator.Axioms` compile unchanged.)

2. **A Lake project the comparator can build in.** The comparator runs `lake build <module>` itself,
   and this library is normally built by `Build.sh` with `LEAN_PATH` at a prebuilt, read-only
   `/opt/mathlib`.  A throw-away project resolves Mathlib *by path* instead of from the registry:

   ```sh
   # .scratch/lake/lakefile.toml
   name = "ietfree_lake"
   [[require]] name = "mathlib" path = "/opt/mathlib"
   [[lean_lib]] name = "ChallengeWeak"
   [[lean_lib]] name = "IETFree"
   ```

   with `ChallengeWeak.lean` and `IETFree/` symlinked in and `comparator.json` copied.  Lake then
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
   Exporting #[coe_mkIETEquiv, main, …, mkIETEquiv] from ChallengeWeak
   Exporting #[coe_mkIETEquiv, main, …, mkIETEquiv] from IETFree.ChallengeWeakSolved
   Running Lean default kernel on solution.
   Lean default kernel accepts the solution
   Your solution is okay!
   ```

   Exit status 0.  And it is not vacuous: with `w ≠ 1` changed to `w = 1` in `ChallengeWeak.lean`'s
   `main`, the same command exits 1 with

   ```text
   uncaught exception: Challenge and solution theorem statement do not match: 'main'
   ```

`Build.sh` keeps running `Check.lean` as the cheap, always-on guard; the genuine run above is the
one-off certificate.
