# Almost Every Pair of Interval Exchange Transformations Does Not Generate a Free Group
### A Lean 4 formalization

This repository contains a formalization in Lean 4 of the paper

> Sébastien Gouëzel, *Almost every pair of interval exchange transformations does not generate a
> free group*, [arXiv:2610.29993](https://arxiv.org/abs/2610.29993) [math.DS], 2026.

The paper's abstract: *"We show that the Lebesgue measure of the set of pairs of interval exchange
transformations that generate a free group of rank 2 is zero."*

**Status.** The main theorem is proved **outright**: [`IETFree/ChallengeSolved.lean`](https://github.com/sgouezel/IETFree/blob/main/IETFree/ChallengeSolved.lean) proves
[`main`](https://github.com/sgouezel/IETFree/blob/main/IETFree/ChallengeSolved.lean#L223), the
unconditional form of Theorem 1.1 stated by
[`Challenge.lean`](https://github.com/sgouezel/IETFree/blob/main/Challenge.lean), and the library
carries a single axiom check there — `#print axioms main` — which reports
`[propext, Classical.choice, Quot.sound]`.  Nothing is assumed: the two results that the paper quotes
from the literature are proved in [`IETFree/RauzyVeech/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/RauzyVeech), [`IETFree/Rigidity/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/Rigidity) and
[`IETFree/UniqueErgodicity/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/UniqueErgodicity). The formalization notably includes a full development of
Rauzy–Veech induction in Marmi–Moussa–Yoccoz formalism, culminating in the proof that
a.e. interval exchange transformation for an irreducible permutation is
uniquely ergodic (essentially following Kerckhoff's argument) and rigid
(using Veech's argument rephrased in terms of Kerckhoff's framework to avoid the
need of ergodicity of the projectivized Rauzy–Veech induction).

The formalization was produced by supervised **autoformalization**: an AI agent working in **SAIR Open Math
OS**, writing Lean against a pinned Mathlib and checking every step by compilation,
under human guidance for API choices and proof construction. The full record is
[`HISTORY.md`](HISTORY.md) — the 169 addenda of the development: what was tried, what failed, which
statements had to be restated and why, the reconciliation table of every name that has disappeared,
and the records, blueprints and dependency graphs of the two Masur–Veech campaigns whose theorems the
last step uses.  [`NOTES.md`](NOTES.md) is the one-page summary of the current state: what is proved,
what the build is, which decisions are in force, which traps still bite.  Neither file is a
specification: the declarations in [`IETFree/`](https://github.com/sgouezel/IETFree/tree/main/IETFree) are.

The three `sorry`s of the tree are all in [`Challenge.lean`](https://github.com/sgouezel/IETFree/blob/main/Challenge.lean), and all deliberate: the definition hole
[`mkIETEquiv`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L493) and the two
targets [`coe_mkIETEquiv`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L509) and
[`main`](https://github.com/sgouezel/IETFree/blob/main/IETFree/ChallengeSolved.lean#L223).  That
file *is* the comparator challenge, and [`IETFree/ChallengeSolved.lean`](https://github.com/sgouezel/IETFree/blob/main/IETFree/ChallengeSolved.lean) is its solution; see
[the comparator challenge](#the-comparator-challenge).

## What is proved

The final statement is [`main`](https://github.com/sgouezel/IETFree/blob/main/IETFree/ChallengeSolved.lean#L223), in the words of the challenge file — Theorem 1.1 of the
paper, **with nothing assumed**:

```lean
theorem main {d e : ℕ} [NeZero d] [NeZero e] (π : Equiv.Perm (Fin d)) (σ : Equiv.Perm (Fin e)) :
    ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
    ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧
      evalWordEquiv w (mkIETEquiv p.1 π 0) (mkIETEquiv p.2 σ 0) = 1
```

No hypothesis on `d`, `e`, `π` or `σ`: reducible permutations, fixed cells and one-letter alphabets
are all included.  `#print axioms main` reports `[propext, Classical.choice, Quot.sound]`.

It is assembled from three layers, each of which is a theorem of the library:

* **Masur–Veech** ([`IETFree/RauzyVeech/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/RauzyVeech), [`IETFree/UniqueErgodicity/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/UniqueErgodicity)): almost every irreducible
  exchange is uniquely ergodic, in the sense of Definition 2.1 — a unique invariant probability
  measure carried by `[0, 1)` ([`UniqueErgodic`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L992)).
  Proved by the Rauzy–Veech induction
  ([`masurVeech_ae_unique_invariant`](https://github.com/sgouezel/IETFree/blob/main/IETFree/UniqueErgodicity/MainTheorem.lean#L103),
  and [`masurVeech`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L60) for
  `mkIET1 λ π`); [`IETFree/UniqueErgodicity/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/UniqueErgodicity) then derives the strong form, uniform convergence of
  the Birkhoff averages of continuous functions
  ([`uniformBirkhoff_of_uniqueErgodic`](https://github.com/sgouezel/IETFree/blob/main/IETFree/UniqueErgodicity/IET.lean#L561)).
* **Veech's rigidity** ([`IETFree/Rigidity/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/Rigidity)): almost every irreducible exchange is rigid by
  translations ([`veechRigidity`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L71)).
* **Section 2 and 3** ([`IETFree/Pair/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/Pair)): for almost every pair of length vectors, and for every pair
  of data with those lengths, there is a nontrivial word trivial on `[0, 1)`.  This is
  Lemma 3.4 for a.e. lengths plus the assembly of the per-block words; it is the proof of
  [`main`](https://github.com/sgouezel/IETFree/blob/main/IETFree/ChallengeSolved.lean#L223),
  whose two inputs are the two bullets above.

The two a.e. inputs are stated for the exchange [`mkIET1 λ π : IET 0 1`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L911) and iterated with
the group power, which is the form the Section 2–3 theorems use; they are
[`masurVeech`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L60) and
[`veechRigidity`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L71).
(The transfer argument of `UniqueErgodicity` works with the iterate `f^[n]` of the underlying
function, hence the shape of [`UniformBirkhoff`](https://github.com/sgouezel/IETFree/blob/main/IETFree/UniqueErgodicity/Basic.lean#L61),
which also carries Lemma 2.9
[`exists_uniform_birkhoff`](https://github.com/sgouezel/IETFree/blob/main/IETFree/UniqueErgodicity/IET.lean#L582).)

## The comparator challenge

[Comparator](https://github.com/leanprover/comparator) is Lean FRO's independent judge for a Lean
proof: given a *challenge* file that states a theorem with `sorry` and a *solution* file that proves
it, it checks that the solution proves the same statement, uses no axiom outside a permitted list,
and that the kernel accepts the proof. (Comparator is deprecated upstream: as of Lean v4.35.0 it is
part of core, as `lake comparator` with `lake check`. This library is pinned to Lean 4.33.1, so the
standalone tool is the one that applies.)

The challenge is [`Challenge.lean`](https://github.com/sgouezel/IETFree/blob/main/Challenge.lean) — Theorem 1.1, in Mathlib-only language — and the solution is
**the library itself**:

| file | contents |
|---|---|
| [`comparator.json`](https://github.com/sgouezel/IETFree/blob/main/comparator.json) | the configuration: challenge module, solution module, the theorem targets, the definition hole, `permitted_axioms` |
| [`Challenge.lean`](https://github.com/sgouezel/IETFree/blob/main/Challenge.lean) | the challenge: one self-contained file, `import Mathlib` only |
| [`IETFree/ChallengeSolved.lean`](https://github.com/sgouezel/IETFree/blob/main/IETFree/ChallengeSolved.lean) | the solution: imports the library, proves both targets and fills the definition hole |

```json
{
  "challenge_module": "Challenge",
  "solution_module": "IETFree.ChallengeSolved",
  "theorem_names": ["coe_mkIETEquiv", "main"],
  "definition_names": ["mkIETEquiv"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
```

Comparator compares the two statements declaration by declaration, by name, and then every
declaration they reach; only the targets ([`coe_mkIETEquiv`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L509), [`main`](https://github.com/sgouezel/IETFree/blob/main/IETFree/ChallengeSolved.lean#L223)) and the definition hole
([`mkIETEquiv`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L493)) may differ.  The unconditional statement reaches only the single-exchange API, so the challenge declares
verbatim the declarations it uses — [`leftEnd`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L171), [`imageLeft`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L179), [`translationVector`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L184),
[`idxSet`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L239), [`idx`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L252), [`mkIETFun`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L448), [`simplexRegion`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L107), [`simplexMap`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L118), [`simplexVolume`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L126) and
[`evalWordEquiv`](https://github.com/sgouezel/IETFree/blob/main/IETFree/ChallengeSolved.lean#L62) — and leaves [`mkIETEquiv`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L493) a *definition hole*, pinned down by the target
[`coe_mkIETEquiv`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L509).  Nothing has to be renamed: the strong statement mentions no `…Fun` predicate, so every
declaration it reaches is the library's.  The hole is there to keep the file short and easy to read:
[`mkIETEquiv`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L493) packages the exchange as a bijection of `ℝ` — its inverse is the exchange of the
inverse permutation with the lengths reordered — and the two inverse laws behind that packaging are
not completely trivial, so the challenge leaves them to the solution instead of carrying them.
[Comparator/README.md](Comparator/README.md) has the details.

## Layout and build

The Lean sources are in [`IETFree/`](https://github.com/sgouezel/IETFree/tree/main/IETFree): the single-exchange layer at the root — `CutSet`,
`CutSetMeasure`, [`IET`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L811), which also holds the three notions the theorem is stated with, [`Invariant`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L983),
[`UniqueErgodic`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L992) and [`IsRigidByTranslations`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L999) — the two-bijection datum in `TopBotFormalism`, four thematic
subdirectories above them, and the challenge solution on top.  114 modules, 45 739 lines.
Every file is a Lean **module** — a `module` header, `public import`s, and a `@[expose] public
section` holding its declarations — so the library meets the module-system requirement of the
Palomar registry; the exposure is blanket, which keeps every definition as transparent to its
clients as it was before the conversion.
Every module is used in the proof of [`main`](https://github.com/sgouezel/IETFree/blob/main/IETFree/ChallengeSolved.lean#L223), and so is
every declaration except seventeen: those are `rfl` lemmas applied by `simp` definitionally, so they
leave no trace in any proof term while a live proof still names them.  The library was pruned by
walking the dependency graph of the main theorem (see [`HISTORY.md`](HISTORY.md), Addendum 152).

| path | contents |
|---|---|
| [`IETFree/IET.lean`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean), [`CutSet.lean`](https://github.com/sgouezel/IETFree/blob/main/IETFree/CutSet.lean), [`CutSetMeasure.lean`](https://github.com/sgouezel/IETFree/blob/main/IETFree/CutSetMeasure.lean) | **one exchange**: cut sets and their cells, the measurability of a piecewise translation, the predicate [`IsIET`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L37), the explicit construction [`mkIETFun`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L448) / [`mkIETEquiv`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L493) / [`mkIET1`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L911), the simplex and its measure [`simplexVolume`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L126), Lebesgue measure [`unitMeas`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L947) on `[0, 1)`, the type [`IET a b`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L811) with its group structure, and the three notions the main theorem is stated with, [`Invariant`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L983), [`UniqueErgodic`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L992) (Definition 2.1) and [`IsRigidByTranslations`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L999) (Definition 2.2) |
| [`IETFree/Pair/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/Pair) (25 modules) | **two exchanges**: the free-group development — the centralizer, the lattice bounds on displacements and singularities, Section 2's irreducible case ([`IsIrreduciblePerm`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L1047), [`masurVeech`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L60), [`veechRigidity`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L71), Theorem 2.6) and Proposition 2.5 ([`ae_diophantine`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Diophantine.lean#L963)) — and Section 3's reduction to blocks: the length map, the good regions, the block rescalings, Lemmas 3.2–3.4 and the assembly of the per-block words |
| [`IETFree/RauzyVeech/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/RauzyVeech) (61 modules, 18 of them in [`RichPath/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/RauzyVeech/RichPath)) | the **Rauzy–Veech induction**: the step and the path matrices, the Rauzy diagram, the volume of path cylinders, the columns and their spread, the ray criterion, the towers and their floors, and the graded induction proving that the greedy path is rich — plus the invariant-measure side the induction steps use: [`InvariantMeasure`](https://github.com/sgouezel/IETFree/blob/main/IETFree/RauzyVeech/InvariantMeasure.lean) (Lebesgue's measure, the cells and the length vector of a measure, and the uniqueness step) and `MainComponents` (the notions the ray criterion is phrased with) |
| [`IETFree/Rigidity/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/Rigidity) (10 modules) | **Veech's rigidity** for a.e. irreducible exchange, by the Rauzy–Veech induction: the good node, the rigid step, the hitting lemma and the assembly ([`veechRigidity`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L71)) |
| [`IETFree/UniqueErgodicity/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/UniqueErgodicity) (13 modules) | **unique ergodicity** of an exchange: the a.e. theorem and its assembly (`MainTheorem`, [`masurVeech_ae_unique_invariant`](https://github.com/sgouezel/IETFree/blob/main/IETFree/UniqueErgodicity/MainTheorem.lean#L103)), and the **strong form** of Masur–Veech — a unique invariant probability measure gives uniformly convergent Birkhoff averages, through the compact-space tool `CompactTool` (Tool 1 of the source), the split interval and its germ map ([`uniformBirkhoff_of_uniqueErgodic`](https://github.com/sgouezel/IETFree/blob/main/IETFree/UniqueErgodicity/IET.lean#L561)) — together with Lemma 2.9 ([`exists_uniform_birkhoff`](https://github.com/sgouezel/IETFree/blob/main/IETFree/UniqueErgodicity/IET.lean#L582)) |
| [`IETFree/TopBotFormalism.lean`](https://github.com/sgouezel/IETFree/blob/main/IETFree/TopBotFormalism.lean) | interval exchanges in the Marmi–Moussa–Yoccoz framework for the Rauzy induction: a fixed alphabet with a top and a bottom permutation, the datum [`IETDatum₂`](https://github.com/sgouezel/IETFree/blob/main/IETFree/TopBotFormalism.lean#L76) and its simplex measure, and the translation to and from the single-permutation picture ([`perm`](https://github.com/sgouezel/IETFree/blob/main/IETFree/TopBotFormalism.lean#L88), [`ofPerm`](https://github.com/sgouezel/IETFree/blob/main/IETFree/TopBotFormalism.lean#L166), [`toIET`](https://github.com/sgouezel/IETFree/blob/main/IETFree/TopBotFormalism.lean#L115)) — below [`Pair/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/Pair), [`Rigidity/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/Rigidity) and [`UniqueErgodicity/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/UniqueErgodicity) |
| [`IETFree/ChallengeSolved.lean`](https://github.com/sgouezel/IETFree/blob/main/IETFree/ChallengeSolved.lean) | the solution of the comparator challenge: [`main`](https://github.com/sgouezel/IETFree/blob/main/IETFree/ChallengeSolved.lean#L223) in the challenge's words, and the two bridges [`masurVeech`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L60) / [`veechRigidity`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L71) |
| [`Challenge.lean`](https://github.com/sgouezel/IETFree/blob/main/Challenge.lean) | the comparator challenge: one self-contained file at the top level, `import Mathlib` only |
| [`IETFree.lean`](https://github.com/sgouezel/IETFree/blob/main/IETFree.lean) | the umbrella: it imports every module of the library (its import list is generated by `lake exe mk_all --lib IETFree`) |
| [`Comparator/Check.lean`](https://github.com/sgouezel/IETFree/blob/main/Comparator/Check.lean), [`Comparator/README.md`](https://github.com/sgouezel/IETFree/blob/main/Comparator/README.md) | the local stand-in for the comparator, and the description of the pair |
| [`HISTORY.md`](HISTORY.md), [`NOTES.md`](NOTES.md) | the full development record — the IET2 addenda, the reconciliation table, and the Masur–Veech campaigns' records, blueprints and dependency graphs — and the one-page summary of the current state |

Requirements: Lean 4.33.1. The repository is a **Lake project**: [`lean-toolchain`](https://github.com/sgouezel/IETFree/blob/main/lean-toolchain) (Lean 4.33.1),
[`lakefile.toml`](https://github.com/sgouezel/IETFree/blob/main/lakefile.toml) (Mathlib at the `v4.33.1` tag, and one Lean library for [`IETFree/`](https://github.com/sgouezel/IETFree/tree/main/IETFree) plus one for the statement file) and [`lake-manifest.json`](https://github.com/sgouezel/IETFree/blob/main/lake-manifest.json). The build is

```sh
lake exe cache get   # once: download Mathlib's oleans
lake build           # build IETFree and Challenge
```

`lake build` is the build, here too: this VM's `.lake/packages/mathlib` already holds Mathlib's
oleans, so Lake sees the pinned git package as built and needs no `cache get`.  It is incremental and
parallel — a no-op costs seconds, an edit to a deep module a minute or two, a build from a removed
`.lake/build` under three.  A package that Lake would have to *rewrite* is another matter: those
directories are root-owned, so a change of Mathlib revision needs `lake exe cache get` (or a
`path = "/opt/mathlib"` require) first.

[`SlowBuild.sh`](https://github.com/sgouezel/IETFree/blob/main/SlowBuild.sh) is the *slow* thorough check, not the build: plain `lean`, one process per module,
in dependency order, everything recompiled every time and Mathlib reloaded per module, so a full run
costs several minutes.  It is worth it only when something a `lake build` cannot see is wanted: it
compiles with `warn.sorry` **on** (the lakefile has `warn.sorry = false`) and so counts the
declarations that still depend on `sorryAx`, `--strict` fails if `sorryAx` is reachable from [`main`](https://github.com/sgouezel/IETFree/blob/main/IETFree/ChallengeSolved.lean#L223),
and it runs [`Comparator/Check.lean`](https://github.com/sgouezel/IETFree/blob/main/Comparator/Check.lean) on the two compiled modules.  Its module list is not maintained by
hand: it is the topological sort of the imports of the umbrella [`IETFree.lean`](https://github.com/sgouezel/IETFree/blob/main/IETFree.lean), so a new module needs
only its import there.  That import list itself is generated by `lake exe mk_all --lib IETFree`.

The build enables the Mathlib linter set (as [`lakefile.toml`](https://github.com/sgouezel/IETFree/blob/main/lakefile.toml) specifies) and is **warning-free**: a `lake build`
from a removed `.lake/build` reports no linter warning at all.  The only diagnostics are the three
`sorry`s of the statement file, which the build does not print (`warn.sorry = false`) and which
[`SlowBuild.sh`](https://github.com/sgouezel/IETFree/blob/main/SlowBuild.sh) counts.

The *declaration* linters (Mathlib's `runLinter`, which `lake build` does not run) are clean as well:
0 findings in 2 613 declarations (plus 2 055 automatically generated ones), 14 linters, for `IETFree`
and for `Challenge`.  In this VM the driver's executable cannot be built (its C objects would go into
the read-only Mathlib tree), so it is run interpreted — the command is in [`NOTES.md`](NOTES.md),
§Commands, and the long story in [`HISTORY.md`](HISTORY.md), §"The declaration linters are clean".

```sh
lake build                             # the build: incremental, parallel, warning-free
rm -rf .lake/build && lake build       # the same, from scratch (what a zero-warning claim needs)
LEAN_PATH="$PWD/.lake/build/lib/lean:$PWD:$LEAN_PATH" \
  lake env lean --run Comparator/Check.lean   # the comparator stand-in, ~40 s
./SlowBuild.sh --strict                # the slow thorough check: sorry count, axiom report, the same
                                       # comparator run.  Ask for it; it is not part of the loop.
MATHLIB=/opt/mathlib Comparator/run.sh # the genuine comparator end to end (drop MATHLIB if lake
                                       # resolves Mathlib itself; see the section below)
```

### Reproducing it

```sh
./Comparator/run.sh                        # a machine where lake resolves Mathlib itself
MATHLIB=/opt/mathlib ./Comparator/run.sh   # this VM: prebuilt, read-only Mathlib
```

[`Comparator/run.sh`](https://github.com/sgouezel/IETFree/blob/main/Comparator/run.sh) is the whole recipe in one command: it fetches and builds the two tools (comparator
at `3927ad3`, the last revision on a Lean v4.33 toolchain, with `lean4export` at its `v4.33.0` tag),
builds `Challenge` and `IETFree.ChallengeSolved` with Lake (in a project that requires Mathlib by
path when `MATHLIB` is set — on a machine where `lake exe cache get` has been run, the repository's own
Lake project already has both as targets), exports both modules and runs the comparison. It uses `landrun` if it is on `PATH` and the
comparator's own `fake-landrun.sh` otherwise (`landrun` is not installed here), and it exits 0 only
if the pair is accepted.

The run of record, on this tree, printed

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
== accepted: the challenge and the solution are the same statements, and the solution's proofs
   use only propext, Quot.sound, Classical.choice
```

and the check is not vacuous.  Two mutations of the challenge were tried: with `w ≠ 1` changed to
`w = 1` in [`main`](https://github.com/sgouezel/IETFree/blob/main/IETFree/ChallengeSolved.lean#L223), [`Check.lean`](https://github.com/sgouezel/IETFree/blob/main/Comparator/Check.lean) reports `the statement differs: main`; with `0 < v i` weakened to
`0 ≤ v i` in [`simplexRegion`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L107), it reports `differs: simplexRegion`.  [Comparator/README.md](Comparator/README.md)
explains each step.

[`Comparator/Check.lean`](https://github.com/sgouezel/IETFree/blob/main/Comparator/Check.lean) is the cheap guard: it applies the comparator's own algorithm to the two
compiled modules.  Run it after any change to [`Challenge.lean`](https://github.com/sgouezel/IETFree/blob/main/Challenge.lean), to a statement, or to a declaration
reachable from [`main`](https://github.com/sgouezel/IETFree/blob/main/IETFree/ChallengeSolved.lean#L223); [`./SlowBuild.sh`](https://github.com/sgouezel/IETFree/blob/main/SlowBuild.sh) runs it too.

## The two inputs from the literature

The paper quotes two classical theorems about interval exchange transformations — unique ergodicity
and rigidity by translations, both for almost every irreducible exchange — and the first version of
this formalization took them as hypotheses.  They are **proved**, in two campaigns that reuse the
Rauzy–Veech induction:

| literature | in Lean | where |
|---|---|---|
| **Unique ergodicity** (H. Masur, *Interval exchange transformations and measured foliations*, Ann. of Math. 115 (1982) 169–200; W. A. Veech, *Gauss measures for transformations on the space of interval exchange maps*, Ann. of Math. 115 (1982) 201–242) | [`masurVeech_ae_unique_invariant`](https://github.com/sgouezel/IETFree/blob/main/IETFree/UniqueErgodicity/MainTheorem.lean#L103): for irreducible data on `n ≥ 2` letters, a.e. length vector gives an exchange with exactly one invariant probability measure carried by `[0, 1)`; and [`masurVeech`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L60) for `mkIET1 λ π`; the uniform Birkhoff form is the theorem [`uniformBirkhoff_of_uniqueErgodic`](https://github.com/sgouezel/IETFree/blob/main/IETFree/UniqueErgodicity/IET.lean#L561) | [`IETFree/RauzyVeech/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/RauzyVeech), [`IETFree/UniqueErgodicity/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/UniqueErgodicity) (61 + 13 modules) |
| **Rigidity by translations** (Veech, *Metric theory of interval exchange transformations I*, Amer. J. Math. 106 (1984) 1331–1359, Theorem 1.4) | [`veechRigidity`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L71): a.e. length vector gives an exchange rigid by translations, in the paper's Definition 2.2 form | [`IETFree/Rigidity/`](https://github.com/sgouezel/IETFree/tree/main/IETFree/Rigidity) (10 modules) |

Both inputs are theorems of the library, stated once, in [`IETFree/Pair/Irreducible.lean`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean) besides the
Section 2 material: [`masurVeech`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L60)
and [`veechRigidity`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L71).
The Section 2–3 argument uses them the way the paper does, by applying them; no hypothesis of that
kind is left anywhere in the tree.

Everything in the paper is proved, including Proposition 2.5 (almost every pair is Diophantine),
which is a consequence of the easy direction of Khintchine–Groshev and is formalized as
[`ae_diophantine`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Diophantine.lean#L963).

Two remarks on the scope of the formalization:

* [`masurVeech`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L60) carries the hypothesis `2 ≤ d`. On a single cell the exchange is the identity for
  every length vector, and the identity is not uniquely ergodic, so the restriction is necessary;
  [`veechRigidity`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L71) does not need it (the identity is rigid by translations), and the unconditional
  theorem above has no hypothesis on the number of cells at all.
* Lemma 1.2 of the paper (an irrational rotation and an exchange do not generate a free group) is an
  illustration in the introduction and is **not** part of this development; nor is the remark
  following Theorem 1.1 (that the set of pairs is, in fact, open and of full measure).

## Correspondence between the paper and the formalization

Statement by statement: one row per entry of the `alignment` block of [`formalization.yaml`](https://github.com/sgouezel/IETFree/blob/main/formalization.yaml), in the same
order, with the same `status`; that file is the machine-readable version of this table. File names in
the third column are relative to [`IETFree/`](https://github.com/sgouezel/IETFree/tree/main/IETFree), and every `file:line` reference is a hyperlink to that
line in this tree, on [GitHub](https://github.com/sgouezel/IETFree). In the last column `proved` is
for a theorem or a lemma, `implemented` for a definition, and `not-formalized` for an item of the
paper that is not in the tree.

| paper | Lean | file:line | status |
|---|---|---|---|
| Theorem 1.1 (main theorem) | [`main`](https://github.com/sgouezel/IETFree/blob/main/IETFree/ChallengeSolved.lean#L223), unconditional | [`ChallengeSolved.lean`](https://github.com/sgouezel/IETFree/blob/main/IETFree/ChallengeSolved.lean#L223) | `proved` |
| Remark after Theorem 1.1 (the set of pairs is open and of full measure) | — | — | `not-formalized` |
| Lemma 1.2 (an irrational rotation and an interval exchange do not generate a free group) | — | — | `not-formalized` |
| Definition 2.1 (uniquely ergodic) | [`UniqueErgodic`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L992) (a unique invariant probability measure carried by `[0, 1)`; the uniform Birkhoff form is the predicate [`UniformBirkhoff`](https://github.com/sgouezel/IETFree/blob/main/IETFree/UniqueErgodicity/Basic.lean#L61), derived from it in [`uniformBirkhoff_of_uniqueErgodic`](https://github.com/sgouezel/IETFree/blob/main/IETFree/UniqueErgodicity/IET.lean#L561)) | [`IET.lean:992`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L992) | `implemented` |
| a.e. interval exchange is uniquely ergodic (Masur; Veech) | [`masurVeech`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L60), from the measure form [`masurVeech_ae_unique_invariant`](https://github.com/sgouezel/IETFree/blob/main/IETFree/UniqueErgodicity/MainTheorem.lean#L103) | [`MainTheorem.lean:103`](https://github.com/sgouezel/IETFree/blob/main/IETFree/UniqueErgodicity/MainTheorem.lean#L103) | `proved` |
| Definition 2.2 (rigid by translations) | [`IsRigidByTranslations`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L999) | [`IET.lean:999`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L999) | `implemented` |
| Proposition 2.4 (a.e. exchange is rigid by translations) | [`veechRigidity`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L71) | [`Irreducible.lean:71`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L71) | `proved` |
| Definition 2.3 (Diophantine pair) | [`IsDiophantine`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Diophantine.lean#L41) (with [`coeffMax`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Diophantine.lean#L38)) | [`Diophantine.lean:41`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Diophantine.lean#L41) | `implemented` |
| Proposition 2.5 (almost every pair is Diophantine) | [`ae_diophantine`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Diophantine.lean#L963) | [`Diophantine.lean:963`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Diophantine.lean#L963) | `proved` |
| Theorem 2.6 (the irreducible case) | [`irreducible_case`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L446) | [`Irreducible.lean:446`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L446) | `proved` |
| Lemma 2.7 (one of three commutators of two nontrivial words is nontrivial) | [`exists_nontrivial_commutator`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L99) (Mathlib's `⁅u, v⁆`, with `commutatorElement_eq_one_iff_mul_comm`) | [`Irreducible.lean:99`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L99) | `proved` |
| Lemma 2.8 (a word with support of measure at most ε) | [`exists_word_small_support`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L211) | [`Irreducible.lean:211`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L211) | `proved` |
| Lemma 2.9, display (2.2) (uniform Birkhoff bound) | [`exists_uniform_birkhoff`](https://github.com/sgouezel/IETFree/blob/main/IETFree/UniqueErgodicity/IET.lean#L582) | [`IET.lean:582`](https://github.com/sgouezel/IETFree/blob/main/IETFree/UniqueErgodicity/IET.lean#L582) | `proved` |
| Lemma 2.10 (one commutator step: the support shrinks by a factor 18ε) | [`iterate_word`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L365) (`Leb(supp w') ≤ 18 ε Leb(supp w)`) | [`Irreducible.lean:365`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Irreducible.lean#L365) | `proved` |
| Lemma 3.1 (the length map of gf is an invertible affine map) | [`compLen_injective`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/LengthMap.lean#L267) (injectivity; the other two give the absolute continuity), [`compLen_absolutelyContinuousAt`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockData.lean#L195), [`absolutelyContinuous_map_blockFree`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockAETransfer.lean#L175) | [`LengthMap.lean:267`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/LengthMap.lean#L267), [`BlockData.lean:195`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockData.lean#L195), [`BlockAETransfer.lean:175`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockAETransfer.lean#L175) | `proved` |
| splitting singularity / fixed interval / pair-splitting singularity (Section 3) | [`IETDatum.IsSplitting`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/ReductionData.lean#L192), [`IETDatum.InFixedCell`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/ReductionData.lean#L370), [`IsPairSplitting`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/ReductionData.lean#L407) | [`ReductionData.lean:192`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/ReductionData.lean#L192), [`ReductionData.lean:192`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/ReductionData.lean#L192), [`ReductionData.lean:192`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/ReductionData.lean#L192) | `implemented` |
| Lemma 3.2 (between consecutive pair-splitting singularities the permutation is irreducible) | [`block_irreducible_on_good`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockIrreducibility.lean#L1070) (the intrinsic form), [`irreduciblePerm_blockPerm`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockDatum.lean#L54) (for the explicit [`blockPerm`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockRescaling.lean#L347)) | [`BlockIrreducibility.lean:1070`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockIrreducibility.lean#L1070), [`BlockDatum.lean:54`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockDatum.lean#L54) | `proved` |
| Lemma 3.3 (a permutation fixing an initial segment of the image order) | [`perm_eq_of_preimage`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/ReductionData.lean#L496) | [`ReductionData.lean:496`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/ReductionData.lean#L496) | `proved` |
| Lemma 3.4 (a.e. a nontrivial word is trivial on a given block) | [`exists_word_trivial_on_block`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockLemma.lean#L207) | [`BlockLemma.lean:207`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockLemma.lean#L207) | `proved` |
| Theorem 1.1 in block form, and the assembly of the per-block words | [`main_theorem_of_blocks`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockLemma.lean#L233) (the a.e. statement for the data of the composition), [`exists_word_trivial_on_all_of_blocks`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockAssembly.lean#L108) | [`BlockLemma.lean:233`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockLemma.lean#L233), [`BlockAssembly.lean:108`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockAssembly.lean#L108) | `proved` |
| the open regions of Section 3, and their countable cover | [`GoodRegion`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/GoodRegion.lean#L1064) (the open region `O`, the list `s`, the permutation `ρ`, the cut and cell maps `a`, `B`), [`exists_goodRegion`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/GoodRegion.lean#L1173), [`exists_countable_goodRegion_cover`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockEndpoints.lean#L317) | [`GoodRegion.lean:1064`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/GoodRegion.lean#L1064), [`GoodRegion.lean:1064`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/GoodRegion.lean#L1064), [`BlockEndpoints.lean:317`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockEndpoints.lean#L317) | `proved` |

## Discrepancies with the paper, and why the formalization departs from it

None of these changes a statement of the paper; each is a deliberate choice of *form*, made where the
paper's prose leaves room and where the formal version is markedly easier to prove. Two of them are
statements that had to be pinned down because the first formal reading turned out to be **false**;
both were found by machine-checked counterexamples, and both were repaired towards the paper's
meaning.

**1. Open regions instead of connected components of a hyperplane complement.**
The paper fixes a connected component `O` of the complement of the finitely many hyperplanes
`k + Σ a_i λ_i + Σ b_j μ_j = 0` (with integer coefficients bounded by 4), on which the combinatorics
of `gf` is constant, and argues inside it. The formalization instead defines a [`GoodRegion`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/GoodRegion.lean#L1064) as an
*open ball* around a good parameter ([`exists_compPresentation_on_ball`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/GoodRegion.lean#L858)), on which one fixed list `s`,
one fixed permutation `ρ` and one fixed combinatorial type are known to present `gf`, and then covers
the almost-everywhere statement by a *countable* family of such balls
([`exists_countable_goodRegion_cover`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockEndpoints.lean#L317)) and `MeasureTheory.ae_all_iff`. What the paper obtains from
connectedness, the formalization obtains from continuity and compactness-free openness: no connected
component, no hyperplane, and — importantly for everything downstream — no *global* monotonicity of
the singularity list, only the pointwise form `G.cellLen hq = compLenVec G.s q (monoAt G hq)`. This is
why no preconnectedness or convexity hypothesis appears anywhere in the final development.

**2. Bad parameters through the Diophantine condition, not through hyperplanes.**
Relatedly, the paper's "except on finitely many hyperplanes" becomes `¬ IsBadParam q`
(i.e. `q ∈ goodParams`: no small integer relation `k + Σ a_i v_i + Σ b_j w_j = 0` between the free
coordinates), whose null set is proved with the same Khintchine–Groshev/Diophantine machinery as
Proposition 2.5 ([`ae_goodParams_real`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/ReductionData.lean#L788)). Reusing Proposition 2.5 is much cheaper than building a
measure-theory-of-hyperplanes API, and it gives the statement the proof actually needs (a bound, not
just nonvanishing).

**3. Explicit combinatorial data instead of "the combinatorics is constant".**
The paper says "the map `gf` is an interval exchange transformation with respect to a permutation `ρ`
which does not depend on the parameters in `O`". The formalization carries the combinatorial type as
explicit data: [`IsCompType lam π hl mu s a B`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Presentation.lean#L56) with a cut map `a : Fin (d+1) → Fin (n+1)` and a cell
map `B : Fin n → Fin e`, the singularity shape [`SingularityShape`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/GoodRegion.lean#L63), `ρ` as a field of [`GoodRegion`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/GoodRegion.lean#L1064), and
the *block* permutation as an explicit `Equiv.Perm (Fin (l - k))` ([`blockPerm π k hkl hln hstab`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockRescaling.lean#L347),
`ρ_b j = π (j+k) - k`). This is the single biggest simplification: every statement about the block is
then a statement about a concrete permutation, so the literature inputs — which quantify over
permutations — apply to it directly, with no transport along an existence statement.

**4. Lemma 3.2 stated intrinsically — and the first rendering of it was false.**
The paper concludes "the restriction to `P` of the permutation `ρ` is irreducible", i.e. that no
*proper initial piece* of the block is invariant. The first formal rendering said something weaker
and different: that no initial piece `[u, c)` is mapped into the **whole block** `[u, v)`. That is
**false** — it fails as soon as `E ∘ D` maps some `[u, c)` into `[u, v)` at all, which happens for
every pair on the block `[0, 1)` (the composition maps `[0, 1)` into itself) and, more generally,
whenever a good pair has no interior pair-splitting point. Machine-checked counterexample:
`d = e = 2`, both permutations the transposition, `λ = 1/3`, `μ = 1/4`. The repaired statement,
[`IsCompIrreducibleOn D E u v`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockIrreducibility.lean#L147), says exactly what the paper says (no invariant initial sub-block
`[u, c)` inside `[u, v)`), and [`irreduciblePerm_blockPerm`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockDatum.lean#L54) turns it into [`IsIrreduciblePerm`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L1047) of
[`blockPerm`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockRescaling.lean#L347).

**5. The datum of "`gf` is an IET" had to be pinned down the same way.**
Our first [`IsCompPresentation`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Presentation.lean#L99) required `gf` to map the `i`-th marked cell *onto the `ρ i`-th cell of
the same list* — again false (for `λ = (1/3, 2/3)` and the transposition, `f 0 = 2/3` is not a cell
start). The corrected field is the standard IET datum: `gf` translates the `i`-th cell by
[`listImageLeft ρ s i`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Presentation.lean#L74) - [`listLeftEnd s i`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/Presentation.lean#L69). The images of the cells are a *different* interval partition
of `[0,1)`, placed according to `ρ`.

**6. Unique ergodicity: the paper's definition, plus its uniform form as a theorem.**
Definition 2.1 says "the only invariant probability measure is Lebesgue", and that is what
[`UniqueErgodic f`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L992) says.  The
consequence Lemma 2.9 uses — for every continuous `ψ` the Birkhoff averages converge to
`∫ ψ d unitMeas` *uniformly on* `[0,1)`, a convergence statement with an explicit `N` — is not part
of the definition: it is the theorem
[`uniformBirkhoff_of_uniqueErgodic`](https://github.com/sgouezel/IETFree/blob/main/IETFree/UniqueErgodicity/IET.lean#L561),
and the form Lemma 2.9 states it in is [`UniformBirkhoff`](https://github.com/sgouezel/IETFree/blob/main/IETFree/UniqueErgodicity/Basic.lean#L61).

**7. Almost-everywhere statements carry the simplex membership as a binder.**
Where the paper writes "there is a full measure subset `Ω ⊆ Δ_π × Δ_σ` such that, for `(λ,μ) ∈ Ω`,
…", the formalization writes `∀ᵐ λ ∂(simplexVolume d), ∀ (h : λ ∈ simplex d), …`. The two are
equivalent, and the binder gives the proof access to the membership of the point it is reasoning
about.

**8. The measure is the pushforward of Lebesgue measure on the free coordinates.**
[`simplexVolume d`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L126) is the image of Lebesgue measure on the region `{v | v > 0, Σ v < 1}` under
[`simplexMap d`](https://github.com/sgouezel/IETFree/blob/main/IETFree/IET.lean#L118), rather than Lebesgue measure on the simplex `Δ_π` itself. Since only null sets are
ever transported, no Jacobian appears anywhere; [`absolutelyContinuous_map_rescaleSub`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/SubintervalTransfer.lean#L505),
[`compLen_absolutelyContinuousAt`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockData.lean#L195) and [`absolutelyContinuous_map_blockFree`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/BlockAETransfer.lean#L175) are absolute-continuity
statements, which is exactly what the paper's "smooth with a derivative of maximal rank" step is used
for.

**9. The one-cell block is separated out.**
In Lemma 3.4 the paper splits `r = 1` (`gf` is the identity on the block, and the word `yx` works)
from `r ≥ 2` (where Theorem 2.6 applies to the rescaled pair). The formalization does the same, and
makes the split explicit: the hypothesis `2 ≤ l - k` is carried by the branch that applies Theorem 2.6
(at `l - k = 1` the rescaled length vector is identically `1` and the rescaled exchange is the
identity, which is not uniquely ergodic), and the one-cell block is handled by an explicit word
([`genX`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/MeasureTools.lean#L111) in Lemma 3.4, [`genY`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/MeasureTools.lean#L114) * [`genX`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/MeasureTools.lean#L111) when the single cell is a cell of `g`).

**10. Commutators are Mathlib's.**
The paper writes `[a, b] = a⁻¹b⁻¹ab`, putting the inverses on the left; the formalization uses
Mathlib's `⁅a, b⁆ = a * b * a⁻¹ * b⁻¹` (`commutatorElement`, with the inverses on the right), so the
paper's commutator is `⁅a⁻¹, b⁻¹⁆`. Most of the lemmas are true in either convention and are stated
with `⁅·,·⁆` — the combinatorial Lemma 2.7, the word-length bound, the evaluation of a commutator, and
the two assembly lemmas that make a commutator trivial on a union of invariant blocks. The one place
where the direction matters is the support estimate of Lemmas 2.8–2.10: the support of `[φ, ψ]` is
contained in `A ∪ φ⁻¹A ∪ ψ⁻¹A`, with `A` the intersection of the supports, and the measure of the
`ψ⁻¹` term is controlled by the unique ergodicity of `f` (with `ψ = f^q`). There the words are written
`⁅φ⁻¹, ψ⁻¹⁆`, which is the paper's commutator, and the proofs are unchanged. The two conventions
vanish together ([`commutatorElement_inv_inv_eq_one_iff`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Pair/MeasureTools.lean#L196)), so no statement is weakened.

## License

The Lean sources carry `Copyright (c) 2026 Sébastien Gouëzel` and are released under the Apache 2.0
license, as described in [`LICENSE`](LICENSE).
