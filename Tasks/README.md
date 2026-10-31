# Statement files for the discovery runs

Each file here is self-contained: it imports only `Mathlib`, inlines the definitions its statement
needs, and ends with exactly one `theorem ... := by sorry` — the shape `discovery_start` requires.
They were used to hand single lemmas to the prover harness, and are kept as records.

| file | theorem | library declaration |
|---|---|---|
| `transl_of_locally.lean` | `IsCutSet.transl_of_locally` | `IET.lean` (run id `disp_of_locally`) |
| `cutset_comp.lean` | `IsCutSet.comp` | `IET.lean` (run id `cutset_comp`) |
| `mkiet_is_iet.lean` | `isIET_mkIETFun` | `IET.lean` (run id `mkiet_is_iet`) |
| `exists_mkiet_equiv_eq.lean` | `exists_mkIETEquiv_eq` | `IET.lean` (run id `exists_mkiet_equiv_eq`) |
| `nontrivial_commutator.lean` | `exists_nontrivial_commutator` | `Irreducible.lean` (run `nontrivial-commutator`, **stopped unsolved** after round 1; the library statement now uses Mathlib's commutator `⁅u, v⁆ = u v u⁻¹ v⁻¹` instead of the file's `commWord`, which is the paper's convention `u⁻¹v⁻¹uv` — the two statements are equivalent) |
| `continuous_domination.lean` | `exists_continuous_indicator_le` | not yet in the library (run `continuous-domination`, running) |
| `ae_diophantine.lean` | `ae_diophantine` | `Diophantine.lean` (run `ae-diophantine`, **solved and ported** as `ae_diophantine_of_mem`; the hypothesis-free `ae_diophantine` is now in the same file) |
| `centralizer_cyclic.lean` | `exists_centralizer_pow` | `Centralizer.lean` — LS 2.19, now `FreeGroup.exists_zpow_eq_of_mul_comm` (**proved**, §D8; the abstract form of this statement file has `r : FreeGroup Gen`) |
| `cyclicallyReduced_rotate.lean` | `rotate_cyclically_reduced` | `Centralizer.lean` — one-step rotation of a cyclically reduced word (run `cyclically-reduced-rotate`, **solved and ported**) |
| `singularity_bound.lean` | `exists_lattice_cuts` | `SingularityBound.lean` — cuts of a word are lattice points with coefficients `≤ |w| + 1` (run `singularity-bound-2`, **solved and ported**; the library statement is stronger: the run's unused `hTV` hypothesis is dropped, and `Match.lean` proves the frozen form from it) |
| `translation_vector_bound.lean` | `exists_lattice_displacement` | `TranslationVector.lean` — the word-length bound on the coefficients of a word's displacement (run `translation-vector-bound`, **solved and ported**; instantiated as `evalWord_sub_eq_lattice`) |
| `commensurable.lean` | `commute_of_zpow_eq` | `Commensurable.lean` — commensurable elements of a free group commute (run `commensurable-commute`, **solved and ported**; the run was stopped after its proof checked out) |
| `Match.lean` | — | the guard: proves each run's statement from the library declaration |

`Match.lean` is the check that matters: it restates, verbatim, the statement each run was given and
proves it by the corresponding library declaration. If the library statement drifts, `Match.lean`
stops compiling. It is part of `./Build.sh`.

## Renames since the runs

- `disp_of_locally` → `IsCutSet.transl_of_locally` (same statement);
- `mkiet_is_iet` → `isIET_mkIETFun` (same statement);
- `mkiet_is_iet`'s library companion `mkIETEquiv_isIET` → `isIET_mkIETEquiv`;
- `cutset_comp`: the run's statement used the cellwise preimage
  `s ∪ ((t ×ˢ insert a s).image (fun p => p.1 - (f p.2 - p.2))).filter (· ∈ Ico a b)`; the library
  now states it in the canonical form `s ∪ hf.preimage t`, which is what `Match.lean` checks;
- `exists_mkIETEquiv_eq` gained the hypothesis `a ≤ b`: without it the statement is **false**
  (`b < a` makes `IsIET a b e` hold with `e = id` while `∑ lam = b - a < 0` is impossible). The run
  was never started on the old statement.

## Id syntax

`discovery_start` requires a problem id matching `^[a-z0-9_]{1,64}$`, so a future run cannot use
these theorem names (they contain dots and capitals). Rename the target theorem to a snake_case id
and keep the statement body byte-identical.

## Note on statement files with helper lemmas

`discovery_start` accepts only **one** declaration in the frozen source: a file containing helper
`theorem`s (even proved ones) is refused with "the frozen file's theorem must be named `<id>`".  The
target must also be at top level, since a theorem inside `namespace FreeGroup` is exported as
`FreeGroup.<id>`.  Put the route (and any facts one wants to hand over) in the module docstring.

## Linter noise in this directory

These files are **frozen records of the exact sources handed to the discovery runs** (they import only
`Mathlib` and end in `:= by sorry`), so they are deliberately left byte-identical and are *not*
compiled by `Build.sh` — only `Match.lean` is, and that one is lint-clean.  If you include `Tasks/` in a
library build with `set_option linter.mathlibStandardSet true`, you will get `sorry` and unused-binder
warnings here; that is the record, not the library.  `Match.lean` is what guarantees that the
statements in these files still agree with the library.
