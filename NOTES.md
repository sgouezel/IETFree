# Working notes: findings that the next session must not rediscover

Status snapshots and hard facts about the development. Keep this file short and factual;
it is not a report.

**Read §State first.**  It is the only section below that describes the tree *as it is now*; everything
after it is a session log, so a sentence such as "what is missing is …" describes the day it was
written, not the current state.  §"Deleted declarations (reconciliation)" maps the names that have
since disappeared, and the audit entries at the end record why.

## State

**This section is the only part of this file that describes the tree as it is now.**  Everything below
it is a session log, written in the order the work was done: it records what was true *then*, and many
of the declarations it names have since been deleted or renamed.  The section right after this one,
"Deleted declarations (reconciliation)", maps every name that no longer exists to its replacement (or
says it was dropped), so an old entry can still be read.

### Build and axiom status

- **Packaging rule (owner's standing instruction):** `IET2.zip` is the *sources only* — no `Tasks/`
  (that directory no longer exists, but keep the exclusion), no `.lake/`, no `.scratch/`, no
  `*.olean`.  Recipe (also in §"Prose `file:line` links, `Tasks/` dropped"):
  `zip -r -q IET2.zip IET2 -x 'IET2/.lake/*' 'IET2/.scratch/*' 'IET2/Tasks/*' '*.olean'`, run from the
  repository root.
- **The repository** is <https://github.com/sgouezel/IETFree> (`main`); it holds the contents of
  `IET2/` at its *root*, so module paths there are `IETFree/…`, not `IET2/IETFree/…`.  `Tasks/` no
  longer exists, in the repository or in this tree (the owner deleted it; see the last entry).  `README.md`
  links every declaration it names to the line that declares it (§"README links every declaration"
  at the end).  The command-line recipes below are the ones of *this* VM.
- **Both builds are green and warning-free**: `lake build` (the genuine Lake project) succeeds from a
  clean `.lake` — 8740 jobs, exit 0, **no warnings** — and `./Build.sh` (plain `lean`, same options)
  also prints no warning.  §"The linter warnings are all gone" at the end of this file records what
  that took.  The **declaration** linters (Mathlib's `runLinter`, which `lake build` does not run) are
  clean too: 0 findings (§"The declaration linters are clean").  `./Build.sh` reports
  `declarations still depending on sorryAx: 6`: three in the **display-only** file `Challenge` (the
  definition hole `mkIETEquiv`, `coe_mkIETEquiv`, and the unconditional `main`), and three in the
  comparator challenge `ChallengeWeak.lean` (the same three, with the two hypotheses).  The library
  itself has **none**: it carries a **single axiom check**, `#print axioms main`, registered directly
  below `main` in `ChallengeWeakSolved.lean`, which reports
  `[propext, Classical.choice, Quot.sound]` (§"`Check.lean` replaced by a single axiom check").
  `Comparator/Check.lean`, the local stand-in for the comparator, passes (32661 declarations
  compared, no difference).
- **All of the paper's Section 3 is proved**: Lemma 3.1 (`compLen_injective` plus the absolute
  continuity `compLenAffine_absolutelyContinuousAt`/`compLen_absolutelyContinuousAt`), Lemma 3.2
  (`block_irreducible_on_good`, `irreduciblePerm_blockPerm`), Lemma 3.4
  (`exists_word_trivial_on_block`, over the countable cover of good regions) and Theorem 1.1
  (`main_theorem_of_blocks`, with the per-block words assembled into one word by
  `exists_word_trivial_on_all_of_blocks`).  Section 2 is complete as well (Lemmas 2.7–2.10,
  Theorem 2.6 `irreducible_case`, Proposition 2.5 `ae_diophantine`) — Theorem 1.1 is proved from the
  paper's two external inputs, `MasurVeech` and `VeechRigidity`, which stay as hypotheses — and so is
  the centralizer route
  (`Centralizer.lean`: P2–P4, P7, `exists_zpow_eq_of_forall_commute`, `norm_pow_eq`, LS 2.19 as
  `exists_zpow_eq_of_mul_comm`).
- The frozen interfaces: `Challenge.lean` (display only, `import Mathlib` only, imported by nothing)
  and, inside `IET.lean`, the block `leftEnd` … `coe_mkIETEquiv`, whose definitions it mirrors.  Since
  the sixth design, `Challenge.lean` no longer states `mkIETFun_inv_left`: like `ChallengeWeak.lean` it
  has `mkIETEquiv := sorry` and the statement `coe_mkIETEquiv` instead, and its declarations are at the
  root namespace.  `IET.lean` still proves `mkIETFun_inv_left` (the library needs it); the mirroring is
  now of the definitions, not of the inverse lemma.

### Module layout — 29 modules under `IET2/IETFree/` and the two statement files above it, 19 120 lines

- `Challenge.lean`, `ChallengeWeak.lean` (one directory above `IETFree/`, modules `Challenge` and
  `ChallengeWeak`) — the two statement files: display only and the comparator challenge.  Nothing
  imports them, so their `sorry`s do not pollute any axiom report.  `IETFree/ChallengeWeakSolved.lean`
  is the solution: it proves the challenge's `main` and uses the library's `coe_mkIETEquiv`, importing
  only library modules.
- `Comparator/Check.lean`, `Comparator/README.md` (outside `IETFree/`) — the local stand-in for the
  comparator and the description of the pair.  The challenge is `ChallengeWeak.lean` itself
  (one file, `import Mathlib` only) and the solution is `IETFree/ChallengeWeakSolved.lean` plus the
  library's `mkIETEquiv`; `comparator.json` names `coe_mkIETEquiv` and `main` as theorem targets and
  `mkIETEquiv` as a *definition hole*.  See the last entry, "The comparator challenge, fourth design".
  The files of the third design (`Comparator/Challenge.lean`, `Comparator/gen.sh`, the directory
  `Comparator/Challenge/`) have been deleted.
- `CutSet`, `CutSetMeasure`, `IET` — cut sets and their measure; `IsIET`, the explicit construction
  (`mkIETFun`, `mkIETEquiv`, `mkIET1`), `leftEnd`/`upperEnd`/`imageLeft`/`translationVector`/`idx`,
  `Positive` (positivity of a length vector), the simplex as a measure space
  (`simplexRegion`/`simplexMap`/`simplexVolume`), the classification `exists_mkIETEquiv_eq`, and the
  group `IET a b`.
- `Diophantine` — `simplex`, `simplexVolume`'s support, `coeffMax`, `IsDiophantine` and its
  closure properties (`of_int_combination`), Proposition 2.5 (`ae_diophantine`).
- `Commensurable`, `MeasureTools`, `TranslationVector`, `SingularityBound`, `Centralizer`,
  `Irreducible` — the Section 2 layer: root uniqueness, `unitMeas` and words in two generators
  (`evalWord`, `evalWordEquiv`), the translation-vector bound, the singularity bound, the centralizer,
  and `UniqueErgodic`/`IsRigidByTranslations`/`IsIrreduciblePerm`/`MasurVeech`/`VeechRigidity` with
  Lemmas 2.7–2.10 and Theorem 2.6.
- `ReductionData`, `Presentation`, `IntegerAffine`, `SingularityList`, `GoodRegion`, `LengthMap`,
  `SubintervalTransfer` — the local analysis of `g ∘ f`: `IETDatum`, `IsCompPresentation`/`IsCompType`,
  integer-affine functions of the parameters, the marked list `s` and `SingularityShape`, `GoodRegion`
  (with `BlockIdx`, `Block`, `Fits`, the fields `pres`/`type` — `G.pres q hq`, `G.type q hq` —
  `cellLen`, `cellLen_pos`, `blockLam`),
  Lemma 3.1, and the transfer of null sets to a rescaled sub-interval.
- `BlockRescaling`, `GeneratorChange`, `InvariantInterval`, `BlockEndpoints`,
  `BlockAETransfer`, `BlockDiophantine`, `BlockData`, `BlockIrreducibility`, `BlockAssembly`,
  `BlockDatum`, `BlockLemma` — the block development: the rescaled block
  (`blockMass`/`blockLam`/`blockPerm`), the change of generators and the transport of a word, the
  restriction of `g` to an invariant interval, the block endpoints and the parameter measure, the a.e.
  transfer (`BlockGood`, `ae_blockGood`, `BlockGoodAt`, `ae_BlockGoodPt`), the Diophantine transfer
  (`isDiophantine_blockPair`), the irreducibility on a block (`block_irreducible_on_good`), the
  assembly of the per-block words into one, `GoodRegion.blockOf`/`blockPermOf`/`blockRescaled`/
  `comp_conj_rescale`/`restrict_rescale`, and A4 (`exists_word_trivial_of_region`) with Lemma 3.4 and
  Theorem 1.1.
- `Reduction` — the umbrella module, with the narrative docstring that explains the reduction;
  `Check` — the `#print axioms` report.

### Conventions that the code now follows

- **Everything is pointwise.**  A `GoodRegion` gives the strict monotonicity of its list only on the
  open set `O`, so there is no global `hmono` and no `compLenVecOf`: the length vector of the
  composition at a point is `G.cellLen hq` (= `compLenVec G.s q (monoAt G hq)`), the block length
  vector is `G.blockLam hq k hkl hln`, and the a.e. statements are `∀ B : Block G` over a countable
  type rather than over `Finset.range` enumerations.
- **The repeated tuples are structures**: a block is a `GoodRegion.Block` (`k`, `l`, `hkl`, `hln`,
  `hstab`, with `lam`, `perm`), a pair of data fitting a point is
  `GoodRegion.Fits q D E` (`D.π = π`, `D.v = q.1`, `E.π = σ`, `E.v = q.2`), and the positivity of a
  length vector is `Positive lam`.  The bare index tuple of a block is `BlockIdx n` (in `IET.lean`):
  it carries `hkl`/`hln` and *derives* the instance `NeZero (I.l - I.k)`, so no statement about a block
  has to take that instance as a binder; `I.kFin : Fin n` is `k` as an index, an `abbrev` so that
  rewrites and `exact` see through it (a regular `def` does not unfold during rewrite matching).
- **`Build.sh` has two hand-maintained lists** — the module loop and the `cat` of per-module logs — so
  a new module needs an entry in both, or the `sorry` count silently under-reports.
- `IET2/NOTES.md` is a log, not a specification: the declarations in `IETFree/` are the truth.

## Deleted declarations (reconciliation)

The audit of the repeated arguments (five items, entries below: "Audit of the repeated arguments:
items 1 and 2", "Audit item 3", "Audit item 4", "Audit item 5", "The 75 unused declarations are
deleted") removed 107 declarations.  Nothing below this point should be read as saying they exist.
Where a statement survived in another shape, the right-hand column has it; the rest were dropped, and
the whole pre-deletion tree is in `IET2/.scratch/bak/audit-item6/` (`audit-item0/` … `audit-item5/`
hold the earlier stages).

Module *names* changed too: every `Section3*.lean` named in the entries below has been renamed — the
correspondence is the table in "File layout: no more `Section3` in file names; four files split", near
the end of this file — and the current module list and build order are in §State above.  Two files
under `Comparator/` went the same way: `Comparator/Solution.lean` is **deleted** (the comparator's
solution is the library), and `Comparator/Challenge.lean` with the folder `Comparator/Challenge/`
(copies of six library modules) is dead too; the challenge is now `ChallengeWeak.lean` itself.
The entries "The comparator challenge", "…, redesigned" and "…, third design" describe the three
abandoned designs.

| gone | now |
|---|---|
| `compLenVecOf` | `compLenVec` at a point, abbreviated `G.cellLen hq` |
| `compLenVec_eq_compLenVecOf`, `compLenVecAt_eq_compLenVec`, `compLenVec_eq_compLenVecAt` | — (the global and pointwise vectors are now one object) |
| `compLenVecAt` | `compLenVec` |
| `compLenVecAt_eq_simplexMap` | `compLenVec_eq_simplexMap` |
| `compLenVecAt_pos`, `compLenVec_pos`, `pos_compLenVec` | `G.cellLen_pos hq` |
| `compLenVec_sum`, `sum_compLenVec` | `G.cellLen_sum hq` |
| `GoodRegion.compLen_eq_simplexMap` | `compLenVec_eq_simplexMap` |
| `GoodRegion.compLenAffine_mem_region` | `compLenAffine_mem_regionAt` |
| `GoodRegion.compLenAffine_absolutelyContinuous` | `compLenAffine_absolutelyContinuousAt` |
| `GoodRegion.compLen_absolutelyContinuous` | `compLen_absolutelyContinuousAt` |
| `ae_of_ae_compLen` | `ae_of_ae_of_absolutelyContinuous` (kept), fed with `compLen_absolutelyContinuousAt` inside `ae_block_of_ae_simplexVolume` |
| `ae_uniqueErgodic_blockLam`, `ae_isRigidByTranslations_blockLam`, `ae_uniqueErgodic_blockLam_of_compLenVec_pos`, `ae_isRigidByTranslations_blockLam_of_compLenVec_pos`, `ae_uniqueErgodic_blockLam_apply`, `ae_isRigidByTranslations_blockLam_apply` | `BlockGood`, `ae_blockGood_free`, `ae_blockGood` |
| `ae_blockGood_allStab`, `ae_blockGood_range` | `ae_blockGood` (over `∀ B : Block G`, via `Countable (Block G)` and `MeasureTheory.ae_all_iff`) |
| `blockLam_compLenVec_eq` | `blockLamAt_eq` |
| `mkIET1_congr` | — (proof irrelevance makes the proof argument of `mkIET1` irrelevant) |
| `GoodRegion.rescaleSub_compLenAffine`, `rescaleSub_eq_blockLam` | — |
| `GoodRegion.exists_isIntAffine_trunc` | `exists_isIntAffine_truncatedLengths` |
| `exists_isIntAffine_blockLen` | — (the block data come from `IsIntAffine (G.s i)` via `isDiophantine_blockPair`) |
| `isDiophantine_blockLam` | `isDiophantine_blockPair` (`BlockLemma`) |
| `SumForm`, `sumForm_zero`, `sumForm_one`, `sumForm_cutAffineRight`, `sumForm_upperEndAffineRight`, `sumForm_cutAffine`, `sumForm_imageLeftAffine`, `sumForm_preimageCutAffine`, `leftEnd_simplexMap_coeff`, `upperEnd_simplexMap_coeff`, `eq_on_of_eq_at`, `le_of_lt_of_sumForm`, `le_or_le_of_sumForm`, `exists_sumForm_s`, `sSum`, `isIntAffine_sSum`, `sumForm_sSum`, `sSum_spec`, `isIntAffine_upperEndAffineRight` | `IsIntAffine`, `IsDiophantine.of_intAffine_family` (that route was the superseded formalisation of the same paper step) |
| `IsCutSet.lengths_coe`, `IsCutSet.cellStarts_eq`, `IsCutSet.cell_eq` | — (`IsCutSet.sum_lengths`, `leftEnd_lengths`, `imageLeft_lengths` remain) |
| `IsCompPresentation.toIsCutSet` | — |
| `ae_irreduciblePerm_blockPerm` | — (A4 calls `isIrreduciblePerm_blockPermOf` directly) |
| `IETDatum.ofMem_π`, `IETDatum.ofMem_v` | — |

Dropped with no replacement (unused; the entries below describe how each came to be):
`exists_isCutSet_of`, `not_separated_iff`, `ae_mem_simplex`,
`take_length_flatten_replicate`, `volume_Ico_zero_one`, `unitMeas_univ_Ico`, `IET.unitMeas_preimage_pow`,
`IsFiniteUnionIntervals.biUnion`, `freeGroup_lift_natural`, `mkIETFun_sub_eq_lattice`,
`evalWord_sub_eq_lattice`, `invLetter_invLetter`, `invRev_singleton`,
`isReduced_append_iff`, `isReduced_append`, `mk_ne_one_of_isReduced`, `IETDatum.isSplitting_zero`,
`IETDatum.isSplitting_last`, `measurable_paramAffine`, `lt_iff_lt_of_ne`,
`lt_or_gt_of_ne_of_convex_affine`, `exists_ball_isIntAffine_truncatedLength`,
`exists_ball_subset_goodParams`, `cellLen_last`, `rescaleFun_comp`, `evalWordEquiv_conj`,
`mark_eq_markedList`, `listLeftEnd_sub`, `rho_convex_of_image_Ico`, `lamNat_of_le`,
`RescaleBlock.imageLeft_blockPerm`, `substGen_apply`, `clamp_le`, `le_clamp`, `clamp_mono`,
`clamp_of_le`, `mkIET1_restrict_invariant_image`, `mkIET1_inv_one`, `sum_blockLen_simplexMap`,
`cellLen_apply`, `blockLam_apply`, `BlockIdx.lam_apply`, `BlockIdx.mass_def`, `BlockIdx.mass_pos`,
`BlockIdx.len`, `BlockIdx.mass`,
`Block.perm_def`, `paramMeasure_absolutelyContinuous`, `ae_of_ae_map_of_measurable`,
`isIntAffine_gLenAffine`, `GoodRegion.truncatedLengths_eq`, `exists_isCutSet_comp`, `comp_mapsTo`,
`exists_cut_below`, `BlockGood.congr_lam`, `blockGoodPt_of_mem`, `mkIET1_fin_one`,
`leftEnd_ne_leftEnd_of_good`, `idx_rescaleMap` (both the root and the `RescaleBlock` copy),
`RescaleBlock.leftEnd_blockLam`, `lt_or_gt_of_ne_of_convex`, `lt_or_gt_of_ne_of_convex_intAffine`,
`Convex.exists_isIntAffine_max`, `Convex.exists_isIntAffine_min`,
`Convex.exists_isIntAffine_posPart`, `Convex.exists_isIntAffine_truncatedLength`,
`lt_or_gt_of_ne_of_isPreconnected`, `IsIntAffine.continuous`, `sign_congr`,
`listImageLeft_sub_of_Icc`, `leftEnd_add_blockMass_le_total`, `idx_mem_block`,
`translationVector_fin_one`, `pos_of_pos`, `sign_const`, `lamNat_nonneg` (the duplicate of
`sum_range_lamNat_nonneg`), `leftEnd_blockMass`, `GoodRegion.presAt`, `GoodRegion.typeAt`,
`GoodRegion.s_mono` (`G.pres q hq` / `G.type q hq` / `monoAt G hq` replace them).

Kept on purpose although nothing in the library uses them: `mem_markCuts`,
`ite_one_sub_ite_one_eq_zero`, `isBadParam_swap`, `continuous_toReal`, `IET.coeHom_apply` (dot
notation or `simp` uses), and `exists_continuous_indicator_le`, which is the statement of the
discovery run `continuous-domination` in `Tasks/`, not library code.

## The centralizer route now in use (replaces P5b/P6/P8 of the old blueprint)

Two shortcuts carry the whole theorem; both are proved in `Centralizer.lean` Part D.

1. **A free group that is abelian is cyclic** (`exists_zpow_eq_of_forall_commute`).  Take a basis
   `b : ι → G` with `G ≃* FreeGroup ι` (`IsFreeGroup.nonempty_basis`); if `G` is abelian then any two
   generators of `FreeGroup ι` commute, and `of x * of y ≠ of y * of x` for `x ≠ y`
   (`of_mul_of_ne`, from `reduce.sound` on two reduced words), so `ι` is a subsingleton; a free group
   on a subsingleton is generated by one element (`exists_zpow_eq_of_subsingleton`, by
   `FreeGroup.induction_on`).  Applied to the subgroup generated by two *commuting* elements
   (`Subgroup.closure {u, w}` is abelian because `centralizer (closure s) = centralizer s` and `u`, `w`
   lie in `centralizer {u, w}`) this gives **P7 directly** (`exists_common_zpow`): commuting
   nontrivial elements are powers of a common element — with no cyclic-word theory at all.
2. **The norm of a power** (`norm_zpow_eq`): for `m ≠ 0`,
   `norm (q ^ m) = 2 * (conjugator q.toWord).length + m.natAbs * (reduceCyclically q.toWord).length`,
   from `toWord_pow` and `reduceCyclically.reduce_flatten_replicate`.  With the norm triangle
   inequality this gives **`natAbs_eq_of_conj_zpow`**: if `g * q ^ m * g⁻¹ = q ^ n` with `m, n ≠ 0`
   and `q ≠ 1` then `m.natAbs = n.natAbs` (the `k`-scaling trick: compare the norms of `q ^ (m k)` and
   `q ^ (n k)` at `k = 2 * norm g + 1`).

**Commensurability** (`commute_of_zpow_eq`: `z ^ m = s ^ q`, `m, n ≠ 0` ⟹ `z * s = s * z`) came out
of the run `commensurable-commute` (`Tasks/commensurable.lean`; the proof is now
`Commensurable.lean`, no `sorry`, axiom-clean).  With it, `exists_common_zpow` upgrades commutativity
to a common root, and LS 2.19 is the maximal-root argument of §7 of the blueprint and *nothing else*:
`exists_common_zpow_of_zpow_eq` (commensurable ⟹ common root), `exists_nat_pow_or_inv_of_zpow`
(a nonzero integral power is a positive natural power of `s` or of `s⁻¹`),
`exists_zpow_eq_of_mul_comm` (`C(v) = ⟨q₀⟩` for the maximal root `q₀` of `v`; the root set is the
finite set `S = (range (norm v + 1)).filter (fun k => ∃ q, v = q ^ k)` and `S.max'` is the maximal
exponent, bounded by P3).  All three are in `Centralizer.lean` §D6–§D8, proved.

**Lemma 2.7 needs no cyclic length and no "conjugate to inverse" theory** either.  If `u`,
`genX⁻¹ * u * genX` and `genY⁻¹ * u * genY` all commute with `v ≠ 1`, they lie in `C(v) = ⟨r⟩`; write
`u = r ^ a`, `genX⁻¹ * u * genX = r ^ b` with `a ≠ 0`; `natAbs_eq_of_conj_zpow` gives `a.natAbs =
b.natAbs`, so `r ^ b = u ^ ±1`, hence `genX ^ 2 * u = u * genX ^ 2`; likewise for `genY`; then
`C(u) = ⟨r'⟩` makes `genX ^ 2` and `genY ^ 2` commute, contradicting `pow_two_mul_pow_two_of_ne`
(`genX ≠ genY`, again `reduce.sound` on two reduced words).  This is `exists_nontrivial_commutator`
in `Irreducible.lean`, proved (no `sorry`); with it `iterate_word` (Lemma 2.10) became axiom-clean.

## Lemma 2.9 (`exists_uniform_birkhoff`): closure + Urysohn, no re-presentation of `S`

The earlier plan (Finding 1 below) proposed replacing the cut-set presentation by a *pair-based*
one and working with disjoint pieces.  That is not needed: the proof now in `Irreducible.lean` goes
through the closure, where overlapping pieces cost nothing.

1. `P := (cuts ×ˢ cuts).filter (·.1 < ·.2)` gives `S = ⋃ p ∈ P, Ico p.1 p.2` (immediate from
   `IsFiniteUnionIntervals`), and `T := S ∩ Ico 0 1 = ⋃ p ∈ P, Ico (max p.1 0) (min p.2 1)`.
   Only `T` matters, since `unitMeas` is supported on `[0,1)`: `unitMeas.real S = volume.real T`.
2. `closure T ⊆ ⋃ p ∈ P, Icc (max p.1 0) (min p.2 1)` (that finite union of closed intervals is
   closed and contains `T`), and `closure T \ T ⊆ ⋃ p ∈ P, {min p.2 1}` — the right endpoints, since
   a point of `Icc a b` that is not in `Ico a b` must be `b`.  So `volume (closure T) ≤ volume T`
   (finite union of singletons is null: `measure_biUnion_finset_le`), which is the step that
   overlapping pieces would have broken.
3. `volume (closure T) ≠ ⊤` follows from that bound (`volume T ≤ volume (Ico 0 1) = 1`), so
   `MeasurableSet.exists_isOpen_sdiff_lt` (the `diff` name is deprecated in this Mathlib) gives an
   open `U ⊇ closure T` with `volume (U \ closure T) < ofReal (ε/2)`, hence
   `volume.real U ≤ volume.real (closure T) + ε/2`.
4. `exists_continuous_zero_one_of_isClosed` applied to `Uᶜ` and `closure T` gives
   `ψ : C(ℝ,ℝ)` with `ψ = 0` off `U`, `ψ = 1` on `closure T`, `0 ≤ ψ ≤ 1`.  Then `1_S ≤ ψ` on
   `[0,1)` and `∫ ψ ∂unitMeas ≤ unitMeas.real U ≤ volume.real U ≤ unitMeas.real S + ε/2`.
5. `UniqueErgodic f ψ` at tolerance `ε/2`, then compare the two Birkhoff sums pointwise (iterates of
   `x ∈ [0,1)` stay in `[0,1)`).

Gotchas met: `Set.EqOn ψ 1 s` gives `ψ x = 1 x`, so `Pi.one_apply`/`Pi.zero_apply` must be used;
`measure_union_le` needs `(μ := volume)` because `volume` is not otherwise determined;
`closure_Ico` wants `a ≠ b` (so the identity `closure (Ico a b) = Icc a b` is false at `a = b` —
avoid it and use only the *inclusion* of the closure into the closed inflation).

## Lemma 2.10 (`iterate_word`): how the proof goes

Pieces, all in `Irreducible.lean` now:

- `measurableSet_wordSupp`, `unitMeas_real_nonneg`, `supp_conj` (support of `θ⁻¹hθ` is `θ⁻¹` of the
  support), `wordSupp_conj_pow`, `commWord_supp_subset` + `unitMeas_real_supp_commWord_le`: the
  paper's `supp[φ,ψ] ⊆ A ∪ φ⁻¹A ∪ ψ⁻¹A` and `Leb supp[φ,ψ] ≤ 3 Leb(A)`.
- `sum_inter_le`: the averaged Birkhoff estimate. **Real analysis, not bookkeeping**: restrict
  `unitMeas` to `A`, write `μ(A ∩ f^{-i}S₀)` as `∫ (f^i)⁻¹S₀.indicator 1 ∂(unitMeas.restrict A)`
  (`integral_indicator_one`), pull the finite sum inside the integral (`integral_finsetSum`), bound
  a.e. by `2εN` using the hypothesis (the a.e. statement that points off `[0,1)` are null for the
  restricted measure is `hνnull`), then `integral_const`. Local API names in this Mathlib:
  `integral_finsetSum`, `integrable_finsetSum` (camelCase), `Measure.real` has no API (unfold it
  with `rw [Measure.real]`), `div_le_div_iff₀`, `Set.indicator_of_notMem`, `ENNReal.natCast_ne_top`.
- `exists_small_intersection`: display (2.3), by averaging over `i < N` for `S`, `f⁻¹S`, `g⁻¹S`.
- The word: `v = x^{-i} w₀ x^i` (`v ≠ 1`, `|v| ≤ |w₀| + 2i`), then Lemma 2.7 on `(w, v)`. The three
  cases give `[w,v]`, `[x⁻¹wx, v]`, `[y⁻¹wy, v]`; lengths `2|w| + 2|v|` and `2(|w|+2) + 2|v|`, both
  `≤ 2|w| + 4N + 2|w₀|` because `i < N`.  Length lemmas: `wordLength_commWord_le`,
  `wordLength_conj_le_of` (any letter of length one), `wordLength_conj_pow_le`,
  `wordLength_genX_pow` — note `wordLength` **is** `FreeGroup.norm` definitionally, so state goals
  with `show … FreeGroup.norm …` before `omega` (otherwise `omega` treats them as different atoms).
- `_hε` and `_hsmall` are unused in this step (they belong to the standing assumptions).

## The measure-theory layer in `IET.lean` (after `Equiv.IsIET.tiling_disjoint`)

`IsCutSet.exists_mem_cell`, `cells_union`, `cellPos_le_cellStarts`, `cells_disjoint`,
`Equiv.IsIET.image_cells_union`, `image_preimage_inter`, `volume_image_add`,
`volume_inter_eq_sum`, `preimage_inter_cell`, `volume_preimage_cell`,
`Equiv.IsIET.measure_preimage` (**an exchange preserves Lebesgue measure on `[a, b)`**),
`eq_add_sum_indicator`, `IsCutSet.measurable`. At the end of the file: `IET.measurable`,
`IET.symm_apply_apply`, `IET.apply_symm_apply'`, `IET.mul_apply`, `IET.one_apply`
(all `@[simp]`).

`Irreducible.lean`, after `unitMeas_le_one`: `IET.measurable_pow`, `IET.unitMeas_preimage`,
`IET.unitMeas_real_preimage`, `IET.unitMeas_preimage_pow`, `unitMeas_ne_top`,
`unitMeas_real_mono`, `unitMeas_real_union_le`, `unitMeas_real_biUnion_finset_le`,
`unitMeas_real_compl`, `unitMeas_real_Icc_le`.

Note: `Measure.real` has **no** API lemmas in this Mathlib snapshot (only `real_def`), so every
statement about `unitMeas.real` goes through `ENNReal.toReal_*` by hand.

## Lemma 2.8 (`exists_word_small_support`): how the proof goes

Read `hBμ`/`ht`/`hq` simultaneously to get one `n` with `q n ≥ 1`, `|t n| ≤ δ` and
`unitMeas.real (B n) ≥ 1 - ε/3`, where `δ = ε / (6 (#S_g + 1))` and `S_g` is a cut set of `g`.
Take `w = [y, x^{q n}]` and

`U = {x | Separated S_g x (x + t n)}`,

the set of `x` for which a cut separates `x` from `x + t n`. Then
`supp w ⊆ (B n)ᶜ ∪ U ∪ g ⁻¹' (B n)ᶜ`: on the complement `f^{q n} x = x + t`, `¬ Separated` gives
`g (x + t) = g x + t` by `IsCutSet.transl_of_not_separated` (both points lie in `[0, 1)` since
iterates stay there), and `g x ∈ B n` gives `(f^{q n})⁻¹ (g x + t) = g x`. Measure:
`≤ ε/3 + ε/3 + ε/3`, using `unitMeas_real_compl`,
`U ⊆ ⋃ c ∈ S_g, Icc (c - |t|) (c + |t|)` (each of measure `≤ 2|t|`), and
`IET.unitMeas_real_preimage` for `g ⁻¹' (B n)ᶜ`.

Nontriviality of the word: **no centralizer theorem needed**. The representation
`F_2 →* Equiv.Perm ℝ`, `x ↦ (t ↦ t + 1)`, `y ↦ (t ↦ 2t)` (`shiftPerm`, `scalePerm`), sends
`[y, x^q]` to `t ↦ t + q/2` (`commWord_genY_genX_pow_ne_one`). This does **not** generalise to
Lemma 2.7, which is about all words.

## Finding 1 (SUPERSEDED — see "`IsFiniteUnionIntervals` was redefined" below): *cut-set* presentation

`IsFiniteUnionIntervals S` says: `∃ cuts, ∀ x, x ∈ S ↔ ∃ a ∈ cuts, ∃ b ∈ cuts, a < b ∧ x ∈ Ico a b`.
So the "pieces" are *all pairs* of cuts, and they may overlap: `cuts = {0, 1/2, 1}` presents
`[0, 1)` with three pieces of total length `2`. Consequences:

- summing tent functions over the pairs is wrong, not merely awkward;
- `S ∩ Ico 0 1` (which Lemma 2.9 needs, since `unitMeas` only sees `[0, 1)`) is a finite union of
  half-open intervals but **not** of that form with the cut set `insert 0 (insert 1 cuts)`: with
  `cuts = {1/4, 1/2}` and `x = 1/10`, the pair `(0, 1)` would wrongly claim `x ∈ S ∩ Ico 0 1`.

For Lemma 2.9 use a **pair-based** presentation (`S = ⋃ p ∈ P, Ico p.1 p.2`, immediate from the
cut-set form) and intersect pairs: `Ico a b ∩ Ico c d = Ico (max a c) (min b d)`. Either redefine
`IsFiniteUnionIntervals` in pair form (the paper only says "finite union of intervals", so both are
faithful) or keep the cut-set interface and add a lemma producing the pair presentation.

## Finding 2: `block_invariant_irreducible` (Lemma 3.2) — fixed, one conjunct left then; **Lemma 3.2 is now fully proved** (`block_irreducible_on_good`, `irreduciblePerm_blockPerm`) and `block_invariant_irreducible` itself is gone

**The old statement was false.**  It used `IsFixedNear g x` ("`g` is the identity near `x`") for
"`x` lies in the interior of a fixed interval for `g`".  Counterexample (both maps three-interval
exchanges): `g` with cells `[0,2/5)`, `[2/5,3/5)`, `[3/5,1)` and permutation `(1 3)(2)` (so
`g(7/10) = 1/10`), `f` with cells `[0,1/2)`, `[1/2,3/4)`, `[3/4,1)` and permutation `(1)(2 3)`.
Then `IsBlock f g (1/2) 1` held but `7/10 ∈ [1/2,1)` mapped to `1/10 ∉ [1/2,1)`.

**What is implemented now.**  `InvariantBelow f x := ∀ y ∈ [0,1), y < x → f y < x`
(`[0,x)` invariant), `InvariantAbove f x := ∀ y ∈ [0,1), x ≤ y → x ≤ f y` (`[x,1)` invariant), and

```lean
def SplitsAt (f : IET 0 1) (x : ℝ) : Prop := InvariantBelow f x ∧ InvariantAbove f x
def IsPairSplitting (f g : IET 0 1) (x : ℝ) : Prop :=
  x = 0 ∨ x = 1 ∨ ((IsSplitting f x ∨ IsSplitting g x) ∧ SplitsAt f x ∧ SplitsAt g x)
```

This is the paper's derived property of a pair-splitting singularity ("then `[0,x)` and `[x,1)` are
invariant under both `f` and `g`"); deriving it from the `σ`-conditions needs the frozen permutation
presentation.  The three invariance conjuncts of Lemma 3.2 are now **proved**; the fourth
(`IsIrreducibleOn (g * f) u v`) is still `sorry`.

**Why both halves and not just `InvariantBelow`.**  I first recommended the one-sided
`InvariantBelow` alone.  That is *not* enough to conclude `[x,1)` invariance, and the missing step is
not cheap: from `f '' ([0,x) ∩ [0,1)) ⊆ [0,x)` and measure preservation one gets equality only up
to a null set, and upgrading that to a pointwise statement needs "a finite union of half-open
intervals whose complement in `[0,x)` is null is everything" — a real lemma about the cells, which
is not formalised.  (Note `IsSplitting f x` gives only `InvariantBelow f x`.)  If someone wants to
drop `InvariantAbove` from the definition, that lemma is the thing to prove first.

## Lemma 2.7 (`exists_nontrivial_commutator`): **PROVED** (kept for the record of what blocked it)

The paper's proof is: all three commutators trivial ⟹ `u`, `x⁻¹ux`, `y⁻¹uy` all lie in the
centralizer of `v`, which is **cyclic by Lyndon–Schupp Prop. 2.19**; conjugates have equal cyclically
reduced length so `x⁻¹ux = u^{±1}`; `u` is not conjugate to `u⁻¹` (again LS 2.19), so `x⁻¹ux = u`, and
likewise for `y`; then `⟨x,y⟩ = F₂` sits in the cyclic group `C(u)`, impossible since `y ∉ ⟨x⟩`.

The deep input is **`C(v)` cyclic for `v ≠ 1`**; Mathlib has nothing about centralizers or commuting
elements in free groups, and no tree actions.  The representation trick that proves Lemma 2.8's word
nontrivial is useless here: it decides one *fixed* word, while Lemma 2.7 quantifies over all `u`, `v`.
A hand proof is a substantial standalone development (cyclic words up to rotation + a free-monoid
commutation induction + conjugator bookkeeping); estimate several hundred to ~1500 lines.

Verified facts about what Mathlib *does* give (checked in Lean):
* `IsMulTorsionFree (FreeGroup α)` with `pow_left_injective : n ≠ 0 → a ^ n = b ^ n → a = b`;
* `subgroupIsFreeOfIsFree` (Nielsen–Schreier) — so once `C(v)` is known abelian it is cyclic;
* `reduceCyclically`, `conjugator`, `conj_conjugator_reduceCyclically`, `reduce_flatten_replicate`
  (the reduced word of `w ^ n` for cyclically reduced `w`);
* note: "joint injectivity" (`a ^ m = b ^ n → a = b`) does **not** follow from `pow_left_injective`
  by an lcm trick — the exponents come out different — so root uniqueness is *also* part of LS 2.19.

`Tasks/centralizer_cyclic.lean` holds the isolated crux statement, and **`Centralizer.lean` holds the
full blueprint** for proving it (reference: Bogopolski §2.2–2.4 Prop. 3, i.e. LS 2.19): the lemmas
`P2` (powers of cyclically reduced words), `P3` (root bound), `P4` (free-monoid commutation),
`P5` (conjugates of cyclically reduced words are cyclic permutations), `P6` (**crux**: commuting
cyclically reduced words), `P7` (commuting ⟹ common power), `P8` (maximal root, `C(g) = C(q₀)`),
`P9` (the target), plus §8 on what Lemma 2.7 additionally needs (`Q1` cyclic length of powers,
`Q2` no element is conjugate to its inverse — with a complete argument, `Q3` `F₂` is not cyclic,
`Q4` the assembly).  The blueprint file is compiled by `Build.sh` and has no declarations yet.

## Discovery runs

- `nontrivial-commutator` (`exists_nontrivial_commutator`, Lemma 2.7) — **stopped** after round 1
  unsolved (the worker was building cyclic-word / `IsFreeGroup` machinery). Mathlib has no
  centralizer theorem for free groups; this is the one genuinely hard input left in Section 2.
- `continuous-domination` (`exists_continuous_indicator_le`) — **solved** (state `done`). The lemma
  is no longer needed: Lemma 2.9 is proved directly by the closure route. The proof is in
  `runs/continuous-domination/exists_continuous_indicator_le/` if someone wants to port it as a
  standalone Mathlib-style lemma.
- `ae-diophantine` (`ae_diophantine`, Proposition 2.5) — **solved and ported**: the proof is
  `Diophantine.lean` (from worker `t000002`, 926 lines, no `sorry`); `Tasks/Match.lean` checks the
  run's statement against it, and `ae_diophantine` is axiom-clean.
- Statement files: `Tasks/nontrivial_commutator.lean`, `Tasks/continuous_domination.lean`,
  `Tasks/ae_diophantine.lean`, `Tasks/centralizer_cyclic.lean`. `Tasks/Match.lean` has entries for
  `transl_of_locally`, `cutset_comp`, `mkiet_is_iet`, `exists_mkiet_equiv_eq` and `ae_diophantine`.

## `IsFiniteUnionIntervals` was redefined (pair form) — and why

The old definition took a finite set `cuts` and quantified over **all** pairs `a < b` of cuts:
`∃ cuts, ∀ x, x ∈ S ↔ ∃ a ∈ cuts, ∃ b ∈ cuts, a < b ∧ x ∈ Ico a b`.  That is strictly weaker than a
finite union of intervals: the union of *all* `[a, b)` with `a, b ∈ cuts` is exactly the single
interval `[min cuts, max cuts)`, so a support made of *some* of the cells of an exchange could not be
presented in that form (and `exists_uniform_birkhoff` was only ever applied to such single intervals).
The definition in `MeasureTools.lean` is now the pair-based one,

`∃ P : Finset (ℝ × ℝ), ∀ x, x ∈ S ↔ ∃ p ∈ P, x ∈ Set.Ico p.1 p.2`,

which is closed under finite unions (`IsFiniteUnionIntervals.biUnion`) and is what the cells of an
exchange give.  `exists_uniform_birkhoff`'s statement is unchanged (same predicate name, genuine
finite unions now) and its proof needed only its first three lines changed.  When the support is
presented directly by the cells of `evalWord w f g`, `IsFiniteUnionIntervals.biUnion` applies with
`a i := cellPos i`, `b i := cellPos (i+1)`.

## Theorem 2.6 (`irreducible_case`): **PROVED** (axiom-clean; this section is the road there)

The three prerequisites, in the order they are used:

1. `IsFiniteUnionIntervals (wordSupp w f g)` — `isFiniteUnionIntervals_ne_id`
   (`MeasureTools.lean`): if `h : IET 0 1` translates between points not separated by a finite
   `C ∋ 0, 1`, then `{x | h x ≠ x}` is a finite union of `[a, b)` with `a, b ∈ C`.  The presentation
   is explicit: the pairs `(c₁, c₂)` of elements of `C` that are consecutive and satisfy
   `h c₁ - c₁ ≠ 0`.  Two points in the *left-closed* cell `[c₁, c₂)` are never separated (the right
   endpoint is excluded), so they share the displacement of `c₁`.
   The instance for the paper's exchanges is `isFiniteUnionIntervals_wordSupp`
   (`SingularityBound.lean`), by `evalWord_cuts` with `C = insert 0 (insert 1 C₀)` — the
   `Ioc`-convention structure of the singularity bound *suffices* for the left-closed cells, so no
   second induction was needed.
2. **Singularities are lattice points with bounded coefficients**: `SingularityBound.lean`.
   The run `singularity-bound-2` proved the abstract statement (`CutBound.exists_lattice_cuts`): for
   two piecewise-translation permutations of `ℝ` with finite cut sets whose pieces have constant,
   lattice-valued displacement (coefficients in `{-1,0,1}`) and whose cuts are lattice points, there is
   a finite `C` cutting `w(f, g)` into translation pieces, all of whose elements are lattice
   combinations with coefficients `≤ |w| + 1`.  Two findings from the port:
   * the run's statement carried the translation-vector bound `hTV` as a hypothesis, but the proof
     never uses it (preimages of cuts are always taken under a *single* letter), so the library
     statement is stronger and does not mention `hTV`;
   * `Tasks/Match.lean` proves the frozen (with-`hTV`) statement from the stronger one.
   The instantiation for the paper's exchanges is `evalWord_cuts` (cut set `ietCuts lam =
   insert 1 (cellCuts lam)`; `cellCuts` omits `1`, across which the displacement is *not* constant).
   Note `mkIET1 lam π` does **not** fix `0` in general (the first cell maps to the interval starting at
   `∑_{π j < π 0} λ_j`), so arguments must not assume `h 0 = 0`.
   The cell-length lemma `exists_lattice_cell` is proved: a nontrivial `w(f, g)` has a translation
   interval whose length is a nonzero lattice combination with coefficients `≤ 2|w| + 2` and at most
   `unitMeas.real (wordSupp w f g)`.  **Half-open subtlety** (cost two hours): with the `Ioc`
   convention the pieces are `(cᵢ, cᵢ₊₁]`, so a moved point may itself be a cut; the right choice is
   `c₁ = max {c ∈ C : c ≤ x}` and `c₂ = min {c ∈ C : x < c}`, for which every `y ∈ (c₁, c₂)` is
   *unseparated* from `x` (the strict variants leave a cut at the endpoint and the `¬CutSep` hypothesis
   of the singularity bound does not apply).
3. The iteration, in `irreducible_case` itself (proof ported from `.scratch/try/irr3.lean`):
   `ε := 1 / (4 * 18 * 2 ^ c)` so that `18 ε 2 ^ c = 1/4 < 1`; Lemma 2.8 gives `w₀ ≠ 1` with
   `Leb (supp w₀) ≤ ε`; Lemma 2.9 gives `N`; `K := 4N + 2|w₀|`; `next` is the `iterate_word` choice
   (with the junk value `w₀` at `w = 1`, so that `next` is total and `next_spec` is available for
   `w ≠ 1`), `W := next^[·] w₀`.  Then `|W n| + K ≤ 2^n (|w₀| + K)` and
   `Leb (supp (W n)) ≤ ε (18ε)^n`, and `W n ≠ 1` by induction (this is the free-group nontriviality,
   *not* triviality of `W n(f,g)`).
   For the contradiction fix `n` from `exists_pow_lt_of_lt_one` with
   `(18ε 2^c)^n < C / (ε M₀^c 2^c)`, `M₀ = |w₀| + K + 1`, and suppose no `W n(f,g)` is the identity.
   `exists_lattice_cell` gives `ℓ` with `0 < ℓ ≤ ε (18ε)^n` and coefficients `≤ 2|W n| + 2`, so with
   `T := max (coeffMax a) (coeffMax b)` (`T ≥ 1` because `ℓ ≠ 0`)
   `C ≤ ℓ T^c ≤ ε (18ε)^n (2|W n| + 2)^c ≤ ε (18ε)^n (2^{n+1} M₀)^c`
   `= ε M₀^c 2^c (18ε 2^c)^n < C`.  The bound `2|W n| + 2 ≤ 2^{n+1} M₀` uses `2 ≤ 2^{n+1}`.
   Three Lean-specific points that cost time here:
   * the identity `((2:ℝ) ^ (n+1)) ^ c = ((2:ℝ) ^ c) ^ (n+1)` is NOT `Real.rpow_mul` (whose
     direction is `x ^ (y*z) = (x^y)^z`): use `← Real.rpow_natCast_mul hx (n+1) c` and
     `← Real.rpow_mul_natCast hx c (n+1)`, then `mul_comm`;
   * for the final regrouping `ε (18ε)^n ((2^c)^{n+1} M₀^c) = (ε M₀^c 2^c) (18ε 2^c)^n`, `rw` in the
     *forward* direction `mul_pow (18ε) (2^c) n` on the right-hand side, then `pow_succ`, then `ring`
     (which does treat variable-exponent powers as atoms);
   * `set L : ℕ := wordLength (W n)` is a trap: after `set`, `rw [hLdef]` fails to rewrite because the
     elaborated occurrence is the local definition itself.  Write the term out.  And `coeffMax` has to
     be unfolded explicitly (`rw [coeffMax]`) before a `Finset.univ.sup`-level rewrite applies.

Then `exists_nontrivial_commutator` (Lemma 2.7) is what makes the three candidate words in the last
brick of Lemma 2.10 nontrivial; it is proved.

## Section 3 interface (`Section3.lean`, approved and landed)

*(The interface described here was carried out: `Section3.lean` is now `Reduction.lean`, and the
modules it grew into are listed in §State.  The `IsCompPresentation` field names below are still
accurate; the hypotheses of that interface have since been thinned, see the audit entries at the
end.)*

The paper's Section 3, in the order the reduction runs.

- **`O`**: `IsBadParam p` says there is a nontrivial relation `k + ∑ aᵢλᵢ + ∑ bⱼμⱼ = 0` with all
  coefficients bounded by **2** (the paper takes `4`; the user chose `2`, and `2` is exactly what the
  case analysis of Lemma 3.2 needs, since its relations have coefficients in `{-1,0,1}`).  Two proved
  consequences: `coeffs_eq_of_good` (two relations with coefficients bounded by `1` that agree are
  equal — the difference is a small relation) and `coeffs_zero_of_good` (a relation with coefficients
  bounded by `2` that vanishes is trivial; this is the form needed after the paper's Case 1b adds two
  relations, where a collected coefficient can reach `2`).
- **The presentation** `IsCompPresentation lam π mu σ hl hm n s ρ`: `s : Fin (n+1) → ℝ` is the
  increasing list of singularities of `g ∘ f` with `s 0 = 0`, `s (last) = 1`, and `g ∘ f` translates
  the cell `[s i, s (i+1))` onto the `ρ i`-th cell.  `compLen` is the induced length vector (so its
  affineness needs no proof; the content is that one `s`, `ρ` serves a whole region).  `IsAffineFn`
  uses Mathlib's `AffineMap ℝ ((Fin d → ℝ) × (Fin e → ℝ)) ℝ` on the ambient real space, because
  `ℝ≥0` is not a vector space, and `IsAffineFn.measurable` comes from continuity.
- **`GoodRegion`**: an *open* `O ∋ p₀` with `O ⊆ goodParams`, a fixed `n, s, ρ` of affine functions
  presenting `g ∘ f` at every point of `O`.  `ae_exists_goodRegion` says a.e. parameter pair has one.
  This is the form Section 3 needs: Masur–Veech and Veech's rigidity are applied to `mkIET1 ν ρ` for
  one *fixed* `ρ`, so the region, not just an `s` at each point, must be produced.
- **Lemma 3.1**: split into `compLen_injective` (on `O`, the length vector determines `(λ, μ)`) and
  `compLen_absolutelyContinuous` (`(map of the parameter measure).map ν ≪ simplexVolume n`), consumed
  through the proved `ae_of_ae_compLen`.
- **The covering step** `measure_zero_of_forall_exists_isOpen_null` (proved): if every point of `s` has
  an open neighbourhood `O` with `μ (O ∩ bad) = 0`, then `μ (s ∩ bad) = 0` — in a second-countable
  space the countably many basis elements inside good neighbourhoods cover `s`.  This is how
  `ae_exists_goodRegion` + `ae_goodParams` will combine into "the bad set is null".

**`O` was wrong once: the free coordinates are essential.** The first version of `IsBadParam` used all
`d + e` lengths.  That is degenerate: the relation `-1 + ∑ᵢ λᵢ = 0` has coefficients `1` and constant
`-1`, all bounded by `2`, and holds on the whole simplex, so *every* parameter pair is bad and
`ae_goodParams` is false.  `IsBadParam` now uses the **free** coordinates (`redIdx d i`, i.e.
`λ₁, …, λ_{d-1}` and `μ₁, …, μ_{e-1}`), which is the paper's own convention (`i = 1, …, d-1`); with
them a nonzero coefficient vector gives a genuine hyperplane.  The same degeneracy made the old
`coeffs_eq_of_good` false (its counterexample is the difference of two relations being a multiple of
`∑λ = 1`), and it is true again in free coordinates.

## `IET.lean` refactor (this round): `a` is a cut, and every cut set is `mkIET` data

Done on request, in four parts; `IET.lean` compiles clean under `linter.mathlibStandardSet`.

1. **`IsCutSet` now has `a_mem : a ∈ s`.**  Consequence: `IsCutSet.lt : a < b`, so a cut set can only
   exist on a nonempty interval.  Hence `IsIET` had to be relaxed to
   `def IsIET (a b : ℝ) (f : ℝ → ℝ) : Prop := (∀ x, f x = x) ∨ ∃ s, IsCutSet f a b s`, with
   `IsIET.exists_isCutSet (h) (hab : a < b)` (identity case: `{a}`) and
   `IsIET.eq_id_of_le (h) (hba : b ≤ a)`.  This is what keeps `IsIET.id a b`, `IET.id` and the
   `Group (IET a b)` instance total on empty intervals.
2. **`cellLeft` no longer takes a `Nonempty` proof.**  It is now
   `hs.cellLeft (x) (hx : x ∈ Set.Ico a b)`, and `cellLeft_mem`, `cellLeft_mem_Ico`, `cellLeft_le`,
   `le_cellLeft`, `not_separated_cellLeft`, `cellLeft_eq` are its API.  `IsCutSet.map_eq_cell` became
   a two-line proof, and all 11 `((insert a s).filter (fun c => c ≤ x)).Nonempty` constructions are
   gone.
3. **`insert a s` → `s` throughout** (104 occurrences): `cellStarts`, `cellPos`, `cellLen`,
   `imageStarts = s.image f`, `cellPerm : Equiv.Perm (Fin s.card)`.  The now-redundant hypotheses
   went with it: `hlt : a < b` from `cellStarts_mem_Ico`, `cellPos_le`, `cellStarts_lt_cellPos`,
   `image_cell`, `image_cell_le`, `image_cell_disjoint`, `imageStarts_subset`, `image_union`,
   `sum_cellLen_image`, `cells_union`, `image_cells_union`, `preimage_inter_cell`,
   `volume_preimage_cell`, `measure_preimage`, `eq_add_sum_indicator`; and `hne : 0 < s.card` from
   `cellStarts_zero` and `sum_cellLen_lt` (it is `IsCutSet.card_pos`).  `imageStarts_subset`,
   `cellStarts_mem_Ico` and `finite_preimage` became one-liners.
4. **Any cut set gives `mkIET` data** (new section "The exchange attached to a cut set"):
   `IsCutSet.lengths : Fin s.card → ℝ≥0`, `IsCutSet.perm` (= `cellPerm`), and
   `sum_lengths`, `lengths_coe`, `leftEnd_lengths` (= `sum_cellLen_lt`), `cellStarts_eq`,
   `imageLeft_lengths` (= `sum_cellLen_image`), `translationVector_lengths`, `cell_eq`
   (`[cellStarts i, cellPos (i+1)) = [a + leftEnd ν i, a + leftEnd ν i + ν i)`), and the two
   representation theorems **`IsCutSet.eq_mkIETFun`** (`∀ x, ⇑e x = mkIETFun hs.lengths
   (hs.perm e.injective) a x`) and **`IsCutSet.eq_mkIETEquiv`**.  Both are stated for
   `⇑e` with `e : Equiv ℝ ℝ` (the `imageLeft_lengths` half needs `e.symm`), and take
   `[NeZero s.card]`, which callers get from `hs.card_pos`.  `exists_mkIETEquiv_eq` is now four
   lines: the empty case from `eq_id_of_le`, the general one from `lengths`/`perm`/`eq_mkIETFun`.

**Downstream was fixed by adding the `IsIET` API instead of case splits at each site**:
`IsIET.eq_of_notMem`, `IsIET.apply_eq_self_of_lt`, `IsIET.apply_eq_self_of_le`, `IsIET.mapsTo` (all
proved through `eq_id_of_le`/`exists_isCutSet`).  With them, `obtain ⟨s, hs⟩ := f.isIET` became
`(f.isIET.mapsTo hy).1`, `f.isIET.eq_of_notMem hx`, or `f.isIET.exists_isCutSet zero_lt_one` where the
cut set itself was needed (`MeasureTools.IET.unitMeas_preimage`, `exists_word_small_support`).  The
tree is green again: 12 `sorryAx`, as before the refactor.

**Small Lean traps met here** (worth not rediscovering): `Finset.max' s _` on a *filter* needs the
filter given explicitly (`Finset.max'_mem (s.filter p) _`), otherwise `LinearOrder` is stuck on a
metavariable; `rw [h]` where `h`'s left side occurs *inside a lambda* of the goal rewrites the
lambda body (use `Finset.mem_image.mpr ⟨0, _, _⟩` instead); `← sub_eq_zero`-style rewriting with a
`set` abbreviation (`hT : T = ∑ …`) does not fire under `linarith`, so state the arithmetic fact with
explicit `have`s.

**`compLen_injective`: the marked reshape (done) and what is left.**

The first version of `IsCompPresentation` only said that `g ∘ f` translates each `s`-cell, and with
that `compLen_injective` is **false**: for `d = e = 2`, `π = σ` the transposition,
`p = (3/10, 1/10)`, `q = (1/10, 3/10)`, both good with bound `2`, give the *same* `g ∘ f` (the
two-interval exchange with cut `2/5`, since `λ₁ + μ₁ = 2/5` for both), presented by the coarser
`s = (0, 1/5, 1)` with `n = 2 ≠ d + e - 1`.

`IsCompPresentation` now carries the **marked** list, as the paper's `ν` requires:

* `f_transl : ∀ i, ∃ δ, ∀ x ∈ [s i, s i+1), f x = x + δ` (the list refines the partition of `f`);
* `g_transl : ∀ i, ∃ δ, ∀ x ∈ [s i, s i+1), g (f x) = f x + δ` (it also refines the preimage of the
  partition of `g`);
* `card_eq : n = d + e - 1`.

Related fact worth keeping: a singularity of `f` need **not** be a discontinuity of `g ∘ f` (`g` maps
`0` and `1` to the same point, so the jump of `f` at a cell boundary can be cancelled); the paper's
"the singularity set of `gf` is `S_f ∪ f⁻¹ S_g`" is about the marked set, not the discontinuities.

With the reshape, no counterexample survives: a search over all good pairs on a `30 × 30` rational
grid for `d = e = 2` (596 good pairs, 332 marked sets: same marked set and same `g ∘ f` never
happens), and for `d = e = 2` there is a hand proof — the marked set is `{λ, λ+μ}` when `λ+μ < 1` and
`{λ, λ+μ-1}` when `λ+μ > 1`, so it carries `λ` and the sum, hence `(λ, μ)`.

What the general proof still needs: on each marked cell `t i := s (ρ i) - s i` is fixed by the data
and splits as `δ i + γ i`; the content is that on `O` the split is unique.  The tools are there —
`coeffs_zero_of_good` gives `λᵢ ≠ λ_j` (a relation `λᵢ - λ_j = 0` has coefficients in `{-1,0,1}`),
hence the displacement of `f` really does jump at every cut of `f` and the cuts of `f` are exactly
the jump points of `δ` — but relating the two splits needs the case analysis of the paper's Lemma 3.2.
Note the bound `2` is enough here: the bound-`4` relations `1 - 3λ₁ - 4μ₁`, `1 - 4λ₁ - 3μ₁` from the
coarse counterexample are not needed once `s` is the marked list.

**The extracted core: `O` acts on relations among *all* the lengths.** `coeffs_eq_of_good` and
`coeffs_zero_of_good` are about the *free* coordinates, but Lemma 3.2's case analysis produces
relations among all `d + e` lengths (`Σ_{i ∈ A} λᵢ + Σ_{j ∈ B} μⱼ = Σ_{i ∈ A'} λᵢ + Σ_{j ∈ B'} μⱼ`).
The bridge is

```lean
theorem relation_of_good {p} (hp : ¬ IsBadParam p) {a : Fin d → ℤ} {b : Fin e → ℤ}
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ j, |b j| ≤ 1) (hl : p.1 ∈ simplex d) (hm : p.2 ∈ simplex e)
    (h : ∑ aᵢ λᵢ + ∑ bⱼ μⱼ = 0) :
    (∀ i, a i = a (lastIdx d)) ∧ (∀ j, b j = b (lastIdx e)) ∧ a (lastIdx d) + b (lastIdx e) = 0
```

— a homogeneous relation with coefficients in `{-1,0,1}` on a good pair forces the coefficient
function to be **constant** (with the two constants cancelling).  Its consequences are what both
Lemma 3.2 and the injectivity need: `λᵢ ≠ λ_j` for `i ≠ j` (apply it to `eᵢ - e_j`: all coefficients
equal would give `1 = -1`), so the displacement of `f` really does jump at every cut of `f`; and
"each coefficient is `0`" for a relation between two sums, which is how the four cases of Lemma 3.2
close.  Ingredients: `sum_eq_last_add_free` (split `∑_{Fin d}` into the last coordinate and the free
ones using `∑ λ = 1`), `coeffs_zero_of_good'` (the vanishing form *with* the constant term), and
`Fin.sum_univ_castSucc` — note its summand order is `∑ + last`, not `last + ∑`, so a `ring` is needed
after it, and one must substitute `d = m + 1` before it applies at all.

**`ae_goodParams` reuses Proposition 2.5's machinery.** `Diophantine.lean` already contains the whole
apparatus: `ubox`, `simplexRegion`, `formBox p q N` (the finitely many integer forms with coefficients
bounded by `N`), `tube p q N x` (the `(N+1)^(-expo p q)`-neighbourhood of the zero set of `x`) and
`ae_eventually_notMem_badSet` (Borel–Cantelli: a.e. free point is outside `badSet N` for all large
`N`).  The proof of `ae_goodParams` is then three steps: `(simplexVolume d).prod (simplexVolume e)` is
the pushforward of `(volume.restrict (simplexRegion d)).prod (volume.restrict …)` under
`Prod.map (simplexMap d) (simplexMap e)` (`Measure.map_prod_map`); `ae_map_iff` moves the a.e.
statement to the free coordinates (the good set is open, hence measurable); and
`isBadParam_mem_badSet` turns a bad pair at the simplex point `simplexMap d z.1, simplexMap e z.2` into
`z ∈ badSet (d-1) (e-1) N` (via `simplexMap_redIdx` and `Real.coe_toNNReal`).  Note `formBox`'s
elements are `(Fin p → ℤ) × ((Fin q → ℤ) × ℤ)` — right-associated — and `eventually_atTop` gives
`∃ a, ∀ b ≥ a`, not `∃ a, a ≤ b ∧`.

## The assembly and the reduction, restated on `IsBlock`; Lemma 3.2 reduced

**`IsPairSplitting.invariant`** (proved): a pair-splitting point is two-sidedly invariant for *both*
maps — the `x = 0` and `x = 1` cases are the convention and `[0,1)`-invariance, the other two are
`pairSplitting_invariant` (and its mirror image, obtained by swapping `D` and `E`).
**`IsPairSplitting.iff_mem`** (proved) turns that into the assembly's hypothesis: for `u`, `v`
pair-splitting and `y ∈ [0,1)`, `u ≤ y ∧ y < v ↔ u ≤ F y ∧ F y < v` — the "mapped onto itself"
condition.  Both `[propext, Classical.choice, Quot.sound]`.

Restated (statements only):

* `exists_word_trivial_on_all_of_blocks (D E) (u v : Fin n → ℝ)` — the assembly, unchanged in shape
  but on data: a cover by intervals mapped onto themselves and carrying words gives one word
  trivial on `[0,1)`, hence `evalWord w D.toIET E.toIET = 1`.
* `main_theorem_of_blocks (π σ) (hMV) (hVR)` — the reduction, in free coordinates: a.e. `z ∈
  simplexRegion d × simplexRegion e`, for all data with those lengths and permutations, the
  enumeration `u v` of the pair-splitting points exists with the invariance and per-block words.

**Lemma 3.2 is now reduced to one geometric lemma** — `block_irreducible_on_good` is *proved* from

```lean
theorem exists_pairSplitting_of_invariant (D E) (hp : ¬ IsBadParam (D.v, E.v)) (huc : u < c)
    (hcv : c < v) (hinv : ∀ x ∈ Ico 0 1, u ≤ x → x < c → E.toFun (D.toFun x) ∈ Ico u v) :
    ∃ x, IsPairSplitting D E x ∧ u < x ∧ x < v
```

as `hb.2.2.2 x hx hux hxv` (the maximality clause of `IsBlock`).  The docstring of
`exists_pairSplitting_of_invariant` records the paper's four cases and what each needs
(`relation_of_good` to kill the length relation, then the combinatorial reading of `gfx`).  That
lemma is the real work left in Lemma 3.2.

## The splitting invariance, proved

The paper's "if a splitting singularity `x` of `f` lies in a fixed interval for `g`, then `[0,x)` and
`[x,1)` are invariant under both" is now **proved** (`[propext, Classical.choice, Quot.sound]`):

```lean
theorem IETDatum.isSplitting_below  (hk : D.IsSplitting k) (hy : y ∈ Ico 0 1) (hyk : y < D.mark k) :
    D.toFun y < D.mark k
theorem IETDatum.isSplitting_above  (hk : D.IsSplitting k) (hy : y ∈ Ico 0 1) (hyk : D.mark k ≤ y) :
    D.mark k ≤ D.toFun y
theorem pairSplitting_invariant (hk : D.IsSplitting k) (hfix : D.InFixedCell E k) :
    (both D-parts) ∧ (both E-parts)
```

Ingredients, all new: `IETDatum.mark_zero`, `mark_last`, `mark_castSucc`/`mark_succ`
(`mark i.castSucc = leftEnd` and `mark i.succ = upperEnd`, the latter by induction on the filter),
`mark_mono`, `sum_lam` (`∑ λ = 1`), and `imageLeft_add`
(`imageLeft π lam i + λ i = ∑_{j : π j ≤ π i} λⱼ`).

The two steps of `isSplitting_below`: the cell `i` of `y` satisfies `i < k` (otherwise
`mark k ≤ leftEnd i ≤ y`), so `π i < k` and the whole image cell is below `mark k`
(`imageLeft_add` + `Finset.sum_le_sum_of_subset_of_nonneg` against the filter defining `mark k`);
`isSplitting_above` is the mirror image.  `pairSplitting_invariant` then splits on whether `y` is
left of the fixed cell, inside it (where `E` is the identity by `isFixedCell_apply`), or right of it.

**Restated** (statements only, `sorry`): `IsIrreducibleOn` (on a function `ℝ → ℝ`),
`block_irreducible_on_good` (Lemma 3.2, on `(D E : IETDatum)` with `hp : ¬ IsBadParam (D.v, E.v)` and
`hb : IsBlock D E u v`), and `exists_word_trivial_on_block` (Lemma 3.4, in free coordinates: a.e. `z`
in `simplexRegion d × simplexRegion e`, every pair of data with those lengths and permutations, and
every block).  `main_theorem_of_blocks`, the assembly and `main_theorem` are still not restated.

## The block notions: restarted from the paper's combinatorial definitions

The previous `IsSplitting`/`InvariantBelow`/`InvariantAbove`/`SplitsAt`/`IsPairSplitting` (and
everything downstream: `IsBlock`, `block_invariant`, `block_irreducible_on_good`, the assembly, the
old Lemma 3.4 and `main_theorem`) were **deleted**.  They took a marked set `S` on the side, which is
redundant once the exchange is given by its data, and they were phrased analytically ("`f` maps
`[0,x)` into itself") instead of combinatorially.

The new section "The combinatorial definitions of the paper" (all on `IETDatum`, no extra
parameters):

```lean
noncomputable def IETDatum.mark (D) (k : Fin (n+1)) : ℝ       -- ∑_{i<k} λᵢ ; 0 at k = 0, 1 at k = n
def IETDatum.IsSplitting (D) (k : Fin (n+1)) : Prop           -- π {i | i < k} = {i | i < k}
@[simp] theorem IETDatum.isSplitting_zero / isSplitting_last  -- 0 and 1 are splitting by convention
def IETDatum.IsFixedCell (D) (l : Fin n) : Prop               -- both ends l and l+1 splitting
theorem IETDatum.isFixedCell_apply                              -- D is the identity on a fixed cell
def IETDatum.InFixedCell (D) (E) (k : Fin (d+1)) : Prop        -- marked point inside a fixed cell of E
def IsPairSplitting (D) (E) (x : ℝ) : Prop                    -- 0, 1, or a splitting singularity of one
                                                             -- lying in a fixed cell of the other
def IsBlock (D) (E) (u v : ℝ) : Prop                          -- consecutive pair-splitting points
```

`isFixedCell_apply` is the paper's "then `g` acts as the identity on `J_ℓ`", proved: both ends
splitting give `π l = l`, hence `imageLeft = leftEnd` and the displacement on the cell vanishes.

Naming: `IETDatum.leftEnd` was renamed `IETDatum.mark` — as `IETDatum.leftEnd` it *shadowed* the root
`leftEnd` (from `IET.lean`) inside the `IETDatum` namespace, which broke `rw`/name resolution in the
very proofs that mix both.

**Not restated yet** (they were deleted with the old notions, and their old statements were the
wrong ones): Lemma 3.2 (`block_irreducible_on_good`), Lemma 3.4, the assembly, `main_theorem_of_blocks`
and `main_theorem` (Theorem 1.1).  They must be restated in terms of `IsBlock`/`IsPairSplitting` above
before they are proved.  That is why the `sorryAx` count fell to **5** (`Challenge.lean` 2 and
`Section3.lean` 3: `exists_compPresentation_on_region`, `compLen_injective`,
`compLen_absolutelyContinuous`) — it is a drop in *statements*, not progress on proofs.

## Section 3 now carries the *data*, not `IET 0 1`

`IET 0 1` no longer occurs as an input anywhere in `Section3.lean` (only `IETDatum.toIET`, a derived
definition needed by `evalWord`, and prose).  The carrier is

```lean
structure IETDatum (n : ℕ) [NeZero n] where
  π : Equiv.Perm (Fin n)
  v : Fin (n - 1) → ℝ
  mem_region : v ∈ simplexRegion n        -- the free lengths, as a point of the region
```

`simplexRegion n` is reused rather than restated: it is the set whose `simplexMap`-image is
`simplexVolume n`, so a datum is literally a point of the measure space.  `D.pos` and
`D.sum_lt_one` are lemmas (`D.mem_region.1`, `.2`), and `IETDatum.ofMem π hv` builds a datum from a
point of the region — the way data arise almost everywhere.

No projections are added on top of the fields: `D.v` *is* the point of the free region (an earlier
`IETDatum.toPReal := D.v` was deleted), and a pair of data is used as `(D.v, E.v) : PReal d e`
directly.

with `D.lam := simplexMap n D.v`, `D.mem_simplex` (from `simplexMap_mem_simplex`), `D.toFun :=
mkIETFun D.lam D.π 0`, `D.toIET := mkIET1 D.lam D.π D.mem_simplex`, and the API `mapsTo`,
`eq_of_notMem` (identity outside `[0,1)`).  A *pair* of data is literally a point of `PReal`
(`(D.v, E.v)`), which is why `IsBadParam (D.v, E.v)` typechecks with no conversion.

Everything in the block layer moved to it:

```lean
def InvariantBelow {n} [NeZero n] (D : IETDatum n) (x : ℝ) : Prop
def InvariantAbove / SplitsAt (D : IETDatum n) (x : ℝ)
def IsSplitting (S : Finset ℝ) (D : IETDatum n) (x : ℝ)
def IsPairSplitting (S) (D : IETDatum d) (E : IETDatum e) (x : ℝ)
def IsBlock (S) (D : IETDatum d) (E : IETDatum e) (u v : ℝ)
def IsIrreducibleOn (F : ℝ → ℝ) (u v : ℝ)      -- a *function*, since g∘f is not a datum
def IsIrreducibleIET (D : IETDatum n) : Prop
```

`block_invariant`, `blocks_strongly_invariant`, `IsPairSplitting.splits_left/right` are re-proved in
this form; `not_irreducibleOn_one` is now `¬ IsIrreducibleOn (fun x => x) 0 1`.
`block_irreducible_on_good` and `exists_word_trivial_on_block` are restated on `(D, E)` (the good
condition is `¬ IsBadParam (D.v, E.v)`), and `exists_word_trivial_on_all_of_blocks` on data too.

**`main_theorem` is stated again in `mkIET1` form and is `sorry`** (10 `sorryAx` now, was 9): the
assembly is in datum form and `IETDatum` requires *strict* positivity of the free lengths, which a
point of the simplex need not have — only a.e. one.  Passing from the datum form to the `mkIET1` form
therefore needs the a.e. positivity of the coordinates (i.e. `simplexRegion`), which is not yet
formalised.  Two ways out: (a) prove `∀ᵐ p, ∀ i, 0 < p.1 i ∧ 0 < p.2 j` (From `simplexVolume`'s
construction, straightforward but not done), or (b) state the assembly for the bare functions and
keep the conclusion `∀ x ∈ Ico 0 1, …` with the final `IET` identity obtained from "identity on
`[0,1)` and outside".  (a) is the cleaner one and also gives the datum needed by
`exists_word_trivial_on_block`.

## `O` moved to the free coordinates; the splitting notions made representation-dependent

**`IsBadParam`/`goodParams` now live on `PReal`**, the space of the `d + e - 2` free coordinates, and
`IsBadParamReal`/`isBadParam_iff` (the "transport to the pair") are gone.  Consequently:

* `coeffs_eq_of_good`, `coeffs_zero_of_good`, `coeffs_zero_of_good'`, `isBadParam_iff`,
  `isClosed_badParam`, `isOpen_goodParams` are all stated on `q : PReal d e` — `isOpen_goodParams` is
  now one line (`isClosed_badParam.isOpen_compl`), with no `toReal` in sight;
* the a.e. statement is `ae_goodParams : ∀ᵐ p ∂((simplexVolume d).prod (simplexVolume e)),
  ¬ IsBadParam (toReal p)`, and its proof needs the new `toReal_simplexMap`
  (`toReal (simplexMap d v, simplexMap e w) = (v, w)` for positive coordinates) to see that a bad pair
  at the simplex point *is* a bad point of `PReal`;
* `GoodRegion.subset_good` is `∀ p ∈ O, toReal p ∈ goodParams d e` and
  `exists_ball_subset_goodParams` became a one-liner: a ball **in `PReal`** around `toReal p` lies in
  `goodParams`, since `O` is now open there.

**The splitting notions now carry the marked set.**  `IsSplitting`, `IsPairSplitting` and `IsBlock`
take a `Finset ℝ` (the marked points) as their first argument:

```lean
def IsSplitting (S : Finset ℝ) (f : IET 0 1) (x : ℝ) : Prop :=
  x ∈ S ∧ 0 < x ∧ x < 1 ∧ ∀ y ∈ Set.Ico (0 : ℝ) 1, y < x → f y < x
def IsPairSplitting (S : Finset ℝ) (f g : IET 0 1) (x : ℝ) : Prop :=
  x = 0 ∨ x = 1 ∨ (x ∈ S ∧ (IsSplitting S f x ∨ IsSplitting S g x) ∧ SplitsAt f x ∧ SplitsAt g x)
def IsBlock (S : Finset ℝ) (f g : IET 0 1) (u v : ℝ) : Prop := …
```

Reason (the user's): being a singularity is **not** a property of an exchange on its own — an IET has
many cut sets, and which points count as its singularities is part of the chosen representation.  For
the paper's pair the marked list is `S_f ∪ f⁻¹ S_g`, which is exactly the cut set of
`IsCompPresentation.toIsCutSet`.  The old definitions quantified over a bare `IET 0 1` and did not
mention any marked point at all.

`block_invariant`, `block_irreducible_on_good` and `exists_word_trivial_on_block` now take `S` as well
(the first is proved and unchanged otherwise; the other two are open, and `exists_word_trivial_on_block`
additionally assumes `∀ x ∈ S, x ∈ Ico 0 1`).

**Still to decide** (not done): `block_irreducible_on_good` and `exists_word_trivial_on_block` take
`S` as a *parameter*, so the caller must supply the right one.  The right one is the marked list of
the presentation, so the clean form of Lemma 3.4 is stated on `GoodRegion` and derives `S` from
`s` (`Finset.univ.image fun i => s i.castSucc`); this should be settled when Lemma 3.4 is proved.

## `redIdx` was `Fin.castLE` (removed)

`redIdx n : Fin (n-1) → Fin n` was `⟨i.val, i.isLt.trans (Nat.sub_le n 1)⟩`, which is **Mathlib's
`Fin.castLE (Nat.sub_le n 1)`** (`Fin.castLE : n ≤ m → Fin n → Fin m`).  It is gone: the free
coordinate of the `i`-th length is now `Fin.castLE (Nat.sub_le d 1) i`, and

* `(Fin.castLE h i).val = i.val` is `Fin.val_castLE`;
* for `n` literally of the form `m+1`, `Fin.castLE (Nat.sub_le (m+1) 1) i` is *definitionally*
  `i.castSucc` (`rfl`), which is why the old `redIdx_succ`/`redIdx_ne_lastIdx` could simply be
  deleted — the rewrites that used them are now definitional.  (For a *variable* `n` this is not
  definitional: `n - 1 + 1` does not reduce to `n`.)

The helper `simplexMap_redIdx` is renamed `simplexMap_castLE`.

`lastIdx` is kept: Mathlib's `Fin.last : (n) → Fin (n+1)` has the wrong index type (it would need
`Fin.cast (n-1+1 = n)` around it, which is not definitional), and `Fin.rev 0` is the same index but
unreadable.  `lastIdx_eq_last` identifies the two in the `m+1` case.

## `PReal` corrected to the free coordinates (degrees of freedom)

`PReal d e` was `(Fin d → ℝ) × (Fin e → ℝ)`; it is now

```lean
abbrev PReal (d e : ℕ) := (Fin (d - 1) → ℝ) × (Fin (e - 1) → ℝ)      -- d + e - 2 degrees of freedom
```

because that is where the Lebesgue measure of Lemma 3.1 lives — and, not by coincidence, it is the
space `simplexVolume` is built from (`simplexRegion d ⊆ (Fin (d-1) → ℝ)`), so
`compLen_absolutelyContinuous` will compare Lebesgue on `PReal n'` with `simplexVolume`.

Consequences, all handled: `toReal` is now the **projection to the free coordinates**
(`fun i => p.1 (redIdx d i)`), so it is no longer injective on the orthant — it is injective only on
the simplexes (where `λ_last = 1 - ∑` is determined).  `toReal_injective` was deleted rather than
restated: nothing used it, and its on-simplex form should be added with the consumer that needs it.
`IsBadParamReal` and `relReal` now read `q.1 i` / `q.2 j` directly (no `redIdx` indirection), and
`IsAffineFn` is an `AffineMap ℝ (PReal d e) ℝ` — affinity in the `d + e - 2` free coordinates.

Everything about `O` survives unchanged, because `isBadParam_iff`, `isOpen_goodParams`,
`exists_ball_subset_goodParams` and the path argument `toReal_seg` are all stated for a map `toReal`
that is continuous and affine on the orthant, not for an injective one.

## The two bridges, and the start of Lemma 3.2

**`mkIETCuts` + `isCutSet_mkIETCuts`** (`IET.lean`).  The cut set that `isIET_mkIETFun` built inline is
now a definition, `mkIETCuts lam a t` (cell starts `a + leftEnd lam i`, plus `a + ∑ lam` when
`[a, a+t)` is longer than the total length), with

```lean
theorem isCutSet_mkIETCuts (ht : ∑ lam ≤ t) (htpos : 0 < t) :
    IsCutSet (mkIETFun lam π a) a (a + t) (mkIETCuts lam a t)
theorem isCutSet_mkIET1 (hl : ∑ lam = 1) :
    IsCutSet (mkIET1 lam π hl) 0 1 (mkIETCuts lam 0 1)
```

and `isIET_mkIETFun` is now three lines: the degenerate case (all lengths `0`, so `T = 0` and the map
is the identity) and `Or.inr ⟨mkIETCuts …⟩`.  The `0 < t` cannot be dropped: for `t ≤ 0` no cut set
exists (`a ∈ Ico a (a+t)` fails), which is exactly why `IsIET` has the identity disjunct.
`isCutSet_mkIET1` needed `⇑(mkIET1 lam π hl).toEquiv = mkIETFun lam π 0` as a `have … := rfl` before
`simpa`: `simpa` alone will not see through `mkIET1`'s structure projection.

**`IsCompPresentation.toIsCutSet`** (`Section3.lean`):

```lean
theorem IsCompPresentation.toIsCutSet (hp : IsCompPresentation lam π mu σ hl hm n s ρ) :
    IsCutSet (⇑(mkIET1 mu σ hm * mkIET1 lam π hl)) 0 1
      (Finset.univ.image (fun i : Fin n => s i.castSucc))
```

The four non-trivial fields: the identity outside `[0,1)` comes from `IET.isIET.eq_of_notMem` (the
product is an `IET 0 1` through the group instance), `mapsTo` from `IET.isIET.mapsTo`, `cuts_mem` from
`StrictMono` (`s i.castSucc ≥ s 0 = 0` and `s i.castSucc < s (last) = 1` since `i.castSucc < last`),
and `transl_of_not_separated` from `exists_cell_of_strictMono`: two points in different cells are
separated by the right end of the lower cell (written `s k.castSucc` with `k = ⟨i.val+1, _⟩` — the two
are *definitionally* equal as `Fin (n+1)` terms, so `rfl` closes the identification), and two points
in the same cell have the same displacement by the `cell` field.

Note what this bridge does **not** need: it does not need the cell lengths of `g ∘ f` to be the
`s i.succ - s i`, only that `g ∘ f` translates each `s`-cell.  That is why it goes through.

**Start of Lemma 3.2**: `mkIETFun_leftEnd`, the coordinate computation every case of the analysis
begins with — for a nonempty `i`-th cell (`0 < lam i`, `leftEnd lam i < ∑ lam`),

```lean
theorem mkIETFun_leftEnd (hi : 0 < (lam i : ℝ)) (hb : a + leftEnd lam i < a + ∑ k, lam k) :
    mkIETFun lam π a (a + leftEnd lam i) = a + imageLeft π lam i
```

i.e. the exchange sends the left end of a cell to the left end of its image.  This is what turns "the
singularity `x` of `f`" into the coordinate `imageLeft π lam i` of the paper's Case 1, and the `g`
analogue (Case 2) is the same lemma with `(mu, σ)`.  `0 < lam i` is needed for `idx lam (leftEnd lam
i) = i`; when `lam i = 0` the cell is empty and `leftEnd lam i = upperEnd lam i = leftEnd lam (i+1)`.

## Missing API found by auditing the proofs (done)

Two idioms dominated the tactic scripts and both were API gaps rather than local noise.

**1. `Separated` had no usable form.**  Its definition is `∃ c ∈ C, c ∈ Ioc (min x y) (max x y)`, so
every use began by rewriting `min`/`max` away with hypotheses `min_eq_left`/`max_eq_right` — 45
occurrences across `IET`, `SingularityBound`, `Irreducible`, `MeasureTools`.  Added in `IET.lean`:

```lean
theorem Separated.symm        (h : Separated C x y) : Separated C y x
theorem Separated.comm        : Separated C x y ↔ Separated C y x
theorem Separated.exists_of_le (h : Separated C x y) (hxy : x ≤ y) : ∃ c ∈ C, x < c ∧ c ≤ y
theorem Separated.of_lt_le (hc : c ∈ C) (h1 : x < c) (h2 : c ≤ y) : Separated C x y   -- no order on x, y
theorem mem_Ioc_min_max (x y : ℝ) {c} (hxy : x ≤ y) :
    c ∈ Set.Ioc (min x y) (max x y) ↔ x < c ∧ c ≤ y
theorem mem_Ioc_min_max_of_le {x y c} (hyx : y ≤ x) :
    c ∈ Set.Ioc (min x y) (max x y) ↔ y < c ∧ c ≤ x
```

`Separated.of_lt_le` needs **no** comparison between `x` and `y` (`min x y ≤ x < c` and `c ≤ y ≤
max x y`), which is what removed most of the case splits.  The two `mem_Ioc_min_max` orientations are
needed because the lemma's `x`/`y` are inferred from `hxy`; with only one of them, sites whose
hypothesis is `y ≤ x` fail to unify (they silently pick the wrong orientation and report a `min c₁ x`).

`SingularityBound.lean` also **duplicated the definition** as `CutSep`; it is now
`abbrev CutSep (S) (x y) := Separated S x y`, with `cutSep_comm`/`cutSep_mono` one-line corollaries.
Effect: 45 → 17 occurrences of `min_eq_*`/`max_eq_*`, and the rest are the API's own proofs or genuine
`min`-arithmetic (in `Irreducible`, `Commensurable`).

**2. `evalWord` had no API on the generators or on conjugates.**  Three sites (`iterate_word` twice,
`evalWord_conj_pow`) opened the definition down to `FreeGroup.lift (fun j => if j = 0 then f else g)`
and applied `simp [genX]`.  Added in `MeasureTools.lean`:

```lean
@[simp] theorem evalWord_one / evalWord_mul / evalWord_inv / evalWord_pow
@[simp] theorem evalWord_genX (f g : IET 0 1) : evalWord genX f g = f
@[simp] theorem evalWord_genY
theorem evalWord_conjX (u) : evalWord (genX⁻¹ * u * genX) f g = f⁻¹ * evalWord u f g * f
theorem evalWord_conjY
```

so a conjugation is now `rw [evalWord_conjX]` instead of a five-line `have`.  Note these are *not*
`rfl` (`evalWord_mul` is `map_mul _ u v`), and `simp only [evalWord, …]` *prevents* `evalWord_genX`
from firing, since after unfolding the term is the raw `lift` application.

**3. Section 3 had no cell decomposition.**  Added `exists_cell_of_strictMono` (in `Section3.lean`):
for a strictly increasing `s : Fin (n+1) → ℝ` with `s 0 = 0` and `s (last) = 1`, every `x ∈ [0, 1)`
lies in some `[s i.castSucc, s i.succ)`.  This is the discrete counterpart of
`IsCutSet.exists_mem_cell` and is needed by every case analysis over the cells of the composition.

**API still missing, deliberately not added yet** (each is a judgement call for the round that needs
it):

* `IsCompPresentation` vs `IsCutSet`: the fields `cell`/`f_transl`/`g_transl`/`card_eq` *are* a cut set
  for `g ∘ f` in disguise (with cut set `univ.image s.castSucc`), and `compLen` is exactly
  `IsCutSet.lengths`.  A bridge `IsCompPresentation.toIsCutSet` would give Lemma 3.2 and
  `compLen_injective` the whole cell API (cell starts, lengths, the `perm`) for free, and would let
  `compLenVec`/`compLen` be definitions rather than duplicates.  Worth doing *with* Lemma 3.2.
* `SingularityBound` builds its own `ietCuts lam` and proves it is a cut set, duplicating what
  `isIET_mkIETFun` already constructs internally.  Making that cut set a `def`
  (`mkIETCuts`/`isCutSet_mkIETCuts`) would remove the duplication and give `mkIET1` the cell API.
* `IET 0 1`-level wrappers `IET.mapsTo` / `IET.eq_of_notMem` (9 sites currently write
  `f.isIET.mapsTo hy`); and `IsAffineFn` has no algebra (`add`, `sub`, `const`, `smul`) — needed once
  Lemma 3.1's injectivity is done with the explicit inverse.

**The real parameter space.** The statements live in `(Fin d → ℝ≥0) × (Fin e → ℝ≥0)` (that is where
`simplexVolume`, `MasurVeech` and `VeechRigidity` are), but that space is not a real vector space, and
the proofs need one.  So `PReal d e := (Fin d → ℝ) × (Fin e → ℝ)`, `toReal : P → PReal` (the
coordinatewise coercion), `IsBadParamReal` (the same relation in real coordinates, `isBadParam_iff`),
and everything analytic is done in `PReal` and pulled back along `continuous_toReal`.  Proved this
way: `isOpen_goodParams`, from the finite enumeration of the coefficient data — `CoeffIndex d e :=
(Fin d ⊕ Fin e) ⊕ Fin 1` indexes the `aᵢ`, the `bⱼ` and the constant `k`, so
`Fintype.piFinset (fun _ => Finset.Icc (-2:ℤ) 2)` is the finite set of coefficient vectors, the bad set
is the finite union of the closed `{relReal t = 0}`, and openness follows.  Do **not** try
`Finset.univ.pi` (it yields `(a : Fin d) → a ∈ univ → ℤ`) nor `Finset.mem_product` (stated for `×ˢ`).

**Two findings that cost time, both recorded in the file.**

1. `compLen_injective` is **false without** the hypothesis `hO : O ⊆ goodParams`, which the draft
   version lacked.  Counterexample: `d = e = 2`, `π = σ` the transposition, `p = (1/4, 3/4)` and
   `q = (1/2, 1/2)` both give `g ∘ f = id` (for `p`, `g` is the inverse of `f`; for `q` both are the
   rotation by `1/2`), so both are presented by `s = (0, 1/3, 2/3, 1)`, `ρ = 1` and the length-vector
   hypothesis holds trivially.  Both pairs are bad (`λ₁ + μ₁ = 1`).  The hyperplanes are exactly what
   keeps the singularities coming from `f` apart from those coming from `f⁻¹ S_g`.
2. `ae_exists_goodRegion` still needs two steps: preconnectedness of `toReal ⁻¹' Metric.ball` (which is
   `ball ∩ orthant`, an intersection of convex sets; the content is that the coercion
   `(Fin d → ℝ≥0) × (Fin e → ℝ≥0) → PReal` is inducing, so preconnectedness transports along it —
   `Topology.IsInducing.isPreconnected_image` is the lemma used in `Analysis/Convex/Quasiconvex.lean`
   for exactly this), and the choice of `ε` from the finite minimum of `|relReal t|` at `toReal p`.
   Note there is no `SeminormedAddCommGroup` on `Fin d → ℝ≥0`, no `convex_ball` and no
   `LocallyConnectedSpace NNReal`, so nothing can be done in the `ℝ≥0`-space directly.

## File headers (added on request)

Every `.lean` file of the paper's development (the 10 modules in `IET2/`, the 13 files in
`IET2/Tasks/`, and the 3 superseded files in `IET/`) now starts with the Mathlib-style copyright
block

```
/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
```

followed by the imports, then a `/-! ... -/` **module doc-string as the first command after the
imports** (`open` lines had to move below it in the `Tasks/` files; in ten files the doc-string used
to sit *above* the imports).  A `LICENSE` file (Apache 2.0, the same text as Mathlib's) was added at
the repository root, since the header refers to it.  Checked with Mathlib's own
`Mathlib.Linter.copyrightHeaderChecks` (0 complaints) and by confirming that `/-! -/` registers as a
module doc in a non-`module` file, so the `linter.style.header` rule is satisfied.  `Kakeya/` belongs
to a different project and was left alone.

## Lean gotchas paid for in this session

* `discovery_start` refuses a statement file whose **target is not at top level** (inside a namespace
  the export is `Ns.<id>`, and the id check fails: "the frozen file's theorem must be named `<id>`").
  Helper lemmas are fine — the run `translation-vector-bound` shipped a `section aux` with three
  lemmas *before* the target and its proof was accepted.  The `source` must also **start with
  `import`**: a copyright header before the imports makes the workers' file assembly fail with
  `invalid 'import' command, it must be used in the beginning of the file` (this killed the first
  attempt at `singularity-bound`; keep the header in the project copy under `Tasks/` only).
* `theorem` names inside `namespace FreeGroup` are `FreeGroup.x`, so a run target must be stated at
  top level (`end FreeGroup` first) for its id to match.
* `Subgroup.closure_le` takes the subgroup explicitly: `(Subgroup.closure_le _).mpr h`.  The bridge
  from "the generators commute" to "the closure is abelian" is
  `Subgroup.centralizer_closure (s) : centralizer ↑(closure s) = centralizer s`, then
  `closure_le` twice (`u`, `w ∈ centralizer {u,w}`, so `closure {u,w} ≤ centralizer {u,w} =
  centralizer (closure {u,w})`).
* `IsFreeGroup.nonempty_basis : ∃ ι, Nonempty (FreeGroupBasis ι G)`; `b.repr : G ≃* FreeGroup ι`,
  `FreeGroupBasis.repr_apply_coe b i : b.repr (b i) = FreeGroup.of i`, and `b.repr.symm (of a) = b a`
  (via `← repr_apply_coe`, `MulEquiv.symm_apply_apply`).
* `IsMulTorsionFree.pow_left_injective (hn : n ≠ 0)` is `Function.Injective (· ^ n)`, so apply it to
  the *equality*: `pow_left_injective h4 h5`, not `pow_left_injective h4 q 1 h5`.
* **`rw` over-application** on `zpow`/cast goals: `rw [zpow_natCast]` can rewrite the right-hand side
  (matching `n : ℕ` with `(↑n).toNat`) and produce a nonsense goal; likewise `rw [h2]` with
  `h2 : ν = ↑ν.toNat` rewrites both sides.  Use explicit terms (`zpow_natCast s n`,
  `congrArg (fun k : ℤ => s ^ k) h2`, `(zpow_mul s m n).symm`) or `conv_lhs => rw [h]`.
* `group` does not close goals containing `g ^ 2` (it keeps `g ^ 2` and `g * g` apart): rewrite
  `pow_two, mul_inv_rev` first (`rw [pow_two, mul_inv_rev]; group`), and note that `rw [pow_two]`
  already rewrites *all* occurrences, so a second `pow_two` in the same `rw` list fails.
* `mul_comm v v` fails on `FreeGroup α` (no `CommMagma`): use `rfl` for `v * v = v * v`.
* `Int.natAbs_eq_natAbs_iff.mp (hab : a.natAbs = b.natAbs) : a = b ∨ a = -b` (note the orientation);
  `Int.natAbs_natCast`, `Int.natAbs_mul`, `Int.natAbs_neg`, `Int.toNat_of_nonneg` cover the casts.
* `push_neg` is deprecated here: `push Not at h`.
* **Linter profile.** Mathlib's recommended downstream setting is
  `set_option linter.mathlibStandardSet true` (`Mathlib/Init.lean` lists the set).  The whole project
  is now clean under it except the `sorry` warnings of the open declarations: the main things it wants
  are a copyright header, a module doc-string as the first command after the imports, no line longer
  than 100 characters (including the first line of a doc-string), `have` rather than `haveI` when the
  goal is a `Prop` (Lean 4's `have` does register local instances), `change` rather than `show` when
  the goal is only definitionally equal, and no unused `[DecidableEq α]`-style hypotheses in
  statements (drop them, put `classical` in the proof).
* The three IET.lean warnings that used to be described here as load-bearing are gone: replacing
  `haveI` by `have` is fine, renaming the existential binder `(hn : NeZero n)` to `(_ : NeZero n)` is
  fine, and `simp only [Fin.val_mk]` before an `omega` that needs to see through `Fin.mk` becomes
  `dsimp only [Fin.val_mk]` (that *was* load-bearing: plain deletion breaks the proof, `dsimp` does
  not and is not flagged as an unused simp argument).
* For the maximal root, avoid `Nat.findGreatest`; `let S := (Finset.range (FreeGroup.norm v + 1)).filter
  (fun k => ∃ q, v = q ^ k)` with `S.max'` (`Finset.le_max'`, `Finset.max'_mem`) is direct, and P3
  gives the bound `k ≤ norm v` that puts every root exponent in `S`.
* `IsFiniteMeasure` wants `μ univ < ⊤`, not `≠ ⊤`: `lt_top_iff_ne_top.mpr`.

## Lemma 3.2 as first stated is **false** — `IsIrreducibleOn` re-stated (this session)

`IsIrreducibleOn` and `exists_pairSplitting_of_invariant` were stated with the target `Ico u v`:

```lean
def IsIrreducibleOn (F : ℝ → ℝ) (u v : ℝ) : Prop :=
  ∀ c, u < c → c < v → ¬ (∀ x ∈ Ico 0 1, u ≤ x → x < c → F x ∈ Ico u v)
```

That is false, for *every* pair of data, on the block `[0, 1)`: `E ∘ D` maps `[0, 1)` into itself
(`comp_mapsTo`), so for any `c ∈ (0, 1)` the inner hypothesis holds and the predicate fails.  Since
`IsBlock D E 0 1` only asks for `0` and `1` to be pair-splitting with nothing in between, the
conclusion of `block_irreducible_on_good` fails whenever the pair has no interior pair-splitting
point — and such pairs exist among the *good* ones.

**The concrete counterexample** (machine-checked, `.scratch/try/counter.lean`): `d = e = 2`, both
permutations the transposition, `λ₀ = 1/3`, `μ₀ = 1/4`.

* `¬ IsBadParam ((1/3), (1/4))`: `k + a/3 + b/4 = 0` with `|k|,|a|,|b| ≤ 2` forces `k = a = b = 0`
  (multiply by `12` and use `omega`); note `(1/3, 1/3)` and `(1/3, 2/3)` *are* bad, so the example
  is not vacuous.
* the only marked points are `D.mark = (0, 1/3, 1)`, `E.mark = (0, 1/4, 1)`, and `IsSplitting 1`
  fails for both maps (`π 0 = 1`), so the only *splitting* singularities are `0` and `n`; hence
  `IsPairSplitting D E x ↔ x = 0 ∨ x = 1` and `IsBlock D E 0 1` holds;
* `¬ IsIrreducibleOn (E ∘ D) 0 1` for the old definition, by `comp_mapsTo` with `c = 1/2`.

`exists_pairSplitting_of_invariant` dies with it: with `u = 0`, `c = 1/2`, `v = 1` its hypothesis
`F x ∈ Ico u v` is `F x ∈ [0, 1)`, which holds always, and there is no pair-splitting point in
`(0, 1)`.

**The repair** (forced by the paper, which says the restriction of `ρ` to the block is
irreducible — i.e. no *proper initial piece of the block* is invariant):

* target `Ico u c` instead of `Ico u v`:
  `∀ c, u < c → c < v → ¬ (∀ x ∈ Ico 0 1, u ≤ x → x < c → F x ∈ Ico u c)`;
* `exists_pairSplitting_of_invariant` gains `0 ≤ u`, `u < 1`, `c ≤ 1` (all three follow from
  `IsBlock D E u v` — `IsPairSplitting.mem_Icc` — in `block_irreducible_on_good`), and its
  hypothesis is `F x ∈ Ico u c`.

New API: `IETDatum.mark_mem_Icc : D.mark k ∈ Icc 0 1` and
`IsPairSplitting.mem_Icc : IsPairSplitting D E x → x ∈ Icc 0 1`.

`block_irreducible_on_good` is unchanged as a statement and is now *true*; it is still derived from
the `sorry`'d geometric core.

Divide by `12` again if a later statement uses `Ico u v`: the mistake is easy to repeat, since
`[u, v)` *is* invariant under `E ∘ D` for a block and it feels like the natural thing to write.

## Where Lemma 3.2's case analysis stands, and the bound `2` problem (this session)

**Infrastructure added and proved** (`Section3.lean`, before `exists_pairSplitting_of_invariant`):

```lean
IETDatum.lam_pos            -- 0 < D.lam i  (all lengths of a datum are positive)
IETDatum.leftEnd_lt_sum     -- leftEnd D.lam i < ∑ lam
IETDatum.markCuts           -- univ.image (fun i => D.mark i.castSucc)
IETDatum.mark_mem_markCuts / mem_markCuts / mkIETCuts_eq_markCuts
IETDatum.isCutSet_markCuts  -- IsCutSet D.toFun 0 1 D.markCuts   (from isCutSet_mkIETCuts)
IETDatum.toFun_mark_castSucc -- D.toFun (D.mark i.castSucc) = imageLeft D.π D.lam i
IETDatum.toFun_eq_of_mem_cell -- on a cell, D.toFun x = x + translationVector D.π D.lam i
isCutSet_comp_markCuts      -- IsCutSet (E ∘ D) 0 1 (D.markCuts ∪ D.isCutSet_markCuts.preimage E.markCuts)
mem_comp_markCuts           -- a cut of the composition is a marked point of D, or D x is one of E
```

**Case 1a of the paper's case analysis is PROVED**, axiom-clean (`Section3.lean`):

```lean
theorem splitting_of_imageLeft_relation
    (hgood : ¬ IsBadParam (toReal (lam, mu))) (hl : lam ∈ simplex d) (hm : mu ∈ simplex e)
    {k : Fin d} {l : Fin e} {n : Fin d}
    (h : imageLeft π lam k + imageLeft σ mu l - leftEnd mu l = leftEnd lam n) :
    π k = n ∧ (∀ i, (π i).val < n.val ↔ i.val < n.val) ∧ ∀ j, (σ j).val < l.val ↔ j.val < l.val
```

with helpers `sum_ite_one_mul` and `ite_one_sub_ite_eq_zero`.  The mechanism: the relation's
coefficients are `a i = [π i < π k] - [i < n]`, `b j = [σ j < σ l] - [j < l]`, all of absolute
value `≤ 1`, so `relation_of_good` applies.  It gives `a = t·1`, `b = -t·1` with `t = a (lastIdx d)`;
`t = 0` is the splitting conclusion, and `t = ±1` are impossible because the `lastIdx` index makes
one of the two indicators `0` while the other must be `1`.  **This `t = ±1` case is what the paper
does not have to do** (it writes "each coefficient is 0", which is only true for `t = 0`); it is why
the formal statement of `relation_of_good` has the two constant coefficients.

**The bound `2` is NOT enough for Case 1b, contrary to what this file said until now.**  In Case 1b
(`x ∈ S_f`, `gfx ∈ f⁻¹ S_g`) the relation is

```
Σ_{π i < π(k+1)} λ_i + Σ_{σ j < σ ℓ} μ_j − Σ_{j<ℓ} μ_j + Σ_{π i < π m} λ_i − Σ_{i<m} λ_i = Σ_{j<n} μ_j
```

so the coefficient of `λ_i` is `[π i < π k] + [π i < π m] − [i < m]`, which takes the value **`2`**
when `π i < π k`, `π i < π m` and `i ≥ m`.  A relation with full-coordinate coefficients bounded by
`2` has *free* coefficients bounded by `4` (`a_i - a_last`), so trivialising it needs `IsBadParam`
with bound `4` — which is exactly the paper's choice.  With the current bound `2` Case 1b cannot be
closed this way.

The fix, when it is taken up, is mechanical but touches proved code:

* `IsBadParam`: the three `≤ 2` bounds (`Section3.lean`, in the `def`) become `≤ 4`;
* `smallCoeffs`: `Finset.Icc (-2) 2` becomes `Finset.Icc (-4) 4`, and `mem_smallCoeffs`'s `≤ 2` `≤ 4`;
* `isBadParam_mem_badSet` has `hN : 2 ≤ N` and an estimate in `N`; it becomes `4 ≤ N` and the
  estimate has to be redone (this is the only proof with real content in the list);
* `ae_goodParams` instantiates that `N`, so its witness changes;
* `coeffs_zero_of_good'` / `coeffs_zero_of_good` keep their `≤ 2` hypotheses and stay valid
  (`¬ IsBadParam` at bound `4` is *stronger*), and a new `relation_of_good_two` with full-coordinate
  coefficients `≤ 2` is added next to `relation_of_good`.

Since the user's decision was "use 2 instead of 4 as I guess this should be enough; if it is not the
case, we will revisit later", this is the revisit: **the bound has to go up to 4** (or Case 1b has to
be reorganized so that no coefficient `2` appears, which I do not see how to do).

The remaining cases, in the same style, are 1b, 2a, 2b; each produces a relation of the above shape
(two "position" expressions equated) and each ends in `perm_eq_of_preimage` after the coefficients
are forced to `0`.  Note Case 2a is degenerate: its relation is `Σ_{σ j < σ(ℓ+1)} μ_j = Σ_{i<n} λ_i`,
which at a good pair forces both sides to be empty, i.e. `gfx = 0` — contradicted by `gfx > 0`.

## Lemma 3.2, second correction: the invariance must be quantified over cuts (and the bound is now 4)

### The bound: `IsBadParam` now uses `4`, not `2`

Taken with the user this session, as announced in the previous entry.  Changes: `IsBadParam`'s three
bounds, `smallCoeffs` (`Icc (-4) 4`), `mem_smallCoeffs`, `isBadParam_mem_badSet` (`hN : 4 ≤ N`),
`ae_goodParams` (`max N₀ 4`), and the *stated* bounds of `coeffs_zero_of_good` /
`coeffs_zero_of_good'` (`≤ 4`).  `relation_of_good` is now stated with **coefficients bounded by `2`**
and derives free coefficients bounded by `4`, so Case 1a (coefficients `≤ 1`) and Case 1b
(coefficients `≤ 2`) both go through it.  All still axiom-clean; the build is green at 9 `sorry`s.

### The statement: `exists_pairSplitting_of_invariant` and `IsIrreducibleOn` were still false

Both were quantified over an arbitrary `c ∈ (u, v)`, with the *invariance* of `[u, c)` as hypothesis
and the target `Ico u c`.  Two counterexamples, machine-checked in `.scratch/try/counter2.lean`
(**keep that file**; it compiles against the present library):

`d = e = 2`, both permutations the **identity** (so `D = E = id`), lengths `λ₀ = 2/5`, `μ₀ = 3/7`
(good with bound `4`: `35k + 14a + 15b = 0` with `|k|,|a|,|b| ≤ 4` forces `k = a = b = 0`).

1. `E ∘ D = id`, so `F([u, c)) ⊆ [u, c)` holds for **every** `c`.  The pair-splitting points are
   exactly `{0, 2/5, 3/7, 1}` (all marked points are splitting since the permutation is the identity,
   and each marked point of one map lies in a fixed cell of the other).  So with `u = 0`,
   `c = 1/10`, `v = 1/5` the hypothesis holds and `(0, 1/5)` contains **no** pair-splitting point:
   the `∃ x ∈ (u, v)` conclusion is false (`exists_pairSplitting_false`).
2. `[0, 2/5)` **is a block** (`IsBlock Dc Ec 0 (2/5)`), and `E ∘ D` is the identity on it, so every
   `[0, c)` is mapped into itself (`not_irreducibleOn`).  It is nevertheless irreducible in the
   paper's sense: it is a block of **one cell**, and a permutation of one cell is irreducible.  So the
   invariant piece must be quantified over *cells*, i.e. over `c` in the cut set.

### The present statements

```lean
def IsIrreducibleOn (F : ℝ → ℝ) (S : Finset ℝ) (u v : ℝ) : Prop :=
  ∀ c ∈ S, u < c → c < v → ¬ (∀ x ∈ Set.Ico (0 : ℝ) 1, u ≤ x → x < c → F x ∈ Set.Ico u c)

theorem exists_pairSplitting_of_invariant (D : IETDatum d) (E : IETDatum e)
    (hp : ¬ IsBadParam (D.v, E.v)) {u c : ℝ} (hu0 : 0 ≤ u) (huc : u < c)
    (hcS : c ∈ D.markCuts ∪ D.isCutSet_markCuts.preimage E.markCuts)
    (hinv : ∀ x ∈ Set.Ico (0 : ℝ) 1, u ≤ x → x < c → E.toFun (D.toFun x) ∈ Set.Ico u c) :
    IsPairSplitting D E c

theorem block_irreducible_on_good ... (hb : IsBlock D E u v) :
    IsIrreducibleOn (fun x => E.toFun (D.toFun x))
      (D.markCuts ∪ D.isCutSet_markCuts.preimage E.markCuts) u v
```

`block_irreducible_on_good` is now *proved* from `exists_pairSplitting_of_invariant` (the `u ≤ x` and
`u < 1` side conditions come from `IsPairSplitting.mem_Icc`), and the latter is the single `sorry` of
the geometric core.

### What the case analysis has to do (next)

The conclusion is about **`c` itself**, which is what every case of the paper ends with: the point
`c` (their `gfx`) turns out to be a splitting singularity of one map inside a fixed cell of the
other.  The input is `c ∈ S` (so `c` is a marked point of `D`, or `D c` is a marked point of `E`),
`c > 0`, and `c = F x` for the cut `x` with `F x = c` — the cell just above `c` maps onto the cell
starting at `c`, which is where `hinv` is used (`F([u,c)) = [u,c)`).  With `D.toFun_mark_castSucc`,
`IETDatum.toFun_eq_of_mem_cell` and `splitting_of_imageLeft_relation` (Case 1a, proved) the four
cases are:

* **1a** `c = D.mark k` and `D c = E.mark j`: relation `imageLeft π λ k' + imageLeft σ μ l − leftEnd μ l
  = leftEnd λ n'` — **this is `splitting_of_imageLeft_relation`, done**; it yields `π k' = n'`,
  `D.IsSplitting n'` and `E.IsSplitting l`, hence `c = D.mark n'.castSucc` splitting for `D` in the
  fixed cell `l` of `E` (`E.IsSplitting l` plus `σ l = l` gives `E.IsSplitting l.succ`, i.e.
  `E.IsFixedCell l`).
* **1b** `c = D.mark k` and `D c = E.mark j` with `c` a preimage of an `E`-singularity: relation with
  coefficients up to `2`, which is what the bound `4` is for.  Needs the paper's extra step
  (`l = 1`, then `π k' = 1` or `π m = 1`).
* **2a** `c` and `D c` both preimages: the relation forces `c = 0`, contradicting `0 < c`.
* **2b** symmetric to 1a (exchange `D` and `E`).

## Case 1b of Lemma 3.2: **PROVED** (this session)

`Section3.lean`, axiom-clean (`[propext, Classical.choice, Quot.sound]`), with two helpers:

```lean
theorem ite_add_ite_sub_ite {p q r : Prop} [Decidable p] [Decidable q] [Decidable r]
    (h : ((if p then 1 else 0) + (if q then 1 else 0) - (if r then 1 else 0)) = 0) :
    (r ↔ (p ∨ q)) ∧ ¬ (p ∧ q)
theorem ite_sub_ite_sub_ite ...   -- A - B - C = 0 version

theorem splitting_of_imageLeft_relation_add {d e} [NeZero d] [NeZero e]
    {lam} {π} {mu} {σ} (hgood : ¬ IsBadParam (toReal (lam, mu))) (hl) (hm)
    {k m : Fin d} {l n : Fin e} (hn : 0 < n.val)
    (h : imageLeft π lam k + imageLeft σ mu l - leftEnd mu l + imageLeft π lam m - leftEnd lam m
      = leftEnd mu n) :
    σ 0 = n ∧ (∀ j, (σ j).val < n.val ↔ j.val < n.val) ∧ π k = 0 ∧ π m = m ∧
      ∀ i, (π i).val < m.val ↔ i.val < m.val
```

Coefficients `a i = [π i < π k] + [π i < π m] - [i < m]` (values in `{-1,0,1,2}`) and
`b j = [σ j < σ l] - [j < l] - [j < n]` (values in `{-2,…,1}`), so `relation_of_good` at bound `2`
applies — **this is the case that needed the bound `4`**, and it is the check that the bound change
was necessary and sufficient. Two things the paper does not have to do: (i) `t := a (lastIdx d)`
is not known to be `0` a priori, but `a m = [π m < π k] ∈ {0,1}` and `t = 1` is killed by
`a k = [π k < π m] - [k < m]` against `π m < π k`; (ii) in the sub-case `π m = 0` one must deduce
`m = 0` from splitting at `m` (`π m = 0 < m` would give `m < m`).

The paper's conclusions match exactly: with `l = 0` and `σ 0 = n`, the cell `0` of `σ` is fixed at
its left end and `n` is a splitting singularity of `σ`; and `π k = 0` says the cell `0` of `π` is
fixed while `m` is a splitting singularity of `π`. That is the "`gf x` is a pair-splitting point"
conclusion in coordinates.

## The position lemma: where it reduces to (NOT done then — **proved** later, see "The position lemma is PROVED, and Case 1a is glued")

What the geometric core still needs (`exists_pairSplitting_of_invariant`): from
`u, c ∈ S` (the refinement cuts), `u < c`, and `F([u, c)) ⊆ [u, c)`, produce a cut `x ∈ S` with
`F x = c`, so that `x` and `c` can both be classified by `mem_comp_markCuts`.  The proof I worked
out (all the ingredients exist, the assembly does not):

1. `F⁻¹ c ∈ Ico 0 1`: `F` is injective and the identity from `1` on (`apply_eq_self_of_le`).
2. The **covering step**, the real content: `A := ⋃_{j ∈ J} F '' cell_j = Ico u c`, where
   `J` is the set of cells starting in `[u, c)`.
   * `∑_{j ∈ J} cellLen j = c - u`: `sum_cellLen_lt` twice, with `u = cellStarts k₀`,
     `c = cellStarts k₁` (`cellStarts_surj`), `k₀ < k₁` (`cellStarts_strictMono`), and
     `Finset.filter` arithmetic;
   * the images are pairwise disjoint half-open intervals (`image_cell_disjoint`, `image_cell`) and
     each lies in `[u, c)` (`map_of_mem_cell` + `hinv`), so `volume A = c - u = volume (Ico u c)`
     and `A ⊆ Ico u c`.
3. **No other cell meets `[u, c)`**: if `j ∉ J` had `F '' cell_j` meeting `[u, c)` with
   `j ∉ J`, the intersection has positive measure (it is a half-open interval meet an interval,
   nonempty) and is disjoint from `A`, so `A ∪ (F '' cell_j ∩ Ico u c) ⊆ Ico u c` would have volume
   `> c - u`.  Two small topological facts are needed and are the fiddly part: a finite union of
   half-open intervals with total length equal to that of an interval containing it *is* the
   interval, and such a union is left-closed (so a one-point gap cannot occur).
4. Then `x := cellLeft (F⁻¹ c) ∈ S` and its image `Ico (F x) (F x + len)` contains `c`, so
   `F x ≤ c`.  If `F x < c`, use 3 twice: `F x < u` would put `u ∈ F '' cell_x` while `u ∈ A`
   (left-closedness as in step 3), and `F x ≥ u` gives positive intersection with `[u, c)`.
   Hence `F x = c`.

Steps 1, 2 and 4 are textbook; step 3's two topological facts are the work.  Do not try to shortcut
this with `cellPerm`: `cellPerm` records the *order* of the image starts, and `cellStarts (cellPerm i)`
is **not** `F (cellStarts i)` (the sorted image starts and the sorted cuts are different finsets).

## Position lemma: the length count is in (this session)

`IsCutSet.sum_cellLen_filter` (proved, axiom-clean, `Section3.lean`):

```lean
theorem IsCutSet.sum_cellLen_filter {F : ℝ → ℝ} {S : Finset ℝ} (hS : IsCutSet F 0 1 S)
    {u c : ℝ} (hu : u ∈ S) (hc : c ∈ S) (huc : u < c) :
    ∑ j ∈ Finset.univ.filter (fun j => u ≤ hS.cellStarts j ∧ hS.cellStarts j < c),
        hS.cellLen j = c - u
```

via `cellStarts_surj` (the two indices `k₀ < k₁` of `u` and `c`), `cellStarts_strictMono.le_iff_le`
(the filter is an index interval `{k₀ ≤ j < k₁}`), `Finset.sum_filter_add_sum_filter_not` and
`sum_cellLen_lt` twice.  Two Lean notes: `rw [← hsplit] at h` (not `rw [hsplit]` in the goal) is what
replaces the `¬(j < k₀)` sub-filter, and `hS.cellStarts_zero` must not be in the final `rw` list (the
`sum_cellLen_lt` rewrites already turn `a` into `0`).

### What is left of the position lemma, precisely

After the length count, these remain (see the previous entry for the plan):

1. `volume (⋃_{j ∈ J} F '' cell_j) = c - u` and the union is `⊆ Ico u c` — routine with
   `image_cell`, `map_of_mem_cell`, `hinv`, `image_cell_disjoint`, `Real.volume_Ico`.
2. **No cell outside `J` has an image meeting `Ico u c`** — from 1 and `A ⊆ Ico u c` of the same
   measure: a nonempty intersection of a half-open interval with `Ico u c` has positive measure, and
   it is disjoint from `A`.
3. `F⁻¹ c ∉ Ico u c` is *free*: if `F⁻¹ c ∈ Ico u c` then `hinv` gives `c ∈ Ico u c`.  What is **not**
   free is the straddling case: with `x := cellLeft (F⁻¹ c)` one gets `F x ≤ c` from `image_cell`, and
   `F x < c` must be excluded.  `F⁻¹ c < u` is impossible (`u ∈ S` is a cut, so `F⁻¹ c` cannot be
   interior to a cell containing `u`); what remains is the cell straddling `c` from above
   (`c ≤ x`, `F x < c`), and that is where 2 is needed (`c` and `u` are cuts, so the cell cannot
   contain either in its interior, and its image must start at `c`).

### A design consequence worth keeping

If the position lemma is proved in the strong form **`F c = c`** (which is what the paper has: the
cell starting at `c` maps onto the cell starting at `c`), the case analysis gets *simpler* than
planned, because then `x = c` and both sides of the relation carry the same index:

* Case 1a (`c = D.mark k.castSucc` and `D c` in the `E`-cell `l`): the relation is
  `imageLeft π λ k + imageLeft σ μ l - leftEnd μ l = leftEnd λ k`, so
  `splitting_of_imageLeft_relation` gives `π k = k`, `D.IsSplitting k` and `E.IsSplitting l`;
  with `σ l = l` (which the same lemma gives) that is `E.IsFixedCell l`, and `c = D.mark k.castSucc`
  is a splitting singularity of `D` in the fixed cell `l` of `E`, i.e. `IsPairSplitting D E c`.
* Case 1b is `splitting_of_imageLeft_relation_add` with `m = k`, and its conclusion
  (`π k = 0`, `π` splits at `k`, `σ` splits at `n`, `σ 0 = n`) is again the pair-splitting of `c`.
* Case 2a gives `c = 0`, against `0 < c`; 2b is 1a with `D` and `E` exchanged.

So the remaining work is *only* the position lemma plus gluing these four into
`exists_pairSplitting_of_invariant`; no further relation-chasing is needed.

## The position lemma is PROVED, and Case 1a is glued (this session)

### Position lemma (axiom-clean, `Section3.lean`)

```lean
theorem IsCutSet.exists_imageStart_of_mapsTo {e : Equiv ℝ ℝ} {S : Finset ℝ}
    (hS : IsCutSet (⇑e) 0 1 S) {u c : ℝ} (hu : u ∈ S) (hc : c ∈ S) (huc : u < c)
    (hinv : ∀ x ∈ Set.Ico u c, ⇑e x ∈ Set.Ico u c) : ∃ x ∈ S, ⇑e x = c
```

The route is **shorter than the plan recorded above**: no "finite union of half-open intervals"
lemma is needed.  Let `J` be the cells starting in `[u,c)`, `A = ⋃_{j∈J} e '' cell_j`.
1. `A ⊆ Ico u c` (`map_of_mem_cell` + `hinv`) and `volume A = ∑_{j∈J} cellLen j = c - u`
   (`measure_biUnion_finset` + `image_cell` + `Real.volume_Ico` + `sum_cellLen_filter`).
2. `w := e.symm c ∈ Ico 0 1` (`Equiv.IsIET.symm_mapsTo`), let `i` be its cell
   (`exists_mem_cell`).  Then `e β_i ≤ c < e β_i + cellLen i`
   (`map_of_mem_cell`, `image_cell`) and `c = e w`.
3. **`i ∈ J` is impossible**: the cell is then inside `Ico u c`, so `w ∈ Ico u c`, so
   `c = e w ∈ Ico u c`.
4. **`i ∉ J` is impossible**: `B := Ico (max (e β_i) u) c` is a subset of the image of cell `i`
   (`e β_i ≤ max`, `c < e β_i + len`), hence disjoint from `A`, hence `A ∪ B ⊆ Ico u c` has volume
   `(c - u) + (c - max (e β_i) u) > c - u` — against `volume (Ico u c) = c - u`.
So `e β_i = c`.

Step 4 is where the earlier plan's "no other cell meets `[u,c)`" lives, and the measure argument
replaces the two topological facts: **do not** try to prove `A = Ico u c`.

### `InFixedCell` is now left-closed (`≤`, not `<`)

The paper's fixed interval is `J_ℓ = [s_{ℓ-1}, s_ℓ)` and a singularity at its left end *belongs* to
it, so `IETDatum.InFixedCell` is now
`∃ l, E.IsFixedCell l ∧ E.mark l.castSucc ≤ D.mark k ∧ D.mark k < E.mark l.succ`.
This is needed by the case analysis (the point produced is a marked point *and* a cell boundary) and
is harmless: `pairSplitting_invariant` still goes through (the `le_of_lt hlow` in its proof is now
the identity, that is the whole change), and `IsPairSplitting` merely gains the boundary points,
which are exactly the ones the invariance argument needs.

### Case 1a is PROVED (`Section3.lean`, axiom-clean)

```lean
theorem IETDatum.comp_toFun_mark_castSucc (D) (E) (k : Fin d) {l : Fin e}
    (hl : imageLeft D.π D.lam k ∈ Ico (E.mark l.castSucc) (E.mark l.succ)) :
    E.toFun (D.toFun (D.mark k.castSucc))
      = imageLeft D.π D.lam k + (imageLeft E.π E.lam l - leftEnd E.lam l)   -- (eq:gfx)

theorem IETDatum.isSplitting_succ (D) {l} (hl : D.IsSplitting l.castSucc) (hfix : D.π l = l) :
    D.IsSplitting l.succ

theorem IETDatum.pairSplitting_of_mark_image (D) (E) (hp : ¬ IsBadParam (D.v, E.v)) {k n}
    (h : E.toFun (D.toFun (D.mark k.castSucc)) = D.mark n.castSucc) :
    IsPairSplitting D E (D.mark n.castSucc)
```

`splitting_of_imageLeft_relation` now also returns `σ l = l` (it was already derived inside by
`perm_eq_of_preimage`, just not exposed), which with `E.IsSplitting l` gives `E.IsFixedCell l` via
`isSplitting_succ`.  Also new: `IsPairSplitting.eq_one_or_mem_markCuts` — a pair-splitting point is
either `1` or a cut of the composition (needed to feed `u ∈ S` to the position lemma).

### What is left in the glue

`exists_pairSplitting_of_invariant` needs `u ∈ S` as a hypothesis (`eq_one_or_mem_markCuts` supplies
it from `IsPairSplitting`, and `block_irreducible_on_good` has that).  Then, with `x, c ∈ S` and
`F x = c` from the position lemma, and `mem_comp_markCuts` classifying `x` and `c`:

* **1a** (`x = D.mark k`, `c = D.mark n`): `pairSplitting_of_mark_image`, **done**;
* **1b** (`x = D.mark k`, `D c = E.mark n`): the relation is
  `imageLeft π λ k + imageLeft σ μ l - leftEnd μ l + imageLeft π λ m - leftEnd λ m = leftEnd μ n`
  with `l` the `E`-cell of `D x` and `m` the `D`-cell of `c` — that is
  `splitting_of_imageLeft_relation_add` with `hn : 0 < n`; it yields `π k = 0`, `π m = m`, `π`
  splits at `m` (so `D.IsFixedCell m`, using `isSplitting_succ`), hence `D` fixes the cell `m` of
  `c`, hence `c = D c = E.mark n.castSucc` by `D c = E.mark n`; with `E.IsSplitting n` that is the
  `E`-side disjunct of `IsPairSplitting`.  `hn` comes from `c > 0` (`0 = E.mark 0` would give
  `D c = 0`, so `c = 0`).
* **2a** (`D x = E.mark j`, `c = D.mark n`): the paper gets `c = 0`, contradicting `c > 0`.
* **2b** (`D x = E.mark j`, `D c = E.mark j'`): the paper reduces it to 1a with `D` and `E`
  exchanged.

## **Lemma 3.2 is PROVED** (this session): `exists_pairSplitting_of_invariant` and the block theorem

`./Build.sh` green, **8** declarations reach `sorryAx` (was 9): `Challenge.lean` 2 (frozen) and
`Section3.lean` 6 (`exists_compPresentation_on_region`, `compLen_injective`,
`compLen_absolutelyContinuous`, `exists_word_trivial_on_block` = Lemma 3.4,
`exists_word_trivial_on_all_of_blocks`, `main_theorem_of_blocks`).

**Axiom-clean, `[propext, Classical.choice, Quot.sound]`**: `exists_pairSplitting_of_invariant` and
**`block_irreducible_on_good`** — i.e. Lemma 3.2 (irreducibility of the pair on a block) is done.

### The pieces (all in `Section3.lean`)

```lean
-- Case 1a: both `x` and `F x` are singularities of `D`
IETDatum.pairSplitting_of_mark_image
-- Case 1b: `x` a singularity of `D`, `c` a preimage of one of `E`
IETDatum.pairSplitting_of_mark_preimage
-- Case 2a: impossible
IETDatum.false_of_preimage_mark        -- with leftEnd_eq_zero_of_imageLeft_eq
-- Case 2b: both preimages of singularities of `E`
IETDatum.pairSplitting_of_preimage_preimage
-- glue
IETDatum.exists_castSucc_mark_of_lt_one -- a marked point below 1 is a left end
IETDatum.exists_mark_of_toFun_eq_zero   -- `D c = 0` makes `c` a marked point (the `n = 0` fallback)
IsPairSplitting.eq_one_or_mem_markCuts  -- pair-splitting points are cuts (feeds `u ∈ S`)
imageLeft_eq_leftEnd_of_splitting       -- `π j = k` + splitting at `k` gives `imageLeft = leftEnd`
isBadParam_swap                         -- `O` is symmetric in the two length vectors (Case 2b)
```

`exists_pairSplitting_of_invariant` now carries `huS : u ∈ S` (the position lemma needs it;
`block_irreducible_on_good` gets it from `IsPairSplitting` and `u < v ≤ 1`).

### Details worth keeping

* **Case 2a is a `False`**, not a pair-splitting conclusion, and it needs `0 < c` (without it the
  relation `imageLeft σ μ l = leftEnd λ n` is satisfiable, e.g. at `c = 0`): `leftEnd D.lam n = 0`
  and `c = D.mark n.castSucc` give `c = 0`.
* **Case 1b's `n = 0` sub-case** is not part of `splitting_of_imageLeft_relation_add` (which needs
  `0 < n`): there `D c = 0`, so `c` is a marked point of `D`
  (`exists_mark_of_toFun_eq_zero`: the cell of `c` has `imageLeft = 0` because `imageLeft ≥ 0` and
  `c + imageLeft = leftEnd ≤ c`), and Case 1a applies.
* Cases 1b/2b conclude via the `E`-side disjunct of `IsPairSplitting`, using
  `isSplitting_succ` to turn (`E` splits at `n`, `E.π ? = ?`) into `E.IsFixedCell`; Case 2b needs
  `splitting_of_imageLeft_relation` with `D` and `E` exchanged, hence `isBadParam_swap`.
* The assembly classifies `x` and `c` with `mem_comp_markCuts` and converts every marked point below
  `1` to a cell left end with `exists_castSucc_mark_of_lt_one`; all four cases then dispatch on the
  four lemmas above.

**Remaining for Theorem 1.1**: `exists_compPresentation_on_region`, Lemma 3.1
(`compLen_injective`, `compLen_absolutelyContinuous`), Lemma 3.4, the assembly
`exists_word_trivial_on_all_of_blocks` and `main_theorem_of_blocks`.

## Section 3 moved to free parameters, and `IsAffineFn` dropped (this session, user request)

**`O` is now a set of free parameters everywhere**: `O : Set (PReal d e)`, with the hypothesis
`hO : O ⊆ goodParams d e` (or the field `subset_good : O ⊆ goodParams d e` of `GoodRegion`), instead
of `O : Set ((Fin d → ℝ≥0) × (Fin e → ℝ≥0))` with `∀ p ∈ O, toReal p ∈ goodParams d e`.  `toReal`
now only appears where the `ℝ≥0` length vectors are unavoidable (`IsBadParam`, `isBadParam_iff`,
`isBadParam_mem_badSet`, `ae_goodParams`, `relation_of_good`).

**`IsAffineFn` is gone.**  Its replacement is the type abbreviation

```lean
abbrev ParamAffine (d e : ℕ) := PReal d e →ᵃ[ℝ] ℝ          -- Mathlib's `AffineMap`
```

so the singularity list of a region is `s : Fin (n + 1) → ParamAffine d e` — an affine-map condition
on the *whole* list, not a coordinate-by-coordinate check — and `measurable_paramAffine`
(`(AffineMap.continuous_of_finiteDimensional L).measurable`) supplies the measurability that
`IsAffineFn.measurable` used to.

New/changed statements:

```lean
theorem exists_compPresentation_on_region (π) (σ) (O : Set (PReal d e))
    (hOc : IsPreconnected O) (hOne : O.Nonempty) (hO : O ⊆ goodParams d e) :
    ∃ (n) (s : Fin (n + 1) → ParamAffine d e) (ρ), n = d + e - 1 ∧
      ∀ q ∈ O, ∀ (hl : simplexMap d q.1 ∈ simplex d) (hm : simplexMap e q.2 ∈ simplex e),
        IsCompPresentation (simplexMap d q.1) π (simplexMap e q.2) σ hl hm n (fun k => s k q) ρ

structure GoodRegion (π) (σ) (q₀ : PReal d e) where
  O : Set (PReal d e); isOpen_O; mem_O : q₀ ∈ O; subset_good : O ⊆ goodParams d e
  n; s : Fin (n + 1) → ParamAffine d e; ρ; card_eq; pres

theorem compLen_injective ... (O : Set (PReal d e)) (hO : O ⊆ goodParams d e) ...
    ∀ q ∈ O, ∀ q' ∈ O, (∀ i, s i.succ q - s i.castSucc q = s i.succ q' - s i.castSucc q') → q = q'

theorem compLen_absolutelyContinuous ... :
    (volume.restrict O).map (fun q => compLenVec s hmono q) ≪ simplexVolume n

theorem ae_of_ae_compLen (O : Set (PReal d e)) ... :
    ∀ᵐ q ∂(volume.restrict O), P (compLenVec s hmono q)

noncomputable def compLenVec (s : Fin (n + 1) → ParamAffine d e) (hmono) (q : PReal d e) : Fin n → ℝ≥0
```

`ae_exists_goodRegion` is now stated on the free-coordinate measure
`(volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))` and **proved**
(`sorry`-free, though it reaches `sorryAx` through `exists_compPresentation_on_region`), with the ball
`Metric.ball q ε` as the region: `convex_ball q ε |>.isPreconnected` replaces the old
`toReal ⁻¹' ball` + segment argument.

**Deleted** (no longer used): `IsAffineFn`, `IsAffineFn.measurable`, `seg`, `toReal_seg`, `seg_zero`,
`seg_one`, `unitNN`, `coe_unitNN`, `unitNN_le_one`, `continuous_unitNN`, `continuous_seg_path`,
`isPathConnected_preimage_ball`, `isPreconnected_preimage_ball`.  `exists_ball_subset_goodParams` is
now the `PReal` statement `∃ ε, 0 < ε ∧ Metric.ball q ε ⊆ goodParams d e`.

**Added**: `ae_mem_simplexRegion_prod` (a.e. point of the product measure is in
`simplexRegion d ×ˢ simplexRegion e`) and `ae_goodParams_real` (the free-coordinate form of
`ae_goodParams`); `ae_goodParams` now *derives* from `ae_goodParams_real` by pushing forward along
`simplexMap d × simplexMap e`, which removed the duplicated region argument.

Build green at **8** `sorryAx` (unchanged), `Section3.lean` linter-clean.

## Lemma 3.1 (`compLen_injective`): what is proved, and the exact remaining gap (this session)

### Proved (axiom-clean, `Section3.lean`)

```lean
theorem eq_of_increments_eq {n : ℕ} {s t : Fin (n + 1) → ℝ} (hs0 : s 0 = t 0)
    (h : ∀ i : Fin n, s i.succ - s i.castSucc = t i.succ - t i.castSucc) : s = t

theorem simplexMap_mem_simplex' {n : ℕ} [NeZero n] {v : Fin (n - 1) → ℝ}
    (hpos : ∀ i, 0 < v i) (hsum : ∑ i, v i < 1) : simplexMap n v ∈ simplex n
```

and `compLen_injective` is now *proved down to one inequality-free gap*: given
`hν : ∀ i, s i.succ q - s i.castSucc q = s i.succ q' - s i.castSucc q'`, we have

* **the marked positions agree**: `(fun k => s k q) = fun k => s k q'` (`eq_of_increments_eq` on
  the two presentations' `zero` fields) — this is the "position machinery" step;
* hence (with `ρ`) the composition `g ∘ f` is the **same function** at `q` and at `q'`;
* the remaining goal is `simplexMap d q.1 = simplexMap d q'.1 ∧ simplexMap e q.2 = simplexMap e q'.2`
  (one `sorry`), from which `q = q'` follows via `toReal_simplexMap` and the region hypothesis.

### Statement changes made

* `compLen_injective` (and `compLen_absolutelyContinuous`) gained
  `hreg : ∀ q ∈ O, q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e`.  Two reasons: (i) `q = q'` from
  `λ = λ'` needs `toReal (simplexMap d q.1, simplexMap e q.2) = q`, i.e. *strict* positivity, which
  `O ⊆ goodParams` does not give; (ii) strict positivity is what makes the cells of `f` and `g`
  nondegenerate.
* **The truncation in `simplexMap` is harmless**: `simplexMap d v ∈ simplex d` forces `0 ≤ v i`
  (write `∑ (v i)⁺ + (1 - ∑ v)⁺ = 1`, which forces `∑ (v i)⁻ = 0`).  Not yet formalised; it means
  the only real reason for `hreg` is strictness.

### The gap, precisely

`ν` determines `s`, and `(s, ρ)` determines `F = g ∘ f` as a function.  So the missing statement is
**uniqueness of the factorisation `F = g ∘ f` at a good parameter**: if `g ∘ f = g' ∘ f'` with `f`,
`f'` both `d`-interval exchanges of permutation `π` and `g`, `g'` both `e`-interval exchanges of
permutation `σ`, then `f = f'`.  (The bad case — `λ = (1/4,3/4), μ = (3/4,1/4)` against
`λ = μ = (1/2,1/2)`, both factorising the identity — is excluded by `O`.)

Concretely the proof needs the **monotone map `Fin n → Fin d`** giving, for each marked cell, the
`f`-cell containing it (`f`'s cuts are among the marked points because `f` is a translation on each
marked cell; the map records *which*).  `λ i` is then the sum of `ν` over the block where that map is
`i`.  This map is locally constant on `O` (it can only change where two marked points coincide or a
`f`-displacement coincides with another, all hyperplane conditions), so on a preconnected `O` it is
constant — but it is **not** a function of `ν` at a single point.

Two ways forward, for the user to choose:

1. **Data**: add to `IsCompPresentation` the fields `a : Fin n → Fin d`, `b : Fin n → Fin e` with
   `D.mark (a k).castSucc ≤ s k.castSucc < D.mark (a k).succ` (and the analogue for the image), plus
   monotonicity of `a`.  `compLen_injective` then says: same `ν` and same `a` (hence same cell of
   `f`) implies same `q` — provable, and `λ i = ∑_{k : a k = i} ν k` by construction.
2. **Constancy**: assume `IsPreconnected O` and prove that `a` is constant on `O`, e.g. because
   `{q ∈ O : a k = i}` is open and closed in `O` (openness needs the strict inequalities to persist;
   closedness needs `O` to avoid the hyperplanes where the inequalities degenerate).  This is the
   paper's "the pattern is constant over `O`", and it is more work but keeps `IsCompPresentation`
   as it is.

Option 1 is likely the shorter route to a proved `compLen_injective` and to the explicit inverse map
`λ = A ν` needed by `compLen_absolutelyContinuous`; option 2 is more faithful to the paper's phrasing.

## Lemma 3.1: the combinatorial type is now data (this session, user's option 1)

### `a` and `b` cannot be fields of `IsCompPresentation`

`IsCompPresentation` is `Prop`-valued, and Lean refuses data fields in a `Prop` structure
("failed to generate projection `IsCompPresentation.a` ... field must be a proof").  So the type is
carried by a **`Prop`-valued predicate on given functions**, which is the faithful realisation of the
option:

```lean
def IsCompType {d e n : ℕ} [NeZero d] [NeZero e] (lam : Fin d → ℝ≥0) (π : Equiv.Perm (Fin d))
    (hl : (∑ i, lam i) = 1) (mu : Fin e → ℝ≥0) (s : Fin (n + 1) → ℝ)
    (a : Fin (d + 1) → Fin (n + 1)) (b : Fin (e + 1) → Fin (n + 1)) : Prop :=
  a (Fin.last d) = Fin.last n ∧ (∀ i : Fin d, s (a i.castSucc) = leftEnd lam i) ∧
    b (Fin.last e) = Fin.last n ∧ ∀ j : Fin e, mkIET1 lam π hl (s (b j.castSucc)) = leftEnd mu j
```

* `a i` is the marked index of the `i`-th cut of `f` (`leftEnd lam i`); `a (last) = n` is the point
  `1`.  The marked cells with index in `[a i.castSucc, a i.succ)` are exactly those inside the `i`-th
  cell of `f`, so `λ i` is the sum of their lengths.
* `b j` is the marked index of `f⁻¹` of the `j`-th cut of `g`.

### Where they live now

* `exists_compPresentation_on_region` returns `a`, `b` and asserts `IsCompType` at every `q ∈ O`:
  `∃ n s ρ a b, n = d+e-1 ∧ ∀ q ∈ O, ∀ hl hm, IsCompPresentation … ∧ IsCompType …`;
* `GoodRegion` has fields `a`, `b`, `type` (and `ae_exists_goodRegion` fills them, still proved);
* both statements remain `Prop`-valued and they are still `theorem`s — making `IsCompPresentation`
  `Type`-valued does not work: `theorem` requires a proposition and the `∧` chains would become
  `Σ'`, so `exists_compPresentation_on_region` would have to be a `def`.

### What is left for `compLen_injective`, and why it is now short

With `a` and `b` as region data, the two facts needed are *symmetric block-sum lemmas* at a single
presentation:

```lean
(lam i : ℝ) = ∑ k ∈ {k : Fin n | (a i.castSucc).val ≤ k.val < (a i.succ).val}, (s k.succ - s k.castSucc)
(mu j : ℝ)  = ∑ k ∈ {k : Fin n | (b j.castSucc).val ≤ k.val < (b j.succ).val}, (s k.succ - s k.castSucc)
```

and then `compLen_injective` is *immediate*: at `q` and `q'` the same `a`, `b` give the same blocks,
and `ν` is the same, so both sums coincide — no combinatorial argument at a single point any more.

* the `λ` one is **telescoping**: `∑_{k∈Ico A B} (S (k+1) - S k) = S B - S A` with
  `S m := s ⟨m, _⟩`, and the endpoints are `leftEnd lam i` and `leftEnd lam (i+1)` (`a_val`, and
  `a_top` for `i = last`).  Some `Fin n` ↔ `Finset.Ico` index bookkeeping.
* the `μ` one needs that `f` preserves Lebesgue measure: each marked cell of the block is mapped by a
  translation onto a piece of the `j`-th cell of `g`, so the block's total length is `μ j`
  (`Equiv.IsIET.measure_preimage` in `IET.lean`, plus
  `IsCutSet.sum_cellLen_filter`/`image_cell` or a direct sum over the block).

Both are mechanical; the design question that blocked them is settled.

## Block-sum lemmas: helpers proved, and a correction to the `b` encoding (this session)

### Proved and in the library (axiom-clean)

```lean
theorem sum_Ico_succ_sub (S : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) :
    ∑ k ∈ Finset.Ico A B, (S (k + 1) - S k) = S B - S A      -- telescoping
noncomputable def markExt (s : Fin (n + 1) → ℝ) (m : ℕ) : ℝ -- `ℕ`-indexed extension
theorem markExt_of_le (hm : m ≤ n) : markExt s m = s ⟨m, _⟩
theorem leftEnd_eq_upperEnd_of_succ (h : i.val + 1 < n) : leftEnd lam ⟨i.val+1, h⟩ = upperEnd lam i
```

Two Lean notes: `Finset.sum_Ico_eq_sub` takes `(f) {m n} (hm : m ≤ n)`, and
`Finset.sum_range_sub S B` is the lemma for the summand `S (k+1) - S k` (the version with
`fun k => S (k+1)` produces `S (k+2) - S (k+1)` and does not fire).

### `lam_eq_sum`: stated, telescoping done, two mechanical errors left

```lean
theorem IsCompPresentation.lam_eq_sum (P : IsCompPresentation lam π mu σ hl hm n s ρ)
    (T : IsCompType lam π hl mu s a b) (i : Fin d) :
    (lam i : ℝ) = ∑ k ∈ Finset.Ico (a i.castSucc).val (a i.succ).val,
      (markExt s (k + 1) - markExt s k)
```

Stating the sum over `Finset.Ico` (and not over `{k : Fin n | …}`) removes the `Fin n` ↔ `ℕ`
conversion entirely — that is the lesson of this round.  The proof is: `s (a i.castSucc) =
leftEnd lam i` (`a_val`), `s (a i.succ) = upperEnd lam i` (either `a_val` at the next cut plus
`leftEnd_eq_upperEnd_of_succ`, or, at the last cell, `a_top` + `P.top` + `∑ lam = 1`), then
telescoping and `upperEnd_eq`.  What remains: the `omega` in the last-cell case (`upperEnd lam i =
∑ lam` from `i.val + 1 = d`, done inline) and the `hAB : (a i.castSucc).val ≤ (a i.succ).val`
(string it through `P.mono.le_iff_le`).

### The `b` encoding is wrong for the `mu` formula

`b j` (the marked index of `f⁻¹(leftEnd mu j)`) gives the *consecutive* block of marked cells
between two preimage-cuts, and its total length is `s (b j.succ) - s (b j.castSucc)` — but that is
**not** `mu j`: `f` shuffles the cells, so the marked cells whose images lie in the `j`-th cell of
`g` are a *scattered* set, not a consecutive block.  What the `mu` formula needs is the **cell map**

```lean
B : Fin n → Fin e        -- the cell of `g` containing the image of the `k`-th marked cell
B_mem : ∀ k, leftEnd mu (B k) ≤ f (s k.castSucc) ∧ f (s k.castSucc) + ν k ≤ leftEnd mu (B k) + mu (B k)
```

and then `mu j = ∑_{k : B k = j} ν k`, by: the preimage of the `j`-th cell of `g` is exactly
`⋃_{k : B k = j} marked cell k` (containment gives `⊆`; disjointness of the `g`-cells gives `⊇`), so
its volume is `∑_{k : B k = j} ν k` (the images are disjoint intervals of lengths `ν k`), and this
equals `mu j` by `Equiv.IsIET.measure_preimage` (`f` preserves Lebesgue measure).  Note the `λ`
formula did *not* need a cell map because the `a`-blocks are consecutive, so telescoping sufficed.

So `IsCompType` should carry `B` (with `B_mem`) in place of — or in addition to — `b`; the `b`
cut-index data is not needed for either sum.  `compLen_injective` still carries one `sorry`.

Build green at **8** `sorryAx`, `Section3.lean` linter-clean.

## Lemma 3.1 is **PROVED** (this session): `compLen_injective` and absolute continuity

Build green at **6** `sorryAx` (was 8; `Challenge.lean` 2 frozen, `Section3.lean` 4).

### New in `Section3.lean`, all axiom-clean (`[propext, Classical.choice, Quot.sound]`)

```lean
theorem IsCompPresentation.lam_eq_sum (P) (T : IsCompType lam π hl mu s a B) (i : Fin d) :
    (lam i : ℝ) = ∑ k ∈ Finset.Ico (a i.castSucc).val (a i.succ).val,
      (markExt s (k + 1) - markExt s k)
theorem IsCompPresentation.mu_eq_sum (P) (T : IsCompType lam π hl mu s a B) (j : Fin e) :
    (mu j : ℝ) = ∑ k ∈ Finset.univ.filter (fun k : Fin n => B k = j),
      (s k.succ - s k.castSucc)
theorem disjoint_leftEnd_Ico / leftEnd_Ico_subset / volume_leftEnd_Ico
theorem compLen_injective (π σ O hreg n s ρ a B hpres htype) :
    ∀ q ∈ O, ∀ q' ∈ O, (∀ i, s i.succ q - s i.castSucc q = s i.succ q' - s i.castSucc q') → q = q'
-- absolute continuity of the pushforward, in `section AffineAbsoluteContinuous`
theorem injective_linear_of_injOn, absolutelyContinuous_map_affine, sum_fin_sub,
noncomputable def compLenAffine, compLenAffine_apply,
theorem GoodRegion.sum_compLenAffine, GoodRegion.compLen_eq_simplexMap,
theorem GoodRegion.compLen_absolutelyContinuous (hreg) (hmono) :
    (volume.restrict G.O).map (fun q => compLenVec G.s hmono q) ≪ simplexVolume G.n
```

* **`lam_eq_sum`** is telescoping: `sum_Ico_succ_sub` on `markExt s`, with the two endpoints
  `s (a i.castSucc) = leftEnd lam i` and `s (a i.succ) = upperEnd lam i`.  The second has two cases
  (`i.val + 1 < d`: `hval` at the next cut + `leftEnd_eq_upperEnd_of_succ`; `i = last`: `htop`,
  `P.top`, `upperEnd_of_max`, `∑ lam = 1`).
* **`mu_eq_sum`** is *not* telescoping (the `B`-block is scattered).  Proof: `f = mkIET1 lam π hl`
  preserves Lebesgue measure (`Equiv.IsIET.measure_preimage` + `isCutSet_mkIET1`), and
  `f ⁻¹' [leftEnd mu j, leftEnd mu j + mu j) ∩ [0,1) = ⋃_{k : B k = j} [s k, s (k+1))`:
  `⊇` from the two-sided interval condition of `IsCompType`, `⊆` from `exists_cell_of_strictMono`
  plus the disjointness of the cells of `g` (`disjoint_leftEnd_Ico`).  Then
  `measure_biUnion_finset`, `Real.volume_Ico`, `ENNReal.ofReal_sum_of_nonneg`, `ofReal_eq_ofReal_iff`.
  **Note the preimage is taken under `f`, not under `g ∘ f`** — the `j`-th cell of `g` is a *domain*
  cell, not an image cell, and `B` records where `f` sends each marked cell.
* **`compLen_injective`** no longer needs `hO : O ⊆ goodParams`!  With `a`, `B` fixed on `O`, both
  `λ` and `μ` are explicit sums of the same increments `ν`, so `ν = ν'` forces `λ = λ'`, `μ = μ'`,
  and `toReal_simplexMap` (fed by `hreg`) gives `q = q'`.  The old counterexample
  (`λ = 3/10, μ = 1/10` against `λ = 1/10, μ = 3/10`, `π = σ` the transposition) is separated by
  `B` itself.  **Goodness is now used only where it is mathematically needed.**
* **Absolute continuity**: `compLenAffine G.s` sends `q` to the first `n - 1` lengths (the last is
  `1 - ∑`), so `compLenVec = simplexMap n ∘ compLenAffine`.  It is injective on `G.O` by
  `compLen_injective`, its linear part is therefore injective (`injective_linear_of_injOn`: a small
  multiple of a kernel vector stays in the open set), and
  `LinearMap.linearEquivOfInjective` + `Measure.MapLinearEquiv.isAddHaarMeasure` +
  `Measure.absolutelyContinuous_isAddHaarMeasure` give `(volume.restrict O).map A ≪ volume`.  The
  image lies in `simplexRegion n` (`hmono` for positivity, `sum_compLenAffine` for the total), which
  restricts the absolute continuity to `volume.restrict (simplexRegion n)`, and then
  `Measure.AbsolutelyContinuous.map` pushes it to `simplexVolume n`.

### Lean gotchas paid for here

* **`volume` on `PReal d e` is not an `IsAddHaarMeasure` by instance**: there is no product instance.
  Build it locally with
  `have : Measure.IsAddHaarMeasure (volume : Measure (PReal d e)) := by have : IsAddHaarMeasure
  ((volume : Measure (Fin (d-1) → ℝ)).prod (volume : Measure (Fin (e-1) → ℝ))) :=
  { toIsFiniteMeasureOnCompacts := inferInstance, toIsAddLeftInvariant := inferInstance,
    toIsOpenPosMeasure := inferInstance }; infer_instance`.
  `IsFiniteMeasureOnCompacts`, `Measure.IsAddLeftInvariant` and `Measure.IsOpenPosMeasure` *do* have
  product instances (with variable indices), `IsAddHaarMeasure` does not.
* the classes are `Measure.IsAddHaarMeasure`, `Measure.IsAddLeftInvariant`,
  `Measure.IsOpenPosMeasure` (namespace `Measure`), but `IsFiniteMeasureOnCompacts` is at root.
* `Measure.IsAddRightInvariant.map_add_right_eq_self` takes `μ` **implicitly**: write
  `... (μ := (volume : Measure F)) (A 0)`.
* `AffineMap` has a `Sub` *instance* but no `AffineMap.sub` projection: write `f - g`.
* `A x = A.linear x + A 0` comes from `AffineMap.map_vadd A 0 x` (`map_vadd` is
  `f (v +ᵥ p) = f.linear v +ᵥ f p`), and `+ᵥ` on a group is `+`: `rw [vadd_eq_add, add_zero] at h`.
* `Measure.absolutelyContinuous_isAddHaarMeasure μ ν` needs `[SigmaFinite μ]`, which follows from
  `IsAddHaarMeasure (volume.map e)` (`MeasurableSpace`-only `volume` needs `[MeasureSpace E]`).
* `simplexMap`'s `if h : i.val + 1 = n` needs `rw [dif_pos hk]`/`dif_neg hk`; the companion
  `Real.coe_toNNReal _ h` then needs the nonnegativity of `1 - ∑`, i.e. `∑ < 1`, i.e. `hmono` plus
  `sum_compLenAffine`.
* in a goal `↑⟨x, h⟩ = x` after `simp only`, close with `rfl` (`NNReal.coe_mk` is not a `simp`
  lemma here); `hmono q (Fin.castSucc_lt_succ (i := k))` produces a beta-redex, so `beta_reduce at`
  and then `simp only [Fin.succ_mk, Fin.castSucc_mk]` before `linarith`.
* `Measure.map_congr (h : f =ᵐ[μ] g)` is the way to use an identity that holds only on `O`; and
  `rw [← Measure.map_map]` needs the goal in the exact `g ∘ f` shape, so `change` to it first.

## The assembly of Theorem 1.1 is **PROVED** (this session): `exists_word_trivial_on_all_of_blocks`

Build green at **5** `sorryAx` (`Challenge.lean` 2 frozen, `Section3.lean` 3:
`exists_compPresentation_on_region`, `exists_word_trivial_on_block`, `main_theorem_of_blocks`).

New, all axiom-clean: `commWord_apply_eq_self_left`, `commWord_apply_eq_self_right`,
`conj_apply_eq_self`, `evalWord_mapsTo_of_invariant`, `exists_word_trivial_on_all_of_blocks`
(plus `private def BlockIn`, `private def BlocksIn`).

The paper's argument (end of §4): induct over the blocks, keeping a nontrivial word `w'` trivial on
`P_1 ∪ ⋯ ∪ P_i`.  With `w` trivial on `P_{i+1}`, the commutator `[w', w]` is trivial on the union
**because a commutator is trivial wherever one of its factors is**, and if that word happens to be
`1` use `[x⁻¹w'x, w]` or `[y⁻¹w'y, w]` — `exists_nontrivial_commutator` (Lemma 2.7) says one of the
three is nontrivial.  Two facts make the conjugates work, and both are worth naming:

* **`commWord_apply_eq_self_left`**: if `a` is the identity on `S` and both `a` and `b` map `S` into
  itself, then `commWord a b` is the identity on `S`.  (`commWord a b = a⁻¹ * b⁻¹ * a * b`, and
  `a⁻¹` is then also the identity on `S`.)  Dually `commWord_apply_eq_self_right` for `b`.
* **`evalWord_mapsTo_of_invariant`**: every word preserves a set that both generators preserve *in
  both directions* — proved by `FreeGroup.induction_on` (the set of such words is a subgroup
  containing the two generators).  The two-sided hypothesis is needed: `evalWord u⁻¹` must preserve
  the set, and that is not automatic from one-sided invariance.  Here it comes from the `↔` in
  `hfu`/`hgu`.
* `conj_apply_eq_self`: `f⁻¹ * g * f` is the identity on `S` if `g` is and `f` maps `S` into `S`.

`BlockIn u v i` is `[u i, v i) ∩ [0,1)`, `BlocksIn u v J` is the union over `J`.  The `[0,1)`
intersection is what makes the invariance hypotheses (`hfu`, `hgu`) applicable; the blocks
themselves may stick out of `[0,1)`, where the exchanges are the identity anyway.

The final step: `key Finset.univ` gives a nontrivial word trivial on `⋃_{i} BlockIn u v i`, which
`hcover` makes all of `[0,1)`; an `IET 0 1` is the identity outside `[0,1)`
(`IsIET.eq_of_notMem`), so `IET.ext` gives `evalWord w D.toIET E.toIET = 1`.

### Lean notes

* `IET.apply_symm_apply'` (`f (f⁻¹ x) = x`) is the lemma for the *group* inverse; plain
  `apply_symm_apply` is stated with `f.toEquiv.symm` and does not match `f⁻¹`.
* `Finset.not_mem_empty` does not exist under that name — use `by simp`.
* when several sets are in play, `commWord_apply_eq_self_left (S := …)` must be given `S`
  explicitly, otherwise the `⟨…⟩` for `x ∈ S` has no expected type.
* `Finset.induction`'s step gets the `i ∉ J` proof as the third argument (here named `hi`).

## Local form of the presentation (this session, user request)

`exists_compPresentation_on_region` (preconnected `O`) is **replaced** by

```lean
theorem exists_compPresentation_on_ball (π σ) (q₀ : PReal d e)
    (hq₀ : q₀ ∈ goodParams d e) (hr₀ : q₀.1 ∈ simplexRegion d ∧ q₀.2 ∈ simplexRegion e) :
    ∃ ε > 0, Metric.ball q₀ ε ⊆ goodParams d e ∧
      (∀ q ∈ Metric.ball q₀ ε, q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e) ∧
      ∃ n s ρ a B, n = d + e - 1 ∧ ∀ q ∈ ball, IsCompPresentation … ∧ IsCompType …
```

The reason this is the right (and strictly easier) statement: the pattern of the singularities is
determined by finitely many **strict inequalities** between affine functions of the parameters, and
each of those conditions is *open*.  So no connectedness argument (open-and-closed) is needed, and
the ball can be shrunk at will.  The preconnectedness hypothesis of the old statement is gone.

Consequences already in the library:

* `GoodRegion` gained a field `subset_region : ∀ q ∈ O, q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e`
  — the `hreg` that `compLen_injective` and `compLen_absolutelyContinuous` take is now *part of the
  region data*, instead of being an extra hypothesis the caller has to conjure.
* `exists_goodRegion` (a good region around any good point of the open simplex region) and
  `ae_exists_goodRegion` are **proved** from the local statement in three lines — no `convex_ball`,
  no `IsPreconnected`, no `toReal` (both are axiom-clean modulo the one `sorry`).
* `simplexMap_of_lt` and **`leftEnd_simplexMap`**: on the open simplex region,
  `leftEnd (simplexMap d v) i = ∑ j : Fin (d-1), if j.val < i.val then v j else 0`.  This is the
  paper's first sentence in the proof of Lemma 3.5 — "the singularities of `gf` are located at
  points of the form `∑_{i<n} λᵢ` … these expressions are affine" — for the `S_f` half.
  Axiom-clean.

### What is still missing in `exists_compPresentation_on_ball`, in the order to do it

1. **The affine functions.** `cutAffine d i : ParamAffine d e` packaging `leftEnd_simplexMap`
   (`q ↦ ∑_{j.val<i.val} q.1 j`, a sum of coordinate projections, built with `AffineMap.pi` /
   `LinearMap.toAffineMap`); the same for `imageLeft π` (`imageLeft_simplexMap`), and hence for
   `translationVector π lam k` — all affine on the region.
2. **The cell index of `f` carrying each singularity of `g`.** For `j : Fin e`, `j ≠ 0`, the point
   `y = leftEnd μ j` lies in the image interval of a unique cell `k(j)` of `f`:
   `imageLeft k(j) < y < imageLeft k(j) + λ_{k(j)}`.  The *strict* inequality is where `goodParams`
   enters: `y = imageLeft ℓ` would be a relation with coefficients in `{-1,0,1}`, excluded by
   `coeffs_zero_of_good`.  Then `f⁻¹ y = y - translationVector π λ k(j)` by
   `mkIETFun_of_mem` + `idx_eq`, and this is affine in the parameters.
3. **Sorting.** Order the `d-1` functions of step 1 and the `e-1` functions of step 2 at `q₀`; a small
   ball keeps the order (`StrictMono` of the list is an open condition).  `s` = the sorted list.
4. **`a`, `B`, `ρ`.** `a i` = position of `leftEnd λ i` in `s`; `B k` = the cell of `g` containing
   `f (s k.castSucc)` (step 2's `k(·)` in the other direction: which cell of `g` contains the image
   of each marked cell, again finitely many strict inequalities); `ρ` from the images of the cells.
5. **The `IsCompPresentation` fields.** `zero`/`top` from the sums; `mono` from step 3; `cell`,
   `f_transl`, `g_transl` by the computations `mkIETFun_leftEnd`, `mkIETFun_of_mem`, `idx_eq`;
   `card_eq` from `(d-1) + (e-1) + 1 = d + e - 1` and the disjointness of the two singularity sets
   (again `goodParams`).

Steps 1 and 2 are the bulk; step 3–5 are bookkeeping on `Finset`/`Fin` indices.

## Step 2 of the local presentation: singularities of `g` inside cells of `f` (this session)

All new declarations below are **axiom-clean** (`[propext, Classical.choice, Quot.sound]`); build
green at 5 `sorryAx`, linter-clean.

### The goodness lemma, in the right generality

```lean
theorem leftEnd_ne_sum_lam_of_good (hp : ¬ IsBadParam (toReal p)) (hl : p.1 ∈ simplex d)
    (hm : p.2 ∈ simplex e) {j : Fin e} (hj : j ≠ 0) (S : Finset (Fin d)) :
    leftEnd p.2 j ≠ ∑ i ∈ S, (p.1 i : ℝ)
theorem leftEnd_ne_leftEnd_of_good … (k : Fin d) : leftEnd p.2 j ≠ leftEnd p.1 k
```

The `Finset` form is what is actually needed: `S = {i | i < k}` says *no cut of `g` is a cut of
`f`*, and `S = {i | π i < m}` says *no cut of `g` is a left end of an image interval of `f`*.  Both
occur, and both are the same relation `∑_{i<j} μᵢ - ∑_{i∈S} λᵢ = 0` with coefficients in `{0,1}`,
so `relation_of_good` forces the coefficient function of `μ` to be constant in its index — it is
`1` at `0` and `0` at `lastIdx e` because `j ≠ 0`.  **Goodness is used exactly once** in the whole
step, here.

### Step 2

```lean
theorem exists_lt_imageLeft_of_good (hp) (hl) (hm) (hpos : ∀ i, 0 < p.2 i) (π) (hj : j ≠ 0) :
    ∃ k : Fin d, imageLeft π p.1 k < leftEnd p.2 j ∧
      leftEnd p.2 j < imageLeft π p.1 k + (p.1 k : ℝ)
theorem mkIET1_inv_of_lt_imageLeft (hl) (h1 : imageLeft π p.1 k < y)
    (h2 : y < imageLeft π p.1 k + (p.1 k : ℝ)) :
    (mkIET1 p.1 π hl)⁻¹ y = y - translationVector π p.1 k
theorem exists_lt_imageLeft_simplexMap (hq : q ∈ goodParams d e) (hr) (π) (hl) (hm) (hj : j ≠ 0) :
    ∃ k : Fin d, imageLeft π (simplexMap d q.1) k < leftEnd (simplexMap e q.2) j ∧
      leftEnd (simplexMap e q.2) j < imageLeft π (simplexMap d q.1) k + (simplexMap d q.1 k : ℝ) ∧
      (mkIET1 (simplexMap d q.1) π hl)⁻¹ (leftEnd (simplexMap e q.2) j)
        = leftEnd (simplexMap e q.2) j - translationVector π (simplexMap d q.1) k
```

Existence of `k` is `idx` applied to the **image** lengths `imageLengths π p.1` (the image intervals
are the cells of the reordered lengths), then `k = π.symm m` and `imageLeft_eq_leftEnd` converts.
The strict inequality at the left end is `leftEnd_ne_sum_lam_of_good` with `S = {i | π i < m}`.
The inverse formula: `x := y - translationVector π p.1 k` lies in the `k`-th cell, `idx_eq` gives
`idx p.1 (x - 0) = k`, `mkIETFun_of_mem` gives `f x = x + tv = y`, and `IET.symm_apply_apply`
concludes.  `pos_simplexMap` supplies the positivity of the coordinates of `simplexMap` on the
region (needed only to know `leftEnd μ j < 1`, i.e. that `j ≠ 0` is not degenerate).

### The cuts of `f` as affine functions

```lean
noncomputable def leftCoordAffine (j : Fin (d - 1)) : ParamAffine d e := ((proj j).comp (fst …)).toAffineMap
noncomputable def cutAffine (i : Fin d) : ParamAffine d e := ∑ j, if j.val < i.val then leftCoordAffine j else 0
theorem cutAffine_apply …
theorem cutAffine_eq_leftEnd (hq : q.1 ∈ simplexRegion d) (i : Fin d) :
    cutAffine (e := e) i q = leftEnd (simplexMap d q.1) i
```

**Lean trap paid for**: there is no `AffineMap.coe_sum`/`sum_apply`, so `(∑ j, f j) q` does *not*
rewrite by `Finset.sum_apply` (the coercion `AffineMap → function` blocks the match).  The way out is
`cutAffine_apply_aux`, an induction on the `Finset` inside which `(f + g) q = f q + g q` and
`(0 : PReal d e →ᵃ[ℝ] ℝ) q = 0` are `rfl`.

### What is still missing, precisely

1. the affine packaging of `imageLeft π (simplexMap d q.1) k` — same shape, but one term of the sum
   is the **last** coordinate `1 - ∑` (when `π (last) < π k`), which is still affine; the case
   `d = 1` (no free coordinate at all) has to be split off because `lastIdx` does not exist there;
2. **local constancy of `k(j)`** on a ball: strict containment at `q₀` plus continuity of the two
   affine functions (i.e. `AffineMap.continuous_of_finiteDimensional`) keeps it on a small ball;
3. sorting the `d-1` functions `cutAffine i` (`i ≠ 0`) and the `e-1` functions
   `q ↦ leftEndAffine j q - imageLeftAffine k(j) q + cutAffine …` by their values at `q₀`;
4. `a`, `B`, `ρ` and the `IsCompPresentation` fields.

## Items 1–2 done, item 3 started (this session)

All new declarations are axiom-clean; build green at 5 `sorryAx`, linter-clean.

### Item 1 — the images of the cells of `f` are affine

```lean
theorem AffineMap.sum_apply (s : Finset ι) (F : ι → P1 →ᵃ[k] V2) (q : P1) :
    ((s.sum F : P1 →ᵃ[k] V2)) q = s.sum (fun i => F i q)
noncomputable def imageLenAffine (j : Fin d) : ParamAffine d e   -- λ_j: free coord, or 1 - ∑ at the last
theorem imageLenAffine_apply_last / _apply_free / imageLenAffine_eq   -- = ↑(simplexMap d q.1 j) on the region
noncomputable def imageLeftAffine (π) (k : Fin d) : ParamAffine d e
theorem imageLeftAffine_apply
theorem imageLeftAffine_eq (hq : q.1 ∈ simplexRegion d) (k) :
    imageLeftAffine π k q = imageLeft π (simplexMap d q.1) k
noncomputable def cutAffineRight (j : Fin e) : ParamAffine d e     -- the cuts of `g`
theorem cutAffineRight_eq_leftEnd
theorem isOpen_simplexRegion
```

`AffineMap.sum_apply` is the missing Mathlib lemma that `Finset.sum_apply` does not cover (the
coercion `AffineMap → function` blocks it); it is what makes `(∑ j, if c then f j else 0) q`
evaluate.  `cutAffine_apply` is now proved from it and the old `cutAffine_apply_aux` is gone.

**Lean trap**: in `if c then … else …` (without naming the hypothesis) the else branch gets *no*
`¬ c` hypothesis, so `omega` cannot prove `j.val < d - 1` there; write `if h : c then … else …`.

### Item 2 — the preimages of the cuts of `g`, and their local constancy

```lean
noncomputable def preimageCutAffine (π) (j : Fin e) (k : Fin d) : ParamAffine d e
    -- = cutAffineRight j - imageLeftAffine π k + cutAffine k  (= leftEnd μ j - translationVector π λ k)
theorem preimageCutAffine_eq (hr) (hl) (h1 : imageLeft π lam k < leftEnd mu j)
    (h2 : leftEnd mu j < imageLeft π lam k + lam k) :
    (mkIET1 lam π hl)⁻¹ (leftEnd mu j) = preimageCutAffine π j k q
theorem exists_ball_imageLeft_lt (hq₀) (hr₀) (hj : j ≠ 0) :
    ∃ (k : Fin d) (ε : ℝ), 0 < ε ∧ ball ⊆ goodParams ∧ (ball ⊆ region) ∧
      (∀ q ∈ ball, the strict containment with this k) ∧
      (∀ q ∈ ball, ∀ hl, (mkIET1 …)⁻¹ (leftEnd μ j) = preimageCutAffine π j k q)
```

The ball is the set `W` on which the two *strict* inequalities between affine functions hold,
intersected with `goodParams` and the open simplex region — a finite intersection of open sets, so
`Metric.isOpen_iff` produces `ε`.  Note the set-builder `∩` is **left**-associative, so
`(hball hq).1.1.1` is the first inequality, `(hball hq).1.2` is `goodParams`, `(hball hq).2` is the
region.

**Lean trap**: `rw [mkIET1_inv_of_lt_imageLeft hl h1 h2]` fails because the lemma's `p` cannot be
inferred from `hl` alone (the second component is undetermined); pass it explicitly,
`(p := (simplexMap d q.1, simplexMap e q.2))`.  Same for `exists_lt_imageLeft_of_good` and
`mkIET1_inv_of_lt_imageLeft` elsewhere — implicit inference on `p` times out or mismatches.

### Item 3 — first half

```lean
theorem exists_ball_lt_of_lt (F : Fin m → ParamAffine d e) (h : ∀ i j, i < j → F i q₀ < F j q₀) :
    ∃ ε > 0, ∀ q ∈ ball q₀ ε, ∀ i j, i < j → F i q < F j q
theorem exists_ball_strictMono … (h : StrictMono fun i => F i q₀) :
    ∃ ε > 0, ∀ q ∈ ball q₀ ε, StrictMono fun i => F i q
```

### What is left

* **item 3 (second half)**: take, for `j : Fin (e-1)`, the cut `⟨j.val + 1, _⟩ : Fin e` of `g`, get
  `k j : Fin d` and `ε j` from `exists_ball_imageLeft_lt`, take the finite minimum of the `ε j` and
  the minimum with `exists_compPresentation_on_ball`'s ball.  The family of singularity functions is
  then `F : (Fin (d-1) ⊕ Fin (e-1)) → ParamAffine d e`, with `F (inl i) = cutAffine i.succ` and
  `F (inr j) = preimageCutAffine π (j.succ) (k j)`; it is injective at `q₀`, so it can be **sorted**
  into `s : Fin (d+e-2) → ParamAffine d e` with `StrictMono` at `q₀` (use
  `Finset.orderIsoOfFin` on the image finset, or selection sort on the values at `q₀`), and
  `exists_ball_strictMono` keeps the order on a ball.  Then
  `s' : Fin (d+e-1) → ParamAffine d e` is `s' 0 = 0`, `s' (k+1) = s k`, `s' last = 1`.
* **item 4**: `a i` = the position of `cutAffine i` in `s'` (`i ≠ 0`), `B k` = the cell of `g`
  containing `f (s' k)`, `ρ` from the images; then the `IsCompPresentation` fields `zero`, `top`,
  `mono`, `f_transl`, `g_transl`, `cell`, `card_eq`.  `f_transl`/`g_transl` are the "the marked
  points include the cuts of `f` and the `f⁻¹` of the cuts of `g`" computations; `cell` is the same
  computation composed.

## Item 3: sorting and the uniform ball (this session)

Build green at 5 `sorryAx`; all new declarations axiom-clean.

```lean
theorem exists_strictMono_comp {ι} [Fintype ι] (A : ι → ParamAffine d e) {q₀}
    (hA : Function.Injective (fun i => A i q₀)) :
    ∃ σ : Fin (Fintype.card ι) ≃ ι, StrictMono fun k => A (σ k) q₀
theorem leftEnd_lt_leftEnd (hpos : ∀ i, 0 < lam i) (h : i < i') : leftEnd lam i < leftEnd lam i'
theorem imageLeft_ne_leftEnd_of_good (hq) (hl) (hm) (hj : j ≠ 0) (π) (i) :
    imageLeft π p.1 i ≠ leftEnd p.2 j
theorem exists_ball_forall_imageLeft_lt (π) (hq₀) (hr₀) :
    ∃ (k : Fin (e-1) → Fin d) (ε : ℝ), 0 < ε ∧ ball ⊆ goodParams ∧ ball ⊆ region ∧
      (∀ q ∈ ball, ∀ j, imageLeftAffine π (k j) q < cutAffineRight (j.succ) q ∧
        cutAffineRight (j.succ) q < imageLeftAffine π (k j) q + imageLenAffine (k j) q) ∧
      (∀ q ∈ ball, ∀ j, ∀ hl, (mkIET1 lam π hl)⁻¹ (leftEnd mu (j.succ)) = preimageCutAffine π (j.succ) (k j) q)
```

`exists_strictMono_comp` is the sorting lemma: the finite set of values at `q₀`, enumerated
increasingly by `Finset.orderEmbOfFin`, composed with the chosen inverse of `i ↦ A i q₀`.  Two Lean
traps: `Finset.map` needs the `↪` (`.toEmbedding`) of the order embedding, and `Equiv.ofBijective`'s
value is a beta-redex, so `beta_reduce` before rewriting with the injectivity hypothesis.

`exists_ball_forall_imageLeft_lt` bundles `exists_ball_imageLeft_lt` over the finite index type
`Fin (e-1)` by `choose` + intersecting the finitely many balls (`isOpen_iInter_of_finite`), together
with `goodParams` and the open simplex region.

### Remaining plan for `exists_compPresentation_on_ball`

Let `n := d + e - 1`, `ι := Fin (d-1) ⊕ Fin (e-1)`, `card ι = n - 1`, and
`A : ι → ParamAffine d e` with `A (inl i) = cutAffine i.succ`, `A (inr j) = preimageCutAffine π
j.succ (k j)` (`k` from `exists_ball_forall_imageLeft_lt`).

1. `hA : Function.Injective (fun i => A i q₀)`: from `leftEnd_lt_leftEnd` (cuts of `f` and of `g`
   are strictly increasing), injectivity of `f` (preimages of the cuts of `g` are distinct), and
   `imageLeft_ne_leftEnd_of_good` (cross case; note `f (leftEnd λ i) = imageLeft π λ i` by
   `mkIETFun_leftEnd`, which needs `0 < λ i`).
2. `σ` from `exists_strictMono_comp`; `s : Fin (n+1) → ParamAffine d e` with `s 0 = 0`,
   `s (k+1) = A (σ k)`, `s last = 1`; `StrictMono` on a ball from `exists_ball_strictMono`, the
   endpoints being strict because `0 < leftEnd < 1` on the region.
3. `a : Fin (d+1) → Fin (n+1)`: `a 0 = 0`, `a (i+1) = (σ.symm (inl i)) + 1`, `a last = last`;
   `IsCompType`'s `s (a i.castSucc) = leftEnd λ i` follows from the construction, and `a last = last`
   is by construction.
4. `B : Fin n → Fin e`: the cell of `g` containing `f (s k)`, as `idx mu (f (s k))`; the two-sided
   interval condition follows from "no `f⁻¹` of a cut of `g` lies strictly inside a marked cell",
   which is the sortedness of `s` plus `hinv` of `exists_ball_forall_imageLeft_lt`.
5. the fields: `zero`, `top` by construction; `mono` from step 2; `f_transl` and `g_transl` from
   "no cut of `f` (resp. no `f⁻¹` of a cut of `g`) lies strictly inside a marked cell"
   (`IsCutSet.locallyTranslationAt_of_not_mem` makes this cheap — the cut set of `f` is
   `mkIETCuts λ 0 1`); `cell` by composing the two translations; `card_eq` by `n = d + e - 1`.

## Injectivity of the singularity family, and the marked list (this session)

Build green at 5 `sorryAx`; all new declarations axiom-clean.

```lean
theorem mkIET1_leftEnd (hv : v ∈ simplexRegion d) (hl : simplexMap d v ∈ simplex d) (π) (i : Fin d) :
    mkIET1 (simplexMap d v) π hl (leftEnd (simplexMap d v) i) = imageLeft π (simplexMap d v) i
noncomputable def singAffine (π) (k : Fin (e-1) → Fin d) : Fin (d-1) ⊕ Fin (e-1) → ParamAffine d e
theorem singAffine_injective (hq) (hr) (hl) (hinv) : Function.Injective (fun i => singAffine π k i q)
noncomputable def withEnds (hn : 1 ≤ n) (A : Fin (n-1) → ParamAffine d e) : Fin (n+1) → ParamAffine d e
theorem withEnds_zero / withEnds_last / withEnds_mid
```

`mkIET1_leftEnd` is `mkIETFun_leftEnd` transported to `mkIET1`; note the link
`(mkIET1 …).toEquiv x = mkIETFun … 0 x` must be stated as a `have hlink : … := rfl` — `simpa` does
**not** see through `mkIET1`'s structure projection here (the `noncomputable def` is not unfolded at
`simp`'s transparency).

`singAffine_injective` has the four cases of `Fin (d-1) ⊕ Fin (e-1)`: cuts against cuts
(`leftEnd_lt_leftEnd`), preimages against preimages (injectivity of `f⁻¹` + `leftEnd_lt_leftEnd`), and
the two mixed cases: apply `f` (`IET.apply_symm_apply'`), rewrite with `mkIET1_leftEnd`, and
contradict `imageLeft_ne_leftEnd_of_good`.  Traps: `beta_reduce at h` before rewriting the goal
`(fun i => singAffine π k i q) (Sum.inl a) = …`; and the direction of the rewrite is `rw [h]` in the
`(inl, inr)` case and `rw [← h]` in the `(inr, inl)` one.

`withEnds` needed `AffineMap.const ℝ (PReal d e) 1` rather than `1` (no `One` instance for
`AffineMap`), and `simp [withEnds, show n ≠ 0 by omega]` for `withEnds_last`.

### What is left for `exists_compPresentation_on_ball`

1. `m := n - 1` and `A : Fin m → ParamAffine d e` = `singAffine π k` post-composed with the
   identification `Fin (d+e-2) ≃ Fin (d-1) ⊕ Fin (e-1)` (`Fintype.equivFin`-style);
   `σ` from `exists_strictMono_comp` and `singAffine_injective`; `s := withEnds hn (fun k => A (σ k))`.
2. `StrictMono` on a ball: `exists_ball_strictMono` plus `0 < cutAffine i q₀ < 1` for the ends.
3. `a`: `a 0 = 0`, `a (i+1) = (σ.symm (inl i)) + 1`, `a last = last`; `IsCompType`'s first two
   components then hold by construction (`withEnds_mid`, `cutAffine_eq_leftEnd`).
4. `B k := idx (simplexMap e q₀.2) (f (s k q₀))` and `ρ k := idx (s · q₀) (g (f (s k q₀)))`; both
   are constant on the ball because `s`, `f ∘ s` and `g ∘ f ∘ s` are continuous and the cells are
   separated by the marked points.
5. the fields `zero`, `top`, `mono` (step 2), `f_transl` / `g_transl` (no cut of `f`, resp. no
   `f⁻¹` of a cut of `g`, is strictly inside a marked cell — from the sortedness), `cell`, and
   `IsCompType`'s two-sided interval condition.

## The marked list and the bounds on the singularities (this session)

Build green at 5 `sorryAx`; all new declarations axiom-clean.

```lean
theorem withEnds_apply_eq … : withEnds hn A j q = if h0 : j.val = 0 then 0 else if h1 : j.val = n then 1 else A ⟨j.val - 1, _⟩ q
theorem strictMono_withEnds (h0 : ∀ k, 0 < A k q) (h1 : ∀ k, A k q < 1) (hA : StrictMono fun k => A k q) :
    StrictMono fun j => withEnds hn A j q
theorem cutAffine_pos (hq : q.1 ∈ simplexRegion d) (hi : i ≠ 0) : 0 < cutAffine i q
theorem cutAffine_lt_one (hq : q.1 ∈ simplexRegion d) (i) : cutAffine i q < 1
theorem preimageCutAffine_mem (hq) (hr) (hl) (hm) (hj : j ≠ 0) (hinv : preimageCutAffine π j k q = f⁻¹(leftEnd μ j)) :
    0 < preimageCutAffine π j k q ∧ preimageCutAffine π j k q < 1
```

Lean notes: `(if c then f else g) q` is **not** definitionally `if c then f q else g q` for `AffineMap`
(the `if` lives at the affine-map type), which is why `withEnds_apply_eq` is a case split; and a `dite`
inside the goal must be handled with `dif_pos`/`dif_neg`, in the right order (outer `if` first).

`preimageCutAffine_mem` needs `f 0 = imageLeft π λ 0` (from `mkIET1_leftEnd` at `i = 0` plus
`leftEnd_zero`); writing `rw [← hc, IET.apply_symm_apply']` on the goal with `(mkIET1 …) 0` fails
because `rw` also tries to abstract the `0` of the type `IET 0 1` — state
`f (f⁻¹ y) = y` as a `have` and rewrite `hc` into that.

### Next

`exists_markedList` (step 1's assembly): transport `singAffine π k` along
`finCongr (Fintype.card (Fin (d-1) ⊕ Fin (e-1)) = n - 1)`, sort with `exists_strictMono_comp` +
`singAffine_injective`, set `s := withEnds hn (A ∘ τ)`, and get `StrictMono` on a ball from
`strictMono_withEnds` + `cutAffine_pos`/`cutAffine_lt_one`/`preimageCutAffine_mem`.  Then `a`, `B`,
`ρ` and the six fields.

## Conjunctive predicates turned into structures (this session, user request)

Build green at 5 `sorryAx`; no proof changed, only the shape of three definitions.

### Refactored

* **`IsBlock`** (was `IsPairSplitting D E u ∧ IsPairSplitting D E v ∧ u < v ∧ ∀ w, …`) is now a
  `structure … : Prop` with fields `left`, `right`, `lt`, `consecutive`.  Its only consumer,
  `block_irreducible_on_good`, now reads `hb.left`, `hb.right`, `hb.consecutive` instead of
  `hb.1`, `hb.2.1`, `hb.2.2.2`.  The anonymous constructor `⟨…⟩` is unchanged, so the machine-checked
  counterexamples in `.scratch/` still elaborate where they construct one.
* **`IsCompType`** is now a structure with fields **`top`**, **`cut`**, **`image`** (the three
  conjuncts), and `lam_eq_sum`/`mu_eq_sum` use the names instead of `⟨htop, hval, -⟩`/`⟨-, -, hB⟩`.
* **`IsBadParam`**: its body was a five-part conjunction under the existential.  The conjuncts are
  now the named fields of a new structure
  `IsSmallRelation q k a b` (`a_bound`, `b_bound`, `k_bound`, `nontrivial`, `vanishes`), and
  `IsBadParam q := ∃ k a b, IsSmallRelation q k a b`.  The *type* of `IsBadParam` is unchanged, so
  every statement mentioning it is untouched, and the six sites that destruct or build the
  existential keep working unchanged (nested `⟨…⟩` patterns elaborate through the structure).

### Surveyed and deliberately left alone

* `IETDatum.IsFixedCell` — two conjuncts (`IsSplitting l.castSucc ∧ IsSplitting l.succ`), read as
  prose in `isFixedCell_apply`.  Two clauses do not need names.
* `IsIrreducibleOn`, `IsIET`, `Separated` — a single `∀`/`∨`/`∃`, not a conjunction.
* `UniqueErgodic`, `IsRigidByTranslations`, `IsIrreduciblePerm`, `MasurVeech`, `VeechRigidity`
  (`Irreducible.lean`) — quantifier chains (the paper's Definitions 2.1–2.3 and hypotheses), consumed
  as opaque hypotheses, never destructed; naming their parts would not be faithful to the source.
* `IsDiophantine`, `IsDiophC`, `GoodFree`, `IsLocallyTranslationAt`, `IsFiniteUnionIntervals` —
  existentials of *numbers/functions* whose trailing conditions are the paper's formula; a structure
  would only rename the bits of one formula.
* `IsLat` (`SingularityBound.lean`) — three conjuncts under an `∃`, but it is a local gadget of one
  ported file with eight use sites, and the conjunction is exactly the paper's
  "`x` is an integer combination with coefficients bounded by `k`".  Left as is.
* `IsCutSet`, `IsCompPresentation`, `GoodRegion` — already structures.

### The stale counterexample was deleted (user request)

`.scratch/counter.lean` and its copy `.scratch/try/counter.lean` proved `¬ IsBadParam (1/3, 1/4)`,
which is **false** since the bound in `IsBadParam` was raised from `2` to `4` —
`-1 + 3·(1/3) + 0·(1/4) = 0` has coefficients of absolute value `≤ 4`.  Both copies are gone.
The counterexample itself (that `IsIrreducibleOn` with target `Ico u v` is false) is still valid and
is recorded in `NOTES.md`; it would need a pair that is good at bound `4` with the same
combinatorics, e.g. `(2/5, 3/7)`.  `.scratch/counter2.lean` (the other keeper, which uses
`(2/5, 3/7)`) still compiles and is kept.

## `exists_markedList` (this session)

Build green at 5 `sorryAx`; axiom-clean.

```lean
theorem exists_markedList (π) (hq₀ : q₀ ∈ goodParams d e) (hr₀ : q₀ ∈ region) :
    ∃ (τ : Fin ((d+e-1)-1) ≃ (Fin (d-1) ⊕ Fin (e-1))) (s : Fin (d+e-1+1) → ParamAffine d e) (ε : ℝ),
      0 < ε ∧ ball ⊆ goodParams ∧ ball ⊆ region ∧
      (∀ q ∈ ball, StrictMono fun j => s j q) ∧
      (∀ q ∈ ball, s 0 q = 0) ∧ (∀ q ∈ ball, s (Fin.last (d+e-1)) q = 1) ∧
      (∀ q ∈ ball, ∀ i : Fin (d-1), s ⟨(τ.symm (inl i)).val + 1, _⟩ q = leftEnd (simplexMap d q.1) ⟨i.val+1,_⟩) ∧
      (∀ q ∈ ball, ∀ j : Fin (e-1), ∀ hl, s ⟨(τ.symm (inr j)).val + 1, _⟩ q = f⁻¹(leftEnd (simplexMap e q.2) ⟨j.val+1,_⟩))
```

Route: `exists_ball_forall_imageLeft_lt` gives `k` and a ball; `singAffine_injective` at `q₀` feeds
`exists_strictMono_comp`, giving `σ : Fin (card ι) ≃ ι`; `τ := (finCongr hcard).symm.trans σ` moves it
to `Fin ((d+e-1)-1)`; `A := fun kk => singAffine π k (τ kk)`, `s := withEnds hn A`; `StrictMono` at
`q₀` from `strictMono_withEnds` (`cutAffine_pos`, `cutAffine_lt_one`, `preimageCutAffine_mem` give
the values in `(0,1)`), then on a ball from `exists_ball_strictMono`; finally intersect the two balls.
The index clauses are `withEnds_mid` + `singAffine_inl`/`singAffine_inr` + `cutAffine_eq_leftEnd`/`hinv`.

Lean notes: `Set.Subset` takes its point **implicitly**, so `h : s ⊆ t` is applied as `h hx`, not
`h x hx`; and `show (withEnds hn A 0) q = 0` must be `change` (the linter rejects `show` when it
changes the goal); `(0 : ParamAffine d e) q = 0` and `(AffineMap.const ℝ _ 1) q = 1` then need `rfl`.

### What remains for `exists_compPresentation_on_ball`

1. **the image side**: for each marked cell `k`, the cell `B k` of `g` containing the image
   `f (s k.castSucc)` — a ball where `B k := idx μ (f (s k q₀))` stays the cell, and the two-sided
   inequality of `IsCompType.image`.  The upper bound needs "no cut of `g` lies strictly inside
   `(f (s k), f (s k+1))`", which follows from the `inr` positions of `τ` (a cut inside would have its
   `f⁻¹` strictly inside the marked cell, contradicting `StrictMono s`).
2. **`a`**: `a 0 = 0`, `a (i+1) = (τ.symm (inl i)).val + 1`, `a last = last`; `IsCompType.top`/`cut`
   then follow from `exists_markedList`'s index clauses.
3. **`f_transl`, `g_transl`, `cell`**: on each marked cell, `f` is a translation (`IsCutSet` of
   `mkIETCuts λ 0 1`, since no cut of `f` is strictly inside a marked cell), `g` is a translation on
   the image (no cut of `g` there), and `g ∘ f` is the composite translation.
4. **`ρ`**: `idx (s · q₀)` of `g (f (s k q₀))`, constant on the ball.

## The image side: first lemma (this session)

Build green at 5 `sorryAx`; axiom-clean.

```lean
theorem no_cut_inside_markedCell (lam) (τ) {s} (hmono : StrictMono s)
    (hcut : ∀ i : Fin (d-1), s ⟨(τ.symm (Sum.inl i)).val + 1, _⟩ = leftEnd lam ⟨i.val + 1, _⟩)
    {k : Fin n} {c : Fin d} (hc : c ≠ 0) :
    ¬ (s k.castSucc < leftEnd lam c ∧ leftEnd lam c < s k.succ)
```

**No cut of `f` lies strictly inside a marked cell**: the `inl` entries of `τ` exhibit every
non-trivial cut as a marked point, and `StrictMono s` forbids a marked point strictly between `s k`
and `s k+1`.

Trap: with `set i : Fin (d-1) := ⟨c.val - 1, _⟩`, `i.val` is opaque — record
`hival : i.val = c.val - 1 := by rw [hi]` before using `omega` to identify `c` with `i.val + 1`.

### The remaining chain for the fields (design worked out, not yet formalised)

1. **`f_transl`**: `IsCutSet.transl_of_locally` for `isCutSet_mkIET1 lam π hl` with `x := s k`,
   `y ∈ (s k, s k+1)`: the only cuts in `(min x y, max x y]` would be *strictly inside* the marked
   cell, so the hypothesis of `transl_of_locally` is **vacuous by `no_cut_inside_markedCell`**.
2. **the image identity**: `f '' Ico (s k) (s k+1) = Ico (f (s k)) (f (s k) + (s k+1 - s k))`, from
   step 1 and injectivity.  (Note `f (s k+1) ≠ f (s k) + ν k` in general: `s k+1` may be a jump of
   `f`; the *half-open* cell is what transports.)
3. **no cut of `g` inside the image**: if `f (s k) < leftEnd μ (j+1) < f (s k) + ν k`, then by step 2
   and injectivity `f⁻¹(leftEnd μ (j+1)) = s (bPos j) ∈ (s k, s k+1)`, so `k < bPos j < k+1` —
   impossible.
4. **`B`**: `B k := idx μ (f (s k))` at `q₀`.  Its local constancy is *not* a plain openness argument,
   and this is the delicate point: if the marked point `s k` is an `inr` entry, then
   `f (s k) = leftEnd μ (j+1)` **identically** on the ball (because `s k = preimageCutAffine …` is
   `leftEnd μ (j+1) - translationVector`, and `f` translates by that vector there), so `idx` still
   returns the same index; if `s k` is an `inl` entry, then `f (s k) = imageLeft π λ (i+1)`, which is
   *strictly* inside a `g`-cell at a good parameter (`imageLeft_ne_leftEnd_of_good`), and strictness
   persists on a ball.  So the proof of constancy must split on `τ (k-1)`.
5. **`IsCompType.image`**: lower bound `idx_mem`; upper bound from step 3 (if
   `upperEnd μ (B k) < f (s k) + ν k` then the cut `leftEnd μ (B k + 1) = upperEnd μ (B k)` would be
   strictly inside, contradicting step 3; if `B k` is the last cell, `upperEnd = 1` bounds everything).
6. `g_transl` (same as step 1, for the image, using step 3), `cell` (compose), `a` (from
   `exists_markedList`'s index clauses), `ρ` (`idx (s · q₀)` of `g (f (s k q₀))`).

## `f_transl`, the image identity, and no `g`-cut inside the image (this session)

Build green at 5 `sorryAx`; all four new declarations axiom-clean, linter-clean.

```lean
theorem mem_mkIETCuts_one (hpos : ∀ i, 0 < lam i) (hsum : ∑ lam = 1) {c} :
    c ∈ mkIETCuts lam 0 1 ↔ ∃ i, leftEnd lam i = c
theorem markedCell_transl (hv : v ∈ simplexRegion d) (hl) (hmono) (hzero) (htop) (hcut) (k : Fin n) :
    ∃ δ, ∀ x, s k.castSucc ≤ x → x < s k.succ → mkIET1 (simplexMap d v) π hl x = x + δ
theorem image_Ico_add (h : a < b) (hf : ∀ x, a ≤ x → x < b → f x = x + δ) :
    f '' Set.Ico a b = Set.Ico (a + δ) (b + δ)
theorem no_gcut_inside_image … (k : Fin n) {j : Fin (e-1)} :
    ¬ (f (s k.castSucc) < leftEnd μ (j+1) ∧ leftEnd μ (j+1) < f (s k.castSucc) + (s k.succ - s k.castSucc))
```

* `mem_mkIETCuts_one` is worth having on its own: it is the description of the cut set of `mkIET1`
  as the set of cuts `leftEnd lam i` (the `if (∑ lam < 1)` branch is empty because `∑ lam = 1`).
* `markedCell_transl` is the `f_transl` field: `IsCutSet.transl_of_locally` for
  `isCutSet_mkIET1 lam π hl` with `x := s k.castSucc`, `y` in the cell.  Its hypothesis is **vacuous**
  by `no_cut_inside_markedCell`: a cut `c` with `min x y < c ≤ max x y` would lie strictly inside the
  marked cell, and `i = 0` is excluded because `s k.castSucc ≥ 0 = leftEnd lam 0`.
* `image_Ico_add` is stated for an arbitrary translation `δ` on an arbitrary interval, so it is
  reusable; the marked-cell version is `f '' (s k, s k+1) = Ico (f (s k)) (f (s k) + (s k+1 - s k))`.
* `no_gcut_inside_image`: a `g`-cut strictly inside the image would, by the image identity and
  injectivity of `f`, have `x := f⁻¹(leftEnd μ (j+1)) = s (bPos j)` with `s k.castSucc ≤ x < s k.succ`;
  strict monotonicity forces `bPos j = k.castSucc`, and then `f x = f (s k.castSucc)` contradicts the
  strict left inequality.  (`subst` on the equation `x = s (bPos j)` is what keeps this short.)

### Next: the `B` constancy split on `τ`

```lean
theorem imageInG … : ∃ B : Fin n → Fin e, ∀ k,
    leftEnd μ (B k) ≤ f (s k.castSucc) ∧
      f (s k.castSucc) + (s k.succ - s k.castSucc) ≤ leftEnd μ (B k) + μ (B k)
```

pointwise with `B k := idx μ (f (s k.castSucc))`: the lower bound is `idx_mem`; the upper bound is
`no_gcut_inside_image` — if `upperEnd μ (B k) < f (s k) + ν k` then the cut
`leftEnd μ (B k + 1) = upperEnd μ (B k)` (when `B k ≠ lastIdx e`) lies strictly inside the image.
For `B k = lastIdx e`, `upperEnd = ∑ μ = 1` and `f (s k) + ν k ≤ 1` because `f` maps `[0,1)` into
itself (take `x → s k.succ⁻` in the cell, where `f x = x + δ < 1`).

For the **ball** version the index `B k` must be independent of `q`, and the constancy is the `τ`
split described in the previous section: `inr` entries give the identity `f (s k) = leftEnd μ (j+1)`,
`inl` entries give a strict inequality at `q₀` that persists on a ball.  Note `f (s k)` need not be
continuous in `q` across the *whole* ball — it is, because the cell of `f` containing `s k` is fixed
there (`no_cut_inside_markedCell` is a strict condition in `q` too).

## `imageInG` (this session): the image of each marked cell lies in one cell of `g`

Build green at 5 `sorryAx`; axiom-clean.

```lean
theorem le_of_Ico_subset {a b : ℝ} (ha : a < 1) (h : Set.Ico a b ⊆ Set.Ico (0:ℝ) 1) : b ≤ 1
theorem imageInG (hv) (hl) (hm) (hmono) (hzero) (htop) (hcut) (hpre) :
    ∃ B : Fin n → Fin e, ∀ k : Fin n,
      leftEnd μ (B k) ≤ f (s k.castSucc) ∧
        f (s k.castSucc) + (s k.succ - s k.castSucc) ≤ leftEnd μ (B k) + μ (B k)
```

**The bug that cost two rounds**: the proof opens `by_contra hcon` (upper bound), so *both* branches
of the last-cell split must conclude `False`, not the inequality — the goal inside is `False` and
`rw [← upperEnd_eq]` there fails with a confusing message ("pattern not found in `False`").  Reading
the full error context (which showed `hcon` among the hypotheses) is what identified it.  Fix: each
branch ends with `absurd`/`linarith` against `hcon`.

Second trap: `hcon` is stated with the *unfolded* `B k` (a lambda application), while the branches
work with the `set`-defined `c`; align them once with
`beta_reduce at hcon; rw [← hc, ← upperEnd_eq] at hcon` right after `set c := … with hc`.

`leftEnd_eq_upperEnd_of_succ` was moved up to just before this block (it is a basic `leftEnd` fact
and `imageInG` needs it; it used to sit in section 3, after the marked-list material).

### What remains for `exists_compPresentation_on_ball`

1. **the `τ` constancy split**: `B k` must be independent of `q`.  Write `B k` at `q₀`; for `q` in a
   ball it is still the cell of `f_q (s k q)`:
   * if the marked point at position `k` is an `inr` entry (`s k = f⁻¹(leftEnd μ (j+1))`), then
     `f (s k) = leftEnd μ (j+1)` **identically** on the ball, so `idx` is unchanged (an equality at
     the left end is harmless);
   * if it is an `inl` entry (or `0`, `1`), `f (s k) = imageLeft π λ (i+1)`, which is *strictly*
     inside a `g`-cell at a good parameter (`imageLeft_ne_leftEnd_of_good`), and strictness persists.
   Concretely: define `B k` at `q₀` and prove `leftEnd μ (B k) ≤ f (s k)` and
   `f (s k) + ν k ≤ upperEnd μ (B k)` at every `q` of the ball by the same case split, rather than
   trying to make `idx` itself continuous.
2. `f_transl` / `g_transl` (pointwise versions done: `markedCell_transl`), `cell`, `a`, `ρ`, and the
   packing into `IsCompPresentation` + `IsCompType` on a ball.

## `g_transl` (this session)

Build green at 5 `sorryAx`; axiom-clean.

```lean
theorem markedCell_g_transl (π) (σ) (hv) (hw) (hl) (hm) (hmono) (hzero) (htop) (hcut) (hpre) (k : Fin n) :
    ∃ δ, ∀ x, s k.castSucc ≤ x → x < s k.succ →
      g (f x) = f x + δ
```

Same cut-set criterion as `markedCell_transl`, now for `isCutSet_mkIET1 (simplexMap e w) σ hm`, with
`x := f (s k.castSucc)` and `y := f x`: a cut of `g` in `(min, max]` would lie strictly inside the
image of the marked cell, which is `no_gcut_inside_image`.  The case `j = 0` (`leftEnd μ 0 = 0`) is
excluded by `0 ≤ f (s k.castSucc) < c`.  Note `IsCutSet.transl_of_locally`'s local-translation
hypothesis is its *last* argument, so the `?_` must be discharged before the final `linarith` (the
bullets are in the opposite order from the naive reading).

### What is left for `exists_compPresentation_on_ball`

`f_transl` and `g_transl` are now available *pointwise at each `q`* (the `δ` may depend on `q`),
which is exactly the form the fields need.  Still to do:

1. **`a`** (`IsCompType.top`, `IsCompType.cut`): `a 0 = 0`, `a (i+1) = (τ.symm (inl i)).val + 1`,
   `a (Fin.last d) = Fin.last n` — the `Fin (d+1)` analogue of `withEnds`, with the same
   `if`-cascade.  Then `cut` is `hcut` (plus `s 0 = leftEnd λ 0 = 0`).
2. **`B` constancy + `IsCompType.image`** (the `τ` split).
3. **`ρ` and `cell`**: `ρ i` is the index of the marked point `g (f (s i))` — the image of a marked
   cell under `g ∘ f` is again a marked cell, because a singularity of `g ∘ f` strictly inside the
   image would pull back to one strictly inside the cell.  So `ρ i := idx (s · q₀) (g (f (s i q₀)))`
   and `s (ρ i) q = g (f (s i q))` on the ball (both are "the same" singularity, so the difference
   vanishes identically — the same phenomenon as `B`'s `inr` case).
4. the packing of the per-`q` facts into `IsCompPresentation`/`IsCompType` on the ball.

## `a`, the marked index of the cuts of `f` (this session)

Build green at 5 `sorryAx`; axiom-clean.

```lean
noncomputable def compTypeA (τ) : Fin (d+1) → Fin (n+1)   -- 0, last, and the τ-index of each cut
theorem compTypeA_zero / compTypeA_last / compTypeA_succ
theorem compTypeA_cut (hzero : s 0 = 0) (hcut) (i : Fin d) : s (compTypeA τ i.castSucc) = leftEnd lam i
```

`compTypeA` is the `Fin (d+1)` analogue of `withEnds`: the same `if`-cascade, with the middle case
`⟨(τ.symm (inl ⟨i.val - 1, _⟩)).val + 1, _⟩`.  `compTypeA_cut` splits on `i = 0` (then `s 0 = 0 =
leftEnd λ 0`) and `i = i' + 1` (then `hcut i'`).

Traps: a dependent `rw [hidx]` (rewriting a `Fin` index that also occurs in a proof term) fails with
"motive is not type correct" — use `simp only [hidx]` instead; and `Nat` subtraction `i.val + 1 - 1`
needs `simp`/`omega` rather than being definitional, so `Fin.ext (by simp)` is the short proof of the
index identity.

### Remaining

`B` constancy (τ split) + `IsCompType.image`; `ρ`/`cell`; the packing.  `B`: at each `q` of the ball
`f_q (s k q)` is `imageLeft π λ (i+1)` (`k = 0` or the marked point is an `inl` entry) or
`leftEnd μ (j+1)` (an `inr` entry, where the containment is an identity in `q`); in the first case
strictness at `q₀` persists on a ball because both sides are affine in `q`.

## `B` constancy: attempted, not landed (this session — **landed** later, see "The `B` assembly is **PROVED**: `exists_compImage_on_ball`")

The design is settled and the draft is in `.scratch/try/ctb.lean`, but it does not compile yet and
nothing was added to the library (build unchanged at 5 `sorryAx`).

**Design.** Define `compTypeF π τ : Fin n → ParamAffine d e` (the position of the image of each marked
cell, as an affine function):
* `k = 0` ⟹ `imageLeftAffine π 0`;
* `k = m+1`, `τ m = inl i` ⟹ `imageLeftAffine π (i+1)`;
* `k = m+1`, `τ m = inr j` ⟹ `cutAffineRight (j+1)`.

Then `compTypeF_apply`: `f_q (s k.castSucc q) = compTypeF k q` for `q` good in the region — this is
`mkIET1_leftEnd` (a cut of `f` maps to `imageLeft`) in the first two cases and
`IET.apply_symm_apply'` in the third.  **No f-cell constancy is needed** for this identity, because
the marked point is *by definition* a cut or a preimage.

Given that identity, the constancy of `B k := idx μ₀ (f_{q₀}(s k q₀))` on a ball is:
* `inr` case: `f_q(s k q) = leftEnd μ (j+1) q` **identically**, and `B k = j+1` because `idx` of a cut
  is that cut (equality at the left end is harmless);
* `0`/`inl` cases: `f_q (s k q) = imageLeftAffine π i q`, which at `q₀` is *strictly* inside the
  `g`-cell `B k` (`imageLeft_ne_leftEnd_of_good`), and strictness persists because both
  `imageLeftAffine π i` and `cutAffineRight (B k)`, `cutAffineRight (B k + 1)` are affine in `q`.

**Where it stuck**: the `Fin` index bookkeeping in `compTypeF_apply`.  Three concrete snags:
`(0 : Fin n)` needs `[NeZero n]` (the def and the lemma must carry it); proofs of `a < n - 1 → a + 1 <
n + 1` written inline as `by omega` fail because omega sees the `Fin` constructor as opaque — hoist
them (`lt_succ_of_lt_pred` in the draft); and `k.castSucc` must be identified with
`⟨(τ.symm (τ m)).val + 1, _⟩` through `Fin.ext` before `hcut` applies.

**Suggested simplification for next time**: skip `compTypeF` and do the three cases *inline* in the
final proof, where `k` is either `0` or `m+1` with `τ m` already destructed — that removes the awkward
`match` in the def and the `dif_neg`/`hτ` rewrites in the lemma.

## `IsCompPresentation.cell` was **false** as stated: counterexample and repair (this session)

**The error.** The `cell` field said: `(g ∘ f) x = x + (s (ρ i) - s i)` on the `i`-th marked cell,
i.e. that `g ∘ f` maps the `i`-th cell onto *the `ρ i`-th cell of the same list*.  That is not the
definition of an interval exchange: for `mkIET1 λ π` the image of the `i`-th cell is the interval
`[imageLeft π λ i, imageLeft π λ i + λ i)`, whose left end is a partial sum of the `λ`'s in the order
of `π`, and it is **not** one of the cell starts `leftEnd λ k` in general.  The images of the cells
are an interval partition of `[0,1)` different from the source partition; the standard IET datum only
requires that the images be placed according to `ρ`.

**Counterexample** (`d = 2`, `e = 1`, `π = σ` trivial on `Fin 1`, so `g = id` and `g ∘ f = f`;
`n = d + e - 1 = 2`).  Take `π` the transposition and `λ = (1/3, 2/3)`: `f` is the rotation
`x ↦ x + 2/3 (mod 1)`.  Then

* `f_transl` forces the marked list to be `s = (0, 1/3, 1)` (the only cut of `f` is `1/3`), and
* `f (s 0) = f 0 = 2/3 ∉ {0, 1/3, 1}`, so `cell` at `i = 0` demands `s (ρ 0) = 2/3` for some
  `ρ 0 ∈ {1, 2}`, i.e. `2/3 ∈ {1/3, 1}`.  False.

Numerically checked (`2/3`, `13/15`, `0`, `1/6` for `x = 0, 1/5, 1/3, 1/2` — and `mkIET1 ν ρ` with
`ν = (1/3, 2/3)`, `ρ` the transposition gives the same four values, see the corrected field).  The
general failure is that the `cell` field asks the *image of a cell* to be a *cell of the same list*,
which is exactly what an IET does not do: the images of the cells are the `λ`-intervals rearranged
according to `ρ`, and their left ends are partial sums of the `λ`'s in the order of `ρ`, not the
`leftEnd λ k`.  Nothing about `goodParams` can repair this — it is not a numerical coincidence, it
is the generic situation.  A second, independent failure mode: when `π i = π (i-1) + 1` then
`f` is continuous at the listed cut `leftEnd λ i`, so two adjacent cells are carried by the same
translation and the marked list is not the minimal cut set; that is a purely combinatorial condition
on `π`, so again `goodParams` cannot exclude it.  The first mode is visible in the further example
`d = 3`, `π = (0 2)`, `λ = (1/7, 3/11, 45/77)` (good at bound 4; relation `77k + 11a + 21b = 0` has
no nontrivial solution with `|k|,|a|,|b| ≤ 4`), where the marked list is `s = (0, 1/7, 32/77, 1)`
and the image starts are `(66/77, 45/77, 0)`: the two sets meet only at `0`, yet the corrected field
holds with `ρ = (2, 1, 0)`.

**Repair.** The `cell` field now says what the paper says: `g ∘ f` is the exchange with lengths
`ν i = s (i+1) - s i` and permutation `ρ`, i.e. the translation on the `i`-th cell is
`listImageLeft ρ s i - listLeftEnd s i` where

```lean
def listLen s i       := s i.succ - s i.castSucc
def listLeftEnd s i   := ∑ j ∈ univ.filter (j < i), listLen s j
def listImageLeft ρ s i := ∑ j ∈ univ.filter (ρ j < ρ i), listLen s j
```

This form is *always* satisfiable (`ρ` = the rank of the image start `(g ∘ f)(s i)` among the image
starts), which is what the proof of `exists_compPresentation_on_ball` will have to produce; the
original form is satisfiable only when the marked list is the minimal cut set.  `toIsCutSet` needed
no change (it only uses that the displacement is independent of `x`), and neither did
`lam_eq_sum`/`mu_eq_sum`/`compLen_injective`, which never look at `cell`.

**Consequence for the proof.** Producing `ρ` needs the *partial-sum identity*: the image starts of
`g ∘ f` are the partial sums of the `ν`'s in image order.  That is `IsCutSet.imageLeft_lengths` of
`IET.lean` once the marked list is known to be an `IsCutSet` for `g ∘ f` (which follows from
`f_transl` + `g_transl` alone, no `ρ`), together with the identification of the `Finset`
enumeration `IsCutSet.cellStarts` with the list `s`.

## The ball argument for `exists_compPresentation_on_ball`: machinery landed (this session)

Build green at **5** `sorryAx`; every declaration added below is axiom-clean
(`[propext, Classical.choice, Quot.sound]`, checked in `Check.lean`).

### What was added, in the order it will be used

1. **`affine_comb`** — `G ((1 - t) • q₀ + t • q) = (1 - t) * G q₀ + t * G q` for `G : ParamAffine`.
2. **`comb_zero`**, **`pos_of_pos`**, **`sign_const`**, **`sign_congr`**, **`lt_iff_lt_of_ne`** — "the
   sign of an affine function of the parameters can only change where it vanishes".  `sign_const` is
   the finished version of the old `.scratch/try/sign.lean` (which had two errors: `div_pos` needed
   `0 < G q₀`, and `map_vadd` gives `G (t • (q - q₀) +ᵥ q₀)`, not `G ((1-t) • q₀ + t • q)`).
   `lt_iff_lt_of_ne` is the workhorse: a family of affine functions with no collision has the same
   pointwise order at every parameter, hence **the rank of `f (s k)` among the images, i.e. `ρ`, is
   locally constant**.
3. **`markedPos π τ k`** — the image `f (s k)` of the `k`-th marked point as an affine function of
   the free parameters, with `markedPos_zero` / `markedPos_inl` / `markedPos_inr` (the case analysis
   on `k` and `τ`) and **`markedPos_spec`**: on a good pair in the region,
   `f (s k) = markedPos k`.  This is the lemma the previous session tried to build with
   `compTypeF`; the `def`-with-`match` (and its `dif_pos`/`fin`-cast rewrites) was the blocker, and
   the fix is: **define it on `Fin n` by an `if j.val = 0` cascade whose middle branch is a plain
   `Sum.rec`** (no dependent match), and prove the evaluation lemma by splitting `j.val = 0` versus
   `j = ⟨m+1⟩` with the witness `m` built from plain `Nat` arithmetic (`∃ k, k + 1 = j.val`), then
   *`Fin`-casting once* — every `Fin` fact goes through `Fin.ext` on `Nat` facts, never `omega` on a
   `Fin` constructor (which is opaque to it).
4. **`upperEndAffineRight j`** — the upper end `leftEnd μ j + μ j` of a `g`-cell as an affine
   function, defined *piecewise* (`1` for the last cell, `cutAffineRight (j+1)` otherwise) so that
   `upperEndAffineRight_eq` is a two-case `rw` with the existing `leftEnd_eq_upperEnd_of_succ` and
   `upperEnd_of_max`.  (The first attempt added an `imageLenAffineRight` mirroring `imageLenAffine`;
   that needs a `Finset` sum identity to get from `cutAffineRight j + μ j` to `cutAffineRight (j+1)`,
   which the piecewise definition avoids entirely.)
5. **`imageInG_idx`** — `imageInG` with the index made explicit: the two `IsCompType.image`
   inequalities hold for `B k = idx μ (f (s k))`.  Derived from `imageInG` by showing that *its* `B`
   is `idx`, via `idx_eq` (the right end of a nonempty image is strictly above its left end, so the
   point is strictly inside the `g`-cell).
6. **`markedPos_eq_cut_of_eq`** — **the key non-vanishing lemma**: if `markedPos k q = cutAffineRight j q`
   at *one* `q` in the ball (with `j ≠ 0`), then `markedPos k = cutAffineRight j` as affine
   functions.  Proof: `f (s k) = leftEnd μ j` forces `s k = f⁻¹ (leftEnd μ j) = s (inr (j-1))`, and
   `StrictMono s` gives `k = inr (j-1)`, whose image is that cut identically.

### The remaining shape of `exists_compPresentation_on_ball` (design settled)

* `a := compTypeA τ`; `IsCompType.top` = `compTypeA_last`, `IsCompType.cut` = `compTypeA_cut`.
* `B k := idx μ_{q₀} (markedPos k q₀)`.  For `q` in the ball and `j ≠ 0`, `markedPos k - cutAffineRight j`
  is either `0` or nowhere zero (`markedPos_eq_cut_of_eq` + `sign_const`), so each `f (s k)` stays in
  the *same* `g`-cell as at `q₀` — that is `B` is locally constant — and the two inequalities of
  `IsCompType.image` follow from `imageInG_idx`.  **This is the piece to write next.**
* `ρ i :=` the rank of `markedPos i q₀` among the `markedPos · q₀` (`Finset.orderIsoOfFin` on the
  finite set of values, as in `IsCutSet.cellPerm`), and `lt_iff_lt_of_ne` makes the rank the same at
  every `q` of the ball.  The displacement in `IsCompPresentation.cell` is then
  `listImageLeft ρ s i - listLeftEnd s i`, and the identity follows from the **partial-sum identity**
  "the image starts are the sums of the `ν`'s in image order", which is
  `IsCutSet.sum_cellLen_image` once the marked list is known to be an `IsCutSet` for `g ∘ f` — that
  last step needs only `f_transl` + `g_transl` (no `ρ`), and it is a refactor of
  `IsCompPresentation.toIsCutSet`'s proof with `cell` replaced by the two translation fields.
  The identification of the `Finset` enumeration `IsCutSet.cellStarts` with the list `s` goes through
  `Finset.orderEmbOfFin_unique` (`s ·` is itself a strictly increasing enumeration of the cut set).
* The two remaining apologies (`exists_word_trivial_on_block`, `main_theorem_of_blocks`) are untouched.

## The `B` assembly is **PROVED** (this session): `exists_compImage_on_ball`

Build green at 5 `sorryAx`; axiom-clean.  This fills `IsCompType.image`, so `a := compTypeA τ` and
`B` are now both available on the ball.

```lean
theorem exists_compImage_on_ball (π) (κ : Fin (e-1) → Fin d)
    (τ : Fin (n-1) ≃ (Fin (d-1) ⊕ Fin (e-1))) {hn : 1 ≤ n} {A : ...}
    (hA : ∀ m, A m = singAffine π κ (τ m)) {q₀} {ε} (hε : 0 < ε)
    (hr : ∀ q ∈ ball q₀ ε, q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e)
    (hmono) (hzero) (htop) (hcut) (hpre) :
    ∃ B : Fin n → Fin e, ∀ q ∈ ball q₀ ε, ∀ (hl : ...) (k : Fin n),
      leftEnd μ (B k) ≤ f (s k.castSucc) ∧
        f (s k.castSucc) + (s k.succ - s k.castSucc) ≤ leftEnd μ (B k) + μ (B k)
```

(`hm` is not needed in the conclusion: the sum `∑ μ = 1` comes from `hr`.)

**The proof, in the order that works.**  `B k := idx μ_{q₀} (markedPos k q₀)`.

1. *Lower bound*: `markedPos k - cutAffineRight (B k)` is `≥ 0` at `q₀` (`idx_mem`) and propagates by
   `nonneg_on_ball_of_vanish_imp`, whose vanishing hypothesis is `markedPos_eq_cut_of_eq`; the case
   `B k = 0` is `leftEnd μ 0 = 0 ≤ f (s k)` and needs no propagation.
2. *Upper bound*: `upperEndAffineRight (B k) - markedPos k` is `> 0` at `q₀` (`lt_upperEnd_idx` +
   `upperEndAffineRight_eq`) and propagates by `pos_on_ball_of_vanish_imp`; the vanishing hypothesis
   is again `markedPos_eq_cut_of_eq`, **but only in the case `B k + 1 < e`** — there the upper end is
   `cutAffineRight (B k + 1)` (`upperEndAffineRight_of_lt`).  For `B k + 1 = e` the upper end is the
   constant `1`, and `markedPos k q = f (s k) < 1` always, so the hypothesis is vacuous
   (`upperEndAffineRight_of_last`).
3. *The `idx` is `B k` at every `q`*: `idx_eq` with the two bounds just proved, then `imageInG_idx`
   gives the two inequalities for that `idx`, and `simp only [hidx]` transports them to `B k`.

Traps met: `rw [← upperEndAffineRight_eq ...]` (the direction matters: `hlt` contains `upperEnd`,
not `upperEndAffineRight`); `sub_eq_zero.mpr hBeq.symm` for `markedPos k - cutAffineRight j = 0`;
`(AffineMap.const ℝ (PReal d e) (1 : ℝ)) q = 1` needs the `ℝ` annotation or the numeral is read as
`ℕ` (`AddTorsor ?m ℕ`); and a `∀ q ∈ ball, ∀ hl (hm), ...` conclusion drops `hm` because the sum
`∑ μ = 1` follows from `q.2 ∈ simplexRegion e`.

## `g` at a marked image is affine (this session): `markedImage_g`

```lean
theorem markedImage_g ... (hB : ∀ i, leftEnd μ (B i) ≤ P i ∧ P i + ν i ≤ upperEnd μ (B i)) (i) :
    g (P i) = P i + translationVector σ μ (B i)
```

where `P i = f (s i.castSucc)`.  Proof: `P i` lies in the `B i`-th `g`-cell, so `idx μ (P i) = B i`
(`idx_eq`), and `mkIETFun_of_mem` gives the translation.  Traps: `mkIETFun_of_mem` wants the
membership in `Ico (0 + 0) (0 + ∑ μ)` — the *lower* end must be literally `0`, the upper end
`0 + ∑`; and rewriting `P i - 0` to `P i` must be `simp only [sub_zero]`, not `rw [sub_zero]` (the
`rw` produces a `ring`-generated proof term and the dependent `idx` motive then fails).

Since `translationVector σ μ (B i) = imageLeftAffine σ (B i) q - cutAffineRight (B i) q` on the
region, this gives the **affine function**

```lean
Fgf i := markedPos i + (imageLeftAffine σ (B i) - cutAffineRight (B i))
```

with `Fgf i q = (g ∘ f) (s i.castSucc q)` on the ball.  That is the input for `ρ`:

* `Fgf i q ≠ Fgf j q` for `i ≠ j` on the ball — `g` and `f` are injective and `s` is strictly
  increasing;
* `ρ :=` the rank of `Fgf · q₀` among the `Fgf · q₀`, and `lt_iff_lt_of_ne` makes the rank the same
  at every `q` of the ball;
* `IsCompPresentation.cell` needs `Fgf i q - s i q = listImageLeft ρ s i - listLeftEnd s i`, i.e. the
  **partial-sum identity** `Fgf i q = ∑_{j : Fgf j q < Fgf i q} (s j.succ - s j.castSucc)(q)`.  The
  plan is the measure argument at the list level (disjoint images whose union is `[0, 1)`, then
  `volume` of `Ico 0 (Fgf i q)`), *not* the `Finset`/`orderIsoOfFin` route through `IsCutSet` — the
  latter needs the identification of `IsCutSet.cellStarts` with the list, which the list-level
  argument avoids.

## Inputs for `ρ` and `cell`, all proved (this session)

Build green at 5 `sorryAx`; everything below axiom-clean.

* **`sum_len_eq_of_tiling`** — the volume lemma: if the intervals `Ico (P i) (P i + ν i)` are
  disjoint and cover `[0,1)` (with `0 < ν i`, `0 ≤ P i`, `P i + ν i ≤ 1`), then
  `P i = ∑_{j : P j < P i} ν j`.  Proof: the intervals of `{j : P j < P i}` have union `Ico 0 (P i)`
  (no interval of the family crosses `P i`: otherwise `P i` would lie in two of them), then compare
  `volume`s with `measure_biUnion_finset` and `Real.volume_Ico`.  Traps: `Set.Ico` membership needs
  `le_of_lt` on the left component; `ENNReal.ofReal_sum_of_nonneg` is used **backwards**
  (`← ...`) at `hmain`; and the final step is
  `(ENNReal.ofReal_eq_ofReal_iff (h0 i) (Finset.sum_nonneg hnn)).mp`.
* **`sign_congr_on_ball`**, **`lt_iff_lt_of_ne_on_ball`** — the ball versions of the sign lemmas: on
  a ball where an affine function does not vanish its sign is constant (the affine combination of
  `q` and `q'` stays in the ball by `convex_ball`).
* **`exists_rank_perm`** — for affine `F : Fin m → ParamAffine d e` with no collisions on the ball,
  a permutation `ρ` with `ρ i < ρ j ↔ F i q < F j q` for every `q` in the ball.  Construction:
  `Finset.orderIsoOfFin` on `T = univ.image (F · q₀)` and `ρ i := iso.symm ⟨F i q₀, _⟩`, exactly as
  in `IsCutSet.cellPerm`.  Traps: `Equiv.ofBijective`'s value is a beta-redex (`beta_reduce` before
  rewriting); `Subtype.ext` wants `a.val = b.val` in the direction `F i q₀ = ↑(iso k)`, which is
  `hi` (from `Finset.mem_image.mp`), not `hi.symm`; the subtype order is `Subtype.mk_lt_mk`.
* **`imageLenAffineRight`**, **`imageLeftAffineRight`** (+ `_eq` on the region) — the `g`-side
  analogues of `imageLenAffine`/`imageLeftAffine`: the left end of the image of a cell of `g` as an
  affine function of the free parameters.  (`imageLeftAffine : Perm (Fin d) → ...` cannot be reused
  for `σ`, since its index type is tied to the *first* permutation; that was a genuine gap.)
* **`markedImage_gf`** — `(g ∘ f)(s i) = M i + (imageLeftAffineRight σ (B i) - cutAffineRight (B i))`:
  `(g ∘ f)` at a marked point is affine.  So writing

  ```lean
  Ggf i := markedPos i + (imageLeftAffineRight σ (B i) - cutAffineRight (B i))
  ```

  we have `Ggf i q = (g ∘ f) (s i.castSucc q)` on the ball, and `Ggf i q ≠ Ggf j q` for `i ≠ j`
  there (injectivity of `g`, of `f`, and `StrictMono s`).  `exists_rank_perm` applies to `Ggf`.

### What is left for `exists_compPresentation_on_ball`, precisely

1. **Expose the affine list.**  `exists_markedList` returns `s` existentially, but the lemmas above
   need `s = withEnds hn A` with `hA : ∀ m, A m = singAffine π κ (τ m)`.  Restate it as
   `∃ τ A ε, ... (withEnds hn A) ... ∧ (∀ m, A m = singAffine π κ (τ m))`, taking `κ` and its ball
   from `exists_ball_forall_imageLeft_lt` as *inputs* (the proof already builds `A` this way, so it
   is a matter of moving `A` from the proof into the statement).
2. **`ρ`**: `exists_rank_perm (fun i => Ggf i)`.
3. **`cell`** from two applications of `sum_len_eq_of_tiling` at each `q` of the ball:
   * `P := Ggf · q`, `ν i := s i.succ q - s i.castSucc q`: gives
     `Ggf i q = ∑_{j : Ggf j q < Ggf i q} ν j = listImageLeft ρ s i` (the second equality by the rank
     property of `ρ`);
   * `P := s · q`: gives `s i.castSucc q = ∑_{j : s j.castSucc q < s i.castSucc q} ν j
     = ∑_{j < i} ν j = listLeftEnd s i` (the middle equality by `StrictMono.lt_iff_lt`).
   The tiling facts for the first application: `0 < ν`, `0 ≤ P` (from `f`, `g` mapping into
   `[0,1)`), `P + ν ≤ 1` (**needs the sup argument**: if `P i + ν i > 1`, the point
   `x := s i.succ q - (P i + ν i - 1)/2` lies in `[s i, s i.succ)` — using `P i < 1` and `ν i > 0` —
   and `(g ∘ f) x = (P i + ν i + 1)/2 > 1`, contradicting `mapsTo`), disjointness (injectivity plus
   `Set.Ico_disjoint_Ico` for the cells) and the cover (`(g ∘ f)⁻¹ y` lies in some cell, by
   `exists_cell_of_strictMono`).  For the second application the cover is `exists_cell_of_strictMono`
   and the disjointness is `Set.Ico_disjoint_Ico` from `StrictMono`.
   The displacement of `(g ∘ f)` on each marked cell is `Ggf i q - s i.castSucc q`, from
   `markedCell_transl` + `markedCell_g_transl` (whose hypotheses are exactly `hmono`, `hzero`, `htop`,
   `hcut`, `hpre` — all available on the ball).
4. **The packing**: `IsCompPresentation`'s `zero`/`top`/`mono`/`card_eq` from `exists_markedList`,
   `f_transl`/`g_transl` from `markedCell_transl`/`markedCell_g_transl`, `cell` from item 3;
   `IsCompType`'s `top`/`cut` from `compTypeA_last`/`compTypeA_cut` and `image` from
   `exists_compImage_on_ball`.

## The partial-sum identity, both halves (this session)

Build green at 5 `sorryAx`; axiom-clean.

* **`exists_markedList` restated** to expose the affine list: it now takes the `g`-cut data
  (`k`, `ε₁`, `hε₁`, `hgood₁`, `hreg₁`, `hineq₁`, `hinv₁`, i.e. the output of
  `exists_ball_forall_imageLeft_lt`) as inputs, states its list as `withEnds hn A`, and returns
  `A` together with `∀ m, A m = singAffine π k (τ m)`.  The proof is unchanged except for the three
  bullets that are now `?_`-free: `hzero`/`htop`/`hcut`/`hpre` are stated about `withEnds hn A`, so
  the `hmid` steps had to say `withEnds hn A ⟨…⟩` instead of `s ⟨…⟩` (with `s` a local definition,
  `rw` no longer finds the pattern).  `hn : 1 ≤ d + e - 1` is now an explicit argument.

* **`partialSum_image`** — the image starts are the partial sums of the cell lengths:
  `F i q = ∑_{j : F j q < F i q} (s j.succ q - s j.castSucc q)`, given
  `F i q = (g ∘ f) (s i q)` on the ball and that `(g ∘ f)` is a translation on each marked cell.
  The five tiling facts: `0 < ν` (`StrictMono`), `0 ≤ F` and `F < 1` (`(g ∘ f)` maps `[0,1)` into
  itself, via `hmemcell`), `F + ν ≤ 1` (**the sup argument**: with `P = F`, `ν`, if `P + ν > 1` then
  `x := s.succ - (P + ν - 1)/2 ∈ [s, s.succ)` — using `P < 1` for the lower bound and `s.succ ≤ 1`
  plus `P + ν > 1` for the upper — and `h x = (P + ν + 1)/2 > 1`, contradicting `mapsTo`),
  disjointness (injectivity of `h` and disjointness of the cells), and the cover
  (`h.symm y ∈ [0,1)` needs a cut set for `h`: `h.isIET.exists_isCutSet (by norm_num)`, since
  `Equiv.IsIET.symm_mapsTo` wants an `IsCutSet` and there is no `IsIET` version).

* **`partialSum_cell`** — `s i.castSucc q = ∑_{j < i} (s j.succ q - s j.castSucc q)`, the same volume
  lemma applied to the cells themselves (`exists_cell_of_strictMono` for the cover, the explicit
  `y`-bounds for disjointness), followed by
  `Finset.filter_congr (fun j _ => (hmono q hq).lt_iff_lt)` to turn `{j : s j < s i}` into `{j : j < i}`.

### What remains for `exists_compPresentation_on_ball` (the final assembly)

Everything is now available; what is left is bookkeeping in one proof:

1. `κ`-data from `exists_ball_forall_imageLeft_lt`, then `τ, A, ε, …` from the restated
   `exists_markedList`.
2. `B` from `exists_compImage_on_ball`, `a := compTypeA τ` with `IsCompType.top/cut` from
   `compTypeA_last`/`compTypeA_cut`.
3. `Ggf i := markedPos i + (imageLeftAffineRight σ (B i) - cutAffineRight (B i))`, correctness
   `hGgf` from `markedImage_gf` (with `hM := markedPos_spec`), non-collision from injectivity of
   `g ∘ f`, then `ρ` from `exists_rank_perm`.
4. `IsCompPresentation.cell`: `(g ∘ f) x = x + (Ggf i q - s i.castSucc q)` from
   `markedCell_transl` + `markedCell_g_transl` (evaluate at `x = s i.castSucc`, which is in the
   cell), then rewrite with `partialSum_image` (whose filter becomes `{j : ρ j < ρ i}` by `hρ`),
   `partialSum_cell`, and `AffineMap.sum_apply` to evaluate `listImageLeft`/`listLeftEnd` at `q`.
5. `zero`/`top`/`mono`/`card_eq`, `f_transl`/`g_transl`, then the packing
   (`n := d + e - 1`, `s := withEnds hn A`, `ρ`, `a`, `B`).

## `exists_compPresentation_on_ball` is **PROVED**; the section is split into six modules

Build green, `declarations still depending on sorryAx: 4` (was 5): the two frozen sorries of
`Challenge.lean` and **two** in Section 3 — `exists_word_trivial_on_block` (Lemma 3.4) and
`main_theorem_of_blocks` (the assembly).  `ae_exists_goodRegion`, `exists_goodRegion` and
`exists_compPresentation_on_ball` are now axiom-clean (`[propext, Classical.choice, Quot.sound]`).

### The split (each file ≤ 1500 lines, dependency order)

| module | lines | contents |
|---|---|---|
| `Section3Setup` | 1074 | blocks, pair-splitting, the good set `O`, `ae_goodParams`, covering step |
| `Section3Presentation` | 1073 | `IsCompPresentation`/`IsCompType`, `compLen`, the affine cuts/lengths, sign lemmas, `sum_len_eq_of_tiling` |
| `Section3Singularities` | 1000 | `singAffine`, `withEnds`, `exists_markedList`, `markedCell_transl/_g_transl`, `markedPos`(+`_spec`, `_eq_cut_of_eq`) |
| `Section3Region` | ~1080 | `exists_compImage_on_ball`, `markedImage_g(_f)`, `partialSum_image/_cell`, `exists_rank_perm`, **`exists_compPresentation_on_ball`**, `GoodRegion` |
| `Section3LengthMap` | 673 | Lemma 3.1: `lam_eq_sum`, `mu_eq_sum`, `compLen_injective`, absolute continuity |
| `Section3Reduction` | 1374 | Lemma 3.2, Lemma 3.4, the assembly of Theorem 1.1 |

`Section3.lean` is now an umbrella module importing the six; `Build.sh` compiles them in that order
and its `sorry` counter includes their logs.  `IETFree.lean`'s docstring lists them.

### The assembly proof (in `Section3Region`), in the order that works

1. `⟨k, ε₁, …⟩ := exists_ball_forall_imageLeft_lt π hq₀ hr₀`; `hn : 1 ≤ d + e - 1` by `omega`.
2. `⟨τ, A, ε, …⟩ := exists_markedList π hq₀ hr₀ hn …` (the restated version, which returns `A`).
3. `⟨B, hB⟩ := exists_compImage_on_ball π k τ hA hε hreg hmono hzero htop hcut hpre`.
4. `Ggf i := markedPos π τ i + (imageLeftAffineRight σ (B i) - cutAffineRight (B i))`, with
   `hGgf : (g ∘ f) (s i) = Ggf i` on the ball from `markedImage_gf` (`hM` = `markedPos_spec`, and
   the `B` bounds transported along `hM` by `rw [hM i] at h`).  Note the `rw` must go through
   `IET.mul_apply` first, and the `set`-definition of `Ggf` through `hGgfdef` then `rfl`.
5. Non-collision `Ggf i q ≠ Ggf j q`: `(g ∘ f)` is injective (it is an `Equiv`), `StrictMono` gives
   `i.castSucc = j.castSucc → i = j` by `Fin.ext`/`simpa`.
6. `⟨ρ, hρ⟩ := exists_rank_perm Ggf hε hne`.
7. The conclusion is
   `⟨ε, hε, hgood, hreg, d + e - 1, withEnds hn A, ρ, compTypeA τ, B, rfl, fun q hq hl hm => …⟩`,
   with `IsCompPresentation`'s seven fields: `zero`/`top`/`mono` are `hzero`/`htop`/`hmono`;
   `cell` evaluates the displacement `δf + δg` at `x = s i` (`markedCell_transl`,
   `markedCell_g_transl`, `IET.mul_apply`, `ring`), converts it to `Ggf i q - s i q` via `hGgf`, then
   rewrites with `partialSum_image` (its `htransl` argument built inline from the two marked-cell
   translations), `Finset.filter_congr` with `hρ`, `listImageLeft`/`listLeftEnd`, and
   `partialSum_cell`; `f_transl`/`g_transl` are `markedCell_transl`/`markedCell_g_transl`; `card_eq`
   is `rfl`.  `IsCompType` is `⟨compTypeA_last τ, compTypeA_cut (τ := τ) … , hB q hq hl⟩` — the last
   two need their `τ`/`lam`/`s` arguments named, since they are implicit and not inferable from the
   subgoal alone.

## `main_theorem_of_blocks` is **PROVED**; Lemma 3.4 needs a hypothesis fix (this session)

Build green.  Source `sorry`s: **3** — the two frozen ones in `Challenge.lean` and
`exists_word_trivial_on_block` (Lemma 3.4).  `declarations still depending on sorryAx: 3`;
`main_theorem_of_blocks` is proved but correctly still reports `sorryAx`, since its only unproved
input is Lemma 3.4.

### A statement fix first: Lemma 3.4 must carry the two deep inputs

`exists_word_trivial_on_block` was stated **without** `(hMV : MasurVeech) (hVR : VeechRigidity)`,
while `main_theorem_of_blocks` was stated *with* them.  That cannot be: the only route to the
per-block word is Theorem 2.6, whose hypotheses `UniqueErgodic` / `IsRigidByTranslations` come from
Masur–Veech and Veech's rigidity.  Lemma 3.4 now takes them too (project decision 3: the deep inputs
are `def`s carried as hypotheses), and `main_theorem_of_blocks` passes them along.

### `main_theorem_of_blocks`

Proved from `exists_word_trivial_on_block` plus the already-proved
`exists_word_trivial_on_all_of_blocks`.  The only new mathematical content is the **block
decomposition of `[0, 1)` by the pair-splitting points**:

1. `mark_mem_insert` : a marked point `D.mark k` is `0`, `1`, or one of the cut points
   `D.markCuts` (the case `k = Fin.last n` is `1`, and for `k` with `k.val < n` the index
   `⟨k.val, _⟩ : Fin n` has `⟨k.val,_⟩.castSucc = k` *definitionally*, so `markCuts` catches it —
   this is much shorter than the `k.val - 1` route).
2. `T := insert 0 (insert 1 ((D.markCuts ∪ E.markCuts).filter (IsPairSplitting D E)))`.  Then
   * every `x ∈ T` is pair-splitting,
   * every pair-splitting `x` is in `T` (case analysis on the four disjuncts of `IsPairSplitting`,
     with `mark_mem_insert` for the last two),
   * `T ⊆ [0,1]`, `0, 1 ∈ T`.
3. Sort: `iso := Finset.orderIsoOfFin T rfl`, `t k := (iso k : ℝ)`.  The endpoints are
   `t 0 = T.min' = 0` and `t (last) = T.max' = 1`, via `orderEmbOfFin_zero` / `orderEmbOfFin_last`
   and `coe_orderIsoOfFin_apply`.
4. `n := T.card - 1`, `u i := t (Fin.castLE _ i.castSucc)`, `v i := t (Fin.castLE _ i.succ)`; the
   cover is `exists_cell_of_strictMono` applied to the reindexed list, the invariance is
   `IsPairSplitting.iff_mem`, the `IsBlock` for each `i` has `consecutive` from
   "`w` pair-splitting ⟹ `w ∈ T`" and strict monotonicity of `iso` (the contradiction is
   `i.val < j.val < i.val + 1`), and the word comes from Lemma 3.4 at that `IsBlock`.

Traps: `Finset.mem_insert_self _ _` needs the elements given explicitly (`insert (0 : ℝ)`);
`Fin.strictMono_castLE h` is a *proof of `StrictMono`*, so it is applied (`Fin.strictMono_castLE _ h`)
rather than passed as an inequality; and `IsPairSplitting` is a **four**-way disjunction, so the
filtered membership is `Or.inr (Or.inr (Or.inl ⟨…⟩))`.

### What Lemma 3.4 still needs (the analysis, for the next session)

The route is the paper's: restrict `f` and `g` to the block `[u,v)` (invariant under both), rescale
to `[0,1)`, and apply Theorem 2.6 to the pair `(g̃ ∘ f̃, g̃)` — the *composition* is irreducible on
the block by Lemma 3.2, so Masur–Veech and Veech apply to it, and a word trivial for the rescaled
pair is trivial on the block.  What is missing is API, in three pieces:

1. **Restriction/rescaling.** For an `IETDatum D` and an invariant interval `[u,v)`, the map
   `x ↦ D.toFun (u + x(v-u))` rescaled back is an `IET 0 1`; its permutation and length vector, and
   the identification of the *composition* on the block with `mkIET1 (compLen) (ρ|block)` from
   `GoodRegion`.  Nothing of this is in `IET.lean` yet.
2. **`IsIrreducibleOn → IsIrreduciblePerm`.** `block_irreducible_on_good` concludes the
   `IsIrreducibleOn` form (no invariant initial segment); Masur–Veech wants `IsIrreduciblePerm ρ` for
   the permutation of the block.  The bridge: an invariant initial segment `{i : i < k}` of `ρ` with
   `k ≠ 0, last` makes `[0, leftEnd ν k)` invariant for `mkIET1 ν ρ`, hence for the composition on the
   block, contradicting `IsIrreducibleOn`.
3. **The a.e. transfer.** `IsDiophantine` for the block lengths `(ν, μ|block)` holds a.e. in
   `(ν, μ|block)` (`Diophantine.lean`'s a.e. statement), and pulls back to a.e. `(λ, μ)` along the
   affine map `(λ,μ) ↦ (ν, μ|block)`, which is injective on `GoodRegion` and has an absolutely
   continuous pushforward — exactly `GoodRegion.compLen_absolutelyContinuous`.  Then
   `ae_of_ae_compLen` and `irreducible_case`.

Items 1 and 2 are the real work; item 3 is bookkeeping on top of Lemma 3.1.

## New module `Section3BlockWord`: rescaling core and the block permutation irreducibility (this session)

Build green, `declarations still depending on sorryAx: 3` (the two frozen ones and Lemma 3.4).  All
new declarations are axiom-clean.

`Section3BlockWord` (193 lines, importing `Section3Singularities`, placed between
`Section3LengthMap` and `Section3Reduction` in `Build.sh`) holds the ingredients of Lemma 3.4 that
are independent of the a.e. argument:

* **the rescaling core**: `rescaleMap u v x = (x-u)/(v-u)`, `rescaleMapInv u v y = u + y*(v-u)`, the
  two round trips (`field_simp` needs the goal rearranged to `y * (v-u)/(v-u) = y` first — plain
  `field_simp; ring` leaves the `⁻¹` in place), `rescaleMap_mem`
  (`rescaleMap u v x ∈ [0,1) ↔ x ∈ [u,v)`, needing `div_nonneg_iff`/`div_lt_one`), `rescaleFun`,
  and `rescaleFun_comp` (`rescaleFun u v (f ∘ g) = rescaleFun u v f ∘ rescaleFun u v g`, which is the
  algebra behind "a word trivial for the rescaled pair is trivial on the block");
* **`mkIET1_apply`**: `mkIET1 lam π hl x = x + (imageLeft π lam i - leftEnd lam i)` for
  `i = idx lam x`, i.e. the translation of the cell of `x` (from `mkIETFun_of_mem`, with
  `simp only [sub_zero]` rather than `rw [sub_zero]` inside the `idx` term);
* **`imageLeft_add_le_of_invariant`**: if `{m | m ≤ k}` is `π`-invariant, then
  `imageLeft π lam i + lam i ≤ leftEnd lam (k+1)` for `i ≤ k`.  The key step is
  `{m | m ≤ k} = {m | π m ≤ k}`: `π` maps the finite set into itself, hence onto it by
  `Finset.eq_of_subset_of_card_le` + `Finset.card_image_of_injective`, and injectivity then gives the
  converse;
* **`irreduciblePerm_of_no_invariant_cut`**: `IsIrreduciblePerm π` from the geometric statement
  "no `k ≠ 0` has `[0, leftEnd lam k)` invariant under `mkIET1 lam π hl`" (with all lengths positive).
  This is the bridge from Lemma 3.2's `IsIrreducibleOn` to what Masur–Veech needs.  Proof: given an
  invariant `{i | i ≤ k}` with `k ≠ 0` and `k` not the last index, the interval
  `[0, leftEnd lam (k+1))` is invariant — for `x` in the cell `i ≤ k`,
  `f x < imageLeft π lam i + lam i ≤ leftEnd lam (k+1)` — contradicting the hypothesis at `k+1`.
  Traps: `leftEnd_lt_leftEnd` needs *strict* monotonicity, so the case `k+1 = i` must be separated
  (there the two left ends are equal and the contradiction is immediate); `Fin.lt_def`/`Fin.le_def`
  must be applied to the *matching* relation (`rw [Fin.lt_def] at hi` for `hi : i < k`).

### Still missing for Lemma 3.4 (unchanged from the previous analysis, items 1 and 3)

* the rescaled restriction **as an `IET 0 1`**: `rescaleFun u v F` must be packaged with its cut set
  (the rescaled `D.markCuts` inside `(u,v)`) so that `evalWord` applies to it, and then the
  equivariance `evalWord w (rescaled F) (rescaled G) = 1 → evalWord w F G = id on [u,v)` proved by
  induction on the word (`FreeGroup.lift` congruence), together with the identification of the
  rescaled composition with `mkIET1 (compLen) (ρ|block)` from `GoodRegion`;
* the a.e. transfer of `IsDiophantine` along the length map (`GoodRegion.compLen_absolutelyContinuous`
  + `ae_of_ae_compLen`), then `irreducible_case`.

## `evalWord` conjugacy: design settled, not landed (this session — **landed** later, see "`evalWordEquiv_conj` is **PROVED**"; that declaration has since been deleted as unused)

Build green, `sorryAx` 3.  `Section3BlockWord` holds, and keeps, the rescaling core and
`irreduciblePerm_of_no_invariant_cut` (see the section above).

**A design finding that matters.**  The rescaled restriction of an exchange to an invariant `[u,v)`
is **not** an `IET 0 1`: `IsIET 0 1` demands the map be the identity outside `[0,1)`, whereas the
invariance of `[u,v)` only says that the complement `[0,u) ∪ [v,1)` is mapped *into itself* — for
`y ∈ [v,1)` the rescaled value `R (F (R⁻¹ y))` need not be `y`.  So `evalWord`, whose arguments are
`IET 0 1`, cannot be applied to the rescaled pair directly, and the conjugacy has to be stated for
`Equiv ℝ ℝ`:

* `evalWordEquiv w A B := FreeGroup.lift (fun i => if i = 0 then A else B) w` on `Equiv ℝ ℝ`;
* `evalWord_toEquiv : (evalWord w F G).toEquiv = evalWordEquiv w F.toEquiv G.toEquiv`;
* `evalWordEquiv_conj : MulAut.conj R (evalWordEquiv w A B) = evalWordEquiv w (conj R A) (conj R B)`.

Both follow from one naturality statement,
`φ ((FreeGroup.lift f) w) = (FreeGroup.lift (φ ∘ f)) w` for a monoid hom `φ` (`FreeGroup.lift` is an
`≃`, so there is no `lift_comp`; `FreeGroup.lift_unique` and `FreeGroup.lift_apply_of` are the
tools).  **Where I got stuck**: encoding `φ := { toFun := IET.toEquiv, map_one' := rfl,
map_mul' := fun _ _ => rfl }` as a `MonoidHom` and closing the generator case leaves the residual
goal `φ F = F.toEquiv`, which neither `simp [φ]` nor `rfl` reduced (the `let`-bound structure literal
did not unfold as expected).  The fix to try next is to prove the naturality as a **standalone lemma
by `FreeGroup.induction_on`** — cases `1`, `FreeGroup.of x`, `(FreeGroup.of x)⁻¹`, `x * y`, closed by
`simp`/`map_mul`/`map_inv`/`FreeGroup.lift_apply_of` — and only then instantiate it; that avoids the
structure literal entirely.

**Remaining pipeline for Lemma 3.4** (unchanged otherwise): after the conjugacy,
1. the identification of `rescaleFun u v ⇑(D.toIET * E.toIET)` with `mkIET1 (compLen) (ρ|block)` from
   `GoodRegion` (its cut set is the rescaled `D.markCuts` inside `(u,v)`; `IsCutSet.eq_mkIETFun`
   gives the `mkIET1` form once the cut set and its `lengths`/`perm` are computed);
2. `IsIrreduciblePerm` for `ρ|block` from Lemma 3.2 — `irreduciblePerm_of_no_invariant_cut` is
   already in place, only the instantiation at the block remains;
3. the a.e. transfer of `IsDiophantine` to the block lengths along `GoodRegion.compLen_absolutelyContinuous`
   + `ae_of_ae_compLen`, then `irreducible_case`, then the conjugacy to get the word back on the block.

## Naturality of `FreeGroup.lift` and the `Equiv`-valued word evaluation (this session)

Build green, `sorryAx` 3; both new declarations axiom-clean.  Landed in `Section3BlockWord`
(now 222 lines):

```lean
theorem freeGroup_lift_natural {α G H} [Group G] [Group H] (φ : G →* H) (f : α → G)
    (w : FreeGroup α) : φ ((FreeGroup.lift f) w) = (FreeGroup.lift (fun x => φ (f x))) w

noncomputable def evalWordEquiv (w : FreeGroup Gen) (A B : Equiv ℝ ℝ) : Equiv ℝ ℝ :=
  FreeGroup.lift (fun i : Gen => if i = 0 then A else B) w

theorem evalWord_toEquiv (F G : IET 0 1) (w : FreeGroup Gen) :
    (evalWord w F G).toEquiv = evalWordEquiv w F.toEquiv G.toEquiv
```

**How `freeGroup_lift_natural` went through** (`FreeGroup.induction_on`, whose case names are
`C1`, `of`, `inv_of`, `mul` — *not* `h1`/`hgen`/…; Lean reports the expected names):

```lean
  | C1 => simp
  | of x => simp [FreeGroup.lift_apply_of]
  | inv_of x _ => simp only [map_inv, FreeGroup.lift_apply_of]
  | mul x y ihx ihy => simp only [map_mul, ihx, ihy]
```

(the `inv_of` case does not need its induction hypothesis: `map_inv` on both sides suffices).

**`evalWord_toEquiv` also goes by `FreeGroup.induction_on`**, not through `freeGroup_lift_natural`:
the `MonoidHom` structure literal `{ toFun := IET.toEquiv, … }` is what blocked the earlier attempt
(its application never reduced to `F.toEquiv` under `simp`/`rfl`).  By induction, the two structural
facts `((evalWord u F G)⁻¹).toEquiv = ((evalWord u F G).toEquiv)⁻¹` and
`(evalWord u F G * evalWord v F G).toEquiv = …` are `rfl`, so each case closes with `simp only
[evalWord_inv, map_inv, evalWordEquiv, h1, ih]`.

**Still open: `evalWordEquiv_conj`**,
`MulAut.conj R (evalWordEquiv w A B) = evalWordEquiv w (MulAut.conj R A) (MulAut.conj R B)`.
The obstruction is purely syntactic: `MulAut.conj R` appears as a *coercion* `↑(MulAut.conj R)` in the
goal but as `(MulAut.conj R)` in the induction hypothesis, so neither `rw [ih]` nor `rw [hgen]`
matches inside `FreeGroup.lift`'s argument (and `FreeGroup.lift` is an `≃`, so rewriting under it is
hostile).  The next thing to try: state the conjugation through `MulAut.conj_apply`
(`MulAut.conj R X = R * X * R⁻¹`) so that everything is `*` and `⁻¹` on `Equiv ℝ ℝ` with no
coercions, and induct with `| of x => by_cases hx : x = 0 <;> simp [hx, evalWordEquiv]` plus
`mul_assoc` normalisation in the `mul` case.

## `evalWordEquiv_conj` is **PROVED** via `MulAut.conj_apply` (this session)

Build green, `sorryAx` 3; axiom-clean.  `Section3BlockWord` is now 241 lines and the conjugacy
machinery for Lemma 3.4 is complete:

```lean
theorem evalWordEquiv_conj (w : FreeGroup Gen) (A B R : Equiv ℝ ℝ) :
    MulAut.conj R (evalWordEquiv w A B)
      = evalWordEquiv w (MulAut.conj R A) (MulAut.conj R B)
```

The recipe that worked, exactly as predicted in the previous section: rewrite the two `MulAut.conj`s
into `R * · * R⁻¹` with `MulAut.conj_apply` (three `show … from MulAut.conj_apply …` rewrites, so no
coercion survives), then `FreeGroup.induction_on`:

```lean
  | C1 => simp [evalWordEquiv]
  | of x => by_cases hx : x = 0 <;> simp [hx, evalWordEquiv, FreeGroup.lift_apply_of]
  | inv_of x ih => simp only [evalWordEquiv, map_inv] at ih ⊢; rw [← ih]; group
  | mul x y ihx ihy => simp only [evalWordEquiv, map_mul] at ihx ihy ⊢; rw [← ihx, ← ihy]; group
```
(the `mul` case is the identity `R (Y₁Y₂) R⁻¹ = (R Y₁ R⁻¹)(R Y₂ R⁻¹)`; the `inv_of` case the same for
inverses — `group` closes both.)

### Lemma 3.4: what remains, in the order it must be done

With the conjugacy available, the outstanding items are all on the *geometric* side:

1. **The block presentation.**  For `IsBlock D E u v` on a good region, the rescaled composition
   `rescaleFun u v ⇑(D.toIET * E.toIET)` must be identified with `mkIET1 ν_b ρ_b` for the block data
   `ν_b` (the marked lengths inside `(u,v)`, `GoodRegion.compLen`) and the block permutation `ρ_b`.
   The route: the rescaled marked points inside `(u,v)` are a cut set (`IsCutSet`, transported through
   the affine rescaling), `IsCutSet.eq_mkIETFun` gives the `mkIET1` form, and `IsCutSet.perm`/`lengths`
   identify `ρ_b` with `ρ` restricted.  This is the largest single item.
2. **`IsIrreduciblePerm ρ_b`** from Lemma 3.2: instantiate `irreduciblePerm_of_no_invariant_cut` at
   the block, with `IsIrreducibleOn` converted to "no invariant initial interval".
3. **The a.e. transfer**: `UniqueErgodic`/`IsRigidByTranslations` for `mkIET1 ν_b ρ_b` come from
   `MasurVeech`/`VeechRigidity` at the irreducible `ρ_b`, a.e. in `ν_b`; `IsDiophantine ν_b μ_b` holds
   a.e. in `(ν_b, μ_b)` (`Diophantine.lean`); both pull back to a.e. `(λ, μ)` along the affine
   injective length map of `GoodRegion.compLen_absolutelyContinuous` via `ae_of_ae_compLen`.
4. `irreducible_case` gives the word for the rescaled pair; `evalWord_toEquiv` + `evalWordEquiv_conj`
   transport it back to the block, giving `∃ w ≠ 1` trivial on `[u,v)`.

## Attempt at `evalWord_conj_apply` (this session): not landed then — **landed** later; the lemma now exists and is used in `GeneratorChange`

Build unchanged and green: `sorryAx` 3, the single Section-3 `sorry` is
`exists_word_trivial_on_block`.

The next piece of Lemma 3.4 I attacked is the **word transport**: if `φ` maps `[0,1)` into itself
and conjugates the generators (`F (φ y) = φ (F' y)`, `F⁻¹ (φ y) = φ (F'⁻¹ y)`, same for `G`), then

```lean
theorem evalWord_conj_apply ... (w : FreeGroup Gen) :
    ∀ y ∈ Set.Ico (0 : ℝ) 1, evalWord w F G (φ y) = φ (evalWord w F' G' y)
```

so that `irreducible_case`'s word for the rescaled pair is trivial at `φ y`, i.e. on the block
(`φ = rescaleMapInv u v`).  The induction is `FreeGroup.induction_on` with the four cases; `C1` and
`mul` are fine (the `mul` case needs `(evalWord v F' G') (φ y) ∈ [0,1)`, which is
`(evalWord v F' G').isIET.mapsTo`, and there the implicit point must be pinned — the membership has to
be moved into a `have` whose *type* mentions the point explicitly, otherwise Lean cannot infer the
implicit `x` of `Equiv.IsIET.mapsTo`).  The two cases still failing are the `of`/`inv_of` cases when
the generator is `genY`: after `simp only [evalWord, FreeGroup.lift_apply_of]` the goal contains
`if x = 0 then F else G`, and with `hx : ¬ x = 0` in context both `simp only [hx, if_neg]` and
`rw [if_neg hx]` report "no progress"/leave the goal — the unnamed `Gen` has two elements and the
`if` is not being discharged by the hypothesis alone.  The fix to try next: replace
`by_cases hx : x = 0` by `rcases` on the two-element type (`Gen` is `Fin 2`-like, so
`Fin.eq_zero_or_eq_one`/`Gen.eq_zero_or_eq_one` should give `x = 0 ∨ x = 1`), or state the `of`-case
identity as `evalWord (FreeGroup.of x) F G = if x = 0 then F else G` and rewrite with `h1`/`h2` as I
did in the earlier attempt and *then* close with `rw [if_neg hx, if_neg hx]` — that variant did close
the `of` case but then reported "no goals" on the following `exact hG y hy`, so the two branches need
to be written asymmetrically.

Everything else from the previous sections stands: the conjugacy on `Equiv`s
(`evalWordEquiv_conj`), the `IET`/`Equiv` bridge (`evalWord_toEquiv`), the rescaling core, the block
permutation irreducibility.  Lemma 3.4's remaining geometric core (the block presentation
`mkIET1 ν_b ρ_b` and the a.e. transfer of Masur–Veech / Veech / Diophantine) is unchanged and still
the bulk of the work.

## Block presentation: design, and why I stopped (this session — **done**: `exists_compPresentation_on_ball` is proved, see the entry of that name)

No new declaration this session.  `./Build.sh` green, `sorryAx` 3 (the two frozen ones and
`exists_word_trivial_on_block`), 6608 lines in the eight `Section3*` modules.

### The precise shape of the missing piece

Let `GoodRegion d e π σ q₀` be the datum (`O`, `n`, `s`, `ρ`, `a`, `B`, `pres`, `type`) and let
`q ∈ O`.  Write `S := fun k => s k q`, `ν k := S (k+1) - S k`.

For a block `[u,v)` of the pair, the two endpoints are pair-splitting points, hence **marked
points**: `u = S i₀`, `v = S i₁` for some `i₀ < i₁` (the cuts of `f` are `S (a i.castSucc)` by
`IsCompType.cut`, and the preimages of the cuts of `g` are `S (inr j)` by `IsCompPresentation`'s
`f_transl`/the `hpre` field of `exists_markedList`).  The block is invariant, so
`ρ` maps the run `{i₀, …, i₁-1}` into itself.  The block datum is

```
ν_b k := ν (i₀ + k)              (k : Fin (i₁ - i₀))
ρ_b k := ρ (i₀ + k) - i₀
```

and the claim to formalize is: `rescaleFun u v ⇑(g ∘ f)` agrees on `[0,1)` with `mkIET1 ν_b ρ_b`.
Both sides are piecewise translations with the same cut list `{(S j - u)/(v-u) : i₀ < j < i₁}` and
the same displacement on each piece — the left-hand side by `IsCompPresentation.cell` (the
displacement `listImageLeft ρ S j - listLeftEnd S j`, rescaled), the right-hand side by
`mkIET1_apply`.  So **the clean route is `funext x` + the cell decomposition of `[0,1)` by the
rescaled list** (`exists_cell_of_strictMono`), comparing `mkIET1_apply` with the rescaled
`cell` field — *not* the `IsCutSet.eq_mkIETFun` route I sketched earlier: that one would need the
whole `IsCutSet` transport through the affine rescaling plus the identification of `cellStarts` with
the list, whereas the `funext`/cell comparison only needs
`listImageLeft ρ S (i₀+k) = listImageLeft ρ_b ν_b k + (image start of the block)` and
`listLeftEnd S (i₀+k) = listLeftEnd ν_b k + u`, two `Finset` splitting lemmas over
`{j : ρ j < ρ (i₀+k)}` with the `ρ`-invariance of the run.

### The two `Finset` lemmas that carry it

1. `listLeftEnd` splits at a block:
   `listLeftEnd ν_b k = ∑ j ∈ Ico i₀ (i₀+k), ν j = listLeftEnd S (i₀+k) - listLeftEnd S i₀`
   (`Finset.sum_Ico_eq_sub` on the `ℕ`-indexed `markExt` extension, or induction on `k`).
2. `listImageLeft` splits under the invariance of the run `R := {j | i₀ ≤ j < i₁}` under `ρ`:
   every `j` with `ρ j < ρ (i₀+k)` is either in `R` (contributing inside the block) or has
   `ρ j < (image offset of the block)`; since `ρ '' R = R` and the block's image is an interval of
   the image partition, the sum over the block's predecessors has exactly the block's offset added.

### Then irreducibility

With the presentation `mkIET1 ν_b ρ_b` in hand,
`IsCompPresentation`/`block_irreducible_on_good` (Lemma 3.2, proved) gives the geometric statement
"no `c` inside the block is invariant"; transported back through the rescaling it becomes the
hypothesis of `irreduciblePerm_of_no_invariant_cut` (proved) at `ν_b`, `ρ_b` — giving
`IsIrreduciblePerm ρ_b`, which is what `MasurVeech`/`VeechRigidity` need.

### Status of the rest

Proved and axiom-clean: Lemma 3.1 in both halves, Lemma 3.2, the local presentation
(`exists_compPresentation_on_ball`, `GoodRegion`, `ae_exists_goodRegion`), the block decomposition of
`[0,1)` and the assembly (`main_theorem_of_blocks`, modulo Lemma 3.4), the rescaling core, the block
permutation irreducibility, and the whole word-conjugacy machinery
(`freeGroup_lift_natural`, `evalWordEquiv`, `evalWord_toEquiv`, `evalWordEquiv_conj`).  Unproved:
`exists_word_trivial_on_block` — the block presentation above, the word transport
`evalWord_conj_apply` (three of four `FreeGroup` cases done; the `of`/`inv_of` cases at `genY` are a
`simp`-discharge problem, `Gen` being `Fin 2`), and the a.e. transfer of Masur–Veech / Veech /
Diophantine along `GoodRegion.compLen_absolutelyContinuous`.

## Block splitting: the three lemmas landed (this session)

Build green, `sorryAx` 3; all three axiom-clean.  `Section3BlockWord` is now 340 lines.  Landed, with
the names used below:

```lean
theorem mark_eq_markedList (P : IsCompPresentation lam π mu σ hl hm n s ρ)
    (T : IsCompType lam π hl mu s a B) (k : Fin (d + 1)) :
    s (a k) = ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val < k.val), (lam j : ℝ)

theorem listLeftEnd_sub {s : Fin (n + 1) → ℝ} {i₀ i₁ : Fin n} (h : i₀ ≤ i₁) :
    listLeftEnd s i₁ - listLeftEnd s i₀
      = ∑ j ∈ Finset.univ.filter (fun j : Fin n => i₀ ≤ j ∧ j < i₁), (s j.succ - s j.castSucc)

theorem listImageLeft_sub_of_Icc {ρ : Equiv.Perm (Fin n)} {R : Finset (Fin n)} {a b : Fin n}
    (hR : ∀ j, j ∈ R ↔ (a ≤ ρ j ∧ ρ j ≤ b)) {S : Fin (n + 1) → ℝ} {i₀ i₁ : Fin n}
    (h₀ : ρ i₀ = a) (h₁ : i₁ ∈ R) :
    listImageLeft ρ S i₁ - listImageLeft ρ S i₀
      = ∑ j ∈ R.filter (fun j : Fin n => ρ j < ρ i₁), (S j.succ - S j.castSucc)
```

* `mark_eq_markedList` is the **endpoints-as-marked-points lemma, `f` side**: the right-hand side is
  `IETDatum.mark` read as a sum, so the `k`-th marked point of `f` sits at the `a k`-th position of
  the list.  Proof: `k = Fin.last d` is `T.top` + `P.top` + the total mass `∑ lam = 1`; every other
  `k` is `m.castSucc` for `m : Fin d`, and then it is `T.cut m` with `leftEnd` unfolded (the filters
  `{j.val < m.val}` and `{j < m}` agree by `Fin.lt_def`).
* `listLeftEnd_sub` is the first splitting lemma: split `{j < i₁}` into `{j < i₀}` and
  `{i₀ ≤ j < i₁}` (`Finset.sum_union` of the two disjoint filters) and `ring`.
* `listImageLeft_sub_of_Icc` is the second, in the form in which it is **provable**: the block is
  given by its `ρ`-values lying in an interval `[a, b]` with `a = ρ i₀` the *first* cell.  Then
  `{ρ j < a} ⊆ {ρ j < ρ i₁}` and the difference of the two filters is exactly
  `R.filter (ρ · < ρ i₁)`; `Finset.sum_sdiff` gives the splitting.  Note that the extra hypothesis
  (the block's `ρ`-values are consecutive) is **not** combinatorial — it is the geometric statement
  that the image of the block is one interval of the image partition, i.e. the invariance of the block
  under the exchange, and it must be supplied by the block-presentation proof before this lemma
  applies.

### What the block presentation still needs, after these three

1. the `g`-side counterpart of `mark_eq_markedList`: **every cut of `g` is a marked point**.  From
   `IsCompPresentation.g_transl` (g is a translation on the image of each `s`-cell) plus the tiling of
   the images: a cut `leftEnd mu j` cannot lie strictly inside the image `(f (s i), f (s (i+1)))` of an
   `s`-cell (that would make `g` continuous there), so it equals some `f (s i)`, i.e. `s i` is the
   preimage of a cut — which `IsCompPresentation` records only through `g_transl`, so this needs the
   tiling argument of `partialSum_image`'s disjointness/cover facts rather than a field read-off;
2. the block run `R = {j | i₀ ≤ j < i₁}` from the two endpoints (`mark_eq_markedList` gives the
   `f`-side; item 1 gives the `g`-side), `ρ`-invariance of `R`, and the consecutiveness hypothesis of
   `listImageLeft_sub_of_Icc`;
3. `rescaleFun u v ⇑(g ∘ f) = mkIET1 ν_b ρ_b` by `funext` + the cell comparison of
   `IsCompPresentation.cell` with `mkIET1_apply`, using `listLeftEnd_sub` and
   `listImageLeft_sub_of_Icc` with `ν_b k = ν (i₀ + k)`, `ρ_b k = ρ (i₀ + k) - i₀`.

## The `g`-side: pair-splitting points are marked points (this session)

Build green, `sorryAx` 3; both new lemmas axiom-clean.  `Section3BlockWord` is now 374 lines.

```lean
theorem mark_fixed_of_inFixedCell {d e} [NeZero d] [NeZero e] (D : IETDatum d) (E : IETDatum e)
    (j : Fin (e + 1)) (h : E.InFixedCell D j) : D.toFun (E.mark j) = E.mark j

theorem pairSplitting_mem_markedList {d e n} [NeZero d] [NeZero e] {D : IETDatum d}
    {E : IETDatum e} {s : Fin (n + 1) → ℝ}
    (hD : ∀ k : Fin (d + 1), ∃ i : Fin (n + 1), s i = D.mark k)
    (hE : ∀ j : Fin (e + 1), ∃ i : Fin (n + 1), s i = D.toIET⁻¹ (E.mark j))
    {x : ℝ} (hx : IsPairSplitting D E x) : ∃ i : Fin (n + 1), s i = x
```

### The plan changed here, and for a good reason

The lemma I had planned — "every cut of `g` is a marked point" — is **false**, and its intended proof
(continuity of `g` on the image of a marked cell) cannot work: `g` may be *continuous* at a listed cut
(`σ j = σ (j-1) + 1`), and then that cut sits strictly inside the image of a marked cell without
contradicting `g_transl`.  What is true, and is what the block presentation actually needs, is that
the **pair-splitting** points are marked — and the reason is `IsPairSplitting`'s own structure: the
`g`-disjunct carries `E.InFixedCell D j`, i.e. the point lies in a cell of `D` on which `D` is the
identity (`IETDatum.isFixedCell_apply`).  So `D` fixes the point, hence `D⁻¹` of it is itself, and the
marked list — which contains the `D`-preimages of the marked points of `E` (`hE`) — contains it.  No
tiling argument is needed at all.

Note the shape of the hypotheses: `hD` is `mark_eq_markedList` (proved last session, `f`-side), and
`hE` is the `hpre` field of `exists_markedList` (`s (inr j) = f⁻¹ (leftEnd mu (j+1))`), so both are
available in the `GoodRegion`/`exists_word_trivial_on_block` context; `GoodRegion` will have to record
`hE`, since `IsCompPresentation`'s `g_transl` is the weaker "refines the `f`-preimage partition"
statement.

### Remaining for the block presentation

1. the run `R = {j | i₀ ≤ j < i₁}` from the two endpoints (`pairSplitting_mem_markedList`), its
   `ρ`-invariance, and the consecutiveness of the `ρ`-values on `R` (the geometric input that
   `listImageLeft_sub_of_Icc` takes as a hypothesis — from the block's invariance);
2. `rescaleFun u v ⇑(g ∘ f) = mkIET1 ν_b ρ_b` by `funext` + cell comparison of
   `IsCompPresentation.cell` against `mkIET1_apply`, with `listLeftEnd_sub` and
   `listImageLeft_sub_of_Icc`;
3. then `irreduciblePerm_of_no_invariant_cut` at the block, the a.e. transfer of Masur–Veech / Veech /
   Diophantine along `compLen_absolutelyContinuous`, `irreducible_case`, and the word transport
   `evalWord_conj_apply` (whose `of`/`inv_of` cases at `genY` are still open — `Gen = Fin 2`, so
   `Fin.eq_zero_or_eq_one`-style case analysis should close them).

## Consecutiveness of the `ρ`-values on a block: the combinatorial half (this session)

Build green, `sorryAx` 3; both axiom-clean.  `Section3BlockWord` is now 421 lines.

```lean
theorem listImageLeft_lt {ρ : Equiv.Perm (Fin n)} {S : Fin (n + 1) → ℝ}
    (hpos : ∀ j, 0 < S j.succ - S j.castSucc) {j₁ j₂ : Fin n} (h : ρ j₁ < ρ j₂) :
    listImageLeft ρ S j₁ < listImageLeft ρ S j₂

theorem rho_convex_of_image_Ico {ρ} {S} (hpos : ∀ j, 0 < S j.succ - S j.castSucc)
    {lo hi : ℝ} {j₁ j₂ j₃ : Fin n} (h₁ : lo ≤ P j₁) (_h₁' : P j₁ < hi)
    (h₃' : P j₃ < hi) (h₁₂ : ρ j₁ < ρ j₂) (h₂₃ : ρ j₂ < ρ j₃) :
    lo ≤ P j₂ ∧ P j₂ < hi
```

* `listImageLeft_lt`: `listImageLeft ρ S j = ∑_{ρ m < ρ j} ν m`, and `ρ j₁ < ρ j₂` makes
  `{ρ m < ρ j₁} ⊊ {ρ m < ρ j₂}` — the index `j₁` is in the second set and not the first — so the sum
  strictly increases (`Finset.sum_sdiff` + `Finset.sum_pos` with the witness `j₁`).
* `rho_convex_of_image_Ico`: two applications of `listImageLeft_lt` sandwich the middle cell's image
  start inside `[lo, hi)`.  In other words: **the `ρ`-values of a block are consecutive as soon as the
  block is cut out by an interval of image coordinates**.

### What is left of the consecutiveness claim, and of the block presentation

1. **The geometric half of consecutiveness**: the block's cells are exactly those whose image start
   `P j` lies in `[P i₀, P i₀ + L)` (`L = S i₁ - S i₀`).  This is where the invariance of the block
   is consumed: `h '' block = block` (the block is mapped *into* itself by a bijection, hence onto),
   each cell of the block maps to `[P j, P j + ν j)`, injectivity makes these disjoint, and a cell
   outside the block has its image entirely outside `[P i₀, P i₀ + L)` (`P j + ν j ≤ P i₀` or
   `P i₀ + L ≤ P j`, by `Finset`-free interval reasoning on `h '' block = block`).
   Together with `listImageLeft_lt` this yields the `Icc a b` form of `R` — the last input of
   `listImageLeft_sub_of_Icc` — after taking `a := ρ` of the smallest and `b := ρ` of the largest
   `ρ`-value on `R` (`Finset.exists_min_image` on the finite `R`, using convexity to show that every
   `ρ`-value between them occurs in `R`).
2. **The `funext` against `mkIET1_apply`**: for `x ∈ [0,1)`, let `k` be the index of its rescaled
   cell (`exists_cell_of_strictMono` on the rescaled list `k ↦ (S (i₀+k) - u)/(v-u)`); then
   * `mkIET1 ν_b ρ_b x = x + (imageLeft ρ_b ν_b k - leftEnd ν_b k)` by `mkIET1_apply`, and
   * the rescaled `h` is `x + (P (i₀+k) - S (i₀+k))/(v-u)` by `IsCompPresentation.cell`;
   * `leftEnd ν_b k = (listLeftEnd S (i₀+k) - listLeftEnd S i₀)/L` by `listLeftEnd_sub`, and
   * `imageLeft ρ_b ν_b k = (P (i₀+k) - P i₀)/L` by `listImageLeft_sub_of_Icc` (with `ρ_b k` the
     `ρ`-value shift by `a`), and `P i₀ - listLeftEnd S i₀ = (u - u) = 0` since `S i₀ = u`;
   so the two displacements agree, and `funext` closes.
3. Then `irreduciblePerm_of_no_invariant_cut` at the block (Lemma 3.2 gives `IsIrreducibleOn`), the
   a.e. transfer of Masur–Veech / Veech / Diophantine (`compLen_absolutelyContinuous` +
   `ae_of_ae_compLen`), `irreducible_case`, and the word transport `evalWord_conj_apply` — whose
   `of`/`inv_of` cases at `genY` remain the one open proof obligation of that lemma (`Gen = Fin 2`).

## A shorter route to the block presentation: define `ρ_b` by rank (this session)

No new declaration this session; the point of this entry is that the remaining block-presentation
work is **smaller than the plan recorded above**, and should be redone along these lines.

### The simplification

The plan above defines `ρ_b` as `ρ` restricted to the block, which forces two hard jobs: the
consecutiveness of the block's `ρ`-values and `listImageLeft_sub_of_Icc`.  Both can be **skipped** by
defining `ρ_b` from the geometry instead:

```
ρ_b := the rank of P (i₀ + k) among the values {P (i₀ + m) : m : Fin (i₁ - i₀)}
```

(`P j := listImageLeft ρ S j` is the image start of cell `j`; `ρ_b` is built with
`Finset.orderIsoOfFin` exactly as in `exists_rank_perm`/`IsCutSet.cellPerm`, or obtained from
`exists_rank_perm` applied to the family `k ↦ listImageLeft ρ S (i₀+k)` — whose non-collision is
just the injectivity of the image starts on distinct cells.)

Then the identity needed for the `funext`,

`imageLeft ρ_b ν_b k = (P (i₀ + k) - P i₀)/L`,

is **`sum_len_eq_of_tiling`** (already proved) applied to the block's own cells in the original
coordinates: the intervals `[P j, P j + ν j)` for `j ∈ R` tile `[P i₀, P i₀ + L)` — the cover and the
disjointness being the geometric input (the block is invariant, so `h '' block = block`, injectivity
makes the images of the cells disjoint, and the images of the cells of `R` cover the block's image).
No consecutiveness, no `listImageLeft_sub_of_Icc`, and no comparison with `ρ` at all.

### Consequence for irreducibility

With `ρ_b` defined by rank, `IsIrreduciblePerm ρ_b` no longer comes from `ρ` but from the *same*
`irreduciblePerm_of_no_invariant_cut`, applied in the **rescaled** coordinates: the rescaled exchange
is `mkIET1 ν_b ρ_b` (the `funext`), and Lemma 3.2's `IsIrreducibleOn`, transported through the
rescaling, says precisely that `mkIET1 ν_b ρ_b` has no invariant initial interval.  So the two
remaining geometric inputs are:

1. `h '' block = block` and the resulting tiling of the block's image by the images of the cells of
   `R` (for `sum_len_eq_of_tiling`);
2. the transport of `IsIrreducibleOn` through the rescaling (a `c` inside `[u,v)` corresponds to
   `c' = (c-u)/(v-u)` inside `[0,1)`, and invariance of `[0,c')` for `mkIET1 ν_b ρ_b` is invariance
   of `[u,c)` for `h`).

### Recommendation for the next session

Do **not** continue along `listImageLeft_sub_of_Icc`; the three lemmas proved for it
(`listLeftEnd_sub`, `listImageLeft_sub_of_Icc`, `listImageLeft_lt`, `rho_convex_of_image_Ico`) are
correct and are kept as API, but `listLeftEnd_sub` is the only one the rank-based route needs.  Order
of work: (i) `h '' block = block` + the tiling facts; (ii) `ρ_b` by rank and the `imageLeft` identity
via `sum_len_eq_of_tiling`; (iii) the `funext` against `mkIET1_apply` (using `listLeftEnd_sub` and
`IsCompPresentation.cell`); (iv) `irreduciblePerm_of_no_invariant_cut` in rescaled coordinates;
(v) the a.e. transfer and `irreducible_case`; (vi) `evalWord_conj_apply`, whose `of`/`inv_of` cases at
`genY` are still open.

I did not start subagents: the remaining work is a single tightly coupled chain of dependent
`Finset`/`Fin` lemmas in one module, so parallel workers would collide on the same file and the
verification cost of their output would exceed writing it here.  I also did not attempt further
proofs this session, having run out of working context.

## HANDOFF — Block presentation: precise remaining statements

**Everything in this handoff was carried out** (the splitting lemmas, `pairSplitting_mem_markedList`,
the word transport, and finally Lemma 3.4).  Two of the helper lemmas prescribed below,
`mark_eq_markedList` and `listLeftEnd_sub`, have since been deleted as unused — see §"Deleted
declarations (reconciliation)" — so the names in this section are not all in the tree.

No declaration this session; build unchanged at `sorry` 1 (Lemma 3.4) plus the two frozen
`Challenge` sorries.  This section records **exactly** what has to be proved after the three
splitting lemmas, in the form to use as Lean statements.  Nothing here is a substitute for the Lean
code; every name matches the library.

### 1. The `g`-side: pair-splitting points are marked points

**Not true:** "every cut of `g` is a marked point" (counterexample: `σ j = σ (j-1)+1` makes `g`
continuous at `leftEnd μ j`, which can then lie strictly inside the image of a marked cell without
contradicting `g_transl`).  **True:**

```lean
theorem pairSplitting_mem_markedList {d e n} [NeZero d] [NeZero e]
    {D : IETDatum d} {E : IETDatum e} {s : Fin (n+1) → ℝ}
    (hD : ∀ k : Fin (d+1), ∃ i : Fin (n+1), s i = D.mark k)
    (hE : ∀ j : Fin (e+1), ∃ i : Fin (n+1), s i = D.toIET⁻¹ (E.mark j))
    {x : ℝ} (hx : IsPairSplitting D E x) : ∃ i : Fin (n+1), s i = x
```

`hD` is `mark_eq_markedList` (proved: the `f`-side), `hE` is the `hpre` field of
`exists_markedList` (`s (inr j) = f⁻¹ (leftEnd μ (j+1))`).  Proof: the `f`-side disjunct is `hD k`,
the `g`-side disjunct is `hE j` and `E.InFixedCell D j` makes `D` fix the point
(`mark_fixed_of_inFixedCell`: `D.toFun (E.mark j) = E.mark j` — already proved, hence `D⁻¹` of it is
itself, so `s i = D⁻¹ (E.mark j) = E.mark j = x` by injectivity).

**Consequence:** `GoodRegion` must record `hE` (the strong `f`-preimage form); `IsCompPresentation`
records only `g_transl` (refinement of the `f`-preimage partition), which is too weak.

### 2. The two `Finset` splittings (proved)

```lean
theorem mark_eq_markedList (P : IsCompPresentation lam π mu σ hl hm n s ρ)
    (T : IsCompType lam π hl mu s a B) (k : Fin (d+1)) :
    s (a k) = ∑ j ∈ filter (fun j => j.val < k.val), (lam j : ℝ)

theorem listLeftEnd_sub {s : Fin (n+1) → ℝ} {i₀ i₁ : Fin n} (h : i₀ ≤ i₁) :
    listLeftEnd s i₁ - listLeftEnd s i₀
      = ∑ j ∈ filter (fun j => i₀ ≤ j ∧ j < i₁), (s j.succ - s j.castSucc)

theorem listImageLeft_sub_of_Icc {ρ} {R} {a b} (hR : ∀ j, j ∈ R ↔ (a ≤ ρ j ∧ ρ j ≤ b))
    {S} {i₀ i₁} (h₀ : ρ i₀ = a) (h₁ : i₁ ∈ R) :
    listImageLeft ρ S i₁ - listImageLeft ρ S i₀
      = ∑ j ∈ R.filter (fun j => ρ j < ρ i₁), (S j.succ - S j.castSucc)
```

`listImageLeft_sub_of_Icc` is *the provable form* of B2: the block's `ρ`-values form an interval
`[a,b]` (a `ρ`-invariant block plus consecutiveness).  That interval is *geometric*: the image of the
block is one interval of the image partition.  Proving it is the geometric half — see §4.

### 3. The `funext` against `mkIET1_apply`

For `i₀ i₁` the marked indices of `u = s i₀.castSucc` and `v = s i₁.castSucc` (by §1), let
`R := {j : i₀ ≤ j ∧ j < i₁}` be the run, `ν j := s j.succ - s j.castSucc`, `ν_b k := ν (i₀+k)`,
and `ρ_b k := ρ (i₀+k) - a` (where `a = ρ i₀`).  Then

```lean
theorem rescaledBlock_eq_mkIET1 ... (q) (hq) (x) (hx : x ∈ Ico (0 : ℝ) 1) :
    rescaleFun u v (g ∘ f) x = mkIET1 ν_b ρ_b hx' y  -- where y := rescaleMapInv u v x
```

is `funext` + the `x`-cell of the rescaled list.  For the `k`-th cell of the block the left
comparison is `leftEnd ν_b k = listLeftEnd S (i₀+k) - listLeftEnd S i₀` (`listLeftEnd_sub` with `h`),
the right one is `imageLeft ρ_b ν_b k = listImageLeft ρ S (i₀+k) - listImageLeft ρ S i₀`
(`listImageLeft_sub_of_Icc` with `hR` = consecutiveness).  `IsCompPresentation.cell` supplies
`h(x) = x + (listImageLeft ρ S j - listLeftEnd S j)` for `j := i₀+k`, and `mkIET1_apply` supplies
`mkIET1 ν_b ρ_b (x) = x + (imageLeft ρ_b ν_b k - leftEnd ν_b k)`.  The two agree after the `funext`
and a `ring`.

### 4. Irreducibility of the block permutation

`IsIrreduciblePerm ρ_b` from `irreduciblePerm_of_no_invariant_cut` at the block, with
"no invariant initial interval" coming from Lemma 3.2 transported through the rescaling:
`c` inside `(u,v)` corresponds to `c' = rescaleMap u v c` inside `(0,1)`, and invariance of
`[0,c')` for `mkIET1 ν_b ρ_b` is invariance of `[u,c)` for `h = g∘f` on the block, which is
`block_irreducible_on_good`.  `IsCompPresentation` + the tilings give `h '' block = block`.

### Order of work for Lemma 3.4

1. Land §1 (the `g`-side, 10 lines) and §2 (the two splittings, 80 lines together — done).
2. Prove the geometric consecutiveness: `R = {j : a ≤ ρ j ≤ b}` from `h '' block = block` and the
   invariance of the block (the image of a block cell is inside the block's image, so the
   `ρ`-values on `R` are those `k` with `P i₀ ≤ imageLeft ρ S (ρ⁻¹ k) < P i₁` — use the strict
   monotonicity of `P` in `ρ`, i.e. `listImageLeft_lt` on `k₁ < k₂`).
3. `funext`: `rescaleFun u v ⇑(g ∘ f) = mkIET1 ν_b ρ_b` with the `Finset` splittings.
4. `IsIrreduciblePerm ρ_b`, the a.e. transfer of Masur–Veech / Veech / Diophantine along
   `GoodRegion.compLen_absolutelyContinuous` + `ae_of_ae_compLen`, `irreducible_case`, and the word
   transport `evalWord_conj_apply` (whose `of`/`inv_of` cases at `genY` are the one remaining open
   proof obligation — `Gen = Fin 2`, so `Fin.eq_zero_or_eq_one` should settle them).

## This session: the singularity shape, the block endpoints, and the word transport

Build green, `sorryAx` 3 (the two frozen `Challenge` ones and `exists_word_trivial_on_block`).
One new module: `Section3Block.lean` (imports `Section3LengthMap` + `Section3BlockWord`), added to
`Build.sh` in **both** places (and `Section3BlockWord.log` was missing from the `cat` list of the
sorry counter — now added).

### Landed

* `Section3BlockWord.evalWord_conj_apply`: if `φ` conjugates the two generators *and their inverses*
  (`F (φ y) = φ (F' y)`, `F⁻¹ (φ y) = φ (F'⁻¹ y)`, same for `G`), then
  `evalWord w F G (φ y) = φ (evalWord w F' G' y)` for `y ∈ [0,1)`.  Proof: `FreeGroup.induction_on`
  with the four cases, `fin_cases` on `Gen = Fin 2` for `of`/`inv_of` (the earlier session's
  `by_cases hx : x = 0` route was the problem; `fin_cases` closes both cases immediately), and the
  `mul` case needs `(evalWord v F' G').isIET.mapsTo hy`.  No hypothesis on `φ` itself is needed.
  **This unblocks the "word transport" item of the handoff.**
* `SingularityShape` (in `Section3Region`, declared *before* `exists_compPresentation_on_ball` — a
  structure used in a statement must precede it): the explicit shape of the marked list, with
  `cellIdx : Fin (e-1) → Fin d`, `posF : Fin (d-1) → Fin (n+1)`, `posG : Fin (e-1) → Fin (n+1)`,
  injectivity/disjointness/endpoint-avoidance, and
  * `posF_spec : s (posF i) q = cutAffine ⟨i+1⟩ q`
  * `posG_spec : s (posG j) q = preimageCutAffine π ⟨j+1⟩ (cellIdx j) q`
  * `posG_pre : s (posG j) q = (mkIET1 (simplexMap d q.1) π hl)⁻¹ (leftEnd (simplexMap e q.2) ⟨j+1⟩)`
  (the evaluated form, which is what the pair-splitting argument consumes).
  It is built inside `exists_compPresentation_on_ball` from `τ` and `k` (the `withEnds_mid` route:
  `s = withEnds hn A`, `A m = singAffine π k (τ m)`, so `posF i := τ.symm (inl i) + 1` and
  `posG j := τ.symm (inr j) + 1`), and `GoodRegion` now has a field `shape`.  The conclusion of
  `exists_compPresentation_on_ball` gained an `∃ _shape : SingularityShape n π s (ball q₀ ε)` — it
  must be an `∃` and not a `∧` because the structure has data, hence lives in `Type`.
* `Section3Block`: the consequences.
  * `GoodRegion.n_eq : G.n = d + e - 1` (from `IsCompPresentation.card_eq`);
  * `GoodRegion.surj`: every index of the list is `0`, `Fin.last n`, some `posF i` or some
    `posG j` — a `Finset` count (`d - 1` cuts + `e - 1` preimages + `0` + `1` = `n + 1`);
  * `GoodRegion.s_zero`, `s_last`, `s_mono` (from `pres`);
  * `IETDatum.mark_eq_leftEnd : D.mark k = leftEnd D.lam ⟨k.val, _⟩` for `k.val < n` (avoids a
    `Fin`-dependent rewrite that `rw` cannot do);
  * `mkIET1_inv_zero : (mkIET1 lam π hl)⁻¹ 0 = leftEnd lam (π.symm 0)` — **note `f 0 ≠ 0` in
    general** (the exchange sends `0` to the left end of the image of cell `0`); this is why
    `f⁻¹ 0` is a *cut of `f`*, hence on the list;
  * `mkIET1_inv_one`, `GoodRegion.mem_cutF` (cuts of `f` are on the list, from `IsCompType.cut`),
    `mem_cutList` (the `posG` entries are the `f`-preimages of the cuts of `g`),
    `mem_markD` (the marked points of `D` are on the list);
  * **`GoodRegion.mem_pairSplitting`**: with `D.v = q.1`, `D.π = π`, `E.v = q.2`, `E.π = σ`, every
    pair-splitting point is `G.s i q`.  (The proof first replaces `D`, `E` by `IETDatum.ofMem` — use
    `obtain ⟨a, b, c⟩ := D; obtain rfl : a = π := hπD; …; obtain rfl : c := Subsingleton.elim _ _;
    rfl`, which is the only way found to get past the `Fin`-dependent rewriting.)
  * **`GoodRegion.block_endpoints`**: the endpoints of a block are `G.s i₀ q`, `G.s i₁ q` with
    `i₀ < i₁`.  **This is item 2 of the previous handoff, done.**
  All axiom-clean and added to `Check.lean`.

### The remaining work on Lemma 3.4, and one mathematical point to settle

The block now has a *run of cell indices* `[i₀, i₁)`, so the block datum is

```
m := i₁ - i₀,   ν_b k := G.s ⟨i₀+k+1⟩ q - G.s ⟨i₀+k⟩ q,   L := G.s i₁ q - G.s i₀ q > 0
```

and the block exchange `h := g ∘ f` restricted to `[u, v)` is `mkIET1 (ν_b / L) ρ_b` where `ρ_b` is
the rank of the image starts (this is `IsCutSet.eq_mkIETFun` + `IsCutSet.sum_cellLen_image` applied
to the rescaled map, or the direct `funext` against `mkIET1_apply`; `sum_len_eq_of_tiling` is the
partial-sum identity to use).

**The point that needs a decision.**  The a.e. transfer of Masur–Veech, Veech and Diophantine to the
block (item 6 of the previous handoff) is **not** a straightforward use of
`GoodRegion.compLen_absolutelyContinuous`: that gives absolute continuity of the map
`q ↦ ν(q)` (the *full* length vector, injective affine, matching dimensions), whereas the block
exchange is `mkIET1 (ν_b/L) ρ_b`, whose length vector lives in the `(r-1)`-dimensional simplex with
`r := i₁ - i₀` — a *submersion*, not an injection.  Two facts are needed:

1. **Maximal rank.**  The map `q ↦ (ν_b(q)/L(q))` has rank `r - 1`.  This is true and has a clean
   proof: the interior singularity functions `s_1, …, s_{n-1}` (there are `n - 1 = d + e - 2 = m` of
   them) have linearly independent linear parts, because in the free coordinates `(q.1, q.2)` the
   `q.2`-part of a cut of `f` is `0` and the `q.2`-part of the `j`-th preimage is the prefix sum
   `(1, …, 1, 0, …)`, a triangular system; then with `v_j` the dual basis (`ℓ_i(v_j) = δ_ij`) one has
   `dν_k(v_j) = δ_kj - δ_{k-1,j}` and `dL(v_j) = δ_{i₁,j} - δ_{i₀,j}`, so the matrix of `d(ν_b/L)`
   in the basis `(v_j)_{j=i₀}^{i₁-2}` is lower triangular with non-zero diagonal — rank `r - 1`.
   (The `q.1`-parts then give the rest.)  **This is the ingredient the paper uses without comment**
   ("a derivative of maximal rank"), and it must be formalised: it needs the coefficient forms of the
   singularity functions, i.e. `posF_spec`/`posG_spec` unfolded through `cutAffine_apply`,
   `preimageCutAffine_apply`, `cutAffineRight_apply`, `imageLeftAffine_eq`, `cutAffine_eq_leftEnd`.
   *The Diophantine transfer does not need it*: there one only needs that the block lengths are
   integer affine functions of `q`, which follows from the same unfoldings.
2. **Pushforward of a submersion.**  For a Borel `Z ⊆ ℝ^{r-1}` of measure zero,
   `(volume.restrict G.O) ((ν_b/L) ⁻¹' Z) = 0`.  A workable route, using only what Mathlib has:
   write `(ν_b/L) = ρ ∘ Y` with `Y(q) = (ν_{i₀}(q), …, ν_{i₁-1}(q)) ∈ ℝ^r` affine and `ρ` the
   normalisation `y ↦ (y_i/∑y)`; then `ρ⁻¹Z` is the cone over `Z` inside the positive orthant, which
   is null in `ℝ^r` because it is the image of the null set `Z × ℝ` under the differentiable map
   `(z, s) ↦ s • (z, 1 - ∑z)` — Mathlib's
   `MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`
   (`Mathlib/MeasureTheory/Function/Jacobian.lean`) is exactly "a differentiable map sends null sets
   to null sets".  Then `Y ⁻¹ (ρ⁻¹ Z)` is null by the linear-algebra case: a surjective linear map's
   preimage of a null set is null (take a linear section, split `E ≅ F × ker`, and use
   `Measure.prod_prod` for `Z ×ˢ univ`).  (`Measure.map_linearMap_addHaar_eq_smul_addHaar` only
   covers *injective* endomorphisms, so the section decomposition has to be written out.)

After that, the rest of Lemma 3.4 is bookkeeping: the a.e. transfer along
`ae_of_ae_compLen`-style `ae_of_ae_of_absolutelyContinuous`, `irreducible_case` for
`(mkIET1 ν_b ρ_b, mkIET1 μ_b σ_b)`, `IsIrreduciblePerm ρ_b` from
`irreduciblePerm_of_no_invariant_cut` with the hypothesis transported from
`block_irreducible_on_good`, and `evalWord_conj_apply` (now proved) to come back to the block.

### Structure to keep

* `GoodRegion` now has `shape`; anything constructing it must supply one (`exists_goodRegion` does).
* The sorry counter in `Build.sh` needs a module added in two places; the previous omission of
  `Section3BlockWord` made it undercount.
* `IETDatum.toIET` is a plain `def`: `rw [IETDatum.toIET]` fails, use `show` or the `rfl` equation
  `D.toIET = mkIET1 D.lam D.π D.mem_simplex`.
* `Subsingleton.elim` is the way to identify the proof fields of `IETDatum`/`IET` after rewriting.

## The rescaling transfer, reformulated (this session, after the user's reformulation)

The user replaced my "the block lengths of `g ∘ f` have maximal rank as functions of `(λ, μ)`" by a
strictly better statement, which has no `d`/`e` in it: **rescaling a sub-interval's length vector to
total mass `1` does not create measure from nothing.** They also pointed out that, together with
Lemma 3.1, this is all that is needed for Masur–Veech and Veech. That is right, and it removes the
step I had flagged as the paper's gap: in the simplex coordinates the maximal rank is a projection
followed by a normalisation, so no singularity functions and no dual basis are involved.

New module `Section3Transport` (added to `Build.sh` in both places, imported by `Section3`):

```lean
theorem volume_normalize_preimage_null {r : ℕ} {Z : Set (Fin r → ℝ)} (hZ : volume Z = 0) :
    volume {t : Fin (r + 1) → ℝ |
      (∀ i, 0 < t i) ∧ (fun i : Fin r => t i.castSucc / ∑ j, t j) ∈ Z} = 0
```

**Proved and axiom-clean.**  Proof: take a measurable null superset `Z'` of `Z`; the parameter set
`A := {t | (fun i => t i.castSucc) ∈ Z'}` is null because `piFinSuccAbove` (at `Fin.last r`) is
measure-preserving and identifies `A` with `univ ×ˢ Z'`, so `Measure.prod_prod` gives `⊤ * 0 = 0`;
then the cone is the image of `A` under the polynomial map
`G x j = x (last r) * if j.val = r then 1 - ∑ i, x i.castSucc else x j`, which is `Differentiable`
(per-coordinate `fun_prop` after `by_cases`), so
`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` finishes.  The point `t` is recovered
from `x := Fin.snoc (fun i => t i.castSucc / S) S` with `S = ∑ t` (this is why the statement is on
the *positive* orthant: `S > 0`, so there is no `∑ = 0` case and no need for "a hyperplane is null",
which is not a one-liner in this Mathlib).

### What remains of the plan the user approved

**(1b) `volume_rescaleSub_preimage_null`.**  Statement to prove, in the free coordinates of the
simplex:

```lean
theorem absolutelyContinuous_map_rescaleSub {n r : ℕ} (hn : 0 < n) {k : ℕ} (hk : k + r ≤ n) :
    (volume.restrict (simplexRegion n)).map (rescaleSub (k := k) (r := r)) ≪
      volume.restrict (simplexRegion r)
```

with `rescaleSub x i = cellLen x (k + i) / ∑ j ∈ range r, cellLen x (k + j)` and
`cellLen x m = if m < n - 1 then x ⟨m, _⟩ else 1 - ∑ j, x j`.  Then the `simplexVolume` form follows
by unfolding `simplexVolume` twice and pushing forward along `simplexMap r`
(`Measure.AbsolutelyContinuous.map`); and with `GoodRegion.compLen_absolutelyContinuous`
(`ae_of_ae_compLen`) the chain is complete.

Proof recipe (worked out, not yet written): use the substitution
`Φ x = ((cellLen x (k + i))_{i < r}, (x j for the remaining free coordinates))`, an **affine
injection with matching dimensions** `(r) + (n - 1 - r) = n - 1`, so `absolutelyContinuous_map_affine`
gives `(volume.restrict O).map Φ ≪ volume`; then `rescaleSub = ρ ∘ Φ` with `ρ` the normalisation, and
`volume_normalize_preimage_null` gives `(volume.restrict {t | 0 < t}).map ρ ≪ volume`; conclude with
`Measure.AbsolutelyContinuous.map`/`.trans`.  **Two cases for the "remaining coordinates"**, and this
is the one real trap:
* if `k + r ≤ n - 1` (the block does not contain the last cell), the block lengths are the free
  coordinates `x k, …, x (k+r-1)` and the remaining ones are `{0..n-2} \ {k..k+r-2}`;
* if `k + r = n` (the block contains the last cell), the block lengths are `x k, …, x (n-2)` plus
  `1 - ∑ x`, which determine the *sum* `∑_{i<k} x i` but not the individual `x i` for `i < k`; the
  remaining coordinates are then `x 0, …, x (k-2)` (that is `k - 1 = n - 1 - r` of them, and `x (k-1)`
  is recovered from the sum).  Getting this count right is why the first case cannot simply be
  re-used.

**(2) The Diophantine transfer.**  Not covered by the rescaling statement, since `irreducible_case`
needs `IsDiophantine ν_b μ_b` and `μ_b` (the `g`-pieces of the block) is not a function of `ν_b`.
No rank is needed here, only integrality:

```lean
theorem IsDiophantine.of_int_combination {d e r n : ℕ} {lam : Fin d → ℝ≥0} {mu : Fin e → ℝ≥0}
    (hdio : IsDiophantine lam mu) (w : Fin r → ℝ) (w' : Fin n → ℝ)
    (A B A' B' : ...) (hw : ∀ i, w i = ∑ k, (A i k : ℝ) * lam k + ∑ l, (B i l : ℝ) * mu l)
    (hw' : ...) (hpos : ∀ i, 0 < w i) (hpos' : ∀ j, 0 < w' j) (hL : ∑ i, w i = ∑ j, w' j)
    (hL1 : ∑ i, w i ≤ 1) :
    IsDiophantine (fun i => ⟨w i / ∑ k, w k, _⟩) (fun j => ⟨w' j / ∑ k, w' k, _⟩)
```
(multiply a relation by the total length `≤ 1`; the coefficients grow by `(r + n) * M`).
Two routes to the integrality of the block pair, both `d`/`e`-free in spirit:
* from the shape: each `s k` is an integer affine function of the free parameters — unfold
  `posF_spec`/`posG_spec` through `cutAffine_apply`, `preimageCutAffine_apply`,
  `cutAffineRight_apply`, `imageLeftAffine_eq`, `cutAffine_eq_leftEnd`; then `ν_b` is a difference of
  two `s`'s and `μ_b` a difference of `g`-cut positions and block endpoints, and a.e. `q` is
  Diophantine for all integer affine forms (from `ae_isDiophantine` for `(λ, μ)` plus the fact that an
  integer affine form of `q` is an integer combination of `(λ, μ)`);
* or purely in `ν`: the block endpoints are prefix sums of `ν` (`u = s i₀ = ∑_{j<i₀} ν j`), the
  `g`-cuts inside the block are `f`-images of marked points whose positions are `leftEnd μ m`, and
  `μ_j` is a `0/1` combination of `ν` by `mu_eq_sum`; then a.e. `ν` is Diophantine (a.e. statement on
  `Δ_N`), and the pair inherits it.
The first route reuses `SingularityShape`, which is already in place; I would take it.

**(3) `mkIET1_rescale_subinterval`.**  The restriction of an exchange to a sub-interval it preserves:

```lean
theorem mkIET1_rescale_subinterval {n : ℕ} [NeZero n] (lam : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin n)) (hl : (∑ i, lam i) = 1) {k l : ℕ} (hkl : k < l) (hln : l ≤ n)
    (hstab : ∀ i : Fin n, (i.val < k ↔ (π i).val < k) ∧ (i.val < l ↔ (π i).val < l)) :
    ∃ ρ : Equiv.Perm (Fin (l - k)), <on [leftEnd lam k, leftEnd lam l) the exchange is the rescaled
      one with lengths (lam (k+i))/L and permutation ρ>
```
Ingredients already available: `rescaleMap`/`rescaleFun` and `rescaleFun_comp` (`Section3BlockWord`),
`IsCutSet.eq_mkIETFun` (the cleanest route: the rescaled map has the rescaled cuts as a cut set),
`mkIET1_apply`, `listImageLeft`/`sum_len_eq_of_tiling` for identifying `imageLeft` with the rescaled
image starts.  In the application `hstab` is *derived*, not assumed: the block `[s i₀, s i₁)` is
invariant, so `ρ` preserves `{i₀..i₁-1}` (`listImageLeft_lt` + the tiling), and the two sides because
the endpoints are pair-splitting (`IsPairSplitting.iff_mem`); that the run `[i₀, i₁)` is *consecutive*
comes from `exists_pairSplitting_of_invariant` (the core of Lemma 3.2) plus minimality of the block.
`GoodRegion.block_endpoints` (previous session) supplies `i₀ < i₁`.

### Status of the rescaling transfer at the end of this session

In `Section3Transport`:

* `cellLen x m` — the `m`-th cell length of the simplex point with free coordinates `x`
  (`x m` for `m < n - 1`, `1 - ∑ x` at the last cell);
* `blockLen k r x : Fin r → ℝ` — the cell lengths of the block `k, …, k + r - 1`;
* `rescaleSub k r x : Fin (r - 1) → ℝ` — the free coordinates of the **rescaled** block vector,
  i.e. the map `F` of Lemma 3.4.  These are `def`s with formulas, not existentials, so the
  permutation and the length vector of the block can be fed to
  `irreduciblePerm_of_no_invariant_cut` and to the Diophantine lemma.
* `volume_normalize_preimage_null` — **proved**, axiom-clean.
* `absolutelyContinuous_map_rescaleSub` — **stated, `sorry`** (this is the fourth `sorry`; the count
  in `Build.sh` is now 4: the two frozen `Challenge` ones, `exists_word_trivial_on_block`, and this).
  Statement:
  `(volume.restrict (simplexRegion n)).map (rescaleSub k r) ≪ volume.restrict (simplexRegion r)`
  for `k + r ≤ n`, `n > 0`.
  Proof to write: the affine injection
  `Φ x = (blockLen k r x, the remaining free coordinates)` has matching dimensions
  (`r + (n - 1 - r) = n - 1`), so `absolutelyContinuous_map_affine` gives
  `(volume.restrict O).map Φ ≪ volume`; then `rescaleSub = ρ ∘ Φ` and
  `volume_normalize_preimage_null` (applied with its `r` set to `r - 1`, so that the source is
  `Fin r` and the target `Fin (r - 1)`) gives the normalisation step; finish with
  `Measure.AbsolutelyContinuous.map` and `.trans`.  The "remaining coordinates" are
  `{0..n-2} \ {k..k+r-2}` when the block does not contain the last cell, and `{0..k-2}` when it does
  (the block lengths then determine only `∑_{i<k} x i`, and `x (k-1)` follows from it).  `Φ`'s linear
  part is injective in both cases; the containment `Φ (simplexRegion n) ⊆ {t | 0 < t}` in the first
  component is positivity of the block lengths on the open simplex.

**Convention fixed by the user for the next file:** `mkIET1_rescale_subinterval` must *define* the
block permutation rather than existentially quantify it, since its irreducibility is needed:
`ρ i = π (i + k) - k` on the block (with the inverse `(ρ i) + k`), i.e. the restriction of `π` to the
invariant interval `[k, l)`, shifted; then `IsIrreduciblePerm ρ` can be transported from the
geometric irreducibility of the block (`block_irreducible_on_good`).

### Proof script for `absolutelyContinuous_map_rescaleSub` (to execute; nothing here is proved yet)

Notation: `x : Fin (n-1) → ℝ` are the free coordinates of `simplexRegion n`, `t := blockLen k r x`.
Write `rem x : Fin (n-1-r) → ℝ` for the "remaining coordinates" and `Φ := fun x => (t x, rem x)`.

**Case 1, `hk1 : k + r ≤ n - 1`** (block does not contain the last cell):
`rem x j := x ⟨if j.val < k then j.val else j.val + r, _⟩`, i.e. the free coordinates outside the
block.  `r + (n-1-r) = n-1` ✓.
Inverse (on the image): from `(t, w)` set `x ⟨k + i, _⟩ := t i` for `i < r`, and read the other
coordinates off `w`; this shows `Function.Injective Φ.linear`.
**Case 2, `hk2 : k + r = n`** (block contains the last cell):
`rem x j := x ⟨j.val, _⟩` for `j : Fin (n-1-r) = Fin (k-1)`, i.e. `x 0, …, x (k-2)`.
Recovery: `t` gives `x ⟨k+i, _⟩ = t i` for `i < r-1` and `∑_{i<k} x i = 1 - ∑_{i<r-1} t i - t (r-1)`;
with `rem` this gives `x (k-1) = ∑_{i<k} x i - ∑_{i<k-1} x i`.  Injectivity follows.
Both cases: build `Φ` as an `AffineMap` (`AffineMap.pi` of `x ↦ x ⟨·,_⟩` and, in case 2, of
`1 - ∑ x` if one prefers to put the sum in the block component — but with the recovery above the sum
is *not* needed inside `Φ`, since `rem` together with `t` already determines `x`).

Then:
* `hinj : Function.Injective Φ.linear` and `hdim : finrank ℝ (Fin (n-1) → ℝ)
  = finrank ℝ ((Fin r → ℝ) × (Fin (n-1-r) → ℝ))` (both `n-1`), so
  `hacΦ : (volume.restrict (simplexRegion n)).map Φ ≪ volume` by `absolutelyContinuous_map_affine`;
* `hpos : ∀ x ∈ simplexRegion n, ∀ i, 0 < blockLen k r x i` (positivity of the cell lengths of the
  region: `pos_simplexMap` for the free cells, `1 - ∑ x > 0` from `x ∈ simplexRegion n` for the last)
  gives the containment `Φ (simplexRegion n) ⊆ {u | ∀ i, 0 < u.1 i}`;
* `A := {u : (Fin r → ℝ) × (Fin (n-1-r) → ℝ) | (∀ i, 0 < u.1 i) ∧
  (fun i : Fin (r-1) => u.1 ⟨i.val, _⟩ / ∑ j, u.1 j) ∈ Z₀}`, null in `volume` by
  `volume_normalize_preimage_null` (applied with `r := r-1`: source `Fin ((r-1)+1) = Fin r`, target
  `Fin (r-1)`; use `Nat.sub_one_add_one` with `1 ≤ r`) plus `Measure.prod_prod` for the second factor;
* conclude: `(volume.restrict (simplexRegion n)).map (rescaleSub k r) ≪ volume.restrict (simplexRegion r)`
  by `Measure.AbsolutelyContinuous` transitivity: the map factors as `ρ ∘ Φ`, the pushforward of
  `Φ` is ac, and `ρ` pulls null sets back to null sets.
The `≪` form is consumed through `ae_of_ae_of_absolutelyContinuous`.

Remarks that cost time if forgotten: with `1 ≤ r` one has `r - 1 + 1 = r`
(`Nat.sub_one_add_one`), which is what makes `Fin (r-1)`'s `castSucc` land in `Fin r` and lets
`volume_normalize_preimage_null` be applied; the case `r = 0` is vacuous (the target is a point) and
should be split off first, and `n = 0` is excluded by `0 < n`.

## WORKER BRIEF — prove `absolutelyContinuous_map_rescaleSub` (do this first — **DONE**, see "`absolutelyContinuous_map_rescaleSub` is **PROVED**" two entries below)

```text
Goal:   replace the `sorry` in `IETFree/Section3Transport.lean` by a proof.
Ownership: `IETFree/Section3Transport.lean` only (plus `Check.lean` if you add the
        declaration to the axiom report). Do not touch `Section3Region`,
        `Section3Block`, `Section3Reduction` or `Challenge`.
Frozen target (statement is AUTHOR-APPROVED, do not change it):
        theorem absolutelyContinuous_map_rescaleSub {n : ℕ} (hn : 0 < n) {k r : ℕ}
            (hk : k + r ≤ n) :
            (volume.restrict (simplexRegion n)).map (rescaleSub k r) ≪
              volume.restrict (simplexRegion r)
        with the definitions already in the file:
          cellLen x m      = if m < n - 1 then x ⟨m, _⟩ else 1 - ∑ j, x j
          blockLen k r x i = cellLen x (k + i)                       (i : Fin r)
          rescaleSub k r x i = blockLen k r x ⟨i.val, _⟩ / ∑ j, blockLen k r x j   (i : Fin (r-1))
Allowed inputs (all in the tree, all provable/available):
        `volume_normalize_preimage_null` (Section3Transport, PROVED),
        `absolutelyContinuous_map_affine` (Section3LengthMap, PROVED),
        `Measure.prod_prod`, `Measure.AbsolutelyContinuous.map/.trans/.restrict`,
        `ae_of_ae_of_absolutelyContinuous`, `exists_measurable_superset_of_null`,
        `pos_simplexMap`, `simplexMap_mem_simplex'`, and the definition of
        `simplexRegion n = {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}`.
Checks: `cd IET2 && ./Build.sh` (green, and the count must drop from 4 to 3);
        then `lean -o IETFree/Check.olean IETFree/Check.lean` and confirm
        `#print axioms absolutelyContinuous_map_rescaleSub` is
        `[propext, Classical.choice, Quot.sound]`. Lines ≤ 100 chars
        (the author compiles with `-Dlinter.mathlibStandardSet=true`).
Stop condition: the statement cannot be proved as written (then STOP and report,
        do not weaken it), or the four `sorry`s grow.
Hard rules: `Challenge.lean` is frozen; no new axioms; no hypothesis smuggling;
        keep `NOTES.md` updated with what was proved and any gotcha.
```

### Proof plan, with the parts that cost time

Split off `r = 0` first (the target `Fin (0 - 1) → ℝ` is a point and `simplexRegion 0` is a
subsingleton, so `≪` is automatic) and then assume `1 ≤ r`, which gives `r - 1 + 1 = r`
(`Nat.sub_one_add_one`) so that `Fin (r-1)`'s `castSucc` lands in `Fin r`.

Let `O := simplexRegion n`, and let `Φ : (Fin (n-1) → ℝ) → (Fin r → ℝ) × (Fin (n-1-r) → ℝ)` be

* **case 1, `k + r ≤ n - 1`** (block does not contain the last cell):
  `Φ x = (blockLen k r x, fun j : Fin (n-1-r) => x ⟨if j.val < k then j.val else j.val + r, _⟩)`.
  The second component enumerates the free coordinates outside `{k, …, k+r-1}`, increasingly, and
  `j.val + r ≤ n - 2` exactly because `j.val ≤ n-2-r`.
* **case 2, `k + r = n`** (block contains the last cell):
  `Φ x = (blockLen k r x, fun j : Fin (n-1-r) => x ⟨j.val, _⟩)`, i.e. `x 0, …, x (k-2)`
  (`n - 1 - r = k - 1` here). The block vector determines `x k, …, x (n-2)` and the **sum**
  `∑_{i<k} x i`, hence `x (k-1)`.

Build `Φ` as an `AffineMap` (`AffineMap.pi` of coordinate projections, and in case 2 the last
component of `blockLen` is the affine map `1 - ∑ x`), so that
`absolutelyContinuous_map_affine` applies — it needs `Function.Injective Φ.linear` and
`Module.finrank ℝ (Fin (n-1) → ℝ) = Module.finrank ℝ ((Fin r → ℝ) × (Fin (n-1-r) → ℝ))`; both
sides are `n - 1` (`Module.finrank_prod`, `Module.finrank_fin_fun`).

**Injectivity is cheapest via an explicit left inverse, not linearity**: prove
`∀ v, Ξ (Φ.linear v) = v` for a piecewise `Ξ` you write down, by `funext m` followed by `by_cases`
on `m ∈ {k, …, k+r-1}` (case 1) resp. `m < k - 1`, `m = k - 1`, `k ≤ m ≤ n - 2` (case 2); each branch
is a coordinate evaluation and closes with `omega`/`simp`. In case 2 the `m = k-1` branch uses
`Φ.linear v`'s last block component `-∑ v = 0` plus the other branches.

Then:
* `hacΦ : (volume.restrict O).map Φ ≪ volume` from `absolutelyContinuous_map_affine`
  (it wants a `Measure.IsAddHaarMeasure` instance on both spaces: for `Fin m → ℝ` and for the
  product of two such, `inferInstance` finds it — see `GoodRegion.compLen_absolutelyContinuous` for
  the pattern used in this project);
* `hpos : ∀ x ∈ O, ∀ i, 0 < blockLen k r x i` — positivity: free coordinates from `hyp.1`,
  the last cell from `∑ x < 1`;
* `hA : volume A = 0` for `A := {u : (Fin r → ℝ) × (Fin (n-1-r) → ℝ) | (∀ i, 0 < u.1 i) ∧
  (fun i : Fin (r-1) => u.1 i.castSucc / ∑ j, u.1 j) ∈ Z₀}`, by
  `volume_normalize_preimage_null` applied with its `r := r - 1` (giving source `Fin r`, target
  `Fin (r-1)`) plus `Measure.prod_prod` for the second factor (`⊤ * 0 = 0`); `Z₀` is a measurable
  null superset of `Z ∩ simplexRegion r`, from `exists_measurable_superset_of_null`;
* conclude: on `O`, `rescaleSub k r = ρ ∘ Φ` (a `funext` on `Fin (r-1)`, using
  `blockLen k r x i.castSucc = blockLen k r x ⟨i.val, _⟩` by `rfl`/`Fin.ext rfl`), so
  `(volume.restrict O).map (rescaleSub k r) = ((volume.restrict O).map Φ).map ρ ≪ volume`:
  `Measure.AbsolutelyContinuous.map` for `Φ`'s pushforward and the normalisation lemma in the
  `map`-form for `ρ`, then `.trans`. Finally `restrict` to `simplexRegion r`.

The user's own summary of the mathematical content is worth keeping in view: this is a general fact
about rescaling a sub-vector of a length vector to total mass `1`, and the only IET input is that the
length vector of `g ∘ f` is absolutely continuous (Lemma 3.1), which is already proved
(`GoodRegion.compLen_absolutelyContinuous`). The downstream chain is
`(volume.restrict G.O) --ν--> Δ_N --F--> Δ_r` with `F = rescaleSub`, both maps absolutely continuous.

## `absolutelyContinuous_map_rescaleSub` is **PROVED** (this session)

Build green, `declarations still depending on sorryAx: 3` (the two frozen `Challenge` statements and
Lemma 3.4's `exists_word_trivial_on_block`); `Tasks/Match.lean` ok.  `#print axioms
absolutelyContinuous_map_rescaleSub` is `[propext, Classical.choice, Quot.sound]`.  The statement is
unchanged (frozen form), and every new declaration added to `Section3Transport` is axiom-clean.

### The proof, in the order it runs

Let `O := simplexRegion n`.  Split off `r = 0` (the target is a point; `volume.restrict O` is a
nonzero measure on a subsingleton, `IsOpen.measure_pos` + `Set.eq_univ_of_forall`), then substitute
`r = m + 1` with `m := r - 1` (`Nat.sub_one_add_one`).  **This substitution is the trick that makes
the rest short**: `Fin (r - 1)` becomes *definitionally* `Fin m` and the first component of the split
below is `Fin (m + 1)`-indexed, so `volume_normalize_preimage_null` (source `Fin (m+1)`, target
`Fin m`) applies with no `Fin`-cast gymnastics at all.  All the `Fin (r-1)` vs `Fin r` pain that the
brief anticipated is avoided; do the same next time.

New API in `Section3Transport` (all proved, all before the target theorem):

```lean
cellLen_of_lt / cellLen_of_not_lt, blockLen_of_lt / blockLen_of_not_lt, blockLen_eq_of_le
sum_cellLen : (∑ i : Fin (m+1), cellLen (n := m+1) x i) = 1
splitMap (hk : k + r ≤ n - 1) : E →ᵃ[ℝ] ((Fin r → ℝ) × (Fin (n-1-r) → ℝ))   -- case 1
splitMap_apply, splitMap_injective (linear part, from injective_split)
lastAffine : E →ᵃ[ℝ] ℝ            -- x ↦ 1 - ∑ x,  with lastAffine_apply
splitMapLast : E →ᵃ[ℝ] ((Fin r → ℝ) × (Fin (n-1-r) → ℝ))                      -- case 2
splitMapLast_apply, splitMapLast_injective, splitMapLast_linear_injective
blockLen_pos, finrank_split, measurable_cellLen, measurable_rescaleSub
rescaleSub_mem_simplexRegion : x ∈ simplexRegion n → rescaleSub k (m+1) x ∈ simplexRegion (m+1)
```

* Case 1 (`k + r ≤ n - 1`): `Φ x = (blockLen k r x, x` outside the block`)`, injective by the
  existing `injective_split`; case 2 (`k + r = n`, `k ≥ 1`): `Φ x = (blockLen k r x, x 0, …, x (k-2))`
  — **new** injectivity lemma.  In both, `Φ.linear` is injective because `Φ x = Φ.linear x + Φ 0`,
  and the dimensions agree by `finrank_split`.
* The degenerate sub-case `k = 0 ∧ r = n` cannot use that split (`n - 1 - r = 0` makes the target
  dimension `n`, not `n-1`): there `blockLen 0 n x` is *all* the cell lengths, `∑ = 1` by
  `sum_cellLen`, hence `rescaleSub 0 n = id` and the goal is `Measure.AbsolutelyContinuous.rfl`.
  (Miss this and `IsAddHaarMeasure`/`finrank` will fail with a dimension mismatch.)
* The two non-degenerate cases then share one `key` lemma: for any affine `Φ` with injective linear
  part, matching dimensions and `(Φ x).1 = blockLen k r x`,
  `(volume.restrict O).map (rescaleSub k r) ≪ volume.restrict (simplexRegion r)`.  Its proof is the
  only measure theory: `hZ ↦ volume (Z ∩ simplexRegion r) = 0` (`Measure.restrict_apply`), a
  measurable null superset `Z'`, the null set
  `A = {u | (∀ i, 0 < u.1 i) ∧ ρ u.1 ∈ Z'}` with `ρ t i = t i.castSucc / ∑ t`
  (`volume_normalize_preimage_null` + `Measure.prod_prod`; note `volume` on a product **is**
  `volume.prod volume` definitionally, so `have hvol : volume = volume.prod volume := rfl` then `rw`),
  `A' := toMeasurable volume A` (this is what makes `Measure.map_apply` applicable *without* proving
  `A` measurable), and the chain
  `map (rescaleSub) Z = μ (rescaleSub ⁻¹' Z) ≤ μ (Φ ⁻¹' A') = (map Φ) A' = 0`.
  `Measure.AbsolutelyContinuous.mk` reduces to measurable null sets, and `≪` itself needs no
  measurability.

### Lean gotchas paid for here (each cost a compile cycle)

* `↑↑⟨k + ↑i, ⋯⟩` is opaque to `omega`: it will *not* see `i.isLt` through a `Fin.mk`.  Write the
  intermediate as a `Nat` statement (`have h2 : k + j.val < l := by omega`) and let defeq carry it,
  or keep `simp only [Fin.val_mk]; omega` (which the `unusedSimpArgs` linter then flags, because
  `simp` was doing something the linter does not count).
* `x ⟨0 + ↑j, _⟩ = x j` is **not** `rfl`: Lean 4's `Nat.add` recurses on its *second* argument, so
  `0 + n` does not reduce definitionally.  `rw [Nat.zero_add]` (or `simp only [Nat.zero_add]`, which
  also closes the `Fin`-proof mismatch by reflexivity).
* `Fin.mk a h₁ = Fin.mk a h₂` *is* `rfl` (proof irrelevance is definitional for `Fin`), so
  `(fun i : Fin m => f i.castSucc / …) = rescaleSub k (m+1) x` is `rfl` — no `Fin.ext` needed.
* `show (∑ …) = ∑ … from rfl` fails when the two sides are only *propositionally* equal after
  unfolding a `def`; `simp only [blockMass]` after the `rw` closes it.
* `Measure.prod_prod` does not fire on `volume (s ×ˢ t)` syntactically; state
  `hvol : volume = volume.prod volume := rfl` and `rw [hvol]` first.
* `Measure.map_apply` needs `MeasurableSet A`; rather than proving the set-builder measurable, pass to
  `toMeasurable volume A` (`measure_toMeasurable`, `subset_toMeasurable`).
* `absolutelyContinuous_map_affine` needs a local `Measure.IsAddHaarMeasure` instance for the
  *product* target (as in `GoodRegion.compLen_absolutelyContinuous`): build it from
  `{ toIsFiniteMeasureOnCompacts := inferInstance, toIsAddLeftInvariant := inferInstance,
  toIsOpenPosMeasure := inferInstance }` and `infer_instance`.
* `IsOpenPosMeasure.measure_pos` is `IsOpen.measure_pos (hU) (hne)`, not a `Measure.…` name.
* `Subsingleton (Fin (0-1) → ℝ)` is **not** found by instance search (`Fin (0-1)` is not `Fin 0` for
  the unifier); get `x = a` by `funext i; exact absurd i.isLt (by simp)`.
* `rw` closes the goal when it lands on `rfl` (`rw [hrescale, Measure.map_id]` on a `≪` goal), so do
  not add a trailing `exact Measure.AbsolutelyContinuous.rfl` — it errors with "no goals".

## `blockPerm` and `mkIET1_rescale_subinterval`: statements fixed, proofs in progress (this session)

Nothing of this entered the library yet; the working file is `IET2/.scratch/try/blk.lean` (compiles,
`sorry` only in the four statements listed below).  In the `Block` section, **proved**:

```lean
noncomputable def blockMass (lam : Fin n → ℝ≥0) (k : ℕ) {l : ℕ} (hln : l ≤ n) : ℝ :=
  ∑ j : Fin (l - k), (lam ⟨k + j.val, by omega⟩ : ℝ)          -- `k` explicit: it is not inferable
theorem blockMass_pos (hpos) (k) (hkl : k < l) (hln : l ≤ n) : 0 < blockMass lam k hln
noncomputable def blockLam (lam) (k) {l} (hkl : k < l) (hln : l ≤ n) (hpos) : Fin (l - k) → ℝ≥0
    := fun j => ⟨(lam ⟨k + j.val, _⟩ : ℝ) / blockMass lam k hln, _⟩
theorem blockLam_coe, theorem blockLam_sum : (∑ j, blockLam lam k hkl hln hpos j) = 1
noncomputable def blockPerm (π : Equiv.Perm (Fin n)) (k : ℕ) {l : ℕ} (hkl : k < l) (hln : l ≤ n)
    (hstab : ∀ i : Fin n, (i.val < k ↔ (π i).val < k) ∧ (i.val < l ↔ (π i).val < l)) :
    Equiv.Perm (Fin (l - k))     -- toFun j = ⟨(π ⟨k + j.val, _⟩).val - k, _⟩, inverse from π.symm
```

`blockPerm` is an **explicit `Equiv.Perm`** (per the user's convention: `ρ i = π (i + k) - k` on the
block, inverse `(ρ i) + k`), not an existential, so `IsIrreduciblePerm` of it makes sense.

The four `sorry`s left in that file are the specification for the next round (in this order):

```lean
theorem leftEnd_blockLam (j : Fin (l - k)) :
    leftEnd lam ⟨k + j.val, _⟩ = leftEnd lam ⟨k, _⟩ + blockMass lam k hln
      * leftEnd (blockLam lam k hkl hln hpos) j
theorem imageLeft_blockPerm (j : Fin (l - k)) :
    imageLeft π lam ⟨k + j.val, _⟩ - leftEnd lam ⟨k, _⟩ = blockMass lam k hln
      * imageLeft (blockPerm π k hkl hln hstab) (blockLam lam k hkl hln hpos) j
theorem idx_rescaleMap [NeZero (l - k)] (x) (hx0 : 0 ≤ x) (hx : x ∈ Ico u (u + mass)) (hj : 0 ≤ x') :
    (idx (blockLam …) x' hj).val = (idx lam x hx0).val - k
theorem mkIET1_rescale_subinterval :
    ∀ x ∈ Set.Ico u (u + blockMass lam k hln),
      rescaleMap u (u + blockMass lam k hln) (mkIET1 lam π hl x)
        = mkIET1 (blockLam lam k hkl hln hpos) (blockPerm π k hkl hln hstab)
            (blockLam_sum lam k hkl hln hpos) (rescaleMap u (u + blockMass lam k hln) x)
```

Route (unchanged from the ledger): the first two are sum decompositions — `{m | π m < π (k+j)}`
splits into `{m < k}` (π-invariant, contributes `leftEnd lam k`) and `{m ∈ [k,l) : π m < π (k+j)}`
(reindexed by `m = k + t`, contributes `blockMass * imageLeft ρ ν j`), using both directions of
`hstab`; then `idx_rescaleMap` is `idx_eq` transported through `leftEnd_blockLam`, and the main
identity is `mkIET1_apply` twice plus `field_simp`/`ring` with `blockMass > 0`.  A second swarm was
started on exactly these four statements; it had not reported when this note was written.

### Landed this session (continuation): the block API and `leftEnd_blockLam`

`IETFree/Section3BlockWord.lean` now ends with (all **proved**, axiom-clean, `#print axioms` in
`Check.lean`):

```lean
-- section LeftEnd
noncomputable def lamNat (lam : Fin n → ℝ≥0) (m : ℕ) : ℝ := if h : m < n then ↑(lam ⟨m, h⟩) else 0
lamNat_of_lt, lamNat_of_le
noncomputable def leftEndNat (lam) (i : Fin n) (m : ℕ) : ℝ   -- the `i`-th cut as an ℕ-indexed summand
leftEndNat_of_lt
theorem leftEnd_eq_sum_range (lam : Fin n → ℝ≥0) (i : Fin n) :
    leftEnd lam i = ∑ m ∈ Finset.range i.val, lamNat lam m
-- section Block
blockMass, blockMass_pos, blockLam, blockLam_coe, blockLam_sum, blockPerm
-- and
theorem leftEnd_blockLam {n : ℕ} {lam : Fin n → ℝ≥0} {k l : ℕ} (hpos : ∀ i, 0 < lam i)
    (hkl : k < l) (hln : l ≤ n) (j : Fin (l - k)) :
    leftEnd lam ⟨k + j.val, _⟩ = leftEnd lam ⟨k, _⟩ + blockMass lam k hln
      * leftEnd (blockLam lam k hkl hln hpos) j
```

`leftEnd_eq_sum_range` is the tool the whole block computation needs and it did not exist: it turns
`leftEnd` (a `Finset.filter` of a `Finset.univ` over `Fin n`) into an ℕ-indexed `Finset.range` sum,
which is what `Finset.sum_range_add (f) (k) (j)` splits at `k`
(`∑ x ∈ range (k+j), f x = ∑ x ∈ range k, f x + ∑ x ∈ range j, f (k + x)` — note the *third* argument
is the left block and the shifted summand is `f (k + x)`, which is the order `blockLam` wants).

Lean traps paid for here:
* `Finset.sum_filter` turns `∑ j ∈ univ.filter p, f j` into `∑ j, if p j then f j else 0` (the
  reverse of the notation `∑ j with p j, …`); the ℕ-indexed summand must then be a `def`
  (`leftEndNat`) because a term inside `∑ m ∈ range i, …` is elaborated **without** the membership
  hypothesis, so `⟨m, by omega⟩` cannot be used there.
* `Fin.sum_univ_eq_sum_range` takes an ℕ-indexed function, `∑ i : Fin n, f ↑i = ∑ i ∈ range n, f i`;
  to use it on `∑ j : Fin n, (if j < i then … else 0)` first prove that summand equals
  `leftEndNat lam i ↑j` pointwise.
* `Finset.sum_subset`'s arguments are named `s₁`/`s₂`, not `s`/`t`; pass them positionally.
* `rw` under a `Fin`-indexed `if` (the `Decidable` instance is part of the term) is fragile — state
  the ℕ-level fact (`have h2 : k + j.val < l := by omega`) and let `defeq` carry it to
  `(⟨k + j.val, _⟩ : Fin n).val < l`; `simp only [Fin.val_mk]; omega` also works but the
  `unusedSimpArgs` linter *falsely* flags it in `blockPerm`'s `left_inv`/`right_inv` (removing it
  breaks the `rw [show … from Fin.ext hk]`, so the two warnings at
  `Section3BlockWord.lean:569` and `:589` are accepted for now).

Still open in `.scratch/try/blk.lean` (spec + `sorry`), being worked on: `imageLeft_blockPerm`,
`idx_rescaleMap`, `mkIET1_rescale_subinterval`.  The same file also holds `leftEnd_blockLam`; the
landed version has its statement restated without the unused `hl`/`hstab`/`[NeZero n]` variables.

### Two more landed lemmas for the block computation

Also proved and landed in `Section3BlockWord` (axiom-clean, in `Check.lean`):

```lean
theorem leftEnd_le_leftEnd {n} {lam : Fin n → ℝ≥0} {i i' : Fin n} (h : i ≤ i') :
    leftEnd lam i ≤ leftEnd lam i'
theorem leftEnd_blockMass {n} {lam : Fin n → ℝ≥0} {k l : ℕ} (hkl : k < l) (hln : l < n) :
    leftEnd lam ⟨l, hln⟩ = leftEnd lam ⟨k, by omega⟩ + blockMass lam k (le_of_lt hln)
```

`leftEnd_le_leftEnd` was missing: only the *strict* version (`leftEnd_lt_leftEnd`, which needs positive
lengths) existed.  It is what gives `k ≤ (idx lam x).val` and `(idx lam x).val < l` for `x` in the
block, i.e. the two index facts `idx_rescaleMap` needs.  `leftEnd_blockMass` is the `j = last` case of
`leftEnd_blockLam` in the original coordinates (`l < n`; for `l = n` the same statement reads
`leftEnd lam ⟨l⟩ = 1 = u + blockMass`, which needs `hl : ∑ lam = 1` and has no `⟨l, _⟩ : Fin n`, so
`idx_rescaleMap` must split on `l = n`).

Note `leftEnd_blockMass` is the right-hand end of the block, so combined with `upperEnd_eq` it gives
`upperEnd lam i = u + blockMass * upperEnd ν (i - k)` for every block cell `i` except the last, and the
`x' < upperEnd ν (i-k)` half of `idx_rescaleMap` at the last cell is `x' < 1` (`upperEnd_of_max` +
`blockLam_sum`).

### Third batch for the block computation: what `idx_rescaleMap` needs

Landed (proved, axiom-clean, in `Check.lean`):

```lean
theorem lamNat_nonneg (lam : Fin n → ℝ≥0) (m : ℕ) : 0 ≤ lamNat lam m
theorem leftEnd_add_blockMass_le_total (lam) (hkl : k < l) (hln : l ≤ n) :
    leftEnd lam ⟨k, _⟩ + blockMass lam k hln ≤ ∑ i, (lam i : ℝ)
theorem idx_mem_block [NeZero n] (hkl : k < l) (hln : l ≤ n) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ∈ Set.Ico (leftEnd lam ⟨k, _⟩) (leftEnd lam ⟨k, _⟩ + blockMass lam k hln)) :
    k ≤ (idx lam x hx0).val ∧ (idx lam x hx0).val < l
```

`leftEnd_add_blockMass_le_total` is needed because `idx_rescaleMap` must feed `lt_upperEnd_idx` a
point of `Ico 0 (∑ lam)`, and the hypothesis gives only `x < u + blockMass`; **no case split on
`l = n` is needed** for it: `u + blockMass = ∑_{m<l} lamNat m ≤ ∑_{m<n} lamNat m = ∑ lam`, and
`∑_{m<k} + ∑_{x<l-k} lamNat (k+x) = ∑_{m<l}` by `Finset.sum_range_add` — the same three lines as
`leftEnd_blockLam` but with `l` in place of `k + j`.

`idx_mem_block` needs the `l < n` / `l = n` split only for the upper bound: if `l = n` then
`(idx lam x).val < l = n` is trivial, otherwise `leftEnd lam ⟨l⟩ = u + blockMass` (`leftEnd_blockMass`)
plus monotonicity gives the contradiction.

`idx_rescaleMap` itself is drafted in `.scratch/try/blk4.lean` (section `IdxShift`) and is **not**
finished: the lower bound (`leftEnd ν (i-k) ≤ x'`, from `leftEnd_blockLam` at `j = i - k` and
`idx_mem`) goes through, and the upper bound splits into "next cell inside the block"
(`leftEnd_blockLam` at `j+1` + `leftEnd_eq_upperEnd_of_succ`) and "last cell of the block"
(`upperEnd_of_max` + `blockLam_sum`, giving `x' < 1`); the remaining friction is pure `Nat`
index bookkeeping — `omega` does not accept the `Fin`-constructor casts in
`⟨j.val + 1, ?_⟩ : Fin (l - k)`, and `Nat.sub_lt_sub_right`/`Nat.sub_add_comm` have the argument
order `(k ≤ a) (a < l)`.  A later session should finish it from there rather than from scratch.

### `idx_rescaleMap` is **PROVED** (this session)

Landed in `Section3BlockWord` (axiom-clean, in `Check.lean`):

```lean
theorem idx_rescaleMap {n} [NeZero n] {lam : Fin n → ℝ≥0} {k l : ℕ} (hpos : ∀ i, 0 < lam i)
    (hkl : k < l) (hln : l ≤ n) [NeZero (l - k)] (x : ℝ) (hx0 : 0 ≤ x)
    (hx : x ∈ Set.Ico (leftEnd lam ⟨k, _⟩) (leftEnd lam ⟨k, _⟩ + blockMass lam k hln))
    (hj : 0 ≤ rescaleMap (leftEnd lam ⟨k, _⟩) (leftEnd lam ⟨k, _⟩ + blockMass lam k hln) x) :
    (idx (blockLam lam k hkl hln hpos)
        (rescaleMap (leftEnd lam ⟨k, _⟩) (leftEnd lam ⟨k, _⟩ + blockMass lam k hln) x) hj).val
      = (idx lam x hx0).val - k
```

Proof: `idx_mem_block` puts `i := idx lam x` in `[k, l)`, so `j := ⟨i.val - k, _⟩ : Fin (l - k)` is the
candidate.  Then `idx_eq` needs the two bounds:
* `leftEnd ν j ≤ x'`: `leftEnd_blockLam` at `j` gives `leftEnd lam i = u + blockMass * leftEnd ν j`,
  `idx_mem` gives `leftEnd lam i ≤ x`, so `leftEnd ν j ≤ (x - u)/blockMass` by `le_div_iff₀`;
* `x' < upperEnd ν j`: `lt_upperEnd_idx` needs `x ∈ Ico 0 (∑ lam)`, which is
  `leftEnd_add_blockMass_le_total`; then `upperEnd_eq` gives `x < leftEnd lam (i+1)`, and
  * if `i.val + 1 < l` (next cell inside the block): `leftEnd_blockLam` at `j + 1` plus
    `leftEnd_eq_upperEnd_of_succ` (hence `x' < leftEnd ν (j+1) = upperEnd ν j`);
  * if `i.val + 1 = l` (last cell of the block): `upperEnd ν j = ∑ ν = 1` (`upperEnd_of_max` +
    `blockLam_sum`, i.e. `j` is the last index since `j.val + 1 = l - k`) and `x' < 1` from `x < u + blockMass`.

Traps paid for here (all `Fin`/`Nat` bookkeeping, no mathematics):
* `rw [leftEnd_eq_upperEnd_of_succ (i := …) h]` **fails** even when the index looks identical: the
  lemma's index `⟨i.val + 1, h⟩` has `h` as an argument, and `Fin.val` blocks the unification of
  `?i` with a concrete `Fin`.  State the equality as a `have` with the same proof term
  (`leftEnd_eq_upperEnd_of_succ lam hh`) and `rw` that instead; and if the goal's right-hand side is
  the *unfolded* `upperEnd`, compose with `upperEnd_eq` in the `have`.
* `omega` refuses goals whose `Fin` bound is a constructed cast (`↑↑⟨…⟩` shows up as an opaque atom
  with no relation to `n`); write the bound at `Nat` level with
  `Nat.sub_lt_sub_right (h : c ≤ a) (a < b) : a - c < b - c` (note the argument order) and
  `(Nat.sub_add_comm h).symm : a - c + 1 = a + 1 - c`.
* `rw [blockLam_sum]` does not fire on a sum of *coerced* `ℝ≥0` terms: state
  `(∑ j, (blockLam … j : ℝ)) = 1` by `rw [← NNReal.coe_sum, blockLam_sum, NNReal.coe_one]`.
* `Finset.sum_range_add`'s third argument is the left block and the shifted summand is `f (m + x)`.

### `imageLeft_blockPerm` and `mkIET1_rescale_subinterval` are **PROVED** (this session, from the swarm)

With those two, all four statements of the block presentation are proved.  `./Build.sh` green,
`declarations still depending on sorryAx: 3` (the two frozen `Challenge` statements and Lemma 3.4),
and `#print axioms` of `RescaleBlock.imageLeft_blockPerm` and
`RescaleBlock.mkIET1_rescale_subinterval` is `[propext, Classical.choice, Quot.sound]`.

They came from a member of the second swarm (`m5`), whose file `IET2/.scratch/m5.lean` I compiled and
checked myself (exit 0, no `sorry`/`admit`/axiom, statements verbatim as pinned, nothing weakened).
It is landed at the end of `IETFree/Section3BlockWord.lean` inside `namespace RescaleBlock`, together
with its helpers:

```lean
RescaleBlock.leftEnd_eq_filter            -- leftEnd as a filter-sum over `Fin n` (rather than range)
RescaleBlock.blockPerm_apply_val, blockPerm_lt_iff
RescaleBlock.imageLeft_blockPerm_aux      -- the sum decomposition: {π m < π i} = {m < k} ⊔ {block ∩ …}
RescaleBlock.sum_range_lamNat_nonneg / _mono / _eq_total
RescaleBlock.leftEnd_add_blockMass
RescaleBlock.idx_rescaleMap_aux
RescaleBlock.leftEnd_blockLam, idx_rescaleMap   -- wrappers around the unnamespaced versions landed above
RescaleBlock.imageLeft_blockPerm
RescaleBlock.mkIET1_rescale_subinterval
```

A second member (`m3`, file `IET2/.scratch/m3_rescale.lean`) independently proved the same four
statements (also verified: exit 0, axiom-clean, same statements) and additionally an `_uncond` variant
that passes `[NeZero (l-k)]` as an instance.  Its file is kept; `m5`'s was landed because its
`imageLeft_blockPerm_aux` follows the `{m < k} ⊔ {k ≤ m < l}` decomposition the ledger prescribes.

**Inherited lint debt**: `RescaleBlock` came with `unusedSimpArgs` warnings (and one unused `hstab` in
a wrapper) at `Section3BlockWord.lean:831, 861, 873, 875, 887, 966, 1001, 1006`, plus the two
pre-existing ones at `:569, :589` in `blockPerm`.  The file is *not* linter-clean; the warnings are
cosmetic (unused simp arguments), not soundness issues, and none of the `#print axioms` reports
`sorryAx`.

### What is left for Lemma 3.4 now

The block presentation is complete: `blockLam`/`blockPerm` are the rescaled block's lengths and
permutation, and `RescaleBlock.mkIET1_rescale_subinterval` says the restriction of `mkIET1 lam π hl` to
the block rescaled is `mkIET1 (blockLam …) (blockPerm …)`.  Next in the queue (unchanged from the
ledger): (i) `IsIrreduciblePerm (blockPerm …)` from `block_irreducible_on_good` transported through the
rescaling (`irreduciblePerm_of_no_invariant_cut` in the rescaled coordinates); (ii) the a.e. transfer
of `IsDiophantine` along the length map; then `irreducible_case` and the `evalWord` equivariance.

### Lint cleanup of `Section3BlockWord` (same session)

`IETFree/Section3BlockWord.lean` is now **linter-clean** (no warnings at all).  Two mechanical changes,
no proof changed:

* every removable `simp only [Fin.val_mk]` was deleted (10 sites, in the landed `RescaleBlock` code);
* the two that are *not* removable (`blockPerm`'s `left_inv`/`right_inv`: removing them breaks the
  following `rw [show … from Fin.ext hk]`) are covered by one file-level
  `set_option linter.unusedSimpArgs false`, next to a comment saying why — this version of the linter
  has a false positive on `simp only [Fin.val_mk]` in goals whose `Fin` bound is a constructed cast;
  `beta_reduce` does not help there (it makes the `rw` motive ill-typed).
* the wrappers `RescaleBlock.leftEnd_blockLam`, `imageLeft_blockPerm` and `idx_rescaleMap` keep the
  ambient hypothesis `hl`/`hstab` in their *statements* (it is what the ledger pinned) but bind it as
  `_hl`/`_hstab`, which silences the unused-variable linter without changing the type.

`#print axioms` for all of them is unchanged (`[propext, Classical.choice, Quot.sound]`).

## `IsIrreduciblePerm (blockPerm …)`: transported through the rescaling (**PROVED**, this session)

The block presentation's last piece before the a.e. argument is that the block permutation is
irreducible.  It is now proved, axiom-clean, from the geometric irreducibility of Lemma 3.2 — no new
mathematics, only the transport through `RescaleBlock.mkIET1_rescale_subinterval`.

**Where**: the bound lemmas in `IETFree/Section3BlockWord.lean` (section `LeftEndBounds`), the transport
theorem at the end of `IETFree/Section3Reduction.lean` (section `BlockIrreducibleTransport` — it must be
there, not in `Section3BlockWord`, because it consumes `IsIrreducibleOn`, which is defined in
`Section3Reduction`; the import direction is `Section3Reduction → Section3BlockWord`).

```lean
-- Section3BlockWord
theorem leftEnd_lt_total (hpos : ∀ i, 0 < lam i) (i : Fin n) : leftEnd lam i < ∑ j, (lam j : ℝ)
theorem leftEnd_pos_of_ne_zero (hpos : ∀ i, 0 < lam i) {i : Fin n} (hi : i ≠ 0) : 0 < leftEnd lam i
theorem blockLam_pos (hpos) (hkl : k < l) (hln : l ≤ n) (j : Fin (l - k)) :
    0 < blockLam lam k hkl hln hpos j
-- Section3Reduction
theorem irreduciblePerm_blockPerm {n : ℕ} [NeZero n] {lam : Fin n → ℝ≥0} {π : Equiv.Perm (Fin n)}
    {k l : ℕ} (hl : (∑ i, lam i) = 1) (hpos : ∀ i, 0 < lam i) (hkl : k < l) (hln : l ≤ n)
    (hstab : ∀ i : Fin n, (i.val < k ↔ (π i).val < k) ∧ (i.val < l ↔ (π i).val < l))
    [NeZero (l - k)] (S : Finset ℝ) (hS : ∀ i : Fin n, k < i.val → i.val < l → leftEnd lam i ∈ S)
    (hirr : IsIrreducibleOn (fun x => mkIET1 lam π hl x) S (leftEnd lam ⟨k, _⟩)
      (leftEnd lam ⟨k, _⟩ + blockMass lam k hln)) :
    IsIrreduciblePerm (blockPerm π k hkl hln hstab)
```

**Proof**, in the order it runs.  Apply `irreduciblePerm_of_no_invariant_cut` to `ν := blockLam …` and
`ρ := blockPerm …` (its hypotheses are `blockLam_pos` and `blockLam_sum`): suppose `j ≠ 0` and the
rescaled exchange maps every `x' ∈ [0, leftEnd ν j)` into `[0, leftEnd ν j)`.  Take the corresponding
cut of the original exchange, `c := leftEnd lam ⟨k + j.val, …⟩`; `leftEnd_blockLam` identifies it with
`u + blockMass * leftEnd ν j`, so `u < c < u + blockMass` because `0 < leftEnd ν j < 1`
(`leftEnd_pos_of_ne_zero` and `leftEnd_lt_total`, both new: only the *non-strict* `leftEnd_le_total` and
the strict-positivity `leftEnd_lt_leftEnd` existed).  Then `c ∈ S` by `hS`, so by `hirr` it suffices to
show that the original exchange maps `[u, c)` into itself: for `x ∈ [u, c)`, `x' := rescaleMap u (u+M) x`
satisfies `x' ∈ [0, 1)` (`rescaleMap_mem`) and `x' < leftEnd ν j` (divide `x < u + M * leftEnd ν j` by
`M > 0`), so `mkIET1 ν ρ hν x' < leftEnd ν j` and `mkIET1 ν ρ hν x' ∈ [0,1)` (`isIET.mapsTo`); applying
the increasing map `y ↦ u + M*y` gives `mkIET1 lam π hl x ∈ [u, c)` after rewriting
`mkIET1 lam π hl x = rescaleMapInv u (u+M) (rescaleMap u (u+M) (mkIET1 lam π hl x))` and then
`RescaleBlock.mkIET1_rescale_subinterval`.

Lean traps paid for here: `IET` *extends* `Equiv`, so `mapsTo` is reached as `f.isIET.mapsTo` (there is no
`IET.mapsTo` projection), and it takes the point implicitly (`f.isIET.mapsTo hx`, not `f.isIET.mapsTo x hx`);
`Fin.last n : Fin (n+1)`, so `leftEnd_lt_total` must first write `n = m + 1`
(`Nat.sub_one_add_one (NeZero.ne n)`, *not* `(by omega)` — `omega` has no `n ≠ 0` from `[NeZero n]`);
`rescaleMapInv u v y = u + y*(v-u)`, so after `add_sub_cancel_left` the goal is `u + y*M = u + M*y` and
needs `mul_comm`; and the target of `IsIrreducibleOn` mentions `fun x => mkIET1 lam π hl x`, so a `change`
is needed before rewriting `mkIET1 lam π hl x` (beta-redex).

### `IsIrreducibleOn` is now stated on the data (user request, this session)

**The problem.**  The old definition took a naked function and an arbitrary cut set,

```lean
def IsIrreducibleOn (F : ℝ → ℝ) (S : Finset ℝ) (u v : ℝ) : Prop :=
  ∀ c ∈ S, u < c → c < v → ¬ (∀ x ∈ Set.Ico 0 1, u ≤ x → x < c → F x ∈ Set.Ico u c)
```

and `irreduciblePerm_blockPerm` fed it `fun x => mkIET1 lam π hl x` with an ad-hoc `S` plus a
hypothesis `∀ i, k < i.val → i.val < l → leftEnd lam i ∈ S`.  That is an irreducibility statement
about an `IET`, which forgets its marked points — and `S` being arbitrary made the predicate
*stronger or weaker at will*: with `S = univ` the identity exchange fails it (the counterexample in
`NOTES.md`), while with `S = {0}` it passes.  Irreducibility is a property of the permutation together
with its cells, so it must be read off the datum.

**The fix.**  In `Section3Reduction`, right after the `IETDatum` cut-set API (`markCuts`,
`isCutSet_markCuts`):

```lean
def IsIrreducibleOn {n : ℕ} [NeZero n] (D : IETDatum n) (u v : ℝ) : Prop :=
  ∀ c ∈ D.markCuts, u < c → c < v →
    ¬ (∀ x ∈ Set.Ico (0 : ℝ) 1, u ≤ x → x < c → D.toFun x ∈ Set.Ico u c)

def IsCompIrreducibleOn {d e : ℕ} [NeZero d] [NeZero e] (D : IETDatum d) (E : IETDatum e)
    (u v : ℝ) : Prop :=
  ∀ c ∈ D.markCuts ∪ D.isCutSet_markCuts.preimage E.markCuts, u < c → c < v →
    ¬ (∀ x ∈ Set.Ico (0 : ℝ) 1, u ≤ x → x < c → E.toFun (D.toFun x) ∈ Set.Ico u c)

theorem IsCompIrreducibleOn.toDatum (h : IsCompIrreducibleOn D E u v)
    (hfun : ∀ x, F.toFun x = E.toFun (D.toFun x))
    (hcuts : ∀ c ∈ F.markCuts, c ∈ D.markCuts ∪ D.isCutSet_markCuts.preimage E.markCuts) :
    IsIrreducibleOn F u v
```

The single-datum predicate is the one a *permutation of an exchange* satisfies; the pair predicate is
Lemma 3.2's conclusion for the composition `E ∘ D`, whose cells are the pieces cut by the two mark
sets and which is not a single datum.  `toDatum` is the bridge (it is what a presentation
`IsCompPresentation` will feed: the marked list must contain the cuts of the composition).

**Consequences.**

* `block_irreducible_on_good` now concludes `IsCompIrreducibleOn D E u v` (same proof).
* `irreduciblePerm_blockPerm` now reads, with no ad-hoc `S` and no `hS`:

```lean
theorem irreduciblePerm_blockPerm {n : ℕ} [NeZero n] (D : IETDatum n) {k l : ℕ} (hkl : k < l)
    (hln : l ≤ n) (hstab : ∀ i, (i.val < k ↔ (D.π i).val < k) ∧ (i.val < l ↔ (D.π i).val < l))
    [NeZero (l - k)]
    (hirr : IsIrreducibleOn D (leftEnd D.lam ⟨k, _⟩) (leftEnd D.lam ⟨k, _⟩ + blockMass D.lam k hln)) :
    IsIrreduciblePerm (blockPerm D.π k hkl hln hstab)
```
  its cut is now `leftEnd D.lam ⟨k + j.val, _⟩ ∈ D.markCuts` by `D.mark_mem_markCuts` +
  `D.mark_castSucc`, and `D.toFun` is the exchange (`RescaleBlock.mkIET1_rescale_subinterval` is
  applied with `D.sum_lam`/`D.mem_simplex`; note it needs the `ℝ≥0` sum `hlNN`, obtained from
  `D.sum_lam` by `← NNReal.coe_inj`).
* New, in `Section3BlockWord`: `IETDatum.irreduciblePerm_of_no_invariant_cut`, the datum form of the
  criterion (`D.toFun` instead of `mkIET1 D.lam D.π _`).  Traps: `irreduciblePerm_of_no_invariant_cut`
  must be called as `@_root_.irreduciblePerm_of_no_invariant_cut …` (the qualified name shadows it);
  its `hpos` is `0 < lam i` **in `ℝ≥0`**, not in `ℝ`, so `lam_pos` (which is in `ℝ`, and lives later in
  `Section3Reduction`) cannot be used — prove `← NNReal.coe_pos` first; and
  `(mkIET1 lam π hl) x = mkIETFun lam π 0 x` is `rfl` (`hlink`), which is what turns `hinv` into a
  statement about `D.toFun`.

The module docstring of `Section3Reduction` ("## 4. Lemma 3.2: …") was rewritten accordingly: with the
marked points fixed by the data, an involution gives a two-cell identity datum, which *is* irreducible —
the old failure of `IsIrreducibleOn (1 : IET 0 1) 0 1` was an artefact of the arbitrary `S`.

### The presentation as a datum (this session, continuing after the `IsIrreducibleOn` fix)

`IsCompIrreducibleOn.toDatum` needs a datum `F` presenting the composition, so the next piece is to
make `IsCompPresentation` produce one.  Landed in `Section3BlockWord` (it is there, and not in
`Section3Presentation`, because it uses `leftEnd_eq_sum_range`/`lamNat`, which live in
`Section3BlockWord` — the import order is `Section3Presentation → Section3Singularities →
Section3BlockWord`):

```lean
theorem listLeftEnd_eq_leftEnd (hmono : StrictMono s) (i : Fin n) :
    listLeftEnd s i = leftEnd (compLen hmono) i            -- rfl
theorem listImageLeft_eq_imageLeft (hmono) (ρ) (i) :
    listImageLeft ρ s i = imageLeft ρ (compLen hmono) i    -- rfl
noncomputable def sExt (s : Fin (n + 1) → ℝ) (m : ℕ) : ℝ -- ℕ-indexed extension (0 past `n`)
theorem leftEnd_compLen (hmono) (h0 : s 0 = 0) (i) : leftEnd (compLen hmono) i = s i.castSucc
theorem upperEnd_compLen (hmono) (h0) (i) : upperEnd (compLen hmono) i = s i.succ
theorem compLen_sum (hmono) (h0 : s 0 = 0) (h1 : s (Fin.last n) = 1) : (∑ i, compLen hmono i) = 1

theorem IsCompPresentation.eq_mkIET1 (P : IsCompPresentation lam π mu σ hl hm n s ρ) [NeZero n] :
    mkIET1 mu σ hm * mkIET1 lam π hl = mkIET1 (compLen P.mono) ρ (compLen_sum P.mono P.zero P.top)
```

`leftEnd_compLen` is the telescoping `∑_{j<i} (s (j+1) - s j) = s i - s 0`, done by the same route as
`leftEnd_blockLam`: `leftEnd_eq_sum_range` turns the left end into an ℕ-indexed `Finset.range` sum of
`lamNat (compLen …) m = sExt s (m+1) - sExt s m`, and `Finset.sum_range_sub` telescopes it (the
`ℕ`-indexed `sExt` is needed because the summand must be well-typed without a membership hypothesis).
`eq_mkIET1` is `IET.ext` plus `IsCompPresentation.cell` on the cell of `idx (compLen …) x` — the cell is
identified by `idx_mem`/`lt_upperEnd_idx` rewritten through `leftEnd_compLen`/`upperEnd_compLen` — and,
outside `Ico 0 1`, by `IsIET.apply_eq_self_of_lt`/`apply_eq_self_of_le` on both sides.  Two traps:
`compLen_sum`'s `Fin.sum_univ_eq_sum_range` must be used in the **forward** direction (the goal is
already the `Fin`-sum), and the last-index identification `⟨n, _⟩ = Fin.last n` is `Fin.ext rfl` but
`congrArg s` needs it before `rfl` can close the `s ⟨i.val, _⟩ = s i.castSucc` step.

**Next**: the datum `F` of a presentation is `IETDatum.ofMem ρ hv` where `hv` says the free coordinates
of `compLen` lie in `simplexRegion n` (in the `GoodRegion` setting this is `compLenAffine` and
`compLen_eq_simplexMap`); with `eq_mkIET1` giving `hfun : F.toFun = E.toFun ∘ D.toFun`, and `hcuts`
from the marked list containing the composition's cuts (`GoodRegion.mem_cutList`), the transfer
`IsCompIrreducibleOn D E u v → IsIrreducibleOn F u v` is `IsCompIrreducibleOn.toDatum`.

### The `hcuts` count, and Lemma 3.2 read on the datum of a good region (this session)

This closes the loop opened by stating `IsIrreducibleOn` on data: Lemma 3.2 is about the pair
`(D, E)`, and `irreduciblePerm_blockPerm` wants a single datum, so the chain is

`IsCompIrreducibleOn D E u v  --(toDatum)-->  IsIrreducibleOn F u v  --(irreduciblePerm_blockPerm)-->  IsIrreduciblePerm (blockPerm …)`

where `F` is the datum of the composition presented by its marked list.  All of it is landed, axiom-clean,
in `Section3Reduction` (section `GoodRegionDatum`), except the factored-out bound which is in
`Section3LengthMap`.  `Section3Reduction` gained `import IETFree.Section3Block` (it needs
`GoodRegion.surj`, `mem_cutF`, `mem_cutList`; the build order already has `Section3Block` before it).

```lean
-- Section3LengthMap (extracted from the proof of compLen_absolutelyContinuous, which now uses it)
theorem GoodRegion.compLenAffine_mem_region (hreg) (hmono) (hn1 : 1 ≤ G.n) (hq : q ∈ G.O) :
    compLenAffine G.s q ∈ simplexRegion G.n
-- Section3Reduction
noncomputable def GoodRegion.datum (hreg) (hmono) (hq) : IETDatum G.n :=
  IETDatum.ofMem G.ρ (compLenAffine G.s q)            -- lengths of the marked cells, permutation ρ
theorem GoodRegion.datum_lam       -- (G.datum …).lam = compLenVec G.s hmono q
theorem GoodRegion.datum_markCuts  -- (G.datum …).markCuts = univ.image (fun i => G.s i.castSucc q)
theorem GoodRegion.datum_hcuts     --  ↑ ↑ every marked point is in D.markCuts ∪ D⁻¹ E.markCuts
theorem GoodRegion.datum_toFun     -- (G.datum …).toFun = E.toFun ∘ D.toFun
theorem GoodRegion.irreducibleOn_datum (hirr : IsCompIrreducibleOn D E u v) :
    IsIrreducibleOn (G.datum …) u v
```

**The `hcuts` count.**  `datum_markCuts` identifies the datum's marked points with the list's entries,
and then `GoodRegion.surj` says each entry `i.castSucc` is one of four kinds:

* `0`: `s 0 q = 0` (`P.zero`) and `0 = D.mark 0` (`IETDatum.mark_zero`), so it is in `D.markCuts`;
* `Fin.last`: impossible, `Fin.castSucc_ne_last`;
* `posF i'`: `s (posF i') q = cutAffine ⟨i'+1⟩ q = leftEnd (simplexMap d q.1) ⟨i'+1⟩`
  (`SingularityShape.posF_spec` + `cutAffine_eq_leftEnd`) `= D.mark ⟨i'+1⟩.castSucc` since
  `D.lam = simplexMap d q.1` — so it is in `D.markCuts`;
* `posG j'`: `s (posG j') q = f⁻¹(leftEnd (simplexMap e q.2) ⟨j'+1⟩)` (`posG_pre`) and `D.toFun = f`,
  so `D.toFun c = E.mark ⟨j'+1⟩.castSucc ∈ E.markCuts`, i.e. `c ∈ D.isCutSet_markCuts.preimage E.markCuts`
  by `IsCutSet.mem_preimage`.

Note this needs `D.π = π` as well as `D.v = q.1` (and the `σ`, `q.2` analogues): the *permutation* is
part of the datum, which is exactly the point of the refactor — `D.toFun` is `mkIETFun D.lam D.π 0`, and
`posG_pre` is stated for `mkIET1 (simplexMap d q.1) π hl`.

**`datum_toFun`** is `IsCompPresentation.eq_mkIET1` in disguise: `(G.datum …).toFun x` is
`mkIET1 (compLenVec …) ρ _` and `E.toFun (D.toFun x)` is
`(mkIET1 (simplexMap e q.2) σ hm * mkIET1 (simplexMap d q.1) π hl) x`; the two `mkIET1`s in the
conclusion have different `∑ lam = 1` proofs, so a final `rfl` (not just the `rw`) is needed.

Lean traps paid for here: `NeZero G.n` must be an instance binder on every lemma whose *statement*
mentions `IETDatum G.n` (it is derivable from `1 ≤ G.n`, which `compLenAffine_mem_region` also needs —
hence `hn1` became `[NeZero G.n]` plus `have := NeZero.ne G.n`); `congrArg Fin.val` then
`simp only [Fin.val_castSucc, Fin.val_zero]` gives the `Nat` equation for `Fin` equalities
(`omega` on the `Fin` terms directly fails, as usual); `rw [hDfun]` turns the goal into a beta-redex,
so the `IET.apply_symm_apply'` rewrite needs a `beta_reduce` in between; and
`GoodRegion.compLenAffine_mem_region` must take `1 ≤ G.n` (`G.n = 0` would make the last-index step
false), which is why the extracted lemma has it as a hypothesis and `compLen_absolutelyContinuous`
passes its `hn1`.

### The tiling lemma, `hstab`, and Lemma 3.2 applied to the good region (this session)

The chain of the previous entries now closes: **Lemma 3.2 gives the irreducibility of the block
permutation of the marked cells**, with no hypothesis smuggled in.  All axiom-clean.

```lean
-- Section3BlockWord
theorem listLeftEnd_eq (hmono) (h0 : S 0 = 0) (i) : listLeftEnd S i = S i.castSucc
theorem listLen_pos (hmono) (i) : 0 < S i.succ - S i.castSucc
theorem comp_image_cell (P : IsCompPresentation lam π mu σ hl hm n S ρ) (i) :
    (mkIET1 mu σ hm * mkIET1 lam π hl) '' Set.Ico (S i.castSucc) (S i.succ)
      = Set.Ico (listImageLeft ρ S i) (listImageLeft ρ S i + (S i.succ - S i.castSucc))
theorem list_mem_Icc, card_fin_lt, card_rho_lt
theorem leftEnd_add_blockMass_compLen (hmono) (h0) (hkl : k < l) (hln : l ≤ n) :
    leftEnd (compLen hmono) ⟨k,_⟩ + blockMass (compLen hmono) k hln = s ⟨l,_⟩
-- Section3Reduction
theorem comp_lt_iff_of_pairSplitting (h : IsPairSplitting D E x) (hy : y ∈ Ico 0 1) :
    (E.toFun (D.toFun y) < x ↔ y < x)
theorem comp_image_Ico_zero (h : IsPairSplitting D E x) (hx1 : x ≤ 1) (hF) :
    F '' Set.Ico 0 x = Set.Ico 0 x           -- the tiling `F '' block = block`, half-open
theorem comp_image_Ico_one (h) (hx0 : 0 ≤ x) (hF) : F '' Set.Ico x 1 = Set.Ico x 1
theorem listImageLeft_lt_of_lt (P) (hF) (hu) (hik : i.val < k.val) : listImageLeft ρ S i < S k
theorem listImageLeft_ge_of_le (P) (hF) (hu) (hki : k.val ≤ i.val) : S k ≤ listImageLeft ρ S i
theorem rho_lt_iff (P) (hF) (hu : IsPairSplitting D E (S k)) (i) :
    (i.val < k.val ↔ (ρ i).val < k.val)                      -- one half of `hstab`
theorem blockPerm_stab (P) (hF) {k l} (hk) (hl') (i) :
    (i.val < k.val ↔ (ρ i).val < k.val) ∧ (i.val < l.val ↔ (ρ i).val < l.val)   -- `hstab`
theorem GoodRegion.comp_eq_toFun ...
theorem GoodRegion.irreduciblePerm_blockPerm (G) [NeZero G.n] (hreg) (hmono) (hq)
    (hDπ) (hDv) (hEπ) (hEv) (hl) (hm) {i₀ i₁} (hi : i₀ < i₁)
    (hk : IsPairSplitting D E (G.s i₀ q)) (hl' : IsPairSplitting D E (G.s i₁ q))
    (hirr : IsCompIrreducibleOn D E (G.s i₀ q) (G.s i₁ q)) :
    IsIrreduciblePerm (blockPerm G.ρ i₀.val (l := i₁.val) hi _ (blockPerm_stab …))
```

**How `hstab` is derived — and why it is not the hard route the ledger warned about.**  The ledger
says `listImageLeft_sub_of_Icc` (consecutiveness of the `ρ`-values on a block) "cannot be proved
combinatorially".  That is true of the *global* formulation; what is needed here is only the two
initial segments, and those follow from the invariance of `[0, S k)`:

1. **`F '' [S i, S (i+1)) = [L i, L i + ν i)`** (`comp_image_cell`): on the cell, `P.cell` says `F` is
   the translation by `L i - listLeftEnd S i`, and `listLeftEnd S i = S i.castSucc` is the
   telescoping (`listLeftEnd_eq`, from `leftEnd_compLen`).  Then `image_Ico_add`.
2. **`F` cuts `[0, S k)` two-sidedly** (`comp_lt_iff_of_pairSplitting` + `comp_image_Ico_zero`): this
   is where `IsPairSplitting` is used, and it is two-sided because the *inverse* is handled through
   `F⁻¹` and `IsIET.mapsTo` of the inverse.
3. **`i.val < k.val ↔ L i < S k`**: if the cell is below `S k` its image is, so `L i + ν i ≤ S k` and
   `L i < S k` (`ν i > 0`); conversely if the cell is at or above `S k` so is its image, giving
   `S k ≤ L i`.  No covering or measure argument: the two inclusions of (2) are all that is needed.
4. **The count**: with `A i = {j : L j < L i}` and `B k = {j : L j < S k}` one has
   `#A i = (ρ i).val` (`card_rho_lt`: `L` is monotone in the `ρ`-order by `listImageLeft_lt`, and
   `ρ` is a bijection) and `#B k = k.val` (`card_fin_lt`, by 3).  Then
   `i.val < k.val ⟺ #A i < #B k ⟺ (ρ i).val < k.val`, the first equivalence because
   `i ∈ B k \ A i` (resp. `B k ⊆ A i`) by 3.
5. **The block, in the datum's own coordinates**: `leftEnd (G.datum …).lam ⟨k⟩ = G.s k q`
   (`leftEnd_compLen` + `datum_lam`) and `leftEnd + blockMass = G.s i₁ q`
   (`leftEnd_add_blockMass_compLen`, telescoping in the list, no case split on `i₁ = n`), which is
   what lets `IsCompIrreducibleOn` at the geometric block be fed to
   `irreduciblePerm_blockPerm` for the datum.

Lean traps: `rw [hleft, hright]` fails where `rw [hright, hleft]` works (the first rewrite destroys
the second's pattern); `blockPerm`'s `{l}` is implicit, so `blockPerm ρ k l hkl hln hstab` silently
feeds `l` as `hkl` — write `(l := …)`; and inside the body of `GoodRegion.irreduciblePerm_blockPerm`
the unqualified name `irreduciblePerm_blockPerm` resolves to the *namespaced* declaration being
defined, so the root one must be called as `@_root_.irreduciblePerm_blockPerm`.

**Not done**: the `h "block = block` statement of the paper is half-open here
(`F '' Ico u v = Ico u v`, via `comp_image_Ico_zero`/`_one`); the closed-interval and endpoint
statements are not needed for `hstab` and are not proved.  The a.e. transfer (`irreducible_case`,
`evalWord` equivariance) is untouched.

### The a.e. transfer of the block irreducibility (this session)

Landed in `Section3Reduction` (section `BlockApplicationAE`), axiom-clean:

```lean
noncomputable def GoodRegion.blockPermOf (G) [NeZero G.n] (hreg) (hmono) (hq) (D E) …
    {i₀ i₁ : Fin (G.n + 1)} (hi : i₀ < i₁) (hk : IsPairSplitting D E (G.s i₀ q))
    (hl' : IsPairSplitting D E (G.s i₁ q)) : Equiv.Perm (Fin (i₁.val - i₀.val))
      -- `blockPerm G.ρ i₀ i₁` with its `hstab` derived by `blockPerm_stab`

theorem GoodRegion.isIrreduciblePerm_blockPermOf … (hirr : IsCompIrreducibleOn D E (G.s i₀ q) (G.s i₁ q)) :
    IsIrreduciblePerm (G.blockPermOf …)

theorem ae_irreduciblePerm_blockPerm (π σ) :
    ∀ᵐ z ∂((volume.restrict (simplexRegion d)).prod (volume.restrict (simplexRegion e))),
      ∀ (G : GoodRegion d e π σ z) (hreg) (hmono) [NeZero G.n] (D E), D.π = π → D.v = z.1 →
        E.π = σ → E.v = z.2 → ∀ (hl) (hm) {i₀ i₁} (hi : i₀ < i₁),
        IsBlock D E (G.s i₀ z) (G.s i₁ z) → IsIrreduciblePerm (G.blockPermOf …)
```

Proof: `filter_upwards [ae_goodParams_real]`, so at a.e. `z` every pair with those parameters is good
(`¬ IsBadParam (D.v, E.v)` after rewriting by `D.v = z.1`, `E.v = z.2`); then
`block_irreducible_on_good D E hp (G.s i₀ z) (G.s i₁ z) hb` is exactly the
`IsCompIrreducibleOn` hypothesis of `GoodRegion.isIrreduciblePerm_blockPermOf`.  `blockPermOf` exists
so that the statement does not have to spell out the `hstab` term (which is not printable without the
`P` and `hF` arguments); its definition *is* `blockPerm_stab`'s output, so
`isIrreduciblePerm_blockPermOf` is `irreduciblePerm_blockPerm` by definitional unfolding.

Lean traps: an `∀`-chain cannot contain `(hb : …) →` — the binders are separated by commas, so the
`IsBlock` hypothesis must be a named binder or `‹›` cannot see it; and an appended theorem after
`end BlockApplication` loses the section's `variable`s, so a new `section … variable … end` is needed
(the `NeZero d` failure is the symptom).

### What feeding `irreducible_case` still needs

`irreducible_case` (already proved in `Irreducible.lean`) needs, for the rescaled block exchange,
`hlam, hmu` (simplex membership), `hdio : IsDiophantine lam mu`, `UniqueErgodic` and
`IsRigidByTranslations`.  With `ae_irreduciblePerm_blockPerm` in hand, the last two are reachable:
`MasurVeech`/`VeechRigidity` give them almost surely in the *rescaled block's* length vector, and the
map from the parameters to that vector is absolutely continuous — which is exactly
`absolutelyContinuous_map_rescaleSub` (proved at the start of this session) composed with Lemma 3.1
(`GoodRegion.compLen_absolutelyContinuous` + `ae_of_ae_compLen`).

`hdio` is **not** reachable here: it is the Diophantine transfer, the ledger's item (2)
(`IsDiophantine.of_int_combination`, or the shape-based route through `posF_spec`/`posG_spec`), and it
was never proved.  It is also the item the person said they would prove their own way, so it must not
be substituted silently.  Concretely, what Lemma 3.4 still needs is

```lean
∀ᵐ z ∂(volume.restrict (simplexRegion d) × volume.restrict (simplexRegion e)),
  ∀ (D E) (u v) (hb : IsBlock D E u v),
    IsDiophantine (blockLam D.lam i₀ i₁ …) (blockMu …)    -- the missing transfer
```
together with the `MasurVeech`/`VeechRigidity` transfer along `rescaleSub`; then `irreducible_case`
supplies the word, and the transport of the word back to the block is `evalWord`'s equivariance
(`evalWord_conj_apply`, already proved).

### The Diophantine transfer, as the paper does it (this session)

**The paper is in the workspace**: `attachments/i-have-written-a-rcr8/paper.tex` (the LaTeX source,
1040 lines), with `biblio.bib` and `Veech-MetricTheoryInterval-1984.pdf` beside it.  It is *not* in
`repo/` proper, so it does not show up in Files browsing, but it is readable.

The three places that matter:

* **Definition 2.3** (paper line ~458): `(f_{π,λ}, f_{σ,μ})` is diophantine when there are `C, c > 0`
  with `|∑ aᵢλᵢ + ∑ bⱼμⱼ| ≥ C / max(maxᵢ|aᵢ|, maxⱼ|bⱼ|)^c` for all integer `a, b` with nonzero form.
  The library's `IsDiophantine` (in `Diophantine.lean`, with `coeffMax`) is literally this.
* **Proposition 2.5** (`prop:dioph`, paper line ~496): almost every pair is diophantine.  This is
  `ae_diophantine`, already proved (ported from the discovery run).
* **The step inside `lem:nontrivial_comp`** (paper lines ~985–1015), which is what we need: for the
  pair `(g̃f̃, g̃)` on the block, with `νᵢ` the lengths of `gf` in `P` and `μ'_j` the lengths of `g` in
  `P`,
  > "Multiply everything by `u`, and note that the `νᵢ` and the `μ'_j` are all integer linear
  > combinations of `(λ₁,…,λ_d, μ₁,…,μ_e)`. … The diophantine condition for `(f,g)` implies that the
  > left hand term is bounded below by `C/max(|Aᵢ|,|Bⱼ|)^c`. As `|Aᵢ|` and `|Bⱼ|` are bounded by a
  > constant multiple of `max(|aᵢ|,|bⱼ|)`, the result follows."

So the route is **integrality only** — no rank, no `μ'_j` as a function of `ν`, exactly the ledger's
option (i).  And the constant needs care that the paper does not spell out: after multiplying by `u`
the required bound is `C' u / N^c` while Diophantineness gives `C/(K N)^c`, so `C' := C/K^c` is enough
**because `u ≤ 1`** (the block lies in `[0,1)`).  No *lower* bound on the block length is needed — the
earlier guess in these notes that one was, is wrong.

The transfer lemma is pinned in `.scratch/try/dio.lean` (statement only; two `sorry`s in the proof):

```lean
theorem IsDiophantine.of_int_combination (hdio : IsDiophantine lam mu) (K) (hK : 0 < K)
    (w : Fin r → ℝ≥0) (w' : Fin n → ℝ≥0) (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (A : Fin r → Fin d → ℤ) (B : Fin r → Fin e → ℤ) (A' : Fin n → Fin d → ℤ) (B' : Fin n → Fin e → ℤ)
    (hA : ∀ i k, (A i k).natAbs ≤ K) … (hrn : 0 < r + n)
    (hw : ∀ i, (w i : ℝ) = ∑ k, (A i k : ℝ) * lam k + ∑ l, (B i l : ℝ) * mu l) (hw' : …) :
    IsDiophantine (fun i => ⟨w i / u, _⟩) (fun j => ⟨w' j / u, _⟩)
```
(`hrn : 0 < r + n` is needed only for the constant to be positive: with `r = n = 0` the condition is
vacuous and `C/K^c` would be undefined.  In the application `P` contains at least one cell of `gf`
and one of `g`.)

What remains after that lemma: identifying the block's `ν` and `μ'` as integer combinations of
`(λ, μ)`.  The `ν` side is the shape data (`SingularityShape.posF_spec` + `cutAffine`); the `μ'` side
is the pieces of `P` cut by `g`'s cell boundaries, i.e. the `μ'_j` are differences of `g`-cuts
truncated at `u`, `v` — and `u = s i₀ q`, `v = s i₁ q` are themselves on the list, hence integer
affine in `q`.  That is the piece to formalise next.

### Progress on `IsDiophantine.of_int_combination` (this session, **not finished**)

**Proved** (in the draft `.scratch/try/dio.lean`, not landed in the library):

```lean
theorem natAbs_sum_mul_le {ι} [Fintype ι] (f g : ι → ℤ) (N K : ℕ)
    (hf : ∀ i, (f i).natAbs ≤ N) (hg : ∀ i, (g i).natAbs ≤ K) :
    (∑ i, f i * g i).natAbs ≤ Fintype.card ι * (N * K)
```
(`Int.natAbs_sum_le`, `Int.natAbs_mul`, then `Finset.sum_const`.)

**Pinned and elaborating, proof open**: `IsDiophantine.of_int_combination` as stated in the previous
entry.  What is worked out (it compiles up to the last step):

* the combined coefficients `Acomb a b k = ∑ i aᵢ A_{i,k} + ∑ j bⱼ A'_{j,k}` and `Bcomb`, and the bound
  `(Acomb a b k).natAbs ≤ (r+n) * K * max (coeffMax a) (coeffMax b)` (same for `Bcomb`), by
  `natAbs_sum_mul_le` twice plus `Int.natAbs_add_le`;
* the algebraic identity `∑ i aᵢ (wᵢ/u) + ∑ j bⱼ (w'ⱼ/u) = T/u` where
  `T = ∑ k Acomb k · λ_k + ∑ l Bcomb l · μ_l` — the two telescoping rewrites (`hw`, `hw'`), the two
  sum swaps `Finset.sum_comm` with `Finset.sum_mul`, `add_mul`/`Finset.sum_add_distrib`, and
  `mul_div_assoc` for the `/u`.

**What is left, precisely**: the final numerical chain
`C/Ktot^c/N^c ≤ |T/u|` from the Diophantine inequality `C/maxA^c ≤ |T|`, the coefficient bound
`maxA ≤ Ktot·N`, and `u ≤ 1`:
1. `maxA > 0` — if `coeffMax (Acomb a b) = coeffMax (Bcomb a b) = 0` then every coefficient vanishes
   (each `natAbs ≤ 0`), hence `T = 0`, contradicting the hypothesis `T ≠ 0`;
2. `(Ktot·N)^c = Ktot^c · N^c` (`Real.mul_rpow`) and `maxA^c ≤ (Ktot·N)^c` (`Real.rpow_le_rpow`);
3. `|T| ≤ |T|/u` since `u ≤ 1`;
4. assemble.
That is roughly 50 lines; nothing conceptual, but it is not done.

**The identification of `ν` and `μ'` is untouched.**  Its content: `νᵢ` (lengths of `gf` in the block)
is `s (i+1) - s i`, hence integer affine in `q` by `SingularityShape.posF_spec`/`cutAffine`; and the
`μ'_j` (lengths of `g` inside the block) are the differences of consecutive `g`-cuts truncated at the
block's ends `u = s i₀ q`, `v = s i₁ q` — which are themselves on the list.  Both need the
coefficient matrices `A, B, A', B'` to be *extracted*, and that extraction is the substantial part
(integer affine forms are sums of `q`'s coordinates with integer coefficients, plus constants).

### `IsIntAffine` (this session): the predicate, the closure lemmas, the concrete maps

Landed in `Section3Presentation` (axiom-clean, in `Check.lean`).  This is the piece the Diophantine
transfer was missing: integrality of a `ParamAffine` function was nowhere recorded.

```lean
def IsIntAffine {d e : ℕ} (f : ParamAffine d e) : Prop :=
  ∃ (c : ℤ) (A : Fin (d - 1) → ℤ) (B : Fin (e - 1) → ℤ),
    ∀ q : PReal d e, f q = (c : ℝ) + ∑ i, (A i : ℝ) * q.1 i + ∑ j, (B j : ℝ) * q.2 j

isIntAffine_zero, isIntAffine_const (c : ℤ), isIntAffine_one
isIntAffine_leftCoordAffine (j), isIntAffine_rightCoordAffine (j)
IsIntAffine.add, .neg, .sub, .smul (k : ℤ), .sum (s) (h), .ite
-- the maps the block presentation is built from:
isIntAffine_imageLenAffine [NeZero d] (j : Fin d)
isIntAffine_imageLeftAffine [NeZero d] (π) (k)
isIntAffine_cutAffine (i), isIntAffine_cutAffineRight (j)
isIntAffine_preimageCutAffine [NeZero d] (π) (j) (k)
```

Consequences for the campaign — this is what makes the paper's "the `νᵢ` and the `μ'_j` are integer
linear combinations of `(λ, μ)`" a statement about *the functions of `q`* rather than about unrecorded
structure:

* `νᵢ(q) = s (i+1) q - s i q` is integer affine as soon as `s`'s entries are: `s`'s entries are
  `ParamAffine` built from `cutAffine`, `preimageCutAffine` and the constants `0`, `1`
  (`withEnds`), all covered by the closure lemmas.  In particular `leftEnd (compLen …) i = s i q`, so
  a *cut* is integer affine.
* the `g`-cuts are `cutAffineRight j = leftEnd (simplexMap e q.2) j`, and the `f⁻¹g`-crossings are
  `preimageCutAffine π j k`, so every piece of the block `[u, v) = [s i₀ q, s i₁ q)` cut by a
  `g`-cut has integer-affine endpoints, hence integer-affine length once the two truncations at `u`
  and `v` are handled (both endpoints are list entries, so they are among the `s k`, and the
  truncation `min (max (·) u) v` of an integer-affine function is again a difference of the two — the
  case split is finite and each case is `.sub` of two integer-affine maps).

Lean notes: `((k : ℝ) • f) q = k * f q` is `rfl` (there is no `AffineMap.smul_apply`); the `+`/`-`
of integer coefficient vectors need `simp only [Pi.add_apply]`/`[Pi.neg_apply]` before `push_cast`;
`imageLeftAffine` and `preimageCutAffine` need `[NeZero d]` (they go through `imageLenAffine`).

**Still open** (unchanged in kind from the previous entry): (i) the final numerical chain of
`IsDiophantine.of_int_combination`; (ii) extracting the matrices `A, B, A', B'` from `IsIntAffine`
and assembling the block's `(ν, μ')`; (iii) the `μ'` truncation argument above.

### `IsDiophantine.of_int_combination` is **PROVED** (this session)

Landed in `Diophantine.lean` (axiom-clean, in `Check.lean`), with its helper
`natAbs_sum_mul_le`.  This is the paper's `lem:nontrivial_comp` step: an integer combination of a
Diophantine pair, rescaled by `u` with `0 < u ≤ 1`, is Diophantine with the same exponent.

```lean
theorem natAbs_sum_mul_le {ι} [Fintype ι] (f g : ι → ℤ) (N K : ℕ)
    (hf : ∀ i, (f i).natAbs ≤ N) (hg : ∀ i, (g i).natAbs ≤ K) :
    (∑ i, f i * g i).natAbs ≤ Fintype.card ι * (N * K)

theorem IsDiophantine.of_int_combination (hdio : IsDiophantine lam mu) {K : ℕ} (hK : 0 < K)
    (w : Fin r → ℝ≥0) (w' : Fin n → ℝ≥0) (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (A : Fin r → Fin d → ℤ) (B : Fin r → Fin e → ℤ) (A' : Fin n → Fin d → ℤ) (B' : Fin n → Fin e → ℤ)
    (hrn : 0 < r + n) (hA …) (hB …) (hA' …) (hB' …)
    (hw : ∀ i, (w i : ℝ) = ∑ k, (A i k : ℝ) * lam k + ∑ l, (B i l : ℝ) * mu l) (hw' : …) :
    IsDiophantine (fun i => ⟨w i / u, _⟩) (fun j => ⟨w' j / u, _⟩)
```

**Proof**, in the order it runs.  With `Acomb a b k = ∑ i aᵢA_{i,k} + ∑ j bⱼA'_{j,k}` (and `Bcomb`):

1. `(Acomb a b k).natAbs ≤ Ktot · max (coeffMax a) (coeffMax b)` where `Ktot = (r+n)·K`
   (`natAbs_sum_mul_le` twice + `Int.natAbs_add_le`); same for `Bcomb`.  Hence
   `max (coeffMax (Acomb)) (coeffMax (Bcomb)) ≤ Ktot · max (coeffMax a) (coeffMax b)`.
2. The identity `∑ i aᵢ(wᵢ/u) + ∑ j bⱼ(w'ⱼ/u) = T/u` with
   `T = ∑ k Acomb k · λ_k + ∑ l Bcomb l · μ_l`: expand `hw`, `hw'`, swap the two sums
   (`Finset.sum_comm` + `Finset.sum_mul`), reassociate, and use `mul_div_assoc` for the `/u`.
3. `T ≠ 0`, and `maxA > 0` where `maxA = max (coeffMax (Acomb)) (coeffMax (Bcomb))`: if `maxA = 0`
   every combined coefficient vanishes (`natAbs ≤ 0`), so `T = 0`.
4. `C/(Ktot)^c/N^c = C/(Ktot·N)^c ≤ C/maxA^c ≤ |T| ≤ |T|/u` — `Real.mul_rpow`,
   `Real.rpow_le_rpow`, `div_le_div_of_nonneg_left`, and `u ≤ 1` for the last step.

**This settles the correction recorded earlier**: the constant is `C/Ktot^c`, and the only hypothesis
on `u` is `u ≤ 1` (an *upper* bound), not a lower bound — the paper's `C' u` on the right-hand side
becomes `C' := C/Ktot^c` after dividing.

Lean traps paid for here: `subset`-style `Finset.le_sup` needs the `f :=` argument spelled out or the
coefficient function is not inferred; the `set`-defined `Acomb`/`Bcomb` must be unfolded *before*
`push_cast` (`rw [hAcombdef]; push_cast; rfl`); the goal carries the `NNReal` coercions of the
*constructed* functions, which need an explicit `change` (with `simp only [NNReal.coe_mk]` the beta-redex
survives); and the final `calc` must be stated in the `set`-renamed `N`, not in the original cast.

**Remaining for the Diophantine transfer of Lemma 3.4**: the identification of the block's `ν` and
`μ'` as integer combinations, which the `IsIntAffine` API now supports: `νᵢ = s(i+1) − s i` and the
`g`-cut pieces are integer affine, and the coefficient matrices come from the `IsIntAffine` existentials
(`K` is the max of their coefficient bounds).  Not written yet.

### Extracting the integer coefficients (`deriving the matrices`)

Landed in `Section3Presentation` (axiom-clean, in `Check.lean`):

```lean
IsIntAffine.const, .coeffA, .coeffB      -- `Classical.choose` of the existentials
IsIntAffine.coeff_spec : f q = const + ∑ i, coeffA i * q.1 i + ∑ j, coeffB j * q.2 j

noncomputable def intAffineData {ι} [Fintype ι] (F : ι → ParamAffine d e)
    (h : ∀ i, IsIntAffine (F i)) :
    { K : ℕ // 0 < K ∧ ∃ (c : ι → ℤ) (A : ι → Fin (d-1) → ℤ) (B : ι → Fin (e-1) → ℤ),
        (∀ i k, (A i k).natAbs ≤ K) ∧ (∀ i l, (B i l).natAbs ≤ K) ∧
          ∀ (i : ι) (q : PReal d e), F i q = c i + ∑ k, A i k * q.1 k + ∑ l, B i l * q.2 l }
```

`intAffineData` is the exact input shape of `IsDiophantine.of_int_combination`: a finite family of
integer-affine functions, their constant and coefficient families, and one uniform bound `K`
(`sup + 1`, which is why it is positive).  With `F := fun i => s (i+1) - s i` (the block's `ν`) and
the `g`-cut pieces for `μ'`, and `IsIntAffine` closure giving the hypothesis, this produces the
matrices `A, B, A', B'` that `of_int_combination` consumes.

The one thing to remember: the constant term must be carried — the coefficient matrices alone do not
determine an integer-affine function, and leaving it out makes `intAffineData`'s specification false.

## Session: the word transport and the countable family of regions (landed)

State: `declarations still depending on sorryAx: 3` — `Challenge.lean:63`, `Challenge.lean:108`
(frozen) and `exists_word_trivial_on_block` (Lemma 3.4).  Everything below is axiom-clean and in
`Check.lean`.  Every build claim here was checked module by module with
`lean -o IETFree/<M>.olean IETFree/<M>.lean`; `./Build.sh` was **not** run after the last edits, so
the aggregate script itself is unverified this session.

### What was added (all new, all used by the remaining assembly)

1. **The change of generators `(f, g) ↦ (g ∘ f, g)`** (`Section3BlockWord`): `substGen`,
   `invSubstGen`, `substGen_apply`, `invSubstGen_substGen` (a left inverse, so `substGen` is
   injective), `substGen_ne_one`, `evalWord_substGen`
   (`evalWord (substGen w) f g = evalWord w (g * f) g`).
   Lemma 3.4 produces its word for the pair `(g∘f, g)`; the conclusion of Theorem 1.1 is a word in
   `(f, g)`.  The substitution `genX ↦ genY * genX`, `genY ↦ genY` is injective, with inverse
   `genX ↦ genY⁻¹ * genX`, so nontriviality is preserved.
2. **`conj_inv_of_conj`**: the inverse half of a conjugacy follows from the forward half, because an
   exchange maps `[0,1)` to itself (read the forward identity at `B'⁻¹ y`).
3. **`exists_word_trivial_on_block_of_rescaled`** — the whole transport: if `φ = rescaleMapInv u v`
   conjugates `G ∘ F` to `F'` and `G` to `G'` on `[0,1)`, then a nontrivial word trivial on
   `[0,1)` for `(F', G')` becomes a nontrivial word trivial on `[u,v)` for `(F, G)`.
4. **`ae_diophantine_real`** (`Section3Setup`): Proposition 2.5 in the free coordinates,
   `∀ᵐ z, IsDiophantine (simplexMap d z.1) (simplexMap e z.2)`.  **Do not** try to prove this with
   `MeasureTheory.ae_map_iff`: that needs `MeasurableSet {p | IsDiophantine p.1 p.2}`, which is a
   countable Boolean combination nobody wants to write.  `MeasureTheory.ae_of_ae_map` pulls an
   almost-sure statement back along a measurable map **without any measurability of the set**.
5. **`exists_countable_goodRegion_cover`** and **`ae_exists_of_countable`** (`Section3Block`): the
   local-to-global step.  `exists_goodRegion` produces a region pointwise, and the region's data
   depend on the point, so "a.e. on each region" is *not* directly "a.e.": the fix is that the
   parameter space is second-countable, hence `HereditarilyLindelofSpace`, so the open cover of the
   good set by regions has a **countable** subcover — and only countably many null sets are needed.
   `exists_countable_goodRegion_cover` is stated over `ι = Σ q, GoodRegion d e π σ q`; Lindelöf's
   `IsLindelof.elim_countable_subcover` accepts any index type and returns a countable subset.
6. **T6, the free coordinates of the rescaled block** (`Section3Block`, contributed by swarm member
   `m6` of `smvuy4hvw`, verified here): `blockLen_simplexMap`, `rescaleSub_eq_blockLam`,
   `sum_blockLen_simplexMap`, `blockLam_congr`, `GoodRegion.rescaleSub_compLenAffine`.
   `Section3Block` now imports `Section3Transport` to have `rescaleSub`.
7. **The rescaled composition and its conjugacy** (`Section3Reduction`): `GoodRegion.compLenVec_pos`,
   `GoodRegion.compLenVec_sum`, `GoodRegion.blockRescaled` (the exchange of `[0,1)` obtained by
   restricting `g ∘ f` to a block of marked cells), and `GoodRegion.comp_conj_rescale`:
   `(E.toIET * D.toIET) (rescaleMapInv u v y) = rescaleMapInv u v (blockRescaled y)` for
   `y ∈ Ico 0 1`, where `u = G.s i₀ q`, `v = G.s i₁ q`.  This is
   `RescaleBlock.mkIET1_rescale_subinterval` + `GoodRegion.comp_eq_toFun` + the two identifications
   `leftEnd_compLen` and `leftEnd_add_blockMass_compLen`.

### Lean traps paid for in this session

* `rw` does not unfold a `def`: to rewrite `G.blockRescaled …` into its body use
  `rw [show G.blockRescaled … = mkIET1 … from rfl]` (proof irrelevance makes the `hstab`/`NeZero`
  arguments match definitionally).
* `rw [h]` where `h : x = …` and the goal contains `x` inside a term whose *type* depends on `x`
  (`mkIET1`'s `hl`) breaks the motive — state the equality as a `have` in the unfolded form first,
  and use `IET.ext` + `IET.mul_apply` + `IETDatum.toIET_apply` to identify `mkIET1 … = D.toIET * E.toIET`
  (`rfl` fails: `mkIETFun … 0` vs `toFun`).
* `mkIET1` carries `[NeZero n]`: a `def` producing `mkIET1 (blockLam …)` for `n = i₁ - i₀` must be a
  `by`-block body with `haveI : NeZero (i₁.val - i₀.val) := ⟨by omega⟩` (`letI`/`haveI` present the
  same way; the `linter.style.haveILetI` complaint is spurious here, hence the scoped `set_option`).
* `mkIET1_rescale_subinterval` needs `[NeZero (l - k)]`; `blockPerm … hstab` is insensitive to the
  proof of `hstab` (`blockPermOf` matches it definitionally).
* `linarith` cannot see `0 ≤ y * (L + M - L)`; prove `mul_nonneg` by hand.

### What Lemma 3.4 still needs (concrete, in order)

The proof of `exists_word_trivial_on_block` is now structured as:

1. `filter_upwards` with `ae_goodParams_real`, `ae_mem_simplexRegion_prod`, `ae_diophantine_real`,
   and the a.e. block-ergodicity statement (item A below), all at the same `z`.
2. For each block, `GoodRegion.block_endpoints` gives indices `i₀ < i₁` with `u = s i₀ z`,
   `v = s i₁ z`, and `block_irreducible_on_good` gives `IsCompIrreducibleOn D E u v`, hence
   `IsIrreduciblePerm (blockPermOf …)` for the composition's block permutation.
3. `irreducible_case` applied to `(ν_b, μ'_b)` on `Fin (i₁-i₀)`, `Fin e`:
   * `hlam`: `blockLam_sum`; `hmu`: `∑ μ' = 1` (below);
   * `hdio`: the block Diophantine transfer (below);
   * `hue`, `hrig`: item A;
   * conclusion: a nontrivial word with `evalWord w comp g̃ = 1`;
4. `GoodRegion.comp_conj_rescale` + the `g`-side analogue give the two hypotheses of
   `exists_word_trivial_on_block_of_rescaled`, which produces the word for `(D.toIET, E.toIET)`
   trivial on `[u,v)`.

Missing inputs, each stated so it can be attacked on its own:

**A. Masur–Veech and Veech rigidity for the rescaled composition, pointwise in the region.**
For a *fixed* `G` (and `[NeZero G.n]`, `hreg`, `hmono`, block indices `k < l`):
```lean
∀ᵐ q ∂(volume.restrict G.O), ∀ (h : lam ∈ simplex (l - k)),
  UniqueErgodic (mkIET1 lam (blockPerm G.ρ k hkl hln hstab) h)      -- lam := blockLam (compLenVec G.s hmono q) k …
```
and the same for `IsRigidByTranslations`, from `hMV : MasurVeech`, `hVR : VeechRigidity` and
`IsIrreduciblePerm (blockPerm …)`.  Route: `GoodRegion.compLen_absolutelyContinuous` composed with
`absolutelyContinuous_map_rescaleSub` (using `GoodRegion.rescaleSub_compLenAffine`/`blockLam_congr`
to identify the two maps), then `MeasureTheory.ae_of_ae_map` twice.  (**Not yet written.**)

**B. The `g`-side: the restriction of `E.toIET` to the block, rescaled.**  The `g`-cells cut by the
block: with `μ'_j = max 0 (min v (upperEnd μ j) - max u (leftEnd μ j))/(v-u)` (all `j : Fin e`, zero
for a cell missing the block; `mkIET1` and `simplex` allow zero lengths), the pointwise identity
`E.toIET (rescaleMapInv u v y) = rescaleMapInv u v (mkIET1 μ' σ … y)` for `y ∈ Ico 0 1`.
This is the abstract lemma `mkIET1_restrict_invariant` — an exchange restricted to an invariant
sub-interval and rescaled is an exchange with the *same* permutation — plus the prefix-sum identity
`leftEnd μ' j = (max u (leftEnd μ j) - u)/(v-u)`.  (**Not yet written**; the swarm's `m2` is on it.)

**C. Integer-affine data for `(ν_b, μ'_b)` and the Diophantine transfer.**  `ν_b` comes from
`GoodRegion.surj` + `shape.posF_spec`/`posG_spec` (`∃ g, IsIntAffine g ∧ ∀ q ∈ G.O, G.s k q = g q`);
`μ'_b` needs the truncation pattern to be *constant on the ball* `G.O`, which is where
`IsIntAffine` + "the sign of an affine function with no zero on a convex set is constant" enters
(`Metric.ball` is convex; a sign change would give an interior zero by IVT).  Then `intAffineData` +
`IsDiophantine.of_int_combination` (constant `C/K^c`, hypothesis `u ≤ 1`).  (**Not yet written.**)

**D. The `∑ μ' = 1` and `mkIET1` bookkeeping** for the second factor, and the final `filter_upwards`
assembly.  (**Not yet written.**)

### How to use the counting argument (important)

`ae_irreduciblePerm_blockPerm` has the form `∀ᵐ z, ∀ (G : GoodRegion … z), …`: it holds because its
property is provable *pointwise* at `z` from `¬ IsBadParam z` alone.  A property that is only known
a.e. **on each region** cannot be stated in that form (**this is a trap**): one must use
`exists_countable_goodRegion_cover` + `ae_exists_of_countable`, which conclude
`∀ᵐ z, z ∈ s → ∃ i, z ∈ (G i).O ∧ P i z`.  Note that the conclusion of Lemma 3.4 is region-free, so
*any* region at `z` on which `P` holds suffices — no "the block data do not depend on the region"
lemma is needed.

### Follow-up: the free-coordinate absolute continuity, extracted (landed)

`GoodRegion.compLenAffine_absolutelyContinuous` (`Section3LengthMap`) is now a standalone lemma:
`(volume.restrict G.O).map (compLenAffine G.s) ≪ volume.restrict (simplexRegion G.n)`.
It was the local `hac'` inside `compLen_absolutelyContinuous`, extracted verbatim (the
`IsAddHaarMeasure` instances, `hAinj` from `compLen_injective`, `hinjlin` via
`injective_linear_of_injOn`, and the support argument that the image lies in the simplex region);
`compLen_absolutelyContinuous` now just calls it.  Adding it is what makes the chain for item **A**
short: `compLenAffine_absolutelyContinuous` → `Measure.AbsolutelyContinuous.map measurable_rescaleSub`
→ `absolutelyContinuous_map_rescaleSub` gives the rescaled free coordinates a.c.; one more `.map
(measurable_simplexMap …)` gives the *block length vector* a.c. against `simplexVolume (l - k)`, which
is what `ae_of_ae_compLen`/`ae_of_ae_of_absolutelyContinuous` consume.

**Not finished** (draft in `.scratch/try/blkac.lean`, **does not compile**, do not trust it):
`GoodRegion.blockLam_absolutelyContinuous`, the composition of the three maps above.  What is
proved there: the a.c. chain itself (`hres`) is fine.  What is missing is only the pointwise
identification, a.e. on `G.O`,
`blockLam (compLenVec G.s hmono q) k hkl hln hpos = simplexMap (l - k) (rescaleSub k (l-k) (compLenAffine G.s q))`,
which splits into two `Fin (l-k)` cases: an interior index is `rescaleSub` itself (via
`blockLam_coe`, `blockLen_simplexMap`, `sum_blockLen_simplexMap`), and the last index is
`1 - ∑_{i<l-k-1}` again by `Fin.sum_range_succ` on the mass.  The Lean friction is `NNReal.coe_injective`
+ `Real.coe_toNNReal` (`blockLen` is nonnegative) + the `Fin (l-k-1) ↪ Fin (l-k)` casts; the last
attempt failed on syntax (`Finset.sum_pos` binder) and on `subst` of a `Fin` index, nothing conceptual.

### The restriction of an exchange to an invariant interval: new module `Section3Restrict`

Contributed by swarm member `m2` of `smvuy4hvw`, verified here and landed as
`IETFree/Section3Restrict.lean` (508 lines, warning-free, axiom-clean, in `Check.lean`).  `Build.sh`
has it in **both** lists (`for f in …` and the `cat` of per-module logs — a new module without both
silently under-reports the `sorry` count) and `Section3Block` imports it, so everything downstream
sees it.  `./Build.sh` is green: `declarations still depending on sorryAx: 3`.

Content (namespace `RestrictIET`): `mkIET1_restrict_invariant` — an exchange `mkIET1 mu σ hl` of
`[0,1)` with all lengths positive, restricted to an invariant `[u,v) ⊆ [0,1)` and rescaled by
`rescaleFun u v`, is `mkIET1 mu' σ hl'` with the **same** permutation `σ` and
`mu' j = max 0 (min v (upperEnd mu j) - max u (leftEnd mu j)) / (v - u)` (zero for a cell that
misses the block; `mkIET1` and `simplex` allow zero lengths).  Also
`mkIET1_restrict_invariant_image` (invariance as `g '' Ico u v = Ico u v`), the named family
`truncatedLengths` with `sum_truncatedLengths : ∑ = 1`, and the prefix-sum companion
`leftEnd_truncatedLengths`.

**Correction to the brief, confirmed by hand and by m2**: the companion prefix formula I asked for,
`leftEnd mu' j = (max u (leftEnd mu j) - u)/(v-u)`, is **false** — counterexample
`mu = (1/2,1/4,1/4)`, `u = 0`, `v = 1/2`, `j = 2`: the truncated prefix sum is `1` while the literal
formula gives `3/2`.  The true statement is the **clamped** one,
`leftEnd mu' j = (clamp u v (leftEnd mu j) - u)/(v-u)` with `clamp u v t = min v (max u t)`
(`leftEnd_truncatedLengths`); it agrees with the literal form when `leftEnd mu j ≤ v`
(`leftEnd_truncatedLengths_of_le`).  Use the clamped form.

### Where item A now stands

`GoodRegion.compLenAffine_absolutelyContinuous` gives a.c. of the composition's free coordinates;
`absolutelyContinuous_map_rescaleSub` then gives a.c. of `rescaleSub` of them; one more
`.map (measurable_simplexMap …)` gives a.c. of the **block length vector** against
`simplexVolume (l - k)` — that is the chain, and it is two `Measure.AbsolutelyContinuous.map` and one
`.trans` away from being written.

The only missing ingredient is the pointwise identification
`blockLam (compLenVec G.s hmono q) k hkl hln hpos = simplexMap (l - k) (rescaleSub k (l-k) (compLenAffine G.s q))`
for `q ∈ G.O`.  With `GoodRegion.rescaleSub_compLenAffine` this is now the **first `r - 1`
coordinates for free** (`Finset.sum_congr` + that lemma), and only the last coordinate is left:
`blockLam … ⟨r-1,_⟩ = 1 - ∑_{i : Fin (r-1)} (rescaleSub …) i`, i.e.
`∑_{i<r-1} blockLam i + blockLam (r-1) = 1`, which is `blockLam_sum` combined with
`Fin.sum_univ_castSucc`.  **The friction is purely the `Fin (r-1) ↪ Fin r` cast**: `Fin r` is not
defeq to `Fin ((r-1)+1)`, so `Fin.sum_univ_castSucc` does not apply directly, and `rw`-ing
`Nat.sub_one_add_one` breaks the motive because `blockLam`'s index type depends on `r`.  Two ways
out, both cheap: (i) `Finset.add_sum_erase` on `Finset.univ.erase ⟨r-1,_⟩` plus a `Finset.sum_bij`
from `Fin (r-1)`, or (ii) state the identity for `∑ j : Fin r` with `if j.val < r-1 then … else 0`
and split with `Finset.sum_ite_lt`.  Draft with everything but that cast: `.scratch/try/blkac2.lean`.

**Lean trap for the last coordinate** (cost a cycle): there is no `Fin.sum_univ_cast`; the
route that works for `∑_{i : Fin (r-1)} f ⟨i,_⟩ + f ⟨r-1,_⟩ = ∑_{j : Fin r} f j` is to send both
sides to `Finset.range` with `Fin.sum_univ_eq_sum_range` applied to the total function
`fun m => if h : m < r then f ⟨m,h⟩ else 0`, then `Finset.sum_range_succ`.  `Fin.sum_univ_castSucc`
does not apply directly because `Fin r ≠ Fin ((r-1)+1)` definitionally, and rewriting
`Nat.sub_one_add_one` in the goal breaks the motive (`blockLam`'s index type mentions `r`).

### The swarm ended: three more modules, recovered from the "abandoned" members

`smvuy4hvw` ended with 3 accepted solutions (m6 = T6, m3 = T3, m2 = T4). **The other three members
were recorded as "abandoned — ran out of steps" and yet each had left a complete, compiling file in
its directory.** Lesson for the next swarm: after it ends, compile `*.lean` under
`.ultramath/<swarm>/*/` before writing anything off; a member can finish its proof and still be
unable to submit. All three were checked here (compile, no `sorry`, `#print axioms`) and landed.

**`IETFree/Section3BlockAE.lean`** (from m1, item **A** of the plan, now done): the almost-sure
transfer of the two external hypotheses to the block.
* `cellLen_eq_coe_simplexMap`, `blockMass_simplexMap`, `blockLam_eq_simplexMap_rescaleSub` — the
  rescaled block length vector *is* `simplexMap (l - k) (rescaleSub k (l - k) x)` (this also settles
  the last-coordinate `Fin` cast that blocked me: the trick used is
  `eq_of_forall_lt_last_eq_of_sum_eq`, two vectors of equal sum that agree below the last index are
  equal — no `Fin (r-1) ↪ Fin r` transfer needed);
* `absolutelyContinuous_map_blockFree`, `ae_blockFree_of_ae_simplexVolume`;
* `ae_uniqueErgodic_blockLam` and `ae_isRigidByTranslations_blockLam`: for a region `G`, a block
  `k < l ≤ G.n` with `hstab` and `IsIrreduciblePerm (blockPerm …)`,
  `∀ᵐ q ∂(volume.restrict G.O), ∀ (h : blockLam … ∈ simplex (l - k)), UniqueErgodic (mkIET1 (blockLam …) (blockPerm …) h)`
  (and the `IsRigidByTranslations` version), from `MasurVeech`/`VeechRigidity`.
  Its internal `ae_of_ae_map` (a wrapper of Mathlib's) was renamed `ae_of_ae_map_of_measurable` to
  avoid a root-level clash.

**`IETFree/Section3BlockDioph.lean`** (from m4 + m5, item **C**): the integer-affine data and the
Diophantine transfer.
* `GoodRegion.exists_isIntAffine_s` (every entry of the marked list agrees on `G.O` with an
  integer-affine function) and the packaged `GoodRegion.sAffine` with `isIntAffine_sAffine`,
  `sAffine_spec`;
* `GoodRegion.exists_isIntAffine_blockLen`: the block's composition lengths *and* the block mass as a
  family of integer-affine functions, with `0 < L ≤ 1` on the region;
* a `SumForm` machinery (`leftEnd/upperEnd/cutAffine/imageLeft/preimageCutAffine` are "sums of
  coordinates with integer coefficients") and `le_of_lt_of_sumForm`;
* `IsDiophantine.of_intAffine_family` (the paper's packaging) and
  `GoodRegion.isDiophantine_blockLam`, which produces `IsDiophantine (blockLam …) (fun j => Hs j q / L)`
  from `IsDiophantine (simplexMap d q.1) (simplexMap e q.2)`, an integer-affine family `Hs` for the
  `g`-pieces and their nonnegativity.  **`Hs` is the one input still to be supplied**: it is the
  `μ'` family, whose integrality needs `exists_ball_isIntAffine_truncatedLength` (m3) applied to
  `upperEnd/lowerEnd` of `simplexMap e q.2`, which are integer affine on the region but *not*
  globally (`simplexMap` uses `.toNNReal`), so state it region-locally.

Both new modules are in **both** `Build.sh` lists, imported by `Section3.lean` and
`Section3Reduction.lean`, and their key lemmas are in `Check.lean`.  `./Build.sh`: all modules `ok`,
`Tasks/Match.lean` `ok`, `declarations still depending on sorryAx: 3`.

### Remaining work for Lemma 3.4 (much smaller now)

1. The `μ'` family: `Hs j q = max 0 (min v (upperEnd (simplexMap e q.2) j) - max u (leftEnd … j))`,
   integer affine on `G.O` (m3's `exists_ball_isIntAffine_truncatedLength`, region-locally), with
   `v = G.s i₁ q`, `u = G.s i₀ q` (integer affine by m4's `exists_isIntAffine_s`);
   `RestrictIET.sum_truncatedLengths` gives `∑ μ' = 1`, i.e. `hmu` for `irreducible_case`.
2. The `g`-side conjugacy: `RestrictIET.mkIET1_restrict_invariant` with
   `hinv` from `IsPairSplitting.iff_mem` at the two ends of the block.
3. The assembly: `GoodRegion.block_endpoints` (indices `i₀ < i₁`), `block_irreducible_on_good` +
   `GoodRegion.irreduciblePerm_blockPerm` (the `hirr` of item A),
   `GoodRegion.comp_conj_rescale` + (2) feed `exists_word_trivial_on_block_of_rescaled`;
   the whole a.e. statement is assembled with `exists_countable_goodRegion_cover` +
   `ae_exists_of_countable` + `ae_diophantine_real` + `ae_goodParams_real`.

### The `g`-side of the transport (landed in `Section3Reduction`)

`GoodRegion.restrict_rescale`: for a block `[s i₀, s i₁)` of marked cells of a good region,
`E.toIET (rescaleMapInv u v y) = rescaleMapInv u v (mkIET1 μ' σ … y)` for `y ∈ Ico 0 1`, where
`μ' = RestrictIET.truncatedLengths (simplexMap e q.2) u v`.  Proof: `E.toIET = mkIET1 (simplexMap e q.2) σ hm`
(by `IET.ext` and `mkIETFun`, **not** by rewriting `toFun` — the `hm` proof argument does not transport
across `rw`), the invariance of the block under `g` from `IsPairSplitting.iff_mem` (note the `.symm`:
it gives `x ∈ Ico u v ↔ g x ∈ Ico u v`), then
`RestrictIET.mkIET1_restrict_invariant` and `rescaleMapInv_rescaleMap`.

Both halves of the pointwise conjugacy now exist (`GoodRegion.comp_conj_rescale` for `g ∘ f`,
`GoodRegion.restrict_rescale` for `g`), so `exists_word_trivial_on_block_of_rescaled` can be applied
as soon as the rescaled pair is fed to `irreducible_case`.

Still open: (1) the integer-affine family `Hs` for the `μ'` (needs
`exists_ball_isIntAffine_truncatedLength` on `upperEnd/leftEnd (simplexMap e q.2)`, region-locally);
(2) the assembly of `exists_word_trivial_on_block` (`irreducible_case` instantiation, the a.e. chain
with `exists_countable_goodRegion_cover` + `ae_exists_of_countable`, the two conjugacies, and the
case of a block with a single composition cell, where `g ∘ f = id` on the block and the word is
`genY * genX`).

### Corrections and additions after the person's review

**The person's point, now implemented**: the rescaled block lengths must not be routed through
`NNReal`.  The real cell lengths of `g` are free coordinates, so they are integer affine on *all* of
`PReal d e` and no region-local integrality is needed for them.  Added to `Section3BlockDioph`
(section `GCells`), all axiom-clean:

* `gLenAffine (j : Fin e) : ParamAffine d e` — `q.2 j` away from the last cell, `1 - ∑ q.2` at the
  last one (the `g`-analogue of `imageLenAffine`), with `isIntAffine_gLenAffine`;
* `gLenAffine_eq`: on the open simplex region it is `(simplexMap e q.2 j : ℝ)`;
* `gUpperEnd (j : Fin e)` — the next cut, and `1` at the last cell — with `isIntAffine_gUpperEnd` and
  `gUpperEnd_eq : gUpperEnd j q = (upperEnd (simplexMap e q.2) j : ℝ)` on the region;
* the left ends are `cutAffineRight j` (`isIntAffine_cutAffineRight`, `cutAffineRight_eq_leftEnd`),
  already there.

So the `μ'` family is `max 0 (min v (gUpperEnd j) - max u (cutAffineRight j))` with `u = sAffine i₀`,
`v = sAffine i₁` — **all four functions globally integer affine**, and `max 0`/`min`/`max` are
decided on the region `G.O` by the rigidity lemmas of `Section3BlockDioph`
(`le_of_lt_of_sumForm`, `eq_on_of_eq_at`, plus `Convex.exists_isIntAffine_truncatedLength` for the
branch with strict inequalities).  The sign decisions are read off the single point `G.mem_O`: `O` is
a ball (`exists_goodRegion`), hence convex, and two `SumForm` functions that meet at one point of a
good region coincide on all of it.

Note for the assembly: `GoodRegion` records only `IsOpen O`, not convexity, so the `μ'` lemma carries
`hconv : Convex ℝ G.O` as a hypothesis (discharged from `Metric.isOpen_ball`-style convexity at the
point of use, since `exists_goodRegion` produces a ball).

**Also landed this round**: `GoodRegion.restrict_rescale` (the `g`-side conjugacy) — see above.

**Still open**: the `μ'` existence lemma itself (the case analysis over the truncation pattern), and
the assembly of `exists_word_trivial_on_block`.

### The `μ'` family of a block (landed in `Section3BlockDioph`)

`GoodRegion.exists_isIntAffine_mu'`: at any point `q ∈ G.O` there is a family `Hs : Fin e →
ParamAffine d e`, **all of it globally integer affine**, with
```
Hs j q = max 0 (min (G.s i₁ q) (upperEnd (simplexMap e q.2) j) - max (G.s i₀ q) (leftEnd … j))
```
and `GoodRegion.truncatedLengths_eq`: `(RestrictIET.truncatedLengths (simplexMap e q.2) (G.s i₀ q)
(G.s i₁ q) huv j : ℝ) = Hs j q / (G.s i₁ q - G.s i₀ q)`.

**Key design point** (this is what made it short — about 60 lines): the truncation pattern only has
to be settled **at the point `q`**, not on the region, because `IsDiophantine.of_intAffine_family`
consumes the identity `w' j = ∑ A' λ + ∑ B' μ` at that one point.  So the proof is a four-way
`rcases le_total` at `q` (`L q` vs `u q`, `v q` vs `U q`) plus `by_cases` on the sign of the
difference, and in each branch the witness is one of `v - u`, `U - u`, `v - L`, `U - L`, or `0` —
all globally integer affine.  No convexity, no rigidity, no `¬ IsBadParam` argument is needed.  The
witness is written as `if (0:ℝ) ≤ v q - u q then v - u else 0` (`IsIntAffine.ite`), with the
condition in *unfolded* form so that the subsequent `rw [AffineMap.coe_sub, Pi.sub_apply]` matches
`h3 : (0:ℝ) ≤ v q - u q` (this mismatch cost a cycle).  Note `AffineMap` has no `One`:
write `AffineMap.const ℝ (PReal d e) (1 : ℝ)`.

### The assembly of `exists_word_trivial_on_block`: the plan (swarm `smvuzi4hf` is on it)

Five independent pieces, each stated in the swarm brief:
* **A1** the degenerate block (`i₁.val - i₀.val = 1`): `mkIET1 (fun _ => 1) π hl = 1` for `Fin 1`
  (`translationVector` vanishes at the only index), `blockLam … = fun _ => 1` when `l - k = 1`, and
  `genY * genX ≠ 1`; the word is `genX` (whose substitute `substGen genX = genY * genX` is the
  composition `g ∘ f`, trivial on the block).
* **A2** the Diophantine instantiation: `IsDiophantine (blockLam …) (truncatedLengths …)` from
  `IsDiophantine (simplexMap d q.1) (simplexMap e q.2)` via `IsDiophantine.of_intAffine_family`,
  `Fs := G.sAffine ⟨k+j+1⟩ - G.sAffine ⟨k+j⟩`, `Hs` from `exists_isIntAffine_mu'`,
  `L := G.s i₁ q - G.s i₀ q` (with `0 < L ≤ 1` from `leftEnd_add_blockMass_compLen`).
* **A3** the a.e. glue: `rw [ae_iff]`, bound the bad set by the countable union
  `⋃ i, ((Gfam i).2.O ∩ BAD i)` from `exists_countable_goodRegion_cover`, each term null
  (`G.subset_good`, `G.subset_region`, `ae_diophantine_real`, and the two `ae_…_blockLam`
  statements combined over all `k, l` with `Filter.Eventually.all`).
* **A4** the pointwise conclusion (the core): `block_endpoints` → `i₀ < i₁`; `blockPerm_stab`;
  `block_irreducible_on_good` + `irreduciblePerm_blockPerm` for `hirr`; then either the single-cell
  case (A1) or `irreducible_case` + `exists_word_trivial_on_block_of_rescaled` fed by
  `GoodRegion.comp_conj_rescale` and `GoodRegion.restrict_rescale`.
* **A5** the final `filter_upwards` combination.

Status: `./Build.sh` green before the swarm started, `declarations still depending on sorryAx: 3`
(the two frozen `Challenge` statements and Lemma 3.4).  The `μ'` family was the last *missing
mathematical input*; what remains is the case analysis and the a.e. bookkeeping.

### Lemma 3.4: A1, A2 and A4 landed (this round)

`./Build.sh` green, `declarations still depending on sorryAx: 3` (the two frozen `Challenge`
statements and `exists_word_trivial_on_block`).  Landed in `Section3Reduction` (in the `GoodRegion`
namespace) and `Section3Block`, all axiom-clean and in `Check.lean`:

* **A4, the pointwise conclusion** — `GoodRegion.exists_word_trivial_of_region`: at a point `q` of a
  good region, given the block data *at that point* (`hue`, `hrig` for every `(k,l,hstab,hirr)`, and
  `hdio` for every block), every `IsBlock D E u v` carries a nontrivial word trivial on it.  Proof:
  `block_endpoints` → `i₀ < i₁`; `block_irreducible_on_good` + `isIrreduciblePerm_blockPermOf` for
  `hirr`; then either `i₁ - i₀ = 1` (the rescaled composition is the identity, `mkIET1_of_all_one`,
  and `hex := ⟨genX, …⟩` since `evalWord genX F' G' = F' = 1`) or ≥ 2 (`irreducible_case`), and both
  cases end with `exists_word_trivial_on_block_of_rescaled` fed by `comp_conj_rescale` and
  `restrict_rescale`.
* **A1, the degenerate block**: `mkIET1_of_all_one` (an exchange all of whose lengths are `1` is the
  identity — `∑ lam = 1` forces `Fin r` to be a subsingleton, then every translation vector vanishes),
  `blockLam_of_one`, `mkIET1_fin_one`, `translationVector_fin_one`, `genX_ne_one`,
  `genY_mul_genX_ne_one` (via `FreeGroup.toWord`: `toWord (genY * genX) = [(1,true),(0,true)]`).
* **A2, the Diophantine condition at the block** — `GoodRegion.isDiophantine_blockPair`:
  `IsDiophantine (blockLam …) (RestrictIET.truncatedLengths …)` from
  `IsDiophantine (simplexMap d q.1) (simplexMap e q.2)`, via `IsDiophantine.of_intAffine_family` with
  `Fs j = sAffine ⟨k+j+1⟩ - sAffine ⟨k+j⟩` and `Hs` from `exists_isIntAffine_mu'`, `L = s i₁ q - s i₀ q`,
  then identifying the two families with `blockLam_coe`, `hmass` (`s i₁ q - s i₀ q = blockMass`) and
  `truncatedLengths_coe`.
* **`paramMeasure` + `paramMeasure_absolutelyContinuous`** (`Section3Block`): the assembly mixes two
  measures (the product measure for `ae_goodParams_real`/`ae_diophantine_real`, and
  `volume.restrict G.O` for the block statements); this reconciles them via
  `Measure.absolutelyContinuous_restrict` and `Measure.AbsolutelyContinuous.prod`.

**What is still missing** (A3 and A5, the a.e. bookkeeping; swarm `smvuzi4hf` is on both):
* **A3** — the bundled a.e. statement: `rw`-free route is
  ```
  ∀ᵐ z ∂(paramMeasure d e), z ∈ goodParams d e → z.1 ∈ simplexRegion d → z.2 ∈ simplexRegion e →
    ∃ G : GoodRegion d e π σ z, z ∈ G.O ∧ IsDiophantine … ∧
      ∀ (hmono : ∀ q, StrictMono fun k => G.s k q) (k l) (hkl) (hln) [NeZero (l-k)] (hstab),
        IsIrreduciblePerm (blockPerm …) → (∀ h, UniqueErgodic …) ∧ (∀ h, IsRigidByTranslations …)
  ```
  proved with `exists_countable_goodRegion_cover` + `ae_exists_of_countable`: for each index `i` the
  bad set is null on `(Gfam i).2.O`, because `IsDiophantine` fails only on a `paramMeasure`-null set
  (`ae_diophantine_real`), and the block statements hold `volume.restrict O`-a.e.
  (`ae_uniqueErgodic_blockLam`, `ae_isRigidByTranslations_blockLam`, combined over all `k, l` with
  `Filter.Eventually.all`), so `paramMeasure (O i ∩ bad) = 0` by
  `paramMeasure_absolutelyContinuous`.  **Note** `hmono` is *not* a field of `GoodRegion` (it is
  `(G.pres q hq hl hm).mono` at each `q ∈ O`, but not available off `O`), so it must be a binder in
  the bundle, exactly as in the hypotheses of A4.
* **A5** — `filter_upwards` with A3 (`ae_goodParams_real`, `ae_mem_simplexRegion_prod`), then for the
  data apply A4 with `hue`/`hrig` from the bundle and `hdio := fun i₀ i₁ hi => isDiophantine_blockPair …`.

### A3 landed (swarm `smvuzi4hf`, member m2): `Section3BlockData`

Verified here and landed as `IETFree/Section3BlockData.lean` (477 lines, warning-free, axiom-clean,
namespace `BlockData`, in both `Build.sh` lists and imported by `Section3.lean`).  `./Build.sh`: all
`ok`, `declarations still depending on sorryAx: 3`.

`BlockData.exists_ae_block_good π σ hMV hVR` gives the countable family `G : ι → Σ q, GoodRegion d e
π σ q` together with its cover of the good set and the almost-sure bundle
```
∀ᵐ z ∂(paramMeasure d e), ¬ IsBadParam z ∧ z.1 ∈ simplexRegion d ∧ z.2 ∈ simplexRegion e ∧
  IsDiophantine (simplexMap d z.1) (simplexMap e z.2) ∧
  ∀ (i : ι) (hz : z ∈ (G i).2.O), BlockGoodAt (G i).2 hz
```
with `BlockGoodAt G hz = ∀ (k l) (hkl) (hln) (hne : NeZero (l-k)) (hstab),
IsIrreduciblePerm (blockPerm …) → BlockGood (blockLam (compLenVecAt G.s q (monoAt G hz)) …) …` and
`BlockGood lam τ = (∀ h, UniqueErgodic (mkIET1 lam τ h)) ∧ ∀ h, IsRigidByTranslations …`.
Auxiliary: `ae_forall_countable`, `ae_imp_of_ae_restrict`, `prodRestrict_le_volume`, the
unconditional `compLen_absolutelyContinuousAt`, `compLenVecAt_eq_simplexMap`, `blockLamAt_eq`.

**The important design point (m2's, and it is right): `hmono` is not derivable.**  `compLenVec s hmono
q` takes `hmono : ∀ q, StrictMono fun k => s k q`, but a `GoodRegion` only knows monotonicity at
points of `O` (through `G.pres`), and nothing prevents `G.s · q` from being non-monotone for `q ∉ O`.
So m2 introduced `compLenVecAt s q (hm : StrictMono fun k => s k q)` — the *pointwise* contract,
definitionally equal to `compLenVec s hmono q` — and `monoAt G hq : StrictMono fun k => G.s k q`.  The
bundle is therefore `hmono`-free, and **A2/A4 (which I wrote with a global `hmono`) must be refactored
to take the pointwise `hmono` and use `compLenVecAt`/`compLenVecAt_pos`** before A5 can be stated.
The refactor is textual (`compLenVec G.s hmono q ↦ compLenVecAt G.s q hmono`,
`compLenVec_pos G hmono q ↦ compLenVecAt_pos G.s q hmono`, `hmono q hi ↦ hmono hi`) but it also has to
be done in `GoodRegion.comp_conj_rescale` and `GoodRegion.restrict_rescale`, and the proofs that use
m4's `compLenVec_coe_eq` (global `hmono`) must go through `compLenVecAt_eq_compLenVec`.  A first
attempt failed on exactly that: `(fun _ => hmono)` is **ill-typed** as a `∀ q, StrictMono (fun k =>
G.s k q)` (the body is at the fixed point, not at `q`), and `truncatedLengths`'s `huv` needs the
`show`-cleaned form `(hmono hi : G.s i₀ q < G.s i₁ q)` (beta-redex otherwise).

**A5, the last step**, is then `filter_upwards [exists_ae_block_good …]`, `hcov` to pick `i` with
`z ∈ (G i).2.O`, and one application of `exists_word_trivial_of_region` with `hmono := monoAt (G i).2
hz`, `hue`/`hrig` from `BlockGoodAt`, `hdio` from `isDiophantine_blockPair` — as soon as A2/A4 take the
pointwise `hmono`.

### A refutation of the old hypothesis, and the fix (person's decision)

**Finding (swarm `smvuzi4hf`, member m3 — verified independently here).**  `MasurVeech` as it stood
was **false**, hence every theorem conditional on it (Lemma 3.4, `main_theorem_of_blocks`, and my
A1–A4) was vacuous.  The chain, each step checked in Lean and by hand:

* `translationVector (1 : Equiv.Perm (Fin n)) lam i = 0` (`imageLeft` and `leftEnd` are the same
  sum), hence `mkIET1 lam (1 : Equiv.Perm (Fin n)) h = 1` for every `n, lam`;
* `¬ UniqueErgodic (1 : IET 0 1)`: for `ψ = y ↦ y` and `ε = 1/4` the Birkhoff averages of the
  identity are constantly `x`, so `x = 0` and `x = 3/4` contradict the uniform bound;
* `IsIrreduciblePerm` is **vacuous on `Fin 1` and `Fin 2`**: its conclusion
  `(∀ i, ¬ i < k) ∨ (∀ i, i ≤ k)` holds at every `k` when `d ≤ 2`;
* `simplexVolume 1` is a Dirac mass (`(univ : Set (Fin 0 → ℝ))` has volume `1`), so it is nonzero.

Hence `¬ MasurVeech`.  **Consequence not to be taken**: `exists_word_trivial_on_block` followed by
`absurd hMV not_masurVeech`.  That proof is not landed — it would make the development trivially
true.  The defect is in the *formalisation of the hypothesis*, not in the paper.

**The fix (the person's decision: do not touch `IsIrreduciblePerm`, restrict `MasurVeech` to `2 ≤ d`).**
Implemented in `Irreducible.lean` as `2 ≤ d` **and** `π ≠ 1`:
```lean
def MasurVeech : Prop :=
  ∀ (d : ℕ) (_ : 2 ≤ d) [NeZero d] (π : Equiv.Perm (Fin d)), IsIrreduciblePerm π → π ≠ 1 →
    ∀ᵐ lam ∂(simplexVolume d), ∀ (h : lam ∈ simplex d), UniqueErgodic (mkIET1 lam π h)
```
`π ≠ 1` is **not** redundant: with only `2 ≤ d` the `d = 2` case is still vacuous
(`IsIrreduciblePerm (1 : Perm (Fin 2))` holds), so the same refutation would go through at `d = 2`.
At `d ≥ 3` the identity is already excluded by `IsIrreduciblePerm`, so `π ≠ 1` only bites at `d = 2`,
where it selects the transposition — which is exactly the paper's content (a two-interval exchange is
a rotation, uniquely ergodic for a.e. length).  `VeechRigidity` is **not** refutable this way: the
identity *is* rigid by translations (`tₙ = 0`, `Bₙ = [0,1)`), so it keeps its old form.

**Re-threaded for the new signature** (both compile, axiom-clean): `ae_uniqueErgodic_blockLam` and its
`'`/`_apply` variants now carry `(h2 : 2 ≤ l - k)` and `(hne1 : blockPerm … ≠ 1)`;
`BlockData.ae_blockGood_free`/`ae_blockGood_allStab`/`ae_blockGood_range`/`BlockGoodAt` carry the two
new arrows `→ 2 ≤ l - k → blockPerm … ≠ 1 →` in their telescopes.  `./Build.sh`: all `ok`,
`declarations still depending on sorryAx: 3`.

**Consequences for the remaining assembly (A5).**
1. `GoodRegion.exists_word_trivial_of_region` (A4) must take the same two arrows in `hue` (its `hrig`
   is unchanged), supplied in the `≥ 2` branch by `h2 : 2 ≤ i₁.val - i₀.val` and `hne1` — and `hne1`
   is *not* free at `l - k = 2`, because `IsIrreduciblePerm` gives nothing there.  Two ways out, both
   sound: (i) prove `blockPerm ≠ 1` from `IsCompIrreducibleOn`: if `blockPerm = 1` on two cells then
   `imageLeft = leftEnd` on the first cell, so `g ∘ f` is the identity on `[u, s(i₀+1))`, whose
   interior cut `s(i₀+1)` is then invariant, contradicting `hirr`; (ii) better, treat `blockPerm = 1`
   uniformly with the `r = 1` case: then the rescaled composition is `mkIET1 ν 1 = 1` (needs only
   `translationVector_one`, i.e. the lemma `mkIET1_one` below), so `hex := ⟨genX, …⟩` works exactly as
   in the single-cell case, and `irreducible_case` is only used when `blockPerm ≠ 1`.
2. The `r = 1` case also follows from `mkIET1_one` (no need for `mkIET1_of_all_one`): `Fin 1` has a
   unique permutation, namely `1`.
3. `mkIET1_one` and its helpers (`translationVector_one`, `mkIETFun_one`) are in m3's file and are
   *independent of the refutation*; they should be landed (they are the clean form of "the exchange
   with the identity permutation is the identity") and then used as in (1)(ii).

### `IsIrreduciblePerm` now matches the paper (person's instruction)

The old definition was
```lean
∀ k : Fin d, (∀ i, i ≤ k → π i ≤ k) → (∀ i, ¬ i < k) ∨ ∀ i, i ≤ k
```
whose two disjuncts are the *trivial* initial segments `{i | i ≤ k}` = ∅ (at `k = 0`) and the whole
of `Fin d` (at `k = d-1`).  That is **weaker than the paper's condition at every `d`**, not only at
`d ≤ 2`: it permits a **fixed first cell** (`π 0 = 0`), which is the paper's `k = 1` obstruction
(`π{1} = {1}`).  Witnesses in Lean, before the change: `IsIrreduciblePerm (1 : Equiv.Perm (Fin 2))`
and `IsIrreduciblePerm (Equiv.swap (1 : Fin 3) 2)` both held.  The consequence was not academic: for
`π 0 = 0` one has `translationVector π lam 0 = 0`, so `mkIET1 lam π h` is the identity pointwise on
`[0, λ₀)`, hence not ergodic and not uniquely ergodic — so `MasurVeech` was refutable at `d = 3` as
well, and `2 ≤ d` (or `2 ≤ d ∧ π ≠ 1`) could not repair it.

**New definition** (the paper's: the only invariant initial segment is the full one — equivalently
`π{1,…,k} ≠ {1,…,k}` for `1 ≤ k < d`):
```lean
def IsIrreduciblePerm {d : ℕ} (π : Equiv.Perm (Fin d)) : Prop :=
  ∀ k : Fin d, (∀ i : Fin d, i ≤ k → π i ≤ k) → ∀ i : Fin d, i ≤ k
```
`MasurVeech` keeps only `(_ : 2 ≤ d)` (still necessary: on one cell the exchange is the identity for
every length vector, and `IsIrreduciblePerm` holds on `Fin 1`); the `π ≠ 1` conjunct is now
**redundant** and has been removed — at `d ≥ 2` the singleton case `k = 0` already forbids `π 0 = 0`,
hence the identity.  `VeechRigidity` needs no restriction at all (the identity *is* rigid by
translations, `tₙ = 0`).

**What had to change.**
* `irreduciblePerm_of_no_invariant_cut`: only the `k = 0` branch was replaced.  The old proof did
  `left` there (the trivial disjunct); the general argument — take `k' = ⟨k.val + 1, _⟩`, apply the
  no-invariant-interval hypothesis, and use `imageLeft_add_le_of_invariant` — **never used `k ≠ 0`**,
  so deleting the case split makes the proof the paper's.  `IETDatum.irreduciblePerm_of_no_invariant_cut`,
  `irreduciblePerm_blockPerm` and `isIrreduciblePerm_blockPermOf` then follow unchanged.
* `Section3BlockAE` / `Section3BlockData`: the `blockPerm … ≠ 1` hypothesis threaded through the block
  bundle is gone (only `2 ≤ l - k` remains, which m3's `not_uniqueErgodic_fin_one` shows is *forced*:
  no one-cell exchange is uniquely ergodic).
* Verified after the change: `¬ IsIrreduciblePerm (1 : Equiv.Perm (Fin 2))`,
  `¬ IsIrreduciblePerm (Equiv.swap (1 : Fin 3) 2)`, and `IsIrreduciblePerm (Equiv.swap (0 : Fin 2) 1)`
  (the transposition, i.e. the paper's `d = 2` case) — all in Lean.

`./Build.sh`: all `ok`, `declarations still depending on sorryAx: 3`.  The refutation of
`MasurVeech` is dead, and the hypothesis is now the paper's.

### The last blocker of A4, found and proved (swarm `smvuzi4hf`, member m3)

`GoodRegion.exists_word_trivial_of_region` (A4, landed) quantifies `hue` over **all**
`k < l ≤ G.n`, with no lower bound on `l - k`.  That is **unsatisfiable**, and provably so:
`not_uniqueErgodic_blockLam_of_one_cell` — at `l - k = 1` the block length vector is identically `1`
(`blockLam_of_one`), so `mkIET1_of_all_one` makes the block exchange the identity, and the identity is
not uniquely ergodic.  So `hue` must carry `(h2 : 2 ≤ l - k)`; `hrig` needs **no** arrow, because the
one-cell block *is* rigid by translations (`isRigidByTranslations_blockLam_of_one_cell`).  That is
exactly the shape the landed `BlockData.BlockGoodAt` / `exists_ae_block_good` supplies, so after this
one re-threading A5 is `filter_upwards` only.

Supporting audit in the same file (all verified, axiom-clean): `not_uniqueErgodic_of_perm_zero` (a
fixed first cell `π 0 = 0` makes the exchange the identity on `[0, λ₀)`, hence never uniquely
ergodic — the independent witness that `IsIrreduciblePerm` had to be strengthened, now done);
`ne_zero_apply_zero_of_isIrreduciblePerm`, `ne_one_of_isIrreduciblePerm` (at `2 ≤ d` both refutation
routes are excluded, so the corrected `MasurVeech` is consistent by these means);
`eq_swap_of_isIrreduciblePerm` (`d = 2` forces the transposition); `blockPerm_ne_one_of_isIrreducible`
(from `2 ≤ l - k` and irreducibility, `blockPerm ≠ 1`).

**Remaining for A5** (both items mechanical but they must be done together):
1. A4 and A2 take a *global* `hmono : ∀ q, StrictMono fun k => G.s k q`, which is **not derivable**
   from `GoodRegion` (monotonicity is known only at points of `O`, via `G.pres`), so they must be
   re-threaded onto m2's pointwise contract `compLenVecAt G.s q (monoAt G hq)` — and so must
   `GoodRegion.comp_conj_rescale` and `GoodRegion.restrict_rescale`, which take the same global
   `hmono`.  The substitutions are: `compLenVec G.s hmono q ↦ compLenVecAt G.s q hmono`,
   `compLenVec_pos G hmono q ↦ compLenVecAt_pos G.s q hmono`, `hmono q hi ↦ hmono hi`, and
   `compLenVec_coe_eq hmono hq ↦` via `compLenVecAt_eq_compLenVec`.  Note `(fun _ => hmono)` is
   **ill-typed** as a `∀ q, StrictMono (fun k => G.s k q)`: the body lives at the fixed point.
2. A4's `hue` gains `(h2 : 2 ≤ l - k)` (from m3's finding above); `hrig` and `hdio` do not.
3. A5: `filter_upwards [BlockData.exists_ae_block_good π σ hMV hVR]`, `hcov` to pick the region
   containing `z`, then `exists_word_trivial_of_region` with `hmono := monoAt (G i).2 hz`, `hue`/`hrig`
   from `BlockGoodAt` and `hdio := isDiophantine_blockPair`.

### Why the pointwise-`hmono` refactor is not a substitution (measured, not estimated)

The refactor asked for — A2/A4 and the two conjugacy lemmas on `compLenVecAt G.s q (monoAt G hq)`
instead of a global `hmono : ∀ q, StrictMono fun k => G.s k q` — hits a structural obstacle that is
worth recording before anyone tries it again.

`compLenVec s hmono q` needs `hmono : ∀ q, StrictMono fun k => s k q`, and **a pointwise proof cannot
be turned into a global one**: `GoodRegion` only knows monotonicity at points of `O` (via `G.pres`),
nothing prevents `G.s · q` from being non-monotone off `O`, and no `Classical.choice` can fabricate a
proof of a possibly-false `Prop`.  Likewise `(fun _ => hmono)` is ill-typed as a `∀ q, StrictMono
(fun k => s k q)` — the body lives at a fixed point.

Consequently the *binders have to be reordered*: a pointwise `hmono` mentions `q`, so `{q}` must be
bound before it, whereas every lemma in the chain currently binds `(hmono) … {q} (hq)`.  The lemmas on
the critical path, each needing its argument order changed and its proof adjusted, are
`GoodRegion.compLenAffine_mem_region` and `compLen_eq_simplexMap` (`Section3LengthMap`),
`GoodRegion.datum`, `datum_lam`, `datum_toFun`, `comp_eq_toFun`, `blockPermOf`,
`irreduciblePerm_blockPerm`, `blockRescaled`, `comp_conj_rescale`, `restrict_rescale`,
`isDiophantine_blockPair`, `exists_word_trivial_of_region`.  Two of these (`comp_eq_toFun`,
`irreduciblePerm_blockPerm`) go through `GoodRegion.datum`, which is built from
`compLenAffine_mem_region`; m2's `BlockData` layer already provides the pointwise replacements
(`compLenAffine_mem_regionAt`, `compLenVecAt_eq_simplexMap`, `monoAt`, `compLen_absolutelyContinuousAt`),
so the hmono-free copies should be written *against those*, replacing `G.datum …` by
`IETDatum.ofMem G.ρ (compLenAffine_mem_regionAt …)` and `G.blockPermOf …` by
`blockPerm G.ρ k hkl hln (blockPerm_stab P hF hk hk')` directly (they are definitionally equal).

**The cleaner architectural fix** is to change `compLenVec`'s own interface: make it take the
pointwise `StrictMono` (i.e. make `compLenVecAt` the primitive and keep `compLenVec s hmono q` as the
derived form), then the reordering happens once, at the definition, instead of at thirteen lemmas.
That is a larger but single edit, and it is the one I recommend before A5.

State: nothing in the library was touched for this; `./Build.sh` is green with `sorryAx: 3`.

### `compLenVec` re-interfaced; `hue` now carries `2 ≤ l - k` (landed)

1. **`compLenVec` is now the pointwise primitive** (`Section3Presentation`):
```lean
noncomputable def compLenVec (s : Fin (n + 1) → ParamAffine d e) (q : PReal d e)
    (hmono : StrictMono fun k => s k q) : Fin n → ℝ≥0 := fun i => compLen hmono i
```
and the old global form is `compLenVecOf`, with
`compLenVec_eq_compLenVecOf : compLenVec s q (hmono q) = compLenVecOf s hmono q := rfl`.
Everything downstream migrated by the bare-identifier rename `compLenVec ↦ compLenVecOf` (102 occurrences,
7 files) and still compiles unchanged — so the re-interface is backward compatible, and new lemmas can
now take a pointwise `hmono` without a global one.
2. **A4's `hue` and `hrig` carry `2 ≤ l - k`** (m3's finding: at `l - k = 1` the block exchange is the
identity and `UniqueErgodic` is *false*; `IsRigidByTranslations` is true there, so the arrow on `hrig` is
only for uniformity with `BlockData.BlockGoodAt`, which has it outside the conjunction).  The `≥ 2` branch
of A4 supplies it by `omega`.

`./Build.sh`: all `ok`, `declarations still depending on sorryAx: 3`.

### The last step to A5 (one refactor, then pure substitution)

`GoodRegion.datum` is the node that forces every lemma above it to carry a *global* `hmono`: it is built as
`IETDatum.ofMem G.ρ (G.compLenAffine_mem_region hreg hmono hn1 hq)`.  m2's
`compLenAffine_mem_regionAt (G) (hq) (hmono : StrictMono fun k => G.s k q) (hn1)` builds the same region
membership from the *pointwise* `hmono`, and `monoAt G hq` supplies that.  So:
1. rebuild `datum` with `compLenAffine_mem_regionAt hq (monoAt G hq) hn1` — `datum` then needs no `hmono`;
2. `datum_lam` becomes `(G.datum hreg hq).lam = compLenVec G.s q (monoAt G hq)` (via m2's
   `compLenVecAt_eq_simplexMap`), and `datum_markCuts`, `datum_toFun` follow;
3. `comp_eq_toFun`, `blockPermOf`, `irreduciblePerm_blockPerm`, `isIrreduciblePerm_blockPermOf` then lose
   `hmono` as well (their only use of it was `datum`), and `blockRescaled`, `comp_conj_rescale`,
   `restrict_rescale`, `isDiophantine_blockPair`, `exists_word_trivial_of_region` take the pointwise
   `hmono : StrictMono fun k => G.s k q` with `compLenVec G.s q hmono`;
4. A5 is then `filter_upwards [BlockData.exists_ae_block_good π σ hMV hVR]`, pick the region containing
   `z` from the cover, and apply `exists_word_trivial_of_region` with `hmono := monoAt (G i).2 hz`,
   `hue`/`hrig` from `BlockGoodAt`, `hdio := isDiophantine_blockPair …`.
Because `compLenVecOf G.s hmono q` and `compLenVec G.s q hmono` are `rfl`-equal, each proof above needs
only the binder moved (`{q} (hq)` before `hmono`) — no mathematical changes.

### The pointwise layer is now *below* the datum chain (landed)

`monoAt` and `compLenAffine_mem_regionAt` have been **moved from `Section3BlockData` to
`Section3LengthMap`**, next to `compLenAffine_mem_region` and `compLen_check_eq_simplexMap`.  This was the
prerequisite identified last round: the datum chain lives in `Section3Reduction`, which is built
*before* `Section3BlockData`, so it could not see the pointwise lemmas; moving them down removes the
module-ordering blocker.  `monoAt` had to be reproved on the way — it used `G.s_mono`, which is defined
in `Section3Block` (later), and now goes through `(G.pres q hq …).mono` directly, which is available in
`Section3LengthMap`.

Both files compile, and so does the whole chain after the move: `./Build.sh` all `ok`,
`declarations still depending on sorryAx: 3`.

**What is still needed for A5** (the datum migration proper, now unblocked): `datum` can drop `hmono`
from its *body* (one line, using `compLenAffine_mem_regionAt hq (monoAt G hq) hn1`), but its *statement*
and `datum_lam`/`datum_toFun`/`datum_markCuts`/`comp_eq_toFun`/`blockPermOf`/`irreduciblePerm_blockPerm`
keep `hmono` in their conclusions through `compLenVecOf G.s hmono q`.  Since `compLenVecOf G.s hmono q`
and `compLenVec G.s q (monoAt G hq)` are propositionally equal only through proof irrelevance of
`StrictMono` (not syntactically), each of those statements must be restated with the pointwise form and
its proof adjusted — `datum_lam` via m2's `compLenVecAt_eq_simplexMap`, the rest by composition.  Then
`blockRescaled`/`comp_conj_rescale`/`restrict_rescale`/`isDiophantine_blockPair`/
`exists_word_trivial_of_region` take `hmono : StrictMono fun k => G.s k q` and `A5` follows by
`filter_upwards` with `BlockData.exists_ae_block_good`.

### Lemma 3.4 is closed: `sorryAx: 2` (frozen `Challenge` only)

`./Build.sh` (all `ok`, `Tasks/Match.lean` ok): **`declarations still depending on sorryAx: 2`** —
`Challenge.lean:61` (`mkIETFun_inv_left`) and `Challenge.lean:103` (`main`), both frozen.
`Section3Reduction.lean` has **no `sorry`**, and `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for `exists_word_trivial_on_block`,
`exists_word_trivial_on_all_of_blocks` and `main_theorem_of_blocks`.

**1. The layering had to be inverted first.** `exists_word_trivial_on_block` (Lemma 3.4) lives in
`Section3Reduction`, but its only possible proof consumes `BlockData.exists_ae_block_good` (A3),
which was in `Section3BlockData` — a module that *imported* `Section3Reduction`. That import was
incidental: `Section3BlockData` compiles unchanged with
`import IETFree.Section3BlockAE` + `import IETFree.Section3BlockDioph` instead (verified before
touching anything). So the order is now `… Section3BlockDioph → Section3BlockData →
Section3Reduction → Section3 → Check` (module loop in `Build.sh` reordered; `Section3.lean` imports
reordered; the `cat` list of per-module logs already had `Section3BlockData` before
`Section3Reduction`). Consequences: A3 sits *below* the datum chain, and `Section3Reduction` may use
`BlockData.compLenVecAt*`, `BlockData.BlockGoodAt`, `BlockData.neZeroN`.

**2. The `hmono` migration (the real work) is done in place.** All 18 occurrences of the global
`(hmono : ∀ q, StrictMono fun k => G.s k q)` binder are gone. Every lemma of the chain already had
`(hq : q ∈ G.O)`, so the substitutions were `compLenVecOf G.s hmono q ↦ compLenVec G.s q (monoAt G hq)`,
`compLenVec_pos G hmono q ↦ compLenVec_pos G hq`, `hmono q hi ↦ monoAt G hq hi`, and each call
`G.<lemma> … hmono hq … ↦ G.<lemma> … hq …`. No binder had to be reordered: `monoAt G hq` is
recovered from `hq`, so the pointwise proof never had to become global.
* Restated pointwise, same names: `GoodRegion.compLenVec_pos` (now `{q} (hq) (i)`),
  `GoodRegion.compLenVec_sum` (now `{q} (hq) (hl) (hm)`), and — in `Section3BlockDioph` —
  `compLenVec_coe_eq` (now `{q} (hq) (i)`, conclusion `((compLenVec G.s q (monoAt G hq) i : ℝ≥0) : ℝ) = …`).
* `GoodRegion.datum` and `GoodRegion.datum_lam` lost **both** `hreg` and `hmono`: the body is now
  `IETDatum.ofMem G.ρ (compLenAffine_mem_regionAt G hq (monoAt G hq) (by have := NeZero.ne G.n; omega))`,
  and `datum_lam` concludes `= compLenVec G.s q (monoAt G hq)` via
  `BlockData.compLenVecAt_eq_simplexMap`. `hreg` stays in the other `datum_*` lemmas (still used).
  `ae_irreduciblePerm_blockPerm` lost its `hmono` telescope entry.
* `compLenVec` (the primitive of `Section3Presentation`) and `BlockData.compLenVecAt` are the *same
  function* (`fun i => compLen hmono i`), so the two families are interchangeable by `exact`
  (defeq, no rewrite lemma needed); `BlockData.compLenVecAt_pos` and `GoodRegion.compLenVec_pos`
  likewise. `BlockData.compLenVecAt` was left in place rather than de-duplicated.
* **A2 and A4 had to stop using the region's base point.** They were stated `(G : GoodRegion d e π σ q)`
  with `q` serving both as `G`'s base point and as the evaluation point, so they could only be applied
  at the base — useless for A5, where the a.e. statement is read at an arbitrary `z ∈ O`. Both are
  now `(G : GoodRegion d e π σ q₀) {q : PReal d e} (hq : q ∈ G.O)`, i.e. `hq` is a real hypothesis.
  The proofs needed no change (they only ever use `G.pres q hq`, `G.subset_region q hq`,
  `G.block_endpoints hq …`, `G.exists_isIntAffine_mu' hq`). This is a strict generalization, not a
  weakening.
* A4's `hue`/`hrig` keep `[NeZero (l - k)]` as an instance binder — an explicit `fun … (hne : NeZero (l-k)) …`
  lambda still typechecks against it, so nothing had to be re-threaded there.

**3. The two sorry theorems moved to the end of `Section3Reduction`, verbatim.** A5 and
`main_theorem_of_blocks` (which consumes it) were above the A4/A2 section, so with the `sorry` gone
they could not elaborate there. Both blocks were moved to the end of the file (after `end GoodRegion`)
with their statements **byte-identical** (checked by `diff` of the `theorem … := by` prefixes against
the pre-change file); no new module, so both `Build.sh` lists stay as they are.

**4. The proof of A5** (13 lines, in place of `sorry`):
`obtain ⟨ι, hι, Gfam, hcov, hae⟩ := BlockData.exists_ae_block_good π σ hMV hVR`, `haveI := hι`,
`filter_upwards [hae]`, split the five conjuncts, `intro D E hDπ hEπ hDv hEv` (**note the order**:
the statement is `D.π = π → E.π = σ → D.v = z.1 → E.v = z.2`), `obtain ⟨i, hzO⟩ := hcov z hbad hz1 hz2`
(`goodParams d e = {q | ¬ IsBadParam q}`, so `hbad` is used directly), then
`GoodRegion.exists_word_trivial_of_region (G := (Gfam i).2) hzO hbad` with
`hue := fun k l hkl hln hne hstab hirr h2 h => (hblk i hzO k l hkl hln hne hstab hirr h2).1 h`,
the same for `hrig` with `.2`, and `hdio := fun i₀ i₁ hi => GoodRegion.isDiophantine_blockPair hzO hi hdio`.
The three fields match `BlockGoodAt` definitionally (`BlockGood`'s explicit `hne`, `compLenVec` vs
`compLenVecAt`, `compLenVec_pos` vs `compLenVecAt_pos`), so `exact` closes each.

**What is left.** Only the two frozen `Challenge` statements. Theorem 1.1 is now proved *up to* the
frozen `main`, which is the paper's statement in its own interface; nothing in the library depends on
a `sorry` any more.

### The weak challenge: display files `Challenge`/`ChallengeWeak`, solution `ChallengeWeakSolved`

`Challenge.lean` is unprovable in this development by design: its `main` has *no* hypothesis, so any
proof must contain Masur–Veech and Veech's rigidity.  `ChallengeWeak.lean` states the same conclusion
from those two inputs, and `ChallengeWeakSolved.lean` proves it from the library.  The three files are
arranged so that the solution is genuinely axiom-free:

* `IETFree/Challenge.lean` (frozen) and `IETFree/ChallengeWeak.lean` — **display only**: they import
  only `Mathlib`, *nothing imports them*, and their `sorry`s are statements, not gaps
  (`ChallengeWeak` has two: `mkIETFun_inv_left`, which only builds the `Equiv` packaging and is
  proved in `IET.lean`, and `main`).  `ChallengeWeak` copies the exchange API of `Challenge.lean`
  verbatim and adds `MasurVeech`/`VeechRigidity`, stated for the *map* `mkIETFun ν τ 0` (unique
  ergodicity and rigidity are properties of the self-map of `ℝ`; the `Equiv` packaging is needed only
  in the conclusion, where a word is evaluated in the group of permutations), with the two notions of
  Definitions 2.1/2.2 stated for `ℝ → ℝ` and iterated by `Function.iterate`.
* `IETFree/ChallengeWeakSolved.lean` — **imports `IETFree.Section3Reduction` only** (not the display
  files) and proves the theorem, restated in the library's names: nothing had to be copied, since
  every notion of the display file is library API.  Its `#print axioms` lines report
  `[propext, Classical.choice, Quot.sound]` for every declaration, `main` included.

The correspondence is verbatim (same definitions, occasionally another name): `mkIETFun`,
`imageLengths`, `mkIETEquiv`, `simplexRegion`, `simplexMap`, `simplexVolume`, `IsIrreduciblePerm`,
`UniqueErgodic`, `IsRigidByTranslations`, `MasurVeech`, `VeechRigidity` are the same constants; the
display file's `evalWord` on `Equiv ℝ ℝ` is the library's `evalWordEquiv`; and the display file
iterates by `Function.iterate` where the library iterates in the group `IET 0 1`
(`IET.pow_apply_iterate : (f ^ n) x = f^[n] x` is the bridge, not needed in the solution because both
sides of the theorem are the library's).

**Why the display files are not imported.**  `#print axioms` traverses the *type* as well as the
value, and the `sorry` on `mkIETFun_inv_left` sits inside the definition of `mkIETEquiv` and hence
inside the display file's `mainStatement`.  As long as the solution mentions those constants, its
`main` inherits `sorryAx` (= the earlier arrangement); importing nothing from the display files
removes the constant and every report is clean.  (Checked separately:
`def f : ℕ := sorry; theorem h : f = f := rfl` reports `sorryAx`.)

**The proof of the theorem.**  `exists_word_ae` is Lemma 3.4 at almost every length vector, for
`IETDatum`s: `main_theorem_of_blocks` (A5, from the a.e. block data of
`BlockData.exists_ae_block_good`) produces the blocks and a word trivial on each, and
`exists_word_trivial_on_all_of_blocks` assembles them into one nontrivial word trivial on `[0, 1)`.
`main` repackages it into the permutations `mkIETEquiv p_i π 0` by `evalWord_toEquiv_eq_one`, using
`simplexMap d (toReal p).1 = p.1` for a.e. `p`.

**The transfer `ae_prod_of_ae_free` is the reusable part** (the frozen `Challenge.main` would need it
too): `(simplexVolume d).prod (simplexVolume e)` is the pushforward of the product of Lebesgue
measures on the two free regions under `prodSimplexMap` (`Measure.map_prod_map`), and the *forward*
pushforward of an almost-sure statement needs measurability of the predicate — which the conclusion of
Lemma 3.4 (an existential over words, equality of functions) does not have.  The way out: pull back
along `toReal` instead.  `(((ν).map prodSimplexMap).map toReal) = ν` because `toReal` inverts
`simplexMap` on the region (`toReal_simplexMap`), so `MeasureTheory.ae_of_ae_map` gives the statement
for a.e. `p` in the form `P (prodSimplexMap (toReal p))`; and `prodSimplexMap (toReal p) = p` for a.e.
`p` (`ae_toReal_simplexMap`, whose fixed-point set is the preimage under a *continuous* map of the
diagonal, hence measurable, and whose complement is contained in the null set `(region)ᶜ` — this is
`Measure.prod_restrict` + `restrict_apply`).  No measurability of `P` is ever used.  (`Prod.map` is
`implicit_reducible` in core Lean, so it is not unfolded by `rw`; `prodSimplexMap` is a plain lambda
for that reason.)

**Build.**  `Build.sh` compiles all three files (they need only `Mathlib`, resp. `Section3Reduction`)
and its report now reads
```
declarations still depending on sorryAx: 4
  of which display-only statement files (Challenge, ChallengeWeak): 4
  of which the library (with ChallengeWeakSolved): 0
```
`IETFree.lean` (the root module) and `Check.lean` import none of the three.

### File layout: no more `Section3` in file names; four files split

The paper's Section 3 development is now named after its subject.  **Earlier entries of this file
refer to the old names**; the correspondence is:

| old | new | subject |
|---|---|---|
| `Section3Setup` | `ReductionData` | blocks, pair-splitting singularities, the good set `O`, the covering step |
| `Section3Presentation` | `Presentation` | `IsCompPresentation` of `g ∘ f`, `IsCompType`, `compLen`, the affine cuts |
| (its second half) | `IntegerAffine` | integer-affine functions of the parameters, sign constancy, truncation |
| `Section3Singularities` | `SingularityList` | the marked list `s`, `markedPos` |
| `Section3Region` | `GoodRegion` | the image side, partial sums, `GoodRegion`, `ae_exists_goodRegion` |
| `Section3LengthMap` | `LengthMap` | Lemma 3.1 |
| `Section3Transport` | `SubintervalTransfer` | null sets pull back under the rescaling to a sub-interval |
| `Section3BlockWord` | `BlockRescaling` (+ `GeneratorChange`) | rescaling to an invariant interval, `blockLam`/`blockPerm`/`mkIET1_rescale_subinterval`; the change of generators and the transport of a word |
| `Section3Restrict` | `InvariantInterval` | the restriction of `g` to an invariant interval, same permutation |
| `Section3Block` | `BlockEndpoints` | the shape of the list, the block endpoints, `paramMeasure`, the countable cover |
| `Section3BlockAE` | `BlockAETransfer` | Masur–Veech and Veech to the rescaled block |
| `Section3BlockDioph` | `BlockDiophantine` | the integer-affine data of a block, the Diophantine transfer |
| `Section3BlockData` | `BlockData` | A3, the a.e. block data over the cover |
| `Section3Reduction` | `BlockIrreducibility` + `BlockAssembly` + `BlockDatum` + `BlockLemma` | Lemma 3.2; the per-block words assembled into one; the datum/invariance/rescaled composition; Lemma 3.4 and Theorem 1.1 |
| `Section3` | `Reduction` | the umbrella module, with the narrative docstring |
| `IET` (2211 lines) | `CutSet` + `CutSetMeasure` + `IET` | cut sets and cells; measure preservation and the local structure; `IsIET`, the explicit construction, the classification, the group |

Every file is now under 1500 lines (`IET` 2211 → 652/583/1024; `Section3Reduction` 2648 →
1195/218/937/367; `Section3BlockWord` 1537 → 1409/136; `Section3Presentation` 1519 → 1085/457), and
each has a module docstring stating its subject.  Two pieces moved to where they belong: the
evaluation of a word in two permutations of `ℝ` (`evalWordEquiv`, `evalWord_toEquiv`,
`freeGroup_lift_natural`) from the block file to `MeasureTools`, next to `evalWord`; and the
`exists_isIntAffine_mu'`/`IsIntAffine` clientele of `BlockDiophantine` now imports `IntegerAffine`
explicitly rather than getting it through `Presentation`.

`Build.sh` (module loop and the `cat` list of logs — kept in step, and verified to be exactly the set
of files), `IETFree.lean` (root module, with the list of modules), `Reduction.lean` (umbrella) and
`Check.lean` were all updated.  Build green: `declarations still depending on sorryAx: 4`, all four
in the display-only statement files, none in the library.

### Naming and docstring pass

Theorems/lemmas were audited against the naming rules: snake_case throughout (camelCase only as the
name of the definition a lemma is about), UpperCamelCase for structures and types, lowerCamelCase for
data, dot notation into the most specific namespace.  All seven prime-suffixed names are gone —
`simplexMap_mem_simplex'` → `simplexMap_mem_simplex_fin`, `exists_isIntAffine_mu'` →
`exists_isIntAffine_truncatedLengths`, `mkIETFun_sub_eq_sum'` → `mkIETFun_sub_eq_lattice`,
`coeffs_zero_of_good'` → `coeffs_zero_of_good_with_const`, the two `ae_*_blockLam'` →
`ae_*_blockLam_of_compLenVec_pos`, and `invRev_cons'` deleted (it was Mathlib's
`FreeGroup.invRev_cons` plus `invRev_singleton`, and unused).

Assumptions: every declaration-level hypothesis is a binder.  The one exception,
`cutSep_mono_ioc : … : CutSep S x z → CutSep S x y`, now takes `(h : CutSep S x z)`.  What remains to
the right of a colon is not a hypothesis of the declaration but a condition on a bound variable
(`∀ x ∈ s`, `MapsTo`-shaped conditions, `∀ y y', ¬ CutSep … → …`), an a.e. predicate that mentions
the point (`∀ᵐ x ∂μ, x ∈ O → p x`), or the inner telescoping `∀ᵐ z, ∀ D E, D.π = π → …` of the a.e.
theorems; converting the last to binders makes Lean's `unusedVariables` linter fire, because the
hypothesis does not occur in the conclusion, which is why Mathlib writes this shape with arrows.

Docstrings and comments: no `Section3` name is left in the sources (the remaining "Section 3" are
references to the *paper's* section), no reference to the deleted module `BlockReduction` or to the
old declaration names, and every backticked name in a docstring resolves.  Fixed along the way: the
`evalWordEquiv`/`evalWord_toEquiv` clause of `BlockRescaling` (they moved to `MeasureTools`), the
`paramMeasure` bullet of `BlockData` (it lives in `BlockEndpoints`), `no_cut_inside_image` →
`no_cut_inside_markedCell`, `volume_rescaleSub_preimage_null` →
`absolutelyContinuous_map_rescaleSub`, `exists_compPresentation_on_region` →
`exists_compPresentation_on_ball`, `block_invariant_irreducible` and `mkIET` (both gone) replaced by
the lemmas that exist, the leftover task labels `T2:`/`T5:` in `BlockDiophantine`, "Lemma 2.7 … still
`sorry`" in `Centralizer`, and "`import IETFree` pulls in everything" in the root module.
`IET.pow_apply_iterate` (group power = iterate) was added to `IET.lean`, since two docstrings refer to
it and it had gone with the earlier version of the challenge solution.

## Audit of the repeated arguments: items 1 and 2 (this session)

The audit of the arguments repeated across the Section 3 development found five groups; the person
asked for items 1 and 2 first, then a rebuild and the `sorry` count before items 3–5.  This entry
records what was landed.

### Item 1 — the derivable and the dead hypotheses

**(a) `hreg`.**  All 24 hypotheses of the form
`(hreg : ∀ q ∈ G.O, q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e)` are gone: 5 from `LengthMap`
(the previous session), 7 from `BlockAETransfer`, 1 from `BlockEndpoints`, 11 from `BlockDatum`.
Every use was either an argument passed to another lemma or `hreg q hq`, now `G.subset_region q hq`.
The three kinds of `hreg` that are *not* derivable are kept: those over a raw `O`
(`BlockDiophantine`, `LengthMap.compLen_injective`), and the pointwise
`(hreg : q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e)` of `GoodRegion.markedImage_gf` and
`SingularityList.markedPos_spec`.

**(b) `hl` / `hm`.**  The two simplex memberships are derived wherever the point of a `GoodRegion`
is known, through two new lemmas in `GoodRegion.lean`:

```lean
theorem GoodRegion.simplexMap_mem_simplex_fst (G) (hq : q ∈ G.O) : simplexMap d q.1 ∈ simplex d
theorem GoodRegion.simplexMap_mem_simplex_snd (G) (hq : q ∈ G.O) : simplexMap e q.2 ∈ simplex e
```

and, for the two places where a whole hypothesis *is* the presentation at a point,

```lean
theorem GoodRegion.presAt (G) (hq : q ∈ G.O) :
  IsCompPresentation (simplexMap d q.1) π (simplexMap e q.2) σ
    (G.simplexMap_mem_simplex_fst hq) (G.simplexMap_mem_simplex_snd hq) G.n (fun k => G.s k q) G.ρ
theorem GoodRegion.typeAt (G) (hq : q ∈ G.O) : IsCompType (simplexMap d q.1) π _ (simplexMap e q.2) …
```

`presAt`/`typeAt` replace every `G.pres q hq hl hm` / `G.type q hq hl hm`, which was the reason those
two hypotheses were threaded through the whole block development.  The binders deleted, by file:
`BlockEndpoints` 5 (`s_zero`, `s_last`, `s_mono`, `mem_cutF`, `mem_cutList`), `BlockDatum` 10
(`datum_hcuts`, `datum_toFun`, `irreducibleOn_datum`, `comp_eq_toFun`, `blockPermOf`,
`irreduciblePerm_blockPerm`, `isIrreduciblePerm_blockPermOf`, `blockRescaled`, `comp_conj_rescale`,
`restrict_rescale`) plus the `ae_irreduciblePerm_blockPerm` telescope, `BlockLemma` 1
(`exists_word_trivial_of_region`, so A4 and the final assembly no longer pass them),
`Presentation` 2 (`exists_lt_imageLeft_simplexMap`, `preimageCutAffine_eq`, from their `hr`),
`SingularityList` 3 (`singAffine_injective`, `preimageCutAffine_mem`, `markedPos_spec`, from their
`hr`/`hreg`), `GoodRegion` 1 (`markedImage_gf`).

**(c) Dead `_`-named arguments.**  `_hEπ` (`datum_hcuts`), `_hperm` (`mem_markD`), `_hl` in
`imageLeft_add_le_of_invariant` and in the three `RescaleBlock` wrappers, `_hstab` in
`idx_rescaleMap_aux` and the wrappers, `_hm` in the `GoodRegion.type` field and in
`compLen_injective`'s `htype`, `_hm` in `datum_hcuts`.  Three `{π : Equiv.Perm (Fin n)}` variables
that had become unreferenced (`idx_rescaleMap_aux`, `RescaleBlock.leftEnd_blockLam`,
`RescaleBlock.idx_rescaleMap`) are gone with them.

**What item 1 did *not* reach.**  The remaining `hl`/`hm` are all *nested inside a hypothesis or a
structure field*, not declaration-level: `SingularityShape.posG_pre`, the `hpre`/`hF`/`htransl`
hypotheses of `exists_compPresentation_on_ball`, `partialSum_image`, `SingularityList`'s
`exists_...` conclusions, `GoodRegion`'s nested ∃ at 880/898, and the fields
`GoodRegion.pres`/`GoodRegion.type` themselves.  Removing those means either rewriting those
hypotheses to carry a pointwise `q.1 ∈ simplexRegion d` instead (so the memberships are derivable
inside), or making `pres`/`type` refer to the `subset_region` field — the dependent-field route was
not attempted.  `partialSum_image`'s own `(hl) (hm)` are *not* derivable: its only hypothesis on the
point is membership in a ball.

### Item 2 — `GoodRegion.cellLen` and `GoodRegion.blockLam`

`BlockEndpoints` now carries, next to the block-length API,

```lean
noncomputable def GoodRegion.cellLen (G) (hq : q ∈ G.O) : Fin G.n → ℝ≥0 :=
  compLenVec G.s q (monoAt G hq)
theorem GoodRegion.cellLen_pos (G) (hq) (i) : 0 < G.cellLen hq i
theorem GoodRegion.cellLen_sum (G) [NeZero G.n] (hq) : (∑ i, G.cellLen hq i) = 1
noncomputable def GoodRegion.blockLam (G) (hq) (k : ℕ) {l : ℕ} (hkl : k < l) (hln : l ≤ G.n) :
    Fin (l - k) → ℝ≥0 :=
  _root_.blockLam (G.cellLen hq) k hkl hln (G.cellLen_pos hq)
theorem GoodRegion.blockLam_def / blockLam_apply / blockLam_sum / blockLam_coe
```

The home is `BlockEndpoints` rather than `BlockData` because `BlockDiophantine` (which imports
`BlockEndpoints`) uses `cellLen` and cannot import `BlockData`.  `blockLam_def` is `@[simp]` and is
what makes `G.blockLam` usable inside dependent positions (`simp only [GoodRegion.blockLam_def]`
closes the `rfl`-identification in `comp_conj_rescale`, where `rw` fails with "motive is not type
correct").

All 36 occurrences of `blockLam (compLenVec G.s q (monoAt G hq)) k hkl hln (compLenVec_pos G hq)`
became `G.blockLam hq k hkl hln`, and `compLenVec G.s q (monoAt G hq)` became `G.cellLen hq`
everywhere.  `GoodRegion.compLenVec_pos` and `GoodRegion.compLenVec_sum` (in `BlockDatum`) were then
redundant and are deleted, with `Check.lean` reporting `cellLen_pos`/`cellLen_sum` in their place.
A4's statement (`exists_word_trivial_of_region`) and the three `hdio`/`hue`/`hrig` hypotheses went
from three lines each to one.

Note that `GoodRegion.blockLam` shadows the root `blockLam` inside `namespace GoodRegion`; the two
remaining uses of the root one in such a scope (`GoodRegion.blockLam_of_one`'s body and
`isDiophantine_blockLam`'s two statements, which are about `compLenVecOf`) are qualified
`_root_.blockLam`.

### State

`./Build.sh` green, no warnings, and

```
declarations still depending on sorryAx: 4
  of which display-only statement files (Challenge, ChallengeWeak): 4
  of which the library (with ChallengeWeakSolved): 0
```

Items 3–5 are untouched: `BlockIdx`/`Block` structures, `Fits`, retiring `compLenVecOf` and the
global-`hmono` API, unifying `∑ lam = 1` on `lam ∈ simplex`, and thinning the duplicate families
(`compLenVec_pos`/`compLenVecAt_pos`, the six `ae_*_blockLam*`, the `leftEnd`/`upperEnd` bounds, the
three `*_congr`).  The `RescaleBlock` wrappers `leftEnd_blockLam`, `imageLeft_blockPerm` and
`idx_rescaleMap` have no remaining users and are candidates for deletion there.

## Audit item 3: the block and the fitting data are structures (this session)

Item 3 of the audit was the tuple `(k, l, hkl, hln, hstab)` and the tuple
`(D.π = π, D.v = q.1, E.π = σ, E.v = q.2)`.  Both are now structures, and every live statement that
carried them mentions them once.

### The structures

In `GoodRegion.lean`, right after `GoodRegion` itself:

```lean
structure GoodRegion.BlockIdx (G : GoodRegion d e π σ q₀) where
  k : ℕ
  l : ℕ
  hkl : k < l
  hln : l ≤ G.n

structure GoodRegion.Block (G) extends BlockIdx G where
  hstab : ∀ i : Fin G.n, (i.val < toIdx.k ↔ (G.ρ i).val < toIdx.k) ∧ …
```

with the instance `BlockIdx.instNeZeroLen : NeZero (I.l - I.k)` (so `mkIET1` and `simplex` apply to
a block without a side condition), and
`Block.countable : Countable (Block G)` — the indices determine the block, since the bounds and the
invariance are propositions.  `Countable` is what turns "every block" into a countable intersection
through `MeasureTheory.ae_all_iff`, which is why `ae_blockGood_range` (the `Finset.range`
enumeration, with its case splits on `k < l` and `l ≤ G.n`) is gone: `ae_blockGood` states
`∀ᵐ q, ∀ B : Block G, …` directly.

The rest of the API lives where its ingredients do: `BlockIdx.lam`, `BlockIdx.lam_sum`,
`Block.perm` in `BlockEndpoints` (they need `G.blockLam`, and
`BlockRescaling` — which has `blockPerm` — does not import `GoodRegion`).

`GoodRegion.Fits` is the second structure:

```lean
structure GoodRegion.Fits (G) (q : PReal d e) (D : IETDatum d) (E : IETDatum e) : Prop where
  hDπ : D.π = π
  hDv : D.v = q.1
  hEπ : E.π = σ
  hEv : E.v = q.2
```

### What the conversion changed

* `BlockData`: `ae_blockGood_free` now takes `(B : Block G)` and
  `(hirr : IsIrreduciblePerm B.perm)`; `ae_blockGood` replaces `ae_blockGood_allStab` and
  `ae_blockGood_range`; `BlockGoodAt` is
  `∀ B : Block G, IsIrreduciblePerm B.perm → 2 ≤ B.l - B.k → BlockGood (B.lam hq) B.perm`, and
  `ae_BlockGoodPt` is its a.e. form.
* `BlockLemma`: A4's `hue`/`hrig` are `∀ B : Block G, IsIrreduciblePerm B.perm → 2 ≤ B.l - B.k →
  ∀ h : B.lam hq ∈ simplex (B.l - B.k), …` — six binders each became one — and A4 takes
  `(h : G.Fits q D E)`.  A5 passes `fun B hirr h2 h => (hblk i hzO B hirr h2).1 h` instead of
  unpacking seven arguments.
* `BlockDatum`: the eleven declarations that carried the four data equalities take
  `(h : G.Fits q D E)`; `ae_irreduciblePerm_blockPerm`'s telescope went from six items to three.
  `GoodRegion.blockOf` is new — the `Block` of a pair of data whose ends are pair-splitting — and
  `blockPermOf` is now `(G.blockOf …).perm`, one definitional equation away from `Block.perm`, so
  that `IsIrreduciblePerm (G.blockOf …).perm` and `IsIrreduciblePerm (blockPermOf …)` are cheap to
  identify.  `isIrreduciblePerm_blockPermOf` and `ae_irreduciblePerm_blockPerm` conclude in the
  `blockOf` form for that reason.

### A trap worth recording

`have B : Block G := …` makes `B` an *opaque* local hypothesis: `B.l` does not reduce to `l`, and
`2 ≤ B.l - B.k` is not defeq to `2 ≤ l - k` from such a `have`.  `let B : Block G := …` does
reduce, and that is what A4 uses for its block (`let hB : Block G := G.blockOf …`).  The check
`IsIrreduciblePerm X` against `IsIrreduciblePerm Y` with `X ≠ Y` syntactically unfolds `X` and `Y`
to `Equiv.Perm` structures; with `blockPerm` in the way that exhausted the 1M heartbeat budget, which
is why `blockPermOf` was rebased on `Block.perm`.

### What is left of the tuple

The 6 remaining `hstab` binders and the 10 remaining `(hkl : k < l) (hln : l ≤ G.n)` pairs are the
*library* API, not the assembly: the four `ae_*_blockLam*` theorems of `BlockAETransfer`, which are
stated with the global `hmono : ∀ q, StrictMono fun k => G.s k q` and are **unused** (the a.e. data
reaches the assembly through `BlockGoodAt` now); `GoodRegion.isDiophantine_blockLam`, also unused;
`G.rescaleSub_compLenAffine`, also unused; and the ℕ-indexed primitives `G.blockLam`,
`blockMass`, `blockLamAt_eq`.  Retiring those is item 4 (drop the global `hmono` and `compLenVecOf`)
and item 5 (thin the duplicate families), so they were left alone here.

### State

`./Build.sh` green, no warnings:

```
declarations still depending on sorryAx: 4
  of which display-only statement files (Challenge, ChallengeWeak): 4
  of which the library (with ChallengeWeakSolved): 0
```

`Check.lean` gained axiom lines for `ae_blockGood_free`, `ae_blockGood`, `ae_BlockGoodPt`,
`Block.countable`, `BlockIdx.lam_sum` and `blockOf`.

## Audit item 4: `compLenVecOf` and the global `hmono` are gone (this session)

Item 4 was "retire `compLenVecOf` + the global-`hmono` API".  The audit had measured the global form
at 34 occurrences in `BlockAETransfer`, 28 in `BlockDiophantine`, 19 in `LengthMap`, 8 in `BlockData`,
6 in `Presentation`, 4 in `BlockEndpoints`.  All of them are now gone: no Lean file in `IETFree/`
mentions `compLenVecOf`, and no declaration takes `hmono : ∀ q, StrictMono fun k => s k q`.

### What was deleted

The global form existed as a shadow library parallel to the pointwise one, and once items 1–3 had
moved the assembly onto the pointwise forms, none of it had a user.  24 declarations:

* `Presentation`: `compLenVecOf`, `compLenVec_eq_compLenVecOf`;
* `LengthMap`: `GoodRegion.compLen_eq_simplexMap`, `GoodRegion.compLenAffine_mem_region`,
  `GoodRegion.compLenAffine_absolutelyContinuous`, `GoodRegion.compLen_absolutelyContinuous`,
  `ae_of_ae_compLen` — the whole `hmono` half of the file;
* `BlockEndpoints`: `GoodRegion.rescaleSub_compLenAffine`;
* `BlockAETransfer`: the whole `Specialisations` section — `compLenVec_pos`, `blockLam_compLenVec_eq`,
  `mkIET1_congr`, and the six `ae_*_blockLam*` (`ae_uniqueErgodic_blockLam`,
  `ae_isRigidByTranslations_blockLam`, both `_of_compLenVec_pos` and both `_apply`);
* `BlockDiophantine`: `exists_isIntAffine_trunc`, `exists_isIntAffine_blockLen`, `pos_compLenVec`,
  `sum_compLenVec`, `isDiophantine_blockLam`;
* `BlockData`: `compLenVecAt_eq_compLenVec`, `compLenVec_eq_compLenVecAt` (the two bridges between
  the pointwise and the global vector, which are no longer two things).

Files: `LengthMap` 726 → 519 lines, `BlockAETransfer` 377 → 226, `BlockDiophantine` 1103 → 826,
`BlockEndpoints` 568 → 546, `BlockData` 441 → 431, `Presentation` 1087 → 1078.

### What replaced it

Nothing new was needed: the pointwise statements were all already there.

* injectivity of the length map: `compLen_injective` (unchanged);
* the pointwise monotonicity and simplex membership: `monoAt`, `compLenAffine_mem_regionAt`
  (`LengthMap`), `G.cellLen`, `G.cellLen_pos`, `G.cellLen_sum`, `G.blockLam`, `BlockIdx.lam`
  (`BlockEndpoints`);
* absolute continuity: `compLenAffine_absolutelyContinuousAt`, `compLen_absolutelyContinuousAt`
  (`BlockData`), consumed through `ae_of_ae_of_absolutelyContinuous` (`LengthMap`, kept: it is
  abstract and used by `BlockData`);
* the a.e. transfer to the block: `ae_block_of_ae_simplexVolume`, `ae_blockGood_free`, `ae_blockGood`
  (`BlockData`), i.e. `BlockGood` for all blocks at once, which is the conjunction of what
  `ae_uniqueErgodic_blockLam` and `ae_isRigidByTranslations_blockLam` gave for a single block;
* the Diophantine transfer: `IsDiophantine.of_intAffine_family` (`BlockDiophantine`) with
  `isDiophantine_blockPair` (`BlockLemma`) as the instantiation to a block.

Docstrings that pointed at the deleted names were updated (`LengthMap`'s module header and its
`3'.` section, `Presentation`'s `measurable_paramAffine`, `SubintervalTransfer`'s two mentions of
Lemma 3.1, `Reduction`'s module map, `BlockData`'s design note, `BlockDiophantine`'s and
`BlockAETransfer`'s module headers, `BlockEndpoints`' note on the parameter measure), and
`Check.lean` lost the nine `#print axioms` lines for deleted declarations.

### Dead code left for item 5

Removing the global half orphaned a few more declarations, which item 4 did not need to touch:

* `GoodRegion.rescaleSub_eq_blockLam` (`BlockEndpoints`) — its only user was
  `rescaleSub_compLenAffine`;
* `BlockAETransfer`'s `cellLen_eq_coe_simplexMap`, `blockMass_simplexMap`,
  `eq_of_forall_lt_last_eq_of_sum_eq` — the only user of the first two and of the last was the
  deleted `blockLam_compLenVec_eq`; `blockLam_eq_simplexMap_rescaleSub` is live (`blockLamAt_eq`);
* `BlockDiophantine`'s `sSum` family (`exists_sumForm_s`, `sSum`, `isIntAffine_sSum`,
  `sumForm_sSum`, `sSum_spec`) — its only user was `exists_isIntAffine_blockLen`;
* `compLenVecAt` (`BlockData`) is now definitionally the same as `compLenVec` (`Presentation`), since
  the global vector it was distinguished from is gone.

### State

`./Build.sh` green, no warnings:

```
declarations still depending on sorryAx: 4
  of which display-only statement files (Challenge, ChallengeWeak): 4
  of which the library (with ChallengeWeakSolved): 0
```

`Check.lean` has 322 axiom lines, none containing `sorryAx`.  Item 5 (thinning the duplicate
families, `BlockIdx`/`Fits` leftovers in the nested hypotheses) is untouched.

**Correction to the preceding list.**  `cellLen_eq_coe_simplexMap`, `blockMass_simplexMap` and
`eq_of_forall_lt_last_eq_of_sum_eq` are **not** dead: all three are used inside
`blockLam_eq_simplexMap_rescaleSub`, which is live through `blockLamAt_eq`.  The dead declarations
after item 4 are exactly `GoodRegion.rescaleSub_eq_blockLam` and `BlockDiophantine`'s `sSum` family
(`exists_sumForm_s`, `sSum`, `isIntAffine_sSum`, `sumForm_sSum`, `sSum_spec`), plus the
`compLenVecAt`/`compLenVec` duplication.

## Audit item 5: `Positive`, and thinning the duplicates (this session)

Item 5 had three parts — "unify `(∑ lam = 1)` on `lam ∈ simplex`", a `Positive` definition, and
"thin duplicate families (`compLenVec_pos`/`compLenVecAt_pos`/`pos_compLenVec`, the six
`ae_*_blockLam*`, the `leftEnd`/`upperEnd` bound family, the three `*_congr`)".  Two of the three
are done; the first is declined, with the reasoning below.

### `Positive`

`IET.lean`, just before the frozen block (`leftEnd` … `mkIETEquiv`):

```lean
/-- **A length vector is positive** when all its coordinates are. -/
abbrev Positive {n : ℕ} (lam : Fin n → ℝ≥0) : Prop :=
  ∀ i, 0 < lam i
```

It is an `abbrev`, not a `def`, and that is load-bearing: `rw [blockLam_coe]` and
`rw [← NNReal.coe_sum, blockLam_sum, …]` stopped firing against a `def` (the rewrite's keyed matching
does not unfold a regular definition to match the positivity argument), and two proofs broke.  As an
`abbrev` it is reducible, and the same proofs go through unchanged.

24 hypotheses became `Positive` in six files: `BlockRescaling` 16 (`blockMass_pos`, `blockLam`,
`blockLam_coe`, `blockLam_sum`, `leftEnd_blockLam`, `idx_rescaleMap`, the four `RescaleBlock`
wrappers, `mkIET1_rescale_subinterval`, `blockLam_pos`, `leftEnd_lt_total`,
`leftEnd_pos_of_ne_zero`, `imageLeft_add_le_of_invariant`), `SingularityList` 2
(`leftEnd_lt_leftEnd`, `mem_mkIETCuts_one`), `BlockEndpoints` 3 (`mkIET1_inv_zero`, `blockLam_congr`
twice, `blockLam_eq_simplexMap_rescaleSub`'s `Positive (simplexMap n x)`), `BlockAETransfer` 1,
`InvariantInterval` 1, `BlockDatum` 1.

Not converted: the `(hpos : ∀ i, 0 < v i)` hypotheses whose `v : Fin p → ℝ` is a set of **free
coordinates** (`Presentation.simplexMap_mem_simplex_fin`, `Diophantine`'s `simplexMap_castSucc_coe`
and `sum_simplexMap_mul`, `ReductionData`'s `hv`/`hw`).  Those are half of the *region* hypothesis
`v ∈ simplexRegion` (`(∀ i, 0 < v i) ∧ ∑ < 1`), not the positivity of a length vector, and `Positive`
is stated for `Fin n → ℝ≥0`.

### Thinning

Deleted five declarations:

* `compLenVecAt` (`BlockData`) — definitionally identical to `compLenVec` now that the global
  `compLenVecOf` it was distinguished from is gone; the surviving uses are renamed, and
  `compLenVecAt_eq_simplexMap` is now `compLenVec_eq_simplexMap`;
* `compLenVecAt_pos` — dead once `G.cellLen_pos` existed (`compLenVec_pos` and `pos_compLenVec` went
  in items 2 and 4, so that family is now down to `compLenVec_pos`… which no longer exists either:
  the family is `G.cellLen_pos` alone);
* `BlockGood.congr_lam` — dead;
* `rescaleSub_eq_blockLam` (`BlockEndpoints`) — dead, its only user was `rescaleSub_compLenAffine`,
  deleted in item 4;
* `leftEnd_ne_leftEnd_of_good` (`Presentation`) — dead.

The six `ae_*_blockLam*` went in item 4, and of the three `*_congr` lemmas two are now gone
(`mkIET1_congr` in item 4, `BlockGood.congr_lam` here) with `blockLam_congr` live.

The `leftEnd`/`upperEnd` bound family is **not** dead: every member but `leftEnd_ne_leftEnd_of_good`
has at least one live user (`upperEnd_eq` 60 occurrences, `lt_upperEnd_idx` 31, `imageLeft_eq_leftEnd`
21, `leftEnd_nonneg` 15, `upperEnd_le_leftEnd` and `upperEnd_le_total` 16 each, …), and the
non-strict/strict pairs (`leftEnd_le_total`/`leftEnd_lt_total`, `leftEnd_le_leftEnd`/
`leftEnd_lt_leftEnd`) are both used.  There is nothing to thin there.

### Declined: `(∑ lam = 1)` versus `lam ∈ simplex`

`simplex d` is `{lam | ∑ i, lam i = 1}` (`Diophantine.lean`), so the two forms are *definitionally*
equal — this is a surface-syntax split, not a duplication of content.  Unifying on `simplex` would
mean

* moving `simplex` from `Diophantine.lean` to before `mkIET1` in `IET.lean` (a definition move);
* changing `mkIET1`'s own binder, the library's central construction;
* restating 39 hypotheses across 11 files;
* repairing the 21 proofs that consume the equation form syntactically (`exact_mod_cast hl`,
  `rw [← NNReal.coe_sum]; exact_mod_cast hl`, `hl.symm`, …) — a `Set` membership needs `simplex` and
  `Set.mem_setOf_eq` unfolded first, and `rw` does not do that by itself.

That is a large mechanical change to the central definition, with no gain in content.  The status quo
is also principled: the equation is what `mkIET1` and the length lemmas need, and `simplex` is used
where a *set* is genuinely required (`simplexVolume`, `BlockGood`'s `∀ h : lam ∈ simplex r`,
`G.blockLam … ∈ simplex (B.l - B.k)`).  Say the word if you want it unified anyway; it is a
mechanical job of a few hours.

### Found, not done: dead code and one dead route

A scan of every `theorem`/`lemma` whose short name occurs nowhere else in the sources (excluding the
two display-only files and `Check.lean`) lists **75 declarations**.  They are *unused*, not
duplicated, and pruning them is a judgement call, so nothing was deleted.  The complete list:

    BlockAETransfer.lean: ae_of_ae_map_of_measurable
    BlockData.lean: blockGoodPt_of_mem
    BlockDatum.lean: ae_irreduciblePerm_blockPerm
    BlockDatum.lean: mkIET1_fin_one
    BlockDiophantine.lean: sumForm_cutAffineRight
    BlockDiophantine.lean: sumForm_upperEndAffineRight
    BlockDiophantine.lean: sumForm_imageLeftAffine
    BlockDiophantine.lean: le_or_le_of_sumForm
    BlockDiophantine.lean: isIntAffine_upperEndAffineRight
    BlockDiophantine.lean: isIntAffine_sSum
    BlockDiophantine.lean: sumForm_sSum
    BlockDiophantine.lean: sSum_spec
    BlockDiophantine.lean: isIntAffine_gLenAffine
    BlockDiophantine.lean: truncatedLengths_eq
    BlockEndpoints.lean: mkIET1_inv_one
    BlockEndpoints.lean: sum_blockLen_simplexMap
    BlockEndpoints.lean: cellLen_apply
    BlockEndpoints.lean: blockLam_apply
    BlockEndpoints.lean: lam_apply
    BlockEndpoints.lean: mass_def
    BlockEndpoints.lean: mass_pos
    BlockEndpoints.lean: perm_def
    BlockEndpoints.lean: paramMeasure_absolutelyContinuous
    BlockIrreducibility.lean: exists_isCutSet_comp
    BlockIrreducibility.lean: comp_mapsTo
    BlockIrreducibility.lean: exists_cut_below
    BlockIrreducibility.lean: mem_markCuts
    BlockIrreducibility.lean: ite_one_sub_ite_one_eq_zero
    BlockIrreducibility.lean: isBadParam_swap
    BlockRescaling.lean: rescaleFun_comp
    BlockRescaling.lean: evalWordEquiv_conj
    BlockRescaling.lean: mark_eq_markedList
    BlockRescaling.lean: listLeftEnd_sub
    BlockRescaling.lean: rho_convex_of_image_Ico
    BlockRescaling.lean: lamNat_of_le
    BlockRescaling.lean: imageLeft_blockPerm
    Centralizer.lean: invLetter_invLetter
    Centralizer.lean: invRev_singleton
    Centralizer.lean: isReduced_append_iff
    Centralizer.lean: isReduced_append
    Centralizer.lean: mk_ne_one_of_isReduced
    Commensurable.lean: take_length_flatten_replicate
    CutSet.lean: not_separated_iff
    Diophantine.lean: ae_mem_simplex
    GeneratorChange.lean: substGen_apply
    GoodRegion.lean: exists_ball_subset_goodParams
    IET.lean: exists_isCutSet_of
    IET.lean: IsCutSet.lengths_coe
    IET.lean: IsCutSet.cellStarts_eq
    IET.lean: IsCutSet.cell_eq
    IntegerAffine.lean: lt_or_gt_of_ne_of_convex_affine
    IntegerAffine.lean: exists_ball_isIntAffine_truncatedLength
    InvariantInterval.lean: clamp_le
    InvariantInterval.lean: le_clamp
    InvariantInterval.lean: clamp_mono
    InvariantInterval.lean: clamp_of_le
    InvariantInterval.lean: mkIET1_restrict_invariant_image
    MeasureTools.lean: volume_Ico_zero_one
    MeasureTools.lean: unitMeas_univ_Ico
    MeasureTools.lean: IET.unitMeas_preimage_pow
    MeasureTools.lean: IsFiniteUnionIntervals.biUnion
    MeasureTools.lean: freeGroup_lift_natural
    Presentation.lean: IsCompPresentation.toIsCutSet
    Presentation.lean: measurable_paramAffine
    Presentation.lean: lt_iff_lt_of_ne
    ReductionData.lean: ofMem_
    ReductionData.lean: ofMem_v
    ReductionData.lean: IETDatum.isSplitting_zero
    ReductionData.lean: IETDatum.isSplitting_last
    ReductionData.lean: continuous_toReal
    SubintervalTransfer.lean: cellLen_last
    TranslationVector.lean: mkIETFun_sub_eq_lattice
    TranslationVector.lean: IET.coeHom_apply
    TranslationVector.lean: evalWord_sub_eq_lattice
    continuous_domination.lean: exists_continuous_indicator_le

Three of those are worth a decision before the rest:

* the `SumForm` route in `BlockDiophantine` (`SumForm`, `sumForm_zero`, `sumForm_one`,
  `leftEnd_simplexMap_coeff`, `upperEnd_simplexMap_coeff`, `sumForm_cutAffineRight`,
  `sumForm_upperEndAffineRight`, `sumForm_cutAffine`, `sumForm_imageLeftAffine`,
  `sumForm_preimageCutAffine`, `eq_on_of_eq_at`, `le_of_lt_of_sumForm`, `le_or_le_of_sumForm`,
  `exists_sumForm_s`, `sSum`, `isIntAffine_sSum`, `sumForm_sSum`, `sSum_spec`,
  `isIntAffine_upperEndAffineRight` — about 290 lines) is a **whole superseded route** to the
  Diophantine transfer, dead since item 4 removed its last user.  It is the paper's "the `νᵢ` and the
  `μ'_j` are integer linear combinations" formalised through `SumForm`; the live route is
  `IsIntAffine` / `IsDiophantine.of_intAffine_family`.  Deleting it is a decision about the
  narrative, not just about dead code, so it was left; the backup is `.scratch/bak/audit-item5/`.
* `ae_irreduciblePerm_blockPerm` (`BlockDatum`) — the a.e. form of Lemma 3.2's irreducibility for
  blocks.  The assembly calls `isIrreduciblePerm_blockPermOf` inside A4 and does not need the a.e.
  statement; it is the paper's Lemma 3.2 a.e. version, so it was left.
* `IsCompPresentation.toIsCutSet` and `paramMeasure_absolutelyContinuous` — library-shaped API that
  nothing happens to use.

### State

`./Build.sh` green, no warnings:

```
declarations still depending on sorryAx: 4
  of which display-only statement files (Challenge, ChallengeWeak): 4
  of which the library (with ChallengeWeakSolved): 0
```

`Check.lean` has 320 axiom lines, none containing `sorryAx`.

## The 75 unused declarations are deleted (this session)

The person asked for all 75 candidates of the item-5 scan to be deleted, starting with the `SumForm`
route.  **69 of the 75 are gone, and 6 are kept**, four of them because the scan was wrong.

### Deleted: 80 declarations, 974 lines

The scan listed 75 theorems/lemmas whose *short name* did not occur elsewhere in the sources.  Two
things then turned up:

* dot-notation uses (`h.foo`, `continuous_toReal.measurable`, `D.mem_markCuts`) were invisible to the
  scan's tokenizer, which split on `.` and kept only the last component;
* `simp`-only uses are invisible to any name-based scan.

So the deletion was done file by file in build order, with a script that removes a declaration
together with its docstring (`IET` → `CutSet` → `Diophantine` → `Commensurable` → `MeasureTools` →
`TranslationVector` → `Centralizer` → `ReductionData` → `Presentation` → `IntegerAffine` →
`GoodRegion` → `SubintervalTransfer` → `BlockRescaling` → `GeneratorChange` → `InvariantInterval` →
`BlockEndpoints` → `BlockAETransfer` → `BlockDiophantine` → `BlockIrreducibility` → `BlockData` →
`BlockDatum`), compiling each file before moving on, and checking after each file that the diff
contained no added line.

Per file: `IET` 4, `CutSet` 1, `Diophantine` 1, `Commensurable` 1, `MeasureTools` 5,
`TranslationVector` 2, `Centralizer` 5, `ReductionData` 4, `Presentation` 3, `IntegerAffine` 2,
`GoodRegion` 1, `SubintervalTransfer` 1, `BlockRescaling` 7, `GeneratorChange` 1,
`InvariantInterval` 5, `BlockEndpoints` 9, `BlockAETransfer` 1, `BlockDiophantine` 21,
`BlockIrreducibility` 3, `BlockData` 1, `BlockDatum` 2.

### The `SumForm` route (`BlockDiophantine`, 21 declarations, 300 lines)

Deleted as a whole, as asked: `SumForm`, `sumForm_zero`, `sumForm_one`, `leftEnd_simplexMap_coeff`,
`upperEnd_simplexMap_coeff`, `sumForm_cutAffineRight`, `sumForm_upperEndAffineRight`,
`sumForm_cutAffine`, `sumForm_imageLeftAffine`, `sumForm_preimageCutAffine`, `eq_on_of_eq_at`,
`le_of_lt_of_sumForm`, `le_or_le_of_sumForm`, `exists_sumForm_s`, `sSum`, `isIntAffine_sSum`,
`sumForm_sSum`, `sSum_spec`, `isIntAffine_upperEndAffineRight` — the superseded formalisation of the
paper's "the `νᵢ` and the `μ'_j` are integer linear combinations" through `SumForm`.  The live route
(`IsIntAffine`, `IsDiophantine.of_intAffine_family`, `isDiophantine_blockPair`) is untouched.

Two declarations inside that region are **live** and were kept: `cutAffine_eq_leftEnd` (used by
`Presentation` and `BlockDatum`) and `sum_sub_mul` (used by `SingularityBound`).  Their two empty
section headers (`## Small integer combinations of the two length vectors`, `## The sign of the
difference is constant`, `## The marked list, as small integer combinations`) and the `variable` line
that had become unused are gone, and `sum_sub_mul` gained the docstring it was missing.  Also deleted
here: `isIntAffine_gLenAffine`, `truncatedLengths_eq`.

### Kept, and why

* `mem_markCuts`, `ite_one_sub_ite_one_eq_zero`, `isBadParam_swap`, `continuous_toReal` — used, by
  dot notation (`D.mem_markCuts`, `continuous_toReal.measurable`, …), which the scan missed.
* `IET.coeHom_apply` — used, implicitly: `simp [h]` in `evalWord_apply_coe`
  (`TranslationVector`) closes its goal with this `@[simp]` lemma.  Deleting it broke that proof; it
  was restored, and that file lost only the other two.
* `exists_continuous_indicator_le` — not library code: it is the theorem statement of the discovery
  run `continuous-domination` in `Tasks/continuous_domination.lean`, a file that imports only
  `Mathlib` and is not compiled by `Build.sh`.  Deleting it would destroy the task record, so it was
  left; the scan only caught it because it names a theorem and nothing in the tree uses it.

### State

`./Build.sh` green, no warnings:

```
declarations still depending on sorryAx: 4
  of which display-only statement files (Challenge, ChallengeWeak): 4
  of which the library (with ChallengeWeakSolved): 0
```

`Check.lean` lost the 22 `#print axioms` lines of deleted declarations and now has 298, none
containing `sorryAx`.  The library (`IETFree/*.lean`) is now 20 643 lines over 33 modules (21 615 before).

## Audit of the hypotheses: what is removable, and what is not (this session)

The question was whether the hypotheses of the theorems can be weakened or removed, after the earlier
audit had already taken out the `hreg` / `hl` / `hm` families.  Method: extract every hypothesis binder
of every declaration (2 412 binders, data and propositions together), classify them by shape, and test
the candidates by deleting them and recompiling.

### Removed (compiles; full build green)

Two theorems lost three hypotheses between them, all derivable from what remains:

```lean
theorem GoodRegion.compLenAffine_mem_regionAt (G : …) {q : PReal d e} (hq : q ∈ G.O) :
    compLenAffine G.s q ∈ simplexRegion G.n
theorem BlockData.compLenVec_eq_simplexMap (G : …) {q : PReal d e} (hq : q ∈ G.O) :
    compLenVec G.s q (monoAt G hq) = simplexMap G.n (compLenAffine G.s q)
```

* `(hmono : StrictMono fun k => G.s k q)` was **literally** `monoAt G hq` (both statements), so it is
  now `have hmono : StrictMono fun k => G.s k q := monoAt G hq` in the proof;
* `(hn1 : 1 ≤ G.n)` follows from `G.n = d + e - 1` (`(G.pres …).card_eq`) and `NeZero d`, `NeZero e`.

Three call sites dropped their arguments (`BlockData` twice, `BlockDatum` once).

### Checked and **not** removable

* **`[NeZero (l - k)]` (5 binders: `idx_rescaleMap`, `idx_rescaleMap_aux`, the `RescaleBlock`
  wrapper of `idx_rescaleMap`, `mkIET1_rescale_subinterval`, `irreduciblePerm_blockPerm`).**  They
  look derivable from `hkl : k < l`, and the *proofs* indeed only need
  `haveI : NeZero (l - k) := ⟨by omega⟩`.  But the *statement* mentions `idx (blockLam lam k hkl hln)`
  and `mkIET1 (blockLam …)`, whose elaboration needs the instance, and instance search cannot derive
  `NeZero (l - k)` from `hkl`.  Removing the binder therefore fails at the signature, not at the
  proof (verified).  The systematic way to get rid of it is to index those statements by a `BlockIdx`,
  which is what the a.e. block statements already do through `BlockIdx.instNeZeroLen`.
* **The `q.1 ∈ simplexRegion d ∧ q.2 ∈ simplexRegion e` family (12 declarations).**  Both projections
  are used in each proof — I counted the `.1` / `.2` uses: the sparsest are `markedPos_spec`
  (`hreg.2` once), `preimageCutAffine_eq` (`hr.2` once) and `exists_compImage_on_ball` (`hr₀.1`
  twice), and in each the second projection is what gives `pos_simplexMap` for the *other* exchange.
  No one-sided weakening.
* **`Positive lam` (20 binders).**  Irreducible: `blockMass_pos` needs positivity of every coordinate.
  The only genuine weakening available is `blockLam`'s, which needs nothing more than
  `0 < blockMass lam k hln`; that is strictly weaker, but every caller has `Positive lam` anyway and
  the API would become non-standard, so it was not done.
* **The two Diophantine transfers** (`IsDiophantine.of_int_combination`, 9 hypotheses;
  `IsDiophantine.of_intAffine_family`, 11): each hypothesis is used essentially — `hK`/`hA`–`hB'` bound
  the coefficients, `hu0`/`hu1` place the rescaling in `(0, 1]`, `hrn : 0 < r + s` is nonemptiness of
  the family, `hw`/`hw'` are the integer-combination identities, `hL0`/`hL1` the mass bound.  None is
  implied by another.
* **The block statements of `BlockDatum`** (`comp_conj_rescale`, `blockRescaled`, `blockPermOf`,
  `irreduciblePerm_blockPerm`): after items 1–3 each takes exactly `(hq : q ∈ G.O)`, `(h : G.Fits q D E)`,
  `(hi : i₀ < i₁)`, the two pair-splitting hypotheses and the irreducibility input.  None of the six is
  derivable from the others.

### Found on the way: a dead chain (weakenable, but better deleted)

`IntegerAffine`'s `Convex` chain — `lt_or_gt_of_ne_of_convex`, `lt_or_gt_of_ne_of_convex_intAffine`,
`Convex.exists_isIntAffine_max`/`_min`/`_posPart`/`_truncatedLength` — takes `(hO : Convex ℝ O)`, and
every proof only uses that `O` is *preconnected* (sign constancy on a connected set).  So each could be
weakened to `(hO : IsPreconnected O)`; but nothing outside `IntegerAffine` uses any of them (their
short names occur twice in the file, which is why the name-based dead-code scan missed them), so the
better move is deletion rather than weakening.  The live truncation lemma is
`GoodRegion.exists_isIntAffine_truncatedLengths`, which takes no convexity hypothesis at all.

### State

`./Build.sh` green, no warnings, `declarations still depending on sorryAx: 4` (display-only files
only, none in the library), `Check.lean` at 298 axiom lines, none with `sorryAx`.

## The `Convex` chain is deleted and the `NeZero (l - k)` statements are re-indexed (this session)

Two tasks, the first as such and the second the completion of what the previous round left half done.

### `IntegerAffine`: the chain is gone, not weakened

Deleted: `lt_or_gt_of_ne_of_convex`, `lt_or_gt_of_ne_of_convex_intAffine`,
`Convex.exists_isIntAffine_max`, `…_min`, `…_posPart`, `…_truncatedLength`, and the two lemmas that
only they used (`lt_or_gt_of_ne_of_isPreconnected`, `IsIntAffine.continuous`).  Every one of those
proofs used only that `O` is preconnected (constancy of a sign on a connected set), so each could have
been restated with `(hO : IsPreconnected O)` — but nothing outside the file used any of them, so
deletion was the better move and the file lost 105 lines (418 → 313; the pre-deletion file is
`.scratch/bak/audit-cv/IntegerAffine.lean`).  The live truncation lemma is
`GoodRegion.exists_isIntAffine_truncatedLengths` (`BlockDiophantine`), which takes no convexity
hypothesis at all, and the module docstring now says so instead of advertising the chain.  `Check.lean`
lost the three `#print axioms` lines of the chain and is at 475 lines.

### `[NeZero (l - k)]`: what became of all five statements

The instance cannot be *derived at a binder*: instance search cannot use `hkl : k < l`, and a statement
that mentions `idx (blockLam …)` or `mkIET1 (blockLam …)` needs the instance while its own signature
is elaborated.  The only way out is to bundle the indices, which is what `BlockIdx` does.

* `idx_rescaleMap` (root) and `RescaleBlock.idx_rescaleMap` — deleted as dead; nothing used them, the
  live one is `idx_rescaleMap_aux`.
* `IETDatum.irreduciblePerm_blockPerm` (`BlockDatum`) — binder removed.  Its statement never mentions
  the block's `idx`/`mkIET1`, only `blockPerm`, so `haveI : NeZero (l - k) := ⟨by omega⟩` in the proof
  is enough.
* `RescaleBlock.idx_rescaleMap_aux` and `RescaleBlock.mkIET1_rescale_subinterval` — **re-indexed by
  `I : BlockIdx n`** here.  Both statements now read `leftEnd lam I.kFin`, `blockMass lam I.k I.hln`,
  `blockLam lam I.k I.hkl I.hln hpos`, and the conclusion `… - I.k`; the instance comes from
  `BlockIdx.instNeZeroLen`.  The two call sites (both in `BlockDatum`) build the bundle:
  `⟨k, l, hkl, hln⟩` in `irreduciblePerm_blockPerm` and `⟨i₀.val, i₁.val, hi, hln⟩` in
  `comp_conj_rescale`.  No statement about a block in the library carries the instance any more; the
  four remaining `haveI : NeZero (l - k)` (`BlockAETransfer` ×2, `BlockData`, `BlockDatum`) are inside
  proofs, which is where it belongs.

### `obtain ⟨k, l, hkl, hln⟩ := I` fails; `abbrev kFin` plus `set` is what works

The `obtain` route was tried again and failed in a way worth writing down, so that it is not tried a
third time: after the case split the hypotheses mention `⟨k, l, hkl, hln⟩.kFin`, the proof's
`⟨k, by omega⟩` does not match it under `rw`, goals keep the `{k := k, …}.k` shape, and instance
search for `NeZero (l - k)` fails outright (the projections of a metavariable do not reduce).

What does work, and is what the file now does:

1. `BlockIdx.kFin` is an **`abbrev`** rather than a `def`.  A `def` is not unfolded during rewrite
   matching, so the first `rw [hLdef, hMdef]` fails ("did not find an occurrence of the pattern"); with
   `abbrev` it is reducible, `I.kFin` is seen as `⟨I.k, _⟩`, and `Fin`'s proof fields are compared by
   proof irrelevance.  (Same phenomenon as `Positive`: see "Audit item 5".)
2. Keep `I` **opaque** — no `obtain`, no `cases` — and start the proof with
   `set k := I.k; set l := I.l; have hkl : k < l := I.hkl; have hln : l ≤ n := I.hln`.
   The proof bodies then stay **verbatim**: `k`, `l`, `hkl`, `hln` and `⟨k, by omega⟩` are defeq to
   what the statement mentions.
3. `BlockIdx.kFin` is now used by both statements, so the "use it or delete it" question of the
   previous round is closed.

### Also deleted, found on the way

`RescaleBlock.leftEnd_blockLam` — a restatement, under the section's ambient hypotheses, of the root
`leftEnd_blockLam`, and used by nothing: the two uses inside `idx_rescaleMap_aux` resolve to the *root*
lemma (they precede the wrapper in the file) and `mkIET1_rescale_subinterval` writes
`_root_.leftEnd_blockLam` explicitly.  It is exactly the case the name-based dead scan cannot see (a
wrapper with the same short name as a live declaration).  Also removed: a duplicated
`set_option linter.unusedSimpArgs false` with its comment, at the head of `BlockRescaling`.

### State

`./Build.sh` green, no warnings, `declarations still depending on sorryAx: 4` (display-only files
only, none in the library), `Check.lean` at 295 axiom lines, none with `sorryAx`; `Tasks/Match.lean`
passes.  The library is 20 441 lines over 33 modules (`BlockRescaling` 1177).

## The five name-scan candidates are deleted (this session)

The dead scan (`python3 .scratch/deadscan.py`) still listed five declarations whose names occurred
nowhere else in the tree; they are gone, and `Check.lean` lost their four `#print axioms` lines:

* `Presentation`: `sign_congr` — plus a comment in `Check.lean` that an earlier deletion had left
  dangling above `#print axioms listImageLeft_sub_of_Icc`.
* `BlockRescaling`: `listImageLeft_sub_of_Icc` (the `hR`-hypothesis form of the image splitting; the
  live route is `imageLeft_blockPerm_aux`), `leftEnd_add_blockMass_le_total`, `idx_mem_block`
  (the index bounds are read off `le_idx`/`idx_mem` directly where they are needed).
* `BlockDatum`: `translationVector_fin_one` (the degenerate block is handled by `mkIET1_of_all_one`
  and `blockLam_of_one`).

Backups of the three files before the deletion are in `.scratch/bak/audit-dead2/`; the diff against
them is only the declaration blocks plus one collapsed blank line.

### Dead as a consequence, and deliberately left in place

Three declarations lose their last user with the above.  They are **not** deleted: they were not
asked for, and each is a self-contained statement rather than something the deletion made redundant.

* `Presentation.sign_const` — its only use was `sign_congr`.
* `Presentation.pos_of_pos` — its only uses were inside `sign_const`.
* `BlockRescaling.lamNat_nonneg` — this one *is* a duplicate: the same statement as
  `sum_range_lamNat_nonneg`, which stays live inside `sum_range_lamNat_mono`.  After the deletion
  `section IdxBlock` holds only it, with a `variable` line none of whose variables it uses (no
  warning, but the scaffolding is now pointless).

`affine_comb`, `comb_zero`, `sign_const`'s neighbours in the docstring of `Presentation`
(`affine_comb` / `sign_const`, "the sign of an affine function") all stay, and `affine_comb` /
`comb_zero` remain live through `pos_on_ball_of_vanish_imp` and `sign_congr_on_ball`.

### State

`./Build.sh` green, no warnings, `declarations still depending on sorryAx: 4` (display-only files
only, none in the library), `Check.lean` at 291 axiom lines, none with `sorryAx`, all of them
`[propext, Classical.choice, Quot.sound]`; `Tasks/Match.lean` passes.  The library is 20 328 lines
over 33 modules.

## The three declarations the last pass orphaned are deleted (this session)

`Presentation.pos_of_pos`, `Presentation.sign_const` and `BlockRescaling.lamNat_nonneg` (the duplicate
of the live `sum_range_lamNat_nonneg`) are gone, together with `section IdxBlock` in `BlockRescaling`,
which after the previous pass held only `lamNat_nonneg` and a `variable` line nothing used.  `Check.lean`
lost one `#print axioms` line (`sign_const`; the other two never had one) and is at 466 lines.

Two docstrings referred to the deleted declarations and were rewritten:

* `Presentation`'s module docstring advertised `affine_comb` / `sign_const` as the tools that make the
  order locally constant; it now names `affine_comb` / `comb_zero` and the live ball-local pair
  `pos_on_ball_of_vanish_imp` / `sign_congr_on_ball`.
* `pos_on_ball_of_vanish_imp`'s docstring said the affine combination was "used in `pos_of_pos`"; it
  now points at `affine_comb`.

Nothing else changed: `affine_comb` and `comb_zero` stay live through `pos_on_ball_of_vanish_imp` and
`sign_congr_on_ball`, and no docstring mentions any of the three names any more.

### State

`./Build.sh` green, no warnings, `declarations still depending on sorryAx: 4` (display-only files
only, none in the library), `Check.lean` at 290 axiom lines, none with `sorryAx`, all
`[propext, Classical.choice, Quot.sound]`; `Tasks/Match.lean` passes.  The library is 20 288 lines
over 33 modules.  Backups of the three files before this deletion: `.scratch/bak/audit-dead3/`.

## `leftEnd_blockMass` is deleted (this session)

The last entry's closing scan found `BlockRescaling.leftEnd_blockMass` orphaned — its only consumer was
`idx_mem_block`, deleted two passes ago — and it is now gone, with its `#print axioms` line.  It was the
`j = last` case of `leftEnd_blockLam` (the right end of the block is the left end of its last cell plus
its mass); nothing in the library needs that form, because the endpoints of a block are taken from
`G.s i₀ q` / `G.s i₁ q` and `leftEnd_add_blockMass` / `leftEnd_add_blockMass_compLen` directly.
`section Extra` loses nothing (`leftEnd_le_leftEnd` remains, and it uses the section's `{n : ℕ}`).

### State

`./Build.sh` green, no warnings, `declarations still depending on sorryAx: 4` (display-only files only,
none in the library), `Check.lean` at 289 axiom lines, none with `sorryAx`, all
`[propext, Classical.choice, Quot.sound]`; `Tasks/Match.lean` passes.  The library is 20 275 lines over
33 modules.  Backup before this deletion: `.scratch/bak/audit-dead4/`.

The dead scan now lists only the declarations that are *kept on purpose* (`mem_markCuts`,
`ite_one_sub_ite_one_eq_zero`, `isBadParam_swap`, `continuous_toReal`, `IET.coeHom_apply`, used by dot
notation or `simp`) and `Tasks/continuous_domination.lean`'s `exists_continuous_indicator_le`.

## Audit of the repeated arguments (this session; nothing changed)

Method: a parser for the 33 modules (`.scratch/audit/parse.py`, `report.py`, `dups.py`) extracts the
914 declarations and their 4 792 binders, then counts binder shapes, consecutive and unordered
repetitions, near-identical conclusions (token Jaccard) and repeated proof lines.  Numbers below are
declaration counts, i.e. how many *statements* carry the tuple.  **No code was changed.**

Size of the problem: 96 of the 914 declarations have at least 10 binders
(`GoodRegion` 15, `Presentation` 11, `BlockIrreducibility` 10, `SingularityList` 10, `BlockDatum` 8,
`SingularityBound` 7, `LengthMap` 6).  Bindera per declaration: `GoodRegion` 11.1, `BlockLemma` 9.5,
`SingularityList` 8.0, `BlockDatum` 7.7, `LengthMap` 7.7.  Hypothesis density (Prop-valued binders):
`InvariantInterval` 40 %, `Irreducible` 36 %, `BlockDatum` 36 %, `BlockLemma` 34 %.

Ordered by payoff over cost:

1. **`BlockOf π` (a `BlockIdx` + `hstab`).**  Nine declarations spell the same five arguments
   `(k) (l) (hkl) (hln) (hstab)`: `BlockRescaling.blockPerm`, `blockPerm_apply_val`,
   `blockPerm_lt_iff`, `imageLeft_blockPerm_aux`, `mkIET1_rescale_subinterval`;
   `BlockDatum.irreduciblePerm_blockPerm`; `BlockAssembly.exists_word_trivial_on_all_of_blocks`;
   `BlockIrreducibility.imageLeft_eq_leftEnd_of_splitting`; `ReductionData.perm_eq_of_preimage`.
   A structure in `BlockRescaling` extending `BlockIdx` with the `stab` field, with
   `GoodRegion.Block` then extending *it* instead of duplicating `hstab`, would take each of the nine
   to one argument, and would let `blockLam` / `blockMass` / `blockPerm` gain `BlockIdx`-shaped
   versions (`blockLamOf I hpos`) — they are called 71 / 53 / 16 times with `lam k hkl hln (hpos)`.
2. **`BlockAt G` (the block data at a point).**  Seven declarations in `BlockDatum` with 12–14
   binders repeat `(hq) {D} {E} (h) {i₀ i₁} (hi) (hk) (hk')`: `blockOf`, `blockPermOf`,
   `irreduciblePerm_blockPerm`, `isIrreduciblePerm_blockPermOf`, `blockRescaled`, `comp_conj_rescale`,
   `restrict_rescale`.  One structure would leave ~4 binders each, and would absorb the repeated
   `(by omega : i₁.val ≤ G.n)` side conditions.
3. **`IsCutSet` boilerplate.**  60 declarations write `{f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}
   (hs : IsCutSet f a b s)` out in full (`CutSet` 39, `CutSetMeasure` 14, `IET` 7; plus 13 more of
   the `(⇑e)` variant).  Source-level fix only: hoist into `variable {f a b s}` +
   `variable (hs : IsCutSet f a b s)` per section (~200 binder spellings).  Bundling `IsCutSet` into
   a structure is *not* worth it — dot notation already keeps the call sites clean.
4. **`GoodRegion.pres` / `type` still carry the `hl` / `hm` witnesses**, which is why `presAt` /
   `typeAt` exist at all; 13 uses of `.pres` vs 16 of `.presAt` is two shapes for one statement.  The
   fields can inline the witnesses (they may use the earlier field `subset_region`), after which
   `presAt`/`typeAt` are `G.pres q hq` / `G.type q hq`.
5. **`monoAt` and `GoodRegion.s_mono` are the same lemma** (`StrictMono fun k => G.s k q`); `s_mono`
   proves it in one line from the new `presAt`, `monoAt` rebuilds the two `simplexMap_mem_simplex_fin`
   witnesses by hand (~30 uses of `monoAt`, 2 of `s_mono`).  Leftover of the `presAt` refactor:
   `monoAt := (G.presAt hq).mono`, then `s_mono` is redundant.
6. **`(u, v, 0 ≤ u, u < v, v ≤ 1)` and the invariant-interval hypothesis** (`InvariantInterval`, the
   most hypothesis-dense file): 9 declarations, 4–5 of them adding
   `(hinv : ∀ x ∈ Set.Ico u v, mkIET1 mu σ hl x ∈ Set.Ico u v ↔ x ∈ Set.Ico u v)`.  A `SubInterval`
   structure (with `truncatedLengths` indexed by it, 38 call sites) plus an `InvariantSub` for `hinv`.
7. **The combinatorial core of `GoodRegion`/`SingularityList`** — `(π) {v w} (hv) (hl) (hm) {τ} {s}
   (hmono) (hzero) (htop) (hcut …)`, 15 of the 19 big declarations in `GoodRegion` and 10 of 14 in
   `SingularityList`; the six largest statements have 18–22 binders.  One `CompDatum d e n` structure
   would remove 10–15 binders from ~18 statements.  Biggest win, biggest diff (every proof body names
   these); do `SingularityList` first, where they are concentrated.
8. **Smaller**: `¬ IsBadParam (D.v, E.v)` with `(D) (E)` in 18 declarations (a `Pair` bundle);
   `isLat_fwd_disp` / `isLat_fwd_disp_mu` and `isLat_inv_disp` / `isLat_inv_disp_mu` are two pairs of
   the same lemma for the `lam` and `mu` families — `TranslationVector.latticeDisp_gen` already shows
   the `Sum.elim lam mu` unification; `(lam) (π) (hl : ∑ = 1)` in 20 declarations is the honest
   interface of the frozen `mkIET1` (a bundle would be additive API, not a change); 10 ×
   `obtain ⟨hp, hw⟩ := G.subset_region q hq` would read better with `G.mem_region_fst`/`_snd`
   accessors; `[NeZero G.n]` is taken explicitly in 17 declarations although `G.n = d + e - 1`.

Deliberately left alone: `{d e} [NeZero d] [NeZero e]` (the Lean idiom for the ambient pair),
`(hq : q ∈ G.O)` (a `Subtype` would add `val` noise at 47 sites), `GoodRegion`'s `π σ q₀` parameters
(making them fields would drop 3 binders from 61 declarations but rename them in every proof),
the `mkIETFun_inv_left` triples (frozen statement files) and
`cutSet_isCutSet`/`IsIET.cutSet_isCutSet` (a wrapper that builds `∃ s` from `IsIET`).

## Acting on the audit: items 3, 4 and 5 (this session)

### Item 3 — the `IsCutSet` data is a section variable, but `hs` cannot be

57 declarations no longer spell out `{f : ℝ → ℝ} {a b : ℝ} {s : Finset ℝ}`: it is a `variable` line in
a `section CutSetData` (`CutSet` 39, `CutSetMeasure` 12, `IET` 6 — in `IET` a file-level `variable`,
which is why that file grew by a couple of lines).  `(hs : IsCutSet f a b s)` stays the **first explicit
binder** of each of them, and the reason is worth recording, since the audit entry above proposed
hoisting `hs` too:

* in this Lean (4.33) a section variable that does **not** occur in the declaration's type is not in
  scope in its proof: `theorem foo : <statement not mentioning h> := … h …` fails with "unknown
  identifier `h`" unless `include h` is used (probe `.scratch/audit/q9.lean`);
* `include hs` puts it back in scope, but the resulting binder is *inaccessible*, so field notation
  `hs.card_pos` stops working ("Function `card_pos` does not have a usable parameter of type
  `IsCutSet …`", probes `q4`/`q5`/`q10`).  Both are needed: many cut-set lemmas have statements that
  never mention `hs` (`IsCutSet.card_pos : 0 < s.card`) and are used by dot notation.

**Signatures are unchanged**: the declarations of the three files were dumped with `#check @` before and
after (`.scratch/audit/checksig3.lean` → `sig_before.txt`, `sig_final.txt`) and the dumps are
identical.  The 11 `(⇑e)` variants (`{a b} {e} {s}`, in two different orders) are left explicit: one
section cannot reproduce both orders.

### Item 4 — `G.pres` / `G.type` no longer take the simplex-membership witnesses

The two fields build them from the earlier field `subset_region`:

```lean
pres : ∀ (q) (hq : q ∈ O),
  IsCompPresentation (simplexMap d q.1) π (simplexMap e q.2) σ
    (simplexMap_mem_simplex_fin (subset_region q hq).1.1 (subset_region q hq).1.2)
    (simplexMap_mem_simplex_fin (subset_region q hq).2.1 (subset_region q hq).2.2)
    n (fun k => s k q) ρ
```

(`type` likewise, with the first witness only).  Consequences:

* `GoodRegion.presAt` and `GoodRegion.typeAt` are **deleted** — they existed only to apply the fields to
  derived witnesses; their 15 uses are now `G.pres q hq` / `G.type q hq`.
* `LengthMap.compLen_injective` takes `(hpres : ∀ (q) (hq : q ∈ O), IsCompPresentation … (witnesses
  from `hreg q hq`) …)` and `htype` likewise, so its caller still passes `G.pres G.type` verbatim; the
  proof lost four `have hlq : … := simplexMap_mem_simplex_fin …` lines and the witness arguments.
* the `G.pres q hq (witness) (witness)` call sites (`BlockData` ×4, `BlockDatum`, `BlockEndpoints` ×2,
  `LengthMap` ×2) and the 8 `obtain ⟨hp, hw⟩ := G.subset_region …` lines that fed them are gone.
* `exists_goodRegion`, the one place that *builds* a `GoodRegion`, still passes the witnesses explicitly
  (`fun q hq => (hpres q hq w1 w2).1`): `_` does not elaborate there — the field's argument is
  elaborated before the constructor is known.

### Item 5 — `monoAt` is one line and `s_mono` is gone

`monoAt`'s proof was a leftover of the time before `pres` built its own witnesses: it rebuilt the two
`simplexMap_mem_simplex_fin` terms by hand.  It is now `(G.pres q hq).mono`, and `GoodRegion.s_mono` —
the same statement in one line, added later on top of `presAt` — is deleted; its two uses
(`BlockLemma`, `BlockEndpoints`) are `monoAt G hq`.

### State

`./Build.sh` green, no warnings, `declarations still depending on sorryAx: 4` (display-only files only,
none in the library), `Check.lean` unchanged at 289 axiom lines, none with `sorryAx`, all
`[propext, Classical.choice, Quot.sound]`; `Tasks/Match.lean` passes.  The library is 20 233 lines over
33 modules (`CutSet` 618, `CutSetMeasure` 585, `IET` 1034, `GoodRegion` 1219, `LengthMap` 521,
`BlockData` 393, `BlockDatum` 878, `BlockEndpoints` 477).

## Elaboration test and cleanup pass (this session)

### Method

`Build.sh` compiles 33 modules sequentially with plain `lean` (no Lake).  The test times every module
in build order with warm oleans, two passes, machine otherwise idle (4 cores, 15 GB, load average
< 0.1, Lean 4.33.1):

* **full**: `/usr/bin/time -f '%e %U %S %M'` around `lean -o <scratch>/M.olean IETFree/M.lean`;
* **import load**: the same around a stub `import IETFree.M`;
* **own file** = full − import load.

Harness `.scratch/elab/measure.sh <outdir>`, summary `.scratch/elab/report.py <dirs…>`.  Spread
between the two passes is ≤ 0.08 s per module (before) and ≤ 0.04 s (after), so a difference above
0.1 s is meaningful.  Per-declaration costs were localised with declaration-aligned prefix compiles
(`.scratch/elab/cut.py <module> <fraction>`) and isolated reproducers in `.scratch/elab/prof/`.

### Before

| module | full | import | own | lines | ms/line |
|---|---|---|---|---|---|
| SubintervalTransfer | 4.65 | 1.91 | **2.74** | 643 | 4.3 |
| Diophantine | 4.25 | 1.90 | **2.35** | 1248 | 1.9 |
| Irreducible | 3.99 | 1.91 | **2.08** | 843 | 2.5 |
| GoodRegion | 3.34 | 1.91 | 1.43 | 1219 | 1.2 |
| BlockDatum | 3.29 | 1.90 | 1.40 | 878 | 1.6 |
| SingularityList | 3.16 | 1.90 | 1.26 | 1003 | 1.3 |
| BlockRescaling | 3.08 | 1.90 | 1.19 | 1068 | 1.1 |
| SingularityBound | 3.06 | 1.89 | 1.17 | 943 | 1.2 |
| ReductionData | 3.04 | 1.91 | 1.13 | 1080 | 1.0 |
| TranslationVector | 2.84 | 1.91 | 0.93 | 288 | 3.2 |

**Total: 90.8 s = 62.9 s import loading + 27.9 s own-file.**  Two thirds of the build is the
`import Mathlib` load that every module pays; nothing here changes it.

Phase profile of the expensive modules (`set_option profiler true`, exclusive cumulative times):

* `SubintervalTransfer`: typeclass inference **2.5 s**, of which one `AddTorsor` search **1.34 s**;
  tactic execution 711 ms (`simp` 256), type checking 372, linting 214, olean 180, process
  pre-definitions 198, elaboration 135.
* `Diophantine`: tactic execution 2.67 s (`nlinarith` 547 ms in one step, 15 `positivity` calls of
  20–58 ms), typeclass inference 1.89 (diffuse), linting 369, `simp` 327, `norm_num` 125.
* `Irreducible`: tactic execution 1.92 (`simp` 534, `norm_num` 260, `ring` 80), typeclass inference
  1.38 (diffuse), linting 228.
* `BlockDatum`, first 153 lines: tactic execution 668 ms, **`nlinarith` ×4 = 474 ms**
  (238/136/52/48).
* `TranslationVector`, lines 93–199: 4 `simp` ≈ 175 ms, `Nonempty` instance searches ≈ 135 ms.

Bisect of `SubintervalTransfer` (quarters of the file, own time): 0.52 / **1.35** / 0.50 / 0.38 —
and within the second quarter the jump is at lines 260→284, i.e. the definition of `splitMap`
(+1.47 s).  Isolated reproducer (`.scratch/elab/prof/splitmap.lean`): the same definition alone costs
1.28 s of `AddTorsor` search; a type ascription on the `prod` does not help (1.26 s); rewriting it
with `LinearMap.pi` / `LinearMap.prod` and `.toAffineMap` removes the search entirely (wall 3.51 →
1.98 s).

### Changes

1. **`SubintervalTransfer.splitMap`** — the `AffineMap.pi … |>.prod …` construction replaced by
   `LinearMap.pi … |>.prod … |>.toAffineMap`; `splitMap_apply` reproved through
   `LinearMap.coe_toAffineMap`, `LinearMap.prod_apply`, `Function.prod`, `LinearMap.pi_apply` (three
   `rfl`s where the old proof had them).  Its **type is unchanged and `splitMap_apply` — the
   specification — is unchanged**, so nothing downstream moved.  Own file 2.74 → **1.22 s**; the
   `AddTorsor` search is gone and `typeclass inference` drops to 1.13 s.
2. **`BlockDatum.irreduciblePerm_blockPerm`** — the four `nlinarith` calls are linear goals; replaced
   by `linarith [mul_pos hMpos hjpos]`, `linarith [mul_lt_mul_of_pos_left hjlt hMpos]`,
   `linarith [hxc, hkey]` and `le_add_of_nonneg_right (mul_nonneg hMpos.le hy0)`.  Proof only.  Own
   file 1.40 → **0.80 s**; in the first 153 lines tactic execution falls 668 → 227 ms and
   `typeclass inference` 190 → 80 ms.
3. **`Diophantine.summable_badBound`** — one `nlinarith` on a linear goal → `linarith`.  **No
   measurable change** (4.25 → 4.24 s); kept because the goal is linear, so `linarith` suffices.

### After

| module | full | import | own | Δ own |
|---|---|---|---|---|
| SubintervalTransfer | 3.11 | 1.89 | **1.22** | −1.52 |
| BlockDatum | 2.71 | 1.91 | **0.80** | −0.60 |
| Diophantine | 4.24 | 1.90 | 2.34 | −0.01 |
| every other module | — | — | — | within ±0.04 |

**Total: 88.5 s = 62.8 s import loading + 25.7 s own-file** (−2.3 s, −2.5 % of the build; −2.2 s,
−7.9 % of the own-file elaboration).  `./Build.sh` green, `declarations still depending on sorryAx: 4`
(display-only files only), `Check.lean` at 289 axiom lines, none with `sorryAx`, `Tasks/Match.lean`
ok.  End to end, `./Build.sh` went from 94 s to about 88 s.

### Found, measured, **not** changed

* `TranslationVector.latticeDisp_list` (0.6 s of that module's 0.93 s): the cost is in the statement,
  which repeats `cond p.2 (if p.1 = 0 then f else g) ((if p.1 = 0 then f else g)⁻¹)` six times.
  Shortening it means introducing a generator abbreviation and changing three statements that
  `BlockAssembly` consumes — a statement change, not a proof cleanup.
* `Irreducible` (2.1 s) and `Diophantine` (2.3 s) are **diffuse**: no declaration with one lever;
  `simp`, `norm_num` and instance search spread over dozens of steps of 10–50 ms.
* `positivity` in `Diophantine` costs 20–58 ms per call there but **5 ms on the same goal shape in
  isolation**, so the cost is the local context, not the tactic; there is no certain tactic-level fix.
* Linting costs 150–370 ms per module (roughly 6–8 s in total, a quarter of the own-file time).
  Turning linters off in `Build.sh` would be a policy change (the tree is warning-free), so this is
  reported, not done.
* Import loading (62.9 s, 69 %) would need narrower Mathlib imports in every module; the project
  imports `Mathlib` throughout and two files are frozen.

### Measurement caveat

The first "after" pass was polluted by a concurrent probe of mine (Diophantine's import stub spiked
from 1.90 to 2.29 s, `Commensurable` with it); it was discarded and both "after" passes were re-run on
an idle machine.  The figures above are from those two clean passes.

## The library uses Mathlib's commutator now (this session)

`commWord a b = a⁻¹ * b⁻¹ * a * b` (the paper's `[a,b]`) is **deleted**.  The library uses Mathlib's
`⁅a, b⁆ = a * b * a⁻¹ * b⁻¹` (`commutatorElement`, from `Mathlib.Algebra.Group.Commutator`, available
after `open scoped commutatorElement` — added to `MeasureTools`, `Irreducible`, `BlockAssembly`).
Mathlib's convention puts the inverses on the right, so the paper's commutator is `⁅a⁻¹, b⁻¹⁆`, and
the support argument of Section 2 — the one that runs through `f`'s unique ergodicity — is the place
where the two differ, so that is the place where the *words* (not the proofs) change.

### What is now stated with `⁅·,·⁆` (true for either convention, proof unchanged)

| declaration | file |
|---|---|
| `exists_nontrivial_commutator` (Lemma 2.7) | `Irreducible` |
| `wordLength_commutatorElement_le` (was `wordLength_commWord_le`) | `MeasureTools` |
| `evalWord_commutatorElement` (was `evalWord_commWord`) | `Irreducible` |
| `commutator_apply_eq_self_left`, `commutator_apply_eq_self_right` (the assembly) | `BlockAssembly` |

`commWord_eq_one_iff` is gone: Mathlib has `commutatorElement_eq_one_iff_mul_comm`, which is exactly
it, and Lemma 2.7's proof now calls that.

### What is stated with `⁅φ⁻¹, ψ⁻¹⁆` (the paper's `[φ,ψ]`, where the direction is essential)

* `commutator_inv_genY_genX_pow_ne_one` (was `commWord_genY_genX_pow_ne_one`): the word of Lemma 2.8,
  the paper's `[g, f^q] = g⁻¹(f^q)⁻¹gf^q`;
* `commutator_inv_apply_eq`, `commutator_inv_supp_subset`, `unitMeas_real_supp_commutator_inv_le`
  (was `commWord_apply_eq`, `commWord_supp_subset`, `unitMeas_real_supp_commWord_le`): the support of
  `[φ,ψ]` is contained in `A ∪ φ⁻¹A ∪ ψ⁻¹A`, with `A` the intersection of the supports.  The direction
  matters here — the estimate is used with `φ = g` and `ψ = f^q`, and `f^q` is the factor whose
  preimage is measured by uniqueness of `unitMeas`;
* the words produced by Lemma 2.8 and Lemma 2.10: `⁅genY⁻¹, (genX^q)⁻¹⁆` and `⁅w⁻¹, v⁻¹⁆`.

Two small additions made this refactor cheap: `commutatorElement_inv_inv_eq_one_iff`
(`⁅a⁻¹, b⁻¹⁆ = 1 ↔ ⁅a, b⁆ = 1`, so Lemma 2.7's plain-commutator disjunction transfers to the words
Lemma 2.10 builds) and `wordLength_inv`.  `commutatorElement_inv_inv_eq_one_iff` needs only
`[propext]`.

### The assembly: the two helper lemmas had to change shape

For Mathlib's `⁅a,b⁆ = a b a⁻¹ b⁻¹` applied to `x`, the innermost factor is `b⁻¹`, so the earlier
hypothesis "`b` maps `S` into `S`" is not enough: what is needed is that `b⁻¹` comes back to `S`.  The
two lemmas now read

```lean
theorem commutator_apply_eq_self_left {a b : IET 0 1} {S : Set ℝ} {x : ℝ} (hx : x ∈ S)
    (ha : ∀ y ∈ S, a y = y) (hb : ∀ y ∈ S, b⁻¹ y ∈ S) : (⁅a, b⁆) x = x
theorem commutator_apply_eq_self_right {a b : IET 0 1} {S : Set ℝ} {x : ℝ} (hx : x ∈ S)
    (hb : ∀ y ∈ S, b y = y) (ha : ∀ y ∈ S, a⁻¹ y ∈ S) : (⁅a, b⁆) x = x
```

(the second goes through `⁅a,b⁆ = ⁅b,a⁆⁻¹`, since `commutatorElement_inv` gives `⁅b,a⁆ = ⁅a,b⁆⁻¹`).
The hypotheses became "the *inverse* preserves `S`", which the assembly has anyway: it now proves
`hpres' : … (evalWord u …)⁻¹ x ∈ S` from `hpres u⁻¹` plus `evalWord_inv`, and the conjugated factors
use `(D⁻¹ * u * D)⁻¹ = D⁻¹ * u⁻¹ * D`.  The assembly's words are the plain `⁅w, wi⁆`,
`⁅genX⁻¹ * w * genX, wi⁆`, `⁅genY⁻¹ * w * genY, wi⁆`, so no bridge is needed there with Lemma 2.7.

### State

`./Build.sh` green, no warnings (but the four display-file sorries), `declarations still depending on
sorryAx: 4` (display-only files only, none in the library), `Check.lean` at **297** axiom lines (289
+ 8 for the new commutator API), none with `sorryAx`, all of them
`[propext, Classical.choice, Quot.sound]` except `commutatorElement_inv_inv_eq_one_iff` (which is
`[propext]`); `Tasks/Match.lean` passes.  The library is 20 280 lines.

`Tasks/nontrivial_commutator.lean` keeps its own `commWord`: it is the frozen statement handed to the
run `nontrivial-commutator` (stopped unsolved), and `Tasks/README.md` now records that the library
statement is the `⁅u, v⁆` form and that the two are equivalent.

## The comparator challenge (this session)

`comparator.json` sets up [leanprover/comparator](https://github.com/leanprover/comparator) for the
main theorem.  The goal of the challenge is the statement of `IETFree/ChallengeWeak.lean`:

```json
{ "challenge_module": "Comparator.Challenge",
  "solution_module":  "Comparator.Solution",
  "theorem_names": ["Comparator.mkIETFun_inv_left", "Comparator.main"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"] }
```

* `Comparator/Challenge.lean` imports `IETFree.Irreducible` and states the two theorems of
  `ChallengeWeak.lean` with `sorry`;
* `Comparator/Solution.lean` imports `IETFree.ChallengeWeakSolved` and proves them
  (`_root_.mkIETFun_inv_left`, `_root_.ChallengeWeakSolved.main`).

### Why `ChallengeWeak.lean` itself is not the challenge module

Comparator compares every declaration used in the statement of the listed theorems across the two
environments.  `ChallengeWeak.lean` is self-contained (`import Mathlib`) and re-declares its own
copies of `leftEnd`, `imageLengths`, `mkIETFun`, `mkIETEquiv`, `evalWord`, `UniqueErgodic`,
`MasurVeech`, …; its statements are therefore about `ChallengeWeak.mkIETEquiv` and
`ChallengeWeak.MasurVeech`, not about the library's, and no proof in the library inhabits them (the
two `UniqueErgodic` predicates even have different carriers, `ℝ → ℝ` against `IET 0 1`).  The
comparator pair states the same theorems over the library's definitions instead, so the statements
are the same constants on both sides.  `ChallengeWeak.lean` keeps its role as the self-contained
display of the theorem.

### What was checked here, and what was not

Verified in the VM: both modules compile; `#check @Comparator.main` and
`#check @Comparator.mkIETFun_inv_left` with `pp.explicit` are byte-identical between the two files
(`.scratch/cmp/`), so the statement comparison is immediate; both theorems of the solution print
`[propext, Classical.choice, Quot.sound]`.

**Not** run: the comparator itself.  It needs `landrun` and `lean4export` (absent) and a Lake package
that can be built, and in this VM `/opt/mathlib` is root-owned, so `lake` fails with `permission
denied` on `/opt/mathlib/.lake/packages/plausible` (measured).  `lakefile.toml` was added for that
purpose and is likewise untested here; `Build.sh` stays the canonical build.

### `Build.sh` now compiles the comparator pair, and reports three buckets

The two comparator modules are in the build loop (so a statement drift between the challenge and the
library is a build failure), which changed the log naming: one log per module, named after its path
(`IETFree/IET` → `IETFree_IET.log`), and the module list is a single `mods` variable that the sorry
report reuses.  The report is now

```
declarations still depending on sorryAx: 6
  of which display-only statement files (Challenge, ChallengeWeak): 4
  of which the comparator challenge (Comparator/Challenge): 2
  of which the library (with ChallengeWeakSolved): 0
```

`formalization.yaml` gained `comparator_config: "comparator.json"` on its first main result, its
`status.scope` now counts the six sorries, and its review note quotes the right `Check.lean` count
(297).  The README has a "The comparator challenge" section.

## The comparator challenge, redesigned: the challenge is the self-contained file (this session)

The entry above ("The comparator challenge") describes the **first** design, in which
`Comparator/Challenge.lean` imported `IETFree.Irreducible` and restated the theorems over the
library's definitions.  That is superseded: a challenge that imports the library is too hard to check,
so the challenge is now `IETFree/ChallengeWeak.lean` itself — self-contained, `import Mathlib` only,
the file that was already the display statement.

### What is where now

| file | role |
|---|---|
| `IETFree/ChallengeWeak.lean` | the challenge: `import Mathlib`, own copies of `leftEnd`, `imageLengths`, `mkIETFun`, `mkIETEquiv`, `simplexMap`, `simplexVolume`, `unitMeas`, `UniqueErgodic`, `IsRigidByTranslations`, `IsIrreduciblePerm`, `MasurVeech`, `VeechRigidity`, `evalWord`; two theorems with `sorry` |
| `Comparator/Solution.lean` | the solution: a **verbatim copy** of those definitions, the same two statements, proved |
| `comparator.json` | `challenge_module: IETFree.ChallengeWeak`, `solution_module: Comparator.Solution`, the two theorem names, the three permitted axioms |

`Comparator/Challenge.lean` is deleted.  The duplication is the point: the comparator compares the
declarations used in the statements across the two environments, and a word-for-word copy is what makes
them the same declarations.  The solution's header says so, and says that it must be regenerated if
`IETFree/ChallengeWeak.lean` ever changes.

### The proof is a transport, and that is the new content

`mkIETFun_inv_left` is the library's theorem applied verbatim (the copies are the same definitions).
`main` needed two bridges, because the library states the hypotheses in a different form:

* `uniqueErgodic_iff` and `isRigidByTranslations_iff`: for `g : IET 0 1` and `f : ℝ → ℝ` with
  `⇑g = f`, the library's predicate on `g` (whose `^` is the group power) is this file's predicate on
  `f` (whose `^[·]` is the function iterate) — by `IET.pow_apply_iterate`, plus unfolding the two
  copies of `unitMeas`;
* `MasurVeech` here is stated for the map `mkIETFun lam π 0` with no simplex membership, the library's
  for the exchange `mkIET1 lam π h` with `(h : lam ∈ simplex d)`; the missing hypothesis is supplied
  a.e. by `simplexVolume_compl_simplex`;
* the conclusion is transported by rewriting the two `Equiv`s with `Equiv.ext fun _ => rfl` (the copies
  of `mkIETEquiv` differ only in the `right_inv` proof).

### Verification

Both modules compile; `#check @ChallengeWeak.main` and `#check @ChallengeWeak.mkIETFun_inv_left` with
`pp.universes`/`pp.explicit` are **byte-identical** between `IETFree/ChallengeWeak.lean` and
`Comparator/Solution.lean` (`.scratch/cmp/`); both solution theorems report
`[propext, Classical.choice, Quot.sound]`.

Still not run: the comparator itself (`landrun`, `lean4export` absent; `/opt/mathlib` root-owned, so
`lake` cannot build here — measured).  `lakefile.toml` is unchanged and untested for the same reason.

### `Build.sh` is back to two buckets

`Comparator/Challenge` left the module list, so the report is again

```
declarations still depending on sorryAx: 4
  of which display-only statement files (Challenge, ChallengeWeak): 4
  of which the library (with ChallengeWeakSolved): 0
```

`Comparator/Solution` stays in the build, so a drift between the challenge file and the library breaks
the build.  `formalization.yaml` (`status.scope`) and the README were updated to match.

## The comparator challenge, third design: the definition hole does the work (this session)

The two entries above ("The comparator challenge" and "... redesigned") are **superseded**.  The
first made the challenge import the library, which is what the owner rejected; the second made the
solution a copy of the challenge's definitions, which is what the owner rejected ("you shouldn't need
to copy in the solution file all the API that is already in the module; what matters is only that the
exact same theorem is proved").  Both are gone: `Comparator/Solution.lean` is deleted.

### What the comparator actually compares, read off its source

`Comparator/Compare.lean` + `Comparator/Util.lean` + `Comparator/Axioms.lean` (master, checked against
the README): for each name in `theorem_names` it compares the two statements (`ConstantVal`: name,
universe parameters, type) and walks the type's constants; for each name in `definition_names` it
compares statement *and* `safety` but **not the body**; for every other constant it reaches — through
type, value (`value? (allowOpaque := true)`, so proofs included) and the ctor/`all` fields of
inductives — it requires the *same* `ConstantInfo`, i.e. same type **and same value**.  `Expr`'s `BEq`
is `Expr.eqv`, so binder names and `mdata` are ignored; everything else is not.  It then checks the
solution's proofs and definition holes for unpermitted axioms and replays the solution into the kernel.

Consequence: a challenge can only be accepted if it re-declares the library's declarations verbatim —
*including the proofs stored inside definitions* — except for the target theorems and the definitions
listed as holes.  That is the whole design below.

### What is on disk

| file | role |
|---|---|
| `comparator.json` | challenge `Comparator.Challenge`, solution `IETFree.ChallengeWeakSolved`, `theorem_names = [mkIETFun_inv_left, ChallengeWeakSolved.main]`, `definition_names = [mkIETEquiv]`, the three permitted axioms |
| `Comparator/Challenge.lean` | the challenge: `ChallengeWeakSolved.main` with `sorry` |
| `Comparator/Challenge/*.lean` | six **prefixes** of library modules, verbatim except for the `import` lines: `CutSet` (618), `CutSetMeasure` (585), `IET` (1034), `Diophantine` (49), `MeasureTools` (674), `Irreducible` (66) |
| `Comparator/gen.sh` | regenerates them (marked-string cut points, then `sed` on the imports) |
| `Comparator/Check.lean` | the comparator's algorithm on the two `.olean`s — `Build.sh` runs it and fails on any difference |
| `Comparator/README.md` | the same story for a reader of the repository |

The solution is the library: `ChallengeWeakSolved.main` in `IETFree/ChallengeWeakSolved.lean`, and the
left-inverse law `mkIETFun_inv_left` in `IETFree/IET.lean`.

### The private-core obstruction, and why `mkIETEquiv` is a definition hole

Copies must reproduce *values*, and the library's `mkIETEquiv` proves its two inverse laws through the
`private` core `mkIETFunCore` (`IET.lean:477`-`591`).  A private declaration's name is
`_private.<module>.<n>.<name>`, so it is different in every module: no challenge file can ever declare
the same constant, and the comparison of `mkIETEquiv`'s body fails at `mkIETEquiv._proof_1` (the
right-inverse auxiliary) and then at the private core itself.  Measured, not guessed: with
`definition_names` emptied, `Comparator/Check.lean` prints `differs: mkIETEquiv._proof_1`.

The fix is the comparator's *definition hole* mechanism, as the owner suggested: listing `mkIETEquiv`
in `definition_names` makes the comparator skip its body, while still requiring the same statement
and safety, kernel acceptance and axiom-cleanliness.  The challenge keeps showing the library's body
for the reader.  The alternative — exempting `mkIETEquiv._proof_1` by name in `theorem_names` — also
works and keeps the body compared, but it hard-codes an auto-generated auxiliary name; not taken.

This replaced the earlier plan of making `mkIETFunCore` public in `IET.lean` (which worked, and made
the check pass, but is a library change; reverted at the owner's request, the library is now exactly
as it was).

### Verification

`Comparator/Check.lean` (a real implementation of the algorithm above, `deriving BEq` for
`ConstantInfo` and all) reports `declarations compared: 34324`, no difference, solution axioms
`[Classical.choice, Quot.sound, propext]`.  Mutation tests: `simplex`'s body changed in the challenge →
`differs: simplex`; `w ≠ 1` → `w = 1` in the challenge's `main` → `the statement differs:
ChallengeWeakSolved.main`; `definition_names` emptied → `differs: mkIETEquiv._proof_1`.  The real
comparator was **not** run: `landrun` and `lean4export` are absent, and `lake` cannot build a package
here because `/opt/mathlib` is root-owned.

`Build.sh` compiles the six challenge modules and `Comparator/Challenge`, then runs the check; the
sorry report is back to three buckets, now

```
declarations still depending on sorryAx: 5
  of which display-only statement files (Challenge, ChallengeWeak): 4
  of which the comparator challenge (Comparator/Challenge): 1
  of which the library (with ChallengeWeakSolved): 0
```

`Check.lean` is unchanged (297 axiom lines), `formalization.yaml` revalidates against the v0.4 schema,
and the README's correspondence table still matches the `alignment` block.

## The comparator challenge, fourth design: the owner's own `ChallengeWeak.lean` (this session)

The three entries above are **superseded**.  The owner rewrote `IETFree/ChallengeWeak.lean` and asked
for it to *be* the challenge, so the third design's copies (`Comparator/Challenge/`, `gen.sh`) are
dead, and `Comparator/Solution.lean` is long gone.

### What the owner's file does, and the three things I had to change in it

The file declares, at the root namespace, the library's names with the library's text: `leftEnd`,
`imageLeft`, `translationVector`, `imageLengths`, `leftEnd_zero`, `idxSet`, `idx`, `mkIETFun`,
`simplexRegion`, `simplexMap`, `simplexVolume`, `unitMeas`, `IsIrreduciblePerm`, `Gen`, `genX`,
`evalWordEquiv`; and four declarations that cannot be the library's, `UniqueErgodicFun`,
`IsRigidByTranslationsFun`, `MasurVeechFun`, `VeechRigidityFun` (the library's forms are for
`f : IET 0 1`); `mkIETEquiv := sorry` (a definition hole), the statement `coe_mkIETEquiv`, and
`main`.  Four trivial or forced edits:

* a trailing `end ChallengeWeak` with no `namespace` (the declaration must be at the root: comparator
  matches declarations *by name* against the library's) — removed;
* `main` was stated with `MasurVeech`/`VeechRigidity`, which the file does not define (it defines the
  `…Fun` versions) — fixed to `MasurVeechFun`/`VeechRigidityFun`;
* `UniqueErgodic` and `IsRigidByTranslations` would have been **collisions with a different
  statement**: the library's are `IET 0 1 → Prop`, these are `(ℝ → ℝ) → Prop`, and the solution
  (which imports the library) could never declare them.  Renamed `…Fun`, like the two hypotheses;
* `idx` had an inlined body (`Finset.univ.filter …`) where the library has `idxSet`.  Same type, so
  the comparator would only have said `differs: idx` — and, worse, a *different definitional height*,
  which is part of `ConstantInfo` (`ReducibilityHints` is compared!), so `mkIETFun`, whose body uses
  `idx`, would have differed too.  `idxSet` and `idx` are now the library's text, and `leftEnd_zero`
  (used by `idx`'s proof) with them.

Also needed, for the same reason: `evalWordEquiv` must be over `Gen`, not over `Fin 2` (the
abbreviation is part of the elaborated type), and `genX` has to be declared before it, because the
library's `evalWordEquiv` re-uses the auxiliary proof `genX._proof_1` (the proof of `0 < 2` inside
`0 : Gen`) — without `genX` the elaborator creates `evalWordEquiv._proof_1` and the two bodies differ.

Measured after the fixes (`cmpdecls.lean` in `.scratch/`): 30 declarations identical, and exactly
three with the same type and a different value — the hole `mkIETEquiv` and the two targets
`coe_mkIETEquiv`, `main`.  That is the whole design.

### The solution

`IETFree/ChallengeWeakSolved.lean` gained, at the root: the four `…Fun` predicates (the challenge's
text, so that comparator sees the same constants), `coe_mkIETEquiv` (from `mkIETEquiv_apply`), and
`main` (the challenge's statement).  Inside its namespace: `uniqueErgodic_iff`,
`isRigidByTranslations_iff` (both `simp only [..., IET.pow_apply_iterate]`), `masurVeech_of_fun` and
`veechRigidity_of_fun` (from the challenge's hypotheses, using `simplexVolume_compl_simplex` and
`⇑(mkIET1 lam π h) = mkIETFun lam π 0`, which is `rfl`), and the previous `main`, renamed
`main_of_library`, with its proof untouched.  The root `main` is four lines: transport the hypotheses
and quote `main_of_library`.  Axioms: `[propext, Classical.choice, Quot.sound]` for all of them.

### Configuration, build, and checks

`comparator.json`: challenge `IETFree.ChallengeWeak`, solution `IETFree.ChallengeWeakSolved`,
`theorem_names = [coe_mkIETEquiv, main]`, `definition_names = [mkIETEquiv]`.  `Build.sh` no longer
compiles the copies (`Comparator/Challenge*` left the module list); its sorry report is

```
declarations still depending on sorryAx: 5
  of which the display-only statement file (Challenge): 2
  of which the comparator challenge (ChallengeWeak): 3
  of which the library (with ChallengeWeakSolved): 0
```

`Comparator/Check.lean` (the comparator's algorithm on the two compiled modules) reports
`declarations compared: 32661`, no difference, solution axioms `[Classical.choice, Quot.sound,
propext]` — down from 34324 because the challenge no longer drags in the cut-set machinery.  The real
comparator is still not runnable here (`landrun`, `lean4export` absent; `/opt/mathlib` root-owned).

`formalization.yaml` (`alignment`, `status`, `review`) was updated for the rename
`ChallengeWeakSolved.main` → `main` (the root theorem, in the challenge's words; `main_of_library` is
the library-hypothesis form) and the README's correspondence table regenerated; both checkers
(`readme_check.py`, the v0.4 schema) report no problem.

## The comparator challenge, fifth design: the files move up, and two renames (this session)

The owner's instructions this round, and what they needed.

### The two statement files moved one directory up

`IETFree/Challenge.lean` → `Challenge.lean` and `IETFree/ChallengeWeak.lean` → `ChallengeWeak.lean`, so
the modules are `Challenge` and `ChallengeWeak`; they import only `Mathlib` and are imported by nothing,
so nothing else had to change.  `Build.sh`'s module list starts with them, `comparator.json` names
`ChallengeWeak`, `lakefile.toml` gained `lean_lib`s for both (their old `.olean`s were removed), and
every live reference (the READMEs, `formalization.yaml`, `IETFree.lean`'s docstring, `Build.sh`'s comments)
was updated.  `Challenge.lean`'s docstring no longer calls itself "the comparator target" — its
*statements* are still frozen, but the target is `ChallengeWeak.lean`.

### `mkIETEquiv_apply` → `coe_mkIETEquiv`

The owner's criterion: `_apply` is for a lemma about a value at a point.  This one states the equality
of *functions* `⇑(mkIETEquiv lam π a) = mkIETFun lam π a`, i.e. it is a coercion lemma.  Renamed in
`IET.lean` (with a docstring saying so), its three uses and the frozen-block comment updated, and the
solution's own `coe_mkIETEquiv` — which it had to declare in the fourth design — deleted: the library's
is now exactly the declaration the challenge's target names.

Scan for the same defect: all 25 `theorem`/`lemma *_apply` of the library were read; every other one is
`X … (point) = …` (`mkIET1_apply`, `toIET_apply`, `splitMap_apply`, `AffineMap.sum_apply`,
`shiftPerm_apply`, …).  Two borderline names, left alone: `IET.coeHom_apply`
(`IET.coeHom e = e.toEquiv`, and `coeHom` is a bundled `→*`, so "the value at `e`" is the standard
reading) and `invSubstGen_substGen_apply (i : Gen)` (a value on the generator `FreeGroup.of i`, with no
application at all — `invSubstGen_substGen_of` would be better).

### `Gen` and `genX` out of the challenge, `evalWordEquiv` over `Fin 2`

The challenge no longer mentions `Gen` or `genX`, and its `evalWordEquiv` is over `Fin 2`.  Two
consequences, both measured:

* the library's `evalWordEquiv` had to follow: over `Gen` its *type* was `FreeGroup Gen`, and `Gen` is an
  abbrev, which is not the same expression as `FreeGroup (Fin 2)` — comparator compares expressions, not
  their unfoldings.  `MeasureTools.lean` now states
  `evalWordEquiv (w : FreeGroup (Fin 2)) (f g : Equiv ℝ ℝ)`;
* and it had to move *before* `abbrev Gen`: the library's body re-uses the auxiliary proof
  `genX._proof_1` for `0 : Fin 2` (Lean deduplicates those auxiliaries by type), whereas a challenge
  without `genX` creates `evalWordEquiv._proof_1`.  Declared before `genX`, both environments create
  `evalWordEquiv._proof_1` and the bodies agree — so no new definition hole was needed.  Measured:
  `evalWordEquiv` and `evalWordEquiv._proof_1` identical.

`coe_mkIETEquiv` now has a docstring in both files; the challenge's says what the hole would otherwise
allow (an arbitrary permutation of `ℝ` of the right type).

### State

`./Build.sh` green; `Comparator/Check.lean` OK with `declarations compared: 32661`; the sorry report is
unchanged (5 = 2 + 3 + 0).  All 33 declarations of `ChallengeWeak` are either identical to the library's
(30) or one of the three intended exceptions (the targets `coe_mkIETEquiv`, `main` and the hole
`mkIETEquiv`).  `formalization.yaml` and the README's correspondence table were regenerated (`main` is at
`ChallengeWeakSolved.lean:302`).

## `evalWordEquiv` moves to the solution file (this session)

`evalWordEquiv` and its API (`evalWord_toEquiv`) left `MeasureTools.lean` for
`IETFree/ChallengeWeakSolved.lean`: the definition is not a library tool but the bridge between
`evalWord` (words in two *exchanges*, which is all of Section 3) and the statement of Theorem 1.1
(words in two *permutations of `ℝ`*, where no `IsIET` datum is available).  Inside `IETFree/` it now
appears only in the solution file; `MeasureTools` keeps `evalWord` and its API, and its module
docstring says where the `Equiv`-valued version went.  Its `#print axioms` line moved from
`Check.lean` (which does not import the solution) to the solution file's own axiom report.

Nothing about the comparator changes: the declaration keeps its name, type and value, so the check is
still OK with `declarations compared: 32661`.  Worth recording for the next session: the auxiliary proof
inside `evalWordEquiv` (`0 < 2`, for `0 : Fin 2`) is created as `evalWordEquiv._proof_1` in both
environments — Lean's deduplication of those auxiliaries only reaches declarations of the *same* module,
so moving the definition out of `MeasureTools.lean` also removed the reuse of `genX._proof_1` that had
forced the earlier reordering (the definition is now the first declaration of
`ChallengeWeakSolved.lean`, which keeps it safe from a future `0 < 2` proof in that file).

## The genuine comparator was run, with `fake-landrun` (this session)

The owner asked whether `lean4export` could be installed to run the real comparator with the
repository's `fake-landrun.sh` (comparator's README, "Development").  Yes, and it works.

### The version problem, and the revision pair

Comparator's `master` and the `lean4export` it pins are on Lean **v4.35.0**; this library is Lean
**4.33.1** (its Mathlib is built for it, and oleans do not cross Lean versions).  `lean4export` has a
`v4.33.0` tag (`15f6055`), and comparator has exactly one commit whose `lean-toolchain` is v4.33:
**`3927ad3`**, which pins `lean4export` at that tag.  Built with the local toolchain (its
`lean-toolchain` rewritten to `v4.33.1`), both compile unchanged:

```
lake build comparator lean4export     # in .scratch/cmp/comparator, ~15 s
```

### What had to be shimmed, and what did not

* `landrun`: replaced by the repository's own `scripts/fake-landrun.sh` (unsandboxed).  `landrun` is not
  installed here; the shim is the tool's documented development path.
* `lake build`: **not** shimmed.  The comparator runs `lake build <module>` in its working directory,
  which fails in `IET2/` because `lakefile.toml` requires Mathlib from the registry (it clones Mathlib
  and even moves the toolchain to v4.36.0-rc2).  Instead a throw-away Lake project in `.scratch/lake/`
  requires Mathlib **by path** (`path = "/opt/mathlib"`), symlinks `ChallengeWeak.lean` and `IETFree/`,
  and copies `comparator.json`; Lake then builds both modules from source against the prebuilt Mathlib
  in about a minute (its dependencies are cloned once into that project's `.lake/packages`, and the
  shared cache `~/.cache/mathlib` is 441 MB).
* `lean4export`, the comparison, the axiom check and the kernel replay: genuine.

### The result, and the mutation check

```
Exporting #[coe_mkIETEquiv, main, …, mkIETEquiv] from ChallengeWeak
Exporting #[coe_mkIETEquiv, main, …, mkIETEquiv] from IETFree.ChallengeWeakSolved
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

exit status 0.  Not vacuous: with `w ≠ 1` changed to `w = 1` in `ChallengeWeak.lean`'s `main`, the same
command exits 1 with `uncaught exception: Challenge and solution theorem statement do not match:
'main'`; the tree was then restored and rebuilt.

Logs: `.scratch/cmp/comparator_run.log` and `.scratch/cmp/comparator_mutant.log`.  The recipe is in
`Comparator/README.md`; `Comparator/Check.lean` stays as the cheap always-on guard (32 661 declarations,
no difference), since the genuine run is a minute of exports plus a kernel replay of the whole
solution.

## `Comparator/run.sh`, and `Challenge.lean` at the root namespace (this session)

### One script for the comparator

`Comparator/run.sh` is the recipe of the previous entry, end to end: it fetches and builds
comparator `3927ad3` + `lean4export` (rewriting the tools' `lean-toolchain` to the *installed* Lean,
and skipping that if a stamp says they are already built), sets up the Lake project, builds
`ChallengeWeak` and `IETFree.ChallengeWeakSolved`, and runs the comparator with the repository's
`fake-landrun.sh` unless a real `landrun` is on `PATH`.  Knobs: `COMPARATOR_REV`, `COMPARATOR_WORK`
(default `.scratch/cmp`), `MATHLIB` (path to a Mathlib checkout; empty means "let `lakefile.toml`
resolve Mathlib itself"), `COMPARATOR_LANDRUN`; `--rebuild` forces the tools to be rebuilt.

Two things the script has to do that are easy to miss:

* the projects it builds in must have a `lean-toolchain` *before* the first `lake build`: Lake derives
  it from the required Mathlib, writes it, and then refuses to continue in the same process ("no Elan
  detected; you will need to manually restart Lake", exit 4).  The script writes it up front and
  retries the build once if needed;
* the paths must be absolute: the script `cd`s into the project before invoking the comparator, which
  is *inside* `.scratch`.

Tested from scratch (`rm -rf .scratch/cmp/lake`, then `MATHLIB=/opt/mathlib ./Comparator/run.sh`):
2 min 22 s including the fetch and the two Lake builds, ending in `Lean default kernel accepts the
solution` / `Your solution is okay!`, exit 0.

### `Challenge.lean` follows `ChallengeWeak.lean`'s strategy

* its declarations are at the **root** namespace (the `namespace Challenge` wrapper is gone), so its
  names are the library's, as in `ChallengeWeak.lean`;
* the inverse is no longer constructed: `mkIETFun_inv_left` and the `Equiv` literal are replaced by the
  **definition hole** `mkIETEquiv := sorry` and the statement `coe_mkIETEquiv` (both with docstrings),
  exactly the strategy of the comparator challenge.  It has three `sorry`s now;
* its `Equiv`-valued word evaluation is called `evalWordEquiv`, the library's name for it — `evalWord`
  alone would have been a root name colliding (with a different type) with the library's `evalWord` on
  `IET 0 1`.

`IET.lean` is untouched (it still proves `mkIETFun_inv_left`, which the library needs), so the frozen
block's comment "they mirror `Challenge.lean`" is now one lemma wider than the file it mirrors; noted
in §State.  As instructed, only `Challenge.lean` (and `ChallengeWeak.lean`, whose docstring changed)
were recompiled — the next full `./Build.sh` will print `sorryAx: 6` (3 + 3).

## `IETFree.lean` regenerated with `mk_all` (this session)

`IETFree.lean` is now the standard umbrella: its import list is what `lake exe mk_all --lib IETFree`
writes (one `import IETFree.<Module>` per module, sorted, 31 lines), so it also pulls in
`ChallengeWeakSolved` and `Check`, which the hand-written list left out.  The copyright header and the
module docstring are kept around it, and the docstring now says the list is generated (a regeneration
replaces the whole file, so the docstring has to be put back).  Root module compiles (77 lines).

**How it had to be run.**  `lake exe mk_all` cannot be *built* in this VM: Mathlib's `mk_all`
executable imports `Cli.Basic`, and the prebuilt `/opt/mathlib` has no build of the `Cli` package;
building it wants to write `.c.o` files into `/opt/mathlib/.lake/build/ir/`, which is read-only
(`error: unable to open output file '…/DirectoryDependency.c.o.export': Permission denied`).  What
worked is the tool's own generator function, run interpreted from a scratch project that requires
Mathlib by path (`.scratch/mkall`, `lean --run` on a 12-line file that imports
`Mathlib.Util.GetAllModules` and calls `getAllModulesSorted false "IETFree"`, then writes
`"\n".intercalate (files.map ("import " ++ ·))` — the exact body `mk_all` builds); its 31-module output
was installed verbatim.  On a machine where `lake` can build Mathlib's `cli`, the real command is
`lake exe mk_all --lib IETFree` (add `--check` to only verify).

## The repository is a genuine Lake project (this session)

The owner replaced `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` with local versions: Lean
4.33.1 (the toolchain installed here), Mathlib pinned at the `v4.33.1` tag (rev `0df444a3…`, whose
sources are byte-identical to the prebuilt `/opt/mathlib` — checked with `diff -rq`), the mathlib linter
set, `autoImplicit = false`, `warn.sorry = false`.  The files agree with each other: same package name
(`IETFree`), the manifest's `inputRev` is the lakefile's `rev`, and the toolchain matches the one
`lean` reports.

Three things were needed to make `lake build` work, all small:

* `IETFree/IET.lean`: two declarations relied on **auto-implicit** binders — `instance
  BlockIdx.instNeZeroLen (I : BlockIdx n)` and `abbrev kFin (I : BlockIdx n)` — which
  `autoImplicit = false` rejects.  `n` is now an explicit `{n : ℕ}`; no statement changes;
* `IETFree/BlockData.lean`: after `end Transfer`, nine declarations used `π σ q₀` as auto-implicit
  variables (they were bound by the `variable` line *inside* `Transfer`).  A
  `variable {π : …} {σ : …} {q₀ : …}` line was added after the section;
* `lakefile.toml`: the two statement files (`Challenge.lean`, `ChallengeWeak.lean`) are root modules
  outside the `IETFree` library's globs, so `lake build ChallengeWeak` — the comparator's own build step,
  and what `Comparator/README.md` documents — was `unknown target`.  Two `[[lean_lib]]` entries were
  added and `defaultTargets` extended, so `lake build` builds all three libraries.

`lake build` then succeeds from a clean `.lake`: 8742 jobs, exit 0.  **103 warnings** remain, all from
the linter set the lakefile enables and all cosmetic: 68 `longLine` (lines over 100 columns, spread over
~20 files) and 32 `linter.style.show`.  Not touched this session.

**How the build was made to work in this VM.**  Lake cannot use `/opt/mathlib` as a package here
(root-owned, read-only), so the genuine build was run against the *cloned* Mathlib at the pinned
revision with its `.lake/build` directories symlinked to the prebuilt ones (`/opt/mathlib/.lake/build`
and `/opt/mathlib/.lake/packages/*/.lake/build`), the cloned sources' mtimes pushed back so that nothing
looks stale, and `Cli` (no prebuilt build) built by Lake itself.  None of that is needed on a machine
with a normal Mathlib checkout: `lake exe cache get && lake build`.

`Build.sh` now passes the lakefile's options to `lean` (`-DautoImplicit=false`,
`-DrelaxedAutoImplicit=false`, `-DmaxSynthPendingDepth=3`, `-Dlinter.mathlibStandardSet=true`) — keeping
`warn.sorry` enabled, since the sorry count is computed from those warnings — and is green with them
(6 sorries, comparator check OK).  `.lake/` was added to the root `.gitignore`.

## The linter warnings are all gone: `lake build` is warning-free (this session)

Starting point: the genuine Lake project built green but with **103 warnings** from the linter set the
owner's `lakefile.toml` enables — 68 `longLine` (a line over 100 *code points*: `g̃` counts two, so
`awk length` overestimates), 32 `linter.style.show`, one unscoped `set_option maxHeartbeats`
(`BlockData`), one `set_option maxHeartbeats … in` without the comment the linter asks for
(`BlockLemma`), and one missing copyright header (`InvariantInterval.lean`).  All are fixed and both
builds are clean:

```
lake build      # from a clean .lake: 8742 jobs, exit 0, 0 warnings, 1 m 15 s
./Build.sh      # 35 ok lines, 0 warning lines, sorryAx 6 (3 Challenge + 3 ChallengeWeak, library 0)
MATHLIB=/opt/mathlib Comparator/run.sh   # still `Lean default kernel accepts the solution`, exit 0
```

**`longLine`.**  All 68 sites are split.  For prose (`/-!` paragraphs, `--` comments, docstrings) a
script rewrote each over-long line as prose at ≤100 code points, continuing `--` comments with `-- `
and re-wrapping `/-!` paragraphs *with their existing indentation* (that indentation is Markdown: a
bullet's continuation line must keep its two spaces).  Nine sites were *code* and were done by hand:
argument lists wrapped after a comma, `:= by` pushed onto its own line (`leftEnd_blockLam`, where the
missing space in `j:= by` was fixed at the same time), and one `have` split at the `=` of its
statement.  `Presentation.lean`'s two `(mkIET1 …)⁻¹ (leftEnd …)` lines break after `⁻¹`.  Checked
afterwards: no line of any of the 36 `.lean` files exceeds 100 code points.

**`show` → `change`.**  31 sites, one edit per site: the first `show` on the flagged line (the
linter's column) becomes `change`.  That is exactly right — the linter only fires when the goal
*changed*, i.e. when the two types are definitionally equal — and `change … = _` keeps the `_`
placeholder working.  The 32nd site, `SubintervalTransfer.lean:106`, is not mechanical: it was
`show (fun i => (Fin.snoc … z S) i.castSucc) ∈ Z'` followed by
`rwa [show (fun i => …) = z from by funext i; rw [Fin.snoc_castSucc]]`, and changing both keywords
does not compile (`rw` no longer finds the pattern, `simpa only` gives a type mismatch).  What works
is `have hcast' : (Fin.snoc z S ∘ Fin.castSucc : Fin r → ℝ) = z := by funext i; simp [Fin.snoc_castSucc]`,
then `change (Fin.snoc z S ∘ Fin.castSucc : Fin r → ℝ) ∈ Z'`, then `rwa [hcast']`.

**The two stray `maxHeartbeats`.**  `BlockData.lean`'s unscoped `set_option maxHeartbeats 1000000`
and `BlockLemma.lean`'s `set_option maxHeartbeats 1000000 in` are deleted, not commented: both files
elaborate at the default 200 000 heartbeats, which the clean build above proves.  The two in
`SingularityBound.lean` keep theirs — those ones carry the explanatory `--` comment the linter wants.

**A fourth linter appeared at the end: `linter.style.emptyLine`.**  It fires on a blank line inside a
command, but it *returns early whenever the file has any other diagnostic*, so it was invisible while
the `show`/`longLine` warnings were there, and it also only triggers for a command whose text holds
at least two blank lines (one of which may be inside its docstring, since the docstring is excused but
still counted).  The single offending blank line — right after `:= by` in
`absolutelyContinuous_map_rescaleSub` — is removed.  Keep this in mind before declaring a tree
warning-free from an incremental build: the empty-line warnings only *appear* once a file has no
other warning, so a warning-free claim needs one clean build from `rm -rf .lake/build`.

**Two approaches that failed and were reverted** (the pristine pre-edit copy of all 36 `.lean` files is
`.scratch/bak/warnfix/`; nothing else needed it):

* a naive word-splitter over all 68 long lines: it emitted 1–3-word artefact lines (`and`, `the`) and
  broke two `--` comments (a continuation line without `--` in `BlockEndpoints.lean`, which
  `lake build` reports as `unknown tactic`, and a `--` run in `Check.lean`);
* a "reflow the paragraph" pass: it duplicated `/-!` markers and did not terminate.

**Nothing but comments was meant to change, and nothing but comments and the `show`s did.**  Verified
by stripping comments and blank lines from all 36 files and diffing against `.scratch/bak/warnfix/`:
the code differences are exactly the 31 `show` → `change`, the `SubintervalTransfer` rewrite above,
the two deleted `maxHeartbeats` lines, and pure line-break changes (the wrapped argument lists, one
`exact ⟨fun h => by_contra fun hcon =>` split after `=>` in `BlockDatum.lean`).  `Challenge.lean` and
`ChallengeWeak.lean` have **no** code change at all — only docstrings — so the frozen statements and
the comparator pair are untouched, which is what the comparator run above confirms.

---

## Session: audit of Yoccoz's survey and blueprint for Masur–Veech (not the free-group paper)

**Task.** Audit `Yoccoz/UPL13956_yoccoz.pdf` (J.-C. Yoccoz, *Continued Fraction Algorithms for
Interval Exchange Maps: an Introduction*, 35 pp.) as a proof of the Masur–Veech theorem, and write
the formalisation blueprint. Deliverable: `blueprint.md` at the repository root (Part I audit,
Part II blueprint). Extracted text: `.scratch/yoccoz/yoccoz.txt`. Nothing in `IETFree/` was touched.

**The theorem is proved in source §2–§4.4 (pp. 3–20); source §5–§6 (suspensions, Teichmüller flow,
Zorich acceleration, pp. 20–34) are NOT used by it, and source §3.4 (the Denjoy model) is not used
either.** The proof is Kerckhoff's, in Yoccoz's simplification; it needs no infinite ergodic theory.

**Five places where the printed proof does not close** (all repairable; complete replacement proofs
are in `blueprint.md` §10):

* **last paragraph of §4.4, p. 20** is invalid: Lemma 6 gives one-step coverings, not infinitely
  many balanced times for a.e. path, and Lemma 2 contracts *some* extension which the path need not
  follow. Replacement: the nested-cylinder Borel–Cantelli lemma, `blueprint.md` §10.5 (hypotheses
  (H1) = the Rauzy nesting lemma, (H2) = Lemma 6 + Lemma 2). This is the one real gap.
* **Corollary 5, p. 14** has the matrix product reversed: with `λ = V⁽¹⁾⋯V⁽ⁿ⁾λ⁽ⁿ⁾` the recursion must
  be `C⁽ⁿ⁾ = V⁽¹⁾⋯V⁽ⁿ⁾(R*₊)^A`, not `V⁽ⁿ⁺¹⁾C⁽ⁿ⁾`. The V's do not commute.
* **Proposition 4.3, p. 13** (every name infinitely often) is true but the printed proof interchanges
  `π_ε` and `π_{1-ε}` at the last step; a type-`ε` step modifies `π_{1-ε}`, verified on an explicit
  `d = 4` example. Do not transcribe it.
* **Proposition 4.4, p. 15**: "`T_μ` is immediately seen to be an i.e.m" is **false** for
  `μ ≠ c·Leb` (`H_μ` is not affine on cells). The needed conclusion `λ(μ) ∈ ⋂ₙ C⁽ⁿ⁾` is true, by the
  tower decomposition of `T` itself; no conjugacy and no i.e.m structure on `T_μ` is involved.
* **Proposition 4.4** never proves that `μ ↦ λ(μ)` is injective, which is what the "in particular"
  needs. Proof: `det Q(γₙ) = 1` plus refinement of the tower partitions with mesh `→ 0` (Cor. 2).

**Simplification found while auditing (important for scope).** Only two small pieces of source §3 are
needed: *Keane ⇒ no periodic orbit* (part 1 of Theorem 3.2, ~200 lines) and hence non-atomicity of
invariant measures. **Keane minimality (part 2) and Proposition 3.3 (rational independence) are not
needed**: the ray criterion is applied with **closed** cones, and the tower formula gives
`λ(μ) ∈ ⋂ₙ closure C⁽ⁿ⁾` with entries `μ(I⁽ⁿ⁾_β) ≥ 0` — strict positivity, i.e. full support, i.e.
minimality, is never used. `MasurVeech` as frozen does not ask for minimality either.

**Fidelity.** `d ≥ 2` in `MasurVeech` is a genuine hypothesis: the printed theorem is false at
`d = 1` (admissible is vacuous, the exchange is the identity). `IsIrreduciblePerm π` is exactly
source 2.5 for `(π₀,π₁) = (id,π)`, and `mkIET1 lam π` has `π = π₁∘π₀⁻¹` (checked against `leftEnd`
and `imageLeft`). `UniqueErgodic` is the Birkhoff-uniform form, the source proves the
unique-invariant-measure form; the bridge is a separate task (blueprint §9 R8.2).

**Sizes.** Blueprint estimates 11 700–16 000 lines in ten modules `IETFree/RV/*`, critical path
`Basic → Step → Path → Balance → Shrink → Main`. Open decisions for the author are listed in
`blueprint.md` §13 (which conclusion is authoritative; where the code lives; full Prop. 4.4 or only
the ray criterion; §5–§6 now or never; `d = 2` smoke test; freeze policy).

### Author's rulings on the Masur–Veech blueprint (supersede the questions of the first draft)

Six rulings, given after the audit; `blueprint.md` has been rewritten to them. **No Lean has been
started**, by explicit instruction.

1. **Conclusion: uniqueness of the invariant probability measure.** The Birkhoff-averages form
   (`IETFree.MasurVeech`) is to be *deduced later*; that deduction "will require a substantial
   argument" and is not a priority. So `UniqueErgodic` is not a target and is not copied; the
   theorem is `∃! μ : ProbabilityMeasure ℝ, Invariant μ T` a.e. This is blueprint D1 (deferred).
2. **Location: a separate top-level library**, not `IET2/IETFree/RV/` — another project, and it
   spares build time; may be merged with `IET2/` later. Existing API may be **copied**, notably
   `IET.lean` and the *shape* of `IETDatum`. The main structure records **two bijections**
   `piTop`, `piBottom` between the alphabet and `Fin n` instead of one permutation; the exchange is
   the existing single-permutation API applied to `piTop ∘ piBottom⁻¹`. Blueprint proposes
   `MasurVeech/` with its own `lakefile.toml`, `lean-toolchain` (4.33.1), `lake-manifest.json`,
   Mathlib-only imports, and lengths indexed by the **alphabet** (needed so that
   `λ = V λ̂` stays an identity of `α`-indexed vectors after the step; the only place `piBottom`
   touches lengths is `toIET_eq_mkIET1`).
3. **No full Proposition 4.4**; shortest path to a.e. unique ergodicity, i.e. the ray criterion
   (Lemma 1–6 + nested cylinders + tower formula + injectivity). No orbit-coding lemma.
4. **Source §5–§6 confirmed out of scope**; they are not in the dependency graph.
5. **No `d = 2` case analysis**; the general proof covers `d ≥ 2`.
6. **Freeze policy confirmed**: `IETFree.MasurVeech` and every other `IETFree` declaration stay
   byte-identical; the new library proves its own statement; the bridge to `IETFree` belongs to D1.

**Consequence worth remembering: source §3 leaves the critical path entirely.** With the measure
form as the target, Keane's theorem is needed neither for minimality (the tower formula is applied
with *closed* cones, so no full support is used) nor for non-atomicity (only D1's weak-limit
argument needs that, and only its easy half: Keane ⇒ no periodic orbit). Corollary 3 also becomes
unnecessary: "a.e. path is infinite" is pure measure theory (null hyperplanes). So the critical
path is `Basic → Step → Path → Balance → Shrink → Main`, and the estimate drops from 11 700–16 000
to 10 900–14 800 lines. `MasurVeech/Keane.lean` and `MasurVeech/Birkhoff.lean` are marked
deferred and are not part of the built library.

**Correction to the target statement (author's remark, same round).** Two points, both correct and
now reflected in `blueprint.md` §0, §9 R0.1, R8.1, §13 and Appendix C:

* `simplexVolumeOn` must **not** depend on `P`. Lebesgue measure on the simplex of $\alpha$-indexed
  length vectors is canonical: reindexing `Fin n → ℝ` along a bijection is an orthogonal map for the
  $\ell^2$ structure with the Dirac basis, so it preserves the measure, and every choice of
  bijection gives the same pushforward. It is `simplexVolumeOn α`, with
  `simplexVolumeOn_eq_map (P) : simplexVolumeOn α = (simplexVolume n).map (fun l a => l (P.piBottom a))`
  as a lemma, not as the definition of the statement.
* `(h : lam ∈ simplexOn α)` is **not an assumption**: a.e. point of `simplexVolumeOn α` is in the
  simplex (`ae_mem_simplexOn`). The `∀ h` in `IETFree.MasurVeech` exists only because `mkIET1`
  consumes `∑ lam = 1` as an explicit proof argument. The new statement therefore drops it:
  `∀ᵐ lam ∂(simplexVolumeOn α), ∃! μ : ProbabilityMeasure ℝ, Invariant μ (P.toIET lam)`, with
  `toIET` total — junk value off the simplex, exactly as `mkIETFun` already is. The equation lemma
  `CombData.toIET_eq_mkIET1` is stated on `simplexOn α` and is the only place the proof appears.

**Definition of `simplexVolumeOn` (author's challenge: it must be an $(n-1)$-dimensional measure).**
The earlier "reindexing is orthogonal for $\ell^2$" remark was about the *ambient* $n$-dimensional
Lebesgue measure and is not by itself an argument: the simplex is null for it. The precise
definition, now in `blueprint.md` §10.0, is

```lean
noncomputable def simplexVolumeOn (α : Type) [Fintype α] : Measure (α → ℝ≥0) :=
  (simplexVolume (Fintype.card α)).map (fun l a => l (Fintype.equivFin α a))
```

so it is literally the pushforward of the copied `simplexVolume`, which is the image of Lebesgue on
the open `simplexRegion` of $\mathbb R^{n-1}$ under the chart $v\mapsto(v_0,\dots,v_{n-2},1-\sum v)$
— a genuine $(n-1)$-dimensional measure, equal to $\frac1{\sqrt n}H^{n-1}$ on the simplex (the area
element is $\sqrt{\det(D\iota^{\mathsf T}D\iota)}=\sqrt n$; the constant is irrelevant, F5).

Independence of the chosen equivalence is the lemma `simplexVolume_map_perm`: for every
`σ : Equiv.Perm (Fin n)`, `(simplexVolume n).map (fun l i => l (σ i)) = simplexVolume n`. Proof by
charts, no Hausdorff API: `l ↦ (simplexMap n l) ∘ σ` is the chart that drops the coordinate
`a = σ⁻¹ last`, and the transition between the charts dropping `last` and dropping `a` is
`y_i = x_i` for `i ≠ a, last`, `y_a = 1 - ∑_{i≠a} x_i`, whose linear part is the identity with one
row replaced by `-1ᵀ` — adding the other rows makes it `-e_aᵀ`, so the determinant is `±1`.
(Hausdorff alternative: an ambient orthogonal map fixing `{Σ=1}` preserves `H^{n-1}` there.)

Consequently `simplexVolumeOn α` is a function of the alphabet only — not of `P` and not of any
bijection with `Fin n` — and `simplexVolumeOn_eq_map (P) : simplexVolumeOn α =
(simplexVolume n).map (fun l a => l (P.piBottom a))` follows, since the two reindexings differ by
`(Fintype.equivFin α).symm.trans P.piBottom`. (`Fintype.equivFin` and `Fintype.equivFinOfCardEq`
both exist in the pinned Mathlib.) Total mass is `vol (simplexRegion n) = 1/(n-1)!`; not normalised,
since every statement used is a.e. or a ratio. `ae_mem_simplexOn` then erases the proof argument
from the theorem's statement.

---

## Session: M0 of the Masur–Veech campaign — the statement spike (done)

**Author's instruction: "Let's go for M0."** M0 is the statement spike of `blueprint.md` §14: the
objects and the final statement must compile, with `toIET_eq_mkIET1` proved.

**Created `MasurVeech/` at the repository root** — a standalone Lake project, as ruled: own
`lean-toolchain` (4.33.1), `lakefile.toml` with a **path dependency on `/opt/mathlib`** (the
prebuilt read-only Mathlib of this VM), generated `lake-manifest.json`, Mathlib-only imports, and
the library `MasurVeech`. `lake build` is **green: 8714 jobs, exit 0, ~35 s warm, no warnings**
(`warn.sorry = false` is on, so the 8 `sorry`s are silent; two linter warnings about unused
`[DecidableEq α]` were removed by `omit`/dropping the binder). `.gitignore` gained
`MasurVeech/.lake/` and the stray-olean patterns.

**Copied API (verbatim except the import lines):** `MasurVeech/CutSet.lean`,
`CutSetMeasure.lean`, `IET.lean` from `IET2/IETFree` — 2241 lines, root namespace (the files use
`namespace CutSetData` / root, not `IETFree`), so a future merge with `IETFree` will need a
namespace pass. Deliberate: `IETFree.Irreducible.lean` is *not* copied; only `IsIrreduciblePerm` is
re-stated in `Basic.lean`.

**New modules.** `Basic.lean`: `IsIrreduciblePerm`, `simplexOn`, `simplexVolumeOn`
(`(simplexVolume (card α)).map (fun l a => l (Fintype.equivFin α a))`), `ae_mem_simplexOn`,
`simplexVolume_map_perm`, `CombData` with `piTop`/`piBottom`, `perm = piBottom.symm.trans piTop`,
`Admissible`, `lengthsInBottom`, `sum_lengthsInBottom`, `pos`, `j`, total `toFun`/`toIET` (junk `1`
off the simplex), `toIET_eq_mkIET1`, `inv`, `perm_inv`, `toIET_inv`, `IETDatum`.
`Step.lean`: `lastPos`, `last`, `rvType`, `rvStep` (sorry), `rvMat`, `rv_length` (sorry),
`rvStep_admissible` (sorry), `Path.Q`, `cone`, `simplexCyl`. `Main.lean`: `Invariant μ f :=
(μ : Measure ℝ).map ⇑f = μ` and the target `masurVeech_ae_unique_invariant`:
`∀ᵐ lam ∂(simplexVolumeOn α), ∃! μ : ProbabilityMeasure ℝ, Invariant μ (P.toIET lam)` — no
hypothesis on `lam`, `simplexVolumeOn` on the alphabet only, as ruled. Plus `Check.lean` (axiom
report) and the umbrella `MasurVeech.lean`.

**Axioms**: `CombData.toIET_eq_mkIET1`, `sum_lengthsInBottom`, `perm_inv` are
`[propext, Classical.choice, Quot.sound]`; `masurVeech_ae_unique_invariant` has `sorryAx`, as
expected at M0.

**Remaining `sorry`s (each a named task):** `ae_mem_simplexOn` (split the sum with
`Fin.sum_univ_castSucc`; the only place the free chart is unfolded), `simplexVolume_map_perm` and
`simplexVolumeOn_eq_map` (§10.0/R4.1: the two charts differ by `det ±1`), `toIET_inv` (source 2.4;
needs `imageLengths` and the `mkIET1` inversion API), `rvStep`/`rv_length`/`rvStep_admissible`
(R2.1), and the main theorem.

**Next: M1 (R4, volumes)** — `simplexVolume_map_perm` first, then `Volume.lean`.

---

## Session: M1 of the Masur–Veech campaign — the volume layer (M1a done, M1b open)

**Author's instruction: "Go with M1."** M1 = R4 (`blueprint.md` §14): Lemma 1 and Lemma 3,
axiom-clean.

**A structural decision.** Lemma 1/Lemma 3 are statements about `Path.Q P γ` and `simplexCyl P γ`,
and `rvStep` is a `sorry`-def, so any theorem phrased through them would depend on `sorryAx`. The
volume layer is therefore proved **for an arbitrary matrix `M`** (continuous image of the standard
simplex), and the application to `Q(γ)` waits for R2. A second structural point: everything is
stated in the `n → n+1` indexing (free coordinates `Fin n`, simplex in `Fin (n+1)`), because
`Fin.snoc` has type `Fin n → α → Fin (n+1) → α`; the copied `simplexMap d` lives on
`Fin (d-1) → Fin d`, and `Fin (d-1+1)` is not defeq to `Fin d`. The mismatch is confined to one
bridge lemma (`simplexVolume_eq_chartVolume`), a lesson for R2/R3: **state the new API in the
`n+1` indexing**.

**New file `MasurVeech/Volume.lean`, proved and axiom-clean** (checked in `Check.lean`):
`chart`, `region`, `chart_castSucc`, `chart_last`, `chart_sum`, `chart_injective`, `chart_pos`,
`measurableSet_region`, `linChart` (image in `{∑=0}`), `linChart_sum`, `linChart_add`,
`linChart_smul`, `chart_eq_linChart_add`, `inducedMap` (affine) and `linInducedMap` (its linear
part), `linInducedMap_add`, `linInducedMap_smul`, and the key identity
**`chart_inducedMap : chart (inducedMap M v) = M • chart v`** for column sums `1`.
`chart` is *affine*, not linear: `chart (v+w) ≠ chart v + chart w`, which is why `inducedMap` is
affine and `det` is taken on `linInducedMap`.

**Still `sorry` (M1b):** `det_linInducedMap` (`det (linInducedMap M) = det M`, via the basis
adapted to `{∑=0} ⊕ ℝ·1`), `inducedMap_injective`, `inducedMap_mem_region`,
`volume_image_inducedMap` (`MeasureTheory.map_linearMap_addHaar_eq_smul_addHaar` with
`|det| = 1` after normalisation), `chartVolume_map_perm` (= the same with a permutation matrix),
`simplexVolume_eq_chartVolume` (the `n+1` ↔ `d` bridge), and in `Basic.lean` still
`ae_mem_simplexOn`, `simplexVolume_map_perm`, `simplexVolumeOn_eq_map`, `toIET_inv`.

**Build**: `lake build` green, 8715 jobs, no warnings. `Check.lean` now reports
`toIET_eq_mkIET1`, `chart_inducedMap`, `linInducedMap_smul`, `chart_sum`, `sum_lengthsInBottom`,
`perm_inv` all at `[propext, Classical.choice, Quot.sound]`; the main statement still has
`sorryAx`.

**Next for M1**: `det_linInducedMap` (the only real mathematics left in R4), then
`volume_image_inducedMap` + `chartVolume_map_perm` + the bridge, which together give Lemma 1 for
an arbitrary matrix and hence, once R2 exists, Lemma 3.

## The declaration linters are clean: `runLinter` passes (this session)

`lake build` only runs the *syntax* linters (one linter per command).  The **declaration** linters
(`docBlame`, `simpNF`, `unusedArguments`, `defLemma`, `dupNamespace`, …) are Batteries' `runLinter`,
which Mathlib CI runs as `lake exe runLinter Mathlib`.  It found 25 problems here; the tree is now
clean — 0 findings in 982 declarations (plus 1057 automatically generated ones), 14 linters active,
for `IETFree`, `Challenge` and `ChallengeWeak` alike.

**How to run it in this VM.**  `lake exe runLinter` cannot be *built*: the driver is Batteries'
`lean_exe` `runLinter`, so Lake wants to compile C objects, and
`.lake/packages/batteries/.lake/build` is a symlink into the root-owned `/opt/mathlib`
(`error: unable to open output file …/Batteries/Tactic/Lint/Basic.c.o.export: Permission denied`) —
the same wall as `lake exe mk_all`.  The driver itself works *interpreted*, which is what to use:

```
cd IET2
lake env lean --run .lake/packages/batteries/scripts/runLinter.lean --no-build IETFree
lake env lean --run .lake/packages/batteries/scripts/runLinter.lean --no-build Challenge
lake env lean --run .lake/packages/batteries/scripts/runLinter.lean --no-build ChallengeWeak
```

Name the modules: with no argument the driver resolves the Lake workspace itself and hits
`LEAN ASSERTION VIOLATION … ir_interpreter.cpp:928` (an interpreter failure in `Lake.loadWorkspace`,
nothing to do with this project).  `--no-build` is required, otherwise the driver shells out to
`lake build`.  It reads `scripts/nolints.json` relative to the *current directory*, which does not
exist here, so no nolint list applies.  The whole run is ~5 s per invocation.

**What it found, and what was done.**

* `docBlame`, 4: docstrings added to `GoodRegion.blockPermOf`, `ubox` and the two data fields
  `BlockIdx.k` / `BlockIdx.l` (docBlame only asks for fields that carry data, not for `hkl`/`hln`).
* `simpNF`, 1: **`IET.apply_symm_apply` is deleted**.  It stated `f (f.toEquiv.symm x) = x`, which is
  `Equiv.apply_symm_apply` after the coercion, so it was not a useful simp lemma; nothing in the tree
  used it either — the `⁻¹` form `IET.apply_symm_apply'` (`f (f⁻¹ x) = x`) is the one that has 17
  uses, and it is untouched.  Do not recreate the deleted one.
* `unusedArguments`, 20 findings: unused instance arguments removed from the statements — in the end
  **39 instance arguments in 34 declarations**, 34 deleted from the statement and 5 through
  `omit [NeZero …] in` where the argument is an automatically included section variable
  (`BlockData.prodRestrict_le_volume`, `BlockDiophantine.GoodRegion.cutAffine_eq_leftEnd`,
  `InvariantInterval.RestrictIET.sum_truncatedLengths`).  Every one of them was unused in the *value*
  as well as the type (Batteries' linter collects free variables over both), so no proof needed
  changing — the statements only became more general.

**The removals cascade, so this has to be iterated to a fixed point.**  An instance argument that was
needed only in order to *call* a lemma loses its last use when that lemma stops taking it, so each
round exposes the next one: 25 findings → 9 → 4 → 2 → 0, i.e. 20, 9, 4 and 2 findings in the four
rounds; the fifth run passes.  Two instructive cases:

* `ae_exists_of_countable` lost `[SecondCountableTopology α]` and then `[TopologicalSpace α]`, which
  had only been there to type the former: the lemma needs no topology at all;
* after `sum_clamp_sub` lost `[NeZero n]`, the proof of `RestrictIET.sum_truncatedLengths` no longer
  used its section's `[NeZero e]`, and `lake build` started printing an `unusedSectionVars` warning
  for it — the same phenomenon under a different linter.  Fixed with `omit [NeZero e] in`.  **Check
  `lake build` after every round, not just `runLinter`.**

The whole-file `simp`-lemma set is unaffected by the deleted lemma: `simp` closes what it used to
rewrite through `Equiv.apply_symm_apply`.

**Text-based style.**  `lake exe lint-style` is the other half of Mathlib's linting and cannot be run
here for the same reason (it also needs to load the Lake workspace, which is what crashes the
interpreter).  A direct scan of the 34 `.lean` files for what it checks — tabs, CRLF, trailing
whitespace, missing final newline — is clean.  Two leftovers outside the library were left alone on
purpose: `lakefile.toml` (the owner's file, CRLF line endings, so every line "ends in whitespace") and
one trailing-whitespace line in each of `Tasks/cutset_comp.lean`, `Tasks/exists_mkiet_equiv_eq.lean`
and `Tasks/transl_of_locally.lean` (frozen statement files handed to proof searches).

**Verification of this pass** (all from the final tree): clean `lake build` — 8742 jobs, exit 0,
0 warnings; `./Build.sh` — 35/35 `ok`, 0 warnings, `sorryAx: 6` (3 `Challenge` + 3 `ChallengeWeak`,
library 0), comparator check OK (32661 declarations); `MATHLIB=/opt/mathlib ./Comparator/run.sh` —
`Lean default kernel accepts the solution`; `runLinter` on `IETFree`, `Challenge`, `ChallengeWeak` —
three passes.  `Tasks/Match.lean` still compiles, so the frozen discovery statements still match.
One frozen-region touch, on the owner's explicit instruction: `IET.lean`'s **frozen block** runs from
the marker before `leftEnd` to `coe_mkIETEquiv`, and the lemma `image_point_mem` sits inside it; its
unused `[NeZero n]` was removed.  It is a lemma, not one of the definitions mirrored by
`Challenge.lean`, and no definition or statement in the frozen block changed — the comparator run
above is the check on that.

---

## Session: swarm `smvwp4zuj` (M1b frontier) — first two landings, three false auxiliary statements

**Dispatch.** Four members on the four independent packets of the M1b frontier: A = determinant
identity (`det_sub_last_col` / `det_linInducedMap`), B = change of variables for `inducedMap`, C =
`ae_mem_simplexOn`, D = `rvStep`. A second wave (up to four more, total eight) will take
`chartVolume_map_perm`, `simplexVolume_map_perm`, `simplexVolumeOn_eq_map`, `toIET_inv` and the
`simplexVolume_eq_chartVolume` bridge once A/B have landed.

**Pattern to remember: three auxiliary statements I wrote were FALSE as stated, all refuted by the
swarm with explicit witnesses.** The missing hypotheses are not cosmetic; each is exactly what makes
the statement true.

1. `inducedMap_injective` with only `M.det ≠ 0` is false: `M = !![1,1;0,1]` has det `1` and
   `inducedMap M ≡ 1`. Needs the column sums (`hM : ∀ j, ∑ i, M i j = 1`), because only then is
   `inducedMap M = linInducedMap M + b` with `linInducedMap M` the map of `Q - b·1ᵀ`.
2. `inducedMap_mem_region` with only `0 ≤ M` and column sums `1` is false: `M = !![0,0;1,1]` sends
   the region to `0`. Needs `M.det ≠ 0` (a zero row forces det `0`; and `det ≠ 0` holds for
   `M = Q·diag(1/Q_β)` since `det Q = 1`).
3. `ae_mem_simplexOn` with only `[Fintype α]` is false: for the empty alphabet `simplexOn α = ∅`
   while `simplexVolumeOn α` is a probability measure. Needs `[Nonempty α]` (available from
   `P : CombData α n`, `n ≠ 0`).

**Landed.** `MasurVeech/Affine.lean` (from member m4): the affine decomposition
`inducedMap M = linInducedMap M + b`, `toMatrix'_linInducedMapLinear`, the change of variables
`volume (inducedMap M '' S) = |det M| · volume S` via `Measure.addHaar_image_linearMap` +
`measure_preimage_add_right`, injectivity and region membership with the corrected hypotheses, and
the axiom-free core `PacketB.volume_image_inducedMap_of_det` (every `S`, no measurability, no
nonnegativity). **M1b is now reduced to the single pure matrix identity `det_sub_last_col`**;
`det_linInducedMap` follows from it via `PacketB.det_linInducedMap_of_matrix`.
`MasurVeech/SimplexAe.lean` (from member m1): `sum_simplexMap`, `ae_mem_simplexOn_fin`,
`ae_mem_simplexOn_of_nonempty`, plus the counterexample. `Basic.lean` no longer contains the false
`ae_mem_simplexOn`; `Volume.lean` no longer contains the false injectivity/region statements and is
`sorry`-free (geometric layer only).

**Build**: `lake build` green, 8717 jobs, no warnings. `Check.lean` reports `volume_image_inducedMap`
(=`PacketB.volume_image_inducedMap`) with `sorryAx` from packet A only;
`PacketB.volume_image_inducedMap_of_det`, `inducedMap_mem_region`, `ae_mem_simplexOn_of_nonempty`,
`sum_simplexMap`, `chart_inducedMap` all clean.

**Open after the first wave**: `det_sub_last_col` (packet A, member m2, running), `rvStep` (packet D,
member m3, running), and then the second-wave targets.

**Landing (package A + B complete; M1b closed except two corollaries).** Member m2's
`det_sub_last_col` (row/column operations: `L * M * E = ![A,b;0,1]` with `L` = add all rows to the
last, `E` = subtract the last column from the others, both unit lower triangular; column sums enter
exactly in `lastRowOp_mul_lastColOp`; then Laplace along the last row) is landed in
`MasurVeech/Affine.lean`, and `det_linInducedMap` follows from it. **`volume_image_inducedMap` is
now axiom-clean** — the change of variables for `inducedMap` is unconditional:
`volume (inducedMap M '' S) = ENNreal.ofReal |det M| * volume S` for every `S`, no measurability,
no nonnegativity. Remaining `sorry`s in the project: `chartVolume_map_perm` and
`simplexVolume_eq_chartVolume` (Affine), `simplexVolume_map_perm`, `simplexVolumeOn_eq_map`,
`toIET_inv` (Basic), `rvStep`, `rv_length`, `rvStep_admissible` (Step), and the main theorem.

**Packet F landed (swarm `smvwpk8zn`, member m3).** `simplexVolume_eq_chartVolume` is proved and
in `Affine.lean`: the copied `simplexVolume (n+1)`, transported to real vectors, is
`(volume.restrict (region n)).map (chart n)`. Two facts worth remembering:

* **`simplexRegion (n+1) = region n` is definitional (`rfl`)**: `(n+1)-1` reduces to `n` by `Nat.sub`
  recursion, unlike `(d-1)+1` versus `d`. So the `n → n+1` indexing is cheap in this direction, and
  the bridge needs no `finCongr` transport. State everything in the `n → n+1` form.
* The pointwise identity `(fun i => ((simplexMap (n+1) v i : ℝ≥0) : ℝ)) = chart n v` holds on
  `region n` (`Fin.lastCases` + `simplexMap_last`/`simplexMap_castSucc` + `Real.coe_toNNReal`), and
  `Measure.map_congr` with `ae_restrict_mem` keeps the junk values outside the region out of it.

`Affine.lean` now has a single `sorry`: `chartVolume_map_perm`. Remaining in the project: that one,
`simplexVolume_map_perm`, `simplexVolumeOn_eq_map`, `toIET_inv` (Basic), `rvStep`, `rv_length`,
`rvStep_admissible` (Step), and the main theorem. Members in flight: swarm `smvwp4zuj` m3 on
`rvStep`; swarm `smvwpk8zn` m1 on `chartVolume_map_perm`, m2 on `toIET_inv`. Seven of the eight
allowed members are used; the eighth is held for R3 (`Path.lean`, Prop. 4.3 and Corollaries 1–4),
which is the next large packet after M1.

**Packet H landed (swarm `smvwpk8zn`, member m2).** `CombData.toIET_inv` — source 2.4, swapping the
two orders inverts the exchange — is proved and in `Basic.lean`; the `sorry` is gone. The route:
`(mkIET1 lam π)⁻¹ = mkIET1 (imageLengths π lam) π.symm` (`mkIET1_inv`, from `mkIETEquiv`'s
`invFun`, `IET.ext`, `rfl`), `perm (inv P) = (perm P)⁻¹`, and the length-vector identity
`imageLengths (perm P) (lam ∘ π_bottom⁻¹) = lam ∘ π_top⁻¹`, which is `perm_symm_apply :
(perm P).symm k = π_bottom (π_top.symm k)`. The helpers (`mkIET1_proof_irrel`, `coe_mkIET1`,
`sum_imageLengths_one`, `mkIET1_inv`, `mkIET1_congr`, `CombData.perm_symm_apply`) are now in
`Basic.lean`; `mkIET1_inv` in particular is what R2/R3 will need.

Remaining `sorry`s: `chartVolume_map_perm` (Affine), `simplexVolume_map_perm`,
`simplexVolumeOn_eq_map` (Basic), `rvStep`, `rv_length`, `rvStep_admissible` (Step), and the main
theorem — seven in all. Build green, 8717 jobs.

**Packet D landed (swarm `smvwp4zuj`, member m3): `rvStep` is real.** `Step.lean` now has the actual
Rauzy–Veech step and its admissibility proof; the only `sorry` left in that file is `rv_length`.

* **Convention** (record this): `rvStep P true` keeps `piTop` and inserts the letter `last false`
  just after `last true` in `piBottom`; `rvStep P false` is the mirror image. `ε = true` is the
  source's **type 1** (`λ_{α₁} > λ_{α₀}`), consistent with
  `rvType := if lam (last false) < lam (last true) then true else false`.
* **Independently verified on the source's `d = 4` example** (blueprint V2): bottom `(A,B,C,D)`,
  top `(B,D,A,C)`, `λ_D > λ_C` (type `false`); `rvStep exP false` gives top order `(B,D,C,A)` and
  bottom unchanged — matching the hand computation. So the definition, not just its API, is right.
* Machinery: `insertEquiv`/`insertFun`/`removeFun` (the insertion of the last letter after the
  pivot), `pivot P ε`, the defining equations in position and coordinate form, the branch lemmas,
  `rvStep_inv` (the step commutes with the involution), `pivot_succ_lt` (for admissible data with
  `2 ≤ n` the pivot is never the last position, so the total/junk extension is never used), and
  `IsIrreduciblePerm.symm`.

`rvStep_admissible` and `pivot_succ_lt` are axiom-clean. Remaining `sorry`s in the project:
`chartVolume_map_perm` (Affine), `simplexVolume_map_perm`, `simplexVolumeOn_eq_map` (Basic),
`rv_length` (Step), and the main theorem — five in all. Build green, 8717 jobs.

**Packet E landed (swarm `smvwpk8zn`, member m1): `chartVolume_map_perm`, and `Affine.lean` is now
`sorry`-free.** Route: `permMat σ i j = if σ i = j then 1 else 0`; nonneg, column sums 1,
`permMat σᵀ * permMat σ = 1` hence `det * det = 1` (orthogonality, cleaner than a signed-permutation
count), so `|det| = 1`; `l ↦ l ∘ σ` is `inducedMap (permMat σ)` in the chart
(`chart_inducedMap_permMat`); `inducedMap (permMat σ)` maps `region n` **onto** itself, using
`inducedMap_mem_region` for `σ` and `σ⁻¹`; then `PacketB.volume_image_inducedMap_of_det` with
`|det| = 1`. Also contributed `continuous_chart`, `continuous_inducedMap`, `inducedMap_one`,
`inducedMap_comp` — reusable for the a.e. transfer in R6.

**M1 (R4) is closed**: `det_sub_last_col` + `det_linInducedMap` + the unconditional change of
variables + permutation invariance + the `simplexVolume` bridge, all in `Affine.lean`, axiom-clean.
Remaining in the project (four): `simplexVolume_map_perm` and `simplexVolumeOn_eq_map` in
`Basic.lean` (a short assembly from E and F, mine), `rv_length` in `Step.lean` (now a direct
computation with the real `rvStep`), and the main theorem.

Swarm `smvwpk8zn`: 2 accepted (m3 = F, m2 = H, m1 = E → 3 accepted), still running with no member
left? (check `ultramath_status`). Seven of the eight allowed members used; the eighth is reserved
for R3.

**Both swarms ended solved.** `smvwp4zuj`: 4 accepted (A determinant, B change of variables, C a.e.
membership, D `rvStep`). `smvwpk8zn`: 3 accepted (E permutation invariance, F the `simplexVolume`
bridge, H `toIET_inv`). Seven members, all accepted, no rejection needed.

**A fourth false auxiliary statement of mine, caught before anyone could prove it:**
`rv_length` (Step.lean) asserted `∃ λ̂ > 0, λ = V λ̂` from `λ (last (!ε)) < λ (last ε)` alone. That
is false if some coordinate of `λ` is `0` (a zero cannot be written as a positive combination). The
statement now carries `hpos : ∀ a, 0 < lam a`, which is what a length vector of an i.e.m has. The
pattern is consistent: the hypotheses I omit are the ones that carry the mathematical content.

Project state: four `sorry`s — `simplexVolume_map_perm`, `simplexVolumeOn_eq_map` (Basic; short
assemblies from E and F), `rv_length` (Step; direct computation with the real `rvStep`), and the main
theorem. `Affine.lean` is `sorry`-free: determinant, change of variables, injectivity/region
membership, permutation invariance, and the `simplexVolume` bridge, all axiom-clean. Build green,
8717 jobs.

**Packet P1 landed (swarm `smvwq64va`, member m4): M1 is completely closed.** `simplexVolume_map_perm`
and `simplexVolumeOn_eq_map` are proved. Since `Basic.lean` precedes `Affine.lean`, the two
*statements* were moved out of `Basic.lean` (nothing consumed them) and proved in `Affine.lean`.
The key device, reusable: the coordinatewise coercion `ι : (Fin m → ℝ≥0) → (Fin m → ℝ)` has left
inverse `c x = fun i => (x i).toNNReal`, so `μ = (μ.map ι).map c` for *every* `μ` — inverting the
bridge needs no injectivity argument. Also kept: `simplexVolume_succ_eq_map_toNNReal`,
`measurable_coord_toNNReal` (needed for the a.e. transfer in R6).

**The project now has two `sorry`s: `rv_length` (Step) and the main theorem.** Everything else —
the copied IET API, `CombData`/`toIET`/`toIET_inv`, `simplexVolumeOn` and its invariance, the chart,
the induced map, the determinant, the change of variables, the `simplexVolume` bridge, `rvStep` and
its admissibility, and the a.e. simplex membership — is proved and axiom-clean. Build green, 8717
jobs, warning-free.

**Packet P3 landed (swarm `smvwq64va`, member m1): `MasurVeech/Path.lean`.** The path API of R3:
`vertex` (iterated `rvStep`) with `vertex_append`; `name`/`secondary`; `rvStep_last_self`
(`(P.rvStep e).last e = P.last e`); **Corollary 1** in both forms (`secondary_eq_of_type_ne`,
`secondary_eq_of_name_ne`, and the path-level `secondary_eq_name_of_name_ne`);
`Path.Q_nil/cons/append`; `last_true_ne_last_false` and `name_ne_secondary` for admissible data with
`2 ≤ n`; and `vertexNat` with `vertexNat_eq_vertex_ofFn` for infinite paths.

Two facts to remember for R5/R6: `vertex_append` + `Path.Q_append` make the matrix product compose
along concatenated paths (needed for the multiplicativity in Lemma 5/6), and `rvStep_last_self` is
what makes "same type ⟺ same name" work along a path (needed in Lemma 4's induction).

Housekeeping debt: the transplanted member code brings linter warnings (long lines, unused section
variables) that are not yet silenced; a warning-cleanup pass is owed before the release. Build green,
8718 jobs.

**Packet P2 landed (swarm `smvwq64va`, member m3): `rv_length` proved. `Step.lean` is sorry-free.**
The renormalised vector is `λ̂ = λ` off `last ε` and `λ (last ε) - λ (last !ε)` at `last ε`;
`last ε ≠ last !ε` follows from the strict inequality (`rvMat ε = 1` when they coincide — the same
degeneracy as the algorithm stopping). Helpers: `rvMat_cast`, `sum_rvMat_mul`,
`sum_rvMat_row_sec/main`, and **`type_of_mem_cone`**: for `last ε ≠ last !ε`, the type-`ε` region is
*exactly* the open cone `C(ε)` — which is the input packet P6 needs for the exact nesting identity.

**Project state: exactly one `sorry` left — the main theorem.** Everything else (the copied IET
API; `CombData`, `toIET`, `toIET_inv`; the simplex and its measure with invariance and independence
of the labelling; the chart, the induced map, the determinant, the change of variables; `rvStep` with
its defining equations and admissibility; `rv_length`; the path API and Corollary 1; a.e. simplex
membership) is proved and axiom-clean. Build green, 8718 jobs.

## README links every declaration to its line on GitHub (this session)

The repository is public at <https://github.com/sgouezel/IETFree>, default branch `main`, and its
tree is **the contents of `IET2/` at the repository root** — a link to a module is
`.../blob/main/IETFree/IET.lean#L271`, with no `IET2/` component.  `README.md` now links every
declaration name it mentions to the line that declares it: 120 line links over 20 files
(`https://github.com/sgouezel/IETFree/blob/main/<file>#L<n>`), plus the code spans that are a
declaration applied to arguments (`IET a b`, `mkIET1 lam π h : IET 0 1`, `IsCompType lam π hl mu s a B`,
`blockPerm π k hkl hln hstab`, `IsCompIrreducibleOn D E u v`, `UniqueErgodic f`, `simplexMap d`,
`simplexVolume d`, `mkIETFun λ π 0`, `IsRigidByTranslations (mkIET1 lam π h)`).  Formulas (`G.cellLen
hq = compLenVec G.s q (monoAt G hq)`, `genY * genX`, `listImageLeft ρ s i - listLeftEnd s i`) are left
as plain code.  The names `mkIETEquiv`, `coe_mkIETEquiv` and `main` also exist as the two statement
files' holes/placeholders, so the mentions that are *about* those files point at `Challenge.lean` /
`ChallengeWeak.lean` and every other mention at the library.

Verified mechanically against `main` = `f5b3b09` ("first version", 2026-10-31T18:19Z): for each link,
the raw file was fetched and the anchored line checked to contain the declaration — 120/120 agree.

The `file:line` mentions in the prose and in the correspondence table had gone stale by a few lines in
the unused-binder pass and are refreshed: `main` 331→332 (twice), `ae_diophantine` 1011→1013 (twice),
`compLen_injective` 272→273, `compLen_absolutelyContinuousAt` 198→197, `irreduciblePerm_blockPerm`
55→56, `exists_word_trivial_on_block` 217→216, `main_theorem_of_blocks` 242→241, `GoodRegion`
1087→1088, `exists_goodRegion` 1196→1197, `ae_exists_goodRegion` 1213→1214; every other `file:line`
in the README was already right.  The layout table's "20 449 lines" became 20 475.

No Lean file was touched, so the build is unaffected (`lake build`: 0 warnings, `./Build.sh`:
`sorryAx: 6`, comparator accepted).  One thing seen in the repository and **not** touched: `main` also
carries a `tmp/` directory — stale copies of `IET2/…` together with committed `.olean` binaries, which
looks accidental.

**Packet P6 landed (swarm `smvwqi199`, member m2): `MasurVeech/Nesting.lean`.** The nesting and
partition of the path cylinders, **exactly as sets**:

* `cone_mul : cone (A * B) = qApply A '' cone B` (no hypotheses) and
  `cone_rvMat : cone (rvMat ε) = {w | w > 0, w (last !ε) < w (last ε)}` — the converse half of
  `type_of_mem_cone`.
* `mem_simplexCyl_append_iff : x ∈ Δ(γ ++ [e]) ↔ x ∈ Δ(γ) ∧ w (last !e) < w (last e)`, with `w` the
  renormalised vector at the vertex; `IsRenorm.unique` via the **explicit two-sided inverse**
  `Path.Qinv` of `Path.Q` (no determinant).
* `simplexCyl_eq_union : Δ(γ) = Δ(γ0) ∪ Δ(γ1) ∪ cylStop`, pairwise disjoint, and
  `simplexVolumeOn α (cylStop P γ) = 0`; `simplexVolumeOn_simplexCyl_add :
  μ Δ(γ) = μ Δ(γ0) + μ Δ(γ1)`; `H1_measure` is hypothesis (H1) of blueprint §10.5 verbatim.
* `2 ≤ n` is needed: at `n = 1` the two children coincide and the stopping set is the whole
  simplex — consistent with the main theorem's hypothesis.

**This closes the "exact partition" requirement** that the tree argument of §10.5 rests on (it must
be a set identity, not an a.e. one, because the diameters are compared as sets).

**Packet P5 landed (swarm `smvwqi199`, member m1): `MasurVeech/CylinderVolume.lean` = Lemma 1 of the
source.** `volume_simplexCyl : simplexVolumeOn α (simplexCyl P γ) =
(∏ b, (colsumNN (Path.Q P γ) b)⁻¹) * simplexVolumeOn α (simplexOn α)` — the
`(∏ Q_β)⁻¹` orientation of the source, axiom-clean. By-products now available:
`CombData.det_Path.Q` (`det (Path.Q P γ) = 1`, by induction from `det rvMat = 1`),
`Path.Q_nonneg`, `Path.Q_colsum_pos`, `chart_image_region` (`chart m '' region m =
openRealSimplex m`) and the `co`-coercion injectivity.

With `Nesting.lean` (exact partition + `μ Δ(γ) = μ Δ(γ0) + μ Δ(γ1)`) this closes the volume side of
R4: Lemma 3 and the mass estimates of Lemmas 4–6 have their inputs. Packets P9 (Lemma 3) and P10
(Lemma 5) dispatched in swarm `smvwrc3d8`; P4 (Prop. 4.3), P7 (Lemma 4) and P8 (Lemma 2 + nested
cylinders) still running.

**Packet P4 landed (swarm `smvwq64va`, member m2): Proposition 4.3, with a sharp correction.**
`MasurVeech/NameInfinite.lean`: `name_infinite (P) (hP : P.Admissible) (γ) (lam) (hpos) (hty)
(hnxt) (a) : ∃ᶠ k, mn P γ k = a` (and the `vertex P (List.ofFn γ k)` form), axiom-clean.

**The statement without `P.Admissible` is FALSE**, machine-checked in
`NameInfiniteCounterexample.lean`: `Fin 3`, `piTop = id`, `piBottom = (1 2)` (so `perm = (1 2)`,
reducible); both `rvStep`s fix the vertex (the pivot is the second-to-last position), so the name `0`
never occurs; the two lengths run the subtractive Euclidean algorithm on `(1, (√5−1)/2)`, whose
two-step self-similarity `g² + g = 1` keeps them positive and distinct forever. Admissibility is a
standing hypothesis of the source's §4, so restoring it is right — but the example shows the
proposition is genuinely about irreducible data, not about the recursion alone.

Proof (better than the telescoping sketch of my brief): lengths antitone, total drops by the
secondary length ⟹ a rarely-main letter is rarely secondary and eventually **frozen**; an active
letter cannot sit *below* a frozen one (the block below is fixed, so each main occurrence shifts the
frozen letter up); hence the frozen letters occupy the first `|F|` positions of both orders — a
nonempty proper invariant initial segment, contradicting `IsIrreduciblePerm`.

## `file:line` cells are links too; `formalization.yaml` drops the `IET/` reference (this session)

* The correspondence table's 28 `file:line` cells (in 19 rows) are now hyperlinks of the same form as
  the declaration names — `` [`Irreducible.lean:30`](https://github.com/sgouezel/IETFree/blob/main/IETFree/Irreducible.lean#L30) ``
  — with the same refresh of the numbers recorded in the previous entry.  The two *prose*
  parentheticals (`… `main` (`IETFree/ChallengeWeakSolved.lean:332`) …`, and the same for
  `main_of_library`) stay plain text: the name immediately before them is already a link to exactly
  that line.  `README.md` now has 148 line links over 20 files, all re-verified against `main` =
  `f5b3b09` (each anchor's line fetched and checked): 120 name links + 28 `file:line` links, 0
  failures.  The sentence introducing the table says so.
* `formalization.yaml` no longer refers to the earlier, superseded development: the
  `related_formalizations` block (the `IET/` entry with its sorry counts and `rotation_not_free`) is
  removed, and so is the mention of `../IET` in the `alignment` note for Lemma 1.2, which now reads
  "An illustration in the introduction; not part of this development."  The file still parses
  (`yaml.safe_load`), and the published v0.4 schema has no top-level `required` list and no
  `related_formalizations` property, so removing the key leaves nothing dangling.

No Lean file was touched; `lake build` (0 warnings), `./Build.sh` (`sorryAx: 6`) and the comparator
are unaffected.

**The final assembly is started and its logical core is proved (`MasurVeech/Assembly.lean`).**

* `Assembly.existsUnique_of_lengths` — **the last mile**, fully proved: if the length map of an
  invariant probability measure is injective and every length vector lies in the ray `ℝ • lam`,
  and length vectors have total mass `1`, and Lebesgue's is `lam`, then there is exactly one
  invariant probability measure. (Two measures have vectors `c•lam`, `d•lam`; both sum to `1` and
  `∑lam = 1`, so `c = d = 1`; injectivity finishes.)
* `Assembly.unitMeas` (`volume.restrict (Ico 0 1)`), its `IsProbabilityMeasure` instance, and
  **`Assembly.IET.unitMeas_preimage`** — an exchange of `[0,1)` preserves Lebesgue measure
  (from the copied `Equiv.IsIET.measure_preimage`), plus `invariant_unitMeas`.
* `Assembly.cellOf`, `Assembly.lambdaOf` — the cell of a letter and the length map
  `μ ↦ (μ (cell a))_{a}`.
* `Assembly.masurVeech_of_components` — **the assembly**, fully proved: given the three a.e.
  statements `hray` (ray criterion), `hsum` (mass one) and `hinj` (injectivity of the length map),
  the main theorem follows. All axiom-clean.

So the main theorem is now reduced to exactly three a.e. statements plus one pointwise computation
(`hLeb : lambdaOf unitMeas P lam = lam` on the simplex, which is the cell-partition computation and
is provable from the copied cut-set API — next job for me). The three a.e. statements are the packets
in flight: `hray` needs P8 (nested cylinders) and P11 (tower formula); `hsum` needs the cell partition
(P11); `hinj` needs P11.

**Packet P9 landed (swarm `smvwrc3d8`, member m2): `MasurVeech/ChildVolume.lean` = Lemma 3.**
`volume_simplexCyl_append (hP) (hn) (γ) (e) : vol Δ(γ++[e]) =
(colsumNN Q(γ) (last !e) / (colsumNN Q(γ) (last false) + colsumNN Q(γ) (last true))) * vol Δ(γ)` —
the **secondary** name's column is the one that changes, as in the source; axiom-clean. Plus the
absolute restatement and the strict ratio.

**Fifth false side-remark of mine caught:** the packet asked for "ratio `≤ 1`, equality iff never
rewarded"; that is false — both column sums are positive, so the ratio is *strictly* `< 1`
(`ratio_lt_one`, unconditional). Pattern across the five: an inequality stated without checking its
degenerate case (column sums, `det ≠ 0`, `Nonempty`, `hpos`, and now positivity of the column sums).

Inputs for Lemmas 4–6 are now all landed: Lemma 1 (`CylinderVolume`), Lemma 3 (`ChildVolume`), the
exact partition (`Nesting`), the path API (`Path`), Proposition 4.3 (`NameInfinite`), and the
assembly skeleton (`Assembly`, conditional on `hray`/`hsum`/`hinj`).

## Prose `file:line` links, `Tasks/` dropped from the README and from the zip (this session)

* The two prose parentheticals that name a location — `main` (`IETFree/ChallengeWeakSolved.lean:332`)
  and `main_of_library` (`IETFree/ChallengeWeakSolved.lean:281`) — are links now, of the same form as
  the rest.  `README.md` has **150** line links (120 names + 28 `file:line` cells + these 2), all
  re-verified against `main` = `f5b3b09`: 0 failures.
* The owner has **removed `Tasks/` from the GitHub repository**, so `README.md` no longer mentions it:
  the Status paragraph's parenthetical ("`Tasks/` holds the statement files that seeded the AI proof
  search … `Build.sh` compiles only `Tasks/Match.lean` …") is gone.  Nothing else in the README named
  the directory.
* **`IET2.zip` must not contain `Tasks/`** (owner's instruction, standing).  The recipe, run from the
  repository root, is

  ```
  cd /workspace/nucleus/work/projects/default/repo && rm -f IET2.zip &&
  zip -r -q IET2.zip IET2 -x 'IET2/.lake/*' 'IET2/.scratch/*' 'IET2/Tasks/*' '*.olean'
  ```

  i.e. sources only: `.lake/` (941 MB of clones and build products), `.scratch/` (2.3 GB of logs and
  the comparator work dir), `*.olean`, and now `Tasks/`.  Current zip: 475 KB, 46 files.  Check with
  `unzip -Z1 IET2.zip | grep Tasks` (must print nothing) and `unzip -t`.

Two references to `Tasks/` outside the README are **still there**, deliberately untouched: six mentions
in `formalization.yaml` (`automation.tool_setup`, `fidelity`, `review`, `acknowledgements`) and the
`Tasks/Match.lean` compile step in `Build.sh` (which would now fail on a fresh clone, since the
directory is gone).  Both need the owner's word: deleting the yaml sentences is easy, and the
`Build.sh` step can be dropped or kept for the local tree.

**`hLeb` proved (`Assembly.lambdaOf_lebesgue`).** The length vector of Lebesgue measure is the length
vector: each cell `[leftEnd l i, upperEnd l i)` lies in `[0,1)` (`leftEnd_nonneg`,
`upperEnd_le_total` with `∑ lam = 1`) and has Lebesgue measure `upperEnd - leftEnd = lam a`
(`Real.volume_Ico`, `upperEnd_eq`). Axiom-clean.

**Consequence: `Assembly.masurVeech_of_components` now has exactly three hypotheses** — `hray`,
`hsum`, `hinj`, all a.e. statements about the length map — and the main theorem is a one-line
application of it. `Assembly.existsUnique_of_lengths`, `lambdaOf_lebesgue`,
`IET.unitMeas_preimage`, `invariant_unitMeas` and the assembly are all axiom-clean; build green
(8724 jobs).

**Packet P10 landed (swarm `smvwrc3d8`, member m1): `MasurVeech/BalancedSet.lean` = Lemma 5, with its
analytic input isolated.** `enlarge_balanced_set` is proved from `EnlargeInput` (a seven-conjunct
predicate: a prefix extension `γt` with a mass fraction, a half-mass set `G`, and pointwise
balance/domination), and `EnlargeInput` is *not* a restatement of Lemma 5 — it is the concrete
output of Steps 1–3.

Unconditional and reusable infrastructure proved on the way: `colsumNN_append_singleton`
(`Q_b(γe) = Q_b(γ) + [b = last(!e)] Q_{last e}(γ)`), `colsumNN_mono` along extensions,
**laminarity** of the cylinders (`isPrefix_or_isPrefix_of_mem_inter`,
`disjoint_simplexCyl_of_not_isPrefix`, `volume_iUnion_antichain`), `volume_append_mul` (the exact
child/parent ratio), `volume_simplexCyl_lt_top`, and **`exists_finset_antichain`** — Step 4 of the
source, the extraction of a finite prefix-antichain from a laminar cover of a set, which is where
`μΔ(γ) < ⊤` is used.

Follow-up swarm `smvws3lwk` dispatched to discharge `EnlargeInput`: Step 1 (finite choice of exiting
paths, unblocked), Step 3 (Prop. 4.3 is landed, so the two-case analysis is unblocked), Step 2
(Lemma 4, P7, in flight — to be taken as an explicit hypothesis if it has not landed).

## `Tasks/` is gone from the tree; `Build.sh` and the module docstrings are clean of it (this session)

The owner deleted `Tasks/` (14 files, 224 KB — `Match.lean`, `README.md` and the twelve statement files
of the proof-search runs) from the repository and from this tree.  Nothing depends on it any more.

* `Build.sh`: the `Tasks/Match.lean` step (compile, `FAIL` branch, `ok` line — nine lines) is removed.
  The script is now the 34 modules + `IETFree.lean` + the comparator check + the sorry count +
  `--strict`.  Green on the final tree: **34 `ok` lines, 0 warnings**, `sorryAx: 6` (3 `Challenge` +
  3 `ChallengeWeak`, library 0), comparator check OK.  `lake build` was re-run after the docstring
  edits below: 8742 jobs, exit 0, 0 warnings.
* `formalization.yaml`: the last five `Tasks` passages are rewritten — `automation.tool_setup` (both
  sentences of the first method), the second method's `tool_setup` and `prompting_notes`, `review.notes`
  and `acknowledgements`.  `grep -c Tasks formalization.yaml` is 0 and the file parses.
* **The module docstrings pointed at `Tasks/…` too**, and are cleaned; the provenance (the *run* names)
  is kept and the dead paths dropped: `Centralizer.lean` ×3 (the `α = Fin 2` remark, the "Acceptance
  criteria" bullet of the plan section, and the `commensurable-commute` sentence),
  `SingularityBound.lean` ×1 (`singularity-bound-2`, whose paragraph also had a stray two-space
  continuation, now normalised) and `TranslationVector.lean` ×1 (`translation-vector-bound`).
  Docstring-only edits: no statement, proof or declaration position changed, and none of those three
  files is the target of a README link, so no link drifts.  `grep -rn Tasks` over the tree now hits only
  `NOTES.md` (this history) and `.scratch/`.
* `README.md` had already been cleaned and `IET2.zip` already excluded `Tasks/`, so both needed no
  change; the exclusion stays in the recipe (it is now a no-op).

## MasurVeech session: Lemma 6 landed, the main statement is FALSE as stated and is repaired (this session)

**The headline finding.** `Main.masurVeech_ae_unique_invariant` was false as written.  An exchange
`P.toIET lam` is the identity off `[0,1)` (`mkIETFun_of_notMem`), so every probability measure on
`[0,1)ᶜ` is invariant: `δ₂` is invariant and is not Lebesgue.  Hence
`∃! μ : ProbabilityMeasure ℝ, Invariant μ (P.toIET lam)` fails at **every** `lam ∈ simplexOn α`, not
merely on a null set.  Machine-checked in the new module `MasurVeech/MasurVeech/MainCounterexample.lean`
(`MainCounterexample.not_existsUnique`, axioms `[propext, Classical.choice, Quot.sound]`).

*Repair* (the source's own setting — an exchange *of the interval*): the quantifier is restricted to
invariant probability measures with `μ (Ico 0 1) = 1`.  `Main.lean`'s statement now carries that
conjunct; `Assembly.existsUnique_of_lengths` and `Assembly.masurVeech_of_components` were restated
accordingly.

**`hsum` is no longer a hypothesis.** With the mass condition, the total mass of the length vector is
a theorem: the bottom cells `cellOf P lam a` partition `Ico 0 1`, so `∑ a, lambdaOf μ P lam a = 1`
(`Assembly.sum_lambdaOf`).  New lemmas in `Assembly.lean`: `leftEnd_mono`,
`leftEnd_succ_eq_upperEnd`, `upperEnd_le_leftEnd`, `mem_cellOf_idx`, `cellOf_subset`,
`disjoint_cellOf`, `iUnion_cellOf`, `sum_lambdaOf`, `lebesgue_Ico`.  `masurVeech_of_components` now
takes only **`hray`** and **`hinj`**, both carrying `μ (Ico 0 1) = 1`.

**Landed this session** (all `lake build` green, 8729 jobs, `#print axioms` clean, in `Check.lean`):

| module | content |
|---|---|
| `BalancedCover.lean` (`PacketP6bis`, swarm `smvwremj7` m1) | **Lemma 6**: `exists_balanced_cover` / `_sep` / **`_uniform`** (one `C` for all nodes), from `Lemma5Shape` / `Lemma5ShapeUniform` |
| `NestedCylinder.lean` (`NestedCylinder`, swarm `smvwr69sq` m1) | cylinder tree (H1)+(H2), nested-or-disjoint dichotomy, child-mass identity, Claim 2, `nested_cylinder_tendsto` (conditional on `hhits`) |
| `Lemma2Diameter.lean` (`Lemma2Diameter`, same) | barycentric contraction `bary_contraction`, sharpness, and the machine-checked refutation of the printed `2(1-dδ)` |
| `MainCounterexample.lean` | the false statement above |

**Interface repair at landing.** `Lemma5Shape` / `Lemma5ShapeUniform` as submitted had the conjunct
`A_l ⊆ A` for a general ambient set `A`.  That is *not* derivable from the landed Lemma 5, and not
implied by the `A = univ` case either (`A₀ = {1}`, `A = {1,2}`, `B = {1,3}` gives `A₀ = A ∩ B` with
both inclusions strict).  The iteration only ever instantiates the hypothesis at `A = univ`
(`hL5 γ A Finset.univ …`), so both shapes were restated with the ambient set fixed to `univ` and the
subset conjunct dropped; the proofs were unchanged.

**Two source slips confirmed by members, machine-checked counterexamples.** (i) §10.5 Claim 1 as
printed is invalid: from `Δ(γ_{n+1}) ∩ G(γ_n) ≠ ∅` one cannot conclude `λ ∈ G(γ_n)` when a family
member is longer than `n+1`; the lemma is nevertheless true, by the stopping-time/level-decomposition
argument (conditional Borel–Cantelli without `condExp`) — swarm `smvwr69sq` m1 was sent back to
remove `hhits` and `hgood` and prove it.  (ii) §10.1's `Σ_α |θ_{αβ} - θ_{αβ'}| ≤ 2(1-dδ)` gives no
contraction (`2(1-dδ) > 1` for small `δ`); the factor 2 is unnecessary and
`diam ≤ (1 - dδ) · diam` holds, which is `Lemma2Diameter.bary_contraction`.

**New swarm `smvwsf0m0`** (3 members, 420 min) on the pieces nobody had: (A) Cor. 4 uniformly over
the diagram (a positive `Q`-path from every vertex — the `C₁` of Lemma 2 and of Lemma 5's Step 1),
(B) Lemma 2's mass half plus the `simp`lex/vertex identification for its diameter half given the
`B`-matrix hypothesis, (C) "a finite measure on `ℝ` is determined by a refining sequence of
partitions with mesh → 0" (the `hinj` input).

**Still open.** `hray` (needs the towers, `smvwrcl9u`; then Lemma 2 + nested cylinders + R6.2/R6.4),
`hinj` (needs the towers + the refining-partition lemma), `EnlargeInput` (`smvws3lwk`, needs Lemma 4
from `smvwr69sq` m2), and the `sorry` in `Main.lean`.

### Addendum (same session): Lemma 4 and the first-return layer landed

* **`MasurVeech/MasurVeech/Lemma4.lean`** (swarm `smvwr69sq` m2, accepted) — **Lemma 4**:
  `CombData.lemma4_source`, `lemma4`, with `Qhit` (the source's `Q′_α(T)`, well defined by
  `hit_unique`), the column recursion `qcol_append`, Lemma 3 as `volume_append_singleton`, and
  `ratio_add`.  Induction on the *truncation depth* `fh` instead of the source's `n̄`, then
  continuity from below; no measurability of a cylinder is used.  At landing the vendored copy of
  packets P5/P6 was deleted and replaced by `import MasurVeech.CylinderVolume` / `Nesting`: the
  member's parts compile unchanged against the landed modules.
* **`MasurVeech/MasurVeech/FirstReturn.lean`** (swarm `smvwrcl9u` m1) — **R0.3–R0.4, Part 1 and
  §10.4 at level one**: first return time in `{1,2}` (`ret_mem`, `ret_min`), the return map is
  `mkIETFun` for `rvStep _ false` (`firstReturn_eq`, `firstReturn_eq_rvStep`), the `mkIETFun ↔
  rvStep` bridge (`rvStep_toComb_false_perm`, `lam_eq_rvMat_mul`), the tower decomposition
  (`tower_decomp`, `tower_decomp_iUnion`), equal floor masses (`measure_image_iterate`), Kac
  (`kac_two_floors`) and the level-one formula with multiplicities `multOne = rvMat false`.  The
  member was **sent back** (not accepted as the packet answer) for the two real gaps: the *level-n*
  formula `μ (cell α) = ∑ β, (Path.Q P γ α β : ℝ) μ (level-n cell β)`, and the inverse Rauzy type
  (the induced interval is a *suffix* there, so it is not the same computation).
* New swarm **`smvwsufxd`** on the bridge `PacketP6bis.Lemma5ShapeUniform` ⟸
  `PacketP10.enlarge_balanced_set` + a uniform `EnlargeInput`: the two landed layers disagree on the
  scalar type of the column sums (real `colsum` vs `PacketP10.colsumNN`), on the domination form
  (`∃ b' ∈ A₀` vs `≤ A₀.sup`), and on the disjointness form (antichain vs `Disjoint`).  Once the
  `EnlargeInput` packet lands, this makes Lemma 6 unconditional.

### Addendum 2: TARGET C landed; and a gap found in the blueprint's R7.3 (`hinj`)

* **`MasurVeech/MasurVeech/RefiningPartition.lean`** (swarm `smvwsf0m0` m2, accepted) — a finite
  measure on `ℝ` is determined by agreeing on the atoms of a refining sequence of partitions with
  mesh → 0: `measure_eq_of_measurableSet_subset`, `measure_restrict_eq_of_refining_partitions`,
  `measure_eq_of_refining_partitions`, plus `_diam` and `_Ico` variants.  No shape hypothesis on the
  atoms; inner regularity by compact sets upgrades closed `F` to all Borel `B ⊆ I`.  The mesh
  hypothesis is in *pairwise* form because Mathlib's `Metric.diam` is `0` for unbounded sets, so a
  `diam`-based mesh would be vacuous.  This is the measure-theoretic half of `hinj`.
* **Gap found while reading R7.3.**  The other half of `hinj` needs the *mesh of the level-`n` floor
  partition* to tend to `0`, i.e. `max_β λ^{(n)}_β → 0` a.e. (the source's Cor. 2).  That is **not**
  the same statement as `diam Δ(γ_n) → 0`, which is what §10.5 proves, and `blueprint.md` R7.3 reads
  as though it were.  It does follow from it, by a short argument: if `(λ^{(n)})_{β} ≥ ε` along a
  subsequence then `ν_n := Q_n(λ^{(n)} + t e_β)` normalised lies in the same cylinder `Δ(γ_n)` and
  is at distance `≥ t / C` from `λ` because the diagonal entries of `Q_n` are `≥ 1`
  (`PacketP10.one_le_diag_Path.Q`), contradicting `diam Δ(γ_n) → 0`.  So the implication
  `diam Δ(γ_n) → 0 ⟹ max_β λ^{(n)}_β → 0` is a **separate small packet to formalise**, not a
  consequence to be quoted; it is on the critical path of `hinj` and is not in any running packet.

### Addendum 3: Lemma 2 in the real setting landed; Cor. 4 is now the critical risk

* **`MasurVeech/MasurVeech/Lemma2Real.lean`** (swarm `smvwsf0m0` m3, accepted) — **Lemma 2**, both
  halves, in the real setting: `volume_simplexCyl_append_ge` (mass, constant `((n C₁ C)⁻¹)^n`),
  `diam_simplexCyl_append_le` (diameter, factor `1 - (C₁C)⁻¹`) and `lemma2_append` with a *single*
  constant serving both (`cMass_le_cDiam`), plus `cMass_pos`.  The hard geometry is done and
  reusable: `eq_sum_smul_vtx` (a point of a cylinder is a convex combination of the vertices
  `vtx M b = Q e_b / Q_β`), `vtx_mul` (child vertex = `θ`-image of the parent's, `θ = Q_α B_{αβ}/Q'_β`),
  `le_theta` (`θ ≥ 1/(n C₁ C)`), `vtxNN_mem_closure` (vertices are limits of cylinder points, via an
  explicit sequence), `dist_co_co`, `isBounded_simplexCyl`.  Hypotheses are the source's: `B` is the
  matrix of an actual `δ` from the current vertex, `1 ≤ B ≤ C₁` entrywise, `Q(γ)` `C`-balanced.
* **`Metric.diam` is `ℝ`-valued in this Mathlib** (`@Metric.diam : Set α → ℝ`), so the `CylTree`
  instance for R6.2 still needs a `Real.toNNReal` transfer (monotonicity of `toNNReal`, with
  `1 - c ≥ 0`).  That plus the `CylTree` record is all that stands between `lemma2_append` and R6.2.
* **Cor. 4 is the critical risk.** R6.2's constant `c` is a single number for the whole tree, so the
  `C₁` of Lemma 2 must be uniform over the vertices of the diagram, i.e. Cor. 4 has to be proved with
  a bound depending only on `n`.  A first attempt (`smvwsf0m0` m1) reached ~85% of its step budget
  with no report; a second, sharper attempt was started as swarm `smvwt8bkd` with the support
  recursion (`Q'_{ab} = Q_{ab} + [b = name]·Q_{a,secondary}` from `Path.Q_append` + `rvMat = 1 + E`)
  as the route, Prop. 4.3 (`PacketP4.name_infinite`) as the source of "every name occurs infinitely
  often", and the explicit instruction not to substitute a column-sum statement for the entrywise
  one.  If Cor. 4 fails, R6.2 and hence `hray` cannot be assembled as planned, and the fallback is a
  balanced-node-specific version (a fixed-length path making `Q` entrywise positive, using the balance
  constant `C` from Lemma 6) — that is a legitimate weaker statement for our purposes and should be
  tried next in that case.

## The build section's file names are links too (this session)

`README.md`'s "Layout and build" section named 34 files without linking them: the path column of the
layout table, and `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `IETFree/`, `IETFree.lean`,
`Build.sh` and `NOTES.md` in its prose.  They are links now, to
`https://github.com/sgouezel/IETFree/blob/main/<path>` for a file and `.../tree/main/<path>` for a
directory (the `IETFree/` directory and the `IETFree/*.lean` glob).  All 34 were checked against the
repository's tree listing at `main` — `blob` for files, `tree` for the directory — 34/34 resolve.  The
repeats of `IETFree/` and `IETFree.lean` in the *contents* column of the first row are left as plain
code, so no row links the same target twice, and nothing inside a fenced code block was touched
(the commands `lake build`, `./Build.sh`, `Comparator/run.sh` stay plain).

`README.md` now carries 193 links: 150 to a declaration's line, 34 to a file, 3 external, 4 relative
(`NOTES.md`, `LICENSE`, `Comparator/README.md`) and 2 internal anchors.

### Addendum 4: the nested-cylinder lemma needs a survival hypothesis — the blueprint's §10.5 repair was wrong twice

**My own error, corrected.**  In the previous pass I wrote into `blueprint.md` that §10.5's Claim 1,
while invalid as printed, "is nevertheless true and provable from (H1)+(H2) alone" by stopping levels
`T(k)`, with `μ{T(k+1)=∞} ≤ (1-c)^{k+1}`.  That is **wrong**: `{T(k)=∞}` is *absorbing*, it contains
`{T(k-1)=∞}`, so the level decomposition gives
`μ{T(k+1)=∞} ≤ (1-c)·μ{T(k)<∞} + μ{T(k)=∞}`, i.e. `1 - a_{k+1} ≥ c(1 - a_k)`, i.e. only
`μ{T(k)<∞} ≥ c^k`, which is compatible with 0.  Swarm `smvwr69sq` m1 caught this and produced the
fair-coin tree as a counterexample to the derivability of survival: cylinders in `{0,1}^ℕ`,
`F(γ) = {γ0}`, `c = 1/2`, `diam γ = 2^{-|γ|}` satisfies (H1)+(H2), yet surviving `k` levels needs `k`
consecutive 0s, so the survival set is null.  (In that example the *conclusion* `diam → 0` still
holds, so it refutes the derivability of `hsurv`, not the lemma.)

**What actually works** (now in `blueprint.md` §10.5): the martingale form, with the extra hypothesis
that members of `F(γ)` have **bounded length** `≤ |γ| + L`.  Badness is then decided at level `n+L`,
so `Z ⊆ Δγ_n \ Gγ_n` gives `μ(Z | F_n) ≤ 1-c` on every atom, while `μ(Z|F_n) → 1_Z` a.e. by Lévy's
downward theorem; hence `1_Z ≤ 1-c` a.e. and `μ Z = 0`.  Neither a stopping-time recursion nor a
first-moment sum over a level can give this (both bottom out at `1-c`).  Mathlib has `condExp` but
**no Lévy theorem / conditional Borel–Cantelli**, so supplying `hsurv` is a packet of its own, in the
concrete setting where `L` is bounded by a constant depending only on `n` (Lemma 6's family composed
with Lemma 2's single extension).

**Landed:** `MasurVeech/MasurVeech/NestedCylinder.lean` (revised, swarm `smvwr69sq` m1, accepted): the
canonical path with `Good` holding *everywhere* (`good_everywhere`, so `p` and `hgood` are gone), the
stopping levels `Tl`, the cylinder-constancy `Tl_subset`, the escape estimate `measure_diff_G`, and
`CylTree.nested_cylinder_tendsto` with `hsurv` explicit.  Its `hsurv` is a genuine hypothesis, not a
smuggled conclusion.

### Addendum 5: towers level-1 matrix form, `EnlargeInput` reduced to a combinatorial input, `smvwrcl9u` exhausted

* **`MasurVeech/MasurVeech/TowerLevel.lean`** (swarm `smvwrcl9u` m1) — **level-one tower formula in
  matrix form**: `tower_formula_one_step_mult`,
  `μ (Ico (leftEnd i) (upperEnd i)) = ∑ j, (multOne π i j : ℝ≥0∞) * μ (cellHat j)`, the shape the
  level-`n` induction needs, with `multOne = rvMat false` from the landed file.  Also
  `multOne_cast_mul`, `mem_cellHat_topCell_iff`, `set_ret_two`.
  **Corrections recorded from that member:** (i) my brief said the type-`true` induced interval is a
  *suffix*; it is a *prefix* `[0, Λ − λ botCell)` — the brief was wrong, the member's example
  (`λ=(0.5,0.3,0.2)`, `π=(0 2)`, return time 4) is the reason; (ii) induced invariance of
  `μ.restrict (Ico 0 cut)` reduces to one additivity step, and the missing `MeasurableSet (T '' S)` is
  free because `T` is injective, so `T '' S = (T⁻¹) ⁻¹' S` and `measurable_exchEquiv_symm` applies.
* **`MasurVeech/MasurVeech/EnlargeInput.lean`** (swarm `smvws3lwk` m1, namespace `PacketP10`) —
  **Step 3 of §10.3 discharged unconditionally** (`step3_core`: the two-case first-return analysis
  with `Nat.find` truncation at the first crossing), `enlargeInput_of_step1_step2`,
  `enlarge_balanced_set_of_step1_step2`, `cs_append_eq_sum`, `volume_mass_of_secondary_in`, and
  `enlargeInput_of_exit_word`, which reduces `EnlargeInput` to a purely combinatorial exit word.
  **Still open:** (C) existence of that exit word for every (admissible vertex, last-arrow type, `A₀`)
  with a `Q`-bound — a real combinatorial statement of the same family as Cor. 4 — and Step 2's
  coding of the landed Lemma 4.  The member continues on exactly those two.
* **`smvwrcl9u` ended exhausted**: after the second rejection its direction died and its model budget
  was spent.  The towers work (level-`n` formula, level-`n` floors, type `true`) therefore moved to a
  fresh swarm **`smvwtehvp`** (2 members, targets A and B above), seeded on the two landed files and
  on the measurability observation above.

### Addendum 6: G6 landed; Mathlib *has* Lévy's theorem, so the §10.5 survival route is open

* **`MasurVeech/MasurVeech/RauzyPath.lean`** (swarm `smvwslisw` m1, accepted) — **G6**: for
  `simplexVolumeOn`-a.e. `x` there is `p : ℕ → Bool` with `x ∈ simplexCyl P (pfx p k)` for all `k`,
  with only `P.Admissible` and `2 ≤ n` as hypotheses.  Three ingredients, none assumed:
  `ae_pos_simplexVolumeOn` (a.e. strict positivity — and *everywhere* on the support, since
  `simplexMap` takes strictly positive values on the free region, so no hyperplane/Fubini argument
  at all), `CombData.simplexVolumeOn_cylStop_of_partition` (the stopping set is null, from the exact
  partition plus the mass identity, independent of the tree's existing hyperplane proof
  `CombData.simplexVolumeOn_cylStop`), and the greedy path with
  `simplexCyl_pfx_succ_subset` for the nesting.  `exists_measurable_path_ae` and a non-vacuity
  witness stay in the member's directory, not landed.
* **The §10.5 survival step is *not* blocked on missing machinery**: `Mathlib` has Lévy's upward
  theorem, `MeasureTheory.tendsto_ae_condExp`
  (`Mathlib/Probability/Martingale/Convergence.lean:426`),
  `∀ᵐ x, Tendsto (fun n => (μ[g | ℱ n]) x) atTop (𝓝 ((μ[g | ⨆ n, ℱ n]) x))`, plus
  `Integrable.tendsto_ae_condExp`.  So `hsurv` can be proved as: with bounded-length families, the
  never-hit set `Z` is measurable for the cylinder filtration, `μ (Z ∩ Δ γ) ≤ (1-c) μ (Δ γ)` on every
  level-`n` cylinder, hence the atomwise density `f n` of `μ[1_Z | ℱ n]` is `≤ 1-c`, while Lévy gives
  `μ[1_Z | ℱ n] → 1_Z`.  This replaces the earlier note that Lévy is absent (it is present; only
  conditional Borel–Cantelli as such is not, and Lévy suffices).
* New swarm **`smvwtgwq5`** (2 members): (A) `hsurv` from bounded length via `tendsto_ae_condExp`;
  (B) the concrete `CylTree` instance in the real setting (`Δ := simplexCyl`, `diam := Real.toNNReal
  ∘ Metric.diam`, `fam :=` Lemma 6 composed with Lemma 2), including the bounded-length field, with
  the two families as uniform providers.

### Addendum 7: Cor. 4 reduced to `PairReach`, with the uniform `C₁`

* **`MasurVeech/MasurVeech/Cor4.lean`** (swarm `smvwsf0m0` m1, namespace `CombData.Path`) — Cor. 4
  *modulo* the purely combinatorial predicate `PairReach P` ("from every admissible vertex every
  ordered pair of distinct letters occurs as `(last e, last !e)` at a reachable vertex"):
  `Q_nonneg`, `one_le_Q_diag`, `Q_growth` (a step whose *name* is `c` adds the *secondary* name to
  the positive set of row `a`), `exists_pos_row`, `exists_pos_word`,
  **`cor4_of_pairReach`**, and **`exists_uniform_bound`** — the single `C₁` of Lemma 2 over *all*
  admissible vertices, obtained by making `CombData α n` a `Fintype` through
  `(α ≃ Fin n) × (α ≃ Fin n)`.  That last theorem is exactly what R6.2's constant needs.
* **`PairReach` is not proved.**  The member has a paper proof (descent on `pos_T(last false)`, two
  block cases, counting, two-block manoeuvres), verified exhaustively for `n ≤ 5` and the descent
  step only up to `n = 6`; ~250–400 Lean lines remain (their NOTES §6).  The member continues on it,
  with a fallback: the *balanced-case* version of `PairReach` (a vertex whose column sums are within
  a factor `C`), which is weaker but sufficient for R6.2 and possibly a much shorter descent.  A
  second, independent attempt (swarm `smvwt8bkd`) is working the support-recursion route.

### Addendum 8: the two assembly lemmas of `hray` and `hinj` landed

These are the pieces of the final assembly that do not depend on any of the open packets; they turn
the packet outputs into the hypotheses of `Assembly.masurVeech_of_components`.

* **`MasurVeech/MasurVeech/RayCriterion.lean`** — the ray criterion, assembled.
  `iInter_closure_eq_singleton` (a nested family of sets through a common point whose diameters tend
  to `0` has `⋂ closure = {x}`; needs antitonicity and boundedness of the first member);
  `mem_simplexCyl_of_cone` (**a nonnegative real vector of total mass `1` in the cone `C(γ)` is a
  point of `Δ(γ)`** — this needed `x : α → ℝ≥0` *let-bound*, because `NNReal.coe_sum` does not match
  a lambda term under `instances` transparency, the recurring `ℝ≥0 = {r // 0 ≤ r}` unfolding trap);
  `eq_of_mem_cone_all`; and **`eq_of_mem_cone_of_diam`**: if `w k` are nested path cylinders through
  `lam` with `diam → 0` and `Sig` is a nonnegative vector of mass `1` in every `C(w k)`, then
  `Sig = lam`.  The hypotheses are exactly (i) G6 (`RauzyPath.exists_path_ae` plus nesting,
  landed), (ii) the a.e. shrinking (§10.5 + bounded length + Lévy, in flight), (iii) the tower
  formula (`Sig ∈ C(γ_n)` for all `n`, in flight).  Boundedness of `Δ(γ_0)` is
  `Lemma2Real.isBounded_simplexCyl`, landed.
* **`MasurVeech/MasurVeech/LengthInjective.lean`** — the measure-theoretic half of `hinj`:
  `measure_eq_of_floors`, two finite measures supported on `Ico 0 1` which agree on every atom of a
  refining sequence of partitions of `Ico 0 1` with mesh → 0 are equal (immediate from the landed
  `RefiningPartition.measure_restrict_eq_of_refining_partitions` plus
  `Measure.restrict_eq_self_of_ae_mem`).  The interface takes the support as
  `∀ᵐ x ∂μ, x ∈ Ico 0 1` rather than `μ (Ico 0 1) = 1`, to avoid an `ENNReal` arithmetic detour at
  the call site; the caller gets it from `μ (Ico 0 1) = 1 = μ univ`.

### Addendum 9: the level-`n` floors (type-false, per level) landed; and a defect in my own `RayCriterion` interface

* **`MasurVeech/MasurVeech/TowerLevelN.lean`** (swarm `smvwtehvp` m1, namespace `TowerN`) — the
  floor layer: `measurableSet_image_iterate`/`measurableSet_floor` (from
  `T^[j] '' A = ((exchEquiv.symm)^[j]) ⁻¹' A`, the same injectivity trick as induced invariance),
  `pairwiseDisjoint_floor`, `iUnion_floor_sigma` (the base is the *disjoint* union of the floors of
  height `≤ 2`), `measure_floor` (each floor has its cell's mass), `kac_level1`, the level-2 case,
  `exch_iterate_countUp`, `subset_iUnion_image_levelTwoBase`, and the inductive
  `levelSucc_refine/_decomp/_measurable/_kac/_cover` with `permAfter`/`lamAfter` (the word
  `false^k`).
  **Open, and correctly not assumed:** the `Q`-multiplicity of the level-`n` floors — the number of
  level-`n` floors over `β` inside the original cell `α` is `Q(γ)_{αβ}` — hence the cell-indexed
  form `μ (cell α) = ∑ β (Q(γ)_{αβ} : ℝ≥0∞) * μ (level-n cell β)`; and the general word and type
  `true`.  The member continues on the multiplicity.
* **Defect in my `RayCriterion.lean`.**  `mem_simplexCyl_of_cone` (and so
  `eq_of_mem_cone_of_diam`) takes `Sig ∈ cone (Q w)`, but `cone` in this project demands a
  **strictly positive** renormalised vector, while the tower formula only yields a **nonnegative**
  one (level-`n` cell masses may vanish; full support would need minimality, which is deferred).
  So the honest interface is `Sig = qApply (Q w) y` with `y ≥ 0` and the conclusion
  `(fun a => ⟨Sig a, _⟩) ∈ closure (simplexCyl P w)`, which combines with the landed
  `iInter_closure_eq_singleton`.  The closure lemma is exactly true by an explicit estimate
  (`z t := (y + t)/(1 + t W)`, `xt t := Q (z t)`, `|xt t a - x a| ≤ 2 t W`), now swarm
  `smvwtwz74`.  Until it lands, `eq_of_mem_cone_of_diam` must not be used with a tower-formula
  hypothesis; it is stated for the strict cone only.

### Addendum 10: Cor. 4 unconditional (`PairReach` proved) and the uniform Lemma 2

* **`MasurVeech/MasurVeech/PairReach.lean`** (swarm `smvwsf0m0` m1, accepted) — **`PairReach` proved**,
  hence **Cor. 4 unconditional**: `CombData.pairReach`, `pairReach_all` (the vacuous `n ≤ 1` case),
  `cor4` and `exists_uniform_bound'` (`∃ C₁ ≥ 1, ∀ P admissible, ∃ w, 1 ≤ Q w ≤ C₁`).  The descent is
  on `pos_T(last false)` with the Case A / Case B split (`descent_step`, `descent_subclaim` via
  `card_filter_lt/le/gt` and `PacketP4.no_block`), and the termination comes from a *strong
  induction* (`exists_last_true_first`) iterating the descent, not from a postulated rank function.
  The second, independent attempt (`smvwt8bkd`) was stopped: same target, no longer worth its cost.
* **`MasurVeech/MasurVeech/Lemma2Uniform.lean`** (mine) — **Lemma 2 with a constant uniform in the
  node**, composing the landed `Lemma2Real.lemma2_append` with `exists_uniform_bound'`:
  `exists_C1_nn` (the Cor. 4 constant as `ℝ≥0`) and
  `lemma2_uniform (hn) (C) (hC) : ∃ c > 0, c ≤ 1, ∀ P admissible γ, C-balanced →
  ∃ w ⊇ γ, c·vol Δ(γ) ≤ vol Δ(w) ∧ diam Δ(w) ≤ (1-c)·diam Δ(γ)` with
  `c = ((n · C₁ · C)⁻¹)^n` depending only on `n` and `C`.  This is the `fam_mass`/`fam_diam` input of
  the `CylTree` instance, with no per-node constant left.
* **Obstacle for the `CylTree` instance, found while writing the above.**  `NestedCylinder.CylTree`
  demands `Δ [] = univ`, but in the real setting `simplexCyl P []` is the **open** simplex (it is
  `cone 1 ∩ simplexOn`, and `cone` wants strict positivity), not `simplexOn`.  So the instance must
  either (i) live on the subtype `{x : α → ℝ≥0 // x ∈ simplexCyl P []}` (then `Δ [] = univ` holds and
  `simplexVolumeOn α` restricts to it, the boundary being null), or (ii) `CylTree.root` must be
  weakened to `μ (univ \ Δ []) = 0`.  Option (i) avoids touching the landed file and is what I will
  ask for; it also makes the `diam`/`closure` transfers go through the subtype metric.

### Addendum 11: the level-`n` tower formula landed for `false`-words; the type-`true` step is the remaining gap

* **`MasurVeech/MasurVeech/LevelN.lean`** (swarm `smvwtehvp` m2, namespace `Tower`) — the tower
  formula at level `n`:
  * **`restrict_cut_invariant`** — the analytic input the towers work had been missing for two
    rounds: `μ.restrict (Ico 0 (cut π lam))` is invariant under the return map
    `exch (piHat π) (lamHat π lam)`, from `μ.map (exch π lam) = μ` and
    `lam (topCell π) < lam botCell`; iterated by `restrict_lamN_invariant`;
  * `tower_formula_level` (the matrix identity with multiplicities `multN`),
    `tower_formula_level_comb`, and `tower_formula_level_pathQ`:
    `μ (cellOf P lam a) = ∑ b, ((Path.Q P (List.replicate k false) a b).toNat : ℝ≥0∞) *
    μ (cellAt P (List.replicate k false) lam b)`, for `lam ∈ simplexOn`, `μ.map (P.toIET lam) = μ`
    and `IterFalseP P lam k`;
  * `tower_formula_level_one` checks `k = 1` against the landed `tower_formula_one_step_mult`.
  `cellAt` is the cell of the renormalised `mkIETFun` at the vertex reached by `γ`.  Landing repair:
  `CombData.vertex_replicate_succ` clashed with `Cor4.lean` and is renamed
  `vertex_replicate_false_succ`.
* **The gap: type `true`.**  The formula is proved only for words of the form `List.replicate k
  false`, and a.e. `λ` has both Rauzy types infinitely often, so the actual path is mixed.  The
  member's model budget was spent, so the mirror was handed to a fresh swarm **`smvwwu4khg`** (as
  `smvwu4khg`) with the route spelled out: the induced interval for type `true` is the **prefix**
  `Ico 0 (tot lam − lam botCell)`, and `rvStep P true = (rvStep P.inv false).inv`
  (`Step.lean`'s `rvStep_inv`) reduces the whole thing to the landed `false` case at `P.inv`,
  transported by `mkIETFun_inv_left`/`imageLengths`/`perm_inv`.  Targets: the type-`true` return-time
  description, `rvStep_toComb_true_perm`, `restrict_cut_invariant_true`,
  `tower_formula_one_step_mult_true`, and finally the formula along an arbitrary word.

### Addendum 12: the closure lemma landed — the `hray` interface is now correct

* **`MasurVeech/MasurVeech/ClosureSimplex.lean`** (swarm `smvwtwz74` m1, namespace `RayCriterion`,
  accepted) — `mem_closure_simplexCyl_of_nonneg`: a nonnegative `Sig` of total mass `1` with
  `Sig = qApply (Q w) y`, `y ≥ 0`, is in `closure (simplexCyl P w)`.  Proof: `z t := (y + t)/(1 + tW)`
  is strictly positive, `xt t := Q (z t) ∈ cone Q` with total mass `1`, hence `xt t ∈ simplexCyl`;
  and `|xt t a − x a| ≤ 2 t W` with `t = ε/(2(W+1))` gives `dist ≤ εW/(W+1) < ε`.  Only `0 ≤ W` is
  used, never `0 < W` — which is what covers the degenerate node.  Also
  `mem_closure_simplexCyl_of_nonneg'` (`hSig0` derived from `hSig` and `Path.Q_nonneg`, so the caller
  need not supply it), the aux iliaries `sum_qApply_cast`, `totSum_eq_sum_colR`, `qApply_add_div`,
  `rowSum`/`totSum`, and **`eq_of_nonneg_preimage_of_diam`** — the ray criterion with a *nonnegative*
  preimage instead of the strict cone.
* **This supersedes `RayCriterion.eq_of_mem_cone_of_diam`** for any tower-formula hypothesis: the
  tower formula gives `λ(μ) = Q(γ_n) λ^{(n)}` with `λ^{(n)} ≥ 0` (the level-`n` cell masses can
  vanish; positivity needs minimality, which is deferred), never `> 0`.  The strict-cone lemma stays
  in the tree but must not be fed a tower-formula hypothesis.  With
  `eq_of_nonneg_preimage_of_diam` + `RauzyPath.exists_path_ae` (nested cylinders through `λ`,
  `Lemma2Real.isBounded_simplexCyl` for boundedness) + the a.e. shrinking, `hray` is now a matter of
  supplying `∀ k, lambdaOf μ P lam = qApply (Q (w k)) (y k)` with `y k ≥ 0` — i.e. the level-`n`
  tower formula, which is landed for `false`-words and in flight for arbitrary words.

### Addendum 13: the concrete `CylTree` landed, and its `ExtData` provider closed

* **`MasurVeech/MasurVeech/RealCylTree.lean`** (swarm `smvwtgwq5` m1, namespace
  `NestedCylinder.RealCyl`, accepted) — the concrete `CylTree` of the real Rauzy–Veech algorithm:
  `realCylTree : CylTree (GoodSpace P) (gMeas P) (cReal CD ED)` with **all twelve fields** proved,
  `realCylTree_boundedLength` (`L = CD.L + ED.L`), `realCylTree_c_pos`, `realCylTree_c_lt_one`,
  `realCylTree_tendsto` (only `hsurv` left), and the a.e. transfer `ae_iff_gMeas`.
  **Structural finding (recorded because it is a real trap):** `CylTree`'s exact (H1) *fails* for the
  raw `simplexCyl` family — `cylStop` is nonempty (only null) — and repairing it by adjoining a junk
  set breaks `disj`/`fam_pair`.  The repair is to delete the null lamination,
  `goodSet P = simplexCyl P [] \ ⋃ cylStop`, carry `gMeas P` on that conull subtype, and transfer
  a.e. statements back with `ae_iff_gMeas`.  `nonempty_coverData` states exactly what Lemma 6 does
  *not* give (the length bound).
* **`MasurVeech/MasurVeech/ExtData.lean`** (mine) — **`ExtData` is now unconditional**:
  `extData (P) (hP) (hn) : ExtData P`, from `CombData.exists_uniform_bound'` (Cor. 4) plus
  `Fintype (CombData α n)` built as `(α ≃ Fin n) × (α ≃ Fin n)` (the pattern of
  `Cor4.exists_uniform_bound`), with `L := univ.sup (fun Q => (cor4Word Q).length)`.  Supporting:
  `ne_nil_of_one_le` (an entrywise-`≥ 1` `Q`-matrix cannot come from `[]`, since `Q [] = 1` is zero
  off the diagonal), `cor4C`, `one_le_cor4C`, `cor4Word`, `cor4Word_spec`.  So one of the two
  providers of `realCylTree` is discharged; `CoverData` (Lemma 6 + the exit word's length bound)
  still needs `EnlargeInput`.

### Addendum 14: §10.5 closed (no survival hypothesis), the tower multiplicity landed, `EnlargeInput` down to one combinatorial case

* **§10.5 CLOSED — `MasurVeech/MasurVeech/NestedBounded.lean`** (swarm `smvwtgwq5` m2, accepted).
  `nested_cylinder_tendsto_of_bounded`: (H1) + (H2) + **bounded length**
  (`∀ γ δ ∈ fam γ, δ.length ≤ γ.length + L`) give a.e. `diam (Δ(γₙ(x))) → 0`, with **no survival
  hypothesis**; variants `_prob` and `_uniform_fam` (one finite `W` with `fam γ ⊆ {γ ++ w}`, the
  interface the concrete tree needs).  The proof is elementary — no `condExp`, no Lévy: the never-hit
  sets `N(n₀)` are nested, each surviving block of `L` levels loses a factor `c` (bounded length is
  what makes "inside `Gγ`" versus "inside `Δγ \ Gγ`" a dichotomy at level `|γ|+L`), so
  `μ(N ∩ Δγ) ≤ (1-c)^j μ(Δγ) → 0`.
  **Two of my errors corrected, machine-checked:** (1) `hsurv` is **false** for (H1)+(H2)+bounded
  length — the dyadic tree of `NestedCylinderCounterexample.lean` (`not_hsurv`, `TC_bounded_length`,
  now landed) has `Tl` dying on `Δ[true,true]` of measure `1/4`; (2) Lévy gives only
  `∀ n₀, μ(Never n₀) = 0`, which in `TC` holds while `hsurv` fails.  So the `hsurv`-explicit
  `nested_cylinder_tendsto` is a dead end for the real tree; **use the `_of_bounded` form**.
* **The tower multiplicity — `MasurVeech/MasurVeech/TowerQ.lean`** (swarm `smvwtehvp` m1, accepted).
  `measure_image_exchK`: induced invariance at **every** level, proved by induction on `k` (split
  `A` along the level-`(k+1)` cells, so `T_{k+1} = T_k^[h_β]`, `h_β ∈ {1,2}`, and no comparison of
  images at different heights is ever needed).  `level_formula`: `μ (cell k a) = ∑ b, multOne π_k a b
  · μ (cell (k+1) b)` from `μ.map T = μ` alone; `level_iterate` iterates it; `Qmat_eq_pathQ_real` +
  `Qmat_toNat` identify the product of `multOne` matrices with `Path.Q` on `false^k`;
  `level_iterate_pathQ` is the formula asked for.  Restriction: `false^k` only, and `Path.Q` appears
  as `.toNat` (`Qnat_cast_ennreal` + `Path.Q_nonneg` justify it; there is no `ℤ → ℝ≥0∞` cast).
* **`EnlargeInput`: Step 2 done, one case left — `MasurVeech/MasurVeech/EnlargeStep2.lean`**
  (swarm `smvws3lwk` m1, namespace `PacketP10b`): `step2_point`, `step2_coding` (the half-mass set `G`
  with `C = 2n`, via the landed `lemma4_source`), `enlargeInput_of_step1` (**`EnlargeInput` from
  Step 1's output alone**), `exists_exit_step`, `exists_exit_of_not_both`,
  `exists_enlargeInput_of_not_both`, `exists_enlargeInput_singleton`.
  **Open: case (C′)** — both last letters of `vertex P γ` inside `A₀` (`A₀` proper): need `δ ⊇ γ`
  whose last name is outside `A₀`, with growth and mass bounds.  The member's model budget was spent,
  so a fresh swarm **`smvwui0qj`** has that single statement, with the `CombData.cor4` route as the
  suggested attack (entrywise positivity from Cor. 4 + `cs_append_le_sup_mul` for growth +
  `volume_mass_of_secondary_in` for mass).  `exists_enlargeInput_of_not_both` + (C′) is the whole of
  `EnlargeInput`, hence of Lemmas 5, 6 and the shrink layer.

### Addendum 15: the mesh input of `hinj` identified and delegated (Cor. 2)

`hinj` needs the level-`n` floor partitions to have mesh → 0.  Recording the derivation, because it is
not a corollary of the diameter shrinking alone and I had it wrong twice:

* `λ^{(n)} := Q(w n)⁻¹ λ` is the renormalised vector, and `λ^{(n)}_* := ∑ β λ^{(n)}_β` is the length
  of the level-`n` **base interval** — a sub-interval of `[0, Λ)`, so the floor lengths are the
  `λ^{(n)}_β` themselves in the original coordinates and the mesh is `max_β λ^{(n)}_β ≤ λ^{(n)}_*`.
  (The simplex point is `λ̂^{(n)} = λ^{(n)}/λ^{(n)}_*`; the `λ^{(n)}_β` do *not* sum to `1`.)
* `λ̂^{(n)} ∈ simplexCyl P (w n)` and `λ̂ ∈ ⋂ n, simplexCyl P (w n)`, so `diam → 0` gives
  `λ̂^{(n)} → λ̂`; with `ae_pos_simplexVolumeOn` this keeps `min_β λ̂^{(n)}_β` bounded below.
* `λ^{(n)}_* = Λ / (∑ a, (Q(w n) λ̂^{(n)}) a)` and `∑ a, (Q ŷ) a = ∑ b, colsum_b · ŷ_b`, so it
  suffices that the **column sums blow up along the path**: `cs n := ∑ b, colsumNN (Q (w n)) b`
  satisfies `cs (n+1) ≥ cs n + 1` (each step replaces one column by itself plus another, and every
  column sum is `≥ 1`), hence `cs n → ∞`.
* Therefore `λ^{(n)}_* → 0` a.e., which is the mesh statement `LengthInjective.measure_eq_of_floors`
  consumes.

Delegated as swarm **`smvwunvxb`**, with the shrinking (`hdiam`) as an explicit hypothesis because the
concrete `CylTree`'s `CoverData` provider is still open — the derivation above does not depend on it.
This is the last unassigned input of `hinj`; the other two (`RefiningPartition`, `measure_eq_of_floors`,
and the tower formula's mass identity) are landed.

### Addendum 16: the type-`true` step: targets 1–3 landed (target 4, arbitrary word, in flight)

* **`MasurVeech/MasurVeech/TrueStep.lean`** (swarm `smvwu4khg` m1, namespace `TowerTrue`, 1276 lines)
  — the Rauzy **type-`true`** step, first three targets:
  * `cutT = Λ − λ botCell` and the two-case return-time description (`exch_mem_cutT_of_ne_top`,
    `exch_mem_cutT_of_top_low`, `exch_mem_Ico_cutT_tot_of_top_high`, `exch_exch_eq_true`,
    `exch_sq_mem_cutT`, `retT`, `retT_mem`, `retT_min`, `retT_eq_one_or_two`) — the induced interval
    is the **prefix** `[0, Λ − λ botCell)`, as an earlier member showed, and the return time is `1`
    or `2` with `2` exactly on the upper part of the top cell;
  * **`firstReturnT_eq`**: the return map *is* `mkIETFun (lamT π lam) (piHatT π) 0`;
  * **`firstReturnT_eq_rvStep`** and **`rvStep_toComb_true_perm`** — the identification the project
    lacked, obtained from `rvStep_inv : rvStep P true = (rvStep P.inv false).inv` plus the landed
    `false` case at `P.inv` and `perm_rvStep_false`, then inverting the permutation;
  * **`restrict_cut_invariant_true`**, `tower_formula_one_step_true`,
    **`tower_formula_one_step_mult_true`** with `multOneT_eq_rvMat` (and `multOneT`, `cellHatL`,
    `eT = insertEquiv (topCell π)` for the letter-indexed new cells).
  Landed ahead of the member's own submission because it is complete, compiling (both modes),
  warning-free and axiom-clean on seven headline declarations — the swarm's budget is not worth
  risking 1276 lines of verified work over.
  **Still open (target 4):** the level-`n` formula along an **arbitrary** word, by combining the
  landed `false`-word result (`TowerQ.level_iterate`, `LevelN.tower_formula_level`) with this `true`
  case through `Path.Q_cons`/`Path.Q_append`.  That is the last input of `hray`.

### Addendum 17: a cleaner `CylTree` by tie-breaking; and the length bound is a *strengthening* of (C′)

* **`MasurVeech/MasurVeech/CylTreeReal.lean`** (swarm `smvwu1zym` m1, namespace `CylTreeReal`,
  accepted) — second, cleaner concrete `CylTree`.  Instead of deleting the null lamination
  (`RealCylTree`'s repair), it **resolves the ties**: `nbit x γ := x ∈ cyl (γ ++ [true])`,
  `Δ γ := {x | path x γ.length = γ}`.  Then `Delta_root`, `Delta_nest`, `Delta_cover`, `Delta_disj`
  hold **literally**, `carrier_fields` is unconditional, and `mu_Delta` gives
  `mu (Δ γ) = vol (cyl γ)` up to the null `bad γ`.  `provider_of_cover` makes the **antichain free by
  pruning** (`prune`, `prune_subset`, `prune_antichain`, `iUnion_prune`, `sum_prune`: the union and
  the mass are unchanged), so no consumer proves laminarity.  `exists_cylTree_of_cover` reduces
  everything to Lemma 6's family (`hpre`, `hdisj`, `hmass`, `hbal`) plus one length bound
  `f : CombData α n → ℕ` with `∀ γ l ∈ G γ, l.length ≤ γ.length + f (vertex P γ)`, and returns
  `∃ c, 0 < c ∧ c < 1 ∧ T ∧ L, ∀ γ δ ∈ T.fam γ, δ.length ≤ γ.length + L`.
* **The length bound is the next gap, and it is a *strengthening* of (C′).**  Lemma 5's exit word
  depends on `A₀ = maxSet (Q γ)`, so a Lemma 6 member's length depends on the `A₀` chain, not only on
  `vertex P γ`.  What makes the bound provable is that the exits can be chosen depending only on
  `(vertex, A₀)` — finitely many pairs since `CombData α n` is a `Fintype` — and the Lemma 6 iteration
  has at most `n − 1` steps, so `f := n * (max exit length)` works.  So the statement to prove, after
  (C′), is: **a bounded-length exit word, chosen as a function of `(vertex, A₀)`**, with the growth
  and mass bounds.  Recorded as the packet after `smvwui0qj`.

### Addendum 18: the last mile of `hray` landed (`TowerGlue`)

* **`MasurVeech/MasurVeech/TowerGlue.lean`** (mine, namespace `TowerGlue`) — the translation from the
  tower formula to the ray criterion, and the final step of `hray`:
  * `coe_toNat`: `((Q a b).toNat : ℝ) = Q a b` for `Q ≥ 0` — the cast that makes the `ℤ`-valued
    `Path.Q` usable against `ℝ≥0∞` (`Qnat_cast_ennreal` gives the `ℝ≥0∞` half);
  * `real_eq_qApply`: if `μ (cellOf a) = ∑ b, ((Q γ a b).toNat : ℝ≥0∞) * μ (κ b)` (the level-`n`
    tower formula), then the length vector
    `a ↦ μ.real (cellOf a)` equals `qApply (Q γ) (fun b => (μ (κ b)).toReal)`;
  * **`ray_of_shrink_and_tower`**: if the cylinders along a path through `lam` are nested, bounded,
    contain `lam` and have diameters `→ 0`, and the length vector of an invariant probability measure
    on `[0,1)` lies in `qApply (Q (w k))` of a **nonnegative** vector for every `k`, then that length
    vector **is** `lam` — so the ray parameter is `c = 1`.  This composes the landed
    `RayCriterion.eq_of_nonneg_preimage_of_diam` with `Assembly.sum_lambdaOf`.
  So `hray` is now: `RayCriterion.ae_exists_path_hypotheses` (landed) + the a.e. shrinking
  (`CylTreeReal` + `nested_cylinder_tendsto_of_bounded`, conditional on the length bound) + the
  arbitrary-word tower formula (`TowerQ`/`LevelN` for `false^k`, `TrueStep` for the `true` step,
  target 4 pending) + `ray_of_shrink_and_tower` (landed).

### Addendum 19: **the arbitrary-word tower formula landed** (checkpoint 2 met)

* **`MasurVeech/MasurVeech/TrueStep.lean`** (swarm `smvwu4khg` m1, namespace `TowerTrue`,
  **1662 lines**, accepted) — the Rauzy type-`true` step **and the arbitrary-word tower formula**:
  * type `true`: `cutT = Λ − λ botCell`, return time `1` except on the upper part
    `[splitT, upperEnd top)` of the top cell where it is `2` (`retT`, `retT_mem`, `retT_min`,
    `retT_eq_one_or_two`), `firstReturnT_eq` (return map `= mkIETFun (lamT π lam) (piHatT π) 0`),
    `firstReturnT_eq_rvStep`, **`rvStep_toComb_true_perm`** (via `rvStep_inv`),
    `restrict_cut_invariant_true`, `tower_formula_one_step_true`,
    **`tower_formula_one_step_mult_true`** (`multOneT_eq_rvMat`);
  * **`tower_formula_one_step_comb`** and **`tower_formula_level_pathQ_any`**: for **any** word `γ`
    with the single predicate `IterOK P lam γ` (`StepOK P lam ε := ε = true ↔ λ(last false) <
    λ(last true)`, iterated with `hatLam` renormalisation — the Rauzy algorithm's own type rule),
    `μ (cellOf P lam a) = ∑ b, ((Path.Q P γ a b).toNat : ℝ≥0∞) * μ (cellAt P γ lam b)`.
  So §10.4 is closed for arbitrary words.  The interim 1276-line copy (targets 1–3) which I landed
  from the member's finding is replaced by this.
* **Remaining glue for `hray`** (mine, not a packet): the G6 greedy path
  (`RauzyPath.exists_path_ae`) must be shown to satisfy `IterOK`, since the tower formula is stated
  for `IterOK`-words while G6 builds the path from `simplexCyl_eq_union`.  Ingredients all landed:
  `mem_simplexCyl_append_iff` (the `ε`-type condition at a vertex), `IsRenorm.unique` (the
  renormalised vector is unique), `hatLam`/`lamHat` (`LevelN.lengthsInBottom_hatLam`,
  `rv_length`).

### Addendum 20: `IterOK` glue, part 1 (the length identities)

* **`MasurVeech/MasurVeech/IterGlue.lean`** (mine) — the length half of the `IterOK` bridge between
  the tower formula (`TrueStep.tower_formula_level_pathQ_any`, stated for `IterOK` words) and the a.e.
  path of G6 (built from `simplexCyl_eq_union`):
  * **`qApply_rvMat_hatLam`**: `qApply (rvMat ε) (hatLam P ε lam) = lam` — **provided** the type
    condition `lam (last (!ε)) ≤ lam (last ε)`.  The hypothesis is *not* removable: `hatLam` uses
    truncated subtraction, so without it the identity is false.  This is the one-step inverse of
    `rvMat` on length vectors;
  * `stepOK_le`: `StepOK P lam ε → lam (last (!ε)) ≤ lam (last ε)`;
  * **`qApply_lamAfter`**: along an `IterOK` word,
    `qApply (Path.Q P γ) (lamAfter P γ lam) = lam` — i.e. `lamAfter` is the `Q(γ)⁻¹`-transport of
    `lam`, by induction on `γ` with `rvStep`/`hatLam` matching `Path.Q`'s recursion.
* **Remaining (part 2)**: the joint induction showing the G6 greedy path
  (`RauzyPath.pathWord`/`pathBranch`) satisfies `IterOK`.  Route: at step `j` the branch is decided by
  `pathBranch_eq_true_iff` (`x ∈ simplexCyl P (γ ++ [true])`), and
  `mem_simplexCyl_append_iff` gives a renormalised `w` with `w (last (!e)) < w (last e)`; `w` is
  `lamAfter P γ x` by `qApply_lamAfter` + `IsRenorm.unique`, with **positivity of `lamAfter` carried
  in the same induction** (it follows from `hatLam`'s definition plus the comparisons already
  proved).  So `IterOK` and `∀ a, 0 < lamAfter P γ x a` are proved simultaneously.

### Addendum 21: Corollary 2 landed unconditionally — `hinj`'s mesh is closed

* **`MasurVeech/MasurVeech/MeshShrink.lean`** (swarm `smvwunvxb` m1, namespace `MeshShrink`,
  accepted) — **Corollary 2** (the level-`k` base interval shrinks to a point), with only
  `P.Admissible` and `2 ≤ n`:
  * `eventually_coord_lt`, `tendsto_total`: for **every** path `p` and **every** renormalisation
    sequence `w` with `IsRenorm P (pfx p k) lam (w k)`, all coordinates `w k b → 0`;
  * `ae_tendsto_total`, `ae_exists_tendsto_coord` (a.e., every path through `lam`);
  * **`ae_tendsto_levelLength`**: `Tendsto (fun k => levelLength P p lam k) → 0` — the literal target;
  * `total_eq_of_isRenorm`, `total_eq_Lam_div`: the canonical `λ^{(k)}_* = Λ / ∑_a (Q_k λ̂^{(k)})_a`.
* **The mechanism is *not* the diameter shrinking — my brief's steps 2–3 were false.**  What proves it
  is the *column-sum* count: `w(k+1) b = w k b - [b = nm k] w k (scd k)` from `Q_{k+1} = Q_k · rvMat`,
  every letter is the **main** name infinitely often (`PacketP4.name_infinite`) and the **secondary**
  name infinitely often (the `a runs` argument, `rvStep_last_self`, `secondary_eq_of_type_ne`), hence
  `Cs k b ≥ #{j < k : scd j = b} → ∞`, and `Λ ≥ (Cs k b) · (w k b)` gives `w k b → 0`.  So Cor. 2 is a
  counting statement about the Rauzy path, independent of §10.5.  `hdiam` unused.
* Consequence: with `LengthInjective.measure_eq_of_floors` and the arbitrary-word tower formula both
  landed, **`hinj` has no analytic input left** — only the tower/floor bookkeeping (the level-`k`
  floors as a `Finset (Set ℝ)` partition of `Ico 0 1` with refinement, and the mass agreement from
  `det Q = 1`).

### Addendum 22: **the greedy-path induction closed** — `hray` has one input left

* **`MasurVeech/MasurVeech/IterGlue2.lean`** (mine) — the greedy path of G6 satisfies `IterOK`,
  with a positive renormalised vector, proved **simultaneously** (positivity is what feeds
  `IsRenorm.unique`):
  * `iterOK_append_singleton`: `IterOK P lam (γ ++ [e]) ↔ IterOK P lam γ ∧
    StepOK (vertex P γ) (lamAfter P γ lam) e`;
  * `lamAfter_append_singleton`: `lamAfter P (γ ++ [e]) lam = hatLam (vertex P γ) e (lamAfter P γ lam)`;
  * `stepOK_last_iff`: `StepOK P lam ε ↔ lam (last (!ε)) < lam (last ε)`;
  * **`iterOK_pathWord`**: for `x ∈ simplexCyl P []` never in a `cylStop`,
    `∀ k, IterOK P x (pathWord P x k) ∧ ∀ a, 0 < lamAfter P (pathWord P x k) x a`.
  The proof: `mem_simplexCyl_append_iff` gives a renormalised `w` with
  `w (last (!e)) < w (last e)`; `qApply_lamAfter` + positivity make `lamAfter` an `IsRenorm`, so
  `IsRenorm.unique` gives `w = lamAfter` and the strict comparison *is* the algorithm's `StepOK`.
* Consequence: the tower formula (`TrueStep.tower_formula_level_pathQ_any`, stated for `IterOK` words)
  now applies along the very path G6 produces, and `TowerGlue.real_eq_qApply` turns it into the
  `qApply` form that `RayCriterion.eq_of_nonneg_preimage_of_diam` consumes.  So **`hray` is reduced to
  a single input: the shrinking `Tendsto (fun k => Metric.diam (simplexCyl P (pathWord P lam k))) → 0`**,
  which is `CylTreeReal.exists_cylTree_of_cover` + `NestedCylinder.CylTree.nested_cylinder_tendsto_of_bounded`
  and therefore needs only the `CoverData` length bound — i.e. a bounded-length exit word, the
  strengthening of (C′) that is still running.

### Addendum 23: **case (C′) closed — `EnlargeInput` is a theorem** (checkpoint 1 met)

* **`MasurVeech/MasurVeech/ExitBoth.lean`** (swarm `smvwui0qj` m1, namespace `PacketP10c`,
  accepted) — case (C′) and hence **`EnlargeInput` unconditional modulo its balance/domination
  hypotheses**:
  * `SecIn V A₀ w` (every arrow's secondary in `A₀`) ⟹ the entries of `Path.Q V w` outside `A₀` are
    diagonal (`Q_col_zero`) — this is the `hzero` input of `volume_mass_of_secondary_in`;
  * `lastFalse_replicate_true`: `j` `true` steps put the letter at bottom position `n-1-j` last (and
    the mirror), which gives the scans `exists_exit_bottom`/`exists_exit_top`;
  * **`key_improve`** (the core): if no letter outside `A₀` lies beyond either pivot
    (`p = pos_B(last true)`, `q = pos_T(last false)`), then a block strictly decreases `p` or `q`.
    Proof: `{pos_B < p} ⊆ {pos_T < q}` and `{p ≤ pos_B} ⊆ {q ≤ pos_T}`, so `card_filter_lt` gives
    `p = q`, the strict prefixes coincide, and an invariant initial segment contradicts `Admissible`.
    **Note the mechanism: this is irreducibility doing the work, not growth of `Q`** — different from
    the Cor. 4 descent;
  * `exists_exit_aux` (induction on `p + q`), `exists_exit_both`, **`exists_exit_uniform`**
    (`W : CombData α n → List Bool` depending only on the *vertex*, with `K` bounding `qnn`),
    `exists_exit_both_full`;
  * **`exists_enlargeInput`**: for all `γ`, proper nonempty `A₀`, `C₀ ≥ 1`, with the balance and
    domination hypotheses, `∃ C₁ c₁ > 0, EnlargeInput P γ A₀ C₁ c₁`.
* **What remains for Lemma 5** (mine): hoist the constants to be `A₀`-uniform.  Reading
  `exists_enlargeInput_both`, `C₁ = C₀·(1 + 2n·nK)` and `c₁ = ((K n C₀)^n)⁻¹` where
  `K = K(A₀)` is a maximum over the (finite) diagram *for that `A₀`* — so the `γ`-dependence is
  already absent and a finite maximum over the proper nonempty `A₀ ⊆ univ` gives the uniform provider
  `hInput` that `Lemma5Bridge.lemma5ShapeUniform_of_enlarge` consumes.  Then Lemma 6 unconditional,
  then `CoverData`, then the shrinking, then `hray`.

### Addendum 24: `hray` is one hypothesis from proved (`HrayAssembly`)

* **`MasurVeech/MasurVeech/HrayAssembly.lean`** (mine) — **`hray_of_shrink`**: for admissible `P`
  with `2 ≤ n`,
  ```
  (∀ᵐ lam, Tendsto (fun k => Metric.diam (simplexCyl P (pathWord P lam k))) atTop (𝓝 0)) →
  ∀ᵐ lam, ∀ μ : ProbabilityMeasure ℝ, Invariant μ (P.toIET lam) → μ (Ico 0 1) = 1 →
    ∃ c, lambdaOf μ P lam = c • (fun a => (lam a : ℝ))
  ```
  i.e. the ray criterion (R7.4/R6.4) from the single remaining analytic input.  The proof assembles,
  along the *greedy* path `pathWord`: `mem_pathWord` (the cylinders contain `lam`),
  `antitone_simplexCyl_pfx` + `isBounded_simplexCyl_pfx` (nesting and boundedness),
  `iterOK_pathWord` (`IterOK`, hence `tower_formula_level_pathQ_any` applies),
  `TowerGlue.real_eq_qApply` (the `qApply` form), and `TowerGlue.ray_of_shrink_and_tower`
  (which uses `Assembly.sum_lambdaOf` and `RayCriterion.eq_of_nonneg_preimage_of_diam`).
  Axiom-clean, build green at 8760 jobs.
* So `hray` = **shrinking only**.  The shrinking is `CylTreeReal.exists_cylTree_of_cover` +
  `NestedCylinder.CylTree.nested_cylinder_tendsto_of_bounded`, whose only input is `CoverData` —
  a single `C` with Lemma 6's family per node plus a length bound `f (vertex P γ)`.
* **What `CoverData` still needs**: the *uniform* `EnlargeInput` provider.  `PacketP10c.exists_enlargeInput`
  gives constants depending on `A₀` (the `γ`-dependence is already absent: `C₁ = C₀(1 + 2n·nK)`,
  `c₁ = ((K n C₀)^n)⁻¹` with `K = K(A₀)`), and the `nil` branch's constants are numeric (`growth 2`,
  mass ratio `1/2`).  So with `K* := sup over proper nonempty A₀ of K(A₀)` and
  `(C₁, c₁) := (C₀(1 + 2n·nK*), ((K* n C₀)^n)⁻¹)`, `PacketP10c.enlargeInput_mono` (mine, in
  `.scratch/mvuni/Uni.lean` together with `goodSets`, `goodSets_nonempty`, `mem_goodSets`) pushes both
  branches through.  **This hoisting is the last link of the shrink chain and is not landed.**

### Addendum 25: both remaining links delegated, with the monotonicity lemma landed

* **`MasurVeech/MasurVeech/UniformEnlarge.lean`** (mine, namespace `UniformEnlarge`) —
  `enlargeInput_mono`: `EnlargeInput` is monotone (larger balance constant, smaller mass constant);
  `goodSets` (the proper nonempty `A₀`), `goodSets_nonempty` (uses `Fintype.card α = n` via
  `P.piTop`), `mem_goodSets`.  These are what the hoisting of the two branch constants needs.
  Build green at 8761 jobs, axiom-clean.
* Swarm **`smvxk0e5g`** on the **uniform `EnlargeInput` provider**
  (`forall C₀ ≥ 1, ∃ C₁ c₁ > 0, ∀ γ A₀ (balanced, dominated), EnlargeInput P γ A₀ C₁ c₁`), with the
  route: `K A₀` from `exists_exit_uniform`, `Kstar := goodSets.sup K`, the pair
  `(C₀(1 + 2n·nKstar), ((Kstar n C₀)^n)⁻¹)`, the two branch constants exposed as separate lemmas,
  then `enlargeInput_mono`.  This is the last link before Lemma 5 → Lemma 6 → `CoverData` → the
  shrinking → `HrayAssembly.hray_of_shrink`.
* Swarm **`smvxk0kc6`** on **`hinj`** (`hinj_of_tower`), with the route: equal length vectors +
  `det Q = 1` give equal level-`k` cell masses; equal floor masses from `T`-invariance
  (`Tower.measure_image_iterate`); the level-`k` floors as a partition with mesh `≤ λ^{(k)}_* → 0`
  (`MeshShrink.ae_tendsto_levelLength`); then `LengthInjective.measure_eq_of_floors`.
* With `HrayAssembly.hray_of_shrink` landed, the main theorem is
  `Assembly.masurVeech_of_components P hray hinj` with `hray` = the shrinking (needs
  `smvxk0e5g`) and `hinj` = `smvxk0kc6`.  Nothing else is open.

### Addendum 26: **Lemma 5 and Lemma 6 are unconditional** (uniform `EnlargeInput` landed)

* **`MasurVeech/MasurVeech/UniformProvider.lean`** (swarm `smvxk0e5g` m1, namespace `UniformEnlarge`,
  accepted) — the uniform provider **and the whole balanced-cover layer with no hypotheses**:
  * `enlargeInput_of_exitBound`, `enlargeInput_nil_explicit`, `qnn_nil`, `qnn_singleton`,
    `qnn_singleton_le_two`;
  * `goodK`, **`Kstar`** (`:= max 2 (goodSets.sup goodK)`), `one_le_Kstar`, `two_le_Kstar`,
    `goodK_le_Kstar`, `exists_uniformExit_le_Kstar`;
  * `uniformC`/`uniformc`, `one_le_uniformC`, `pos_uniformc`, `nil_C_le_uniformC`,
    `uniformc_le_half`;
  * `enlargeInput_both_uniform`, `enlargeInput_nil_uniform`, `enlargeInput_of_oneStep`;
  * **`exists_enlargeInput_uniform`**: `∀ C₀ ≥ 1, ∃ C₁ c₁ > 0, ∀ γ A₀ (nonempty, proper, balanced,
    dominated), EnlargeInput P γ A₀ C₁ c₁`;
  * **`lemma5ShapeUniform_unconditional`**: `PacketP6bis.Lemma5ShapeUniform P` **unconditionally**
    (only `P.Admissible`, `2 ≤ n`);
  * **`exists_balanced_cover_uniform_of_enlarge_uniform`**: **Lemma 6** with a single `C` for all
    nodes, unconditionally.
* **My `hInput` was wrong and the member proved it so.**  The version in `Lemma5Bridge.lean` carries
  `A₀.sup (fun a => colsumNN (Path.Q P γ) b)` — a *constant* family, hence vacuous; taken literally it
  asks for `EnlargeInput` for **all** `γ, A₀` with one fixed pair of constants, which is unattainable
  because the balance constant the provider returns grows with the balance constant of the
  hypothesis.  Machine-checked as `hInput_forces_unbalanced` / `exists_balance_constant`.  The
  correctly-shaped bridge is `lemma5ShapeUniform_of_enlarge_uniform` (with the proper sup), and
  `lemma5ShapeUniform_of_enlarge` in `Lemma5Bridge.lean` must **not** be used.
* Remaining for the shrinking: `CoverData` = Lemma 6's family (now unconditional) **plus the length
  bound** `f (vertex P γ)` on its members — and `exists_exit_uniform`'s `W` (vertex-dependent) is the
  input for that.  Then `CylTreeReal.exists_cylTree_of_cover` →
  `NestedCylinder.CylTree.nested_cylinder_tendsto_of_bounded` → `HrayAssembly.hray_of_shrink`.

### Addendum 27: how the `nil` branch of the uniform provider really works, and `CoverData` delegated

* The fuller report of `smvxk0e5g` (already accepted and landed) records a correction to *my* plan for
  the hoisting: the not-both (`nil`) branch's constants are **not** dominated by the both-branch pair
  — `C₀(1 + 2n(1+C₀))` exceeds `C₀(1 + 2n·n·Kstar)` once `C₀ > n·Kstar`.  The member re-derived that
  branch from the `qnn`-based one-step exit word, and `Kstar` carries an extra `max 2` so that the
  numeric constants `2` and `((1+C₀)^n)⁻¹` are dominated.  So the hoisting is *not* a pure
  monotonicity argument: the `nil` branch had to be redone with the right constants.
* Swarm **`smvxklykf`** on **`RealCyl.CoverData`** — Lemma 6's family *with the length bound*, the last
  input of the shrinking.  The reason it should be provable: `PacketP6bis.exists_balanced_cover_aux`
  iterates Lemma 5 at most `n − 1` times, and each exit word is `W (vertex P γ)` with `W` from
  `exists_exit_uniform`, so `maxW := univ.sup (fun V => (W V).length)` is a constant and every member
  has length `≤ γ.length + k·(1 + maxW)`, `k ≤ n`.  And even a *vertex*-dependent `f` is enough,
  because `CombData α n` is a `Fintype` and then `L := univ.sup f` is still finite — so
  `CylTreeReal.exists_cylTree_of_cover`'s `hLen` is available in either form.

### Addendum 28: the main theorem is down to **two a.e. inputs** (`Inj2`)

* **`MasurVeech/MasurVeech/Inj2.lean`** (swarm `smvxk0kc6` m1, namespace `InjTower`) — `hinj`
  closed modulo one *geometric* statement:
  * **`cellAt_mass_eq`**: equal `lambdaOf` ⟹ equal masses on all level-`γ` cells, **with no extra
    hypothesis** — `det Q = 1` makes `Q` injective as a real matrix (`injective_qApply_Q`), and
    `Q⁻¹ ≥ 0` is *not* used.  This is what keeps injectivity independent of positivity/minimality;
  * `floor_mass_eq` (equal floor masses from `T`-invariance), `TowerPartitions`,
    `hinj_of_tower_of_floors`, `ae_exists_iterOK_path`, `mesh_of_Ico_lengths`, `iUnion_cellAt`,
    `disjoint_cellAt`, `base_mass_eq`, `measurableSet_cellAt`;
  * `hinj_of_tower_of_tiling`: `hinj` from the concrete `TowerTiling`;
  * **`masurVeech_of_shrink_and_floors`**: the main conclusion from exactly two a.e. inputs —
    the cylinder shrink (`HrayAssembly.hray_of_shrink`) and `FloorPartitionData`;
  * `floorPartitionData_of_tiling`: `TowerTiling ⟹ FloorPartitionData`.
* **`TowerTiling P lam γ`** is the one open statement (no measure in it): the floors
  `T^[j] '' cellAt (γ k) lam b` for `j < ∑_a Q(γ k)_{ab}` are half-open intervals, ⊆ `[0,1)`,
  pairwise disjoint, covering `[0,1)`, and level-`k+1` floors refine level-`k` ones.  Member evidence:
  exact rational check, 80 random trials (2–6 letters), 0 failures, ≤ 14 levels; `k = 1` essentially
  landed.  The member continues on it (first rejection), with the split spelled out (interval/length
  bookkeeping from `lamAfter`'s recursion; disjoint/cover from `iUnion_cellAt`/`disjoint_cellAt`;
  refinement from the tower-of-towers nesting).
* **Implication for the campaign**: `Main.lean` is now
  `masurVeech_of_shrink_and_floors P hP hn hshrink hfloor`, i.e. **the shrink** (needs
  `smvxklykf`'s `CoverData`) **and** `TowerTiling` a.e.  Nothing else is open.

### Addendum 29: **`CoverData` is REFUTED** — the bounded-length route to the shrink is dead

* **`MasurVeech/MasurVeech/CoverDataFalse.lean`** (swarm `smvxklykf` m1, namespace
  `CoverDataFalse`, accepted) — machine-checked refutation, for `P2 = CombData.mk (refl (Fin 2))
  (swap 0 1)`:
  * `not_coverData`, **`not_exists_coverData : ¬ ∃ CD : RealCyl.CoverData P2, True`**,
    `isEmpty_coverData`;
  * `false_of_vertexBound`: the *vertex-dependent* length bound of
    `CylTreeReal.exists_cylTree_of_cover` is unattainable too;
  * **the mechanism**: at `γ_k = [true]^k`, `vertex P2 γ_k = P2` and
    `colsum (Q γ_k) = (k+1, 1)`; columns are monotone along extension, so a `C`-balanced descendant
    `l` has `max ≥ k+1` while `∏_b colsum(l)_b ≥ max²/C`, hence
    `vol(Δl)/vol(Δγ_k) ≤ C/(k+1)`; at relative depth `≤ L` there are at most `(L+1)·2^L` words, so the
    family's mass falls below `C⁻¹ vol(Δγ_k)` once `k+1 > C²(L+1)2^L` (`vol_le_of_balanced`,
    `card_le_of_length`, `sum_vol_le`, `false_of_rayBound`).
  * Corrected, unconditional: `lemma6Shape_unconditional` (Lemma 6's four fields, no length bound) and
    **`exists_cylTree_unconditional`** — the concrete `CylTree` with no length bound.
* **What this kills and what it does not.**
  * *Dead*: `CoverData`, hence `CylTreeReal.exists_cylTree_of_cover` and
    `NestedCylinder.CylTree.nested_cylinder_tendsto_of_bounded` — the bounded-length form of §10.5 — are
    **unusable for this application**.  The §10.5 route to the shrink does not exist.
  * *Not dead*: the source's Lemma 6.  With *unbounded* depth a family may consist of many members
    each of tiny mass, so the sum can still reach `C⁻¹`; that is why `lemma6Shape_unconditional`
    survives.  The error was mine: I strengthened (H2) by bounded length.
  * *The shrink now needs* `hsurv` for the **concrete** tree
    (`nested_cylinder_tendsto`'s `∀ᵐ x, ∀ k, Tl x k ≠ none`), via conditional Borel–Cantelli.  The
    dyadic counterexample (`NestedCylinderCounterexample`) shows (H1)+(H2) alone do not give it, but
    the concrete tree has unbounded-depth families, so it is a genuinely different situation.
* Consequence for the campaign: `Main.lean` = `masurVeech_of_shrink_and_floors` with
  (a) `hfloor` ← `TowerTiling` (running, `smvxk0kc6`), and (b) `hshrink` ← **`hsurv` for the concrete
  tree** (new packet).  Everything else is landed.

### Addendum 30: the shrink is now the campaign's open core — new packet, with both dead routes named

* Swarm **`smvxlhz6y`** on the **a.e. shrinking** `diam (simplexCyl P (pathWord P x k)) → 0`, with the
  two dead routes stated up front so they are not repeated:
  (a) `hsurv` is not implied by (H1)+(H2) (`NestedCylinderCounterexample.not_hsurv`) and Lévy gives
  only the weaker `∀ n₀, μ (never-hit after n₀) = 0`;
  (b) a bounded-length family is *impossible* (`CoverDataFalse.not_exists_coverData`,
  `false_of_vertexBound`), so `nested_cylinder_tendsto_of_bounded` and
  `CylTreeReal.exists_cylTree_of_cover` are not applicable.
* The packet's first task is to **decide whether the shrink is true** for the concrete tree — a
  machine-checked counterexample would be a finding about the source (the blueprint's §10.5 replaced
  the source's own "last paragraph of §4.4", and every repair attempted so far has failed), not a
  failure of the packet.
* The suggested route is the *concrete* one, using the unconditional
  `MeshShrink.ae_tendsto_levelLength` (renormalised total length `λ^{(k)}_* → 0` along any path)
  together with the cone description `simplexCyl P (w k) = {x ∈ simplexOn | x = Q(w k) y, y > 0}`:
  a point of `⋂ k, Δ̄(w k)` is `Q(w k) y_k` with `y_k ≥ 0` and `∑_b colsum_b(Q(w k)) (y_k)_b = 1`,
  while `λ = Q(w k) λ^{(k)}` with `∑_β λ^{(k)}_β = λ^{(k)}_*` in *un-normalised* coordinates.  The
  question is whether `λ^{(k)}_* → 0` forces the intersection to a point; the normalisation
  bookkeeping is where the difficulty sits and the member is asked to report exactly what follows.
* Everything else in the campaign is landed: `Main.lean` = `masurVeech_of_shrink_and_floors` with
  `hfloor` ← `TowerTiling` (running, `smvxk0kc6`) and `hshrink` ← this packet.

### Addendum 31: `TowerTiling` packet exhausted; its base case landed; restarted

* `smvxk0kc6` ended **exhausted** (the second rejection killed the direction), without an accepted
  solution — but it left a compiling, 578-line `Tw.lean`, now landed as
  **`MasurVeech/MasurVeech/Tw.lean`** (namespace `InjTower`):
  * **the level-one tower in `CombData` letters for both step types**:
    `Ico 0 (∑ b, L b) = ⋃ b ⋃ j : Fin (hgt1 P e b), T^[j] '' cellAt P [e] L b`
    (`level_tower_false`, `level_tower_true`, `iUnion_floor_true`, `tower_decomp_true`);
  * `hgt1_eq` / `returnB_eq_hgt1` / `returnBT_eq_hgt1`: the heights are the column sums of `rvMat`,
    i.e. the `Q`-recursion — the height-convention check, matching;
  * `firstReturn_false`, `firstReturn_true` (the first return of `T` on each level-one cell is the
    renormalised exchange), `names_false_sub/image`, `names_true_sub/scd/image` (where the level-one
    cells sit and where the top floor goes, both types), `level_one_mass`
    (`∑_b h · λ_after = ∑_b L`), and
  * **`hgt_succ`**: `h (k+1) b = h k b + (if b = last (!e) then h k (last e) else 0)` along the greedy
    path, from `Path.Q_append` and `rvMat`'s equation — the `Q`-recursion of the heights.
  Build green at 8765 jobs, axiom-clean.
* The member's own list of what remains for `TowerTiling`: the combinatorial index identity (assembling
  `hgt_succ` with `names_*`), the composite construction (level-`k` tower composed with the level-one
  tower at level `k`, via `firstReturn_*`), and a strengthened induction hypothesis.
* Fresh swarm **`smvxluwda`** on `TowerTiling`, seeded on `Tw.lean`, `Inj2.lean` and the previous
  member's `ROUTE.md`/`report.md`, with the instruction that the height convention is closed and must
  not be re-opened.

### Addendum 32: the shrink is EXACTLY a.e. coalescence of the RV cocycle columns — and no mass statement can give it

* **`MasurVeech/MasurVeech/ColDiam.lean`** (swarm `smvxlhz6y` m1, namespaces `ColShrink`/`ColConc`)
  — exact characterisation, both directions:
  * `diam_le_of_cols_close`: `diam Δ(γ) ≤ 2 · max |ŵ_{b,a} − ŵ_{b',a}|` (every point of `Δ(γ)` is a
    convex combination of the vertices `ŵ_b = Q e_b / c_b`);
  * `spread_le_diam`: the reverse, via the points `(1−δ)ŵ_b + δ·Qu` and `δ → 0`;
  * **`tendsto_diam_iff_cols`**: `diam Δ(γ_k) → 0` ⟺ the normalised columns of `Q(γ_k)` coalesce.
* **`MasurVeech/MasurVeech/Obstruction.lean`** — **no volume/mass statement can prove the shrink.**
  For `P3 = (finRotate 3, id)` (admissible) and `γ = [true]^M`:
  `volume_small_diam_large : vol Δ(γ) = vol Δ/(M+1)` **and** `2/3 ≤ diam Δ(γ)`;
  `volume_zero_diam_not`: arbitrarily small volume with diam `≥ 2/3`.  So Lemma 1, Lemma 6's mass half
  and `MeshShrink.ae_tendsto_levelLength` are all *compatible with maximal diameter*.
* **`MasurVeech/MasurVeech/MassShrink.lean`** — the strongest a.e. statement that mass gives:
  `ae_eventually_volume_le`: for a.e. `λ`, every `M ≥ 1`, `vol Δ(pathWord P λ k) ≤ vol Δ / M`
  eventually.  Unconditional, and provably insufficient.
* Consequences: (i) the §10.5 route to the shrink is dead three times over (invalid Claim 1; `hsurv`
  not derivable and bounded length impossible; and now mass cannot give diameter); (ii) the shrink is
  *equivalent* to a.e. coalescence of the RV cocycle's normalised columns, i.e. to the classical
  expansion content — the campaign's last step is therefore not a bookkeeping gap but the same circle
  it is trying to break.  Also recorded: the shape bound `diam ≤ C / min_b c_b` is **false** for `n = 4`
  (all words to length 14).
* Numerics: no counterexample to the shrink for `n = 3, 4`; slow convergence only along long runs of
  one type, which is a null set of parameters — so the statement is very likely true and the difficulty
  is entirely in the argument.  The member is continuing (one more run) on the a.e. form of (1) and on
  whether `P3`'s `[true]^M` family is the borderline case.

### Addendum 33: the campaign's single missing input, isolated exactly

* **`ColDiam.ae_tendsto_diam_iff_cols`** (landed): the a.e. form of the characterisation,
  ```
  (∀ᵐ λ, Tendsto (fun k => diam (simplexCyl P (pathWord P λ k))) → 0)
    ↔ ∀ᵐ λ, ∀ ε > 0, ∀ᶠ k, ∀ b b' a, |ŵ^{(k)}_{b,a} − ŵ^{(k)}_{b',a}| ≤ ε
  ```
  with `ŵ^{(k)}_b = Q(pathWord P λ k) e_b / c_b`.  So `HrayAssembly.hray_of_shrink`'s hypothesis *is*
  a.e. coalescence of the cocycle's normalised columns, and if that is ever proved the main theorem
  follows by one application (through `InjTower.masurVeech_of_shrink_and_floors` and the landed
  `TowerTiling ⟹ FloorPartitionData`).
* **`Obstruction.lt_coord_of_mem_replicate`** and the transience lemmas: for `P3 = (finRotate 3, id)`
  the `[true]^M` ray gives `x ∈ Δ([true]^M) → M·x₂ < x₁`, so the closed cylinder is the slab
  `{x₁ ≥ M x₂}`, the intersection over `M` is **empty** (`not_forall_mem_replicate`,
  `ae_not_forall_mem_replicate`), and for a given `x` only `⌈x₁/x₂⌉ + 1` values of `M` occur
  (`exists_forall_not_mem_replicate`).  **So the obstruction is transient: coalescence fails at every
  finite depth of the ray, yet no parameter sees it at unbounded depth.**  That is exactly why every
  mass-based argument must fail while the a.e. statement can still hold, and it rules out any proof
  that works level-by-level against a fixed ray.
* The swarm ended **exhausted** after the second rejection; the direction is dead.  The remaining
  question is quantitative (does some path-growing quantity bound `max_{b,b'} |ŵ_b − ŵ_{b'}|`? — noting
  that `diam ≤ C/min_b c_b` is **false** for `n = 4`, so the shape must also use balance or the
  type-change count).

### Addendum 34: **`TowerTiling` proved — `hinj` is unconditional, and the main theorem is one statement away**

* **`MasurVeech/MasurVeech/TowerTiling.lean`** (swarm `smvxluwda` m1, namespace `InjTower`,
  1334 lines, accepted) — **`TowerTiling` fully proved**, all seven conjuncts verbatim:
  * `FR_all`: the first-return identity `T^[HH k b] = KK k` on each level-`k` cell, induction on `k`
    from `Tw.firstReturn_*`, `Tw.hgt1_eq`, `Tw.hgt_succ`, `Tw.names_*`;
  * `SH_all`: `T^[j]` is a translation on each level-`k` cell for `j ≤ HH k b` — which yields
    `floor_Ico` (the `Ico u v` / length conjunct);
  * `TL`: `∑ h λ = 1`; `LVL1` = `Tw.level_tower_*` at the vertex; `CV_all` covering via
    `S k ⊆ S (k+1)`; `href_all` refinement by index case analysis; `floors_disjoint` via
    `measure_union_add_inter` + `measure_biUnion_finset_le`;
  * `towerTiling`, `towerTiling_pfx`, `towerTiling_pathWord`, `ae_towerTiling`;
  * **`hinj_of_tower`** — **`hinj` UNCONDITIONAL**;
  * **`masurVeech_of_shrink`** — the main conclusion from the a.e. cylinder shrink alone.
* **`MasurVeech/MasurVeech/Final.lean`** (mine) — `masurVeech_ae_unique_invariant_of_shrink`: the main
  theorem from the single hypothesis `∀ᵐ lam, Tendsto (fun k => diam (simplexCyl P (pathWord P lam k)))
  → 0`.  (`Main.lean` keeps the `sorry` on the full statement, since `Final` has to import
  `TowerTiling`, which transitively imports `Main`; the reduction is stated as its own theorem.)
  Build green at 8770 jobs, axiom-clean.
* **Campaign status**: everything is landed and axiom-clean except one statement —
  a.e. **coalescence of the normalised columns of the RV cocycle**, isolated in both directions by
  `ColShrink.ae_tendsto_diam_iff_cols`, with `Obstruction.lean` showing that no volume/mass estimate
  can give it and that the obstruction is transient along one-type rays.

### Addendum 35: Appendix A obtained; the (1) problem restated in its language; swarm launched

* **Only `main.tex` was attached**, which is the top-level file and `\input`s `teich`,
  `easyyoccoz`, `spectral`.  I fetched the arXiv source (`arxiv.org/e-print/math/0511614`) and
  confirmed it matches the attached file (same `\input` list, journal-style vs amsart preamble), so
  the appendix is the arXiv's `easyyoccoz.tex` — "A simple distortion estimate".  Extracted to
  `.scratch/avg/`, with a digest of the toolbox in `.scratch/avg/APPENDIX_A.md`.
* **The toolbox** (transcribed): the cocycle `B_γ ∈ SL(𝒜,ℤ)` and `Δ_γ = B_γ*ℝ^𝒜_+ × {π}` (so the
  cylinder is the cone — the project's `simplexCyl`); complete / k-complete / positive paths with the
  two MMY lemmas (Δ^∞-points have complete prefixes for all large n; `k ≥ 2#𝒜−3` k-complete ⟹
  positive); the finite measure family `ν_q` with `ν_q(B_γ*A) = ν_{B_γ q}(A)` and the exact mass
  formula `Leb(Λ_{q,γ})/Leb(Λ_q) = 𝔫(q)/𝔫(B_γ q)` (this *is* the project's Lemma 1, with `q` the
  column-sum vector); the path measure `P_q` with the chain rule `P_q(Γ|γ) = P_{B_γ q}(Γ^γ|π)` and the
  disjoint-family inequality; **Kerckhoff's lemma** `P_q(γ ∈ Γ_α(π), (B_γ q)_α > T q_α|π) < 1/T`; and
  Appendix A's theorem: a *uniform-in-q* definite `P_q`-probability of reaching a `C`-balanced vector.
* **(1) restated in that language**: for every finite `γ₀` and every `N`, `λ ∈ Δ_{γ(n)γ₀}` for
  infinitely many `n`, for a.e. `λ`.
* **My own attempt failed**, on the same obstruction as before: Appendix A gives a definite chance of
  *balance* from any state with constants uniform in `q`, and at a balanced node the chance of
  following `γ₀` within `|γ₀|` steps is `≥ (nCK)^{-n}` (a Lemma-1 computation), but the events are
  only decidable an unbounded number of levels ahead of the filtration where the bound holds, and the
  project has proved no bounded-length family can carry a definite mass fraction.  So the adaptivity
  question is the crux, and it is now a question about a *uniform-in-q* estimate rather than about a
  node-dependent one — which may be the way around it.
* Swarm **`smvxnf2ro`** (3 members) launched on a **self-contained mathematical proof of (1)** with
  four registered directions: (d1) definite-probability + chain rule and the adaptivity question;
  (d2) positivity + Hilbert-metric contraction of the nested cones; (d3) completeness ⟹ richness;
  (d4) refute (1) or find its sharp form.  Ergodicity of the RV induction is explicitly excluded.

### Addendum 36: `smvxnf2ro` m3 accepted — but (1) is *not* the tree's missing input; new swarm on (S)

* **m3's `PROOF.md` accepted** (swarm `smvxnf2ro`, direction d2, 531 lines, paper proof).  It proves
  statement (1) as posed: for every finite Rauzy path `γ₀` and every `N`, a.e. `λ` follows `γ₀` at
  some time `> N`.  I re-derived the whole chain: Theorem A.1 quoted verbatim from
  `.scratch/avg/easyyoccoz.tex` (`simpleyoccoz`, uniform in `q` *and* `π`, with the
  `min{𝔪(B_γ q), 𝔐(q)}`); Lemmas 1.2/1.3/2.1 (density of `ν_q`, invariance, mass formula, conditional
  measure `= P_{q_w}`); Lemma 4.1 (balanced node ⟹ follow `γ₀` within `K` w.p. `≥ δ₂`, via Lemma 3.1);
  Lemma 5.1 (prefix-freeness of the minimal-path family from Theorem A.1, so the mass bound is a sum);
  Step 1 (`E_{wγ}` disjoint over `Γ_min(w)`, times `≥ |w|`); and **Lemma 6.1** (Lévy: if every atom of
  every level `n ≥ N` carries a `δ`-fraction in a set disjoint from `Z`, then `μ Z = 0`).  Lemma 6.1
  is the new device: the `F_w` need not be measurable in `w`, which is exactly what defeats the
  adaptivity obstruction.  Two non-fatal defects flagged to the member: the §1.2 convention slip
  (`B e_α = e_α+e_β` with `α` the *winner* contradicts `P_q = q_α/(q_α+q_β)`; it must be
  `B e_loser = e_loser + e_winner`, i.e. transpose), and §9(c) calling
  `PacketP10.volume_append_mul` a machine check of Lemma 2.1 (it is the multiplicative mass formula).
  m1/m2 stopped with the swarm (`finish`), since their directions targeted the same statement.
* **(1) is not what the tree is missing.**  `Final.masurVeech_ae_unique_invariant_of_shrink` and
  `Main.lean`'s single `sorry` (`:66`) need the a.e. **diameter shrink**
  `∀ᵐ λ, Tendsto (fun k => diam (simplexCyl P (pathWord P λ k))) atTop (𝓝 0)` — call it **(S)** —
  which is strictly stronger than (1): (1) is conservativity of the RV induction, (S) is a statement
  about the *cones*.  Do not describe the campaign as closed on (1).
* **Numerics on (S)** (my check, exact integer `Q`, 60-digit state, project conventions): for
  **rational** `λ` the greedy path is eventually periodic and `diam` does **not** tend to 0 — checked
  for every irreducible `d = 3` class, with the normalised-column spread converging to a positive
  limit (the whole `d = 3` class of `P3` has 3 vertices, not 1, so the "inert letter" worry is real
  but does *not* refute (S): all letters win somewhere).  For **irrational** `λ` the spread decays,
  roughly like `1/‖Q‖` (≈ `1e-4` at `k = 250` in all classes).  So (S) is genuinely an a.e.
  statement and any argument must use genericity somewhere.
* **New swarm `smvxo5ewn`** (6 members, 240 min, `member_steps` 260) on **(S)**, pointing at
  `.ultramath/smvxnf2ro/m3/PROOF.md` for the four transferable lemmas.  The strategy sketched for
  d1 (and to be re-derived, not assumed): *positivity + Hilbert contraction + Lévy*.
  Flesh of it, as I checked it: (a) thinness of a node does **not** transfer to descendants in the
  Euclidean simplex metric, but it does through the Hilbert metric on `ℝ^𝒜_+` —
  `x ↦ Ax` is Hilbert-nonexpansive for `A ⪰ 0`, and Hilbert-small ⟹ Euclidean-small after
  normalisation (`‖x̂ - ŷ‖_∞ ≤ e^{d_H(x,y)} - 1`); (b) `m` entrywise-positive blocks, with *arbitrary*
  nonneg matrices in between, give cone diameter `≤ κ^{m-1}·2 log M` with `κ = tanh(Δ/4)`,
  `Δ ≤ 2 log M` (Birkhoff contraction) — this is the compounding step that a bare entry-ratio bound
  fails to give; (c) at a `C`-balanced node every fixed word of bounded length has
  `P_q`-probability `≥ C^{-d}/𝔫(B_γ(π)1)`, uniformly in the vertex (Lemma 3.1 + mass formula), so a
  *fixed* positive block is followed with definite probability; (d) balance at unbounded depth is free
  (Lemma 5.1); (e) Lévy with `Z_ε = {λ : diam ≥ ε for all k}` (legitimate since `diam` is antitone
  along nested cylinders).  Still needed on the combinatorial side: for **each vertex** `π ∈ ℛ` a
  word `v_π` of bounded length with `B_{v_π}(π)` entrywise positive (strong connectivity of `ℛ` +
  every letter wins somewhere).
* **State of the tree**: `lake build` green at 8770 jobs; the only real `sorry` is
  `masurVeech_ae_unique_invariant` (in `MainTheorem.lean` now); everything else cited above is
  axiom-clean.  `blueprint.md` §14 and the READMEs are still owed.

### Addendum 37: an elementary replacement for Birkhoff in the (S) strategy — checked numerically

The `d1` sketch in Addendum 36 used the Hilbert metric.  There is a purely elementary contraction with an
explicit constant, on the "$r-s$" form of the spread, which is what the formalisation should target
(no Hilbert metric, no `tanh`):

* **Setting.** `C ∈ ℝ^{n×n}` with `m ≤ C i j ≤ M` (all `i j`, `0 < m ≤ M`); `u, v > 0`;
  `s = min_i u_i/v_i`, `r = max_i u_i/v_i`; `s' = min_i (Cu)_i/(Cv)_i`,
  `r' = max_i (Cu)_i/(Cv)_i`.  Then
  * (monotonicity, needs only `C ⪰ 0`)  `s ≤ s' ≤ r' ≤ r`;
  * (contraction)  `r' - s' ≤ κ (r - s)`  with  `κ = 1 - m²/(n M²)`;
  * (scale-free form)  `(r'/s') - 1 ≤ κ ((r/s) - 1)`, because `s' ≥ s`;
  * (normalised spread)  `‖u/Σu - v/Σv‖_∞ ≤ (r/s) - 1`.
* **Proof of the contraction** (elementary, `5` lines): `(Cu)_i/(Cv)_i` is the `p^{(i)}`-average of
  `θ_j = u_j/v_j` with `p^{(i)}_j = C_{ij}v_j / Σ_j C_{ij}v_j`; so `r'-s' = r(θ)`-average minus
  `s(θ)`-average, and for the argmax `i` and argmin `j`,
  `r'-s' = Σ_{k,l} p^{(i)}_k p^{(j)}_l (θ_k - θ_l) ≤ (r-s)·Pr[θ_K > θ_L]`.  And
  `Pr[θ_K > θ_L] ≤ Σ_k p^{(i)}_k (1 - p^{(j)}_k) = 1 - Σ_k p^{(i)}_k p^{(j)}_k`, while
  `p^{(i)}_k p^{(j)}_k ≥ m²v_k²/(M Σv)²`, so Cauchy–Schwarz gives `Σ_k p^{(i)}_k p^{(j)}_k ≥ m²/(nM²)`.
  Multiply.  (A sharper `½(1 - m²/(nM²))` is FALSE — `p ⊗ q` is not symmetric; cf. an earlier draft
  of this note.)
* **Consequence for (S).** Between positive blocks only `C ⪰ 0` occurs, and then `r-` and `s-` are
  monotone, so `((r/s) - 1)` never increases; each entrywise-positive block multiplies it by `≤ κ < 1`.
  Since a positive block has *bounded* integer entries (`1 ≤ C i j ≤ M`), `κ` is uniform over the
  whole Rauzy class, and since the diameter is monotone along nested cylinders, "infinitely often thin"
  is "eventually thin".  So the Lévy scheme of Addendum 36 needs only: (i) this contraction,
  (ii) the normalised-spread bound, (iii) a bounded positive block at every vertex, (iv) Lemmas
  3.1/5.1/6.1 of `.ultramath/smvxnf2ro/m3/PROOF.md`.  All four are elementary; (i)–(iii) are what I
  will formalise next, (iv) is to be transcribed from the paper proof.
* Checked numerically (exact rational arithmetic, `n = 2..8`, `M` up to `1000`): the contraction
  inequality holds with the stated `κ` in every trial, and the normalised-spread bound holds too.

### Addendum 38: the three-statement design, landed as a module

The person asked whether the tree is already separated cleanly into (1), (2), (3), and to refactor for
that design.  Answer: it was **not** — (2) existed only inside `Cor4`, (1) nowhere in Lean, and (3) only
as an anonymous hypothesis of `Final`.  It is now, in **`MasurVeech/MasurVeech/Design.lean`**:

* **(1)** `MVDesign.Statement1 P` — for every finite word `γ₀` and every `k`, a.e. `λ` follows `γ₀` at
  some time `≥ k` (richness / recurrence of the renormalisation).  Paper proof only (m3).
* **(2)** `MVDesign.statement2` — Cor. 4 (`CombData.exists_uniform_bound'`), **plus the new**
  `MVDesign.exists_word_pos_everywhere` : there are `V : List Bool` and `M ≥ 1` with, at **every**
  admissible vertex `Q`, `1 ≤ Q(V)(Q) a b ≤ M`.  Proved from Cor. 4 by a greedy induction over the
  finite type of combinatorial data, axiom-clean, first try.
* **(3)** `MVDesign.Statement3 P` — a.e. shrink of the path cylinders; `statement3_iff_cols` (the
  `ColDiam` characterisation), and `main_of_statement3` (the landed `Final` reduction).
* **Bridge** `MVDesign.Bridge P := Statement1 P → Statement3 P`, and
  `MVDesign.main_of_statement1 : Bridge P → Statement1 P → main theorem`.

**Why (2) had to be strengthened to (2⁺) — this is a real design point, not bookkeeping.**  (1) is a
statement about *letters*: at an occurrence of a fixed word the current *vertex* is uncontrolled.  A
word positive at one vertex therefore does not give a positive block at an occurrence.  A word positive
at *every* vertex does, and that is exactly what `exists_word_pos_everywhere` provides.  (Note also
that `Cor4.exists_pos_word` positivity *persists* under appending, `Q_le_append`, which is what makes
the greedy induction work.)

**Content of the bridge** (paper-checked, two Addenda ago, formalisation pending): each occurrence of
`V` is a positive block with entries in `[1,M]`; a positive block contracts the spread
`r - s` of `u_i/v_i` by `κ = 1 - m²/(nM²)` (weighted average + Cauchy–Schwarz); nonnegative matrices
are nonexpansive in the same quantity, so the spread after the `j`-th block is `≤ κ^{j-1} log(M²)`;
and `ColDiam`'s two-sided `diam ↔ spread` dictionary turns that into `Metric.diam → 0`.
So (1) + (2⁺) ⟹ (3), and with `main_of_statement1` the whole campaign becomes: **(1) plus the
contraction lemma**.

**Tree state after the refactor**: `lake build` green at **8771 jobs**; `Design` added to the umbrella
and to `Check.lean`; all five new axiom reports are `[propext, Classical.choice, Quot.sound]`.  The one
real `sorry` is still `Main.lean:66` (`masurVeech_ae_unique_invariant`), now accounted for by the
Design module as `Bridge` + `(1)`.

### Addendum 39: correction — (1) is a statement about *paths*, vertices included

The person corrected Addendum 38 and my `Statement1`: "a finite path in the Rauzy graph" is the sequence
of vertices **and** the letters of the path; the vertex is part of the data.  I had formalised (1) as a
letters-only statement (`λ ∈ simplexCyl P (w ++ γ₀)`), which is strictly weaker — knowing the letters of
`γ₀` occur says nothing about the vertex they start at.

* **`Statement1` corrected** (`MasurVeech/MasurVeech/Design.lean`): for every vertex `π₀` of the
  diagram of `P` (`∃ u, vertex P u = π₀`), every type sequence `γ₀` and every `k`, a.e. `λ` has
  `∃ m ≥ k, ∃ w, w.length = m ∧ vertex P w = π₀ ∧ λ ∈ simplexCyl P (w ++ γ₀)` — i.e. the greedy path
  returns to that vertex and then follows the word.  New lemma `statement1.letters` : (1) implies the
  letters-only form, so the old reading is a proper weakening.
* **Consequence for the design (the part I had backwards)**: with (1) pinning the vertex, *plain Cor. 4
  suffices* for the bridge — the word only has to be positive **at the vertex where it is delivered**.
  `exists_word_pos_everywhere` (a single word positive at every vertex) is a proved convenience, not a
  requirement; the bridge is `(1) + (2) ⟹ (3)` in the two statements' original forms, as the person's
  design has it.  The header of `Design.lean` is corrected accordingly.
* **m3's paper proof already gives the pinned form, up to bookkeeping**: the single path whose cylinder
  its Lemma 4.1 measures is `γ₂(π_w) γ₀`, a path *from* the node's vertex `π_w` *to* `π₀`, so the
  estimate it proves is for the pinned event; only the event displayed in its §7 (a union over
  positions) is the larger letters-only one, and that is the thing to replace when transcribing.
* Build green at **8771 jobs**; `Check.lean` reports `statement1.letters`, `statement2`,
  `exists_word_pos_everywhere`, `statement3_iff_cols`, `main_of_statement3`, `main_of_statement1`, all
  `[propext, Classical.choice, Quot.sound]`.

### Addendum 40: (S) is PROVED — swarm `smvxo5ewn` m6 accepted; the campaign's mathematics is complete

Member m6 of swarm `smvxo5ewn` (direction d3) submitted `.ultramath/smvxo5ewn/m6/PROOF.md`, a complete
paper proof of the a.e. shrinking of the path cylinders — the one missing input of the campaign.  I
refereed it and **accepted**; the other five members were stopped.

**The proof.** With `h_b = colsum_b Q(w)` (the heights), `p_b = Q e_b/h_b` (the normalised columns) and
`S(Q) = max_{b,b',a} |p_b(a) - p_{b'}(a)|` (so `diam Δ_w ≤ 2 S(Q(w))` by the landed
`ColShrink.diam_le_of_cols_close`, and `σ(Δ_w) = 1/𝔫(h)` by `volume_simplexCyl`):

* **Lemma 3.1 (the new ingredient).** If the heights at a node are `C`-balanced and `R = Q_π(u)` is
  entrywise **positive** with entries in `[1,M]`, then `S(QR) ≤ (1 − 1/(dMC))·S(Q)` and
  `σ(Δ_{wu})/σ(Δ_w) ≥ (dMC)^{−d}`; and `S(QR) ≤ S(Q)` for *any* nonneg `R`.
  Proof of the contraction: each `p'_b` is the convex combination `Σ_a θ_{ba}p_a` with
  `θ_{ba} = R_{ab}h_a/h'_b ≥ 1/(dMC)`, so a difference of two of them is `β(u − v)` with
  `u, v ∈ conv{p_a}` and `β = Σ_{a∈S₊}(θ_{ba} − θ_{b'a}) ≤ 1 − |S₊|·1/(dMC) ≤ 1 − 1/(dMC)`.
  *(m6's printed bound `β ≤ 1 − θ_{b'a₀}` is garbled; the clean statement is `|S₊|·θ`, same result.)*
  This is a **relative** contraction, which is what makes it compound — my own earlier version gave
  only a fixed bound per block and did not iterate.
* **The round.** At *every* node, m3's Lemma 5.1 gives balanced descendants of mass `≥ σ(Δ_w)/C`;
  appending the positive word `u(π)` of Lemma 2.2 at each of them gives a family of relative mass
  `δ₁ = C^{−1}(dMC)^{−d}` with `S ≤ κ S(Q(w))`.  Iterating `m` times: mass `≥ δ₁^m`, spread `≤ κ^m`.
* **Lévy** (m3's Lemma 6.1) applied to `Z_ε = {λ : diam Δ_{γ_λ(k)} ≥ ε ∀k}`, which misses every member
  of the round family; `{lim ≠ 0} = ⋃_n Z_{1/n}`.
* **Combinatorial input (P.1 = MMY)**: a positive word exists at every vertex; m6 checks this
  exhaustively for `d ≤ 4` and derives it from the two MMY lemmas.  Positivity is *essential*: the
  P3 all-`true` ray has heights `(1,1,M+1)`, `S = 1` forever — the project's `Obstruction`.

**What I checked independently** (my own code, not m6's): the conventions against the Lean sources
(`rvMat = I + e_αe_βᵀ`, `Q_append`, `cs`, `volume_simplexCyl`, `diam_le_of_cols_close`); Lemma 3.1(2),
(3), (4) on 12 000 random balanced instances for `d = 2,3,4` — zero violations; monotonicity on 6000 —
zero violations; positive words at all three vertices of the class of P3 (lengths 5, 6, 5, entries ≤ 4);
end-to-end on a genuine orbit, 25 balanced nodes, the contraction always held; and the P3 all-`true` ray
reproduces `(1,1,M+1)` heights and `S = 1`, matching `Obstruction`.

**Consequence for the design.** m6's proof does **not** use (1): it runs (2) + Appendix A + MMY + Lévy
straight to (3).  So the campaign's mathematics is complete and the (1)+(2)⟹(3) bridge is no longer the
shortest path; `Design.lean`'s header records both routes (`Bridge`/`main_of_statement1` for the
(1)-shape, and `main_of_statement3` + m6 for the direct one).

**What remains is formalisation**, in this order of difficulty:

1. **m6's Lemma 3.1 + the round + the `m`-round induction** — finite-dimensional algebra plus Finset
   bookkeeping; the contraction should be ~200 lines.
2. **Lévy** — m3's Lemma 6.1; Mathlib has the upward theorem (`MeasureTheory.tendsto_ae_condExp`).
3. **m3's Lemmas 1.2, 1.3, 2.1, 5.1, 6.1** — mass formula (landed), conditioning, and Lemma 5.1 which
   rests on Appendix A.
4. **Appendix A's Theorem `simpleyoccoz`** — the a priori estimate, by induction on the alphabet; this is
   the largest single item, and it is the only place where the argument is not elementary.
5. **MMY** (complete/k-complete ⟹ positive) — combinatorial, needed for the positive word.

Tree state: `lake build` green at 8771 jobs; the single `sorry` is `Main.lean:66`; `Design.lean`'s
docstrings corrected in this pass.

### Addendum 41: the design restated as (1)+(2)+(3) ⟹ main, and the tree goes through (1)

The person's ruling, recorded: **(1) stays on the critical path** even though it is not needed for unique
ergodicity — it is wanted for other applications — and the design is
**(1)+(2)+(3) ⟹ main theorem**, not "(1)+(2) gives (3), and (3) is all we need".

`MasurVeech/MasurVeech/Design.lean` is restated accordingly:

* `Statement2` is now a `def … : Prop` (uniform in the vertex), with `statement2 : Statement2` proved
  from `CombData.exists_uniform_bound'`;
* `main_of_three (h1 : Statement1 P) (h2 : Statement2 α n) (h3 : Statement3 P) : main theorem` — the
  design's assembly, in the person's shape;
* `Bridge P := Statement1 P → Statement2 α n → Statement3 P` (the middle arrow, now taking (2)
  explicitly) and `main_of_statement1 : Bridge P → Statement1 P → Statement2 α n → main theorem`;
* `main_of_statement3 : Statement3 P → main theorem` is the landed `Final` reduction.

The two arrows, and what each costs:

| arrow | status | content |
|---|---|---|
| (1) + (2) ⟹ (3) | paper; formalisation next | richness pins the vertex ⟹ each occurrence of a positive word is a contracting block; core = m6's `Lemma 3.1(3)` (`S(QR) ≤ (1 − 1/(dMC))S(Q)`), then `S` antitone + `diam ≤ 2S` |
| (3) ⟹ main | **landed** | `Final.masurVeech_ae_unique_invariant_of_shrink` |

**Formalisation order** (recorded in the module docstring too):

1. shared base — exact mass formula (landed), Appendix A's a priori estimate (`simpleyoccoz`), the MMY
   lemmas, Lévy's upward theorem;
2. **(1)** — m3's §7 with the vertex-pinned event (its Lemma 4.1 measures `γ₂(π_w)γ₀`, so the delivered
   event already pins the vertex; only the §7 display has to be replaced);
3. the **bridge** (1)+(2) ⟹ (3) — m6's `Lemma 3.1` contraction plus the block bookkeeping;
4. (3) ⟹ main — landed.

Why (1) is the *cheapest* route to (3) as well: richness replaces the "balanced descendants" input, so
m3's Lemma 5.1 (hence Appendix A's balanced-state machinery) is needed only inside (1) and not a second
time for (3).  m6's proof — (2) + Appendix A + MMY + Lévy straight to (3) — is kept as a cross-check on
step 3, not as the route the tree takes.

Tree state: `lake build` green at **8771 jobs**; `Check.lean` reports `statement1.letters`, `statement2`,
`exists_word_pos_everywhere`, `statement3_iff_cols`, `main_of_statement3`, `main_of_statement1`,
`main_of_three`, all `[propext, Classical.choice, Quot.sound]`; the single `sorry` is still
`Main.lean:66`.

### Addendum 42: (3) is an EVERYWHERE statement — design corrected again, and the assembly now proved

The person's correction: **(3) is independent of (1) and (2)**; it *assumes* that the greedy path runs
through a positive matrix infinitely often and derives unique ergodicity, and it is an **everywhere**
statement, by Hilbert contraction.  I had been carrying (3) as the *a.e. diameter shrink*, which is a
consequence of (3) rather than (3) itself, and my contraction lemma (m6's Lemma 3.1(3)) needed
*balanced heights* — an artefact of working with the spread functional
`S(Q) = max|p_b − p_b'|` instead of the Hilbert metric.  With the Hilbert metric there is no balance
hypothesis at all: for an entrywise positive `R` with entries in `[1,M]`, Birkhoff gives
`d_H(Rx,Ry) ≤ κ_R d_H(x,y)` with `κ_R < 1` depending only on `R`, nonnegative matrices are
nonexpansive, and peeling from the *latest* positive block,
`diam_H Γ_k ≤ κ^{m(k)−1} log(M²) → 0` where `m(k)` is the number of positive blocks up to `k` (the
first one makes the diameter finite, every later one contracts).  Hilbert-small gives the simplex spread,
and `TowerGlue.ray_of_shrink_and_tower` (landed, pointwise) converts that into the ray condition.  No
measure theory, no Appendix A, no balance.

**The design in Lean now** (`MasurVeech/MasurVeech/Design.lean`, rebuilt):

* `Statement1` — vertex-pinned richness, with `∀ k` *inside* the a.e. (so the assembly needs a single
  a.e. statement).  `statement1.letters` records that the letters-only form is weaker.
* `Statement2` — Cor. 4, **proved** (`statement2`), plus `exists_word_pos_everywhere`.
* `HasPositiveBlockAt`, `HasPositiveBlocks`, `RayCondition`, and
  `Statement3 P := ∀ lam, HasPositiveBlocks P lam → RayCondition P lam` — the everywhere statement.
* `hasPositiveBlocks_ae : Statement1 P → Statement2 α n → ∀ᵐ λ, HasPositiveBlocks P λ` — **proved**;
  this is exactly where the *vertex* in (1) is used: richness returns to the base vertex `P` and then
  follows the positive word there, so (2)'s word is positive *at the vertex where it is delivered*.
* `hray_of_three : (1) → (2) → (3) → ∀ᵐ λ, RayCondition P λ` — **proved**.
* `main_of_three : (1) → (2) → (3) → main theorem` — **proved**, via
  `Assembly.masurVeech_of_components` and the unconditional `InjTower.hinj_of_tower`.  This is now a
  genuine assembly: all three statements are consumed.

The a.e. shrinking is kept, but demoted to a by-product: `ShrinkStatement`, `shrink_iff_cols`
(the `ColDiam` characterisation) and `main_of_shrink` (the `Final` reduction).

**What remains unformalised is exactly two statements**: (1) (paper, m3) and (3) (Hilbert, elementary —
Birkhoff contraction + the diameter dictionary + the block induction).  (3) is the cheaper of the two and
needs no Appendix A, so the order is: (3) first, then the shared base for (1) (Appendix A's
`simpleyoccoz`, the MMY lemmas, Lévy), then (1)'s transcription.

Build: **8771 jobs**, green; all eight `MVDesign` axiom reports are
`[propext, Classical.choice, Quot.sound]`; the single `sorry` is still `Main.lean:66`.

### Addendum 43: where to pick up (handover block — a fresh session should start here)

**Read in this order**: (a) `MasurVeech/MasurVeech/Design.lean` — its header is the design, and the
declarations in it *are* the current interface; (b) Addenda 36–42 below/above for why the design took
this shape; (c) the two paper proofs, `.ultramath/smvxnf2ro/m3/PROOF.md` (statement (1)) and
`.ultramath/smvxo5ewn/m6/PROOF.md` (the Hilbert/positive-block route to unique ergodicity).

**State.** `lake build` green at 8771 jobs; the only `sorry` is `Main.lean:66`.  In `Design.lean`:
(2) is *proved* in Lean (`statement2`, `exists_word_pos_everywhere`); the assembly
`main_of_three : (1) → (2) → (3) → main` is *proved*, as are the two steps
`hasPositiveBlocks_ae` ((1)+(2) ⟹ the hypothesis of (3) a.e.) and `hray_of_three` ((3) ⟹ the ray
condition a.e.).  (1) and (3) are paper theorems, not yet Lean.

**(3) is an everywhere statement**: positive Rauzy matrix visited at unbounded times ⟹ every invariant
probability measure carried by `[0,1)` has length vector ∝ `λ`.  Its proof is Birkhoff contraction on
the nested cones, no balance hypothesis and no measure theory, then the landed pointwise
`TowerGlue.ray_of_shrink_and_tower`.

**Next three actions, in this order.**
1. Formalise **(3)**: (i) Birkhoff contraction for an entrywise positive matrix with entries in `[1,M]`
   (`κ_R<1` depending only on `R`), nonnegative matrices nonexpansive; (ii) the peeling induction giving
   `diam_H Γ_k ≤ κ^{m(k)−1} log(M²)` where `m(k)` counts the positive blocks up to `k`; (iii) the
   dictionary Hilbert-small ⟹ simplex spread small (`‖x̂ − ŷ‖_∞ ≤ e^{d_H(x,y)} − 1` and
   `ColShrink.diam_le_of_cols_close`); (iv) feed (iii) into `TowerGlue.ray_of_shrink_and_tower` with the
   tower formula (`tower_formula_level_pathQ_any`).  No Appendix A needed.
2. Shared base for **(1)**: Appendix A's `simpleyoccoz` (the a priori estimate — the largest item), the
   two MMY lemmas (a positive word exists at every vertex), Lévy's upward theorem (m3's Lemma 6.1;
   Mathlib has the upward theorem).
3. Transcribe **(1)** (m3 §7, vertex-pinned: its Lemma 4.1 measures the cylinder of `γ₂(π_w)γ₀`, so the
   estimate already pins the vertex; only the §7 event display has to be replaced), then replace
   `Main.lean:66` by `MVDesign.main_of_three` applied to (2), (3) and (1).

**Do not revisit.** (i) (3) formulated as the a.e. diameter shrink, or any contraction requiring
*balanced heights* — both superseded (Addendum 42); the a.e. shrink is a by-product, kept as
`ShrinkStatement`/`main_of_shrink`.  (ii) The six dead routes listed in Addenda 36 and 40 (volume/mass
arguments, bounded-length descendant families, `hsurv` via (H1)+(H2), bounded-lag conditional
Borel–Cantelli, …).  (iii) The letters-only reading of (1) (Addendum 39) — (1) carries its vertices.

**Independent checks on disk** (mine, not the members'): `.scratch/p3/{rv.py, m6check.py, m6end2end.py,
birk2.py}` — Rauzy conventions, m6's contraction on 12 000 random balanced instances, positive words in
the class of `P3`, the end-to-end contraction on a real orbit, and the `(r'−s')/(r−s) ≤ κ` bound.

### Addendum 44: (3) needs a UNIFORM entry bound — design repaired; the contraction loses the balance hypothesis

**The defect, stated precisely.**  `MVDesign.Statement3` (`MasurVeech/MasurVeech/Design.lean`) reads
`∀ lam, HasPositiveBlocks P lam → RayCondition P lam`, and `HasPositiveBlockAt` only asks
`1 ≤ Q(vertex P w) v a b` — there is **no upper bound** on the entries.  The design's own proof
(Addendum 42) does not give that.  A positive block `R` with entries in `[1, M_R]` contracts the
spread of the normalised columns by a factor `1 − 1/(d·M_R)`: the factor **depends on the block's own
entry bound**, so peeling from the latest block gives only `S(γ_k) ≤ ∏_j (1 − 1/(d·M_{j(k)}))`, and
with `M_j → ∞` that product need not tend to 0 (`Σ_j 1/M_j < ∞` is consistent with everything the
hypothesis says).  So the unbounded form is strictly stronger than the argument supports.  It is
**not refuted here** and I do not claim it is false; what is recorded is that the proof on the table
does not reach it, and that the tree should not carry an interface whose stated proof stops short.

**The repair is free**, because (2) already delivers the bound: the word `v` of
`CombData.exists_uniform_bound'` is a *single fixed word* with entries in `[1, C₁]` at every
admissible vertex, and `MVDesign.hasPositiveBlocks_ae` feeds exactly that word to (1).  So (1)+(2)
give blocks with one `M`, not merely `HasPositiveBlocks`.  New definitions
`PosBlock.HasPositiveBlockAtBdd` / `HasPositiveBlocksBdd` (entries in `[1, M]`, `M : ℕ`) and

  `Statement3Bdd P := ∀ (M : ℕ), ∀ lam, lam ∈ simplexCyl P [] → (∀ k, lam ∉ cylStop P (pathWord P lam k))
     → HasPositiveBlocksBdd P lam M → RayCondition P lam`,

with `Statement3` and `main_of_three` kept unchanged (the bounded form is the one with a proof; the
person has been told and asked whether to restate (3) outright).

**The contraction is STRONGER than m6's, and simpler than the Hilbert route of Addendum 42.**  The
sup-norm spread `S(Q) = max_{b,b',a} |ncol b a − ncol b' a|` is already wired to the cylinder diameter
by the landed `ColShrink.diam_le_of_cols_close` (`diam ≤ 2S`), so no Hilbert metric and no dictionary
are needed.  With `h = cs(Q)`, `θ_{ba} = Q'_{ab}h_a/h'_b` (so `ncol(γδ) b = Σ_a θ_{ba} ncol(γ) a`
is a convex combination) and a splitting argument at `a* = argmax h`, one gets

  `1 ≤ Q'_{ab} ≤ M` for all `a,b`  ⟹  `S(QR) ≤ (1 − 1/(d·M))·S(Q)`     (`d = #α`),

**with no balanced-heights hypothesis**: the lower bound `θ_{a*} ≥ 1/(dM)` uses `max h` (not `min h`),
and the case split is on the sign of `c_{a*} = θ_{ba*} − θ_{b'a*}`.  m6's Lemma 3.1(3) had
`1/(dMC)` and carried a balance hypothesis it did not need.  Checked on 4000 random exact-arithmetic
instances (`.scratch/orch/contr.py`, `F=fractions.Fraction`, `d ≤ 5`, `M ≤ 10`), zero violations;
monotonicity `S(QR) ≤ S(Q)` for `R ≥ 0` on 2000 more, zero violations.  The end-to-end bound
`S(γ_k) ≤ κ^{s(k)}` (with `s(k)` the number of disjoint positive blocks) also holds with a very large
margin on real orbits of `d = 3, 4` (`.scratch/orch/peel3.py`, 150-digit decimal arithmetic: at
`k = 400`, `S ≈ 4·10^{-20}` against the bound `0.98`), and the same script confirms that every `m ≤ N`
admits a positive block within 100 letters (296 of 300 starting positions for `d = 3`).

**Landed this round.**  `RayPointwise.lean` (from swarm `smvxpqnff` m4, direction C, refereed and
accepted): `iterOK_pathWord_of_notMem_cylStop` (the `IterOK` induction with the stopping hypothesis
only *along* the greedy path, not for every word), `mem_simplexCyl_nil_of_mem`
(`Δ_γ ⊆ Δ_∅`, from `one_le_Q_diag`), `tendsto_diam_pathWord_of_cols` and the headline
`rayCondition_of_cols` — the pointwise last mile, exactly the statement asked for, no weakening.
Axiom-clean; `lake build` green at **8772** jobs; the only real `sorry` is still `Main.lean:66`.

**Also proved, not yet landed** (composing (1)+(2) with the bounded statement; `PosBlock` namespace,
`.scratch/orch/assemble.lean`, axiom-clean): `hasPositiveBlocksBdd_ae`
(`(1) → (2) → ∀ᵐ λ, ∃ M, HasPositiveBlocksBdd P lam M`), `hray_of_threeBdd` and
`main_of_threeBdd : (1) → (2) → Statement3Bdd → main`.  So the whole assembly layer is done and (3)
is now the only missing input of the main theorem besides (1) itself.

### Addendum 45: (3) IS FORMALISED — `PosBlock` + `Peel` + `RayPointwise` + `PosBlocks` landed

The main theorem now misses exactly one input: **(1)**.  (2) was already proved, and (3) is now a
theorem, so `MVDesign.main_of_threeBdd : Statement1 P → Statement2 α n → Statement3Bdd P → main` is
proved and consumes all three.

**What landed** (all axiom-clean, all warning-free with and without `-DautoImplicit=false`, one build
at a time; `lake build` green at **8775** jobs; the only real `sorry` in the tree is still
`Main.lean:66`):

| file | content | provenance |
|---|---|---|
| `MasurVeech/PosBlock.lean` | `spread` (sup-norm spread of the normalised columns), `ncol_append_eq` (mixing identity: `ncol(γδ) b` is a convex combination of the `ncol(γ) c` with weights `mixW = Q_γ(δ)_{cb}h_c/h'_b`), `spread_append_le`, **`spread_append_contract`** (`≤ (1 - 1/(d·M))·spread` for a block with entries in `[1,M]`, **no balance hypothesis**), `diam_simplexCyl_le` (`diam Δ ≤ 2·spread`) | swarm `smvxpqnff` m1 (direction A), landed |
| `MasurVeech/Peel.lean` | `pathWord_eq_of_mem` (a cylinder determines the greedy word), `Blk`, `exists_chain` (a disjoint chain of blocks), `spread_pow_bound`, **`peel_of_contract`** (the columns coalesce: `∀ ε > 0, ∀ᶠ k, ∀ b b' a, |ncol … − ncol …| ≤ ε`) | swarm `smvxpqnff` m2 (direction B), landed |
| `MasurVeech/RayPointwise.lean` | `iterOK_pathWord_of_notMem_cylStop`, `mem_simplexCyl_nil_of_mem`, `tendsto_diam_pathWord_of_cols`, **`rayCondition_of_cols`** (pointwise last mile) | swarm `smvxpqnff` m4 (direction C), landed (Addendum 44) |
| `MasurVeech/PosBlocks.lean` | `Statement3Bdd`, **`statement3Bdd`**, `hasPositiveBlocksBdd_ae`, `hray_of_threeBdd`, **`main_of_threeBdd`** | orchestrator (composition), landed |

**The proof of (3) in one line**: peel a disjoint chain of positive blocks with entries in a fixed
`[1,M]` off the greedy path; each multiplies the spread of the normalised columns by `≤ 1 - 1/(dM)`,
appending letters never increases it, so the spread tends to `0`; `diam ≤ 2·spread` gives the
shrinking of the cylinders; `TowerGlue.ray_of_shrink_and_tower` gives the ray condition.  No measure
theory, no Appendix A, no balance hypothesis, no Hilbert metric.

**The uniform bound `M` is the one correction to the design** (Addendum 44): `Statement3` (only the
lower bound `1 ≤ Q`) is *kept* in `Design.lean` for the record, with a docstring saying that it is not
what the proof gives and that `Statement3Bdd` is the proved form; `Design.lean`'s `Statement3`
docstring now points at it.  No declaration of `Design.lean` was changed, and `Main.lean` was not
touched (`sorry` still at line 66).

**A remark on `spread_append_contract` that is worth keeping**: the only place where the shape of the
argument could have needed balance is the lower bound `θ_{a₀} ≥ 1/(dM)` for the mixing weight at
*one* letter; taking `a₀` of *maximal* height gives it with no hypothesis, while m6's proof used the
minimal height and hence needed `𝔐(h) ≤ C𝔪(h)`.  The rest is a total-variation bound
(`beta_le_of_mass`) plus the elementary `abs_sum_sub_mul_le`.

**Where the two paper proofs stand**: m6's PROOF.md is now formalised in substance (its Lemma 3.1 was
superseded by the stronger contraction above; its Appendix-A route is not needed at all for (3)).
m3's PROOF.md — statement (1) — remains the only open piece: Appendix A's `simpleyoccoz`
(swarm `smvxpqnff` m3 is on Kerckhoff's lemma), strong connectivity of the Rauzy class with a length
bound, m3's Lemma 4.1 (bounded lag at a balanced node) and Lévy's recurrence lemma
(swarm `smvxpz23d`).  Frozen targets for those four are in `.scratch/orch/statement1_targets.md`.

### Addendum 46: ruling — (3) carries the entry bound, and the bound replaces the old statement

The person's ruling: *"Replace with the bounded version outright.  In (3) as I have written it the word
is always the same, so the boundedness is automatically true, but your condition just requiring
boundedness instead of always the same word is nicer."*

So `Design.lean` was restructured (Addenda 44–45 superseded on this point):

* `HasPositiveBlockAt (P) (lam) (M : ℕ) (m : ℕ)` — **the** definition, with the entry bound
  `∀ a b, 1 ≤ Q … ∧ Q … ≤ (M : ℤ)`; `HasPositiveBlocks (P) (lam) (M : ℕ)` — same `M` for all blocks.
  The unbounded versions are **gone** (the bounded version replaces them outright, it does not sit
  beside them).
* `Statement3 P := ∀ (M : ℕ) (lam : α → ℝ≥0), (∀ k, lam ∉ cylStop P (pathWord P lam k)) →
  HasPositiveBlocks P lam M → RayCondition P lam`.  The `cylStop` hypothesis is the only extra one
  (a null-set condition, discharged a.e. by `ae_notMem_cylStop_all` in `hray_of_three`); positive
  coordinates of `lam` are **not** assumed, they follow from a block at time `0`
  (`RayPointwise.mem_simplexCyl_nil_of_mem`).
* `hasPositiveBlocks_ae : (1) → (2) → ∀ᵐ λ, ∃ M, HasPositiveBlocks P lam M` — the bound `M` is
  exactly where (2) enters.
* `hray_of_three` now takes `hn : 2 ≤ n` (it needs `ae_notMem_cylStop_all`); `main_of_three` keeps its
  shape and its name, now with the bounded `Statement3`.
* `PosBlocks.lean` contains exactly one theorem, **`MVDesign.statement3 : Statement3 P`** (given
  `hP`, `hn`), proved from `PosBlock.peel_of_contract` + `PosBlock.spread_append_contract` +
  `RayPointwise.rayCondition_of_cols`.  `Statement3Bdd`, `hasPositiveBlocksBdd_ae`,
  `hray_of_threeBdd`, `main_of_threeBdd` no longer exist: they were the same statements under
  `…Bdd` names and are now the design's own.
* `PosBlock.lean` no longer defines the block predicates (they live in `Design.lean`); `Peel.lean`
  imports `Design` and states `peel`/`peel_of_contract` with `MVDesign.HasPositiveBlocks`.

**Cleanliness pass on the new files.**  All four (`PosBlock`, `Peel`, `PosBlocks`, `RayPointwise`)
now carry the standard copyright header, the module docstring after the imports, and build with **no
warnings** in both modes (`lake env lean` and `lake env lean -DautoImplicit=false`).  `RayPointwise`'s
two `show`-linter warnings were removed by giving the term instead of a `show` (`⟨trivial, …⟩`).

**State, re-measured**: `lake build` green at **8775** jobs; the only real `sorry` in the tree is
`Main.lean:66`; the twelve headlines of `PosBlock`/`Peel`/`RayPointwise`/`PosBlocks` plus
`MVDesign.statement3` are all `[propext, Classical.choice, Quot.sound]`.  The main theorem now needs
**only (1)**: `MVDesign.main_of_three P hP hn (1) (statement2 hn) (statement3 P hP hn)`.

### Addendum 47: Appendix A phase 1 landed — Kerckhoff's lemma in cylinder-mass form

`MasurVeech/AppendixA.lean` (namespace `AppendixA`, from swarm `smvxpqnff` m3's `Avg.lean`,
refereed and accepted) starts the shared base of statement (1).  Everything in it is about the
Rauzy–Veech path matrices and the exact mass formula — no measure on a projective space.

* `cond P w δ = (∏_b cs P w b) / (∏_b cs P (w ++ δ) b)` — the mass of `Δ(wδ)` relative to `Δ(w)`
  (`volume_append_eq_cond` identifies it with the `PacketP10.volume_append_mul` ratio);
* `cond_arrow : cond P w [e] = h_loser / (h_loser + h_winner)`;
* `state_mono`, `cs_append_eq_sum` (`cs P (w++δ) α = (B_δ q)_α`), `sum_cond_mul_cs` — the key
  identity of the induction: the masses of the (at most two) arrows whose winner is not `α`, weighted
  by the new `α`-height, add up to the old `h_α`;
* **`kerckhoff_aux`**: for `r > 0` and every finite prefix-free `S` of continuations of length `≤ N`,
  with no winner `α` and `r < cs P (w ++ δ) α` on `S`, `∑_{δ ∈ S} cond P w δ < cs P w α / r`;
* **`kerckhoff`**: `∑_{δ ∈ S} cond P w δ < 1/T` under the crossing condition `T·h_α < h'_α` — the
  source's `P_q(γ ∈ Γ_α, (B_γ q)_α > T q_α) < T⁻¹`, with `kerckhoff'` in the `∑_c Q'(δ)_{cα}h_c`
  form.

**A correction to my own task text, recorded**: I had asked for `cond P w [e] = h_α/(h_α+h_β)` with
`α` the *winner*; that is false.  Column `b` of `Q(w)·V` gains `col_α` exactly when `b` is the
**loser**, so the ratio is `h_loser/(h_loser + h_winner)` — which is what the source's
`P_q(γ|π) = q_β/(q_α+q_β)` in `.scratch/avg/APPENDIX_A.md` says, and what the member proved.  The
member caught it; the tree has the correct form.

**Independent check** (mine, not the member's): exact rational arithmetic, `d = 3`, five words `w`,
all three letters `α`, `T ∈ {2, 3, 5, 1/2}`, taking the minimal crossing family inside the NoWin tree
(depth ≤ 9): 60 instances, all satisfy `∑ cond < 1/T` (from `0.028` up to `1.0` against `1/T`), all
families prefix-free.  Script: `.scratch/orch/kcheck.py`.

**What phase 1 does not do** (and what the next round needs): completeness — the complement family
has mass `1 - ∑`, which is where `𝔐(q)` (the `max{…, 𝔐(q)}` in `simpleyoccoz`) enters; the
construction of the minimal crossing family as a `Finset` with prefix-freeness discharged
(`kerckhoff` takes prefix-freeness as a hypothesis, the honest interface); and Theorem
`simpleyoccoz` itself, by induction on `k = #𝒜'` with `𝔪_k` (the max of `𝔪_{𝒜'}` over `#𝒜' = k`).

**State**: `lake build` green at **8775** jobs, `AppendixA` warning-free in both modes, all six new
headlines `[propext, Classical.choice, Quot.sound]`; the only real `sorry` is still `Main.lean:66`.

### Addendum 48: the abstract recurrence lemma landed; next swarm on (1)'s shared base

**Landed `MasurVeech/LevyRecurrence.lean`** (namespace `LevyRecurrence`, from swarm `smvxpz23d` m1,
refereed and accepted): `levy_recurrence` — m3's Lemma 6.1.  Finite level maps `π n : X → Y n`
refining each other, a probability measure `μ`, a target set `Z` measurable for the σ-algebra
generated by the levels, and the hypothesis that every atom of every level `n ≥ N` contains a subset
`Fy` of relative outer measure `≥ δ` disjoint from `Z`; conclusion `μ Z = 0`.  The proof is Lévy's
upward theorem (`Integrable.tendsto_ae_condExp`) plus: the conditional expectation is *atom-constant*
(`measurableSet_comap` unfolding), null atoms are removed once and for all
(`measure_iUnion_null`, the only place `Fintype (Y n)` is used), and then
`(1-δ/2) μA ≤ ∫_A μ[1_Z|F n] = μ(A ∩ Z) ≤ μ(A ∖ Z) ≤ (1-δ) μA` with `μA > 0`.

**Two encoding traps, recorded because they cost a round**:
* The level σ-algebra must be `MeasurableSpace.comap (π n) ⊤` with the **discrete** `⊤` on `Y n`.
  My task text said `⊥`; on `MeasurableSpace` the bottom element is the *indiscrete* σ-algebra
  (`measurableSet_bot_iff`), so every level would have been trivial and the lemma degenerate.  The
  member caught it and also proved the literal-`⊥` version (`RecurrenceIndiscrete.lean`), which is
  degenerate and is **not** landed.
* `Fy` is not assumed measurable (`μ Fy` is the outer measure) — a genuine strengthening of the paper
  statement, and it costs nothing.

**State**: `lake build` green at **8777** jobs; the only real `sorry` is `Main.lean:66`; the seven
new headlines of `AppendixA`/`LevyRecurrence` are `[propext, Classical.choice, Quot.sound]`;
`Check.lean` reports both modules.

**Next swarm `smvxqlc2j`** (3 members, 300 steps, 540 min) on the shared base of (1), one direction
each:
* **E** — Appendix A phase 2, Theorem `simpleyoccoz` (the a priori estimate, uniform in the node):
  the `𝔪_k` induction, with `AppendixA.kerckhoff_aux` as the engine.
* **F** — strong connectivity of the Rauzy class with a diameter bound
  (`∃ L, ∀ Q reachable from P, ∃ u, u.length ≤ L ∧ vertex P u = Q`).  The task text says explicitly
  that the terminal-SCC argument alone is **not** a proof (it gives only that every vertex reaches
  the component), so a genuine argument is needed; partial results are welcome.
* **G** — the instantiation of `levy_recurrence` to the level-`n` cylinder partition of the simplex
  (level map `λ ↦ pathWord P λ n`), giving the a.e.-null set of points that follow `γ₀` at no time
  `≥ N`.

With E, F, G and m3's Lemma 4.1 the transcription of m3's §7 is the only thing left for (1).

### Addendum 49: strong connectivity of the Rauzy class, with a uniform return bound — landed

`MasurVeech/RauzyReach.lean` (namespace `RauzyReach`, from swarm `smvxqlc2j` m3, refereed and
accepted) settles the combinatorial gap recorded in Addendum 47 (m3's Lemma 1.6), and it does so
*without any admissibility hypothesis*:

* `rvStep_injective : Function.Injective (fun Q => Q.rvStep e)` — the inverse Rauzy move is
  determined by the target and the label;
* `mem_of_rvStep_mem` / `mem_of_closed_reachable` — **the counting argument**: a finite set closed
  under both arrows is invariant under each arrow (injectivity + equal cardinality), hence no arrow
  enters it from outside; a word from `P` into such a set therefore starts in it;
* **`reach_back : Reach P Q → Reach Q P`** and `reach_of_reach` — the class of `P` is strongly
  connected.  This is the step whose informal version ("`R` is minimal, so the terminal component is
  everything") does not follow, cf. Addendum 47; the counting argument repairs it;
* `exists_return_path`, `returnWord`, `returnBound`, `returnWord_length_le`,
  `vertex_returnWord_append` — a chosen return word of length `≤ returnBound P` (depending on `P`
  only) with `vertex Q (returnWord P Q ++ γ) = vertex P γ`, i.e. exactly the `pad P w` that m3's
  Lemma 4.1 needs to make the "follows `γ₀`" event vertex-pinned at a bounded lag;
* `exists_path_between`, `exists_uniform_path_between` — the class has a finite diameter.

**A false statement in my own target note, machine-refuted.**  `.scratch/orch/statement1_targets.md`
first stated (I1) with the hypothesis `Q.Admissible` instead of class membership.  That is **false**:
admissible vertices in different Rauzy classes are mutually unreachable, and for `n = 3` there are 6
classes of size 3.  `RauzyReach.not_exists_path_to_admissible` is the machine-checked refutation
(`Q1` admissible, `P1` admissible, `Q1` not reachable from `P1`), and the note is corrected.  The
campaign's `MVDesign.Statement1` was never affected: it quantifies over `∃ u, vertex P u = π₀`, i.e.
over the class of `P`.

**State**: `lake build` green at **8778** jobs; `RauzyReach` warning-free in both modes; the twelve
headlines reported in `Check.lean` are all `[propext, Classical.choice, Quot.sound]`.  (The file also
installs `Fintype (CombData α n)` and `DecidableEq (CombData α n)` as global instances — harmless for
the tree, which builds green with them.)

### Addendum 50: (I1) returned — strong connectivity landed; (I4) landed, the Lévy step is instantiated

Two acceptances from swarm `smvxqlc2j`, both landed and both on the critical path of (1).

**`RauzyReach.lean` (direction F, m3)** — see Addendum 49: `reach_back`, `exists_return_path`,
`returnWord`/`returnBound`/`vertex_returnWord_append`.  This is the `pad` that Lemma 4.1 needs.

**`CylinderRecurrence.lean` (direction G, m1)** — the Lévy step (m3's Lemma 6.1) instantiated on the
level-`n` cylinder partition:

* `CylRec.Word k = {w : List Bool // w.length = k}` (finite); the level map is
  `λ ↦ CombData.pathWord P λ k`, its atoms are the level-`k` cylinders (`lvl_eq_iff`,
  `measurableSet_lvl_atom`, `lvl_refine`); the set `Nbad` where the greedy path is undefined is
  proved null once (`measure_Nbad`) and removed (`measure_eq_of_sdiff_Nbad_eq`);
* **`CylRec.cylinder_recurrence`**: if every level-`k` cylinder with `k ≥ N` carries a subset of
  relative mass `≥ δ` disjoint from `Z = {x ∈ Δ_∅ : x follows γ₀ at no time ≥ k}`, then `Z` is null;
* `CylRec.cylinder_recurrence_ae`: the a.e. form — for a.e. `x` there is `m ≥ N` with
  `x ∈ Δ(pathWord P x m ++ γ₀)`.

That is the form both routes use: Route A (§7 of m3's proof) and Kerckhoff's Corollary 1.9 (his
"subdivide into `C`-distributed sub-simplices, throw out the subsets corresponding to `B`").

**Frozen interface** (`.scratch/orch/statement1_targets.md`, compiled in `.scratch/orch/s1_iface.lean`):
`S1.Step` (what (I2)+(I3) give), `S1.LevyHyp` (what `CylRec.cylinder_recurrence` delivers, now
landed), `S1.Conclusion` (= `Statement1` at a fixed `(π₀, γ₀)`).  So after (I2) and (I3) the
assembly of (1) is a two-step composition, which is mine to do.

**In flight now**: `smvxqlc2j` m2 on (I2) (`simpleyoccoz`, the a priori estimate); `smvxr149x` m1 on
Kerckhoff's Proposition 1.4 (the combinatorial half of his alternative route);
`smvxr5sfq` m1 on (I3) (Lemma 4.1: bounded lag at a balanced node, with the landed `pad`), which
also delivers Kerckhoff's Corollary 1.2 (`cond` lower bound at a balanced node) as its first step.

**State**: `lake build` green at **8779** jobs; the only real `sorry` is `Main.lean:66`; every landed
headline in `Check.lean` is `[propext, Classical.choice, Quot.sound]`.

### Addendum 51: the main theorem is now TWO inputs away — and the vertex pinning is not one of them

`MasurVeech/MainReduction.lean` (namespace `LetterRec`, orchestrator, landed) reduces the main theorem
to two analytic statements about the expansion, both uniform in the node:

* `LetterRec.BalancedDescendants P C` — from every node `w`, a prefix-free family of descendants
  `w ++ γ` that are `C`-balanced and whose cylinders carry a definite fraction of `Δ(w)`.  This is
  exactly what Appendix A's Theorem `simpleyoccoz` must give (m3's Lemma 5.1).
* `LetterRec.DistortionBound P C V` — at a `C`-balanced node, the fixed word `V` is followed
  immediately with definite mass: `δ·σ(Δ(w)) ≤ σ(Δ(w ++ V))` (Kerckhoff's Corollary 1.2 in this
  language).

and it proves the whole chain in between, axiom-clean:

| step | name |
|---|---|
| both inputs ⟹ a definite fraction of every cylinder follows `V` at some time `≥ |w|` | `stepLetters_of` |
| ⟹ a.e. `λ` follows `V` at arbitrarily late times | `ae_follows_of_step` |
| ⟹ positive blocks a.e. (`V` is positive with a uniform bound at *every* vertex) | `posBlocks_ae_of_recurrence` |
| + (3) ⟹ the ray condition a.e. | `hray_of_blocks` |
| ⟹ **the main theorem** | `main_of_recurrence`, `main_of_balanced` |

**The decisive observation** is `MVDesign.exists_word_pos_everywhere` (proved long ago, unconditionally):
there is a *single* word `V` whose Rauzy matrix is entrywise in `[1, M]` at **every** admissible
vertex.  Therefore the letters-only recurrence of `V` ("for a.e. `λ`, for every `N` there is `m ≥ N`
with `λ ∈ Δ(pathWord λ m ++ V)`") already produces positive blocks with a uniform bound, **at
whatever vertex the block starts**.  So the main theorem does not need the vertex-pinned statement
(1) at all: no `pad` path, no strong connectivity, no bounded-lag lemma, no §7 vertex bookkeeping.
Those remain necessary for (1) *as stated* (which the person wants for other applications), and they
are being proved (`RauzyReach`, Lemma 4.1 in flight), but they are off the critical path to `Main.lean`.

**Consequence for the plan**: the remaining inputs of the main theorem are `BalancedDescendants`
(direction E, in flight) and `DistortionBound` (step 2 of the Lemma-4.1 task, in flight).  Both are
finite, uniform-in-the-node statements; neither needs the Lévy instantiation (`CylRec`, landed) to be
re-proved.  `LetterRec.main_of_balanced` is the shape `Main.lean` will consume once they land.

**State**: `lake build` green at **8780** jobs; `MainReduction` warning-free; the six new headlines
are `[propext, Classical.choice, Quot.sound]`; the only real `sorry` is still `Main.lean:66`.

### Addendum 52: the main theorem is ONE INPUT away — `BalancedDescendants`

`MasurVeech/BoundedLag.lean` (namespace `BoundedLag`, from swarm `smvxr5sfq` m1, refereed and
accepted) proves **Lemma 4.1 in full**, in exactly the frozen statement:

* `BoundedLag.cond_ge_of_balanced` — **Kerckhoff's Corollary 1.2 in mass form**: at a `C`-balanced
  node, `(1/(C·d·M))^d ≤ AppendixA.cond P w η` for any word `η` whose path matrix at the node has
  entries `≤ M`.  Proof: a minimal-height letter `b₀`, `cs_append_eq_sum` bounds every child height by
  `d·M·C·h_{b₀}`, while `h_b ≥ h_{b₀}`; multiply the `d` factors.
* `BoundedLag.padWord`, `padWord_spec`, `pathQ_padWord_le` — the nonempty return word (with a
  `[true]` fallback so that `|w| < m`), and the uniform matrix bound.
* **`BoundedLag.bounded_lag`** — `∃ K δ, 0 < δ ∧ ∀ w, Bal w C → δ·σ(Δ(w)) ≤ σ{x ∈ Δ(w) : ∃ m,
  |w| < m ≤ |w| + K, vertex P (pathWord P x m) = P ∧ x ∈ Δ(pathWord P x m ++ γ₀)}`, with
  `K = returnBound P + 1 + |γ₀|` and `δ = (1/(C·d·M))^d`, both independent of the node.

**Then `cond_ge_of_balanced` discharged the distortion side of `MainReduction`**: `LetterRec.distortionBound`
(proved in `MainReduction.lean` by feeding `cond_ge_of_balanced` into
`AppendixA.volume_append_eq_cond`, with `M` the finite supremum of the matrix entries over the
vertices) gives `LetterRec.DistortionBound P C V` for every `V` and every `C ≥ 1`, unconditionally.

Hence, in `MasurVeech/MainReduction.lean`, axiom-clean:

```
LetterRec.main_of_balancedDescendants (P) (hP) (hn) (C : ℝ) (hC : 1 ≤ C)
    (hbd : BalancedDescendants P C) :
    ∀ᵐ lam, ∃! μ, Invariant μ (P.toIET lam) ∧ μ (Ico 0 1) = 1
```

**So the main theorem now has exactly ONE unproved input**: `LetterRec.BalancedDescendants P C` —
from every node a prefix-free family of `C`-balanced descendants carrying a definite fraction of the
cylinder's mass.  That is precisely Appendix A's Theorem `simpleyoccoz` (m3's Lemma 5.1), which is
swarm `smvxqlc2j` m2's direction E, still in flight.  Everything else on the path is landed: (2)
(`statement2`, `exists_word_pos_everywhere`), (3) (`statement3`), the Lévy instantiation (`CylRec`),
the distortion bound, and the assembly (`Assembly.masurVeech_of_components`, `InjTower.hinj_of_tower`).

**State**: `lake build` green at **8781** jobs; `BoundedLag` and `MainReduction` warning-free in both
modes; every headline in `Check.lean` is `[propext, Classical.choice, Quot.sound]`; the only real
`sorry` is still `Main.lean:66`.

### Addendum 53: `BalancedDescendants` reduced to `BalanceStep`; the whole tree is one statement away

`MasurVeech/Apriori.lean` (namespace `Apriori`, from swarm `smvxqlc2j` m2, refereed and accepted as a
*reduction*) formalises Appendix A's induction and lands on the tree's `(I2)` interface:

* the functionals `mmin s q`, `Mk k q = max_{#s=k} mmin s q` with `Mk_le_of_le` (monotone in `k`),
  `Mk_card` (`Mk (#α) = min`), `le_Mk_one` (`Mk 1 = max`);
* `Statement P k Cb Cm` / `StatementMin` — the `k`-statement of the induction (a prefix-free family of
  definite mass, after which the state is `Cb`-balanced on `k` letters and the maximum grew by `≤ Cm`);
* `statement_one` (`k = 1`, `C = 2`), `statement_min` (the paper's `Γ₁`, losing `1/#{k-subsets}`),
  `prefixFree_comp` + `sum_comp` (masses multiply under composition), `statement_succ` (the `k → k+1`
  step), `statement_exists` (the assembled induction);
* **`Apriori.balancedDescendants_of_balance : BalanceStep P C → ∃ C' > 1, LetterRec.BalancedDescendants P C'`**.

`Apriori.BalanceStep P C` is the paper's `Γ₂`–`Γ₄` in cylinder-mass form, with constants uniform in
`w`, `A'`, `Cb`, `k` and a *new* letter `θ ∉ A'` in the conclusion:

```
∀ Cb ≥ 1, ∀ k < #α, ∀ A' (card = k), ∀ w,
  (∀ b ∈ A', (1/Cb)·max w ≤ st w b) →
  ∃ T prefix-free,  1/C < ∑ η ∈ T, cond P w η  ∧
  ∀ η ∈ T, ∃ θ ∉ A',  (∀ b ∈ insert θ A', (1/C)·max(wη) ≤ st (wη) b) ∧  max(wη) ≤ C·max w
```

**So the project is now ONE statement away from discharging `Main.lean:66`**:

```
Apriori.BalanceStep P C   (for some C > 1)
  → Apriori.balancedDescendants_of_balance → LetterRec.BalancedDescendants P C'
  → LetterRec.main_of_balancedDescendants  → masurVeech_ae_unique_invariant
```

Everything else is landed and verified: (2), (3), the Lévy instantiation, the distortion bound, the
Lemma-4.1 bounded-lag lemma, strong connectivity, and Appendix A's `Γ₁` + induction.

**In flight**: swarm `smvxrknd6`, two members on `BalanceStep` — direction H (the extension `Γ₂`: from a
node and a `k`-set `A'`, a prefix-free family of definite mass after which a row ends outside `A'`
while the outside letters stay bounded; the geometric-series argument) and direction I (`Γ₃`–`Γ₄`
given `Γ₂`, using the landed `AppendixA.kerckhoff`).  The frozen target is `Apriori.BalanceStep`.

**State**: `lake build` green at **8782** jobs; `Apriori` warning-free in both modes; every headline in
`Check.lean` is `[propext, Classical.choice, Quot.sound]`; the only real `sorry` is `Main.lean:66`.

### Addendum 54: Kerckhoff's Proposition 1.4 landed — Route B has its combinatorial half

`MasurVeech/KerckhoffBlock.lean` (namespace `Kerckhoff`, from swarm `smvxr149x` m1, refereed and
accepted): **`Kerckhoff.no_isolated`** — for `P` admissible, a block `w` with `vertex P w = P`, and a
subset `S` of the alphabet that is *isolated* in the block (no member is a winner with an outsider as
loser, and every member is a winner at some step and a loser at some step) with `2 ≤ #S`, one has
`#S = #α`.

The proof is the paper's §I argument, and it is now kernel-checked: persistence of an outsider in a
critical position (`TL_succ`), existence of a step where no outsider is critical (`no_TL`), hence
outsiders are never losers and never move (`pos_const`), hence every winner is strictly to the right of
every outsider in both rows (`winner_gt`), hence the outsiders form an initial segment of both rows of
the same cardinality, so `piTop ∘ piBottom⁻¹` preserves it and `P` is reducible — contradiction.

**The encoding matters and is settled**: isolation *alone* makes the statement false (one `true` step
at `P₃` is a block returning to `P₃`, and `{winner, loser}` would be a proper "isolated" set); the
"every member gives and receives" clause is what excludes it, and it is exactly what Kerckhoff's
Proposition 1.5 produces from repeated "jumps".  Task and file agree on that reading.

**Where Route B stands**: Prop 1.4 (combinatorial) ✔; **Prop 1.3** (the simplex measure estimate
`≤ n²/(K−1)`, needing the general mass formula for a real nonnegative matrix) — swarm `smvxs25d4`, just
started; **Prop 1.5 / Lemma 1.6** (the jumps bookkeeping) — not started; then Cor 1.7/1.8 (balanced
states recur a.e.), Cor 1.9 (normality), and the `C`-distortion step, which is the landed
`LetterRec.distortionBound`.

Route A (the paper proof the campaign follows) is still the shorter path to `Main.lean`: it needs only
`Apriori.BalanceStep` (swarm `smvxrknd6`, two members).  Both routes now share everything downstream of
"balanced states recur" — (2), (3), `CylRec`, `LetterRec.distortionBound`, `MainReduction`.

**State**: `lake build` green at **8783** jobs; `KerckhoffBlock` warning-free in both modes; every
headline in `Check.lean` is `[propext, Classical.choice, Quot.sound]`; the only real `sorry` is
`Main.lean:66`.

### Addendum 55: `BalanceStep` as I froze it was too strong — the interface needs a `Cb` parameter

A member of the `BalanceStep` swarm found a defect in **my** target, and it is real.

`Apriori.BalanceStep P C` quantifies `∀ Cb ≥ 1` *inside* the statement: the hypothesis is only
"`A'`-heights are `≥ max/Cb`", so the conclusion — "`insert θ A'` is `C`-balanced" — must hold for a
set `A'` of *arbitrarily* unbalanced heights, with one fixed `C`.  Appendix A's induction does **not**
give that: its level-`k` statement carries its own constant `C_k` and the `k → k+1` step produces
`C_{k+1}` as a function of `C_k`.  The landed `Apriori.statement_succ` shows exactly this — its
conclusion has balance constant `2·C·Cb` — so the tree's own induction already contradicts the shape of
my `BalanceStep`.

**The repair**: the balance constant of the hypothesis must be a parameter.  The target becomes

```
∃ Cb C,  1 ≤ Cb ∧ 1 < C ∧ BalanceStep P Cb C
```

with `BalanceStep P Cb C` the same body as before but with `Cb` fixed rather than universally
quantified; the induction then composes constants `C_1 = 2`, `C_{k+1} = C(C_k)` and ends with a single
constant for `d` letters, which is all `LetterRec.BalancedDescendants` needs.  The member's
`BalanceInterface.BalanceStepCb P (K : ℝ → ℝ)` is the same thing in function form, and
`balanceStepCb_of_balanceStep` records that the (too strong) current form implies it — so nothing
proved so far is wasted.  `Apriori.lean` must be re-parameterised, and
`Apriori.balancedDescendants_of_balance` re-derived against the new form.

**Also landed from that direction** (`MasurVeech/BalanceInterface.lean`, namespace `BalanceInterface`):
`st_ge_one` (heights are positive integers — the degeneracy worry is refuted, the target is not
vacuous at any `w`), `st_eq_of_nonexit` (heights outside `A'` are frozen along a path that never exits
`A'`), `Mk_one_append_le_pow` (the maximum grows by at most `(1+d)^|δ|`), `cond_ge`,
`exists_family_singleton`, `balanceStep_mono`.  And in `.ultramath/smvxrknd6/m2/Two.lean` (not landed
until the interface change settles): **`BalanceStep P 3` for a two-letter alphabet**, i.e. (I2) is
unconditional at `d = 2`.

**State**: `lake build` green at **8784** jobs; `BalanceInterface` warning-free in both modes; every
headline in `Check.lean` is `[propext, Classical.choice, Quot.sound]`; the only real `sorry` is
`Main.lean:66`.  The `BalanceStep` swarm continues with the `Γ₂` extension (direction H, running) and
the interface repair is the orchestrator's next task.

### Addendum 56: `BalanceStep` re-parameterised by `Cb` — the corrected target is `BalanceTarget`

The interface repair promised in Addendum 55 is done, in `MasurVeech/Apriori.lean`:

```lean
def BalanceStep (P : CombData α n) (K : ℝ → ℝ) : Prop :=
  ∀ (Cb : ℝ), 1 ≤ Cb → ∀ (k : ℕ) (A' : Finset α) (w : List Bool),
    A'.card = k → k < Fintype.card α →
    (∀ b ∈ A', (1 / Cb) * Mk 1 (st P w) ≤ st P w b) →
    ∃ T : Finset (List Bool), PrefixFree T ∧
      1 / K Cb < ∑ η ∈ T, AppendixA.cond P w η ∧
      ∀ η ∈ T, ∃ θ : α, θ ∉ A' ∧
        (∀ b ∈ insert θ A', (1 / K Cb) * Mk 1 (st P (w ++ η)) ≤ st P (w ++ η) b) ∧
        Mk 1 (st P (w ++ η)) ≤ K Cb * Mk 1 (st P w)

def BalanceTarget (P : CombData α n) : Prop :=
  ∃ K : ℝ → ℝ, (∀ Cb : ℝ, 1 ≤ Cb → 1 ≤ K Cb) ∧ BalanceStep P K
```

The outgoing constant (`K Cb`) and the mass constant are now a *function* of the incoming balance
constant, which is exactly what the paper's induction produces.  Everything downstream was adapted and
re-proved: `statement_succ : BalanceStep P K → StatementMin P k Cb Cm → Statement P (k+1) (2·K Cb·Cb)
(Cm·K Cb)`, `statement_exists` (with `hK : ∀ Cb ≥ 1, 1 ≤ K Cb`), `statement_card_single`,
`balanced_descendants`, `balanced_descendants_volume`, and

* `Apriori.balancedDescendants_of_balance : BalanceStep P K → ∃ C' > 1, LetterRec.BalancedDescendants P C'`
* `Apriori.balancedDescendants_of_target : BalanceTarget P → ∃ C' > 1, LetterRec.BalancedDescendants P C'`
* **`Apriori.masurVeech_of_balanceTarget : BalanceTarget P → the main theorem`** — axiom-clean.

`BalanceInterface.lean` was trimmed to the transport lemmas that survive (`st_ge_one`,
`st_eq_of_nonexit`, `Mk_one_append_le_pow`, `cond_ge`, `exists_family_singleton`); its old
`BalanceStep`-specific bridges are gone (superseded by the repair).

**The frozen target for the `BalanceStep` swarm is now `Apriori.BalanceTarget P`.**  Note for whoever
picks it up: the paper's `Γ₂` does not need a uniform constant — it produces `K Cb` from `Cb` — so the
`Γ₂` extension should be stated with the incoming constant as a parameter, which is what direction H is
already doing.

**State**: `lake build` green at **8784** jobs; `Apriori` and `BalanceInterface` warning-free in both
modes; every headline in `Check.lean` is `[propext, Classical.choice, Quot.sound]`; the only real
`sorry` is `Main.lean:66`.

### Addendum 57: the general cone-mass formula (Prop 1.3's engine) landed

`MasurVeech/RealMass.lean` and `MasurVeech/Transvection.lean` (namespace `KerckhoffMass`, from swarm
`smvxs25d4` m1, refereed and accepted):

* **`CombData.volume_coneMatOn`** — the mass formula for an arbitrary real nonnegative matrix with
  `det ≠ 0`:

  ```
  σ{ l ∈ Δ : (↑l) ∈ cone M } = ofReal ( |M.det| · (∏_b ∑_a M a b)⁻¹ ) · σ(Δ)
  ```

  generalising the landed `CylinderVolume.volume_simplexCyl` (the `det = 1` case, recovered as
  `volume_coneMatOn_det_one`).  The `|det|` factor is *necessary*: `M = 2·1` gives `|det| = ∏ colsum`,
  ratio `1`, which is right because the cone of `2·1` is the whole positive cone.  Proof:
  `cone M ∩ Δ = (M diag(colsum)⁻¹)•Δ°` plus `PacketB.volume_image_inducedMap_of_det`.
* **`volume_coneMatOn_transMat`** — the one-letter ratio `h_b/(h_b + κ h_i)` for
  `Q · (1 + κ E_{ib})`;
* **`volume_coneMatOn_transMat_growth`** — with `κ = ((K−1)/(#α−1))·(h_b/h_i)`, the ratio is
  `≤ ((#α − 1)/(K−1))`: Kerckhoff's Proposition 1.3 for a *fixed* source column `i`.

Still missing for Prop 1.3 (recorded so it is not redone): (i) the set of continuations along which
`h_b` grows by `K` receiving only from `i` *before* `b` ever wins is contained in the cone of
`Q · transMat i b κ` (a cylinder-inclusion statement about words with winner `i` and loser `b`);
(ii) the sum over `i ≠ b` giving `(#α−1)²/(K−1)` (`PacketP10.volume_iUnion_antichain` is the tool);
(iii) plumbing into `cond`.

**State**: `lake build` green at **8786** jobs; both new modules warning-free in both modes; every
headline in `Check.lean` is `[propext, Classical.choice, Quot.sound]`; the only real `sorry` is
`Main.lean:66`.

### Addendum 58: Γ₂ as I stated it is REFUTED (machine-checked); `BalanceStep` needs the `min` form

Two findings from the `BalanceStep` swarm (member m1, accepted; files kept under
`.ultramath/smvxrknd6/m1/`), both acted on:

**1. The paper's Γ₂ step does not exist at every node.**  `Counterexample.lean` proves, for the
admissible vertex `(top (0,1,2,3), bottom (1,3,0,2))` and `A' = {0,2,3}`, that the Rauzy path
`(false,true,true)` is periodic and that **both rows end inside `A'` at every node**
(`Counterexample.ends_mem_forever`, `no_row_ends_outside`).  So "extend to the first vertex with a row
ending outside `A'`" — the step my brief attributed to Γ₂ — need not exist.  This refutes the form of
`Apriori.BalanceStep` currently in the tree, whose conclusion was a **conjunction** ("a new comparable
letter" *and* "the maximum grew by ≤ C"): in the frozen-outsider configuration the outsider stays
fixed while the others grow, so no descendant satisfies both conjuncts.

**2. The repair is the paper's `min` form.**  `Apriori.Statement`/`StatementMin` already have it:
`Mk 1 (st (w++δ)) < Cb * min (Mk k (st (w++δ))) (Mk 1 (st P w))`, i.e. "the `k`-th largest is within
`Cb` of the maximum **or** the maximum did not grow by more than `Cb`".  The frozen-outsider case is
then covered by the second branch, which is exactly why Appendix A's statement carries `𝔐(q)`.  So
`BalanceStep`'s conclusion becomes

```
∀ η ∈ T, ∃ θ : α, θ ∉ A' ∧
  Mk 1 (st P (w ++ η)) ≤ K Cb * min (mmin (insert θ A') (st P (w ++ η))) (Mk 1 (st P w))
```

and `statement_succ` is re-proved against it (the per-element step becomes a case split on
`mmin (insert θ A') ≤ Mk 1 (st P w)`; swarm `smvxsuthe`, in flight).  Nothing else in `Apriori.lean`
consumes `BalanceStep` except through `statement_succ`/`statement_exists`, so the rest is untouched.

**Also found**: `AppendixA.kerckhoff` requires `NoWin`, which fails along a run — so the paper's
"Γ₂ then Γ₃" separation is not literally available; Γ₂ and Γ₃ have to be handled together (or the
Kerckhoff family re-derived inside the run).  Recorded for whoever attacks `BalanceTarget`.

**Also proved** (kept back until the definition settles): `Apriori.balanceStep_two` — the target
statement for **two letters** with `C = 64` uniform in `Cb, w, A', k` (the Rauzy vertices are
arrow-fixed at `d = 2`, so the heights obey fixed recursions and the family `{true^k ++ [false]}` is
explicit with a telescoping mass).  With `balancedDescendants_of_balance` this makes (I2)
unconditional at `d = 2` — a non-vacuity check on the design.  And the reusable half of Γ₂
(`cs_eq_of_run`, `run_Mk_le`, `run_length_bound`, `exit_le`, `sum_level`).

**State**: `lake build` green at **8786** jobs; the tree still compiles because the defective
`BalanceStep` is a *definition* (nothing false is proved from it — `BalanceTarget → main` is a
conditional arrow).  The only real `sorry` is `Main.lean:66`.  Running: the `min`-form repair
(`smvxsuthe`) and Prop 1.5 (`smvxs8wdx`).

**Consequence for the answer I gave two turns ago**: Γ₂ did *not* close — it turned out to be false as
I phrased it, which is the third interface defect found on this route (after the missing `Cb` parameter
and the missing `min` clause).  The corrected target is strictly weaker and *is* the paper's statement,
so the forecast "Route A is closer" still holds, but the Γ₂ *step* must be re-attacked in the `min`
form and together with Γ₃.

(Erratum to the paragraph above: the `min`-form edit was *reverted* from `Apriori.BalanceStep` within
the same round, because `statement_succ` is stated against the conjunctive form and the tree must stay
green; the defective definition now carries a `WARNING` docstring pointing at this Addendum, and the
repaired definition + re-proved `statement_succ` arrive together from swarm `smvxsuthe`.  The tree
builds at **8786** jobs as of this note.)

### Addendum 59: the `min`-form repair is landed; `BalanceStep` is now the faithful interface

The repair of Addendum 58 is in the tree (swarm `smvxsuthe` m1, refereed and accepted):

* `Apriori.BalanceStep P K` now concludes
  `Mk 1 (st P (w++η)) ≤ K Cb * min (mmin (insert θ A') (st P (w++η))) (Mk 1 (st P w))` — the paper's
  `min{𝔪_{A'∪{θ}}, 𝔐(q)}` clause, i.e. the shape of `Statement`;
* `Apriori.statement_succ` is re-proved against it with the *same* statement
  (`Statement P (k+1) (2·K Cb·Cb) (Cm·K Cb)`), so nothing downstream changed;
* the diff against the previous file touches only `BalanceStep` (docstring + conclusion),
  `statement_succ` (docstring + proof) and two ascriptions — verified by `diff`, not by trust.

My sketch of the proof had an error that the member corrected: in the branch
`mmin (insert θ A') > Mk 1 (st P (w++δ))` the `min` of the *balance-step* conclusion collapses to
`Mk 1 (st P (w++δ))` (not `Mk 1 (st P w)`); the `Mk 1 (st P w)` end of the target is discharged
uniformly by a separate bound.

**Landed alongside, as the *reason* for the repair**: `MasurVeech/BlockedExtension.lean` (namespace
`Apriori.Counterexample`) — at `(top (0,1,2,3), bottom (1,3,0,2))` with `A' = {0,2,3}`, the path
`(false,true,true)` is periodic and both rows end inside `A'` at every node, so the `Γ₂` extension does
not exist there.  So the tree now carries the obstruction next to the corrected interface.

**Where Route A stands**: `Apriori.BalanceTarget P → main theorem` is proved, with `BalanceTarget` now
the faithful `Γ₂`–`Γ₄` statement.  What remains is to *prove* `BalanceTarget` — and after the
obstruction, `Γ₂` and `Γ₃` must be attacked together (`AppendixA.kerckhoff` requires `NoWin`, which
fails on a run), in the `min` form.  The two-letter case (`BalanceStep` at `d = 2`, `C = 64`) is proved
in `.ultramath/smvxrknd6/m1/TwoLetters.lean` but needs adapting to the new signature (`BalanceStep P
(fun _ => 64)`) before landing.

**State**: `lake build` green at **8787** jobs; `Apriori` and `BlockedExtension` warning-free in both
modes; every headline in `Check.lean` is `[propext, Classical.choice, Quot.sound]`; the only real
`sorry` is `Main.lean:66`.  Running: Prop 1.5 (`smvxs8wdx`).

### Addendum 60: Prop 1.5 reduced to `StretchCost`, and why that is a genuine gap in the paper

Swarm `smvxs8wdx` m1 (accepted; **not landed**, kept under `.ultramath/smvxs8wdx/m1/` because what is
past `StretchCost` is conditional).  Compiled with `bash compile.sh` in that directory, exit 0, all
axioms `[propext, Classical.choice, Quot.sound]`.

**Proved there**:
* the height recurrence and monotonicity of `cs` along a step;
* a straddle lemma for the maximum;
* **Lemma 1.6 repaired**: "jumps" are the *first crossings of the absolute level* `L = K'·R` (this is
  the paper's own `C ≠ 1` patch, made precise), and: if a block is breakout-free, every crossing of a
  member is preceded by a win of that member, and all members are stretched to `L`, then
  `Kerckhoff.Isolated` appears.  The paper's `j < |S|` cases are unnecessary;
* Prop 1.4 applied: a *returning* block, breakout-free with genuine crossings, cannot have all
  members stretched;
* level-`N` cylinder masses sum to `1` (`sum_cond_levelWords`), and the mass of the level-`N`
  extensions of `γ` is `cond P w γ` (`cond_sum_extends`);
* Prop 1.3 obtained from the landed `AppendixA.kerckhoff` through the bridge `noWin_iff`;
* `mass_unpaid_crossings`: the part of the estimate that Prop 1.3 *does* pay for (every genuine
  crossing is preceded by a win);
* **Prop 1.5 in cylinder-mass form, from the single input `StretchCost`** (`breakout`, `breakout_set`).

**The gap, precisely** (`StretchCost`): *uniformly in the node `w`, the breakout-free continuations of
`w` along which every height stays below `K·max(w)` carry relative mass at most `1 - ν`.*  It is
**equivalent** to Prop 1.5 (via the level-`N` decomposition), and it is **not** a consequence of the
deterministic engine: a breakout-free step is `S→S`, `T→S` or `T→T`, and on a `T`-step every
`S`-height is frozen (`cs_step_eq_of_both_outside`), so no member ever jumps, Prop 1.3 pays nothing,
while the maximum grows.  Such cycles are common: e.g. `n = 4`, `top = (0,1,2,3)`,
`bottom = (1,2,3,0)`, `S = {1,2}` — the `true` arrow *fixes the vertex* and both last letters are
outside `S`, so `true^N` is breakout-free for every `N`; and `exists_nonBrk_arrow` shows no vertex is
a dead end for breakout-free paths, so no length bound comes from the diagram.  The estimate must
therefore be done in the mass-weighted form `∑ cond` over a *branching* family: in the `T`-step case
the mass telescopes (`cond` of a step with loser `b` is `h_b^old/h_b^new`), which is why the statement
is true, but turning that into a sum over a prefix-free family is the missing argument.

**Second gap**: `Kerckhoff.no_isolated` applies only to a **returning** block; the paper's "only
finitely many such blocks can be strung together before encompassing one beginning and ending with the
same permutation" does not by itself produce one (the isolated sub-collection produced inside the block
need not be a subset of a returning block's members).  Both gaps are the paper's, not ours.

**Consequence for the routes**: this is the first place where a *paper* argument has a hole (all
earlier defects were in my formulations).  Route B is therefore blocked on new mathematics
(`StretchCost`) plus the returning-block bookkeeping, while Route A is blocked on proving
`Apriori.BalanceTarget` (the `min`-form `Γ₂+Γ₃+Γ₄`).  Capacity goes to Route A.

**State**: `lake build` green at **8787** jobs; one real `sorry` (`Main.lean:66`); no member running.

### Addendum 61: the block typology landed; and a numerical refutation of my own mass bound

**Landed `MasurVeech/KerckhoffJumps.lean`** (namespace `Kerckhoff15`, from `.ultramath/smvxs8wdx/m1/
Kerckhoff15.lean`, refereed): the deterministic engine shared by both routes' remaining steps —

* `Brk` (a **breakout**: a member of `S` wins, the loser is outside `S` — the negation of
  `Kerckhoff.Isolated`'s clause), `CDist` (`C`-distributed on `S`), `CrossAt`/`Genuine`/`Stretched`
  (crossings of an absolute level, and whether they are preceded by a win);
* the height recurrence `cs_step` and its consequences: `cs_take_mono` (heights never decrease along a
  path), **`cs_step_eq_of_both_outside`** (a step with winner and loser both outside `S` freezes every
  `S`-height), **`typology_of_not_brk`** (a non-breakout step is `S→S`, `T→S` or `T→T`);
* **`isolated_of_all_stretched`** (Kerckhoff's Lemma 1.6 in repaired form: breakout-free block +
  genuine crossings + all members stretched ⟹ `Kerckhoff.Isolated`; the `j < |S|` cases dropped);
* **`not_all_stretched_of_returning`** (Prop 1.4 for *returning* blocks).

`Check.lean` reports five of its headlines; `lake build` green at **8788** jobs.

**A correction to *my* task text, found by my own numerical check.**  I told the swarm that the mass of
a prefix-free family along which a coordinate has grown by `Λ` is `≤ 1/Λ`, "by telescoping
`cond = h_old/h_new`".  **That is false.**  `.scratch/orch/masscheck.py` (exact rationals, `d = 3`,
four nodes, all three letters, `Λ ∈ {2,3,5}`, minimal-crossing families) gives sums of `0.70`, `0.64`,
`0.51` for `Λ = 2,3,5` at `w = []`, `b = 0` — well above `1/Λ` in every one of the 36 cases.  The
pointwise bound `cond ≤ 1/Λ` on the *last* step is correct, but the sum over a branching family is not
bounded by it: many disjoint minimal-crossing cylinders each pay `≈ 1/Λ`.

So the estimate both routes need is weaker and harder than I said: not `≤ 1/Λ` but a bound of the form
"`≤ 1 − ν`" with `ν` depending only on the data, and it has to be proved by a genuine argument about
the branching structure (which is exactly the `StretchCost` the other member isolated).  Whoever picks
this up must not assume the telescoping bound; the numerically observed sums decrease with `Λ`
(`0.70 → 0.51` for `Λ = 2 → 5`) but far from like `1/Λ`, so the truth is closer to `1 − c/Λ`-shaped
than to `1/Λ`.

**State**: `lake build` green at **8788** jobs; one real `sorry` (`Main.lean:66`); swarm `smvxtf6oy`
(two members on `Apriori.BalanceTarget`: the mass estimate and the `Γ₂`/`Γ₃`/`Γ₄` case) is running and
will be given this correction in their verdicts.

### Addendum 62: `Γ₄` landed — the whole project is now `Gamma3Mass` away

`MasurVeech/Gamma4.lean` (namespace `Apriori.G4`, from swarm `smvxtf6oy` m1, refereed and landed):

* **`Apriori.G4.Gamma3Mass P K₃`** — the joint `Γ₂+Γ₃` statement (Route A's remaining input);
* **`balanceStep_of_gamma3 : Gamma3Mass P K₃ → BalanceStep P (fun Cb => 4·#α·Cb·K₃ Cb)`** — `Γ₄` is
  proved, with constant `4·#α·Cb` and no extra `C₂` factor (it is applied at the `Cb`-balanced node);
* `balanceTarget_of_gamma3`, and **`masurVeech_of_gamma3 : Gamma3Mass P K₃ → the main theorem`**;
* `Γ₄`'s two branches `gamma4_abs`/`gamma4_words` (via `cs_step_le_two`: one arrow at most doubles a
  height), `sum_cond_le_one`, `sum_cond_fibre_le`, and **`exists_prefixFree_mass`** — the minimal
  prefixes of a covering family carry at least its mass, which *replaces the paper's unsound
  truncation* in "`P(Γ₄|π) ≥ P(Γ₃|π)`" (the truncated family is neither prefix-free nor injective).

**Two corrections to my own text, both machine-checked by the member**:

1. **`BalanceStep`'s `min` is a conjunction, not an "or"**: `Mk 1 ≤ K Cb · min x y` ⟺ both bounds.
   So the `min`-form "repair" of Addendum 59 weakened nothing, and my docstring claiming a disjunction
   was wrong (fixed in `Apriori.lean`).  Consequence, and it is good news: `BalanceStep` is *not*
   refuted by the blocked vertices — the blocked case is absorbed inside `Gamma3Mass`, where the
   disjunction lives (`Gamma3Mass` carries "the last arrow is `A' → A∖A'` **or** the maximum already
   exceeds `2d·M(q_w)`"), not by weakening `BalanceStep`.
2. `Γ₄`'s hypothesis needs that disjunction, because at the `BlockedExtension` vertices both arrows
   lose inside `A'` — the paper's unconditional "the last loser is outside `A'`" is false there.

**Where the campaign stands**:

```
Gamma3Mass P K₃   →   BalanceStep P (fun Cb => 4·d·Cb·K₃ Cb)   →   BalanceTarget   →   main theorem
   [OPEN]                    [landed, Gamma4.lean]                [landed]           [landed]
```

and the same `masurVeech_of_gamma3` gives the main theorem directly from `Gamma3Mass`.  So the project
has exactly one open statement left on Route A.  Route B (Kerckhoff) is blocked on `StretchCost`
(Addendum 60) and its engine is landed (`KerckhoffJumps.lean`).

**State**: `lake build` green at **8789** jobs; `Gamma4` warning-free in both modes; every headline in
`Check.lean` is `[propext, Classical.choice, Quot.sound]`; the only real `sorry` is `Main.lean:66`.
Still running: swarm `smvxtf6oy` m2 (the mass estimate for the blocked case).

### Addendum 63: full capacity on `Gamma3Mass` (the last statement of Route A)

Three members started (swarm `smvxu2nu8`), one per direction, plus the mass-estimate member still
running from `smvxtf6oy`:

* **N — `Γ₂` with the dichotomy**: from `w` and a `Cb`-balanced `A'`, a prefix-free family of definite
  mass, each continuation ending either at an available *exit* arrow (winner ∈ `A'`, loser ∉ `A'`) or
  at a node whose maximum already exceeds `2d·M(q_w)`, with all `A'`-heights staying below `2d·M(q_w)`
  along the way.  This absorbs the `BlockedExtension` obstruction.
* **O — `Γ₃`**: the mass of continuations along which some `A'`-height exceeds `2d·M(q_w)` is at most
  `k/(2d)`, by applying `AppendixA.kerckhoff` per letter of `A'` (that family *does* satisfy `NoWin`)
  and summing; needs the level-`N` decomposition `∑_{|δ|=N} cond P w δ = 1`.
* **P — the assembly** (`N` + `O` ⟹ `Gamma3Mass`) and the pure blocked case, where a *new* mass
  estimate may be needed (the naive telescoping bound is false, Addendum 61).

The brief carries the three traps that each cost a round: `min` is a conjunction not a disjunction;
`kerckhoff` needs `NoWin`; and the naive `≤ 1/Λ` mass bound is false.

`TwoLetters.lean` (`BalanceStep` at `d = 2`, `C = 64`, uniform in `Cb`) is still held in
`.ultramath/smvxrknd6/m1/`: adapting it to the post-reparameterisation signature is a small edit
(`BalanceStep P (fun _ => 64)` and the min-form conclusion from the two conjuncts) but it is not on the
critical path, so it waits.

**State**: `lake build` green at **8789** jobs, 82 modules, one real `sorry` (`Main.lean:66`).

### Addendum 64: the first unconditional instance — a.e. two-letter IET is uniquely ergodic

Three files landed from swarm `smvxtf6oy` m2 (refereed and accepted):

* **`MasurVeech/TwoLetters.lean`** — **`Apriori.balanceTarget_two : BalanceTarget P`** for
  `P : CombData α 2` admissible, with `K ≡ 3`, and **`Apriori.masurVeech_two`**:
  **a.e. two-letter interval exchange map is uniquely ergodic**, unconditionally.  The `Γ₂`–`Γ₄`
  family is explicit: with heights `x ≤ y`, `T = {inc^k · res : k < N}`, `N` least with `N·x > y/2`,
  mass `1 − y/(y+Nx) > 1/3`, and every endpoint has `max ≤ 3·min(min, y)`.  This is the campaign's
  first *unconditional* theorem and it exercises the whole chain
  (`BalanceTarget → BalanceStep → masurVeech_of_balanceTarget`) end to end — the non-vacuity check the
  architecture needed after three interface defects.
* **`MasurVeech/MassTelescoping.lean`** — **`mass_grown_le_false`**: a machine-checked refutation of
  the estimate "the mass of a prefix-free family along which a height grew by `Λ` is `≤ 1/Λ`"
  (`P` the two-letter swap, `w = []`, `b = 0`, `Λ = 5/3`, `F = {[true], [false,true]}`: prefix-free,
  every end-height `≥ Λ h_b`, yet `∑ cond = 2/3 > 3/5`).  Diagnosis: **a step that wins `b` costs mass
  without moving `h_b`, which resets the telescoping.**  `mass_grown_le_nowin` shows the estimate is
  true with `NoWin` — i.e. it *is* `AppendixA.kerckhoff`, so it is not new content and cannot settle the
  blocked case, where the growing letter is a winner.
* **`MasurVeech/MassSum.lean`** — `cond_sum_le_one`: a prefix-free family has total relative mass
  `≤ 1`, without any measure theory (induction on the maximal length, `cond_arrow_sum`).

**The open question this raises, and where it is being pursued**: at a *blocked* node (Addendum 58: both
arrows' winner and loser inside `A'`) the obstruction is **not** mass — a cut has mass `1` — but the
*pointwise* clause of `BalanceStep` against a **frozen outsider**: if an outsider's height is far below
`M(q_w)/K Cb` and never grows, no descendant satisfies the `(k+1)`-minimum part of the `min`.  The
`Gamma3Mass` disjunction (swarm `smvxu2nu8`) is where that is supposed to be absorbed; if it cannot be,
the repair is in `BalanceStep`'s conclusion and not in the mass estimates.  `d ≥ 3` remains open.

**State**: `lake build` green at **8792** jobs; the three new modules warning-free in both modes; every
headline in `Check.lean` is `[propext, Classical.choice, Quot.sound]`; the only real `sorry` is
`Main.lean:66`.  Running: `smvxu2nu8` (three members on `Gamma3Mass`).

### Addendum 65: the mass calculus landed; `Gamma3Mass` reduced to an exit-family estimate

`MasurVeech/Gamma3Core.lean` (namespace `Apriori.G4.Core`, from swarm `smvxu2nu8` m1, refereed and
accepted):

* **the mass calculus the tree lacked**: `cond_le_one`, `cond_append_le` (monotone under extending a
  cylinder), **`sum_cond_levelWords`** (`∑_{|δ|=N} cond P w δ = 1`), **`sum_cond_extends`** (fibre
  identity: the level-`N` extensions of `γ` sum to `cond P w γ`), `sum_cond_eq_sum_count`,
  **`sum_cond_le_sum_of_covers`** (a family covered by a prefix-free one has no larger mass);
* **lossless reductions of the last statement**:
  `gamma3Mass_of_exitGrowthMass` (`Gamma3Mass` ⟸ the version with the height bound only at the end of
  each word — the prefix conjunct is free by `state_mono`), `gamma3Mass_of_exitMassBd` (`Gamma3Mass` ⟸
  the **exit-only** family, no growth fallback), and `gamma3Mass_of_gamma2_gamma3` (`Gamma3Mass` ⟸
  `Gamma2In` + `Gamma3In`, the extension split from the covering estimate);
* **the blocked case quantified**: `sum_cs_step_ge_of_both_inside`, `length_le_of_both_inside` — if both
  row-ends stay in `A'`, the `A'`-height sum grows by at least `M/Cb` per letter, so a clean blocked run
  has length `≤ 2·d·#A'·Cb`.  In particular the frozen-outsider configuration cannot persist, and the
  growth branch of `Gamma3Mass` is reached in bounded time.

**The fourth refuted target of this route (mine)**: the Direction-O bound
`mass{some A'-height > 2d·M} ≤ k/(2d)` is **false** — exact rationals give `0.563989` against
`k/(2d) = 0.375` at `BlockedExtension`'s own configuration (`d = 4`, `k = 3`), with the exit family
carrying `0.436011` and growth never used (`.ultramath/smvxu2nu8/m1/orbit.py`).  So the `k/(2d)` form is
dead; what survives is the **exit-family mass bound** `ExitMassBd` (or `Gamma2In` + `Gamma3In`).

**The four refuted targets on this route, for the record** (all mine, all caught before they cost a
round): the missing `Cb` parameter (Add. 55), the `min`-as-disjunction confusion (Add. 59/62), the naive
mass-telescoping bound `≤ 1/Λ` (Add. 61/64, machine-checked in `MassTelescoping.lean`), and now the
`k/(2d)` grading of `Γ₃`.  The pattern is consistent: I have been guessing the *quantitative* form of
each step, and the members' exact computations have corrected it every time.  The lesson for the
remaining work: do not accept a quantitative target of mine without a numerical check.

**Where the campaign stands**: `Gamma3Mass` is the only open statement, and it is now reachable from
either `ExitMassBd` (exit-only family) or `Gamma2In` + `Gamma3In`.  `d = 2` is completely proved
(`TwoLetters.lean`).

**State**: `lake build` green at **8793** jobs; `Gamma3Core` warning-free; every headline in `Check.lean`
is `[propext, Classical.choice, Quot.sound]`; the only real `sorry` is `Main.lean:66`.  Running:
`smvxu2nu8` m2 (Γ₂) and m3 (Γ₃) — both now against the corrected targets.

### Addendum 66: the last statement is now ONE numerical hypothesis — `RaceSmall`

Two files landed from swarm `smvxu2nu8` m2 (refereed and accepted):

**`MasurVeech/Gamma3Race.lean`** (namespace `Apriori.G2`).  A *stop event* at index `j` of a
continuation is "the maximum has exceeded `2d·M(q_w)`, **or** the `j`-th letter is an exit arrow at that
node"; it is *unclean* if moreover some `A'`-height exceeds `2d·M(q_w)` there.

```
RaceSmall P ν  :=  0 < ν  ∧  for every w, A', N:  the level-N words whose FIRST stop event is unclean
                    carry cond-mass ≤ 1 - ν

gamma3Mass_of_race : RaceSmall P ν → Gamma3Mass P (fun _ => 1 + 2/ν)     -- K₃ free of Cb
masurVeech_of_race : RaceSmall P ν → the main theorem
```

On the way: the level-`N` partition, the fibre identity `cond_sum_extends`, growth of the *total*
height, the explicit stopping length (every word of length `⌈2d²M/min⌉+1` has crossed — this removes
the only mass loss), prefix-freeness and the cylinder identity of the minimal stopping family, and the
covering lemma.  Exact-rational numerics: good mass `≥ 0.436` (worst case, the `BlockedExtension`
configuration), `≥ 0.59` on random configurations, i.e. `ν ≈ 0.4`, `K₃ ≈ 6`.  **`RaceSmall` is not
proved.**

**`MasurVeech/Gamma3Refuted.lean`** — **`gamma3_sharp_constant_false`**: my `Γ₃` grading `k/(2d)` is
false, with a small explicit instance (`d = 2`, `A' = {0}`, `w = []`, threshold `4`, prefix-free
`{[t,t,t,t], [f,t,t]}`, mass `3/10 > 1/4`), agreeing with the independent `0.563989 > 0.375` at
`BlockedExtension`.  So the *exit* branch carries the mass — which is exactly what `RaceSmall` says.

**Five refuted targets of mine on this route now** (all caught by members before costing a round): the
missing `Cb` parameter, `min` mistaken for a disjunction, the `≤ 1/Λ` telescoping bound, the `k/(2d)`
grading of `Γ₃`, and (before that) the `Γ₂`-extension statement.  Two of them are now machine-checked
refutations in the tree (`MassTelescoping.lean`, `Gamma3Refuted.lean`), which is the right place for
them.

**Where the campaign stands**: the main theorem follows from `RaceSmall P ν` for any single `ν > 0`
(proved), with numerical evidence that `ν ≈ 0.4` works; `d = 2` is fully proved; Route B is a hedge
blocked on `StretchCost`.  One member still running (`Γ₃`/exit mass).

**State**: `lake build` green at **8795** jobs; both new modules warning-free in both modes; every
headline in `Check.lean` is `[propext, Classical.choice, Quot.sound]`; the only real `sorry` is
`Main.lean:66`.

### Addendum 67: swarm `smvxu2nu8` complete — the board, and the last open statement

Board of `smvxu2nu8` (three members, all ended; two accepted):

* **m1 (direction D, the combinatorial core) — accepted, landed as `Gamma3Core.lean`**: the mass
  calculus (`cond_le_one`, `cond_append_le`, `sum_cond_levelWords`, `sum_cond_extends`,
  `sum_cond_eq_sum_count`, `sum_cond_le_sum_of_covers`), the lossless reductions
  (`Gamma3Mass ⟸ ExitGrowthMass ⟸ ExitMassBd`, and `⟸ Gamma2In + Gamma3In`), and the blocked-run bound
  `length_le_of_both_inside` (`≤ 2·d·#A'·Cb`).
* **m2 (direction N, `Γ₂` with the dichotomy) — accepted, landed as `Gamma3Race.lean` +
  `Gamma3Refuted.lean`**: the whole target reduced to **one** numerical hypothesis `RaceSmall P ν`
  (`gamma3Mass_of_race`, `masurVeech_of_race`, `K₃ = 1 + 2/ν` free of `Cb`), together with the
  stopping-time machinery (level-`N` partition, fibre identity, total-height growth, the explicit
  stopping length `⌈2d²M/min⌉+1`, minimal-family prefix-freeness, covering lemma); and the refutation of
  my `k/(2d)` grading.
* **m3 (directions O and the two-letter instance) — ended without a submission**; its direction O was
  *settled by refutation* (an independent machine-checked `gamma3_mass_bound_false`, agreeing with
  m2's), and its two-letter instance was finished but never submitted.  I read the file, compiled it,
  and landed it as **`MasurVeech/Gamma3TwoLetters.lean`**: `Apriori.G4.gamma3Mass_cxP :
  Gamma3Mass Apriori.cxP (fun _ => 2)` — a machine-checked instance of the *last open statement itself*
  (not merely of `BalanceTarget`), with mass `> 1/2`.  Its scratch `Check*.lean` files include a `sorry`
  and were not landed.

**Where the project stands**:

```
RaceSmall P ν  (some ν > 0)  →  Gamma3Mass P (fun _ => 1 + 2/ν)  →  main theorem      [both arrows proved]
     [OPEN, ν ≈ 0.4 numerically]
```

with `d = 2` fully proved two independent ways (`TwoLetters.lean` via `BalanceTarget`, and
`Gamma3TwoLetters.lean` via `Gamma3Mass` for `cxP`), and Route B a hedge blocked on `StretchCost`.

**The one thing left**: `RaceSmall P ν` for a single `ν > 0` — i.e. uniformly in the node and `A'`, the
level-`N` words whose *first* stop event is unclean carry mass `≤ 1 − ν`.  Numerics: good mass `≥ 0.436`
(worst case, `BlockedExtension`), `≥ 0.59` random; `ν ≈ 0.4`, `K₃ ≈ 6`.

**State**: `lake build` green at **8795** jobs, 89 modules, every headline in `Check.lean` is
`[propext, Classical.choice, Quot.sound]`, the only real `sorry` is `Main.lean:66`.

### Addendum 68: `RaceSmall` as landed in Addendum 66 was FALSE — two machine-checked defects and the repair

Addendum 66 recorded `RaceSmall P ν` as the last open statement of Route A and set swarm `smvxvgknd`
on it. Before the members got going I read the definitions against the two degenerate cases every
consumer must survive, and both refute the statement as written. Both are now theorems in
`MasurVeech/Gamma3Race.lean` (axiom-clean, in `Check.lean`):

* **The empty word never has a clean stop.** `GoodFirst` (the old body of `Good`) asks for a *first
  stop event*; on `[]` there is none, so it is false — `not_goodFirst_nil`. With `Bad := ¬Good` that
  made *every* word bad at level `N = 0`, whose mass is `1` — `sum_badFirst_level_zero`. Hence
  `¬ RaceSmall P ν` for every `P` and every `ν`. The repair is the extra alternative
  `Good = (no stop event in range (δ.length + 1)) ∨ GoodFirst`; the old body is kept under the name
  `GoodFirst`, which is exactly the hypothesis the covering lemma needs (`exists_stopfam_of_good`,
  unchanged proof), and `goodFirst_of_good` converts back at the stopping length, where every word
  has crossed (`exists_stop_length`). Nothing downstream is lost: `gamma3Mass_of_race` now feeds
  `goodFirst_of_good` the crossing it already had from `hN`.
* **`A'` must be proper.** With `A' = univ` there is no exit arrow (`last !e ∉ univ` is false) and a
  crossing is never clean (`Clean` at a node whose maximum exceeds the threshold contradicts
  `Huge`, via `Mk_one_le_iff`), so no word has a clean stop — `not_goodFirst_univ`; and at the
  stopping length the bad words then carry the *whole* mass — `sum_bad_univ_eq_one`. Even with the
  "no stop yet" repair this kills `A' = univ`, because the no-stop mass tends to `0`. `RaceSmall`
  therefore now carries `A'.card < Fintype.card α`, which is *exactly* the shape of `Gamma3Mass`'s
  own hypothesis `k < Fintype.card α` (`A'.card = k`), so the composition loses nothing.

**This is the sixth quantitative target of mine on this route to be refuted, and the first where the
refutation is a one-line logical defect rather than a wrong constant.** The pattern is the same as
Addenda 59/61/64/65/66: I stated the *shape* of a statement from the intended use and did not run
the degenerate cases. Rule adopted from here on: before a statement goes into a brief, its degenerate
cases (`N = 0`, `A' = ∅`, `A' = univ`, `w = []`, `d = 2`) are checked in Lean, not on paper.

**Where the campaign stands**: `RaceSmall P ν` (repaired) is still the single open statement, with
the same chain `RaceSmall → Gamma3Mass P (fun _ => 1 + 2/ν) → main theorem` unimpaired. Exact-rational
numerics of the repaired statement (member m1's `orbit.py`, cut depth `14M + 80`, all nodes of
`d = 3` up to length 6 and of `d = 4` up to length 5, all nonempty proper `A'`): worst good mass
`0.434376` at `P = (top 0,1,2,3 / bottom 1,3,0,2)`, `w = (t,t,t,f,f)`, `A' = {1,2,3}`; `0.686941`
for `d = 3`; `0.436011` at the `BlockedExtension` configuration. Note the ledger's `grow` branch is
`0` there — the exit arrow alone carries the mass, so `ExitMassBd` (Addendum 65) is the sharper target
and `RaceSmall` the weaker one.

**The structural fact worth recording** (it is what the numerics are really saying): the two winners
at a node are the two row-ends, so an **exit arrow exists at a node iff the two row-ends straddle the
partition** `(A', α∖A')`, and then exactly one of the two letters is the exit. Hence along a bad word
every arrow is either internal to `A'`, internal to `α∖A'`, or `(α∖A') → A'`; in particular an
`A'`-height can only grow by absorbing an outsider's height. This is the shape of the paper's `Γ₂`
estimate, i.e. we are again exactly at the place where the source's argument has its hole
(Addendum 60).

**State**: swarm `smvxvgknd` stopped unsolved (it had the false statement in its brief); a new swarm
starts from the repaired statement. `lake build` green at **8795** jobs; `Gamma3Race` warning-free in
both modes; every headline in `Check.lean` is `[propext, Classical.choice, Quot.sound]`; the only
real `sorry` is still `Main.lean:66`.

### Addendum 69: a third defect — `StopEv` fired on the default letter at `j = |δ|`; and the repaired statement's numerics

Addendum 68 repaired two defects of `RaceSmall`; the repair was still false, for a third reason, found
by asking what `StopEv` means at the **last** index.  `StopEv P A' w δ j` read the letter `δ.getD j
false`, and at `j = δ.length` that is the default `false`.  So a node `w` whose `false` row-end lies
in `A'` and whose `true` row-end does not made the *empty word* a stop event: `GoodFirst` is false on
`[]` and the "no stop yet" alternative was defeated by the spurious event, so level `0` carried mass
`1` again.  `StopEv`'s exit clause now carries the guard `j < δ.length`
(`Huge ∨ (j < δ.length ∧ ExitArrow …)`), the only place it bites is `j = |δ|`, where exactly the
`Huge` clause is meant.  Machine-checked both ways: `good_nil` (the empty word is good now) and
`bad_nil_oldStopEv` (the refutation of the unguarded spelling).  Producers of `StopEv`
(`stopEv_of_stopW`, `stopEv_of_stopW_take`, the covering lemma) now supply the index bound; nothing
else changed.

**Independent numerics of the repaired statement.**  My own transcription of the Lean predicates
(`.scratch/orch/racesim.py`, exact rationals, dynamics reused from the member's `orbit.py` but the
description evaluated at the node *before* the letter, and with the `j < |δ|` guard) agrees with the
member's ledger to six digits where they overlap, and gives the good mass `1 − mass(Bad)`:

| configuration | good mass |
|---|---|
| `d = 3`, worst over all nodes up to length 7, all nonempty proper `A'` | `0.678818` |
| `d = 4`, worst over all nodes up to length 5, all nonempty proper `A'` | `0.434376` |
| `d = 4`, member's worst config `P = (0123 / 1302)`, `w = (t,t,t,f,f)`, `A' = {1,2,3}` | `0.434376` |
| `BlockedExtension`, `A' = {0,2,3}`, `w = u^m`, `m = 0, 4, 8` | `0.448447`, `0.436550`, `0.436011` |

Monte Carlo on larger `d` (`.scratch/orch/mcrace.py`, depth-checked to `L = 12000`) puts sampled
configurations at `0.39`–`0.45` for `d = 6, 7`, i.e. no sign of collapse, but the constant must be
expected to shrink with `d` — which is **allowed**: `RaceSmall P ν` lets `ν` depend on `P` (hence on
`d`), only not on `w`, `A'`, `N`.  A `1/d`-type constant is acceptable; a constant independent of `d`
is not needed.

**State**: `lake build` green at **8795** jobs, `Gamma3Race` warning-free in both modes, every headline
in `Check.lean` is `[propext, Classical.choice, Quot.sound]`, the only real `sorry` is `Main.lean:66`.
Swarm `smvxvnqbi` (three members, 600 min) runs on the repaired statement: one member on the exit-mass
route, one on a level-`0` refutation hunt (a wasted direction now that the guard is in — it will find
`good_nil`), one unregistered.

### Addendum 70: how much of the good mass is the exit branch alone

Addendum 68 said the exit arrow alone carries the good mass at the worst configurations.  That is true
*there* but not at every node: sweeping all nodes up to length 4 of `d = 4` and computing the two
families separately (exact rationals, same Lean semantics),

* min over all (node, nonempty proper `A'`) of the **clean-exit-alone** mass: `0.347766`, at
  `P = (0123 / 1302)`, `w = ()`, `A' = {0}`;
* min of the **full good** mass (`1 − mass Bad`): `0.437992`, at `w = (t,t,f,f)`, `A' = {1,2,3}`;
* `d = 3` up to length 5: `0.616667` exit-alone vs `0.686941` full.

So the crossing branch carries genuine mass (about `0.09` at that root configuration), the exit-only
statement is a strictly *stronger* target needing a smaller constant (numerically `ν ≈ 0.34`, not
`0.43`), and `RaceSmall` itself is the right thing to prove.  A member aiming at the exit family must
not carry the `0.43` constant over to it.

### Addendum 71: the good mass decays fast in `d` — the constant must be a function of `P`, and that is allowed

The full exact sweep of the repaired `RaceSmall` (`.scratch/orch/sweep_big.py`, every node to the given
length, every nonempty proper `A'`, depth `20·M + 400`, alive mass `0` at the cut):

| `d` | nodes to length | configurations | min good mass | worst configuration |
|---|---|---|---|---|
| 3 | 7 | 3060 | `0.678818` | `P = (012 / 120)`, `w = (f,f,f,f,t,f,t)`, `A' = {0,1}` |
| 4 | 6 | 10668 | `0.431471` | `P = (0123 / 1302)`, `w = (t,t,t,t,f,f)`, `A' = {1,2,3}` |
| 5 | 4 | 22320 | **`0.230569`** | `P = (01234 / 13042)`, `w = ()`, `A' = {1,2,3,4}` |

So the constant is *not* dimension independent — it roughly halves per dimension (`0.68, 0.43, 0.23`).
This is **not** a defect of the statement: `RaceSmall P ν` lets `ν` depend on `P`, hence on `d`, and
`BalanceTarget` only asks for a *function* `K : ℝ → ℝ` (`∃ K, (∀ Cb ≥ 1, 1 ≤ K Cb) ∧ BalanceStep P K`),
so a large `K₃ = 1 + 2/ν` costs nothing structurally: `statement_succ` iterates
`Cb ↦ 2·(K Cb)·Cb`, which needs `K` defined on all `Cb ≥ 1`, not bounded.  What it does kill is any
plan to prove a *uniform* `ν`: the proof must produce a `d`-dependent constant, and the decay suggests
something like `ν ≈ 2^{-d}` at the root with a single outsider.  A `d`-uniform `ν > 0` would be a
strictly stronger theorem and is not what the chain needs.

### Addendum 72: the good mass decays like `0.44^d` at the threshold `2d·M` — and the threshold factor is a FREE parameter of the interface

Exact sweep at the **root** (`w = ()`, all heights `1`, so `M = 1`, threshold `2d`), `A' = α ∖ {b}` a
single outsider, depth past the stopping length (alive mass `0`), `.scratch/orch/trend.py`:

| `d` | 5 | 6 | 7 |
|---|---|---|---|
| min over `P`, `b` of the good mass | `0.230569` | `0.103380` | `0.043638` |

(d = 8 sampled 8 permutations only: `0.133596`.)  The factor is `≈ 0.44` per dimension, so the best
constant at the campaign's threshold `2d·M(q_w)` is expected to be `≈ c·0.44^d`: positive for every
fixed `d`, but a proof would have to produce an exponentially small `ν`, and no dimension-uniform
constant exists.  **The statement is not refuted** — `ν` is allowed to depend on `P` — but this is what
makes the remaining estimate look hard.

**The observation that changes the difficulty**: the threshold factor is *not* part of the chain.
`BalanceStep P K` quantifies over an arbitrary `K : ℝ → ℝ`, `BalanceTarget` only asks for `∃ K`, and
`statement_succ` iterates `Cb ↦ 2·(K Cb)·Cb`; the threshold `2d·M` in `Gamma3Mass` enters the final
constant only through `Γ₄`'s doubling (`2·(threshold)`), i.e. as a factor `2Λ` in `K` when the
threshold is `Λ·M`.  So `Λ` may be chosen as large as one likes.  Exact/Monte-Carlo good masses at
`Λ·M`, same configurations (`.scratch/orch/mcrace.py`, depth `60·Λ·M/min`):

| configuration | `Λ = 2d` | `4d` | `10d` | `20d` | `100d` |
|---|---|---|---|---|---|
| `d = 4` worst node | `0.434` | `0.495` (`8`) | `0.701` (`16`) | `0.821` (`32`) | `0.920` (`80`) |
| `d = 5` worst (the root) | `0.231` | `0.452` (`20`) | `0.620` (`40`) | `0.787` (`100`) | — |
| `BlockedExtension`, `A' = {0,2,3}`, `u^8` | `0.436` | `0.510` | `0.701` | `0.826` | `0.913` |
| root, `|B| = 1`, worst over sampled `P` | — | — | — | `0.483` (`d=10`) | `0.942` (`d=10`) |

i.e. at `Λ = 100·d` the good mass is `≥ 0.9` **uniformly in `d`** (sampled `d ≤ 10`), against
`0.44^d` at `Λ = 2d`.  That is the difference between an exponentially small constant and `ν ≈ 1/2`.

**So the recommended interface change** (and the reason `Main.lean:66` is still open): replace the
fixed `2·#α·M(q_w)` of `Gamma3Mass` and of `RaceSmall` by a free `Λ·M(q_w)` with `Λ ≥ 2`, derive
`BalanceStep P (fun Cb => 2·Λ·Cb·K₃ Cb)` from it (the `Γ₄` argument is unchanged, verbatim, with `2d`
replaced by `Λ` and `4d` by `2Λ`), keep the old statements as the instance `Λ = 2·#α` — their
constants are *identical* (`2·(2d) = 4d`), so nothing downstream moves.  The last open statement then
becomes: for an explicit `Λ` (say `Λ = 100·#α`), the level-`N` words whose first stop is unclean at
threshold `Λ·M(q_w)` carry mass `≤ 1 - ν` with `ν = 1/2`.

### Addendum 73: `RaceSmall` is PROVED for two letters, with the optimal constant — `MasurVeech/RaceTwo.lean`

Swarm `smvxvnqbi` m1 (direction "smallest complete instance"), refereed and landed as
`MasurVeech/RaceTwo.lean`:

* **`Apriori.G2.raceSmall_two (P : CombData α 2) (hP : P.Admissible) : RaceSmall P (3/4)`** — the
  first *complete instance* of the campaign's last open statement (not of `BalanceTarget`, and not for
  a single `P`: the whole two-letter class), on the **repaired** statement (`Good` with the no-stop
  alternative, `StopEv` guarded, `A'` proper);
* `exists_raceSmall_two : ∃ ν, 0 < ν ∧ RaceSmall P ν`;
* **`cxP_sharp (h : 3/4 < ν) : ¬ RaceSmall cxP ν`** — the constant is *optimal* for two letters;
* `sum_bad_eq : ∑_{Bad} cond = st p / (st p + K·st (last !res))` with `K = ⌊(thr − st p)/st x⌋ + 1`:
  for `N ≥ K` the bad set is *exactly* the cylinder of the single word `(!res)^K`;
* `gamma3Mass_two : Gamma3Mass P (fun _ => 11/3)` and `masurVeech_of_race_two`, so the two-letter
  theorem also comes out of the *race* route (`K₃ = 1 + 2/(3/4) = 11/3`), independently of
  `TwoLetters.lean`'s `BalanceTarget` route.

Why it works: in the two-letter case `CombData` never changes along the tree (`Apriori.vertex_two`), so
the exit arrow is the same letter `res` at *every* node; a bad word must read `!res` at every step up
to its first stop; along `(!res)^k` the tracked height is `y + k·x` and the other stays `x`, and the
`cond` telescopes to `y/(y + kx)`.  So bad mass `≤ y/(y+Kx) ≤ y/thr = 1/(2d) = 1/4`, sharp as `x → 0`.

General lemmas landed with it (any `d`): `good_of_clean` (the endpoint `Clean` alone gives `Good`,
heights being non-decreasing), `bad_subset_crossing`, `bad_first_stop`, and
**`bad_cond_le : Bad → cond P w δ ≤ 1/(2·#α)`** — every individual bad word is light, which is the
natural seed for a counting argument on the minimal unclean family.

**Referee checks I ran** (not the member's): compiled with my own command in both modes, no warnings;
`#print axioms` on all eight headlines is `[propext, Classical.choice, Quot.sound]`; the file declares
no definition of `RaceSmall`/`Bad` (only `cK`), so the statement is the tree's; `hP : P.Admissible` is
the only hypothesis.

`d ≥ 3` remains open: there the exit letter moves along the tree, nothing telescopes, and the bad set
is fat (up to `0.57` in the `d = 4` worst configuration).

**State**: `lake build` green at **8797** jobs (89 modules), `RaceTwo` warning-free in both modes and
`≤ 100`-character lines, every headline in `Check.lean` is
`[propext, Classical.choice, Quot.sound]`, the only real `sorry` is `Main.lean:66`.  Also running:
swarm `smvxwxt5s` (one member) on the free-threshold generalisation of Addendum 72.

### Addendum 74: the free threshold is landed — `MasurVeech/GammaLambda.lean` (`Apriori.G4L`, `Apriori.G2L`)

Swarm `smvxwxt5s` m1, refereed and landed.  The whole `Γ₂`/`Γ₃`/`Γ₄` chain now carries the threshold
`L·M(q_w)` with `L ≥ 2` free:

* **`Apriori.G4L.Gamma3MassL P L K₃`**, `gamma4_absL` (threshold `L·R`, conclusion bound
  `2·L·κ·min`), `gamma4_wordsL`, **`balanceStep_of_gamma3L (hL : 2 ≤ L)`** with the constant
  `K Cb = 2·L·Cb·K₃ Cb`, `balanceTarget_of_gamma3L`, `masurVeech_of_gamma3L`;
* **`Apriori.G2L`**: `thrL = L·Mx`, and the `_L` copies of every threshold-dependent piece of
  `Gamma3Race.lean` (`HugeL`, `CleanL`, `ABoundL`, `StopEvL` — with the `j < δ.length` guard —,
  `GoodFirstL`, `GoodL` — with the no-stop alternative —, `BadL`, `StopWL`, `stopPredL`, `StopFamL`,
  `exists_stop_lengthL`, `prefixFree_stopFamL`, `exists_stopfam_of_goodL`), then
  **`gamma3Mass_of_raceL (hL : 1 < L) : RaceSmallL P L ν → Gamma3MassL P L (fun _ => 1 + 2/ν)`** and
  `masurVeech_of_raceL (hL : 2 ≤ L)`.

**The specialisations are definitional, which is the point**: `gamma3MassL_two_card` and
`gamma3MassL_of_two_card` are the bare identity `h`, `raceSmallL_two_card` is `⟨fun h => h, fun h => h⟩`,
and `balanceStep_of_gamma3L_two_card` gives exactly the landed `4·#α·Cb·K₃ Cb` (via `ring`, since
`2·(2·#α) = 4·#α`).  So nothing downstream moved: `Gamma3Mass`, `balanceStep_of_gamma3`, `RaceSmall`,
`gamma3Mass_of_race`, `masurVeech_of_race` are all still the live statements, and the campaign's last
input may now be stated at *any* `L ≥ 2`.

**Referee checks** (mine): compiled in both modes, zero warnings; 20 `#print axioms` headlines, none
containing `sorryAx`, all `[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`native_decide`/
`maxHeartbeats`; the `_L` definitions are faithful copies of the *repaired* tree versions (guard,
no-stop disjunct, proper `A'`) — which is what makes the `_two_card` specialisations definitional.

**Consequence**: the last open statement is now `∃ ν > 0, RaceSmallL P L ν` for an `L` of one's
choosing.  At `L = 100·#α` the exact/Monte-Carlo sweeps give a good mass `≥ 0.9` uniformly in `d`
(Addendum 72), against `0.44^d` at `L = 2·#α` — so `ν = 1/2` at `L = 100·#α` is the target, and
`gamma3Mass_of_raceL` turns it into `Gamma3MassL P (100·#α) (fun _ => 5)`.

**State**: `lake build` green at **8798** jobs; `GammaLambda` warning-free in both modes, lines
`≤ 100` characters (byte-length in `awk` overstates this: `·`, `Γ`, `₂` are two-byte); every headline
in `Check.lean` is `[propext, Classical.choice, Quot.sound]`; the only real `sorry` is `Main.lean:66`.
Running: `smvxvnqbi` m2/m3 (exit mass and atlas at `L = 2·#α`), `smvxxcy3o` m1 (Route B,
`StretchCost`), and the new `smvxxf1tl` m1 on `RaceSmallL` at `L = 100·#α`.

**Addendum 74, continued**: the `L = 100·#α` target is safe at large `d`. Monte Carlo (root node,
all heights `1`, single outsider, depth `6000`, 600 samples each) gives a good mass of `0.998`
(`d = 12`), `1.000` (`d = 16`), `0.997` (`d = 20`) at threshold `100·d·M`.  So at the free threshold the
constant does not decay with `d` at all (it was `0.44^d` at `2d·M`) — `ν = 1/2` at `L = 100·#α` has a
wide margin, which is the statement the campaign's last open input should now be stated at.

### Addendum 75: `Bad` is *exactly* "first crossing unclean, no exit read before" — the reduction, and the confirmation that the threshold must be freed

Swarm `smvxvnqbi` m2 submitted a reduction rather than the goal; I rejected the submission (the target
`∃ ν > 0, RaceSmall P ν` is not proved) and sent it back once with the pivot to the free threshold.  The
content, checked by me and worth keeping:

* **`bad_iff_crossUnclean`** and **`sum_bad_eq_sum_crossUnclean`**
  (`.ultramath/smvxvnqbi/m2/RaceReduce.lean`): `Bad` is *equivalent* — hence the level-`N` masses are
  *equal* — to `CrossUnclean` = "at the first index where some height crosses `thr`, some `A'`-height
  is already above `thr`, and no exit arrow was read before".  So `ExitArrow`, `StopEv`, `GoodFirst`
  and `Good` drop out of the target entirely; what remains is a statement about heights.
* `Unclean ↔ ¬Clean`, `Unclean → Huge`, hence `¬Huge → Clean`: **a first stop which is an exit arrow
  is always clean** (this had been left as a case split).
* **`raceSmall_of_exitMass`**: `RaceSmall P ν` from "for every `w`, proper `A'`, `N`, the mass of the
  words that read an exit arrow before the maximum crosses `thr` is `≥ ν`".  So the exit family alone
  suffices — the crossing branch is not needed.
* `cond_mul_st_le` (`cond P w δ * st (w++δ) b ≤ st P w b`, hence `cond ≤ 1/(2d)` at an unclean node),
  `cond_mul_st_eq_of_loser` (the telescoping identity when the tracked letter is the loser), and
  **`st_outsider_frozen`** (`A' = univ.erase c` ⇒ a non-exit letter never moves `st c`).

**Independent confirmation of Addendum 71-72**, from a second implementation (`ledger.py`, exact
rationals): worst configuration is the **root with a single outsider**, good mass `0.714` (`d = 3`),
`0.448` (`4`), `0.231` (`5`), `0.103` (`6`), `0.0062` (`9`) at threshold `2d·M` — agreeing with my
`0.230569` (`d = 5`) and `0.103380` (`d = 6`) to three digits, and decaying geometrically.  So no
`d`-independent `ν` exists at `2d·M`, and any proof there needs `ν ~ c^d`; deeper nodes are no worse.

**Consequence, acted on**: the reduction is at the old threshold, so it is *not* landed as is; m2's last
turn is to port it to the `_L` definitions of `GammaLambda.lean` and to attack `ExitMassL` at
`L = 100·#α` with `ν = 1/2`, where the good mass is `≥ 0.9` and does not decay in `d`.  The file stays
in its directory until then.

### Addendum 76: the reduction at the free threshold landed (`MasurVeech/RaceLambda.lean`), the sharpest form of the obstruction, and the conjectured constant

Swarm `smvxxf1tl` m1 delivered the `_L` port of Addendum 75's reduction instead of the goal; I rejected
the submission (the estimate is still open) and **landed the file** — it is the toolkit the last step
needs, and the precedent is `Gamma3Core.lean` (mass calculus landed while `Gamma3Mass` was open).

Landed, in `Apriori.G2L`: `exists_exitArrow_iffL`, `forall_not_exitArrow_iffL`, `exitArrow_uniqueL`,
`UncleanL`, `uncleanL_iff_not_cleanL`, `hugeL_of_uncleanL`, `cleanL_of_not_hugeL`, `cond_le_oneL`,
`cond_append_leL`, `cond_arrow_mul_st_leL`, `cond_mul_st_leL`, the product form
`cond_mul_prod_st_leL`, **`cond_le_of_uncleanL : cond ≤ 1/L`**, `cond_le_of_badL`, `exists_first_stopL`,
`goodL_of_exitArrow_before_huge`, **`badL_iff_crossUncleanL`** (BadL is purely about heights),
`sum_badL_le_one_sub_sum_exitL`, **`raceSmall_of_exitMassL`**, `st_outsider_frozenL`,
`uncleanL_of_hugeL_single_outsider`, `Mx_take_le_pow`, **`sum_badL_eq_zero_of_pow_le`** (no bad mass at
level `N` when `2^N ≤ L`).

**The obstruction in its sharpest form so far** (the member's negative results, all checked):
* counting crossing nodes cannot work — there are `≈ 0.03·L²` of them at a given depth;
* the per-word bound `cond ≤ 1/L` is *attained*: `bad = 1/(L+1)` for one configuration, so it cannot be
  improved per word;
* `BadMass ≤ AliveMass(⌈log₂ L⌉)` is true but void (`BlockedExtension u⁸`: `AliveMass(3) = 1` while
  `bad = 0.5`);
* **there is no increasing potential on the `A'`-max**: at a both-inside node both children have
  `max(H, p+q)` and the mass is preserved, so the maximum's growth is *letter-independent* along a
  non-straddling run while the mass splits.  This is the same frozen-heights phenomenon as Addendum
  60's `StretchCost` gap, now in the cleanest form: the proof must be mass-weighted over the branching,
  never a potential on the maximum.

**The conjectured constant** (the member's, and it is the right target): `mass(BadL) ≤ C·#α/L` uniformly
in `(w, A', N)` with `C` explicit, measured `bad·L ∈ [1, 6.7]` over the configurations tried, and my
independent sweeps fit `C ≤ 10`.  It gives `RaceSmallL P L (1 - C·#α/L)` for every `L > C·#α`, in
particular `ν = 1 - C/100` at `L = 100·#α`; that is the form the last member's turn is now aimed at.

**State**: `lake build` green at **8799** jobs; `RaceLambda` warning-free in both modes, `≤ 100`
characters per line; every headline in `Check.lean` is `[propext, Classical.choice, Quot.sound]`; the
only real `sorry` is `Main.lean:66`.

### Addendum 77: the campaign is stuck on an INTERFACE DEFECT, not on missing mathematics — the refuted length clause is not used

Prompted by the author ("the proofs are supposed to be in the papers — which steps are unclear?"), I
re-read `blueprint.md` Part I against the tree.  Findings:

* The source (Yoccoz's survey) has **one non-local gap, G1** (the last paragraph of §4.4, p. 20: it
  infers "infinitely many `n_k`" from Lemma 6, which is a one-simplex statement, and then applies
  Lemma 2 to a path of `λ` that need not follow the contracted extension), plus five local ones
  (G2–G6) and three proof slips (S1–S3).  G2–G6 and S1–S3 are all repaired and formalised in the
  tree; **G1 is the only one still open, and it is exactly where the campaign stands.**
* G1's repair (`blueprint.md` §10.5) is formalised abstractly: `NestedCylinder.nested_cylinder_tendsto`
  says any `CylTree` with `0 < c < 1` whose stopping process survives a.e. has a.e. `diam → 0`.  All
  the concrete ingredients are landed unconditionally: `lemma6Shape_unconditional` (uniform Lemma 6),
  `ExtData`/`extData` (Lemma 2's uniform extension), `CylTreeReal.carrier_fields` (root, nest, cover,
  disj, measurability, `μ(Δγ) = vol(cyl γ)`), and `CylTreeReal.diam_fam`/`fam_mass`/`fam_pair`/
  `fam_prefix`/`fam_long`.
* **The instantiation is blocked by a clause that is FALSE and UNUSED.**  `CylTreeReal`'s packaging
  `exists_cylTree_of_cover` requires `Provider`, which bundles `IsCover` *plus* a length bound
  `l.length ≤ γ.length + f (vertex P γ)` on the cover's members.  `CoverDataFalse.false_of_vertexBound`
  refutes that bound (two letters: on the `true`-ray the vertex is fixed, and `C`-balanced words of
  bounded length have bounded total volume, `sum_vol_le`).  But **no field of the tree uses it**:
  `diam_fam_child` derives the diameter contraction from `IsCover`'s balance clause plus Lemma 2 at
  each member, and the other `fam` fields likewise.  The bound occurs only in the *extra conclusion*
  `∃ L, …` of `exists_cylTree_of_cover`, i.e. in the statement, not in the proof.

**Decomposition written up** in `results/elementary-steps.md`: E1 (uniform Lemma 6) landed, E2
(antichain by pruning) mechanical, **E3** (the `CylTree` from `IsCover` alone, length clause deleted)
open and mechanical, **E4** (`hsurv` a.e. from `fam_mass` + `measure_diff_G`) open and elementary,
E5 (a.e. shrinking → `Main.lean:66`) landed.  So the whole remaining distance is E3 + E4, both inside
the abstract tree, **with no IET-specific mass estimate** — neither `RaceSmall` nor `StretchCost` is
on this path.

**Acted on**: swarm `smvxvnqbi` stopped (its work is landed as `RaceLambda.lean`/`RaceTwo.lean` and its
atlas is superseded by my own sweeps); new swarm `smvxym6ol` (two members: E3 and E4) started.
Route A (`smvxxf1tl`, one turn left on `bad ≤ C·#α/L`) and Route B (`smvxxcy3o`, `StretchCost` at
`K ≥ 2`) continue as hedges.

**State**: `lake build` green at 8799 jobs; the only real `sorry` is `Main.lean:66`.

### Addendum 78: two different workstreams — the main theorem's route is not (1)'s plan

The author's correction of my wording is right and the record should say it plainly.  There are **two
separate workstreams**, and "the Yoccoz route" names only one of them:

* **The main theorem (`Main.lean:66`).** Three live routes, none of which is (1):
  (a) the designed `Γ₂`/`Γ₃`/`Γ₄` chain `RaceSmall → Gamma3Mass → BalanceStep → BalanceTarget`
      (our own re-parameterisation of Kerckhoff, not a paper statement — this is what the sessions
      since the handover were pushing, and its last input's constant decays like `0.44^d` at the
      campaign's threshold);
  (b) Route B, Kerckhoff's Prop 1.5 / `StretchCost` (paper route; its reduction is stuck on frozen
      `S`-heights);
  (c) **Yoccoz's own route** through a.e. shrinking of the path cylinders (`hshrink`, `Final.lean`,
      `InjTower.masurVeech_of_shrink`), whose repair (blueprint §10.5) is landed abstractly and whose
      instantiation is blocked only by a refuted, *unused* length clause (Addendum 77).
      What I switched to in Addendum 77 is (c) — the main-theorem route — and nothing else.

* **Statement (1)** (`MVDesign.Statement1`, richness of the greedy path with the vertices pinned).
  Yoccoz's survey does **not** prove it.  Our devised proof is
  `.ultramath/smvxnf2ro/m3/PROOF.md` (531 lines, "Statement (1) … a self-contained proof"), which rests
  on **one hard input: Theorem A.1 = Appendix A of Avila–Gouëzel–Yoccoz, Theorem `simpleyoccoz`**
  (uniformly in the state `q` and the vertex, a definite `P_q`-probability of reaching a `C`-balanced
  later state, along the minimal prefix-free family).  Everything else in that proof is either landed
  in the tree (`RauzyReach` = strong connectivity, `BoundedLag` = Lemma 4.1, `AppendixA` = the AGY
  cylinder-mass phase 1, `cond` = Lemma 2.1's mass formula) or mechanical.  **Not formalised; phase 2
  of `AppendixA` (`simpleyoccoz`) is what (1) needs.**  The main theorem does not need (1)
  (`LetterRec.main_of_balancedDescendants`, `Final.lean`), but the author wants (1) for other
  applications.

  Also worth recording: PROOF.md §8 already states that a *bounded-length* descendant family with
  definite mass is impossible — the same fact as the machine-checked
  `CoverDataFalse.false_of_vertexBound`.  So (1)'s §7 replaces it by a Lévy lemma with unbounded
  depth, and (c)'s `CylTree` likewise needs no length bound.  The two are consistent; the refuted
  clause is the one place they *both* avoid.

**Acted on**: swarm `smvxxf1tl` (Route A's last turn) stopped to free the seat; new swarm
`smvxyux4z` (one member) on (1): state `simpleyoccoz` in the tree's vocabulary and formalise
PROOF.md's reduction to it, with a gap list.  Still running: `smvxym6ol` (E3/E4, the Yoccoz
main-theorem route) and `smvxxcy3o` (Route B, `StretchCost`).

**State**: `lake build` green at 8799 jobs; the only real `sorry` is `Main.lean:66`.

**Addendum 78, continued**: `CylTreeReal.not_prefix_of_disjoint` landed — **the antichain clause of
`IsCover` is free**.  Every path cylinder has positive volume (`PacketP9.volume_simplexCyl_pos`), and
`l <+: l'` gives `simplexCyl P l' ⊆ simplexCyl P l`, so disjoint cylinders cannot be nested.  Hence
`Lemma6Shape` (prefix, disjoint cylinders, mass, balance — landed unconditionally as
`CoverDataFalse.lemma6Shape_unconditional`) already gives **all four** clauses of `IsCover`: no
pruning and no length bound are needed for it.  `CylTreeReal` now imports `ChildVolume` for the volume
positivity.  This removes step E2 from `results/elementary-steps.md` altogether; E3 is now purely the
`Provider` re-packaging, and E4 the survival argument.

### Addendum 79: (1) is the only target; AGY's proof of `simpleyoccoz` is in the repository and is decomposed

Author's ruling, this round: **focus only on (1)** (`MVDesign.Statement1`); Main is deferred.  Stayed
running: nothing on Main — swarms `smvxym6ol` (E3/E4, the Yoccoz main-theorem route) and `smvxxcy3o`
(Route B, `StretchCost`) were stopped, their state recorded in Addenda 76–78, and both are resumable.
All capacity now goes to (1).

**The decomposition, and its source.**  The chain is

  `simpleyoccoz` (AGY Appendix A)  →  Lemma 5.1 + Lévy  →  `(1)`,

with the reduction from `simpleyoccoz` to (1) already written on paper by member m3 of `smvxnf2ro`
(`.ultramath/smvxnf2ro/m3/PROOF.md`).  **The AGY appendix itself is in the repository**:
`.scratch/avg/easyyoccoz.tex` (112 lines) with a transcription into our vocabulary in
`.scratch/avg/APPENDIX_A.md`.  Its proof is a finite induction with explicit constants — that is the
decomposition now being formalised (`results/statement-1-steps.md`, with every name):

* **Step 0**: `simpleyoccoz` only needs its *node-relative* form — `q = q_w = B_w·1` and the induction
  moves `q_w ↦ q_{wγ}`, which is again a node — and there `P_q = ∑ cond`, `𝔐 = Mk 1`,
  `𝔪 = Mk (#α)`, and crucial: **`𝔪_k` of the paper *is* the tree's `Mk k`**
  (`Mk k q = max_{#𝒜'=k} min_{α∈𝒜'} q_α`).  So the input is
  `SimpleYoccoz P := ∃ C > 1, ∀ w, ∃ Γ prefix-free, 1/C < ∑_{δ∈Γ} cond P w δ ∧ ∀ δ ∈ Γ,
   Mk 1 (st(wδ)) < C·min (Mk (#α) (st(wδ))) (Mk 1 (st w))` — no `ν_q`, no Lebesgue on cones.
* **S0** base `k = 1` (`Γ = {[]}`, `C = 2`); **S1** minimal families are prefix-free with the
  induction's mass; **S2** pigeonhole over the `k`-subsets `𝒜'`; **S3** the minimal extension to a row
  end outside `𝒜'` (max bound from `sum_cs_step_ge_of_both_inside`, *mass* form only — the
  deterministic form is machine-checked false, `BlockedExtension`); **S4** Kerckhoff
  (`AppendixA.kerckhoff`, landed); **S5** the `k → k+1` dichotomy with constants `4dC₀C₂`;
  **S6** assembly at `k = #α`.
* **Step 2**: `SimpleYoccoz → (1)` by PROOF.md §5–§7 (Lemma 5.1 + the Lévy lemma, candidate
  `LevyRecurrence.levy_recurrence`) plus the landed cylinder/path bridge (`CylinderRecurrence`).

**Landed already**: `cond` and the exact cylinder mass, `Mk`/`Mk_card_eq_mmin`, `AppendixA.kerckhoff`,
strong connectivity (`RauzyReach`), the both-inside growth lemmas, `BoundedLag`, the cylinder/path
bridge.  **Open**: the induction skeleton (S0–S2, S6), the extension step S3's mass form, the dichotomy
S5, and the §5–§7 assembly.

**Acted on**: new swarm `smvxz30fs`, three members, one per open piece (A: skeleton, B: S3, C: S4+S5);
`smvxyux4z` m1 stays on the `SimpleYoccoz` interface and the §5–§7 assembly.

### Addendum 80: piece A of (1) landed — `MasurVeech/Statement1Graded.lean` (AGY's graded induction)

Swarm `smvxz30fs` m3, refereed and landed.  **Piece A of `results/statement-1-steps.md` is closed**:
the skeleton of Appendix A's induction.

* **`Induction.Graded P k C`** — the paper's `(c+2)_k` at a single constant: at every node a
  prefix-free family `Γ` with `1/C < ∑_{δ∈Γ} cond` and
  `Mk 1 (st(wδ)) < C · min (Mk k (st(wδ))) (Mk 1 (st w))`.
* **`Induction.SimpleYoccoz P := ∃ C > 1, Graded P #α C`** — Theorem A.1 in the node-relative form
  (`Mk #α = mmin univ`, `simpleYoccoz_mmin`).
* **The identification that matters**: `graded_iff_statement : Graded P k C ↔ Apriori.Statement P k C C`.
  So `Apriori.lean` **is** AGY's induction already (`Statement` is the two-constant `(c+2)_k`), and
  `statement_succ` is its `k → k+1` step.  `Graded` is the same at `Cb = Cm = C`.
* S0 `graded_one` (`C = 2`, `Γ = {[]}`), S2 `graded_min` (pigeonhole: the paper's `Γ₁` with mass
  `1/(C·C(d,k))`), S1 `minimalElements_prefixFree` + `graded_of_cover`, S6 `graded_exists` /
  `simpleYoccoz_of_step` from `InductionStep`.
* **Cross-links** (new, and they change what (1) depends on):
  `inductionStep_of_balance : BalanceStep P K → InductionStep P`, hence
  `simpleYoccoz_of_balanceTarget : BalanceTarget P → SimpleYoccoz P` and
  `simpleYoccoz_of_gamma3 : Gamma3Mass P K₃ → SimpleYoccoz P`.  So the paper's a priori estimate
  follows from the campaign's `Γ₂`+`Γ₃` interface, and conversely the AGY induction is an independent
  route to it.  Neither direction closes anything on its own (`BalanceStep`/`Gamma3Mass` are the
  unproved inputs of the deferred Main route).
* The member's exact-rational correction: S1's "mass domination" is **false** without
  prefix-freeness of the compared family (`{[], [true]}` has mass `3/2 > 1`), and `graded_of_cover`
  carries exactly the needed hypotheses.

**Referee checks**: both compile modes clean, 21 axiom headlines all
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`axiom`/`native_decide`, lines `≤ 100`.
`lake build` green at **8800** jobs; `Check.lean` extended.

**Where (1) stands**: skeleton done; still open — S3 (the minimal extension to a row end outside `𝒜'`,
mass form; the deterministic form is machine-checked false, `BlockedExtension`), S5 (the `k → k+1`
dichotomy with `4dC₀C₂`), and the `§5–§7` assembly `SimpleYoccoz → Statement1`.

### Addendum 81: Kerckhoff's paper *does* prove (1) — as Corollary 1.9 (normality) — and it is NOT the simpler route

The author asked whether Kerckhoff's paper contains a proof of (1) and whether it would be simpler to
formalise than AGY Appendix A.  The paper is in the repository
(`attachments/you-are-orchestrator-eo7a/simplicial-systems-…pdf`, extracted to
`.scratch/orch/kerckhoff.txt`, 711 lines).  **Yes, it does**, and the chain is:

* **normality is (1)**, stated at l. 165–167: *"show that the sequences of symbols are normal, i.e.
  that any finite block which can occur, does occur infinitely often for almost every A ∈ Σ"* — a
  symbol includes the change of permutation, so the vertex is pinned;
* **Cor. 1.9** (l. 393–400): *"the sequence of symbols in the expansions of an irreducible interval
  exchange map are normal"*, proved by the geometric-series argument: in a `C`-distributed simplex a
  fixed block `B` occupies a proportion `μ` bounded below, so throwing out the `B`-sets leaves
  `(1-μ)^k → 0`; plus **Cor. 1.8** (columns `C`-distributed infinitely often a.e.), and
  **Cor. 1.7** (from any stage, `C`-distributed with probability `μ` before the max norm grows by
  `K''`), **Prop. 1.5** (the inductive step), **Prop. 1.4** (`no_isolated`) and **Lemma 1.6**
  (the jump bookkeeping).

**Why it is not the simpler route.**  Prop. 1.5 — the only hard input, l. 327–333 — is proved by
counting *jumps*, and the proof opens with

> *"Throughout we assume that each time a `v_i` jumps it has been added to some other column. By
> proposition 1.3 this occurs with probability greater than `μ_K`."*

That assumption is precisely where the printed argument does not close: on a step whose two row ends
both lie outside the tracked collection, every tracked height is **frozen** while the maximum grows,
so the jump count does not advance and Prop. 1.3 pays nothing.  **This is exactly the gap the campaign
already isolated as `StretchCost`** (Addendum 60, reduction in
`.ultramath/smvxs8wdx/m1/KerckhoffProp15.lean`): `Prop 1.5 ⟺ StretchCost` plus elementary steps, and
`StretchCost` was not proved.  So Kerckhoff's route to (1) runs into the same wall as Route B — one
that we have already hit once, with a printed proof on the other side that does not close.

By contrast AGY's `simpleyoccoz` — the hard input of the route we are on — has a **complete printed
proof in the repository** (`.scratch/avg/easyyoccoz.tex`, 112 lines), an explicit induction whose
skeleton and two of whose four pieces are already landed (`Statement1Graded.lean`), and whose
extension step is a *bounded-length* argument (`sum_cs_step_ge_of_both_inside`), not a frozen-heights
one.

**Verdict**: stay on AGY for (1).  Kerckhoff's Cor. 1.8–1.9 is worth keeping as a cross-check for the
last mile (`SimpleYoccoz → (1)`), since its geometric-series argument is more elementary than
PROOF.md §5–§7's Lemma 5.1 + Lévy — but it needs the *deadline* form (Cor. 1.7, "before the max grows
by `K''`"), which is stronger than `simpleyoccoz`, so it is not a shortcut unless that stronger form
is proved, and that is where `StretchCost` lives.

### Addendum 82: the last mile of (1) landed — `MasurVeech/Statement1Assembly.lean`; (1) is now `SimpleYoccoz` and nothing else

Swarm `smvxyux4z` m1, refereed and landed (submission accepted, swarm ended solved).

* **`S1.SimpleYoccoz P`** — Theorem A.1 of AGY Appendix A in the *minimal-family* form of PROOF §1.6:
  `∃ C > 1, ∀ w, ∃ S` prefix-free, all members `C`-balanced with max grown by `≤ C`, and
  `1/C < ∑_{δ∈S} cond P w δ`.  `simpleYoccoz_iff_statement` identifies it with
  `∃ C > 1, Apriori.Statement P #α C C` (so it is the `k = #α` instance of the graded induction landed
  in Addendum 80), and `simpleYoccoz_iff_later` with the paper's displayed "some later state"
  inequality.
* **`S1.statement1_of_simpleYoccoz : SimpleYoccoz P → MVDesign.Statement1 P`** — the conclusion is
  literally `MVDesign.Statement1` (vertex-pinned; `Design.lean` untouched, no letters-only weakening).
  So **PROOF.md §2–§7 is now formalised** and (1) has exactly one gap left.
* The two steps that needed real work: **`step_pinned`** (§5+§7 Step 1; the pin comes from composing
  the prescribed `u₀` into the pad cylinder, not from reproving `bounded_lag`) and **`levy_cylinder`**
  (§6: the Lévy recurrence for an *arbitrary level-measurable* target, with `GoodPin`/`ZpinLev`/
  `ZpinTgt` supplying measurability).  Recorded negative: `CylRec.cylinder_recurrence`'s **letters-only**
  target cannot give (1) — the vertex pin has to be carried through the recurrence.
* `S1.statement1_of_balanceTarget : BalanceTarget P → MVDesign.Statement1 P` — so the campaign's
  `Γ₂`–`Γ₄` input also yields (1), independently of AGY.
* Landing added the bridge **`S1.statement1_of_inductionStep : Induction.InductionStep P →
  MVDesign.Statement1 P`** (through the two `simpleYoccoz_iff_statement`s), so pieces B and C of
  `results/statement-1-steps.md` compose directly.

**Where (1) now stands**: the whole chain
`InductionStep (S3 + S5) → SimpleYoccoz → Statement1` is formalised except **pieces B (S3: the minimal
extension to a row end outside `𝒜'`, mass form) and C (S5: the `k → k+1` dichotomy with `4dC₀C₂`)**,
which are the current two members of swarm `smvxz30fs`.  Route B's Kerckhoff alternative for (1) was
assessed in Addendum 81 and rejected (same `StretchCost` hole).

**State**: `lake build` green at **8801** jobs; every headline in `Check.lean` is
`[propext, Classical.choice, Quot.sound]`; the only real `sorry` in the tree is still
`Main.lean:66` (deferred).

### Addendum 83: piece C of (1) landed — `MasurVeech/DichotomyG3.lean`; the source's "> 1/2" is now closed

Swarm `smvxz30fs` m2 (direction "piece C"), refereed and landed.

* **`Apriori.G3U.kerckhoff_union`** — Kerckhoff's lemma summed over a finite *set* of letters.  This
  is the step the source uses silently: `P_q(Γ₃ | γ_s) > 1/2` needs the bound simultaneously for every
  `α ∈ 𝒜'`, so it is a union bound over `#𝒜'` letters, not a single-letter estimate.
* **`mass_noWin_stretch`** — at threshold `Λ·Mk 1 (st w)`, families along which some `𝒜'`-coordinate
  exceeds the threshold *while never winning* carry mass `< #𝒜'/Λ`; hence
  `mass_noWin_stretch_lt_half` at `Λ = 2·#α` and `𝒜'` proper: `< 1/2`.  The `NoWin` clause cannot be
  dropped (`Gamma3Refuted.lean`), so this is the only form Kerckhoff supports and the source's `1/2`
  is exactly it.
* **`dichotomy`** — the paper's per-path `k → k+1` conclusion: from the `Γ₃` data at `w γ_s`, there
  are `γ₁` with `γ_s ≤ γ₁ ≤ γ_s γ_e` and `θ ∉ 𝒜'` with
  `Mk 1 (st(wγ₁)) ≤ 4·d·C₀·C₂ · min {mmin (𝒜' ∪ {θ}) (st(wγ₁)), Mk 1 (st w)}`; `𝒜'₁ = insert θ 𝒜'`
  is the `(k+1)`-subset.  Both cases of the source (max crossed `2d·Mk 1(st(wγ_s))`, or the last
  loser outside `𝒜'` and big) are closed with the one-step column-sum bounds already in the tree.
* **Bonus on the deferred Main route**: `raceSmall_card_one` — `RaceSmall`'s conclusion for
  `#A' = 1`, every `d`, node and level: bad mass `≤ 1/(2·#α)` (new for `d ≥ 3`; at `d = 2` it
  reproduces `RaceTwo`'s sharp `3/4`).  Recorded with it, from the member's report: the mechanism
  cannot generalise (`#A' ≥ 2`: an internal arrow `b₁ → b₂` lets a letter win without exiting) and no
  potential argument on the `A'`-max can work, the arrow masses summing to `1` at every node.

**Where (1) stands**: `InductionStep → SimpleYoccoz → Statement1` is formalised
(`Statement1Assembly.S1.statement1_of_inductionStep`); of `InductionStep`'s ingredients, A (skeleton),
C (dichotomy + `Γ₃` mass) are landed and **B (S3, the minimal extension to a row end outside `𝒜'`, in
its mass form) is the only open one**, still being worked on (`smvxz30fs` m1).  A new member
(`smvxzuw2v` m1) assembles `InductionStep` from A + C with B as an explicit hypothesis, so that (1)
will rest on S3 alone.

**State**: `lake build` green at **8802** jobs; every headline in `Check.lean` is
`[propext, Classical.choice, Quot.sound]`; the only real `sorry` in the tree is `Main.lean:66`
(deferred).

### Addendum 84: the assembly landed (`MasurVeech/AssemblyPieces.lean`) — (1) rests on two named pieces, and AGY's `Γ₃` step is the third printed argument with the same hole

Swarm `smvxzuw2v` m1, refereed and landed.  Statement (1) now reads:

  `ExtMass` (piece B, S3)  +  `G3Straddle` (the `Γ₃` mass `> 1/2`)  ⟹  `MVDesign.Statement1`

* **`Induction.ExtMass P C₂`** — piece B in the form the assembly consumes: at a node `w` with a
  balanced nonempty proper `A'`, a prefix-free family of mass `> 1/C₂`, each member ending with a row
  end outside `A'` and with `Mk 1 (st(wη)) ≤ C₂·Mk 1 (st w)`.
* **`Induction.G3Straddle P`** — at a node `w` with a row end outside a balanced proper `A'`, the
  clean-exit-stop family has mass `> 1/2`, each member `ν ++ [e]` an exit arrow or a crossing at
  `2·#α·𝔐(q_w)`, with the `A'`-heights bounded by `2·#α·𝔐(q_w)` — the shape
  `Apriori.G4.gamma4_abs` consumes.
* **`balanceStep_of_ext`** with `K Cb = 4·d·C₂²·Cb + 2·C₂ + 1`, then `inductionStep_of_ext`,
  `statement1_of_pieces`, `statement1_of_blocked` (only blocked nodes needed), and the sharpening
  `inductionStep_of_ext_of_cards`: **both `#A' = 1` cases are proved** (`extMassCard_one`,
  `g3StraddleCard_one` through the landed `raceSmall_card_one`), so the residue is `#A' ≥ 2`.

**The finding that matters (about the source, not about the proof).**  `G3Straddle` is *not* derivable
from Kerckhoff for `#A' ≥ 2`, and the member says exactly why: a `A'`-height can cross the threshold
*after* an `A'`-letter has already won, which `AppendixA.NoWin` never sees; the residue "no `A'`-win,
no crossing" is not a Kerckhoff family (mass `0.436` at the `BlockedExtension` configuration).
Kerckhoff in covering form (`mass_crossing_noWin_lt_half`) and the first-win decomposition
(`exists_noWin_crossing_of_first`: a first `A'`-crossing before any `A'`-win has a letter that never
wins — including immediately after the first win, where it is the loser) are both proved here, and they
are exactly the part of the source's `Γ₃` claim that *is* available.  So the printed
`"By Lemma [Kerckhoff], P_q(Γ₃|γ_s) > 1/2"` in `easyyoccoz.tex` is not supported by that lemma alone,
and `g3Straddle_of_raceSmall` shows the residue lies in the `RaceSmall` family.

**Consequence for the campaign.**  (1) and Main now visibly share their crux: `G3Straddle` for
`#A' ≥ 2` is a bound on the same exit-stop family that `RaceSmall` bounds (one direction is proved:
`RaceSmall (ν > 1/2) → G3Straddle`).  Three printed arguments now have their hole in the same place —
Yoccoz §4.4's last paragraph (G1), Kerckhoff's Prop 1.5 (`StretchCost`), and AGY's `Γ₃` step
(`G3Straddle`) — and all three holes are a mass bound for the family that reaches a clean exit.

**Where (1) stands**: `InductionStep`-free assembly done; open are
(i) **piece B / `ExtMass`** — `smvxz30fs` m1, in flight; (ii) **`G3Straddle` for `#A' ≥ 2`**, and the
campaign has no fourth route to it.

**State**: `lake build` green at **8803** jobs; every headline in `Check.lean` is
`[propext, Classical.choice, Quot.sound]`; the only real `sorry` in the tree is `Main.lean:66`
(deferred).

### Addendum 85: piece B landed (`MasurVeech/ExtensionG2.lean`) — and it refutes the assembly's `ExtMass`

Swarm `smvxz30fs` m1 (piece B = the source's Γ₂), refereed and landed.

**Proved unconditionally**:
* `exists_exit` / `exists_minimal_exit` — an exit word exists at *every* node; the minimal one exists
  and all its proper prefixes are `Blocked` (`pairReach_all` even prescribes both row ends, which is
  stronger than the source needs);
* **`exists_minimal_exit_bound`** — the paper's `Mk 1`-bound is TRUE, with an explicit
  `C₂ = 2^L + 1` where `L` is the diagram's diameter (`exists_path_between` + `Mk_one_le_two_pow`).
  Notably **not** from `A'`-sum growth: `blocked_growth_unbounded` and `length_le_of_blocked_prefix`
  rule that route out;
* **`gamma2In : Gamma2In P (fun _ => 2)`** — the tree's Γ₂ with mass constant `2` for every `Cb ≥ 1`,
  via all words of a long length; **the stop costs no mass**, so the paper's Γ₂–Γ₃ loses nothing there;
* `gamma3Mass_of_gamma3In` and `gamma3Mass_of_uncleanMassBd` (lossless: `UncleanMassBd P K →
  Gamma3Mass P K`).

**The refutation that forces a repair**: the source's `P_q(Γ₂ | π) > C₂^{-1}` **with a constant is
FALSE** — exact rationals give mass `~ 1/Cb²` (the member's `t8.py`).  The sharp form
`Gamma2MassBd P K` (`1/(K·Cb²)`) is stated and unproved.

**Repair needed, and started**: `MasurVeech/AssemblyPieces.lean`'s `Induction.ExtMass` carries a
*constant* mass bound and is therefore false as stated; the assembly must be redone with the mass
constant `1/(K·Cb²)`.  Since `Apriori.BalanceStep`/`BalanceTarget` take an arbitrary `K : ℝ → ℝ`,
this only changes the constant chase, not the structure.  Swarm `smvy175p5` (one member) is on it:
`ExtMassCb P K` + `G3Straddle P → BalanceStep P (K' ·)` → `statement1_of_piecesCb`.

**Where (1) stands** after this: the chain is
`ExtMassCb (mass ~ 1/(K·Cb²))` + `G3Straddle (#A' ≥ 2)` → `BalanceStep` → `SimpleYoccoz` →
`MVDesign.Statement1`, with `#A' = 1` of both pieces proved and the `Mk 1`/existence parts of Γ₂
unconditional.  The two residues are the same family — the clean-exit / crossing mass — which is also
what `RaceSmall` (Main) and `StretchCost` (Route B) bound.

**State**: `lake build` green at **8804** jobs; all `Check.lean` headlines
`[propext, Classical.choice, Quot.sound]`; the only real `sorry` is `Main.lean:66` (deferred).

### Addendum 86: the author's correction — Kerckhoff DOES bound the crossing part of `Γ₃`; my Addendum 84 statement was wrong on that point

The author's observation, checked in Lean's own vocabulary and confirmed: **the last step of a
first-`𝒜'`-win path does not change the winning coordinate** — `AppendixA.cs_append_singleton` gives
`cs P (w++[e]) b = cs P w b` when `b = (P.vertex w).last e` (winner), the winner and loser being
distinct — so the `Γ₃` condition on the winning letter `α₀` is *already* a condition on the prefix `η`,
and `η` satisfies `NoWin(α₀)` because `α₀` wins only at the last arrow.

Hence, splitting the union bound by the winning letter:

* for `α₀` (the last winner): Kerckhoff applies to the **prefix** family `{η}`, which is prefix-free,
  and the passage to `η ++ [e]` costs nothing (`cond_append_le`, the last arrow has probability ≤ 1);
* for every other `α ∈ 𝒜'`: the whole path satisfies `NoWin(α)`, so Kerckhoff applies directly.

So the mass of the part of the first-`𝒜'`-win family on which some `𝒜'`-coordinate exceeds `2d·M` is
`< #𝒜'/(2d) ≤ (#α−1)/(2d)`.  **Addendum 84 said `G3Straddle` "is not derivable from Kerckhoff for
`#A' ≥ 2`"; that was wrong**, and the member's diagnosis (that a crossing after an `𝒜'`-win is
invisible to `NoWin`) does not apply to `Γ₃`, whose paths have no earlier `𝒜'`-win.

What survives, and is now precise: with `F` the first-`𝒜'`-win family from `γ_s`,
`mass(Γ₃) ≥ mass(F) − #𝒜'/(2d)`, so `P_q(Γ₃|γ_s) > 1/2` needs `mass(F) > 1/2 + #𝒜'/(2d)`.  Splitting
`F`'s complement by the `Γ₄` dichotomy, the only part that neither Kerckhoff nor the crossing branch of
`Γ₄` absorbs is

  **`Residue`**: the continuations that never win in `𝒜'` and along which every height stays
  `≤ 2d·M(q_w)` — a *boundedness* estimate, i.e. the same shape as `StretchCost`.

So the author's correction strictly improves the picture: `Γ₃` is no longer "unsupported"; it follows
from one boundedness statement about the no-win bounded family.  Swarm `smvy1pfio` (one member) is
formalising the correction (`firstwin_crossing_mass`, `gamma3_mass_of_bounded`) and measuring the
residue on exact rationals at the worst configurations — if that sup is `< 1/2`, the `Γ₃` step is
provable after all.

**State**: `lake build` green at **8804** jobs; the only real `sorry` is `Main.lean:66` (deferred).
Running: `smvy175p5` (assembly repair, `ExtMassCb`), `smvy1pfio` (the author's lemma + residue numerics).

### Addendum 87: the exact location of the gap in Kerckhoff's paper

For the record, with page and line references (paper: *Simplicial systems for interval exchange maps and
measured foliations*, ETDS 5 (1985) 257–271; extracted text `.scratch/orch/kerckhoff.txt`):

* **Prop. 1.5**, p. 263, txt l. 326–330: *"Suppose the collection of columns v₁,…,v_k is
  C-distributed. Then with probability μ' > 0, one of the v_i's will be added to a column outside the
  collection **before the maximum of |v| increases by a factor of K**."*
* **The definition of the measuring device**, p. 263, l. 331–334: *"Call each time the norm of a column
  v_i **in the collection** increases by a factor of K' a jump."*
* **The conversion**, p. 264, l. 338–340 and 347–348: *"Throughout we assume that each time a v_i jumps
  it has been added to some other column. By proposition 1.3 this occurs with probability greater than
  μ_K'."* … *"letting **K = (K')^N**, μ' = μ_K', we will be done."*

**The gap.** The deadline of the proposition is the growth of the **maximum over all columns**, but the
proof measures time in *jumps*, which count only increases of **collection** columns. The step
`K = (K')^N` presumes that after N jumps the maximum has grown by at most `(K')^N`, i.e. that the
maximum can only grow when a collection column jumps. That is false: on a step whose winner **and**
loser both lie outside the collection, every collection column is frozen — no jump and no `v_i`–`w_j`
addition — while an outside column grows and the maximum grows. The deadline can therefore pass with
**zero** jumps, and the "bounded number N of jumps" gives no bound on the maximum at all.  The clause
the paper supports with Prop. 1.3 ("jumps are paid for") is true and is not the issue; what is missing
is that nothing else may happen in between.

Concrete witness (checked; in the tree as `KerckhoffJumps.cs_step_eq_of_both_outside` and Addendum 60):
`n = 4`, `top = (0,1,2,3)`, `bottom = (1,2,3,0)`, collection `S = {1,2}` — the `true` arrow fixes the
vertex and both row ends lie outside `S`, so `true^N` has no jump at all while the maximum grows.

**Second, independent gap in the same proof**, p. 264, l. 350–353: *"…only a finite number of such
blocks can be strung together before encompassing one beginning and ending with the same permutation. By
proposition 1.4 this is impossible…"* — Prop. 1.4 (p. 262, l. 289–291) applies only to a block
*"starting and ending with the same permutation"*, and the isolated sub-collection produced inside an
arbitrary finite block need not be isolated inside a returning one.  In the tree this is
`KerckhoffBlock.no_isolated`, whose returning-block hypothesis is explicit.

**Repair, and where it lives**: `.ultramath/smvxs8wdx/m1/KerckhoffProp15.lean` reduces Prop. 1.5 to the
single estimate `StretchCost` — uniformly in the node, the breakout-free continuations along which every
height stays below `K·max(w)` carry mass `≤ 1 - ν` — and `MasurVeech/KerckhoffJumps.lean` has the
freezing lemma, the repaired Lemma 1.6 and `not_all_stretched_of_returning`.  The *statement* of
Prop. 1.5 is not refuted; only its printed proof fails.

### Addendum 88: the author's correction is landed (`MasurVeech/FirstWinG3.lean`) — and the residue is *not* boundedness

Swarm `smvy1pfio` m1, refereed and landed.  The correction of Addendum 86 is now a theorem:

* **`st_eq_winner`** — the winning step leaves the winner's coordinate unchanged (the crux, from
  `cs_append_singleton` plus winner ≠ loser);
* **`firstwin_noWin_prefix`** — along a first-`𝒜'`-win word the prefix satisfies `NoWin` for the letter
  that wins last;
* **`firstwin_crossing_mass`** — for a prefix-free family `F` of first-`𝒜'`-wins,
  `∑_{γ ∈ F, ∃ b ∈ 𝒜', thr < st(w++γ) b} cond P w γ < #𝒜'/(2d)`.
  **Two corrections to my sketch, both needed**: the naive two-case union bound gives only `#𝒜'/d`;
  the sharp `#𝒜'/(2d)` needs the *minimal `b`-crossing prefix per letter `b`*
  (`crossIdx_spec`, `noWin_take_crossIdx`, `prefixFree_image_crossIdx`), and `{dropLast}` is *not*
  prefix-free, so the passage from prefixes to words must go through that per-letter map;
* `gamma3_mass_of_bounded`, `firstwin_bounded_gt_half`, `firstwin_clean_of_straddle`, and
  **`g3Straddle_of_firstWinResidue`**: `FirstWinResidue` (first-`𝒜'`-win mass `> 1/2 + #𝒜'/(2d)`)
  implies `Induction.G3Straddle` with no further loss.

**The negative result, which settles the follow-up question.**  The residue is **not** a boundedness
estimate: chasing the arithmetic on the "never win in `𝒜'` and every height `≤ 2d·M`" family forces
the contradictory `NW_bounded < 1/2 - #𝒜'/d < 0`.  What remains is an **unbounded-length** statement —
"how soon does a tracked letter become a row end" — and, as the member notes, the `BlockedExtension`
node is *not* straddling, so it was never the right witness for this residue (its `0.436` was measured
for exit arrows, a different object).  The exact numbers (816 configurations at `d = 3,4,5`, all proper
`𝒜'`, nodes to length 5) have `FW = FWB` throughout, and the deeper values (`NW₁₆ = 0.12698` at `d = 3`,
`NW₁₅ = 0.35206` at `d = 4`, `NW₁₂ = 0.81140` at `d = 5`) are *lower* bounds on the first-win mass, so
they do **not** decide whether it exceeds `1/2 + #𝒜'/(2d)`.  That inequality is now the precise open
question for the `Γ₃` step, and hence for (1).

**State**: `lake build` green at **8805** jobs; every headline in `Check.lean` is
`[propext, Classical.choice, Quot.sound]`; the only real `sorry` is `Main.lean:66` (deferred).
Running: `smvy175p5` m1 (the assembly repair, `ExtMassCb` with the `1/(K·Cb²)` mass).

### Addendum 89: state of the `easyyoccoz` work (AGY Appendix A → statement (1))

Author's request for a status report; recorded so it can be resumed from here.

**The chain, and what is landed.**  `simpleyoccoz → MVDesign.Statement1` is fully formalised
(`MasurVeech/Statement1Assembly.lean`: `statement1_of_simpleYoccoz`, `step_pinned`, `levy_cylinder`,
`simpleYoccoz_iff_statement`, `simpleYoccoz_iff_later`).  Of the appendix's own four `Γ`-steps:

| step of `easyyoccoz.tex` | status |
|---|---|
| base case `k = 1`; `Γ₁` (minimal family, prefix-free; pigeonhole over the `k`-subsets `𝒜'`); the `k`-induction assembly | **landed**, `MasurVeech/Statement1Graded.lean` (`graded_one`, `graded_of_cover`, `graded_min`, `graded_exists`, `simpleYoccoz_of_step`, and `graded_iff_statement : Graded P k C ↔ Apriori.Statement P k C C`) |
| `Γ₂`: extension to a node with a row end outside `𝒜'` | **existence and the `Mk 1`-bound landed** (`MasurVeech/ExtensionG2.lean`: `exists_minimal_exit`, `exists_minimal_exit_bound` with the explicit `C₂ = 2^L + 1`); **the mass with a constant is FALSE** (exact rationals, `~1/Cb²`); the sharp `1/(K·Cb²)` form (`Gamma2MassBd`) is open.  Note: the tree's own `Γ₂` (stop = exit arrow *or* crossing, mass `> 1/2`) is **free** — `gamma2In : Gamma2In P (fun _ => 2)`, unconditional |
| `Γ₃`: `P_q(Γ₃|γ_s) > 1/2` "by Kerckhoff" | **crossing part landed** by the author's correction (`MasurVeech/FirstWinG3.lean`: `st_eq_winner`, `firstwin_noWin_prefix`, `firstwin_crossing_mass` `< #𝒜'/(2d)`, `g3Straddle_of_firstWinResidue`); what the arithmetic still needs is the **first-win mass `> 1/2 + #𝒜'/(2d)`** — open, numerics inconclusive so far |
| `Γ₄`: the per-path `k → k+1` dichotomy | **landed** (`MasurVeech/DichotomyG3.lean`: `dichotomy`, constant `4·d·C₀·C₂`, plus `kerckhoff_union` and `mass_noWin_stretch_lt_half`, which close the source's silent union bound) |

**The assembly between them** (`MasurVeech/AssemblyPieces.lean`) is landed too: `ExtMass + G3Straddle →
balanceStep_of_ext → inductionStep_of_ext → statement1_of_pieces`, with both `#A' = 1` cases proved.

**So (1) rests on exactly two mass statements**, and each is named in the tree:
* **`Induction.G3Straddle` for `#𝒜' ≥ 2`** — its first-win reformulation is the inequality now being
  tested (`smvy2l7ya`): *for every node with a row end outside `𝒜'`, the first-`𝒜'`-win family has mass
  `> 1/2 + #𝒜'/(2d)`*.  If it holds, `Γ₃` follows from the author's argument; if it fails, `Γ₃`'s
  `> 1/2` is false as printed and the induction step needs another shape.
* **the repaired `Γ₂` mass** — `ExtMassCb` with `1/(K·Cb²)` (`smvy175p5`).  Possibly avoidable: since
  `gamma2In` is free and its members end with an exit arrow *or* a crossing, and `Γ₄`'s crossing branch
  fires on a crossing, the assembly may be re-runnable with `gamma2In` + `G3Straddle` and no `ExtMass`
  at all.  That is the next structural question.

**State**: `lake build` green at **8805** jobs; all `Check.lean` headlines
`[propext, Classical.choice, Quot.sound]`; the only real `sorry` is `Main.lean:66` (deferred).

### Addendum 90: the repaired assembly landed (`MasurVeech/AssemblyRepair.lean`); (1) is now `∃ K, ExtMassCb P K` + `G3StraddleCard P k` (`k ≥ 2`)

Swarm `smvy175p5` m1, refereed and landed.  The false `Induction.ExtMass` (constant mass bound for `Γ₂`)
is replaced by the parametric form, and the old interface is recovered as a specialisation:

* **`ExtMassGen P M C₂`** — piece B with an arbitrary mass function `M : ℝ → ℝ` (`1/(M Cb) < ∑ cond`);
  `ExtMassCb P K` is `0 < K ∧ ∃ C₂ > 1` of it at `M Cb = K·Cb²`; `ExtMass` is the constant case.
* **`balanceStep_of_extMassGen`**: `ExtMassGen P M C₂ → G3Straddle P → BalanceStep P (KeeGen M C₂)` with
  `KeeGen M C₂ Cb = 4·#α·C₂²·Cb + (2·M Cb + 1)`; at `M Cb = K·Cb²` this is
  `K' Cb = 4·#α·C₂²·Cb + (2·K·Cb² + 1)`.  `balanceStep_of_ext_via_gen` recovers the landed `Kee`
  exactly, so nothing earlier moved.
* **`statement1_of_piecesCb : ExtMassCb P K → G3Straddle P → MVDesign.Statement1 P`** and
  **`statement1_of_gaps : (∃ K, ExtMassCb P K) → (∀ k ≥ 2, G3StraddleCard P k) → Statement1 P`**.

**Closed in passing**: `#A' = 0, 1`, the exit-node case (content only at blocked nodes), and
`#α = 2 ⇒ Statement1` (an independent confirmation of the two-letter results).  **Refuted**: 
`MinimalExitLenBd` for *every* `L` at `BlockedExtension` — so the gap is genuinely the *family* form
(`ExtMassBdLen`), not a single minimal exit word.  Exact rationals: `min mass·Cb² = 1/6` over all
irreducible data with `d ≤ 4`, i.e. the numerical candidate **`K = 7`**.

**So statement (1) now rests on exactly two statements**, both in the tree with their constants visible:

1. `∃ K, ExtMassCb P K` — the `Γ₂` family mass `> 1/(K·Cb²)`, numerically `K = 7`;
2. `G3StraddleCard P k` for `k ≥ 2` — the `Γ₃` mass, equivalently (Addendum 88) the first-`𝒜'`-win
   mass `> 1/2 + #𝒜'/(2d)`, being tested by `smvy2l7ya`.

**State**: `lake build` green at **8806** jobs; every headline in `Check.lean` is
`[propext, Classical.choice, Quot.sound]`; the only real `sorry` is `Main.lean:66` (deferred).
Running: `smvy2l7ya` m1 (the first-win inequality).

### Addendum 91: the two remaining mass statements split into three easier slices, one member each

Author's instruction: if the remaining tasks are mathematically hard, split them and staff the pieces.
Done — the two gaps of Addendum 90 are:

* **Γ₂ mass** `∃ K, ExtMassCb P K` (exit family, mass `> 1/(K·Cb²)`, candidate `K = 7`);
* **Γ₃ mass** `∀ k ≥ 2, G3StraddleCard P k` (clean-exit family mass `> 1/2`, equivalently first-`𝒜'`-win
  mass `> 1/2 + k/(2d)`).

Swarm `smvy388if`, three members, one slice each:

1. **A single outsider** (`#𝒜' = d-1`): the worst family numerically everywhere in the campaign and the
   simplest combinatorially — at a straddling node exactly one letter is an exit arrow; at a blocked
   node the outsider's height is frozen (`st_outsider_frozen`, `not_straddle_of_blocked`).  Both masses
   in this case.
2. **The balanced case `Cb = 1`**: all `𝒜'`-heights equal to `Mk 1 (st P w)`, so every one-step ratio is
   `1` or `h_outsider/(h_outsider + M)` with `h_outsider ≥ 1`; this isolates the combinatorics from the
   balance constant, and should be the easiest honest mass computation available.
3. **The engine**: blocked phases (both row ends in `𝒜'`) are short (`length_le_of_both_inside`) and
   their mass is a product of one-step ratios with the winner an `𝒜'`-end of height `≥ M/Cb`; the
   member is to bound the survival mass and say exactly where uniformity in the configuration fails.

Each brief carries the standing numerics rule: no inequality about `∑ cond` may be stated before it is
evaluated on exact rationals, and a machine-checked refutation of a slice hypothesis is a first-class
outcome.  Still running: `smvy2l7ya` m1 (the first-win inequality of `Γ₃`).

**Addendum 91, continued**: my own exact computation of the decisive inequality, at the root node with a
single outsider (the worst family of the campaign), `.scratch/orch/firstwin.py`:

| `d` | `FW` (first-`𝒜'`-win mass) | `FWC` (with `𝒜'`-heights `≤ 2d·M`) | needed `> 1/2 + (d-1)/(2d)` | slack |
|---|---|---|---|---|
| 3 | `1.000000` (worst outsider `0.999750`) | `0.857143` (worst) | `0.8333` | `+0.0238` |
| 4 | `1.000000` (worst `0.999750`) | `0.888889` (worst) | `0.8750` | `+0.0139` |
| 5 | `1.000000` | `1.000000` | `0.9000` | `+0.1000` |
| 6 | `1.000000` | `1.000000` | `0.9167` | `+0.0833` |

So the inequality that `Γ₃` needs **holds with a positive margin** at these configurations, and the
truncation is harmless (`NW ≤ 2.5·10⁻⁴` at the tight ones).  The margin shrinks towards `d = 3, 4`
(`1/72` at the tightest), which is exactly where a proof will have the least room.  A full sweep over
all irreducible data (`d = 3`, nodes to length 4; `d = 4`, nodes to length 3; every proper `𝒜'`) is
running to find the true worst slack — if it stays positive, `Γ₃`'s `> 1/2` is numerically settled and
the slice members' job is the proof, not the constant.

### Addendum 92: the constants `C₁` and the *height* `C₂` are already precise statements; the *mass* `C₂` is a different object

The author asked whether we have precise statements for (i) `C₁ = C₀·#𝒜'`-subsets and (ii) `C₂` obtained
by fixing finitely many paths between vertices and taking the maximal size of their matrices.

* **(i) landed, exactly.**  `Induction.graded_min` (`MasurVeech/Statement1Graded.lean`):
  `Graded P k C → Apriori.StatementMin P k C (C * (univ.powersetCard k).card)`, i.e. the balance constant
  becomes `C · C(d,k)` — the number of `k`-subsets of the alphabet — and it is `Apriori.statement_min`
  (the pigeonhole over `𝒜'`).
* **(ii) landed, and it is precisely that recipe.**  `RauzyReach.exists_path_between` fixes, for each pair
  of vertices of the Rauzy class, one path, and bounds their lengths by a single `L` (the diameter of the
  diagram); `CombData.pairReach_all` even reaches vertices with prescribed winners.  Then
  `Apriori.Extension.exists_exit_length_bound : ∃ L, ∀ w, ∃ u, |u| ≤ L ∧ Exit P (w++u) A'`, and
  **`Apriori.Extension.exists_minimal_exit_bound : ∃ C₂ > 1, ∀ w, ∃ u, Exit P (w++u) A' ∧
  (all proper prefixes Blocked) ∧ Mk 1 (st P (w++u)) < C₂ · Mk 1 (st P w)`**, with the *explicit*
  `C₂ = 2^L + 1` from `Mk_one_le_two_pow` (`Mk 1 (st(w++u)) ≤ 2^{|u|}·Mk 1 (st w)`).  The crude
  `2^{|u|}` can be replaced by the maximal matrix size along the fixed paths — a cosmetic sharpening,
  the statement is the same.
* **What (ii) does not give: the mass constant.**  `cond P w η = ∏_b cs(w,b)/cs(w++η,b)`, so with the
  balance hypothesis and the height bound above, a *single* word satisfies
  `cond ≥ (Cb·C₂)^{-#𝒜'}·(C₂·𝔐(q_w))^{-#(α∖𝒜')}`, and `𝔐(q_w)` is unbounded — so no bound in `Cb` alone
  follows per word.  The exit family's mass is a *sum over many words* and is large for dynamical
  reasons (many branches reach the exit), not ratio reasons.  Consistently, the machine-checked
  refutation in Addendum 85 shows the paper's constant `C₂` **cannot** serve the mass claim
  (`mass ~ 1/Cb²`), which is why the mass is a separate statement (`ExtMass`/`ExtMassCb`, now
  `ExtMassGen` with an arbitrary `M : ℝ → ℝ` — the form that accepts `M Cb = K·Cb^d` if a proof gives
  it).  So the paper's `C₂` plays two roles and only the height role is combinatorial.

**Addendum 92, continued**: the author's suggestion to use **two constants — one for the height, one
for the mass** — is already the shape of the formalisation, and it is what makes the remaining gap
one-parameter:

```lean
def Induction.ExtMassGen (P : CombData α n) (M : ℝ → ℝ) (C2 : ℝ) : Prop :=
  ∀ Cb ≥ 1, ∀ k A' w, A'.card = k → k < #α → A'.Nonempty → Cb-balanced →
    ∃ T, PrefixFree T ∧ 1 / (M Cb) < ∑ η ∈ T, cond P w η ∧
      ∀ η ∈ T, (∃ e, (vertex (w ++ η)).last e ∉ A') ∧
        Mk 1 (st P (w ++ η)) ≤ C2 * Mk 1 (st P w)
```

* **the height constant `C₂` is proved**: `Apriori.Extension.exists_minimal_exit_bound` gives
  `C₂ = 2^L + 1` with `L` the diameter of the Rauzy diagram, *uniformly in `A'`* (since
  `exists_exit_length_bound`'s `L` comes from `RauzyReach.exists_path_between P` alone), each member
  being a minimal exit with all proper prefixes blocked;
* **the mass constant is an arbitrary function `M : ℝ → ℝ`**, not a constant — `ExtMass` is the case
  `M = fun _ => C₂`, refuted (Addendum 85); `ExtMassCbP K` is the case `M Cb = K·Cb²`, numerically
  `K = 7`;
* the two survive separately in the balance constant:
  `KeeGen M C₂ Cb = 4·#α·C₂²·Cb + (2·M Cb + 1)`.

**Consequence**: the last gap of (1) on the `Γ₂` side is exactly "find `M : ℝ → ℝ` with
`ExtMassGen P M (2^L+1)`" — one unknown, and it is a function, so no constant has to be guessed.  The
two constants are still *coupled* through the family: its members must both exit and obey the height
bound, which is why the mass cannot simply be the level-`N` exit mass (that family's members are not
height-bounded).  Any trade-off a proof makes between `M` and `C₂` is visible in `KeeGen`.

**Addendum 92, continued (operational)**: the full exact-rational sweep for the worst slack of the
first-`𝒜'`-win inequality does **not** scale: `.scratch/orch/firstwin_sweep.py` was OOM-killed (exit
137) after ~15 min, and a reduced `d = 3`, nodes ≤ 3, depth `40·M + 200` run hit a 15-minute timeout.
The reason is structural, not a bug: the "not yet won" family keeps *all* its branching (heights grow
without bound, so states never merge), unlike the `Bad`-mass DP where most states die.  Root-node
computations are cheap and were done (Addendum 91: slack `+0.0238` at `d = 3`, `+0.0139` at `d = 4`,
`+0.1` at `d = 5, 6`); anything deeper needs either gcd-normalised keys or a float Monte-Carlo plus an
exact check on the extremal configurations.  The slice members have their own simulators; do not
repeat the full exact sweep here.

### Addendum 93: findings of the agents — the blocked-phase engine landed, with the exact identity and a one-line diagnosis of the obstruction

Landed from `smvy388if` m1 as `MasurVeech/BlockedPhase.lean` (refereed: both modes, zero warnings,
19 axiom headlines all `[propext, Classical.choice, Quot.sound]`, no `sorry`/`axiom`, lines ≤ 100).

**The structural discovery.**  With `φ(w) = ∏_{b ∈ A'} st P w b`:

* `cond_mul_phi` / `cond_eq_div_phi` — **along a blocked run the conditional mass is the ratio of the
  `A'`-products**: `cond P w δ · φ(w++δ) = φ(w)` whenever every proper prefix of `δ` is `Blocked`.
  The per-step ratios telescope *by letter*, not by position, so **the bound is uniform in the length**
  — which is exactly what the length-based arguments (`length_le_of_both_inside`, needing `hR`) could
  never give;
* `pow_le_cond_of_blocked`: `(m/R)^{#A'} ≤ cond` when the `A'`-heights lie in `[m,R]` at the two ends;
  `inv_pow_le_cond_of_blocked_balanced`: under `Cb`-balance, `(1/(2dCb))^{#A'} ≤ cond`;
  `card_mul_pow_le_sum_cond`: the family form.
  Certified: 7272 blocked words, all irreducible `d = 3,4` data, every proper `A'`, 0 violations,
  `min cond/(m/R)^{#A'} = 6/5`.

**A slice of `Γ₃` closed.**  `g3StraddleCard_of_outside_taller`: every node whose outside row end is
strictly taller than the inside one is closed — one arrow, clean exit, mass `> 1/2`, `A'`-heights
unchanged (`exists_clean_family_of_taller`).  Sharp boundary: `cond_clean_exit_of_eq_height` shows that
at equal heights that mass is **exactly `1/2`**.  Hence the residue of `Γ₃` is: *both row ends outside
`A'`, or the outside one not taller*.

**The obstruction, in one sentence** (the member's, and it matches every earlier diagnosis): the
identity bounds the blocked mass from **below**, whereas both remaining statements need an **upper**
bound on the *stuck* family — runs along which the individual `A'`-heights stay bounded.  `Mk`-sum
growth (`sum_cs_step_ge_of_both_inside`) does not give that (`blocked_growth_unbounded`), and the
identity's lower bound is exponential in `#A'`: it supports `ExtMassGen` with `M Cb = K·Cb^{#α}`
(admissible, since `M` is an arbitrary function) but **not** `ExtMassCb`'s `K·Cb²`.

**New tool for the next round** (§6 of the report, landed as theorems): the **row-end walk** — a step
keeps the winner's row end and replaces the loser's by the letter in position `n-2` (`rvStep_last_true`,
`rvStep_last_false_of_pivot_lt`, `vertex_append_last_true_of_pivot_lt`, …), with no move when the pivot
is `n-2`.  The exit is therefore a *positional* condition on the two row ends, which is the shape the
`Γ₂` half needs.

**Status of the other members**: `smvy388if` m2 (balanced `Cb = 1`) and m3 (single outsider) still
running, no findings yet; `smvy2l7ya` m1 (the first-win inequality) still running.

**State**: `lake build` green at **8807** jobs; only real `sorry` is `Main.lean:66` (deferred).

### Addendum 94: numerics stopped; the seat moved to the combinatorial structure of the blocked region

Author's ruling: no further numerical computations — they no longer give useful information (the last
two real advances were the exact identity and the row-end walk of Addendum 93, not constants).
Consequences:

* swarm `smvy2l7ya` (whose whole task was an exact-rational decision of
  `mass(F) > 1/2 + k/(2d)`) is **stopped**; the question of the *value* of the constant is off the
  critical path, since the mathematical route needs a proof of the stuck-family bound, not a constant;
* new swarm `smvy4o4y5` (one member) on the **combinatorics of the blocked region**: package the
  row-end walk from the `rvStep_*` lemmas of `BlockedPhase.lean`, present the blocked region as a finite
  directed graph on `CombData α n × α × α`, prove the dichotomy — *an exit is reachable within an
  explicit bound*, or *the walk runs inside the blocked region forever (a cycle)* — and state the
  mass bound that the bounded case yields via the exact identity, and the linear recurrence on the
  heights in the cycle case.  Purely combinatorial, no numerics;
* the two slice members still running (`smvy388if` m2 balanced `Cb = 1`, m3 single outsider) are proofs,
  not computations, and continue.

**Where the mathematics stands after Addendum 93**: three of the four `Γ`-steps of `easyyoccoz` are
formalised; `Γ₃` is closed at nodes with an outside row end strictly taller than the inside one, with
`1/2` attained exactly at equal heights; and everything that remains is an *upper* bound on the mass of
the family that stays blocked with bounded `A'`-heights.  The identity
`cond · φ(end) = φ(start)` gives exactly the *lower* bound on that family, length-uniformly, so the open
problem is now stated in the sharpest form it has had: *the stuck family cannot be everything.*

### Addendum 95: findings of the three running members — the blocked dichotomy proved with an explicit bound, `Cb = 1` at its sharp boundary, and the potential route closed

**`smvy4o4y5` m1 (blocked region as a finite digraph) — the structural result of the round.**
* packaged row-end walk: **`wl_rvStep : wl (P.rvStep e) e = (P.last e, loserAfter P e)`** with
  `loserAfter P true = if pivot_true < n-2 then (letter at position n-2 of π_bottom) else P.last false`
  (and symmetrically); the `e = false` pivot lemmas were *missing* in `BlockedPhase.lean` and are derived
  from the `true` ones through `rvStep_inv (P := P.inv)`.  Extra fact: for admissible `2 ≤ n` the pivot
  is never `lastPos`, so only the cases `< n-2` and `= n-2` occur;
* abstract finite digraph: `Stays`, `StaysBefore`, and
  **`dichotomy : ExitWithin next B s (card V) ∨ ReachesCycle next B s`** by pigeonhole on `#V + 1`
  states, plus `stays_forever_of_cycle` and `reachesCycle_of_stays`;
* instantiation `State α n = CombData α n × α × α` with **`card (State α n) = (n!)²·(card α)²`**, so
  `blocked_dichotomy` gives the bound **`(n!)²·n²`** — *independent of the Rauzy class* — and
  `blockedCycle_of_long`: a blocked word with all proper prefixes blocked and length `> (n!)²n²` forces
  a blocked cycle.  The mass statement (item 5) is in progress.

**`smvy388if` m2 (balanced `Cb = 1`).**
* `st_eq_Mk_one_of_bal_one` / `bal_one_iff`: `Cb = 1` balance forces `st w b = Mk 1 (st P w)` on `A'`,
  hence `Mk k (st P w) = Mk 1 (st P w)` — a `Cb = 1` node is the **extremal end** of the balance range;
* at a *blocked* `Cb = 1` node **both** arrows have `cond` exactly `1/2` **and**
  `Mk 1 (st P (w++[e])) = 2·Mk 1 (st P w)` exactly (sharp blocked growth); at a *straddling* one the exit
  arrow has `cond = h_out/(h_out+𝔐) ≤ 1/2` and the other `≥ 1/2`, summing to `1`;
* `not_lt_of_bal_one`: at `Cb = 1` the outside row end is **never strictly taller**, so
  `g3StraddleCard_of_outside_taller` never applies — slice 2 *is* the residue, and since the one-step
  exit mass is exactly `1/2`, the strict inequality needs a **second step**.
* (numerics, now deprecated: clean mass `0.83–0.90`, slack `≥ 0.33`, no refutation.)

**`smvy388if` m3 (single outsider) — a closed door, with the exact reason.**
The `A'`-sum potential does **not** bound the unclean mass.  Per arrow,
`cond(μ,[e])·S(μ++[e]) ≤ S(μ)` is true (only the loser moves; if the loser is in `A'` then
`S' = S + h_winner` and `h_loser ≤ S`), but the **sum over the two arrows is not** `≤ S`: at a blocked
node with row ends `a,b ∈ A'` it is `S + 2h_ah_b/(h_a+h_b) > S`, and at a straddling node
`S + (1-p)h_c`.  So `S` is a **submartingale** at blocked nodes and `cond·S` is not a supermartingale;
exact rationals: at the `BlockedExtension` node with all heights `1`, the mass of "first node with
`Mx > thr` is unclean" is `0.9254 > 3/8 = #A'/(2d)`.  Hence **no potential argument on the `A'`-sum can
give `mass_bad ≤ #A'/(2d)`**.  The member also identifies the one potential that *is* a strict
supermartingale for every arrow: `Φ = ∑_{b∈A'} 1/st b` (blocked: decreases by `1/(h_a+h_b)`; straddling:
by `h_c/(h_a+h_c)²`) — but its terminal value is not bounded below.

**What this changes.**  The stuck family now has (i) a *proved* combinatorial skeleton: either an exit
within `(n!)²n²` steps, or a periodic blocked cycle; and (ii) a closed door on the obvious
potential-function proof.  The remaining case is therefore the *cycle* one, and there the exact identity
`cond·φ(end) = φ(start)` already computes the mass — so the open question is the linear recurrence of the
heights around a blocked cycle, which is exactly what `smvy4o4y5` m1's item 4 asks for.

### Addendum 96: does the blocked *cycle* case appear in the source? No — and it is needed exactly for the mass, not for existence

Author's question.  Answer in three parts.

**(a) The source says nothing about it.**  `easyyoccoz.tex`'s `Γ₂` step is one sentence: *"For γ_s ∈ Γ₁,
choose a path γ = γ_sγ_e with minimal length such that γ ends at a permutation π_e such that the top or
the bottom row of π_e (and possibly both) ends by some element of 𝒜∖𝒜'.  Let Γ₂ be the collection of the
γ = γ_sγ_e thus obtained."*  Existence is taken for granted; no case analysis, and no mention of a path
that cannot leave the blocked region.

**(b) For *existence* it needs none, and the tree has it unconditionally.**
`CombData.pairReach_all : Path.PairReach P` — from every admissible vertex, every ordered pair of
distinct letters occurs as the two row ends at a reachable vertex — so from any node a node with a row
end outside `𝒜'` is reachable, with a length bounded by the diagram diameter
(`RauzyReach.exists_path_between` → `Apriori.Extension.exists_exit_length_bound` →
`exists_minimal_exit`, `exists_minimal_exit_bound`).  So the paper's silence here is harmless.

**(c) For the *mass* it is essential, and it is real.**  `BlockedExtension.ends_mem_forever` exhibits a
periodic path along which **both row ends lie in `𝒜'` at every node** — a blocked cycle: no exit arrow
exists at any of its nodes, so those paths lie outside `Γ₂` and are exactly the mass the paper's
`P_q(Γ₂|π) > C₂^{-1}` has to account for.  The paper asserts the bound and never argues it.  The tree now
has the combinatorial skeleton (`smvy4o4y5`: `ExitWithin … (card V) ∨ ReachesCycle …`, bound
`(n!)²·n²`) and the exact identity of a blocked run (`cond · φ(end) = φ(start)`, Addendum 93), so the
only remaining case is the cycle itself.

**A quantitative remark that narrows it.**  At a blocked node the two row ends are both in `𝒜'`, so the
two outgoing `cond`s are `h_a/(h_a+h_b)` and `h_b/(h_a+h_b)`: they sum to `1` and the larger is
`≥ 1/2`.  Hence *whenever a blocked node offers a choice that leaves the blocked region, that choice
carries at least half of the node's mass*.  So the cycle case is not about a small escape fraction: it is
about how soon the walk is offered the choice at all, and along a blocked cycle the heights satisfy a
linear recurrence which fixes the per-period mass factor.  That recurrence is the object to compute.

### Addendum 97: the `Cb = 1` slice landed (`MasurVeech/BalancedOne.lean`) — the first explicit clean-exit family with a proved mass

Swarm `smvy388if` m2, refereed and landed (25 axiom headlines, both compile modes, no warnings, no
`sorry`).  The slice is exactly the residue of `g3StraddleCard_of_outside_taller` (by
`not_lt_of_bal_one`, at `Cb = 1` the outside row end is never *strictly* taller), so it is not a
weakening — and it is closed by an explicit construction:

* `st_eq_Mk_one_of_bal_one`, `bal_one_iff`: `Cb = 1` balance is an *equality*
  (`st w b = Mk 1 (st P w)` on `A'`), hence `Mk k (st P w) = Mk 1 (st P w)`;
* exact one-step masses: at a **blocked** `Cb = 1` node both arrows have `cond = 1/2` **and**
  `Mk 1 (st P (w++[e])) = 2·Mk 1 (st P w)` exactly; at a **straddling** one the exit has
  `h_out/(h_out+𝔐) ≤ 1/2` and the other arrow `≥ 1/2`;
* **`exists_clean_family_of_selfLoop`**: if the letter `e` (whose winner is the *outside* end) fixes the
  vertex of a `Cb = 1` straddling node, then the prefix-free family `{[e]^n ++ [!e] : n < N}`,
  `N = ⌊(2d-1)·𝔐/h⌋ + 1`, has mass **`1 - 𝔐/(𝔐+Nh) > 1 - 1/(2d)`** and satisfies *every* `G3Straddle`
  clause.  Per-word masses are proved exactly (the sum telescopes).
* Refuted in passing: the `Γ₂` slice at `C₂ = 2` is *empty* for `d = 4` (mass `0`), so the height
  constant must be `≥ 3`.

**Why this matters beyond the slice.**  The construction is the first instance of the mechanism the
general case needs: repeat the *outside*-winner letter until the inside height has grown, then exit.  At
a straddling node the exit carries `h_out/(h_out+𝔐)`, which is small exactly while `h_out ≪ 𝔐`; the ray
`[e]^n` makes `h_out` negligible by growing the inside height, and the mass of the resulting family
telescopes to `1 - 𝔐/(𝔐+Nh)`.  The only hypothesis used is `hloop` (`e` fixes the vertex), i.e. that the
node stays straddling — which is what the blocked-graph work (`smvy4o4y5`) is analysing: the general case
needs the walk to *return* to, or *stay at*, a straddling node long enough.

**State**: `lake build` green at **8808** jobs; all `Check.lean` headlines
`[propext, Classical.choice, Quot.sound]`; only real `sorry` is `Main.lean:66` (deferred).
Running: `smvy388if` m3 (single outsider) and `smvy4o4y5` m1 (blocked graph).

### Addendum 98: the blocked region is fully mapped (`MasurVeech/BlockedGraph.lean`) — and the residue is *not* a blocked phenomenon

Swarm `smvy4o4y5` m1, refereed and landed (28 axiom headlines, both modes, no warnings after marking
`stateFintype` instance-reducible, no `sorry`).

* `wl_rvStep`, `pivot_val_le`: the packaged row-end walk (the `false` half derived from `rvStep_inv`;
  for admissible `2 ≤ n` the pivot is never `lastPos`, so only `< n-2` and `= n-2` occur);
* `stays_iff`, `card_state : #State = (n!)²(card α)²` for `State α n = CombData α n × α × α`;
* **`blocked_dichotomy_factorial`**: from any node, an exit is reachable within `(n!)²n²` blocked steps,
  *or* the blocked region contains a cycle; `blockedCycle_of_long` for the length form;
* **`heights_cycle_recurrence : h_{t+1} = (QVv)ᵀh_t`** and **`cycle_Mk_unbounded`**: along a blocked
  cycle the maximum grows **without bound**; `cond_lpow_of_blockedLoop` for the mass of iterating a loop;
* `blocked_family_mass_zero_of_no_cycle`: no blocked cycle ⟹ no path stays blocked beyond `(n!)²n²`,
  so the stuck mass there is `0` and the `Γ₂` mass is `1` (the exit family is everything);
* **`exists_exit_bound_explicit`**: the height constant `C₂ = 2^((n!)²n²)+1`, explicit and independent of
  the diagram diameter.

**The reframing this forces.**  `cycle_Mk_unbounded` says "stuck *with bounded heights*" cannot happen
inside the blocked region: either you exit quickly, or the heights blow up.  So the residue of `Γ₃`
after Addendum 96 — *no `A'`-win and all heights bounded* — is **not** a blocked phenomenon.  Since "no
`A'`-win" literally means *both row ends lie outside `A'`* (the winners are the row ends), the residue
lives in the **complementary region**, and it needs the same analysis.  That is the new task: swarm
`smvy5d0sf` (one member) is doing for `Outside` exactly what `BlockedGraph` did for `Blocked` — the walk,
the dichotomy with the explicit `(n!)²(card α)²` bound, the cycle recurrence, and the question whether an
`Outside` cycle can keep the heights bounded (if it cannot, the residue is empty and `Γ₃` closes; if it
can, the cycle is the obstruction and is a finite combinatorial object to exhibit).

Still running: `smvy388if` m3 (single outsider).
**State**: `lake build` green at **8809** jobs; only real `sorry` is `Main.lean:66` (deferred).

### Addendum 99: the author's argument for Γ₂'s mass — right, and it settles the object I had been computing wrongly

The author's argument: take `γ_e` of minimal length to a node with a row end outside `𝒜'`; every step
before the last is `Blocked` (both row ends in `𝒜'`), so at each step the winner *and* the loser are
`𝒜'`-heights; `γ_s ∈ Γ₁` gives `Cb`-balance at the start; and the balance degrades by at most a factor
`2` per step (`h_loser ← h_loser + h_winner ≤ 2·Mk 1`, while the minimum only grows,
`AppendixA.state_mono`), so over the `≤ L` steps of a minimal extension the state stays
`2^L·Cb`-balanced.  Then every blocked step has `cond ≥ 1/(1 + 2^L·Cb)` (`cond_arrow`), so the blocked
prefix is followed with probability `≥ (1/(1+2^L·Cb))^L`, **uniformly in `γ_s`**; gluing over `Γ₁`
(`graded_min`, mass `> 1/C₁`) gives the mass of `Γ₂`.

**This is correct and it closes the `Γ₂` mass up to one step.**  In particular it corrects my own
Addendum 92 computation: I had bounded the cond of a *single exit word* and found an unbounded factor
`𝔐(q_w)^{#(α∖𝒜')}`; the author's decomposition (blocked prefix, then exit) is the right object, and on
the blocked prefix every ratio is between `𝒜'`-heights, hence controlled by the balance.  The constant
that comes out is of the form **`1/(K·Cb^{L+1})`** — a power of `Cb`, not `Cb²`, which is admissible in
`ExtMassGen` (whose mass constant is an arbitrary `M : ℝ → ℝ`, Addendum 92) and explains why the sharp
`K·Cb²` form was the wrong target.

**The one step the argument as stated does not cover**: the *exit* arrow itself.  Its probability is
`h_out/(h_out + h_{A'-end})`, and `h_out` — the outsider's height — is *frozen* throughout the blocked
phase and is **not** bounded below by the `𝒜'`-balance (the level-`k` hypothesis constrains only the
`k`-subset `𝒜'`).  So a single word's cond is not bounded below.  The repair is the waiting mechanism
already proved in the `Cb = 1` slice (`BalancedOne.exists_clean_family_of_selfLoop`): if the outsider is
the *taller* end, the exit attempt has probability `≥ 1/2`; if it is the shorter, take the other letter —
the outsider then grows by an `𝒜'`-height and becomes comparable — and the family `{[e]^n ++ [!e]}` has
mass `1 - 𝔐/(𝔐+Nh)`.

Swarm `smvy5jzor` (one member) is formalising this: `balance_step`, `balance_prefix`,
`cond_blocked_prefix_ge`, `extMassGen_of_balance` (with the `Cb^{L+1}` constant), and the last step in
either of the two forms above.  If it lands, **`Γ₂` is closed** and (1) rests on `Γ₃` alone.

### Addendum 100: the residue is EMPTY and the induction has bounded lag (`MasurVeech/OutsideGraph.lean`) — the structural side of (1) is closed

Swarm `smvy5d0sf` m1, refereed and landed (36 axiom headlines, both modes, no warnings, no `sorry`).
This changes what has to be proved.

* **`no_exitArrow_iff`**: there is no exit arrow at a node iff the node is `Blocked` (both row ends in
  `A'`) or `Outside` (both row ends outside `A'`, equivalently *no arrow wins in `A'`*).  The third case
  is a straddling node, where an exit arrow exists.
* **`noExit_dichotomy`** — the bounded lag, for every node: *either* a node carrying an exit arrow is
  reached in at most `(n!)²(card α)²` steps along a no-exit path, *or* there is a periodic no-exit
  configuration (`w ++ u ++ v` periodic, no-exit throughout) along which the maximum is **unbounded**
  (`∀ C, ∃ t, C < Mk 1 (st P (w ++ u ++ lpow v t))`).
* **`residue_empty_of_balanced`**: the no-win family with all heights `≤ 2d·M(q_w)` is **empty** beyond
  `2d²·Cb` steps (`residue_length_le : length · mmin ≤ d · H`).  So the "residue" of `Γ₃` after the
  author's correction (Addendum 86–88) is not a mass statement at all — it is a *length* statement, and
  vacuous.
* Structure of the `Outside` region: the `A'`-heights are **frozen** (`st_frozen_step`,
  `st_append_frozen`, `phi_frozen`) since the loser is a row end, hence outside `A'`; the correct
  telescoping there is `cond = psi_w/psi_end` with `psi = ∏_{b ∉ A'} st` (`cond_eq_div_psi`,
  `psi_lt_of_step`); the height recurrence is the same `h_{t+1} = (QVv)ᵀh_t`; and
  **`mk_unbounded_of_periodic`**: the maximum is unbounded along *every* periodic no-exit run, so no
  bounded-height cycle exists.

**What this gives.**  Within `max((n!)²n², 2d²Cb)` steps every path either has an exit arrow available
*or* its maximum has crossed `2d·M` — i.e. exactly the `Γ₄` dichotomy.  Both remaining mass estimates
therefore become *bounded-length products of one-step ratios*, which is precisely the author's argument
(Addendum 99): the balance degrades by a bounded factor over a bounded number of steps, and each step is
bounded below.  No unbounded-time mass estimate remains anywhere.

**Where (1) stands now**: `Γ₂`'s mass is being formalised by the author's argument (`smvy5jzor`);
`Γ₃`'s residue is empty, and what remains of `Γ₃` is the *straddling* case (one end outside `A'`), whose
`1/2`-boundary is `BlockedPhase.cond_clean_exit_of_eq_height` and whose "outside taller" half is
`g3StraddleCard_of_outside_taller`.  `lake build` green at **8810** jobs; only real `sorry` is
`Main.lean:66` (deferred).

### Addendum 101: the author's argument for `Γ₂` formalised (`MasurVeech/Gamma2Mass.lean`) — and my second objection retracted

Swarm `smvy5jzor` m1, refereed and landed (24 axiom headlines, both modes, no warnings, no `sorry`).

**The author's argument is now a theorem** (namespace `Gamma2Mass`):
* `exists_uniform_minimal_exit`: a minimal exit of length `≤ L`, with **`L` uniform in `A'`**;
* `balance_step` / `Mk_one_step_le_max`: one arrow degrades the `A'`-balance by at most `2` (the minimum
  is non-decreasing).  Note the naive form `Mk 1 (st P (v++[e])) ≤ h_l + h_w` is **false** — the sharp
  form is `Mk_one_step_le_max`, which is what the argument needs;
* `balance_prefix`: at every prefix of the minimal exit, the `A'`-heights lie in
  `[m₀, 2^i·Mk 1 (st P (w++γ_s))]`, so the state is `(2^L·Cb)`-balanced throughout;
* `cond_blocked_prefix_ge` and **`cond_minimal_exit_ge`**: `(1/(1+2^L·Cb))^L ≤ cond` for the whole
  minimal exit word;
* `exists_glued_family` and **`extMassGen_of_balance`**:
  `G1WithGrowth P C₁ C₂' → ExtMassGen P (fun Cb => C₁·2^{L(L+1)}·Cb^{L+1}) (2^L·C₂')`;
* `balanceStep_of_G1WithGrowth`: straight into `Apriori.BalanceStep`.

**Retraction (the second one in two rounds, and both were mine).**  Addendum 99 said the exit *arrow*'s
probability `h_out/(h_out+h_{A'-end})` is not controlled because the outsider's height is frozen.  That
was wrong: `Apriori.Extension.Exit` is a property of the **node** ("a row end is outside `A'`"), so the
last arrow of a minimal exit is taken at a **blocked** node, where winner and loser are both
`A'`-heights, hence its mass is `≥ 1/(1+2^L·Cb)`.  The frozen outsider is not a row end there; that
issue belongs to `Γ₄`'s straddling arrow (`G3Straddle`), not to `Γ₂`.  So the author's argument covers
the exit word completely, as stated.

**The one remaining slot**: `ExtMassGen`'s growth constant `C₂'`, i.e. the hypothesis `G1WithGrowth`.
The member reports it as unpatchable from below (`blocked_growth_unbounded`), but at the point of use it
is not: `Graded P k C` gives `Mk 1 (st P (w++δ)) < C·min (Mk k …) (Mk 1 (st P w)) ≤ C·Mk 1 (st P w)` for
every member, i.e. `C₂' = C`, and `graded_min` supplies `Apriori.StatementMin`.  Swarm `smvy6awxv`
(one member, 300 steps) is deriving `Graded → G1WithGrowth`; if it lands, **`Γ₂` is closed outright**
(`ExtMassGen P (fun Cb => K·Cb^{L+1}) (2^L·C)` for the level-`k` stage) and (1) rests on `Γ₃` alone.

**State**: `lake build` green at **8811** jobs; only real `sorry` is `Main.lean:66` (deferred).

### Addendum 102: the single-outsider slice landed (`MasurVeech/SingleOutsider.lean`) — `Γ₃`'s last piece is the *non-dominant straddling* case

Swarm `smvy388if` m3, refereed and landed (22 axiom headlines, both modes, no warnings, no `sorry`).
Namespace `SingleOutsider`.

* `A' = univ.erase c`: `ExitArrow` iff the loser is the outsider; a node straddles iff the outsider is a
  row end; at most one exit arrow per node;
* **`st_frozen_of_ne_loser`**: only the loser's height moves, so every non-exit arrow — and every
  `Blocked` node — leaves `st c` fixed (along an arbitrary non-exit word), with `st c ≤ Mk 1 (st P w)`;
* the exact one-step mass at a straddling node: `cond = st c/(st c + st a)`, which is `> 1/2` iff the
  `A'`-row-end is *shorter* than the outsider;
* **`g3Concl_of_dominant`** (every node where the outsider beats the `A'`-row end) and its `#A' = d-1`
  form `g3StraddleCard_pred_of_forall_dominant`; `g3Concl_two_step` pushes the same to `st a < 2·st c`;
* **`extConcl_of_straddling`**: `Γ₂` is free at straddling nodes for a single outsider.

Refuted in the same file: the `A'`-sum potential (the two-arrow sum exceeds `S`), and the grading
`bad ≤ 1/(2#α)` at *blocked* nodes (values up to `0.9254`).

**What `Γ₃` is reduced to.**  For a single outsider, everything is closed except a straddling node at
which the outsider does **not** dominate the `A'`-row end (`st a ≥ st c`); there the one-step exit carries
`≤ 1/2` and the family has to wait — which is exactly the mechanism of
`BalancedOne.exists_clean_family_of_selfLoop` (`{[e]^n ++ [!e]}`), whose mass `1 - 𝔐/(𝔐+Nh)` tends to
`1 - 1/(2d)` at the boundary `𝔐/h = 2d-1`.  Two independent routes (`BalancedOne` at `Cb = 1`, and this
slice at `#A' = d-1`) reach the same sharp constant `1 - 1/(2d)`, which is a good sign that it is the
right boundary and that the waiting family is the right object.

**State**: `lake build` green at **8812** jobs; all `Check.lean` headlines
`[propext, Classical.choice, Quot.sound]`; only real `sorry` is `Main.lean:66` (deferred).
Running: `smvy6awxv` m1 (the growth slot `Graded → G1WithGrowth`, which would close `Γ₂`).

### Addendum 103: `Γ₂` IS CLOSED — unconditionally (`MasurVeech/GrowthSlot.lean`)

Swarm `smvy6awxv` m1, refereed and landed (14 axiom headlines, both modes, no warnings after silencing
the unused-variable linter, no `sorry`).  Namespace `GrowthSlot`.

**`exists_extMassGen_sharp`**:
```lean
∃ L : ℕ, ∀ ε : ℝ, 0 < ε → Induction.ExtMassGen P
    (fun Cb => (1 + ε) * (1 + 2^L * Cb)^L) (2^L)
```
i.e. **the `Γ₂` mass holds with no hypothesis beyond `P.Admissible` and `2 ≤ n`**, with the mass
function `M Cb = (1+ε)(1 + 2^L·Cb)^L` and the height constant `C₂ = 2^L`, `L` the diameter of the Rauzy
diagram.  Also `exists_extMassGen` (`M Cb = 2·2^{L(L+1)}·Cb^{L+1}`, `C₂ = 2^L`) and
`exists_extMassGen_of_graded` (the level-`k` form; the constant `C` does *not* occur in the output).

**Why it closes.**  `G1WithGrowth` quantifies its prefix-free family *existentially*, so `S = {[]}`
satisfies it outright: mass `cond P w [] = 1`, balance is the caller's hypothesis, growth
`Mk 1 ≤ 1·Mk 1` — hence `C₂' = 1` and **no use of `Graded` at all** (`g1WithGrowth_of_one_lt`,
`1 < C₁`; the constants `C₁ > 1` and `C₂' ≥ 1` are forced, prefix-free mass being `≤ 1` and heights
non-decreasing).  Composing with `Gamma2Mass.extMassGen_of_balance` (the author's balance-degradation
argument, Addendum 101) gives the mass `(1+ε)^{-1}(1+2^L·Cb)^{-L}` for the single minimal exit word, by
`cond_minimal_exit_ge`.

**Divergence from my sketch, confirmed by the member and worth recording**: the pigeonhole's `A'` is
*existential* rather than the caller's, and `graded_min`'s growth slot comes only at `Cb := C`; for a
given `A'` it yields just `Cb·Cb'`-balance.  So the `{[]}` route is the honest one, and `Γ₂`'s interface
does not see the level-`k` property at all.

**Consequence**: statement (1) now rests on **`Γ₃` alone** —
`Induction.statement1_of_gaps` with its first hypothesis discharged unconditionally.  What remains of
`Γ₃`: the straddling case where the outsider does not dominate
(`SingleOutsider`: `st a ≥ st c`), where the waiting family `{[e]^n ++ [!e]}` of
`BalancedOne.exists_clean_family_of_selfLoop` is the known mechanism and the boundary is `1 - 1/(2d)`;
the residue is empty (`OutsideGraph.residue_empty_of_balanced`), and the "outside taller" half plus
`#A' = 1` are closed.

**State**: `lake build` green at **8813** jobs; all `Check.lean` headlines
`[propext, Classical.choice, Quot.sound]`; only real `sorry` is `Main.lean:66` (deferred).

### Addendum 104: everything is on the non-dominant straddling case of `Γ₃` now

Author's instruction.  State of the target: `Γ₂` is closed (`GrowthSlot.exists_extMassGen_sharp`), so by
`Induction.statement1_of_gaps` the whole of (1) is

  **`G3StraddleCard P k` for `k ≥ 2`**

(`k = 0, 1` landed).  New swarm `smvy6z8lp`, three members, all on it:

1. **the waiting family in general** — generalise `BalancedOne.exists_clean_family_of_selfLoop` beyond the
   `hloop` hypothesis (where the survivor letter fixes the vertex), using that the `A'`-end cycles among
   the `k` letters of `A'` and that the outside height `h_c` is frozen;
2. **the unclean family is at most a half** — `mass{first stop is an `A'`-crossing of `2·#α·Mk 1 (st P w)`
   before any exit arrow} ≤ 1/2`, which is exactly what the clean/unclean split needs, with a *proof*
   (a computation is not accepted);
3. **the assembly** — from (1) and (2) as explicit hypotheses, `G3StraddleCard P k` (`k ≥ 2`) and then
   `MVDesign.Statement1`, which pins the interface the other two must meet.

**The mechanism, recorded for the briefs** (it is the same one twice, and it is why the case is
tractable): at a straddling node with outside end `c` (height `h_c`, frozen) and `A'`-end `a` (height
`h_a`), the two letters have masses `h_c/(h_a+h_c)` (**the exit**) and `h_a/(h_a+h_c)` (**the survivor**),
the survivor grows `h_a` by `h_c` and keeps `c` a row end, so repeating it telescopes
`∏ h_{a_i}/(h_{a_i}+h_c)`; the `A'`-end cycles among `k` letters, each growing by `h_c` per visit, so
either a clean exit arrives or some `A'`-height passes `2·#α·Mk 1 (st P w)` — and the latter is the
unclean outcome whose mass must be `≤ 1/2`.

**State**: `lake build` green at **8813** jobs; every headline in `Check.lean` is
`[propext, Classical.choice, Quot.sound]`; the only real `sorry` is `Main.lean:66` (deferred — it needs
`MVDesign.Statement1` for every `P`, which is exactly what these three slices are for).

### Addendum 105: the missing lemma in the language of `easyyoccoz` — and the paper is *not* complete on it

Author's question, answered for the record.

**(a) The missing lemma, in the paper's own notation.**  With `𝒜' ⊆ 𝒜`, `#𝒜' = k < d`,
`𝔐(q) = max_α q_α`, `𝔪_{𝒜'}(q) = min_{α∈𝒜'} q_α`, `q = B_w·1`, `P_q(·|π)` the path measure, and
`Γ₂` as on p. 263 (the minimal extensions to a permutation with a row end outside `𝒜'`, with
`𝔐(B_γ q) < C₂𝔐(B_{γ_s}q)`), the statement our formalisation still owes is:

> for every `γ_s ∈ Γ₂` (equivalently: `q_{γ_s}` `C`-balanced on `𝒜'` and a row end outside `𝒜'` at
> `π_{γ_s}`) the family
> `Γ₃ = {γ = γ_sγ_e : the winner of the last arrow of γ_e lies in 𝒜', the winners of the other arrows of
> γ_e lie in 𝒜∖𝒜', and (B_γ q)_α ≤ 2d(B_{γ_s} q)_α for all α ∈ 𝒜'}`
> carries `P_q(Γ₃ | γ_s) > 1/2`,

which is *verbatim* the paper's own display on p. 264, and in the form `Γ₄` consumes:

> `P_q({γ = ν·e : e an exit arrow at ν (winner ∈ 𝒜', loser ∉ 𝒜'), or 𝔐(B_γ q) > 2d𝔐(q)} | γ_s) > 1/2`,
> restricted to the members with `(B_γ q)_α ≤ 2d(B_{γ_s}q)_α` for all `α ∈ 𝒜'`.

Equivalently — and this is the sharpest form — **the complement must be at most a half**: the paths whose
first stop is a crossing of `2d𝔐(q)` by an `𝒜'`-coordinate, before any exit arrow, carry mass `≤ 1/2`.

**(b) Is the paper complete here?  No — this is a mathematical gap, not a formalisation gap.**  The
paper's entire justification is the sentence *"By Lemma [Kerckhoff], `P_q(Γ₃ | γ_s) > 1/2`"*.  But
Kerckhoff's lemma (the file's Lemma `T q alpha`) says

  `P_q(γ ∈ Γ_α(π), (B_γ q)_α > T q_α | π) < T^{-1}`,

i.e. it bounds the **crossing of one coordinate along paths on which that coordinate never wins**.  The
union bound over `α ∈ 𝒜'` therefore gives

  `P_q(∃α ∈ 𝒜' : (B_γq)_α > 2d(B_{γ_s}q)_α, and no 𝒜'-winner) < #𝒜'/(2d) < 1/2`,

which is a statement about the **unclean** families — the *complement* of `Γ₃`, not `Γ₃`.  To conclude
`P_q(Γ₃|γ_s) > 1/2` from it, one needs the paths that never win in `𝒜'` to carry mass `≈ 0`, which the
lemma does not give; and the a.e. statement "every letter wins eventually" is exactly statement (1) itself,
so using it would be circular.  In short: the one line of the appendix that does not follow from its own
toolbox is precisely this one, and our `Γ₃` target is that line.

**(c) What has been closed around it, and what is left.**  Closed since Addendum 86: the author's
correction shows Kerckhoff *does* apply to the prefix for the winning letter, so the crossing part of
`Γ₃` is now bounded (`Apriori.G3U.FirstWin.firstwin_crossing_mass`, `< #𝒜'/(2d)`); the "never stop with
bounded heights" part is *empty* (`OutsideGraph.residue_empty_of_balanced`), and in the `Outside` region
`𝒜'`-heights are frozen, so a crossing there is by an outsider — hence a **clean** ending, admissible in
`Γ₄`.  What remains is exactly the unclean family: **mass of "first stop is an `𝒜'`-crossing, before any
exit arrow" `≤ 1/2`.**  Believed true with room (`raceSmall_two` gives `1/4` at `d = 2`; the extremal
configurations give `1/(2d)` in exact rationals; two independent routes — `Cb = 1` and `#𝒜' = d-1` —
reach the same boundary `1 - 1/(2d)`), but not proved in the literature and not yet proved here.

### Addendum 106: the author's Γ₃ argument — checked, formalised in its first half, and the residual pinpointed

The author's argument for `P_q(Γ₃|γ_s) > 1/2`: with `q' = B_{γ_s}q`, split the complement of `Γ₃'` by the
winning letter `α ∈ A'`; for each `α` the set "all winners ≠ α until the last, which is α, and
`(B_γ q')_α > 2d q'_α`" has mass `≤ 1/(2d)` **by the improved Kerckhoff** (the winning step leaves the
`α`-coordinate unchanged, so Kerckhoff applies to the prefix — this is the correction of Addendum 86);
union over `α ∈ A'` gives `≤ #A'/(2d) ≤ 1/2`; complement `≥ 1/2`.

**Checked**: correct, and its first half is *already landed* — `Apriori.G3U.FirstWin.firstwin_crossing_mass`
is exactly "the crossing part of the first-`A'`-win family has mass `< #A'/(2#α)`", and
`g3Straddle_of_firstWinResidue` turns the residue into `G3StraddleCard`.

**The one inference that needs care** (and it is the whole remaining gap): "the complement has measure
`≥ 1/2`" uses that the paths *with* a first `A'`-win exhaust the space, i.e. `mass(no A'-win ever) = 0`.
That is not automatic: at a node with both row ends **outside** `A'` no letter wins in `A'`.  The residual
splits into

* **(a)** no `A'`-win and an unbounded maximum — in the `Outside` region the `A'`-heights are *frozen*
  (`OutsideGraph.st_frozen_step`, `phi_frozen`), so the growth is in the outsider coordinates and the
  first crossing is by an outsider: **admissible** for `G3StraddleCard` (which allows the crossing
  alternative).  Moreover a path that stays in `Outside` forever is eventually periodic in the finite
  state space `(π, row ends)`, and `mk_unbounded_of_periodic` makes its maximum unbounded — so this case
  is not empty, but it is *clean*;
* **(b)** no `A'`-win with some **`A'`-height** exceeding `2d·Mk 1 (st P w)` — the genuinely **unclean**
  case, which `G3StraddleCard` cannot accept, and the only remaining obstruction.

**Crude accounting of (b)**, for the record: a step with no `A'`-win at a straddling node is the
*survivor* letter, conditional mass `h_a/(h_a+h_c)`, and it grows the current `A'`-end by `h_c`; the
`A'`-end cycles among the `k` letters, so pushing one past `2d·Mk 1` costs at least
`(2d-1)·Mk 1/h_c` survivor steps, giving survival `≤ (1 - h_c/(2d·Mk 1))^{(2d-1)Mk 1/h_c} ≈ e^{-(2d-1)/(2d)}`.
Combined with `#A'/(2d)`, the two crude terms do **not** in general fall below `1/2` (e.g. `d = 5`,
`k = 4`: `0.4 + 0.14`), so the paper's constant `1/2` is **not delivered by this route as it stands**;
the exact rationals say the true total bad mass is `≤ 1/(2d)`, i.e. an order of magnitude better, so a
sharper accounting (not the crude `e^{-1}`) is what closes it.

**Acted on**: new swarm `smvy7oicf` (one member) on exactly the residual: `no_win_family`, case (a)
admissible via the frozen `A'`-heights, the sharp mass bound for case (b), and the bookkeeping
`mass(F-crossing) + mass(b) ≤ 1/2`.  Together with `smvy6z8lp` (three members: waiting family,
unclean-half, assembly) that is four members on `G3StraddleCard P k` (`k ≥ 2`), the last statement of (1).

### Addendum 107: `Γ₃` PROVED for a single outsider, and **statement (1) unconditionally for `#α ≤ 3`** (`MasurVeech/AssembleG3.lean`)

Swarm `smvy6z8lp` m1, refereed and landed (34 axiom headlines, both modes, no warnings, no `sorry`).
Namespaces `PredCase`, `Assemble`.

* **`PredCase.g3StraddleCard_pred : G3StraddleCard P (#α - 1)`** — `Γ₃` in the single-outsider case,
  **unconditionally** (only `P.Admissible`, `2 ≤ n`; the balance hypothesis is not even used).  The
  observation that makes it work, and which none of us had seen: with one outsider the `A'`-row end
  **never leaves `A'`**, so a clean exit exists at *every* depth along the survivor ray
  `{[e]^m ++ [!e]}`; the masses telescope to `1 - cond P w [e]^N`, the heights grow by at most `h_c` per
  step, and `N = ⌊M/h_c⌋ + 1` already gives mass `> 1/2` inside the `2dM` cap.  No dominance case, no
  balance, no self-loop hypothesis.
* **`Assemble.statement1_of_card_le_three : #α ≤ 3 → MVDesign.Statement1 P`** — **statement (1),
  unconditionally, for alphabets of size 2 and 3.**  This is a theorem about the source problem, not a
  reduction: `k ≥ 2` and `k < #α` force `k = #α - 1` there.
* **`Assemble.statement1_of_g3 : (∀ k ≥ 2, G3StraddleCard P k) → MVDesign.Statement1 P`** — the
  assembly, `Γ₂` discharged by `GrowthSlot.exists_extMassGen_sharp`.  So the *only* missing input of (1)
  is `G3StraddleCard P k` for `k ≥ 2`, and
* **`Assemble.statement1_of_narrow`** pins the residue exactly: `2 ≤ #A' ≤ #α - 2` (so `#α ≥ 4`) **and**
  a straddling node at which **no outside row end is strictly taller** — the non-dominant straddling case.

**Interface finding, important for the other two slices**: `uncleanSmall_iff_levelCleanMass` proves that
"unclean mass `≤ 1-ν`" and "clean mass `≥ ν`" are the *same* inequality, so the two halves are
**complementary, not additive** — summing them double-counts, and `ν > 1/2` must be *strict*.  Bridges
kept: `uncleanSmall_of_raceSmall`, `g3StraddleCard_of_gamma3Mass`, `g3StraddleCard_of_uncleanMassBd`.

**State**: `lake build` green at **8814** jobs; all `Check.lean` headlines
`[propext, Classical.choice, Quot.sound]`; the only real `sorry` is `Main.lean:66`, which now needs
(1) for `#α ≥ 4` — i.e. `G3StraddleCard P k` for `2 ≤ k ≤ #α - 2` at non-dominant straddling nodes.
Running: `smvy6z8lp` m2/m3 (waiting family, unclean half) and `smvy7oicf` m1 (the no-win family).

### Addendum 108: `Γ₃` PROVED IN FULL, and **STATEMENT (1) IS DONE** — `MasurVeech/Statement1Done.lean`

Swarm `smvy6z8lp` m2, refereed and landed as `MasurVeech/UncleanCore.lean` (namespace `Apriori.G5`;
24 axiom headlines, both modes, warning-free after the usual linter silences), and the final assembly
landed as **`MasurVeech/Statement1Done.lean`**:

```lean
theorem Statement1Done.statement1 (P : CombData α n) (hP : P.Admissible) (hn : 2 ≤ n) :
    MVDesign.Statement1 P
-- #print axioms: [propext, Classical.choice, Quot.sound]
```

**The proof of `Γ₃`** (`Apriori.G5.g3StraddleCard_of_unclean : G3StraddleCard P k` for **every** `k`,
unconditional; balance unused):
1. `not_blocked_of_noExit` — a step keeps the row end of its own type, so a *blocked* child of a
   non-blocked node would have to be reached by an exit arrow; hence from a node with a row end outside
   `A'` **no blocked node is reached before the stop**;
2. `step_sum_le` — the `A'`-sum potential `S(u) = Σ_{b∈A'} st u b` contracts on the non-exit branches at
   every **non-blocked** node (straddling: `h_a/(h_a+h_c)·(S+h_c) ≤ S` since `h_a ≤ S`; outside:
   equality).  **Blocked nodes are the only failure** — which is exactly `smvy388if` m3's earlier
   counterexample, now *neutralised* by (1) rather than contradicted;
3. `frontier_bound` — the potential-weighted mass of the frontier of the no-exit/no-crossing tree is
   `≤ S(w)` (level induction);
4. `bad_mass_le` — the unclean mass is `≤ S(w)/thr ≤ #A'/(2·#α) < 1/2`;
5. `good_mass_gt_half` + the landed `g3StraddleCard_of_goodMass_straddle` give the target.

**So the last two rounds' apparent contradiction resolves**: `S` is *not* a supermartingale at blocked
nodes (m3, Addendum 95), but no blocked node is reachable before the stop (m2, item 1) — the two facts
are simultaneous, and together they give the potential argument.

**Where (1) now stands**: proved, unconditionally, for every admissible `P` and `2 ≤ n` — the whole
`easyyoccoz` chain (base, `Γ₁`, `Γ₂`, `Γ₃`, `Γ₄`) plus the reduction `simpleyoccoz → (1)`
(`Statement1Assembly.lean`) is axiom-clean and in the tree.  Landed along the way, as theorems about the
source problem: statement (1) for `#α ≤ 3` (`Assemble.statement1_of_card_le_three`), `Γ₃` for a single
outsider (`PredCase.g3StraddleCard_pred`), `Γ₂`'s mass (`GrowthSlot.exists_extMassGen_sharp`), and the
two machine-checked refutations of the paper's own constants (`CoverDataFalse`, `Gamma3Refuted`) plus the
`easyyoccoz` annotation in `Yoccoz/`.

**State**: `lake build` green at **8816** jobs; every headline in `Check.lean` is
`[propext, Classical.choice, Quot.sound]`; the only real `sorry` in the tree is `Main.lean:66`, which
needs `MVDesign.main_of_three` (i.e. (1) + (2) + (3)) — (1) is now available, so `Main` is unblocked
from the `(1)` side and only the deferred assembly remains.

### Addendum 109: on the "no `A'`-win" question — it is not what the proof needs, and it is false as a uniform statement

Author's question ("is the problem to show `P_q(paths where A' never wins) = 0`?").  **No** — and this is
worth recording, because it was my reading two rounds ago (Addendum 106) and it was wrong in an
instructive way.

* **The landed proof does not need it.**  `UncleanCore.bad_mass_le` bounds the *unclean* mass directly by
  the potential: `mass{first stop is an `A'`-crossing} ≤ S(w)/thr ≤ #A'/(2#α) < 1/2`, where
  `S(u) = Σ_{b∈A'} st u b` contracts on the non-exit branches at every non-blocked node
  (`step_sum_le`) and no blocked node is reached before the stop (`not_blocked_of_noExit`).  Nowhere is
  it asserted that the no-`A'`-win paths are null.
* **And the statement is false in the uniform form.**  At a node with *both* row ends outside `A'` no
  letter wins in `A'`; the `Outside` region can be inhabited (the `A'`-heights are frozen there,
  `OutsideGraph.st_frozen_step`, and along a periodic `Outside` run the maximum is unbounded,
  `mk_unbounded_of_periodic`).  So `P_q(no A'-win)` need not be `0`, and no argument of the form
  "complement of the union, so `≥ 1 - #A'/(2d)`" can be made to work by assuming it is.
* **What is true** is the a.e.-in-`λ` statement (a.e. path wins every letter infinitely often) — and that
  is a *consequence* of (1) itself, which is now proved (`Statement1Done.statement1`), so it is no longer
  an input anywhere.

**Also**: swarm `smvy6z8lp` ended **solved**, two accepted (`AssembleG3.lean` — `Γ₃` for a single
outsider and (1) for `#α ≤ 3`; `UncleanCore.lean` — `Γ₃` in full).  Its third member ended without
submitting but left a compiling file, which is now landed as `MasurVeech/Waiting.lean` (the ray family
`ray s k`, its prefix-freeness, and the `cond`-product formulas — the waiting-family infrastructure,
23 axiom headlines, no `sorry`).  `smvy7oicf` (the no-win family) is stopped, its task being moot.

**State**: `lake build` green at **8817** jobs; (1) proved for every admissible `P`; the only real
`sorry` is `Main.lean:66`, which now needs only `MVDesign.main_of_three` with (2) and (3) — the deferred
assembly.

### Addendum 110: **`Main` is closed** — `MasurVeech/MainTheorem.lean`: a.e. unique ergodicity of interval exchange maps

Author's instruction ("close Main now that you have (1), (2) and (3)").  Done.

```lean
theorem masurVeech_ae_unique_invariant {α : Type*} [Fintype α]
    (n : ℕ) (hn : 2 ≤ n) [NeZero n] (P : CombData α n) (hP : P.Admissible) :
    ∀ᵐ lam ∂(simplexVolumeOn α), ∃! μ : ProbabilityMeasure ℝ,
      Invariant μ (P.toIET lam) ∧ (μ : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1
-- #print axioms: [propext, Classical.choice, Quot.sound]
```

The proof is `MVDesign.main_of_three P hP hn (Statement1Done.statement1 P hP hn)
(MVDesign.statement2 hn) (MVDesign.statement3 P hP hn)` — the three-statement design, all three now
theorems: (1) `Statement1Done.statement1`, (2) `MVDesign.statement2`, (3) `MVDesign.statement3`.

**One structural point, forced by the module graph**: `Main.lean` sits *below* the design — `Final.lean`
imports it (for `Invariant`) and `Design.lean` imports `Final` — so the proof cannot be written in
`Main.lean` without an import cycle.  The theorem therefore moved, **statement unchanged**, to
`MasurVeech/MainTheorem.lean` (above `Statement1Done`); `Main.lean` keeps `Invariant` and carries a
pointer.  Nothing else referenced the old name, and `Check.lean`'s `#print axioms` now reports the proved
version.

**Tidy-ups**: two stale docstrings corrected (`Check.lean`'s axiom-report header still said "the main
statement depends on `sorryAx` at M0"; `Basic.lean`'s `simplexVolumeOn` note said `simplexVolume_map_perm`
was "still a `sorry`").

**Final state of the tree**: `lake build` green at **8818** jobs; **no `sorry` anywhere** (no
`sorryAx` in any `#print axioms`); every headline of the axiom report (now the single line of
`MainTheorem.lean`) is `[propext, Classical.choice, Quot.sound]`.

**How the campaign got here** (route, for the record): (1) was reached through **`easyyoccoz.tex`**
(AGY Appendix A) — base case and `Γ₁` (`Statement1Graded.lean`), `Γ₂` (`Gamma2Mass.lean`,
`GrowthSlot.lean`), `Γ₃` (`FirstWinG3.lean`, `BlockedPhase.lean`, `OutsideGraph.lean`,
`SingleOutsider.lean`, `UncleanCore.lean`), `Γ₄` (`DichotomyG3.lean`) — and then the reduction
`simpleyoccoz → (1)` (`Statement1Assembly.lean`).  Three printed arguments had their hole in the same
place (Yoccoz §4.4's last paragraph, Kerckhoff's Prop 1.5, AGY's `Γ₃` line); the `Γ₃` hole is closed by
the author's correction (Kerckhoff on the prefix) plus the potential `S = Σ_{b∈A'} st b`, which contracts
on the non-exit branches at every non-blocked node while `not_blocked_of_noExit` shows no blocked node is
reached before the stop.

### Addendum 111: dead code pruned — 29 modules not used in the derivation of `Main`

Author's instruction.  Analysis: the import closure of `MasurVeech/MainTheorem.lean` (plus
`MainCounterexample`, kept as the justification of the statement's shape) is **82 of 111 modules**.
The other 29 were **moved** — not deleted, because this repository has no commits and nothing would be
recoverable — to `.scratch/removed/`, with a full backup of the library as it stood in
`.scratch/bak/lib_before_prune.tar.gz`, and the list in `.scratch/removed/LIST.txt`.

**Removed (all from the two abandoned routes or superseded by the final proof):**
* *Yoccoz/blueprint route*: `BalancedCover`, `CylTreeReal`, `EnlargeInput`, `EnlargeStep2`, `ExitBoth`,
  `ExtData`, `Lemma2Uniform`, `Lemma4`, `Lemma5Bridge`, `MassShrink`, `NestedBounded`, `RealCylTree`,
  `UniformEnlarge`, `UniformProvider`, `CoverDataFalse`, `NestedCylinderCounterexample`,
  `NameInfiniteCounterexample`, `Obstruction`;
* *Route A / Kerckhoff route*: `BlockedGraph`, `GammaLambda`, `KerckhoffBlock`, `KerckhoffJumps`,
  `OutsideGraph`, `RaceLambda`, `RealMass`, `Transvection`, `Waiting`, `MassSum`, `Gamma3Refuted`.

**Kept although not needed by the main theorem**: `MainCounterexample` (it is why the statement
carries `μ (Ico 0 1) = 1`) and the axiom report (now the single `#print axioms` line of
`MainTheorem.lean`).

**Repairs needed by the pruning**: the umbrella `MasurVeech.lean` lost 29 imports, the axiom-report
file (since folded into `MainTheorem.lean`) lost 27 imports and 109 `#print axioms` lines referring to
removed declarations (removed mechanically until it compiled), and four stale docstring references were
redirected (`Final.lean`, `ColDiam.lean`, and two more).  The docstring of the module holding
`Invariant` was rewritten: it described the abandoned shrink route, and now says only what the module
contains and where the theorem lives.

**Verification after pruning**: `lake build` green at **8789** jobs (was 8818); 82 modules; **no `sorry`
anywhere**; `masurVeech_ae_unique_invariant` still depends on exactly
`[propext, Classical.choice, Quot.sound]`; the axiom report is clean.

**Note for release**: among the removed files are the machine-checked *refutations* (`Gamma3Refuted`,
`CoverDataFalse`, `Obstruction`, `NestedCylinderCounterexample`) and the Kerckhoff evidence
(`KerckhoffBlock`, `KerckhoffJumps`, `RealMass`, `Transvection`).  The author's convention has been to
keep such refutations as release evidence; they are one `mv` away in `.scratch/removed/` if wanted.

### Addendum 112: declaration-level pruning — 823 declarations and 13 more modules

Author's instruction ("you can build a dependency graph of the declarations").  Method, so it can
be re-run: a `run_cmd` script (`.scratch/orch/graph2.lean`) dumps, for every constant of the
library, `ci.type.getUsedConstants ++ (ci.value? (allowOpaque := true)).getUsedConstants`.  The
earlier attempt had failed (`reachable: 41` of 4039) because `ConstantInfo.value?` returns `none`
for *theorems* unless `allowOpaque := true`; with the flag the graph is exact: 4039 constants,
proof terms included, not just statements.

Roots: `masurVeech_ae_unique_invariant`, `MainCounterexample.not_existsUnique`, `Invariant`, plus
three corrections for dependencies that a proof term cannot record:

* every declaration carrying an attribute (`@[simp]`, `@[ext]`) is a root — an `rfl`-proof simp
  lemma does not occur in the proof terms that use it, so its liveness is invisible to the graph;
* the `CoeFun (IET a b)` instance (used by elaboration only, likewise invisible);
* a declaration is deleted only when it *and all the constants Lean generates for it*
  (`Foo._proof_1`, `Foo.eq_1`, `Foo.congr_simp`, …) are dead, because a live companion keeps the
  parent alive; conversely every dependency of a *kept* declaration is kept (a fixpoint).  Without
  that fixpoint the pass does not compile (e.g. `Apriori.Extension.StopWord` was kept while
  `Apriori.Extension.Straddle`, which it mentions, was deleted).

Result: **823 source declarations** deleted from 56 of the 69 modules; 4039 → 2376 constants;
42 367 → 23 490 lines (45 %).  **13 modules have no live declaration at all** and were moved to
`.scratch/removed/` (`LIST.txt` now has 42 entries): `Gamma3TwoLetters`, `BlockedExtension`,
`FirstWinG3`, `BlockedPhase`, `SingleOutsider`, `TwoLetters`, `BalancedOne`, `MassTelescoping`,
`BalanceInterface`, `MainReduction`, `Lemma2Diameter`, `HrayAssembly`, `Final`.  Heaviest
single-module losses: `Lemma2Real` (72 % of its lines), `TowerQ` (67 %), `RaceTwo` (63 %),
`AssembleG3` (59 %), `NestedCylinder` (50 %), `ExtensionG2` (49 %), then `CutSetMeasure`,
`TowerLevelN`, `Gamma2Mass`, `AssemblyPieces`, `BalancedSet`, `CutSet`, `GrowthSlot`.

Verification:

* `lake build` green at **8776** jobs (was 8789);
* `masurVeech_ae_unique_invariant` still depends on exactly
  `[propext, Classical.choice, Quot.sound]`;
* **nothing was edited, only removed**: every surviving declaration's source text is byte-identical
  (modulo blank lines) to the pre-prune file, and every line of the pruned files is a line of the
  pre-prune file (subsequence check).  Tooling: `.scratch/orch/pipeline.py` (`scan.py`,
  `cleanup_mod.py`) run against the backup `.scratch/bak/predecl/`;
* the constants of the pruned library were compared with the planned live set: the only differences
  are 23 generated auxiliaries (`Foo._proof_1_2`, `Foo.congr_simp`, …) that were renumbered and
  their 4 replacements;
* the axiom report then audited 157 declarations (was 338); the lines referring to deleted
  declarations and the imports of the moved modules were gone.

Repairs the pass needed (traps for the next one): `MasurVeech.Design`, `MasurVeech.UncleanCore` and
`MasurVeech.ExtensionG2` were importing a *live* module only through one of the moved dead modules
(`Final` → `Main` for `Invariant`, `BlockedExtension` → `ExtensionG2`, `BlockedExtension` →
`PairReach`); they now import what they use directly.  `MasurVeech.TowerQ` had lost its import line
and needs `FirstReturn` and `TowerLevelN`.  `Cor4.lean` declares a `CombData.Path.Q_nonneg` that also
exists in `CylinderVolume.lean` under the same name — the two modules must not be imported together
(this is why `Cor4` predates a different `Q_nonneg` and why the name appears once in the graph).

Documentation: the module docstrings of the heavily pruned files were rewritten to describe what is
left (`Lemma2Real`, `TowerQ`, `NestedCylinder`, `RaceTwo`, `GrowthSlot`, `TowerLevelN`,
`BalancedSet`, `CutSetMeasure`, `Gamma2Mass`, `ExtensionG2`, `AssembleG3`, `AssemblyPieces`,
`AssemblyRepair`, `RauzyPath`, `RayPath`, `RayPointwise`); `Gamma3Race`'s "repair of the statement"
section now records only the three design conventions it documents.  Where a docstring was written
before the imports it was moved after them and marked `/-!`.

Left open, for the author:

* **175 docstring references to removed declarations** remain in *individual* declaration
  docstrings (inventory `.scratch/orch/docstale.json`, from the backticked names in `/--` comments);
  they read "see `foo`" / "proved by `foo`" and need removal or rewriting.  Module docstrings are
  clean.
* `MasurVeech/lakefile.toml` still sets `warn.sorry = false`, with the comment "a spike: `sorry` is
  expected at M0".  With no `sorry` anywhere that should probably go, so that a future `sorry` is
  loud; not changed here because the lakefile is the author's.
* 1331 weak-linter warnings remain (header shape, `longLine`, `show` usage); they are pre-existing
  — the pruning added none, and moving sixteen module docstrings behind the imports removed 249 of
  them.  In particular 32 of the 69 files have no copyright header, and many put the module
  docstring before the imports; both are pre-existing.
* 14 modules are now very small: `GrowthSlot`, `LevyRecurrence`, `PosBlocks`, `RaceTwo`, `TowerQ`
  (1 declaration each), `LengthInjective`, `NestedCylinder`, `RayCriterion`, `RayPath`, `TowerGlue`
  (2 each), plus `MainTheorem`, `Statement1Done` (1 each) and the axiom report (0: it is the report).
  Merging them is a separate decision.

**Also in this pass** (after Addendum 112 above was written): five docstrings that still claimed a
`sorry` were corrected — `Affine.lean`'s `chartVolume_map_perm` (which said the root-namespace name
was "`sorry`ed"; there is only one `chartVolume_map_perm`, at the root, and it is proved),
`Affine.lean`'s `map_reindex_eq`, `Step.lean`'s module docstring ("the proofs are `sorry` here"),
`Volume.lean`'s module docstring, `MainTheorem.lean`'s pointer to the then separate `Invariant`
module; and the seven duplicate `#print axioms` lines of the report were removed (157 → 150).  Build still green at 8776 jobs,
`masurVeech_ae_unique_invariant` still `[propext, Classical.choice, Quot.sound]`; 1385 source
declarations and 23 479 lines remain (from 2512 declarations and 42 367 lines).

The residual docstring inventory is written out as `results/docstring-references-to-removed-declarations.md`
(139 occurrences in 34 files after the module-docstring rewrites; 175 before them).

### Addendum 113: `IETFree` pruned to the proof of `main` — 51 declarations

Author's instruction: remove every declaration of `IET2/IETFree` that is not used in the proof of
`main` (`IET2/IETFree/ChallengeWeakSolved.lean`); the root files of `IET2/` and `IET2/Comparator/`
are not to be touched.  So no module was moved or removed (the umbrella `IETFree.lean` and
`Build.sh`'s hard-coded module list, both root files, stay as they are): only declarations inside
`IETFree/*.lean`.

Method: the same constant-level dependency graph as for `MasurVeech` (Addendum 112) —
`.scratch/orch2/graph.lean` dumps, for every `IETFree.*` constant,
`ci.type.getUsedConstants ++ (ci.value? (allowOpaque := true)).getUsedConstants` (2039 constants;
36 without a value, the structures/inductives).  Roots: `main`, plus every declaration carrying an
attribute (`@[simp]`, `@[ext]`, …) and every coercion (`coe_*`, `instCoe*`), which Lean can need
without their terms recording it; a declaration is deleted only when it and all the constants Lean
generates for it (`Foo._proof_1`, `Foo.eq_1`, `Foo.congr_simp`, …) are dead, and every dependency of
a kept declaration is kept (fixpoint).  Two rfl-proof lemmas used in explicit `simp only` lists
(`scalePerm_apply`, `scalePerm_symm_apply`) were caught by the textual audit and kept.

Result: **51 declarations** (715 lines) deleted from **16 of the 31 modules**; the other 15 modules
are untouched.  2039 → 1961 constants, 20 130 → 19 221 lines.  The largest removals:

* `IET.lean` — the minimal-cut-set API (`cutSet`, `cutSet_isCutSet`, `cutSet_subset`,
  `cutSet_comp_subset`, `card_cutSet_le`, `exists_card_cutSet`, `IsIET.cutSet_isCutSet`,
  `IsIET.mono`, `IsCutSet.eq_mkIETEquiv`, `isIET_iff_exists_mkIETEquiv`, `leftEnd_le`,
  `leftEnd_le_total`, `upperEnd_nonneg`);
* `TranslationVector.lean` — the `latticeDisp_gen` / `latticeDisp_list` chain and
  `exists_lattice_displacement`, `mkIETFun_sub_eq_sum`;
* `Centralizer.lean` — the formalisations of P2 and P4 (`FreeGroup.isReduced_flatten_replicate`,
  `FreeGroup.toWord_mk_pow`, `List.commute_eq_replicate`, `List.commute_eq_replicate_aux`), plus
  `FreeGroup.invLetter`, `isCyclicallyReduced_iff_isReduced_append_self`,
  `FreeGroup.rotate_cyclically_reduced`;
* `ReductionData.lean` — `ae_goodParams`, `coeffs_eq_of_good`, `coeffs_zero_of_good`,
  `measure_zero_of_forall_exists_isOpen_null`, `IETDatum.eq_of_notMem`;
* `Reduction.lean`'s dependencies — `pairSplitting_mem_markedList` (`BlockRescaling`),
  `paramMeasure`, `blockLen_simplexMap`, `ae_exists_of_countable` (`BlockEndpoints`),
  `gLenAffine`, `gLenAffine_eq` (`BlockDiophantine`), `GoodRegion.genY_mul_genX_ne_one`,
  `ae_exists_goodRegion`, `GoodRegion.sum_sub_mul`, `Equiv.IsIET.tiling` / `tiling_disjoint`
  (`CutSet`), `IsCutSet.inter` and `IsCutSet.locallyTranslationAt_of_not_mem` (`CutSetMeasure`),
  `IsIntAffine.smul` (`IntegerAffine`), `listLen` (`Presentation`), `IsFiniteUnionIntervals.empty`
  (`MeasureTools`), `RestrictIET.leftEnd_truncatedLengths*` (`InvariantInterval`), `Private`
  `BlockIn` (`BlockAssembly`).

`paramMeasure` was the last survivor of the list of "unused, wait for the author's decision" in
Addendum 96; the instruction settles it.  The `SumForm` route, `ae_irreduciblePerm_blockPerm` and
`IsCompPresentation.toIsCutSet` are no longer in the tree at all.

Verification (all of it re-run after the docstring pass):

* `./Build.sh` green: 32 modules, `IETFree.lean`, and `Comparator/Check.lean` all `ok`; no errors;
* the comparator guard still accepts the pair — "declarations compared: 32661", solution axioms
  `[Classical.choice, Quot.sound, propext]`, "the comparator would accept this pair";
* the library still has **no `sorry`**: the 6 `sorryAx` warnings are the 3 statements of
  `Challenge.lean` and the 3 of `ChallengeWeak.lean`, both untouched;
* nothing was edited, only removed: every surviving declaration's source text is byte-identical
  (modulo blank lines) to the pre-prune file, and every line of the pruned files is a line of the
  pre-prune file (subsequence check).  Tooling: `.scratch/orch2/pipeline.py` (scanner shared with the
  `MasurVeech` pass);
* `IETFree/Check.lean`: the 18 `#print axioms` lines naming removed declarations were dropped
  (296 → 278); the 11 of `ChallengeWeakSolved.lean` are kept.

Documentation: the 37 docstring references to the removed declarations were fixed (module docstrings
of `BlockData`, `BlockDatum`, `BlockDiophantine`, `BlockEndpoints`, `Centralizer`, `CutSet`,
`CutSetMeasure`, `GoodRegion`, `IET`, `IntegerAffine`, `Reduction`, `ReductionData`,
`TranslationVector`), and the section headers that the deletions had emptied were repaired
(`BlockAETransfer`'s "abstract measure-theoretic step", `BlockDatum`'s "Lemma 3.4" note,
`BlockEndpoints`' "parameter measure", `Centralizer`'s Parts B and C, which now record that their
lemmas are no longer in the tree).  One deliberate mention of a removed name remains, in
`Centralizer`'s note on Parts B and C.

Left open: `IET2/lakefile.toml` (root file, untouched) still sets `warn.sorry = false`; with no
`sorry` in the library that should probably go, so that a future one is loud again.

**Recoverability and integrity.** The pre-prune sources are `IET2.zip` (its 31 `IETFree/*.lean` files
totalling exactly the 20 130 lines the tree had, and containing all 51 deleted declarations); a copy is
extracted at `.scratch/bak/iet2_predecl/`.  Checked against that snapshot, every surviving declaration
in `IETFree/` is textually identical to its pre-prune version except for the docstrings of
`GoodRegion.mem_pairSplitting`, `SingularityShape` and `ae_goodParams_real`, which named a removed
declaration and were reworded — no statement and no proof changed anywhere.

**Integrity, final state** (supersedes the paragraph above).  Compared with the pre-prune snapshot
(`IET2.zip`, copied to `.scratch/bak/iet2_predecl/`): the **12** files with no deletion are
byte-identical (`BlockAETransfer`, `BlockIrreducibility`, `BlockLemma`, `ChallengeWeakSolved`,
`Commensurable`, `Diophantine`, `GeneratorChange`, `Irreducible`, `LengthMap`, `SingularityBound`,
`SingularityList`, `SubintervalTransfer`); `Check.lean` (18 `#print axioms` lines dropped), and the
module docstrings of `BlockData` and `Reduction` (stale references) are the only edits outside the 16
pruned files.  `ChallengeWeakSolved.lean` — the file that carries `main` — is byte-identical.  In the
16 pruned files every surviving declaration's statement and proof is unchanged; only the docstrings
that named a removed declaration were reworded.  Final build: `./Build.sh` green (34 `ok`), comparator
"would accept this pair" (32 661 declarations compared), library `sorryAx` count 0.

One number above needs correcting: the final line count of `IET2/IETFree` is **19 228** (not 19 221) —
715 lines of deleted declarations, the rest being blank lines collapsed in the 16 pruned files (the
`clean()` pass; the untouched files were restored byte-identically to the snapshot).

### Addendum 114: `MasurVeech` docstrings cleaned of the removed declarations

Follow-up to Addendum 112 (the MasurVeech pruning), asked for explicitly.  Addendum 112 left 139
references to removed declarations in individual docstrings, inventoried in
`results/docstring-references-to-removed-declarations.md`; all of them are now treated.

**What was done.**  The audit was re-run after each batch (`.scratch/orch/stale.py`, comparing the
pre-prune and post-prune constant dumps), which is what makes the result checkable:

* module docstrings rewritten to describe the files as they are — `Gamma3Core` (the mass calculus of
  `Γ₂`/`Γ₃` with the sections renumbered 1–5), `DichotomyG3` (Kerckhoff summed over a letter set,
  the `k → k+1` dichotomy, the single-letter case), `IET`, `Basic`, `Apriori`, `Nesting`,
  `RauzyReach`, `SimplexAe`, `Gamma4`, `CylinderRecurrence`, `PosBlock`, `Affine`, `Gamma3Race`,
  `GrowthSlot`, `Gamma2Mass`, `RauzyPath`, `ExtensionG2`, `AssemblyPieces`, `AssemblyRepair`,
  `AssembleG3`, `CutSet`;
* declaration docstrings that pointed at a removed lemma were reworded to state the fact without the
  pointer (the counterexamples `not_ae_mem_simplexOn_*`, `cxP_sharp`, `not_goodFirst_nil`,
  `sum_badFirst_level_zero`, `diam_simplexCyl_le`, `ncol_append_eq`, `rvType`, `multOne_eq_rvMat`,
  `cellN_succ`, `firstReturn_eq_rvStep`, … are gone; the mathematical claims they supported stay);
* sections emptied by the deletions were removed — 37 empty headers in `Check.lean`, 29 elsewhere —
  and prose-only sections describing removed material were deleted or cut to a remark
  (`Gamma2Mass` §5–§8 merged into one closing note, `ExtensionG2` §3–§9 dropped, `GrowthSlot`
  §1–§3 dropped, `Centralizer` Parts B/C replaced by a note saying their lemmas were removed);
* `Check.lean` now reads as the axiom report of the *current* library: the 150 `#print axioms`
  lines grouped under headers that have content.

**Re-measured**: 0 stale references in 34 files (was 139), `lake build` green at 8776 jobs,
`masurVeech_ae_unique_invariant` still `[propext, Classical.choice, Quot.sound]`; `MasurVeech/`
goes from 23 479 to 23 054 lines, all of it docstring and section-header material — **no
declaration, statement or proof changed**.  Two slips of my own were caught by the same audit and
fixed (`PacketB.inducedMap_injective_of_matrix` and `IsCutSet.eq_mkIETFun`, names I had written that
do not exist).

### Addendum 115: `MasurVeech` renamed for a public API, and the axiom report reduced to one line

Three instructions from the author: rename `CombData` to `IETDatum₂`; give the declarations names
that refer to mathematics rather than to the discussion (Yoccoz, Appendix A, "Statement 1/2/3",
packets, `Γₙ`, `hinj`/`hray`); and drop every `#print axioms` except the one for the main theorem.

**The datum.** `CombData` → **`IETDatum₂`** (1803 occurrences, 57 files, plus the two instances
`instFintypeCombData`/`instDecidableEqCombData` → `IETDatum₂.instFintype`/`instDecidableEq`).  The
name says what it is: two bijections to `Fin n` instead of the single `IETDatum` of `IET2`.

**The three statements of the main theorem** (they were `MVDesign.Statement1/2/3`, and the `MVDesign`
namespace is gone):

* `Statement1` → **`RichGreedyPath`** (a.e. the greedy path visits a prescribed vertex and then follows
  a prescribed word at arbitrarily late times), proved as `RichPath.richGreedyPath`;
* `Statement2` → **`UniformPositivity`** (one constant bounds the entries of a positive Rauzy matrix
  reachable from every admissible vertex), proved as `uniformPositivity`;
* `Statement3` → **`PositiveBlocksRay`** (positive blocks with a fixed entry bound at unbounded times
  give the ray condition), proved as `positiveBlocksRay`;
* `main_of_three` → **`main_of_components`**, `hray_of_three` → `rayCondition_of_components`, and the
  two a.e. steps keep `hasPositiveBlocks_ae`; `MVDesign.RayCondition` → `RayCondition`.

**Namespaces** (all declarations renamed with them): `Apriori` → `NodeHeight` (the height
functionals), with its parts split off as `Stopping` (level words, stop events, good/bad words),
`HeightDichotomy` (Kerckhoff summed over letters, the `k → k+1` dichotomy, the single-letter case),
`LargeLetter` (the `Γ₄` step), `LevelMass` (level-`N` masses, fibres, the covering bound), `Potential`
(the `A'`-sum potential argument), `MinimalExit` (blocked/exit words, the minimal exit);
`AppendixA` → `CylinderMass`; `S1` → `RichPath`; `Statement1Done` → `RichPath`;
`PacketB` → `AffineVolume`, `PacketP4` → `MeshShrink`, `PacketP9` → `RegionVolume`,
`PacketP10` → `BalancedCylinders`; `InjTower` → `TowerInjectivity`; `Gamma2Mass` → `MinimalExitMass`;
`Lemma2Real` → `BoundedSimplex`; `GrowthSlot` → `MassGrowth`; `TowerQ` → `TowerCells`.

**Declarations**: `Apriori.Statement/StatementMin` → `NodeHeight.GradedStep/GradedStepMin` (and
`statement_succ/min/const_mono` → `gradedStep_*`); `SimpleYoccoz` → `GradedFull` (both copies),
`simpleYoccoz_iff_statement` → `gradedFull_iff_gradedStep`, `statement1_of_simpleYoccoz` →
`rich_of_gradedFull`, `statement1_of_InductionStep` → `rich_of_step`, `statement1_of_g3` →
`rich_of_straddleMass`; `G3Straddle`/`G3StraddleCard` → `StraddleMass`/`StraddleMassCard`;
`gamma4_abs`/`gamma4_words` → `LargeLetter.newLetter_bound`/`newLetter_words`;
`raceSmall_singleton`/`raceSmall_card_one` → `HeightDichotomy.singleton_mass`/`card_one_mass`;
`hinj_of_floors` and friends → `length_injective_of_floors` (… `_of_tower`, `_of_tower_of_floors`,
`_of_tower_of_tiling`); `balanceStep_of_g3`/`inductionStep_of_g3` →
`balanceStep_of_straddleMass`/`inductionStep_of_straddleMass`; in `Assembly.lean` the two hypotheses
`hray`/`hinj` are now `h_ray`/`h_inj`.

**Modules renamed** (23 files, umbrella and imports updated): `Apriori`→`NodeHeight`,
`AppendixA`→`CylinderMass`, `Gamma2Mass`→`MinimalExitMass`, `Gamma3Core`→`LevelMass`,
`Gamma3Race`→`Stopping`, `Gamma4`→`LargeLetter`, `DichotomyG3`→`HeightDichotomy`,
`ExtensionG2`→`MinimalExit`, `AssembleG3`→`InductionAssembly`, `AssemblyPieces`→`StraddleMass`,
`AssemblyRepair`→`MassFunction`, `UncleanCore`→`Potential`, `Statement1Assembly`→`RichPathAssembly`,
`Statement1Done`→`RichGreedyPath`, `Statement1Graded`→`GradedInduction`,
`Lemma2Real`→`BoundedSimplex`, `GrowthSlot`→`MassGrowth`, `RaceTwo`→`BadFirstStop`,
`Cor4`→`CylinderGrowth`, `Inj2`→`TowerInjectivity`, `Design`→`MainComponents`,
`TowerQ`→`TowerCells`, `Tw`→`TowerLevelOne`.

**Axiom report**: the 445 `#print axioms`/`#check`/`#eval` lines of the library are gone; what
remains is one line, `#print axioms masurVeech_ae_unique_invariant`, now placed at the end of the main
theorem's section of `MainTheorem.lean` (it lived for a while in a separate report module, deleted in
Addendum 119).  Since every declaration is used in the proof of the main theorem (that is what the
declaration-level dependency graph of Addendum 112 shows), this single check covers the library.

**Verification**: `lake build` green at 8776 jobs; the constant set is unchanged at 2376 (the pass is
pure renaming, no declaration added or removed); `masurVeech_ae_unique_invariant` still depends on
exactly `[propext, Classical.choice, Quot.sound]`; the docstrings were swept for the old names
(module docstrings rewritten where they spoke of "the campaign", "statement (1)", "packet", swarms or
`simpleyoccoz`).  The library goes from 23 054 to 22 399 lines, all of it `#print` and docstring
material.

### Addendum 116: `MasurVeech` reorganized into `RauzyVeech/` and `RauzyVeech/RichPath/`

Author's instruction: put everything on the Rauzy–Veech induction in a subdirectory (everything but
the main theorem and `IET.lean`), and inside it a further subdirectory with what is specific to the
proof of statement (1).  Directory names become Lean module names, which cannot contain `-` or a
space, so the directory is **`MasurVeech/RauzyVeech/`** (reading "Rauzy–Veech induction") and the
inner one **`MasurVeech/RauzyVeech/RichPath/`** (the richness of the greedy path, the statement
formerly called (1)).  No file was renamed by this pass; the umbrella `MasurVeech.lean` was rewritten
(sorted imports by directory, plus a module docstring that describes the layout) and every `import`
and every `MasurVeech/<File>.lean` docstring path was updated.

**Top level** — the statement and the interval-exchange API it is stated with: `MainComponents` (the
two hypotheses and their assembly), `Assembly` (uniqueness from the ray condition and injectivity),
`MainTheorem`, `MainCounterexample`, and `Basic`, `IET`, `CutSet`, `CutSetMeasure`.  This pass still
had ten modules: the definition of invariance and the axiom report each had a module of their own,
later merged into `Basic` and `MainTheorem` (see Addenda 119 and 120).

**`RauzyVeech/`, 41 modules** — the induction itself: `Step`, `Path`, `RauzyReach`, `RauzyPath`,
`PairReach`, `CylinderGrowth` (the diagram and the path matrices); `Volume`, `Affine`,
`CylinderVolume`, `BalancedSet`, `ChildVolume` (the volume of path cylinders); `ColDiam`, `PosBlock`,
`PosBlocks`, `Peel`, `MeshShrink`, `LengthInjective` (the normalised columns and their spread);
`RayCriterion`, `RayPath`, `RayPointwise`, `ClosureSimplex`, `BoundedSimplex`, `SimplexAe`,
`RefiningPartition`, `LevyRecurrence`, `CylinderRecurrence` (the ray criterion and its inputs);
`TowerLevel`, `TowerLevelN`, `TowerLevelOne`, `TowerCells`, `TowerGlue`, `TowerTiling`,
`TowerInjectivity`, `IterGlue`, `IterGlue2`, `TrueStep`, `FirstReturn`, `LevelN`, `Nesting`,
`NameInfinite`, `NestedCylinder` (the towers and their floors).

**`RauzyVeech/RichPath/`, 18 modules** — specific to the proof of `RichGreedyPath`: `NodeHeight`
(the height functionals of a node and the graded step), `CylinderMass` (the cylinder mass and
Kerckhoff's lemma), `Stopping`, `BadFirstStop` (level words, stop events, good/bad words),
`HeightDichotomy` (Kerckhoff summed over a letter set, the `k → k+1` dichotomy, the single-letter
case), `LargeLetter` (the `Γ₄` step), `LevelMass` (level-`N` masses, fibres, the covering bound),
`MinimalExit`, `MinimalExitMass`, `MassFunction`, `MassGrowth` (the minimal exit and the mass of `Γ₂`),
`StraddleMass`, `InductionAssembly` (the straddle-mass estimate and the assembly of the induction
step), `Potential` (the `A'`-sum potential, which closes `Γ₃`), `BoundedLag` (bounded lag at a balanced
node), `GradedInduction` (the graded induction of Theorem A.1), `RichPathAssembly` (`GradedFull` and
the reduction to the richness statement), `RichGreedyPath` (the unconditional proof).

**The separation is checkable**: in the module graph, the only module of `RichPath/` that is imported
from outside the subtree is `RichGreedyPath` itself, imported by `MainTheorem`; and the subtree only
reaches down into `RauzyVeech/` (`Peel`, `RauzyReach`, `BalancedSet`, `ColDiam`, `PairReach`,
`CylinderRecurrence`) and into `MainComponents` (which *states* `RichGreedyPath`).  So the proof of
statement (1) can be read, replaced or deleted as one unit.

**Verification**: `lake build` green at 8776 jobs, 69 modules in the three directories
(10 + 41 + 18), 22 399 lines, one `#print axioms` line, `masurVeech_ae_unique_invariant` still
`[propext, Classical.choice, Quot.sound]`.  The module-level dependency graph is unchanged by the move
(only the names of the modules changed), and stale docstring references to the old module names
(`Final.lean`, `Design.lean`, `UncleanCore.lean`, `FirstWinG3.lean`, `BlockedPhase.lean`,
`OutsideGraph.lean`, `SingleOutsider.lean`, `RaceTwo.lean`, `AssemblyPieces.lean`) were fixed.

**Also in this pass**: `MasurVeech/README.md` was rewritten — it still described the M0/M1 milestones,
listed a dozen `sorry`s (all proved since), used the old `CombData` name and an obsolete layout.  It now
states the status (proved, axiom `[propext, Classical.choice, Quot.sound]`), the three-directory layout
and the three ingredients of the proof.

## Audit fixes landed, in one pass (this session)

All the items of the audit report were implemented, in turn, except the one marked below.  Nothing
about a *statement* changed except the removal of five unused hypotheses (§3.4) and of two dead
lemmas; every other edit is a proof, a docstring or an interface lemma.

**§4.3 — the 7 `longLine` warnings are gone** (`CutSetMeasure:17`, `IET:12`, `Centralizer:150/449/450`,
`BlockEndpoints:440`, `BlockDatum:813`): the paragraphs are re-wrapped; `lake build` is now
warning-free again.

**§2.1 — two dead lemmas deleted**: `BlockEndpoints.coe_simplexMap_of_lt` and `coe_simplexMap_last`
(unused everywhere, superseded by `Presentation.simplexMap_of_lt`).

**§3.5 — `Check.lean` deduplicated**: 10 `#print axioms` lines occurred twice (278 lines, 268 distinct);
now **268** distinct, which is what `Build.sh --strict` covers.

**§3.4 — five unused hypotheses dropped** (`_`-prefixed, and provably unused by their own statements):
`image_point_mem`'s `_hx`, `mkIET1_restrict_invariant`'s `_hpos`, `image_Ico_add`'s `_h <`; the
`IsCutSet` API's `_hs` and `iterate_word`'s `_hsmall` are kept (API uniformity, paper fidelity).

**§3.3 — `Reduction.lean` is gone** (it had zero declarations): its Section 3 narrative is now a nested
list in `IETFree.lean`'s module docstring, its 16 imports are listed directly in `Check.lean`, and
`Build.sh` no longer compiles it.  **30 modules** now (8741 build jobs, 33 `ok` targets).

**§3.2 (owner's variant): `toFun` / `toIET` stay `def`s, with expansion lemmas, and the use points
rewrite instead of unfolding.**  Added `IETDatum.toFun_def`, `IETDatum.toIET_def` (ReductionData), and —
because the same defeq pattern occurred for the *coercion* of `mkIET1` and for `cellLen` —
`coe_mkIET1`, `mkIET1_eq_mkIETFun` (IET.lean) and `GoodRegion.cellLen_eq` (BlockEndpoints).
`toIET_apply` is now proved by rewriting with the first two instead of `rfl`, and the eleven
`:= rfl` unfoldings of `mkIET1` (BlockRescaling, Presentation, SingularityBound ×5,
ChallengeWeakSolved ×2, `isCutSet_mkIET1`), the four `rw [IETDatum.toFun, …]` / `simpa [IETDatum.toFun]`
sites and the two `change` / `show … from rfl` proofs (BlockDatum's `hE` and its `toFun` step) are all
lemma rewrites now.  Two `change`s remain and are *not* def-unfoldings: `BlockEndpoints:283` reshapes a
coercion (`mkIET1 (simplexMap …)` vs `IETDatum.ofMem …`) and `BlockDatum:138` restates the goal shape.
A dependent-motive trap: rewriting `G.cellLen hq` inside `mkIET1 (G.cellLen hq) G.ρ hsum` fails
(`hsum` depends on the rewritten argument), so such equalities are proved pointwise with
`mkIET1_eq_mkIETFun` and then `hlen`.

**§2.2 — the cast/indicator boilerplate in `BlockIrreducibility.lean` is gone**: the four
`have hsplit … rw [hsplit, sum_ite_one_mul …] rfl` blocks (46 lines) are now `simp only [ha_def,
Int.cast_sub, sub_mul, Finset.sum_sub_distrib, sum_ite_one_mul, imageLeft, leftEnd, Fin.lt_def]`
one-liners (10 lines).  The final `Fin.lt_def` is needed: the `with`-sums use `↑(π i) < ↑(π k)` while
`imageLeft` uses `π i < π k`.  **§2.3 partly**: the `hA`/`hB` coefficient bounds of the two relation
lemmas now cite three new lemmas (`abs_ite_sub_ite_le`, `abs_ite_add_ite_sub_ite_le`,
`abs_ite_sub_ite_sub_ite_le`); the third coefficient block (negated indicators, `:877`) and the
`t`-case-analysis tails were **not** shared — the two tails end in different conclusions, so factoring
them would be churn.

**§2.4 — light**: the three `BlockEndpoints` sites now use the existing
`GoodRegion.simplexMap_mem_simplex_fst/_snd`; the other ~57 occurrences of
`simplexMap_mem_simplex_fin` take a local `hreg`, not a `GoodRegion`, so those lemmas cannot apply.

**§2.5 — the `IsAddHaarMeasure` "simplification" is not one**: replacing the hand-built instance in
`SubintervalTransfer` by `inferInstance` fails (`failed to synthesize volume.IsAddHaarMeasure` for a
product type).  Reverted; the explicit instance stays.  The `r = 0` branch was left alone (§2.5(b)):
every alternative I tried was the same length.

**§3.1 — deliberately not implemented.**  Threading `BlockIdx` through the raw API would touch
`blockMass` (57 call sites), `blockLam` (73) and `blockPerm` (23) — ~150 sites — for no change in any
statement, while `BlockIdx` has 3 users.  Instead the two layers are now documented in `BlockIdx`'s
docstring (raw API unbundled, block-level statements bundled): if the owner wants the threading anyway,
it is a purely mechanical follow-up.

**Docs refreshed in the same pass**: `README.md` — 51 line anchors recomputed against the current tree,
the two links to the purge-deleted `ae_exists_goodRegion`/`ae_goodParams` fixed (the former removed from
the table, the latter renamed `ae_goodParams_real`), the `f : IET 0 1` span repointed at `structure
IET`, and the numbers updated (268 `#print axioms`, 30 modules, 19 593 lines, "every declaration" for
the linter); `formalization.yaml` — the deleted `ae_exists_goodRegion` dropped from `alignment`, and
32/30/33 modules, 268 axiom lines.  `README.md` now has 148 line links + 34 file links, all verified
against the current files.

**Verification of the final tree**: `lake build` — 8741 jobs, exit 0, **0 warnings**; `runLinter` passes
on `IETFree`, `Challenge`, `ChallengeWeak`; `./Build.sh` — **33 `ok`**, 0 warnings, comparator check OK
(32 661 declarations), `sorryAx: 6` (3 `Challenge` + 3 `ChallengeWeak`, library 0); the genuine
`Comparator/run.sh` re-run on the final tree (§"Audit fixes" above).

### Addendum 117: `MasurVeech` docstrings swept of the campaign's own vocabulary

Author's instruction: "Also rename the private/internal lemmas so no name or docstring mentions
Yoccoz or statement numbers, then rebuild and recheck the one axiom line."

**What the measurement said.**  Over the 2376 constants of `.scratch/orch/graph_final3.out`, no
declaration name contains `yoccoz`, `statement`, `packet`, `swarm`, `blueprint`, `campaign`,
`milestone`, `M0`/`M1`, `R<digit>.<digit>`, `G<digit>`, `Target`, `Cor4`, `Lemma<digit>` or
`Apriori` (the two apparent `hinj` hits are `LengthInjective`).  There is no `private` declaration
left in the library either.  So the residue was entirely in **docstrings**.

**What was removed** (docstrings only; §-structure of each file untouched unless said):

* internal document references: `blueprint.md` and every `§10.x` / `§3.2` / `Step 4` to it, the
  campaign ledger `IET2/NOTES.md` / `NOTES.md` / `REPORT.md` pointers, `.ultramath/<swarm>/…`
  provenance paragraphs, `results/statement-1-steps.md`, the `PROOF.md` file together with its
  paragraph numbers;
* registration codes of this campaign: `M0`, `M1`, `M1b`, `F2`, `R0.3`–`R0.4`, `R2.2`, `R3.6`,
  `R3.7`, `R4`, `R6.4`, `R7.3`, `G6`, `P6`, `P5`, `P9`, `P1`, `Packet A/C/E/F`,
  `Target A`, `Target 4`, and the step labels `S0`, `S2`, `S3`, `S5`, `S6`;
* swarm-side vocabulary: "swarm", "member m1/m2", "packet", "the campaign", "the design",
  "the tree"/"the tree's", "landed" (for *proved*), "slice 1/2", "piece A/B/C", "the next packet",
  "statement (1)" (now `RichGreedyPath`), "statement (3)" (now `PositiveBlocksRay`), the numbers
  `(1)`, `(2)`, `(3)` in section titles and bullet lists, and `S3 (i)`;
* source pointers that were a *local* file plus an appendix/theorem number: `Yoccoz, p. 14`,
  `Appendix A`, `Theorem A.1`, `Yoccoz/easyyoccoz.tex`, `.scratch/avg/…`, `Agy's`.  They read
  "the source" / "the source's distortion theorem" / "Lemma 1 of the source" now.  The authors'
  names are kept in `MasurVeech/README.md` only, which states the two sources bibliographically
  (J.-C. Yoccoz, *Continued Fraction Algorithms for Interval Exchange Maps: an Introduction* for
  the Rauzy–Veech part, and the distortion appendix of G. Avila, S. Gouëzel and J.-C. Yoccoz,
  *Exponential mixing for the Teichmüller flow*, for the graded induction) — a public README has
  to say what is formalised.  Say so if the name should disappear there as well: it is one line.
* three misleading leftovers of the previous pass: 24 empty `## Axiom report` / `## Axiom check` /
  `## Statement report` section headings (the `#print axioms` lines they announced are gone), and
  the sentences "Axiom-clean (`#print axioms` at the end)" and "`PairReach` itself is not proved
  here: see `NOTES.md`" (now: proved, in `MasurVeech/RauzyVeech/PairReach.lean`).

**Repairs made on the way, all text-only.**  Renaming the vocabulary exposed references that no
longer resolved, and they were fixed too: stale module paths left by Addendum 116
(`MasurVeech.Affine`, `MasurVeech.Volume`, `MasurVeech.FirstReturn`, `MasurVeech.SimplexAe`,
`MasurVeech.Stopping`, `MasurVeech.RauzyPath`, `MasurVeech.Potential`, `MasurVeech.InductionAssembly`,
now written as `MasurVeech/RauzyVeech/…/X.lean` paths), and dead declaration names in docstrings
(`SimpleYoccozLater`, `simpleYoccoz_iff_later`, `simpleYoccoz_mmin`, `simpleYoccoz_of_gamma3`,
`LargeLetter.Gamma3Mass`, `balanceStep_of_gamma3`, `statement_card_single`, `graded_of_cover`,
`cor4_of_pairReach`, `HrayAssembly.hray_of_shrink`, `ColConc.spread_le_diam`,
`ColShrink.tendsto_diam_iff_cols`, `Tower.ret_mem`/`ret_min`/`lam_eq_rvMat_mul`/`induced_invariant`,
`IterFalseP`, `multN`, `cellN`, `BlockedPhase`, `Main.masurVeech_ae_unique_invariant`, `pad`), each
replaced by the name that the 2376-constant graph actually has, or by a description when the
statement moved.  Four module headers described a **different file** and were rewritten to match
their contents, verified declaration by declaration:

* `RauzyVeech/ChildVolume.lean` ("Lemma 3 of the source, the volume of a child cylinder") — the file
  holds the region model of the simplex and the positivity of `volume_simplexCyl`; Lemma 1 is in
  `CylinderVolume.lean` and the child ratio (Lemma 3) is `BalancedCylinders.volume_append_mul` in
  `BalancedSet.lean`;
* `RauzyVeech/ColDiam.lean` — claimed a `ColConc.spread_le_diam` and the equivalence
  "diam → 0 ⟺ columns coalesce"; only the direction `diam_le_of_cols_close` is proved (plus
  `abs_sub_le_of_cols_close`, `tendsto_diam_of_cols_eventually_close`), and the header now says so;
* `RauzyVeech/LevelN.lean` — announced `IterFalseP` and the level-`n` formula `tower_formula_level`,
  neither of which is in the file (they are `TowerTrue.tower_formula_level_pathQ_any` in
  `TrueStep.lean`); the header now lists the five sections that are there;
* `RauzyVeech/TowerLevel.lean` — announced `Tower.induced_invariant` and `Tower.tower_formula_level`;
  the file has `tower_formula_one_step_mult` (`multOne`) and `image_Ico_tot`, and says so.

**Verification** (all run after the last edit):

* `cd MasurVeech && lake build` → **Build completed successfully (8776 jobs)**, same job count as
  before the sweep, exit 0;
* `.scratch/orch/graph2.lean` re-dumped (`.scratch/orch/graph_final4.out`): `TOTAL 2376 15`, and the
  constant set is **identical** to the pre-sweep dump `graph_final3.out` once the stale
  `_private.MasurVeech.X` prefixes of that dump are normalised to `_private.MasurVeech.RauzyVeech.X`
  — no declaration added, removed or renamed by this pass;
* `lake env lean ../.scratch/orch/finalcheck.lean` →
  `'masurVeech_ae_unique_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]`;
* `rg '^#print' MasurVeech` → one line, in `MainTheorem.lean` (then still in a separate report
  module);
* no `sorry`, `axiom`, `native_decide` or `maxHeartbeats` anywhere in `MasurVeech/`;
* 22 337 lines (was 22 399), 69 modules, 94 docstring lines over 100 characters (the last full build
  log before the sweep reported 112 `longLine` warnings), and every artefact word above re-checked
  by scanning only comment regions of the 69 modules.

**Not done, deliberately.**  The ~1029 `linter.style.header` warnings (missing or abbreviated
copyright/author headers on most modules) and the rest of the weak-linter noise are untouched: the
author has not asked for them, and `Potential.lean`, `InductionAssembly.lean` and `RefiningPartition`
still carry a header without an author line.  The stale-name repair above was driven by a spot audit
(backticked identifier → constant graph); a full statement-by-statement fidelity audit of all 69
module docstrings was not attempted, so a few prose descriptions elsewhere may still lag behind the
code they describe.

### Addendum 118: the main theorem for a single irreducible permutation (`mkIET1`)

Author's instruction: "Currently, the main theorem is written for datum with two permutations.  You
will also write a version with a single irreducible permutation, for `mkIET1`?  This should be a very
short proof if there is also suitable API to translate between `IETDatum₂` and `IETDatum` and
`mkIET1`.  If this API is missing, build it first."

**What was missing.**  `MasurVeech` has no `IETDatum` (a single-permutation datum): the
single-permutation side is the *copied* constructor `mkIET1 (lam : Fin n → ℝ≥0) (π : Equiv.Perm (Fin
n)) (h : ∑ i, lam i = 1)`, and `IETDatum₂` is alphabet-indexed.  So the missing API was the map
`Equiv.Perm (Fin n) → IETDatum₂ (Fin n) n`; the converse map already existed as `toIET_eq_mkIET1`.

**API added** (all in `MasurVeech/MasurVeech/Basic.lean`, section "The datum of a single
permutation"):

* `IETDatum₂.ofPerm π := ⟨π, Equiv.refl (Fin n)⟩` — the datum with `piBottom = id`;
* `ofPerm_piTop`, `ofPerm_piBottom`, `ofPerm_perm`, `ofPerm_lengthsInBottom` (`@[simp]`, all `rfl`);
* `ofPerm_admissible_iff : (ofPerm π).Admissible ↔ IsIrreduciblePerm π`;
* `ofPerm_toIET : (ofPerm π).toIET lam = mkIET1 lam π h` for `h : lam ∈ simplexOn (Fin n)`;
* `toEquiv_mkIET1 : (mkIET1 lam π h).toEquiv = mkIETFun lam π 0`, the `toEquiv` form of the existing
  `coe_mkIET1`.  This one is not cosmetic: inside `μ.map (mkIET1 …)` the coercion is already unfolded
  to `.toEquiv`, so `coe_mkIET1` does not match there.

Plus `simplexVolumeOn_fin : simplexVolumeOn (Fin n) = simplexVolume n` in
`RauzyVeech/Affine.lean`, which is `simplexVolumeOn_eq_map` at `piBottom = id`.

**The theorem** (`MainTheorem.lean`, right after `masurVeech_ae_unique_invariant`):

```lean
theorem masurVeech_ae_unique_invariant_perm {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    (π : Equiv.Perm (Fin n)) (hπ : IsIrreduciblePerm π) :
    ∀ᵐ lam ∂(simplexVolume n), ∀ (h : lam ∈ simplexOn (Fin n)),
      ∃! μ : ProbabilityMeasure ℝ,
        Invariant μ (mkIET1 lam π h) ∧ (μ : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1 := by
  have hmain := masurVeech_ae_unique_invariant (α := Fin n) n hn (IETDatum₂.ofPerm π)
    ((IETDatum₂.ofPerm_admissible_iff π).mpr hπ)
  rw [simplexVolumeOn_fin n] at hmain
  filter_upwards [hmain] with lam hl h
  rwa [IETDatum₂.ofPerm_toIET π h] at hl
```

`2 ≤ n` is kept, not derived: `IsIrreduciblePerm` is vacuous at `n ≤ 2` and the statement is false at
`n = 1` (`mkIET1 lam 1 h` is the identity).  One Lean trap, for the record: the proof argument of
`mkIET1` cannot be rewritten (`h : lam ∈ simplexOn (Fin n)` versus the expected `∑ i, lam i = 1`
breaks the dependent motive of `rw`), so `ofPerm_toIET` rewrites the `.toEquiv` form and closes the
last step by `rfl`, and the corollary rewrites `toIET` *into* `mkIET1`, never the other way.

**Verification**: `lake build` → 8776 jobs, exit 0; the constant graph goes from 2376 to **2387**
(+10 declarations and one auto-generated `IETDatum₂.Admissible.eq_1`), nothing removed;
`#print axioms` in a scratch file gives `[propext, Classical.choice, Quot.sound]` for **both**
`masurVeech_ae_unique_invariant_perm` and `masurVeech_ae_unique_invariant`.  The library still has
its single line, for the main theorem: the corollary is derived from it, so any axiom in the
corollary would already appear there — but note that the corollary is *not* covered by that one line,
which is why its own report was checked out of tree (`.scratch/single/check.lean`); add a second line
if you would rather have it in the library.  `MasurVeech/README.md` now mentions the second form and
`ofPerm`.  94 lines over 100 characters, unchanged.

### Addendum 119: the axiom-report module removed, the report moved next to the main theorem

Author's instruction: "Remove the file `Check.lean`, and include the check just after the main
theorem."

**What moved.**  The separate axiom-report module (18 lines: an import of `MainTheorem`, a note and
one `#print axioms`) is **deleted**; the `#print axioms masurVeech_ae_unique_invariant` line and its
explanatory note are now at the end of `main`'s section of `MasurVeech/MasurVeech/MainTheorem.lean`,
immediately after the proof of `masurVeech_ae_unique_invariant` and before the single-permutation form
(`MainTheorem.lean:55`).  The rationale is unchanged: every declaration of the library is used in the
proof of the main theorem (the declaration-level graph says so), so this one report covers the
library, and it now runs as part of every build of `MainTheorem`.

**Knock-on edits.**  `MasurVeech/MasurVeech.lean` no longer imports the report module and its layout
docstring no longer mentions one (`MainTheorem` is described as "the main theorem with its axiom
report").  `MasurVeech/README.md`: the report's row is gone from the file table, the
`MainTheorem.lean` row mentions the report, and the status paragraph says where the single check
lives.  Nothing else in the tree referred to the file (checked with a grep over the package), and the
references to it in Addenda 110–118 now point at `MainTheorem.lean`, as the author asked in the next
round.

**Verification after the removal**: `cd MasurVeech && lake build` → **8775 jobs** (one fewer module, 68
total), exit 0, and the build itself prints
`info: MasurVeech/MainTheorem.lean:55:0: 'masurVeech_ae_unique_invariant' depends on axioms:
[propext, Classical.choice, Quot.sound]`.  The constant-level graph is **unchanged at 2387**: the
deleted module contributed no declaration.  `rg '^#print' MasurVeech` → exactly one line, in
`MainTheorem.lean`.

## `Check.lean` replaced by a single axiom check (this session, owner's instruction)

`IETFree/Check.lean` is **deleted** (268 `#print axioms` lines, one per declaration).  What justifies the
library now is a single check, registered directly below the theorem it is about, at the end of
`IETFree/ChallengeWeakSolved.lean`:

```lean
-- The axiom check of the library: the single `#print axioms` of the tree, for the main theorem,
-- registered directly below it.
#print axioms main
```

It prints `'main' depends on axioms: [propext, Classical.choice, Quot.sound]` when
`ChallengeWeakSolved` is compiled (that module is imported by the umbrella, so `lake build` runs it).
The nine other `#print axioms` lines that the same file carried for its helpers
(`evalWord_toEquiv`, `ae_prod_of_ae_free`, `main_of_library`, …) went with the file's report, and so did
the one for `coe_mkIETEquiv`: the tree now has exactly one `#print axioms` (a docstring cannot precede a
`#print` command, hence the `--` comment).

Consequences wired through the tree:

* `IETFree.lean` no longer imports `IETFree.Check`; its docstring says that `ChallengeWeakSolved`
  carries the single `#print axioms main`;
* `Build.sh` no longer compiles `IETFree/Check` (32 targets now: the two statement files, 29 modules,
  and `IETFree.lean`); its "axiom report" section greps the `ChallengeWeakSolved` log for
  `depends on axioms`, and **`--strict` now greps that same log for `sorryAx`** — i.e. it fails iff
  `sorryAx` is reachable from `main`, which is the property the single check is for;
* `README.md`: the Status paragraph describes the single check instead of the report file, the layout
  table lost the `IETFree/Check.lean` row, `--strict` says "reachable from `main`", and the counts are
  **29 modules / 19 120 lines**;
* `formalization.yaml`: the two `Check.lean` passages rewritten (single check below `main`), and
  31/29/32 modules.

Verification on the final tree: `lake build` — 8740 jobs, exit 0, 0 warnings; `runLinter` clean on
`IETFree`, `Challenge`, `ChallengeWeak`; `./Build.sh` — 32 `ok`, 0 warnings, the single
`'main' depends on axioms: [propext, Classical.choice, Quot.sound]`, `sorryAx: 6` (3 + 3, library 0),
comparator check OK; `./Comparator/run.sh` accepts.

### Addendum 120: `Main.lean` removed (`Invariant` moved into `Basic.lean`), and the report's name out of the docs

Two instructions in one round: "remove the docstring references to `Check.lean` in NOTES and README so
nothing points at the deleted file", and "`Main.lean` is essentially useless.  Move its content to
another file (for instance the IET file) and delete it."

**`Main.lean` → `Basic.lean`.**  `Main.lean` held nothing but `def Invariant (μ : ProbabilityMeasure
ℝ) (f : IET 0 1) : Prop := (μ : Measure ℝ).map ⇑f = μ`, plus a module docstring (the "no hypothesis on
`lam`" and "the measure must live on `[0, 1)`" remarks).  The definition and those two remarks are now
the last section of `MasurVeech/MasurVeech/Basic.lean` ("Invariance of a probability measure"), and
`Main.lean` is **deleted**.  `Basic.lean` rather than `IET.lean`, which was the suggestion: `IET.lean`
is the **frozen verbatim copy** of `IET2/IETFree/IET.lean` (`Invariant` has no counterpart there, so
putting it in would break the one property that file has), and `Basic.lean` is the module that
"fixes the objects the rest of the development works with" — `Main.lean` itself said nothing may be
imported *below* `Invariant`, and `Basic` is below everything.

Knock-on edits: `MainComponents.lean` and `Assembly.lean` import `MasurVeech.Basic` instead of
`MasurVeech.Main`; the umbrella `MasurVeech.lean` lost the import and its layout docstring now
describes `Basic` as "the exchange data, the simplex and `Invariant`"; `MainTheorem.lean`'s
"lives here rather than in `Main.lean`, because that module sits below the assembly" now says
`Basic.lean`; `MasurVeech/README.md` lost the `Main.lean` row and its `Basic.lean` row gained
`Invariant`.  Nothing else in the tree imported or named the module (checked with a grep).

**The report's name out of the docs.**  Every reference to the axiom report in the *MasurVeech* part of
this ledger (Addenda 110–119) now names `MainTheorem.lean` — where the single `#print axioms` line
lives — instead of the deleted report module; so do the umbrella docstring, `MasurVeech/README.md`
(no `Check` string left in it) and `IET2/README.md` (which already described the IET2 report as the
single check below `main`).  The MasurVeech module list of Addendum 116 was rewritten to the current
top level (nine modules: `Basic`, `MainComponents`, `Assembly`, `MainTheorem`, `MainCounterexample`,
`IET`, `CutSet`, `CutSetMeasure`), with a note that the definition of invariance and the report each
had a module of their own at the time.  Deliberately **not** touched: the older entries of this ledger
that describe `IETFree/Check.lean`, the IET2 report file, which was deleted in the IET2 session and
whose deletion is recorded in the section "`Check.lean` replaced by a single axiom check" — those are
log entries about a file that existed then, not pointers to a live one.  Also untouched:
`blueprint.md`, which is the *plan* of the campaign (its module table lists planned files — `Return`,
`Balance`, `Shrink`, `UniqueErg`, `Main`, `Check` — none of which the finished library has), and
`results/docstring-references-to-removed-declarations.md`, a one-off report.

**Verification**: `cd MasurVeech && lake build` → **8774 jobs**, exit 0, **67 modules**, and the build
still prints `info: MasurVeech/MainTheorem.lean:55:0: 'masurVeech_ae_unique_invariant' depends on
axioms: [propext, Classical.choice, Quot.sound]`.  The constant-level graph is **unchanged at 2387**
with `Invariant` the only declaration that changed module (`MasurVeech.Main` → `MasurVeech.Basic`);
nothing else moved, so the two deletions removed no declaration at all.  94 lines over 100 characters.

## `set_option` hygiene: four left, all declaration-local (this session, owner's instruction)

The library had 14 `set_option`s, 12 of them **file-scoped** linter suppressions.  All 12 are gone and
the tree is still warning-free (`lake build`, 8740 jobs, 0 warnings).  Only four `set_option`s remain,
each `… in`-scoped to a single declaration and each with the comment that explains it.

**What the 12 were, and why none is needed any more**

* `BlockRescaling` / `GeneratorChange`, `linter.unusedSimpArgs`: the 12 BlockRescaling findings were all
  `Fin.val_mk` in `simp only [Fin.val_mk]; omega` (10 sites) plus two standalone
  `simp only [Fin.val_mk]` normalisation steps.  The linter is right that the *lemma* is unused — what
  those calls need is the beta/iota reduction, not the rewrite — so `simp only [Fin.val_mk]` became
  `simp only []` at all 12 places, which still reduces the `Fin` structures and leaves `omega`/`rw` the
  same goal.  (Deleting the call instead breaks the two standalone sites: checked.)
* `GeneratorChange`, `linter.unusedSimpArgs`: the two remaining findings are a **false positive**:
  `simp only [FreeGroup.lift_apply_of, genX, genY]` needs `lift_apply_of` — the `rw` before it reduces
  the *inner* `FreeGroup.lift … (FreeGroup.of i)`, and only the `simp only` (which unfolds `genX`/`genY`
  first) lets the lemma fire on the outer application; without it the goal stays unreduced and the proof
  fails (checked).  So this one is kept, as `set_option linter.unusedSimpArgs false in` on each of the two
  declarations, with a comment saying exactly that.
* `BlockData`, `BlockDiophantine`, `linter.unusedSectionVars` / `linter.unusedVariables`: **unnecessary** —
  removing them produced no finding at all.
* `BlockAETransfer`, `BlockData`, `BlockLemma`, `BlockDatum`, `linter.style.haveILetI` (7 sites after
  dropping the two redundant BlockDatum re-assertions): the linter asks for `have` in place of `haveI`
  when the class is a `Prop`.  It is right: all 11 `haveI`s of the library (`NeZero (l - k)`,
  `NeZero G.n`, `NeZero (i₁ - i₀)`, `Subsingleton (Fin r)`, and the two `haveI := hne`/`hι`) were
  replaced by `have`, and every proof still elaborates — the local hypothesis is still found by instance
  search, which is what the linter's message says.
* The two redundant `set_option linter.style.haveILetI false` lines in `BlockDatum` (`:625`, `:834`,
  no-ops after the top-level one) went first, as instructed.

The five comments that explained the *old* `haveI` choice (`BlockAETransfer`, `BlockLemma`,
`BlockDatum` ×3) and the `Fin.val_mk` comment in `BlockRescaling` were removed with them, since they now
describe code that no longer exists.  The stale `Fin.val_mk` comment in `GeneratorChange` (it had been
copied there but described the wrong linter finding) was replaced by the accurate one above.

**Left standing:** `SingularityBound.lean:175` (`maxHeartbeats 400000 in`, for `inv_translate_aux`) and
`:511` (`maxHeartbeats 800000 in`, for `list_main`), both already `in`-scoped with their `--` reason
line.  So the rule now holds: **no global `set_option` anywhere in the library**, and each of the four is
local to one declaration.

### Addendum 121: `Admissible` → `Irreducible`, and every `set_option` out of the library

Two instructions: "Rename `IETDatum₂.Admissible` to `IETDatum₂.Irreducible`, for coherence.  Check
throughout the library the names that use 'admissible' in this sense, and change them to
'irreducible'", and "remove all the `set_option` throughout the library, and fix the breakage".

**The rename.**  277 occurrences of the `admissib` stem in the 40 modules that use it.  Thirteen
constants were renamed (`Admissible` and its generated `eq_1`, `rvStep_admissible`,
`rvStep_admissible_true`/`_false` and its auxiliaries, `vertex_admissible`, `vertexNat_admissible`,
`ofPerm_admissible_iff`, `MeshShrink.Vs_admissible`), and every docstring now says "irreducible"
("admissible data", "admissibility is preserved", …).  The definition itself reads

```lean
/-- Irreducibility of the datum: no proper initial segment of the permutation is invariant (the
source's admissibility, 2.5). -/
def Irreducible (P : IETDatum₂ α n) : Prop := IsIrreduciblePerm P.perm
```

— the parenthetical in the module docstring and in that sentence are the *only* places where the
word "admissibility" survives, as a citation of the source's own terminology.  The frozen copied files
(`IET`, `CutSet`, `CutSetMeasure`) contain neither word, so nothing there changed.  `README.md`'s
`Basic.lean` row was updated.  Build green on the first try; the constant-level graph is unchanged
apart from the thirteen renames (2387 before and after).

**The `set_option`s.**  There were **154** of them in 53 of the 67 modules: `linter.unusedSectionVars`
(44), `autoImplicit` (38, redundant with `lakefile.toml`), `linter.unusedVariables` (18),
`linter.unusedFintypeInType` (17), `linter.unusedDecidableInType` (17), `linter.style.haveILetI` (12),
`linter.unusedSimpArgs` (3), `linter.style.show` (3), `linter.unnecessarySimpa` (2).  All are gone;
none was needed for the build to elaborate (`autoImplicit = false` is set project-wide in
`MasurVeech/lakefile.toml`, which is a Lake option, not a `set_option`; the remaining Lake options —
`relaxedAutoImplicit`, `maxSynthPendingDepth`, `weak.linter.flexible`, `weak.linter.mathlibStandardSet`,
`warn.sorry` — were left alone, and `warn.sorry = false` is still the "spike" leftover flagged
elsewhere).

Removing them re-enabled nine weak linters and produced **359** new warnings; all but fifteen are
fixed:

* **200 `omit [...] in` clauses** inserted (230 `omit` lines in the library now, counting the 30 that
  were already there), one per declaration that does not use a section variable in its type.  These
  are the `linter.unusedDecidableInType`/`unusedFintypeInType`/`unusedSectionVars` reports; an `omit`
  removes an *unused instance argument* from the declaration, which is what the linter asks for and
  what Mathlib does.  No hypothesis and no mathematical content changed — but note that ~200
  declarations now take one fewer instance argument, so their statements are *not* byte-identical.
  The insertion tool (`.scratch/orch/write_omit_lines.py`) computes all positions on the pristine file
  before inserting, and puts `omit … in` above the docstring and any `@[…]`, since a docstring may not
  be separated from its declaration by the modifier.
* **~20 `classical`** added at the start of proofs that used `DecidableEq` even though their statement
  did not (`classical` finds the instance through `Classical.decEq`; the linter's own hint).  One
  term-mode proof (`TowerTiling.length_injective_of_tower`) became `:= by classical exact …`.
* **59 `show` → `change`** (`linter.style.show`: the tactic changed the goal, so `change` is the right
  word), **6 `haveI` → `have`**, **13 unused binders renamed `_X`**, **3 unused `simp` arguments
  dropped**, **1 blank line** between a docstring and its theorem removed (`style.emptyLine`).
* **15 warnings left, deliberately**: 6 `unusedFintypeInType` + 4 `unusedSectionVars` +
  2 `unusedDecidableInType` are declarations whose *own* binder (not a section variable) is unused in
  the type — `map_reindex_eq`, `levy_recurrence`, `card_low_of`, `trans_insertEquiv_apply_val`,
  `continuous_coe_lengths`, `iUnion_comp_equiv`, `returnWord_spec`, `padWord_spec`,
  `upperEnd_le_leftEnd`, `card_ge_two`, `tot_eq_one`.  The linter's advice there is to *replace or
  remove a hypothesis* (`[Fintype α]` → `[Finite α]`, drop `[∀ n, Fintype (Y n)]`, …), i.e. to change
  a public statement; I did not do that silently.  The other 3 are `simpa using h` where the linter
  suggests `simp`, but `simp using h` does not parse in this toolchain — reverted to `simpa`.

**Verification**: `cd MasurVeech && lake build` → **8774 jobs**, exit 0, 67 modules, and the build still
prints `'masurVeech_ae_unique_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]`
(one `#print axioms` line, `MainTheorem.lean:54`).  Constant set **2387**, identical to the graph after
the rename; 95 lines over 100 characters (94 before: the one new one, a `change` line, was re-wrapped);
`rg 'set_option' MasurVeech` → nothing.

**Operational consequence**: with the per-file `set_option autoImplicit false` gone, checking a single
file with `lake env lean` needs `-DautoImplicit=false` explicitly (as had always been the case for
`lake env lean`, which does not read the lakefile); `lake build` is unaffected.

### Addendum 122: the last unused-binder warnings, generalised or omitted

Instruction: "do the fifteen remaining unused-binder warnings: generalise or drop the hypotheses, but
keep the public statements sensible".  Fourteen are gone; one is genuinely not removable.

**Unused section variables → `omit`** (no statement change; the declaration just stops taking an
instance argument it never uses): `Assembly.upperEnd_le_leftEnd`, `Assembly.disjoint_cellOf` and
`TowerInjectivity.tot_eq_one`, `Stopping.card_ge_two` (`[NeZero n]`), and `RauzyReach.returnWord_spec`,
`BoundedLag.padWord_spec` (`[DecidableEq α]`).  `disjoint_cellOf` had been hiding behind the same
warning as `upperEnd_le_leftEnd`; it appeared once the first was fixed.

**Unused own hypotheses → dropped, statements generalised** (five declarations; no hypothesis was
*added* anywhere):

* `Affine.map_reindex_eq`: dropped `[Fintype α]` — the proof only uses the two equivalences
  `e₁ e₂ : α ≃ Fin n` and `Measure.map_map`, never a `Finset`.  Its caller
  `simplexVolumeOn_eq_map` still passes `Fintype.equivFin α`;
* `Step.trans_insertEquiv_apply_val`, `Nesting.continuous_coe_lengths`,
  `TowerLevelOne.iUnion_comp_equiv`: dropped their `[Fintype α]` / `[Fintype β]` binder (unused in
  statement and proof; the insertion formula only needs `e : α ≃ Fin n`, the coercion lemma and the
  reindexing-of-a-union lemma need no finiteness at all);
* `MeshShrink.card_low_of` (in `NameInfinite.lean`): dropped `[Fintype α]` and recovered it *inside*
  the proof from the equivalence, with
  `have : Fintype α := Fintype.ofEquiv (Fin n) e.symm` — in Lean 4 a plain `have` registers a local
  instance, and `haveI`/`letI` would be flagged by the `haveILetI` linter.

**Not removable**: `LevyRecurrence.levy_recurrence` keeps `[∀ n, Fintype (Y n)]`.  The linter is right
that the *type* does not mention it (the statement is "if every atom carries a definite fraction
avoiding `Z` at every level, then `μ Z = 0`"), but the proof sums over the atoms of `Y n` in three
places, and dropping the hypothesis breaks exactly those three steps (tried).  Replacing it by
`[∀ n, Finite (Y n)]` would only move the same "unused in the type" report to the other linter, and
adding a finitary clause to the statement would change the theorem.  So the one surviving warning is
this one, and it is a case where the linter's advice is not implementable; the hypothesis is part of
the intended setting ("finite level maps", as the docstring says).

**The three `unnecessarySimpa`s** (`RichPath/Potential.lean`) were `simpa using …` where the `using`
term was redundant: `simp` alone closes the goal in all three, so the proofs now say `simp`
(`getD_append_singleton_len`, the two `take (γ.length + 1) = γ ++ γ` steps).

**Verification**: `cd MasurVeech && lake build` → **8774 jobs**, exit 0, 67 modules.  Remaining warnings
are only the pre-existing classes (`style.header` 703, `style.longLine` 104, `style.whitespace` 52,
`style.missingEnd` 3, `unusedTactic` 1) plus the single `unusedFintypeInType` on `levy_recurrence`.
Constant set **2387**, identical to before this pass (no declaration added, removed or renamed).  One
`#print axioms` line (`MainTheorem.lean:54`), still `[propext, Classical.choice, Quot.sound]`; 95 lines
over 100 characters, and no new long line compared with the pre-`set_option` snapshot.

### Addendum 123: the library is warning-free

Instruction: "Fix all the warnings: the long lines, the whitespace, the headers", with the exact header
text given.  `cd MasurVeech && lake build` now reports **one** warning in the whole library (the
`unusedFintypeInType` on `levy_recurrence` discussed in Addendum 122, which would need a statement
change), the build is green at **8774 jobs**, and the constant graph is unchanged (2387 constants, same
names *and* same modules — no declaration was added, removed or renamed by this pass).

**Headers (703 warnings → 0).**  Every one of the 67 modules now starts with the author's block:
```
/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
```
then the imports, then the module docstring, which is what `linter.style.header` asks for.  This
uncovered several distinct defects, all fixed:

* 19 files had no header at all (`MainCounterexample`, `BalancedSet`, …), and 13 more started directly
  with their module docstring (`MainComponents`, `ChildVolume`, `LevelN`, …); `Potential` and
  `InductionAssembly` had a three-line header with no `Authors:` line.  All headers are now the block
  above (the linter's remaining complaints — "Copyright too short", "do not end the authors' line with
  a period", "do not use 'and'" — were it reading the *docstring* as a header);
* 29 files had the module docstring **before** the imports; it is now the first command after the
  imports, as the linter requires;
* 18 module docstrings were plain `/- … -/` comments, not docstrings: they are `/-! … -/` now;
* `TowerInjectivity.lean` and `TowerTiling.lean` had **no** module docstring (only section headers): one
  was written for each, describing the injectivity of the length map and the a.e. tower tiling;
* `linter.style.missingEnd` (3): `BalancedSet`, `ChildVolume` and `MinimalExit` never closed their
  namespace — `end BalancedCylinders`, `end RegionVolume`, `end MinimalExit` added at the end of file.

**Long lines (104 → 0).**  85 were comment/docstring lines, re-wrapped; 19 were code lines, broken by
hand (`rw` argument lists, `have` statements, `⟨·,·⟩` constructors).  Two lessons: a tactic block after
`have h : … := by` must be indented *more* than the `have` keyword (a multi-line statement is fine as
long as the body is deeper), and `rw [a, b,\n  c]` needs its continuation lines at a consistent
indentation.  Then a second pass fixed the *raggedness* the first pass left (a word alone on a line):
42 lines joined, 70 docstring paragraphs re-wrapped to a clean 100-column fill.  The docstrings of
`RichGreedyPath`, `MainComponents`, `MasurVeech.lean` and the rest now read as properly filled
paragraphs.

**Whitespace (52 → 0).**  All were "missing space in the source", the linter's own snippet giving the
fix: `(0:ℝ)` → `(0 : ℝ)` in `Set.Ico` bounds, `(m+1)` → `(m + 1)` in `Fin (m + 1)` types.  The first
attempt aligned the two snippets as if they were a prefix/suffix diff and silently deleted characters
(`Set.Ico (0 : ℝ) :` instead of `(0 : ℝ) 1)`); the repair aligns them on their non-space characters and
replaces the corresponding span — a reminder that the linter's "this part of the code / should be
written as" pair is a *witness*, not an edit script.

**Small ones.**  `linter.unusedTactic` (1): a `push_cast` that did nothing, removed.  The `simpa using`
that `linter.unnecessarySimpa` flagged became `simp`.  `linter.style.emptyLine` (1): a blank line
between a docstring and its theorem removed.

**Verification**: `lake build` → 8774 jobs, exit 0, one warning; `rg 'set_option' MasurVeech` → nothing
(Addendum 121); one `#print axioms` line, `MainTheorem.lean:52`, still
`[propext, Classical.choice, Quot.sound]`; constant graph identical (2387).  Because the header rewrite
reorders the top of every file (header, imports, docstring), the diff of this pass is large but touches
no declaration.

**Post-script to Addendum 123.**  Two more clean-ups after the pass above: the *deprecated* `push_neg`
in `NameInfinite` became `push Not` (the replacement the deprecation message asks for), and an
`@[nolint unusedFintypeInType]` was tried on `levy_recurrence` to silence the last report — the `nolint`
attribute rejects that name ("linter 'unusedFintypeInType' not found"), so it was reverted.  The library
therefore carries exactly **one** warning, the `unusedFintypeInType` on `levy_recurrence`; every other
class is at zero (headers, long lines, whitespace, `missingEnd`, `unusedTactic`, `unusedSimpa`,
`unusedVariables`, `unusedSectionVars`, `unusedDecidableInType`).  Silencing it properly needs the
statement to change: either bundle the level types as finite (`Y : ℕ → FintypeCat`, which also touches
the single application in `RichPathAssembly.lean:327`, written `@`-style with positional arguments), or
state the atoms as a `Finset`-indexed hypothesis.  Both are one decision away.

### Addendum 124: `levy_recurrence` takes `[∀ n, Finite (Y n)]` — the last warning is gone

Instruction (verbatim): *"In levy_recurrence, use [\forall n, Finite (Y n)] and inside the proof
register fintype instances on Y n if needed using Finite.toFintype or whatever it is called."*

**The change** (`MasurVeech/RauzyVeech/LevyRecurrence.lean`): the binder
`[∀ n, Fintype (Y n)]` is `[∀ n, Finite (Y n)]` (line 45), and the theorem docstring (line 38) and
the comment above the namespace (line 30) say `Finite` too.  Nothing else in the file changed: the
proof body is byte-identical to the version that took `Fintype`.

**No instance had to be registered inside the proof.**  The proof consumed `Fintype (Y n)` only
through typeclass instances, and `Finite (Y n)` supplies all of them: `Countable (Y n)` (for
`measure_iUnion_null` over `⋃ y : Y n` and for the two `MeasurableSet.biUnion`s) and `Finite ↑s`
(for `Set.toFinite s` with `s : Set (Y n)`).  The name the instruction was unsure about is
`Fintype.ofFinite (α) : [Finite α] → Fintype α`; `Finite.toFintype` does not exist in this toolchain
(`Unknown constant`) — it was not needed, which also keeps the `haveILetI` linter quiet.

**The single application is unchanged.**  `RauzyVeech/RichPath/RichPathAssembly.lean:327` is still
`@LevyRecurrence.levy_recurrence (α → ℝ≥0) _ (c • simplexVolumeOn α) ⟨hprob⟩ CylRec.Word _ _ _ …`;
the third `_` now supplies `Finite (CylRec.Word k)`, derived from the existing
`noncomputable instance (k : ℕ) : Fintype (Word k)` (`CylinderRecurrence.lean:47`).  So the statement
change is invisible upstream, and since `Finite` is weaker than `Fintype` as a hypothesis the theorem
is *stronger* than before, with no other declaration's type touched.

**Correction to Addenda 122 and 123.**  Both predicted that switching to `Finite` "would only move the
same 'unused in the type' report to the other linter".  That is false, measured: the report is
`unusedFintypeInType`, which is about `Fintype`, and `Finite (Y n)` *is* used by the proof, so no
linter mentions the hypothesis any more.  The reasoning behind keeping `Fintype` was that three
summation steps need it — correct — but a weaker hypothesis that still provides those instances
satisfies both the proof and the linter.

**Verification.**  `cd MasurVeech && rm -rf .lake/build && lake build` (so the `emptyLine` linter cannot
be masked by an earlier diagnostic in the same file): **8774 jobs**, exit 0, all **67 modules** compiled
from source, `grep -c warning` over the whole log → **0** (`error` → 0 too), in 1 m 42 s.  So the library
is now warning-free in every class (header, longLine, whitespace, missingEnd, unused*,
unnecessarySimpa, emptyLine).  Single `#print axioms` at `MainTheorem.lean:52`, printing
`[propext, Classical.choice, Quot.sound]`.  The declaration graph was re-dumped both before and after
the clean rebuild (`.scratch/orch/graph_final11.out`, `graph_final12.out`, byte-identical) and is
byte-identical to `graph_final10.out` as well: `TOTAL 2387`, same names and same modules — no
declaration added, removed or renamed by this pass.  `rg set_option MasurVeech/` → nothing.  No line of
the changed file exceeds 100 characters (character count, not bytes: the Lean linter counts
characters, and the file is full of `π`, `μ`, `≥`).

### Addendum 125: two blueprints for the Birkhoff form (`MasurVeech/UniformConvergence/`), and what the source hides

Instruction (verbatim): *"We will improve this to the form needed in the directory IET2, see the file
ChallengeWeak.lean where the form we will be after is called MasurVeechFun … The new files will be part
of the project MasurVeech, in a subdirectory UniformConvergence. For this, we need two tools: (1) if a
homeomorphism of a nonempty compact space is uniquely ergodic, then the Birkhoff averages of continuous
functions converge uniformly to the average. (2) extending (1) to interval exchange transformations,
which are not continuous. You will write two detailed mathematical blueprints for these two tools …
on the top of page 55. The writing is quite terse here, so you will expand greatly the arguments."*

**No `.lean` file was touched, so there is no build to report.** What was produced is documentation:
`MasurVeech/UniformConvergence/{README.md,BLUEPRINT-1.md,BLUEPRINT-2.md}` (352 + 895 + 93 lines). The
Lean sources of the next round are planned as `MasurVeech/MasurVeech/UniformConvergence/*.lean`. The
existing README line "the Birkhoff-averages form is not formalised here" (`MasurVeech/README.md:67`)
and the deferred item D1 of `blueprint.md:853` are what this round is about.

**Tool 1** is the standard theorem (Oxtoby/Walters), proved in full, plus the *relative form* that
Tool 2 actually consumes: it suffices that every invariant probability measure supported on the closure
of the set of initial points gives the same integral. Minimality and invertibility are never used.
Mathlib already has everything except the assembly: `instCompactSpaceProbabilityMeasure`,
`tendsto_iff_forall_integral_tendsto`, `birkhoffAverage`, `ext_of_forall_integral_eq_of_IsFiniteMeasure`.

**Tool 2 — three corrections to the source paragraph, all recorded in Blueprint 2 §8.**

1. *"`T̃` is easily seen to be uniquely ergodic"* is **false**: `L a = a`, so the left germ of the left
   endpoint is a fixed point of `T̃` for every exchange (and it is isolated). The replacement is a
   transfer statement: with `ρ = proj_*ν` and `J` the finite jump set,
   `∫g dρ − ∫g d(T_*ρ) = Σ_{c∈J} ν{leftGerm c}(g(Lc) − g(Tc))`, and "mass is constant along a
   `T̃`-orbit" kills the defect *provided* (H2) below. The lift of `λ` is then unique because `proj` is
   injective off the countable split set and `λ` has no atoms (this is where atomlessness enters — the
   same point `blueprint.md:634` predicted for D1).
2. **(H2) = "the left-limit map `L` has no periodic point in `(a,b]`" is necessary, not cosmetic.** If
   `x₀ ∈ (a,b)` is `L`-periodic of period `k`, the maps `A_n = (1/n)Σ_{i<n}ψ ∘ p ∘ T̃^[i]` are continuous
   on the split space, `A_n(leftGerm x₀) → (1/k)Σ_j ψ x_j`, and `leftGerm x₀` is a limit of right germs;
   uniform convergence would force `(1/k)Σ_j δ_{x_j} = λ`, impossible. So the *pointwise* theorem needs
   (H2); the a.e. statement does not, because (H2) fails only on a countable union of hyperplanes.
3. *No* compactification carries a homeomorphism `T̃` with `p ∘ T̃ = T ∘ p` everywhere: at a cut `c` a
   net `y ↑ c` converges to the left germ of `c` while `T y → L c ≠ T c`. `T̃` is the **germ map**
   (right germs ↦ right germs of `T x`, left germs ↦ left germs of `L x`), and the semi-conjugacy holds
   on right germs only — which is all that is used. The split set must be the full orbit closure
   `⋃_{n∈ℤ}T^n(s ∪ s' ∪ {b})`: the source's one-sided unions coincide with it (`T s ⊆ s'`,
   `T⁻¹ s' ⊆ s`), but `{b}` has to be added (`b` is a left discontinuity).

The construction avoids the order topology: the space is a closed subspace of
`[a,b] × {false,true}^D`, which gives compact, Hausdorff, pseudo-metrizable and Borel from instances,
and continuity of `T̃` becomes a two-coordinate case analysis.

**Lemma 6.2, the one open point of the first version, is now proved.** It said: for `π` irreducible and
`0 ≠ m ≥ 0`, the functional `λ ↦ Σ_α m_α δ_α(λ)` is not identically zero (equivalently
`ker Ω^t ∩ ℝ_{≥0}^d = {0}`), which is what makes the exceptional set of (H2) a countable union of
*proper* hyperplanes. Proved in the round `.ultramath/smvz4odkr` (member `m3`, accepted; the three other
members were stopped): `c(m)_β = m(I_β) − m(π⁻¹(I_{πβ}))`, and if this vanishes with `m ≥ 0 ≠ 0`, the
least support element `f` satisfies `π f = min π(supp m)` (test (T) at `β = f`), then
`{β : πβ < πf} = I_{f−1}` (both directions from (T)), so cardinalities give `π f = f` and
`π(I_{f−1}) = I_{f−1}` — a proper invariant initial segment, against irreducibility; `f = 0` gives
`π 0 = 0`. Sharp form: for *arbitrary* `π`, a non-negative kernel vector exists iff there is such an
`f`, the converse being `m = e_f`. Real (not just integral) `m`, and `d ≥ 2` is used exactly at `f = 0`.

**Verification of that proof** (referee's own, independent of the member's scripts): the identity for
4000 random *signed rational* instances with `d ≤ 9`; the Lemma's full conclusion on all 4091 cases
with `c(m) = 0` for `d ≤ 6` including reducible `π`; Statement A exhaustively over irreducible `π` for
`(d,K) = (2,4),(3,4),(4,3),(5,3),(6,2)`; the sharp form over all `π` with `d ≤ 7`; 3000 random rational
trials. Zero failures throughout (`/tmp`-free: `.scratch/ref_swarm.py`, plus the member's
`.ultramath/smvz4odkr/m3/verify*.py`, which run clean).

**Open decisions, for the author.** (i) `UniqueErgodicFun`/`MasurVeechFun` are declared in
`IET2/ChallengeWeak.lean` against the `IET2/IETFree` copies; the plan copies both declarations verbatim
into `MasurVeech/UniformConvergence/Basic.lean` and proves `MasurVeechFun` there, `IET2` then copying
them or depending on `MasurVeech/`. (ii) Whether (H2) stays an explicit hypothesis of the pointwise
theorem (it is invisible in the a.e. form), or is to be replaced by "no connection".

### Addendum 126: (H2) is a theorem — a periodic left limit is a periodic interval

Instruction (verbatim): *"(H2) should not be needed: if an IET is uniquely ergodic, then it is
minimal, and then by Keane's condition it has no connection. Don't start on the formalization yet.
Instead, investigate if you agree with my argument. If you do, integrate it to the blueprint,
together with the proof of Keane's theorem that no connections is equivalent to minimality. A proof
of this is included in Yoccoz's notes."*

**Verdict: the conclusion is right, the argument is not, and there is a better argument.** No
`.lean` file touched; Blueprint 2 rewritten (§4.4 new, §5 unconditional, §6 demoted to an appendix,
§8.6 new, §9–§11 adjusted), README updated.

**Why the stated chain fails.** Keane's theorem is *not* an equivalence. Yoccoz, article p. 17
(PDF p. 30): Theorem 5.9 *(Keane) "If an i.e.m. has no connection, it is minimal"*, and immediately
below it Exercise 5.11: *"For d = 2, T is minimal iff there is no connection … For d ≥ 3, show that
there exists T minimal but having a connection, and also T with no connection but lengths data
rationally dependent."* So `minimal ⇒ no connection` is **false for d ≥ 3**, which is exactly the
range of `MasurVeechFun`; the argument uses Keane's theorem in the direction it does not have. The
first step (`uniquely ergodic ⇒ minimal`) is presumably true but its proof needs the structure
theory (minimal components are finite unions of intervals) plus the degenerate case `K ∩ J ≠ ∅`;
it is not written anywhere in the tree and, as it turns out, is not needed. And "no connection" is
not the property the transfer theorem needs: what it needs is "no periodic point of the left-limit
map `L`", which is strictly stronger than "no connection" (an `L`-cycle gives a connection).

**The argument that works (6 lines, elementary, new in §4.4).** Let `x₀ ∈ (a,b)` be `L`-periodic,
period `k ≥ 1`, `x_i := L^[i]x₀`. For `i < k` let `c_i` be the largest cut below `x_i` and
`ε := min_i (x_i − c_i) > 0`. Then `J_i := (x_i − ε, x_i) ⊆ (c_i, x_i]` contains no cut, so `T` is a
translation on `J_i`, by `δ_i`; and `x_i + δ_i = L(x_i) = x_{i+1}` by the explicit formula for `L`.
Hence `T '' J_i = J_{i+1}` **exactly** (indices mod `k`). So `T` permutes the `J_i` cyclically, each
`T|_{J_i}` being a translation: `λ|_K` for `K := ⋃_i J_i` is a `T`-invariant finite measure with
`λ(K) ≤ kε < 1`, and `T^[k]` is the identity on `J_0`. Hence `λ|_K/λ(K)` is a `T`-invariant
probability `≠ λ`, contradicting unique ergodicity. This is the classical "periodic orbits come in
families": a periodic left limit is a **periodic interval**. It gives `(H1) ⇒ (H2)` at every length
vector, needs no minimality, no Keane, no connections, no hyperplanes.

**What this removes from the plan.** `(H2)` is no longer a hypothesis of Theorem 2 (only `(H1)`
remains), `NoPeriodicLeftLimit` becomes a proved lemma (`noPeriodicLeftLimit_of_unique`), and the
module `AeNoPeriodic.lean` — Lemma 6.2 (proved in the previous round, .ultramath/smvz4odkr) plus the
null-hyperplane argument — is **not needed**: §6 is now an appendix recording it as an independent
a.e. proof. Milestones M5/M6 absorb the new lemma and M7 (`Main.lean`) no longer depends on it.

**Consistency check of the new lemma against the previous blueprint.** A periodic left limit is
still *necessary* to avoid (§8.3: it breaks uniform convergence, so a proof must exclude it); the
new lemma says unique ergodicity excludes it. The two together say: the case where the conclusion of
Theorem 2 fails is a case where `(H1)` already fails — which is exactly the situation one wants, and
it is why `(H2)` was never a real extra hypothesis.

### Addendum 127: `T̃` **is** uniquely ergodic on `[a+, b−]` — the author is right, my space was wrong

Instruction (verbatim): *"You write that T' is never uniquely ergodic, but I am not convinced. The
left end point a should *not* be split in two points, only the interior singularities should. Still,
if you want to split also the left end point in {0-, 0+}, then T' is a map on [0+, 1-], and this one
should be uniquely ergodic. Do you agree?"*

**Yes.** And the point is not cosmetic: my claim "`T̃` is never uniquely ergodic" was about the space
`X` of Blueprint 2 §2, which doubles *both* endpoints (because the split set is
`⋃_n T^n(s ∪ s' ∪ {b})` and `a ∈ s`). On `X` there are exactly two isolated points, `leftGerm a`
and `rightGerm b` (minimum and maximum of the order), and `T̃` fixes both (`L a = a`, `T b = b`), so
`δ` at either is an extra invariant measure. They are artefacts: they are the one-sided germs of the
endpoints, never approached from inside `[a,b)`. The correct object is

  `X° := closure (rightGerm '' Ico a b) = X ∖ {leftGerm a, rightGerm b}`  ("`[a+, b−]`"),

which is closed in `X`, hence compact, and `T̃`-invariant (`T̃` injective, and the two deleted points
have no other preimages). On it, `T̃` **is** uniquely ergodic when `T` is, with `rightGerm_*λ` as the
only invariant probability: this is the new **Theorem 4.11** of the blueprint, and its proof is three
lines from Theorem 4.6 + the lift lemma (Lemma 4.1) once the hypothesis `ν X° = 1` is stated
correctly.

**Bug this exposed, now fixed.** My earlier Theorem 4.6 was stated for `ν (closure (rightGerm '' [a,b])) = 1`,
and its proof claimed `rightGerm b ∉ K` — false, `rightGerm b` *is* in the closure of the right germs
of the closed interval (take `y = b`), so `δ_{rightGerm b}` was a counterexample to the statement as
written. With `K = X°` (half-open interval) both the statement and the `ρ {b} = 0` step are correct:
`ν {rightGerm b} = 0` because the point is deleted, and `ν {leftGerm b} = 0` by (H2) at `x = b`.

**Effect on the argument.** With Theorem 4.11 the source's own plan becomes literally valid: Tool 1
(Theorem 1.1) applied to the compact space `X°` and the continuous map `T̃|_{X°}`, whose unique
invariant measure is the lift of `λ`. Blueprint 2 §5 now records this as Route 1 and keeps the
relative form (Theorem 1.2) as Route 2; §8.2 is rewritten (the source's sentence is *true on the
right space*; what is not in the source is the space, the one-sided semi-conjugacy, and the ~20 lines
of transfer), Remark 2.7 and trap 14 warn against doubling the endpoints, and the Lean plan gains
`rightPart` / `uniqueErgodicOn_rightPart`.

### Addendum 128: dependency audit — Keane unused, and three gaps closed

Instruction (verbatim): *"What is the status with Keane? Is it still necessary? Is anything admitted
in the blueprint, or is it self-contained?"*

**Keane: not necessary, anywhere.** No proof in either blueprint mentions minimality, connections or
the structure theory of IETs. It survives only as a record in §8.6 (the true statement is Yoccoz
Theorem 5.9, "no connection ⇒ minimal", article p. 17; the converse is false for `d ≥ 3` by
Exercise 5.11 on the same page). The chain actually used is: `(H1)` ⟹ `(H2)` (Lemma 4.9, the
periodic-interval argument) ⟹ `T̃|_{X°}` uniquely ergodic (Theorem 4.11, from the defect identity and
the lift lemma) ⟹ uniform convergence (Tool 1) ⟹ `MasurVeechFun` a.e. (§7).

**Audit, and what it turned up.** New **§12** of Blueprint 2 lists, in one place, everything the two
blueprints use from outside themselves:

* the single mathematical input `masurVeech_ae_unique_invariant_perm` (this repository, axiom-clean),
  i.e. hypothesis `(H1)`;
* the Mathlib facts: `instCompactSpaceProbabilityMeasure`, `tendsto_iff_forall_integral_tendsto`,
  `Measure.integral_map`, `Measure.ext_of_isPiSystem`,
  `ext_of_forall_integral_eq_of_IsFiniteMeasure` (via `HasOuterApproxClosed` for pseudo-metrizable
  spaces), the `SplitI` instance chain (`Pi.compactSpace`, `PseudoMetrizableSpace.subtype/pi`,
  `Subtype.borelSpace`, `Prod.borelSpace`, `Pi.borelSpace`), `birkhoffSum`/`birkhoffAverage`, and the
  `IsCutSet` API of `MasurVeech/{CutSet,CutSetMeasure,IET}.lean` plus `Assembly.invariant_unitMeas`;
* and, for the appendix only, nullity of proper hyperplanes and Riesz representation.

Three gaps the audit exposed, all now closed:

1. **New Lemma 1.8** (elementary structure of `L`): `L x = x + δ_i` on `(c_i, c_{i+1}]`,
   `T x = x + δ_i` on `[c_i, c_{i+1})`; `L` maps `(c_i, c_{i+1}]` bijectively onto
   `(u_i, u_i + (c_{i+1} − c_i)]`, so `L` is a bijection of `[a,b]` fixing `a`; both maps are
   increasing translations on each open cell; `L` is left continuous, its discontinuities lie in `s`.
   This replaces three "prove separately" hints in §3.3–§3.4 (left continuity of `L`, injectivity of
   `L`, monotonicity on a cell).
2. **Positivity of the lengths is not needed.** Degenerate cells are allowed by `IsCutSet`
   (`isCutSet_mkIETCuts` asks for no positivity), and Lemmas 1.8, 4.9 and Theorem 2 never use it, so
   §7 no longer lists `∀ i, 0 < lam i` and trap 7 is rewritten. The a.e. input is only
   `lam ∈ simplexOn`, which is `ae_mem_simplexOn_of_card_ne_zero`.
3. **Lemma 3.4's surjectivity clause** is the one statement still written with a hint rather than a
   proof; it is **not used** (only injectivity is: Lemma 4.3 and Corollary 2.6), and §12.4 says so.

Conclusion of the audit: the blueprints are self-contained modulo Masur–Veech (the repository's own
theorem) and the listed Mathlib facts; no ergodic-theoretic or IET-theoretic theorem is admitted, in
particular not Keane's; and the only hypothesis of the upgraded theorem is `(H1)`.

### Addendum 129: formalisation started; `UniformConvergence.Basic`, `Transfer`, `Limits` landed

Instruction (verbatim): *"Great. I don't want Keane to be formalized. Continue with the Lean
formalization. You are the orchestrator for our lean formalization project. You will use up to four
ultramath subagents at a time. There is no budget limit."* and *"Once anything lands, you can
directly proceed with the next steps. Keep always 4 agents running until there are no more tasks to
dispatch."*

**Landed so far** (all in `MasurVeech/MasurVeech/UniformConvergence/`, imported by the umbrella,
`lake build` green, 0 warnings):

| module | contents | axioms |
|---|---|---|
| `Basic.lean` | `UniqueErgodicFun`, `MasurVeechFun` (verbatim from `IET2/ChallengeWeak.lean`, with `Assembly.unitMeas`), `uniqueErgodicFun_iff_birkhoffAverage`; **frozen before delegation** | clean |
| `Transfer.lean` | §4.1–4.3 abstract: `measure_singleton_map`, `measure_singleton_eq_zero_of_injOn_orbit`, `lift_unique`, `map_section_invariant`, `defect_identity(_meas)`, `map_map_eq_self` | clean |
| `Limits.lean` | §1 + §4.4: `tendsto_right`, `cutBelow`, `leftLimit` (with cell structure, left continuity, injectivity), `exists_invariant_ne_of_periodic_leftLimit`, `NoPeriodicLeftLimit`, `noPeriodicLeftLimit_of_unique` | clean |

`lift_unique` is proved without the blueprint's generating-π-system step: `ν (p⁻¹'D) = 0` gives
`s ∘ p = id` ν-a.e., hence `ν = ν.map (s∘p) = (ν.map p).map s`. `map_map_eq_self` is stated with the
weakest hypothesis (`ν {e c} = 0` for the finitely many left germs), so the concrete discharge stays
in `IET.lean`. `map_section_invariant` is §4.8 abstract.

**Two statements of the blueprint are false as printed; corrected in `BLUEPRINT-2.md` §1.2/1.8
(Remark 1.9).**
1. `L x = T x` off the cuts holds for `x ∈ [a,b)`, **not** at `x = b`: there `L b = b + δ_{d−1}`
   while `T b = b`. (Consistent with `J ⊆ s ∪ {b}`.) The Lean statement is `x ∈ Ico a b`.
2. `L` need **not** be injective when `T` merely satisfies `IsCutSet`: with `a = 0, b = 2,
   s = {0,1}`, `T x = x` on `[0,1)`, `T x = x − 1/2` on `[1,2)`, one has `L (3/4) = L (5/4) = 3/4`.
   Injectivity of `L` needs `Function.Injective T`, which holds for `T = mkIETEquiv lam π 0`
   (`Equiv.injective`). Blueprint Lemma 1.8(ii) now carries this hypothesis.

**Lemma 4.9 is formalised in a sharper form** than the blueprint's: a periodic left limit gives a
genuine periodic *point* `y = x₀ − ε/2` of `T` (since `T^[k]` is a translation of `J_0` onto itself,
hence the identity), and the atomic measure `k⁻¹ ∑ δ_{T^[j] y}` does the job — no measure-preservation
statement about `⋃_i J_i` is needed. Recorded in `BLUEPRINT-2.md` §4.4.

**Dispatch discipline.** Four agents always running, across swarms: `smvz6alci` (P3 split space,
P1 Tool 1 attempt 1; P4 and P2 already accepted and landed), `smvz6tkse` (final assembly
`masurVeechFun` from `masurVeech_ae_unique_invariant_perm` + Theorem 2 as a hypothesis),
`smvz6wam1` (second, independent P1 attempt by the blueprint's compactness-of-`P(X)` route — the
first attempt's stated Arzelà–Ascoli route is unsound because the averaging operators are not
equicontinuous). Round-2 packets P5 (`IET.lean`: Theorem 4.11 + Theorem 2) and P7 (audit) are
written into `.ultramath/mvuc/SPEC.md` §5.

## README re-checked after the `set_option` pass (this session, owner's request)

The `set_option` work moved declarations in six modules, so 21 of the README's 147 line anchors had
drifted; all of them were recomputed against a fresh declaration index and re-verified by reading the
anchored line of the file — **147/147 agree**, and the 7 links to `main` and the 2 `file:line` cells still
point at `theorem main` (line 322 of `ChallengeWeakSolved`).  The `f : IET 0 1` span was repointed at
`structure IET` again (line 802).  The 33 file/directory links all resolve to existing files.

Numbers touched by the pass: the library is now **19 100 lines** (was 19 120 — the net effect of removing
the linter-suppression comments and the `haveI` explanations, adding the two local `set_option` blocks);
the module count is unchanged at 29.  The README's two build claims were re-read against the tree and are
still true: `lake build`/`./Build.sh` are warning-free, and `runLinter` passes on `IETFree`, `Challenge`,
`ChallengeWeak`; nothing in the README mentions the linter suppressions, so no wording change was needed
there.  `formalization.yaml`'s `alignment` names were re-checked against the index — all present.

### Addendum 130: `Split.lean` landed (the space half of P3)

`MasurVeech/MasurVeech/UniformConvergence/Split.lean` (from member m1 of swarm `smvz6alci`, packet
P3, which was **rejected as incomplete** so that the member continues on the germ map): the split
interval as a closed subspace of `ℝ × (D → Bool)` — `SplitCond`, `SplitI`, compact/Hausdorff/
pseudo-metrizable/Borel instances, `proj` and its continuity, `rightGerm`/`leftGerm` with their
coordinate and projection lemmas, the fibre description `eq_rightGerm_or_leftGerm`, `side`, the
one-sided neighbourhoods `upSet`/`downSet`, `rightPart` with `isClosed_rightPart`/
`isCompact_rightPart`, and `splitSet` with `subset_splitSet`/`mem_splitSet_of_mem`/`one_mem_splitSet`.

Orchestrator edits before landing (all mechanical, semantics unchanged): deleted the member's
private duplicates of `cutBelow`/`leftLimit` (the canonical ones are the landed `Limits.lean` at root
namespace — keeping two notions would have hurt `IET.lean`); `Set.mem_setOf_eq` →
`Set.mem_ofPred_eq` (4×, deprecated); silenced 5 unused-binder warnings in the two germs; and
replaced 6 `show` by `change` (the `linter.style.show` warning only fires under the lakefile's linter
set, which `lake env lean` alone does not enable — the module is now warning-free under
`lake build`). `lake build`: 8778 jobs, 0 warnings, 0 errors; 28 axiom reports, all
`[propext, Classical.choice, Quot.sound]`.

Still missing from P3 (the member is working on it): the germ map `germMap` with
`continuous_germMap`, `germMap_rightGerm`, `germMap_inj`, `mapsTo_rightPart`, plus `image_splitSet`
and `leftGerm_zero_notMem_rightPart`. Delivery plan: a separate `Germ.lean` importing `Split` and
`Limits`, so that the space and the map stay separate modules.

### Addendum 131: `Main.lean` landed — `MasurVeechFun` now follows from the pointwise theorem alone

`MasurVeech/MasurVeech/UniformConvergence/Main.lean` (swarm `smvz6tkse`, accepted):
`unitMeas_Ico : Assembly.unitMeas (Ico 0 1) = 1` and

  `masurVeechFun_of_pointwise : (∀ {n} [NeZero n] (lam) (π), (H1 for mkIETFun lam π 0) → UniqueErgodicFun (mkIETFun lam π 0)) → MasurVeechFun`

with `(H1)` the uniqueness of the invariant probability carried by `[0,1)`, i.e. **`MasurVeechFun`
is reduced to Theorem 2 of the blueprint, and to nothing else**: `filter_upwards` on
`ae_mem_simplexOn_of_card_ne_zero` and on `masurVeech_ae_unique_invariant_perm`, then
`Invariant μ (mkIET1 lam π h)` ≡ `(μ : Measure ℝ).map (mkIETFun lam π 0) = μ` definitionally
(`coe_mkIET1` is `rfl`), the uniqueness identifies `μ` with `Assembly.lebesgue` (invariant by
`Assembly.invariant_unitMeas`, mass 1 by `unitMeas_Ico`), and `rfl` closes `Assembly.lebesgue =
Assembly.unitMeas`. No positivity of lengths, no Keane, no §6 of the blueprint.
Landed with the theorem renamed `masurVeechFun_of_pointwise` (the name `masurVeechFun` is reserved
for the unconditional statement, to be written in `IET.lean`). `lake build`: 8779 jobs, 0 warnings,
0 errors, 30 axiom reports, all `[propext, Classical.choice, Quot.sound]`.

**Campaign state.** Landed and axiom-clean: `Basic` (frozen statements), `Transfer` (§4 abstract),
`Limits` (§1 + §4.4 + (H1)⇒(H2)), `Split` (the space `[0,1] × (D → Bool)`, `rightPart`,
`splitSet`), `Main` (a.e. assembly). Missing for the endgame: P3's germ map (`germMap`,
`continuous_germMap`, `germMap_rightGerm`, `germMap_inj`, `mapsTo_rightPart`, `image_splitSet`,
`leftGerm 0 ∉ rightPart`; member m1 of `smvz6alci` continuing after a rejection) and Tool 1
(two independent attempts running, `smvz6alci` m2 and `smvz6wam1` m1). Then P5 `IET.lean`
(Theorem 4.11 + Theorem 2) closes `masurVeechFun`. An independent refute-first audit of the five
landed modules runs in `smvz71ro7`.
