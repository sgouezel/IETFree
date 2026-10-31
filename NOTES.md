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

- **Both builds are green and warning-free**: `lake build` (the genuine Lake project) succeeds from a
  clean `.lake` — 8742 jobs, exit 0, **no warnings** — and `./Build.sh` (plain `lean`, same options)
  also prints no warning.  §"The linter warnings are all gone" at the end of this file records what
  that took.  The **declaration** linters (Mathlib's `runLinter`, which `lake build` does not run) are
  clean too: 0 findings on the library's 982 declarations (§"The declaration linters are clean").  `./Build.sh` reports
  `declarations still depending on sorryAx: 6`: three in the **display-only** file `Challenge` (the
  definition hole `mkIETEquiv`, `coe_mkIETEquiv`, and the unconditional `main`), and three in the
  comparator challenge `ChallengeWeak.lean` (the same three, with the two hypotheses).  The library itself has **none**: `Check.lean`
  prints 296 `#print axioms` lines and not one of them contains `sorryAx` (the report of
  `ChallengeWeakSolved.lean`, which nothing imports, has 11 more, none with `sorryAx` either).  `Tasks/Match.lean`, which
  guards that the discovery-run statements still match the library, passes, and so does
  `Comparator/Check.lean`, the local stand-in for the comparator (32661 declarations compared, no
  difference).
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

### Module layout — 31 modules under `IET2/IETFree/` and the two statement files above it, 20 397 lines

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
