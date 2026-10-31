/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import IETFree.Commensurable

/-!
**Blueprint and partial formalisation**: the centralizer of a nontrivial element of a free group is
cyclic.  **Status: everything is proved** — P2, P3, P4 (§1–§3), the shortcuts of §D (§D4, §D5), §D6,
  §D7,
and **LS 2.19 itself as `exists_zpow_eq_of_mul_comm` (§D8)**; axiom-clean, no `sorry`.
**P5b and P6 of §§4–5 are NOT needed**: Part D replaces them.  The commensurability input comes from
`Commensurable.lean` (`FreeGroup.commute_of_zpow_eq`, run `commensurable-commute`), and Lemma 2.7 is
`exists_nontrivial_commutator` in `Irreducible.lean`, proved from §D8 + §D3 + §D1.

# Goal

```lean
theorem exists_centralizer_pow {α : Type*} [DecidableEq α] {v : FreeGroup α} (hv : v ≠ 1) :
    ∃ r : FreeGroup α, ∀ z : FreeGroup α, z * v = v * z → ∃ n : ℤ, z = r ^ n
```

(The instance for `α = Fin 2` is the statement filed as `Tasks/centralizer_cyclic.lean`.)  This is
Lyndon–Schupp, *Combinatorial Group Theory*, Prop. 2.19.  It is the single deep input of Lemma 2.7
(`exists_nontrivial_commutator`) of the paper; §8 below records exactly what Lemma 2.7 additionally
needs.  Everything here is stated for a general `α`, so it is reusable beyond `F₂`.

# Reference and why this route

The plan follows Bogopolski, *Combinatorics over free groups*, §2.2.1 (cyclic decomposition), §2.3
(unique `k`-th roots) and §2.4.2, Prop. 3 (centralizers of free groups are cyclic), rather than
Lyndon–Schupp's own proof, for one reason: LS prove the key step with a "cancellation scheme"
(van Kampen diagram) argument, whereas Bogopolski's decomposition splits into lemmas that map onto
Mathlib's `reduce` / `reduceCyclically` / `conjugator` API.  Bogopolski's chain is

* `q₀` = the *maximal root* of `g` (so `g = q₀ ^ k` and `q₀` is not a proper power);
* `k`-th roots are unique  ⟹  `C(g) = C(q₀)`;
* if `f ∈ C(q₀)` then `q₀` and `f` are powers of a common element (**Lemma 4** there = LS 2.19's
  core), and since `q₀` is not a proper power, `q₀ = f' ^ ±1`, so `f ∈ ⟨q₀⟩`;
* hence `C(g) = ⟨q₀⟩`, cyclic.

So everything rests on **"commuting elements are powers of a common element"** (P6/P7 below).

For comparison, here is Lyndon–Schupp's own route (chapter I, §2, Props. 2.14–2.19, pp. 9–10), which
is what the paper cites:

* **LS 2.14**: if `w` and a conjugate `c⁻¹wc` are *both* cyclically reduced, then the conjugate is a
  **cyclic permutation** of `w` (induction on `|c|`, see P5b below);
* **LS 2.15**: `w = a⁻¹w₁a` with `w₁` cyclically reduced gives `w ^ n = a⁻¹ w₁ ^ n a`, reduced, and
  `|w ^ n| = 2|a| + n|w₁|` (see Q1 below);
* **LS 2.16**: free groups are torsion-free (this one *is* in Mathlib);
* **LS 2.17**: if `a ^ m` and `b ^ n` commute (`m n ≠ 0`) then `a`, `b` are powers of a common
  element.  LS deduce this from the theory of *rank*: `⟨a,b⟩` is free of rank `≤ 2`, and of rank `2`
  only if `(a,b)` is a basis — which is impossible here, since `⟨a,b⟩` would then be nonabelian.
  Hence `⟨a,b⟩` is cyclic;
* **LS 2.18**: commuting is an equivalence relation on `F ∖ {1}` (transitivity: apply 2.17 twice);
* **LS 2.19**: the *normalizer* of `⟨w⟩` is cyclic: `u` normalizing gives `u⁻¹wu = w^{±1}`; `w` is
  not conjugate to `w⁻¹` (see Q2 below, LS's argument), so `u⁻¹wu = w`; hence the normalizer
  equals the centralizer, which is abelian by 2.17; and an abelian free group is cyclic.

The two routes differ in exactly one place.  LS's 2.17 needs the **rank** theory of free groups
(their 2.4/2.7: a free group of rank `n` needs at least `n` generators), which Mathlib does not have
  —
it has Nielsen–Schreier (subgroups of free groups are free) but no rank bounds.  Bogopolski's route
used below (the maximal root, §7) produces the cyclic generator without ever mentioning a rank, at
the price of the crux P6.  So this file follows Bogopolski, while taking from LS: 2.14 for P5b,
2.15 for Q1, and the proof of 2.19 for Q2.

# Conventions

* `α : Type*` with `[DecidableEq α]` (Mathlib's `FreeGroup` API needs it); words are
  `List (α × Bool)`; `mk : List (α × Bool) → FreeGroup α`; `W ^ n` for a list means
  `(List.replicate n W).flatten`; `[W]` abbreviates `mk W`; `norm g = g.toWord.length`.
* `U` is *cyclically reduced* when it is reduced and its last letter is not the inverse of its first
  (`FreeGroup.IsCyclicallyReduced`).
* Note `norm` is the length of the reduced word of an element; `|cyc g|` (used in §8) is
  `(reduceCyclically g.toWord).length`.

# Mathlib assets (verified against the installed snapshot, Lean 4.33.1 / Mathlib 4.33.1)

Available:
* `FreeGroup.reduce` with `reduce.cons`, `reduce.eq_of_red`, `reduce.exact`, `reduce.sound`,
  `reduce.self`, `isReduced_iff_reduce_eq`, `IsReduced.reduce_eq`;
* `FreeGroup.toWord` with `toWord_mul`, `toWord_pow`, `toWord_inv`, `toWord_mk`, `mk_toWord`,
  `toWord_inj`, `toWord_eq_nil_iff`, `toWord_of_pow`;
* `FreeGroup.norm` with `norm_mul_le`, `norm_inv_eq`, `norm_of`, `norm_of_pow`, `norm_eq_zero`;
* `FreeGroup.IsCyclicallyReduced`, `isCyclicallyReduced_iff`, `IsCyclicallyReduced.isReduced`,
  `IsCyclicallyReduced.flatten_replicate`,
  `IsReduced.append_flatten_replicate_append`;
* `FreeGroup.reduceCyclically` (`isCyclicallyReduced`, `cons_append`) and, **in the namespace
  `FreeGroup.reduceCyclically`** (not directly under `FreeGroup`), `conjugator`,
  `conj_conjugator_reduceCyclically : conjugator L ++ reduceCyclically L ++ invRev (conjugator L) =
    L`
  (i.e. `[L] = [conjugator L]⁻¹ * [reduceCyclically L] * [conjugator L]`), and
  `reduce_flatten_replicate : reduce ((replicate n L).flatten) = conjuator L ++ (replicate n
  (reduceCyclically L)).flatten ++ invRev (conjugator L)` for `n ≠ 0`;
* `IsMulTorsionFree (FreeGroup α)`, i.e.
  `pow_left_injective : n ≠ 0 → a ^ n = b ^ n → a = b`  (**unique `k`-th roots**);
* `subgroupIsFreeOfIsFree` (Nielsen–Schreier) — not on the critical path, but available as a
  fallback for "abelian + free ⟹ cyclic";
* `FreeGroup.IsMulTorsionFree`'s section in `CyclicallyReduced.lean` shows the flavour of argument
  that works (compare reduced words of powers via `reduce_flatten_replicate`);
* **`Mathlib/Data/List/PeriodicityLemma.lean`: `List.HasPeriod w p : Prop := w <+: take p w ++ w`
  and the Periodicity Lemma (Fine–Wilf)**
  `HasPeriod.gcd (per_p : HasPeriod w p) (per_q : HasPeriod w q) (len : p + q - p.gcd q ≤ w.length)
    :
  HasPeriod w (p.gcd q)`
  — this is exactly the periodicity tool the crux P6 needs, so it does **not** have to be built.

Missing in Mathlib: anything about centralizers or commuting elements in free groups, and cyclic
permutations / conjugacy classes of words (P5).  **P5 is no longer needed** — see §D.

# Dependency graph

**Current graph** (§D; the LS/Bogopolski graph below it is superseded):

```
P9  exists_centralizer_pow                          (the target)
└── P8  C(v) = ⟨q₀⟩,  q₀ the maximal root of v
    ├── P3   root bound : v = q ^ k → k ≤ norm v             PROVED (§1)
    ├── Mathlib  pow_left_injective                          (torsion-free)
    ├── P7   commuting ≠ 1 elements have a common power      PROVED (§D5)
    │   └── D4  a free group that is abelian is cyclic       PROVED (§D4)
    └── COMMENSURABILITY  z ^ m = s ^ q (m, n ≠ 0) ⟹ z, s commute
        │                                                    run `commensurable-commute`
        └── norm of a power, D3   norm (q ^ m) = 2|c| + |m|·|W|     PROVED (§D3)
```

**Superseded graph** (kept for the record; P5b and P6 are *not* needed):

```
P9  exists_centralizer_pow
└── P8  C(g) = ⟨q₀⟩,  q₀ = maximal root of g
    ├── P3  root_bound : g = q^k → k ≤ norm g
    ├── Mathlib  pow_left_injective
    └── P7  commuting ≠ 1 elements have a common power
        ├── P5  cyclically reduced conjugates are cyclic permutations
        └── P6  (CRUX) commuting cyclically reduced words have a common root/power
```

P6 was the risk, and §D4 removes it: "commuting" is replaced by "the subgroup generated by the two
elements is a free group, and its generators commute, so it is cyclic".  The order still worth
following: `P2 → P3 → P4` (done) → `§D3 → §D4 → §D5` (done) → commensurability (run) →
`P8 → P9` → Lemma 2.7.

-/

/-! ## §1. P2 — powers of a cyclically reduced word — **PROVED**
  (`FreeGroup.isReduced_flatten_replicate`,
`FreeGroup.length_flatten_replicate`, `FreeGroup.toWord_mk_pow`)

**Statement.** Let `W : List (α × Bool)` be reduced, cyclically reduced and nonempty.  Then for
`n ≥ 1`, `(List.replicate n W).flatten` is reduced and has length `n * W.length`.

**Proof.** `FreeGroup.IsCyclicallyReduced.flatten_replicate` gives reducedness of
`W ++ (replicate n W).flatten ++ []`-style concatenations; length is `List.length_flatten` +
`List.length_replicate`.  Also needed in the form: `((mk W) ^ n).toWord = (replicate n W).flatten`
(via `toWord_pow`, `reduce_flatten_replicate` — the conjugator of a reduced cyclically reduced word
is `[]`, so the formula collapses, and `reduce` of a reduced word is itself).

*Estimate:* 20–40 lines.  *Status:* straightforward; Mathlib has the ingredients.
-/

/-! ## §2. P3 — the root set is bounded — **PROVED** (`FreeGroup.le_norm_of_pow_eq`)

**Statement.** If `g = q ^ k` with `k ≥ 1`, then `k ≤ FreeGroup.norm g`.

**Proof.** Write `L = q.toWord`, `K = conjugator L`, `V = reduceCyclically L`.  By
`reduce_flatten_replicate` (P2/Mathlib), `g.toWord = K ++ (replicate k V).flatten ++ invRev K`, so
`norm g = 2 * K.length + k * V.length`.  If `q ≠ 1` then `V ≠ []` (the cyclic reduction of a
nontrivial element is nonempty), so `norm g ≥ k`.

Consequence: the set `K(g) = {k ≥ 1 | ∃ q, g = q ^ k}` is finite (bounded by `norm g`) and
nonempty (`k = 1`).  Hence it has a maximum `k₀` and a root `q₀` with `g = q₀ ^ k₀` — the
*maximal root*.

*Estimate:* 30–60 lines.  *Status:* bookkeeping over `reduce_flatten_replicate`; the only care is
`reduceCyclically L ≠ []` for `mk L ≠ 1`.
-/

/-! ## §3. P4 — commutation in a free monoid — **PROVED** (`List.commute_eq_replicate`)

**Statement.** For nonempty `X Y : List α`, `X ++ Y = Y ++ X` implies that there are `Z : List α`,
`m n : ℕ` with `m ≠ 0`, `n ≠ 0`, `X = (replicate m Z).flatten`, `Y = (replicate n Z).flatten`.
(For lists over `α × Bool`, or any alphabet — the statement is about the free monoid.)

**Proof** (induction on `|X| + |Y|, WLOG `|X| ≤ |Y|`).
* `X` is a prefix of `X ++ Y = Y ++ X`, and `|X| ≤ |Y|`, so `X` is a prefix of `Y`
  (`List.prefix_append` / `List.take` reasoning); write `Y = X ++ Y'`.
* Then `X ++ X ++ Y' = X ++ Y' ++ X`; cancelling `X` on the left gives `X ++ Y' = Y' ++ X`.
* `|Y'| = |Y| - |X| < |Y|`, so induction applies to `(X, Y')`: `X = Z^m`, `Y' = Z^n'`.
* Then `Y = X ++ Y' = Z^(m + n')`, and `m ≠ 0` persists.

*Estimate:* 40–80 lines.  *Status:* elementary; the only friction is list bookkeeping
(`List.append_cancel_left`, `List.prefix_iff_eq_append`, `List.length_append`,
  `List.length_replicate`,
`List.flatten_replicate_add`-style arithmetic).
-/

/-! ## §4. P5 — **NOT NEEDED** (superseded by §D3/§D4); one-step rotation is proved in Part C

This is the piece that replaces LS's "cancellation schemes" by clean statements about `reduce`.

**P5a (cascade form of `reduce` of a concatenation).** For reduced nonempty `A`, `B` there are
`A₁` a prefix of `A` and `B₁` a suffix of `B` with
`reduce (A ++ B) = A₁ ++ B₁` and `A.length - A₁.length = B.length - B₁.length`.
(All cancellation happens in one cascade across the junction; `A` and `B` being reduced prevents any
other cancellation.)  Useful special case: if additionally the junction does not cancel
(`(A.getLast, (B.head)).1` and inverse) then `reduce (A ++ B) = A ++ B`.

**P5b (cyclically reduced conjugates are cyclic permutations).** If `U`, `V` are nonempty reduced
cyclically reduced words with `mk U` conjugate to `mk V` (i.e. `∃ w, mk U = w * mk V * w⁻¹`), then
`V` is a cyclic permutation of `U`: `∃ p q, U = p ++ q ∧ V = q ++ p`.
*Proof plan (LS Prop. 2.14).* Induction on the length of the conjugating word `d`, where
`w' = d⁻¹ w d` and both are cyclically reduced.  If `d ≠ 1`, cancellation in `d⁻¹ w d` must occur on
*exactly one* side: if it occurred on both, then `|w'| < |w|`, contradicting that `w` and `w'` are
both cyclically reduced with conjugate reduced words (length is invariant under conjugation among
cyclically reduced words — the same induction).  Say `d⁻¹` cancels against `w`: then the last letter
of `d⁻¹` is the inverse of the first letter of `w`, so `d = y e` and `w = y u` with `y` a single
letter, and `d⁻¹ w d = e⁻¹ (y⁻¹ y) u y e = e⁻¹ (u y) e`, where `u y` is the cyclic permutation of
`w = y u` obtained by moving `y` to the end; recurse on `e`.  The other case is symmetric.
*Corollary* (**P5c**): the cyclic length `(reduceCyclically ·.toWord).length` is a conjugacy
invariant.  (Needed for the paper in §8, not for the centralizer theorem.)

*Estimate:* P5a 80–150 lines; P5b 150–250 lines.  *Status:* medium.  LS's induction (above) is
concrete and avoids the "cascade" analysis for P5b; the remaining friction is expressing "cyclic
permutation" (`∃ p q, U = p ++ q ∧ V = q ++ p`) and single-letter splitting (`w = y u` with
`y : α × Bool`), for which `List.exists_eq_cons_of_ne_nil` and `List.append_cancel_left` suffice.
-/

/-! ## §5. P6 — **NOT NEEDED** (superseded by §D4, §D5); kept for the record

**P6: commuting cyclically reduced words

**Statement.** Let `U`, `V` be nonempty reduced cyclically reduced words with
`reduce (U ++ V) = reduce (V ++ U)`.  Then there is `z : FreeGroup α`, `z ≠ 1`, and `m n : ℤ` with
`m ≠ 0 ≠ n`, `mk U = z ^ m`, `mk V = z ^ n`.

(Note the exponents are integers: `U = a`, `V = a⁻¹` is the degenerate case, cf. step 5.)

**Why this is the crux.**  All the mathematical content of LS 2.19 is here; everything else in §7 is
formal bookkeeping.  Two routes:

**Route A (cascade + periodicity — recommended).**
1. Apply P5a to both products: `reduce (U ++ V) = U₁ ++ V₁` (cascade size `s`: `U₁` = the first
   `|U| - s` letters of `U`, `V₁` = the last `|V| - s` letters of `V`) and
   `reduce (V ++ U) = V₂ ++ U₂` (cascade size `t`).
2. The two results are equal as words; comparing lengths gives **`s = t`**.
3. Put `a := |U| - s = |U| - t` and `W := reduce (U ++ V)`.  The equation `U₁ ++ V₁ = V₂ ++ U₂`
   gives, by comparing prefixes and then cancelling the common prefix (this part is verified):
   * the first `a` letters of `U` and of `V` coincide, and
   * the last `a` letters of `U` and of `V` coincide;
   * after deleting that common prefix, `V_{≥s} = V_{[a, |V|-s)} ++ U_{≥s}` (lengths agree).
4. **Remaining technical step (to be worked out on paper first).**  Extract a common root from step
  3
   using Fine–Wilf, which Mathlib already has as `List.HasPeriod.gcd`.  The intended shape: find a
   word `Y` of length at least `|U| + |V| - gcd(|U|,|V|)` that is a common factor of the two
     periodic
   words with periods `|U|` and `|V|` (candidates: `reduce (U ++ V)` padded by one period on each
   side, or the word `U ++ V_{≥s}` of step 3), prove `HasPeriod Y |U|` and `HasPeriod Y |V|`, apply
   `HasPeriod.gcd`, and conclude that the word `Z` of the first `d = gcd(|U|,|V|)` letters of `Y`
   satisfies `U = Z ^ (|U|/d)` and `V = Z ^ (|V|/d)`.  **Do this derivation on paper before
   formalising**; if it resists, switch to Route B.
5. Degenerate cases, to be treated separately before step 4: `s = 0` (no cancellation at all) makes
   step 3 say `U ++ V = V ++ U`, so P4 applies directly; and `s ≥ |U|` (the cascade eats all of `U`,
   e.g. `V = U⁻¹ ++ …`) leaves one factor empty, giving `mk U = (mk V)⁻¹`-type conclusions with
   negative exponents.
6. Conclude with `z := mk Z`.

**Route B (fallback): the tree/axis argument.**  `C(g)` preserves the axis of `g` in the Cayley tree
of `F`; two elements acting on the axis as translations commuting with `g`'s translation have
translation lengths in `ℤ·L(g)`, and an element fixing the axis pointwise is trivial (free action).
Conceptually cleaner, but Mathlib has no tree/axis infrastructure, so this route means building
geodesic theory for the Cayley graph first — likely more work *and* more risk.  Recorded here in
  case Route A's periodicity step turns out to be painful.

*Estimate:* Route A: cascade lemma ≈ P5a; periodicity (Fine–Wilf for lists) 150–250 lines; the case
analysis 100–200 lines.  *Status:* **the risk point of the whole development.**  Before starting,
check whether Mathlib already has a periodicity lemma for `List`
(`search: List.IsPeriod, List.period, List.count_…`); if it has `List.IsPeriod` with Euclid's
argument, the cost drops a lot.
-/

/-! ## §6. P7 — **PROVED** as `FreeGroup.exists_common_zpow` in §D5 (not by the plan below)

**P7: general commuting elements have a common power

**Statement.** `a b : FreeGroup α`, `a ≠ 1`, `b ≠ 1`, `a * b = b * a` ⟹
`∃ z ≠ 1, ∃ m n : ℤ, m ≠ 0 ≠ n ∧ a = z ^ m ∧ b = z ^ n`.

**Proof plan.**
1. Cyclic decomposition (Mathlib): `a = ca⁻¹ * a₀ * ca` with `a₀ = mk (reduceCyclically a.toWord)`
   cyclically reduced (nonempty since `a ≠ 1`), and `ca = mk (conjugator a.toWord)`; likewise
   `b = cb⁻¹ * b₀ * cb`.
2. `a b = b a` ⟹ `a₀` commutes with `T * b₀ * T⁻¹` where `T = ca * cb⁻¹`.
3. `T * b₀ * T⁻¹` is a conjugate of the cyclically reduced `b₀`.  By P5b its reduced word is a
   cyclic permutation of `b₀`, hence cyclically reduced.
4. Apply P6 to the pair (cyclically reduced `a₀`, cyclically reduced word of `T b₀ T⁻¹`): they are
   powers of a common `z`.  Hence `a₀` and `b₀` are powers of common elements `z` and `T⁻¹ z T`
   respectively; but `b₀` is also a power of `z` from step 4, and — this is where root uniqueness
   (Mathlib `pow_left_injective`) enters — two elements with a common nontrivial power coincide.
5. Unwind the conjugations: `a` and `b` are powers of `ca⁻¹ z ca`.

*Estimate:* 100–200 lines.  *Status:* medium; the fiddly part is the "two elements with a common
power coincide" step and the conjugator bookkeeping (associativity of the `mk`-level products).
A cheaper variant to consider: state P6 directly for "`U` cyclically reduced, `z` arbitrary
commuting
with `mk U`" (LS's form), then P7 is only the conjugator bookkeeping.
-/

/-! ## §7. P8, P9 — maximal root and the theorem (**still to do**; the plan below is the route)

**P8.**  Let `g ≠ 1`, let `k₀` be the maximum of `{k ≥ 1 | ∃ q, g = q ^ k}` (P3) and `q₀` with
`g = q₀ ^ k₀`.  Then:
* `q₀ ≠ 1` (else `g = 1`);
* `q₀` is not a proper power: if `q₀ = w ^ j` with `j ≥ 2`, then `g = w ^ (j * k₀)`, contradicting
  maximality of `k₀`;
* `C(g) = C(q₀)`: `⊇` is clear (`g` is a power of `q₀`); for `⊆`, if `f g f⁻¹ = g` then
  `(f q₀ f⁻¹) ^ k₀ = f q₀ ^ k₀ f⁻¹ = q₀ ^ k₀`, so `f q₀ f⁻¹ = q₀` by `pow_left_injective` (as
  `k₀ ≥ 1`);
* `C(q₀) = ⟨q₀⟩`: `⊇` clear; if `f` commutes with `q₀` then by P7 `q₀` and `f` are powers of a
  common `z`; as `q₀` is not a proper power, `q₀ = z ^ (±1)`, hence `f` is a power of `q₀`.

**P9 (target).** `C(g) = ⟨q₀⟩`, so `r := q₀` satisfies the goal.

*Estimate:* 60–120 lines.  *Status:* easy, given P3, P7 and `pow_left_injective`.
-/

/-! ## §8. What Lemma 2.7 additionally needs (not part of this file's target)

**Update.** With P9 available, Lemma 2.7 needs no cyclic-length or conjugate-to-inverse theory:
`natAbs_eq_of_conj_zpow` (§D3) replaces Q1/Q2, and the final contradiction is
`pow_two_mul_pow_two_of_ne` (§D1) applied to `x ^ 2 * y ^ 2 = y ^ 2 * x ^ 2`.  See Part D.

Lemma 2.7 of the paper (`exists_nontrivial_commutator` in `Irreducible.lean`, by now proved): for
`u v ≠ 1` in `F₂`, one of `[u,v]`, `[x⁻¹ux, v]`, `[y⁻¹uy, v]` is nontrivial.  The paper's proof
needs, beyond P9:

* **Q1 (cyclic length of powers).** `|cyc(g ^ k)| = |k| * |cyc g|` for `k ≠ 0`, from P2's
  `reduce_flatten_replicate`; in LS's form (Prop. 2.15): `w = a⁻¹w₁a` with `w₁` cyclically reduced
  gives `w ^ n = a⁻¹ w₁ ^ n a`, reduced, with `|w ^ n| = 2|a| + n|w₁|`.  With P5c (cyclic length is
    a conjugacy invariant) this gives the
  paper's step "`x⁻¹ux` and `u` have the same cyclically reduced length, so, both being powers
  of the
  single generator `r`, we get `x⁻¹ux = u ^ ±1`".
* **Q2 (`u` is not conjugate to `u⁻¹`).** LS's argument (inside the proof of 2.19 on p. 10), which
  is shorter than the one I first worked out: reduce to `w` cyclically reduced (P5b: conjugating
    changes
  a cyclically reduced word only by a cyclic permutation, so `u ~ u⁻¹` iff `w ~ w⁻¹`).  If
  `w ~ w⁻¹`, then `w⁻¹` is a cyclic permutation of `w`, i.e. `w = p ++ q` and `w⁻¹ = q ++ p` for
    some
  split.  But `w⁻¹ = (p ++ q)⁻¹ = q⁻¹ ++ p⁻¹`, which is reduced; hence `q ++ p = q⁻¹ ++ p⁻¹` as
  reduced words, so comparing letters gives `q = q⁻¹` and `p = p⁻¹`, i.e. every letter of `p` and
    `q`
  is its own inverse — impossible in a free group unless `p = q = []` (torsion-freeness, LS 2.16,
  Mathlib `IsMulTorsionFree`), contradicting `w ≠ 1`.
* **Q3 (`F₂` is not cyclic).** If every element were a power of a single `r`, then `x = r ^ m`,
  `y = r ^ n` with `m n ≠ 0`, so `x ^ n = r ^ (mn) = y ^ m`, and `pow_left_injective` would give
  `x = y` — but `FreeGroup.toWord genX = [(0,true)] ≠ [(1,true)] = FreeGroup.toWord genY`.  Cheap.
* **Q4 (assembly).** With P9 applied to `v`: `C(v) = ⟨r⟩`; the three words `u`, `x⁻¹ux`, `y⁻¹uy` lie
  in `C(v)`, hence are powers of `r`; by Q1 and Q2, `x⁻¹ux = u` and `y⁻¹uy = u`, so `x, y ∈ C(u)`,
  i.e. `⟨x,y⟩ = F₂ ⊆ C(u)`; but `C(u)` is cyclic by P9, contradicting Q3.

These four items can live in this file or next to Lemma 2.7; Q1/Q2 belong to the word theory
developed here, Q4 is a short assembly in `Irreducible.lean`.
-/

/-! ## §9. Formalisation notes, pitfalls, acceptance

* **Alphabet.** Prove everything for a general `α` with `[DecidableEq α]`; the application only
  instantiates `α = Fin 2`.  Mathlib's `FreeGroup` API requires `[DecidableEq α]`.
* **Lists vs. `FreeMonoid`.** Work with `List (α × Bool)` and `reduce`; `P4` can be stated for
  ordinary `List α` (any `α`), which keeps it independent of the free-group API.
* **Avoid quotient reasoning.** Every statement above is about `mk`-images of explicit words, so
  proofs can go through `toWord`/`reduce` (both computable) and `toWord_inj`.  Expect to use
  `reduce.exact`/`reduce.sound` to move between `reduce`-equalities of words and equalities in the
  group.
* **Pitfalls seen in the API.** `FreeGroup.norm` and any local `wordLength` are the same function
  but not syntactically equal — `show` the goal in terms of `FreeGroup.norm` before `omega`.
  `IsCyclicallyReduced.flatten_replicate` is about specific append shapes; check its exact statement
  before use.  `conj_conjugator_reduceCyclically` is stated with `++` and `invRev`; convert to
  `mk`-level products with `← mul_mk`, `← inv_mk`.
* **Suggested increments (each independently checkable by `lean`).**
  1. `P2`, `P3` (powers, root bound) — a day's work, no risk.
  2. `P4` (monoid commutation).
  3. `P5a` (cascade lemma), then `P5b`/`P5c`.
  4. `P6` — budget the most here; check Mathlib for `List` periodicity first.
  5. `P7`, `P8`, `P9` — mechanical once `P6` is in.
* **Acceptance criteria.** `Tasks/centralizer_cyclic.lean` becomes provable; `P9` has no `sorry` and
  its `#print axioms` gives `[propext, Classical.choice, Quot.sound]`; add the file to `Build.sh`.
* **Do not** weaken the target to "`C(v)` is abelian": that is the same theorem (abelian + free ⟹
  cyclic needs Nielsen–Schreier and the rank argument, which is *more* work than the route above).
-/

/-! # Formalisation

## Part A: powers of cyclically reduced words (P2) and the root bound (P3) -/

namespace FreeGroup

variable {α : Type*}

/-- **P2 (reducedness).** A power of a nonempty cyclically reduced word is reduced. -/
theorem isReduced_flatten_replicate {W : List (α × Bool)} (h : IsCyclicallyReduced W) (n : ℕ) :
    IsReduced ((List.replicate n W).flatten) :=
  (h.flatten_replicate n).isReduced

/-- **P2 (length).** Its length is `n * W.length`. -/
theorem length_flatten_replicate (W : List (α × Bool)) (n : ℕ) :
    ((List.replicate n W).flatten).length = n * W.length := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ', List.flatten_concat, List.length_append, ih]
    ring

/-- **P2 (`toWord`).** The reduced word of `(mk W) ^ n` is the flattened `n`-fold repetition of
`W`. -/
theorem toWord_mk_pow [DecidableEq α] {W : List (α × Bool)} (h : IsCyclicallyReduced W) (n : ℕ) :
    ((mk W) ^ n).toWord = (List.replicate n W).flatten := by
  have hW : (mk W).toWord = W := by rw [toWord_mk, h.isReduced.reduce_eq]
  induction n with
  | zero => simp
  | succ m ih =>
    have hflat : (List.replicate (m + 1) W).flatten = (List.replicate m W).flatten ++ W := by
      rw [List.replicate_succ', List.flatten_concat]
    rw [pow_succ, toWord_mul, ih, hW, ← hflat]
    exact IsReduced.reduce_eq (isReduced_flatten_replicate h (m + 1))

/-! ## Part A: the root bound (P3) -/

/-- **P3.** If `q ≠ 1` and `q ^ k = g` with `k ≥ 1`, then `k ≤ norm g`.
(`q = 1` has to be excluded: then `g = 1` and `norm g = 0`.) -/
theorem le_norm_of_pow_eq [DecidableEq α] {g q : FreeGroup α} {k : ℕ} (hk : 0 < k) (hq : q ≠ 1)
    (h : q ^ k = g) : k ≤ FreeGroup.norm g := by
  classical
  have hL : IsReduced q.toWord := isReduced_toWord
  -- the cyclic reduction of a nontrivial element is nonempty
  have hcyc : reduceCyclically q.toWord ≠ [] := by
    intro hnil
    apply hq
    have hconj := FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically q.toWord
    rw [hnil, List.append_nil] at hconj
    have hone : mk q.toWord = 1 := by
      conv_lhs => rw [← hconj]
      rw [← mul_mk, ← inv_mk, mul_inv_cancel]
    rwa [mk_toWord] at hone
  -- the length of `g = q ^ k` is `2 |conjugator| + k |cyclic reduction|`
  have hnorm : FreeGroup.norm g
      = 2 * (FreeGroup.reduceCyclically.conjugator q.toWord).length
        + k * (reduceCyclically q.toWord).length := by
    have h1 : FreeGroup.norm g = (q ^ k).toWord.length := by rw [h]; rfl
    rw [h1, toWord_pow, FreeGroup.reduceCyclically.reduce_flatten_replicate hL k, if_neg (by omega),
      List.length_append, List.length_append, FreeGroup.invRev_length, length_flatten_replicate]
    ring
  have hpos : 0 < (reduceCyclically q.toWord).length := List.length_pos_of_ne_nil hcyc
  rw [hnorm]
  nlinarith

end FreeGroup

/-! ## Part B: commutation in a free monoid (P4) -/

/-- **P4 (auxiliary, induction on the total length).** Two nonempty commuting words are powers of a
common word. -/
theorem List.commute_eq_replicate_aux (N : ℕ) :
    ∀ {α : Type*} {X Y : List α}, X.length + Y.length ≤ N → X ≠ [] → X ++ Y = Y ++ X →
      ∃ Z : List α, Z ≠ [] ∧ ∃ m n : ℕ, m ≠ 0 ∧
        X = (List.replicate m Z).flatten ∧ Y = (List.replicate n Z).flatten := by
  induction N with
  | zero =>
    intro α X Y hN hX _
    have hzero : X.length = 0 := by omega
    exact absurd (List.length_eq_zero_iff.mp hzero) hX
  | succ N ih =>
    intro α X Y hN hX h
    rcases eq_or_ne Y [] with rfl | hY
    · exact ⟨X, hX, 1, 0, one_ne_zero, by simp, by simp⟩
    rcases le_total X.length Y.length with hle | hle
    · -- `X` is a prefix of `Y`
      have htake : Y.take X.length = X := by
        have h1 : (X ++ Y).take X.length = X := List.take_left
        rw [h, List.take_append_of_le_length hle] at h1
        exact h1
      have hYeq : Y = X ++ Y.drop X.length := by
        conv_lhs => rw [← List.take_append_drop X.length Y]
        rw [htake]
      have hcancel : X ++ Y.drop X.length = Y.drop X.length ++ X := by
        have h1 : X ++ (X ++ Y.drop X.length) = (X ++ Y.drop X.length) ++ X := by
          rw [← hYeq]; exact h
        exact List.append_cancel_left (h1.trans (List.append_assoc X (Y.drop X.length) X))
      have hshorter : X.length + (Y.drop X.length).length ≤ N := by
        have h1 : (Y.drop X.length).length = Y.length - X.length := List.length_drop
        have h2 : 0 < X.length := List.length_pos_of_ne_nil hX
        omega
      obtain ⟨Z, hZ, m, n, hm, hXZ, hYZ⟩ := ih hshorter hX hcancel
      refine ⟨Z, hZ, m, m + n, hm, hXZ, ?_⟩
      rw [hYeq, hYZ, hXZ, List.replicate_add, List.flatten_append]
    · -- `Y` is a prefix of `X`
      have htake : X.take Y.length = Y := by
        have h1 : (Y ++ X).take Y.length = Y := List.take_left
        rw [← h, List.take_append_of_le_length hle] at h1
        exact h1
      have hXeq : X = Y ++ X.drop Y.length := by
        conv_lhs => rw [← List.take_append_drop Y.length X]
        rw [htake]
      have hcancel : Y ++ X.drop Y.length = X.drop Y.length ++ Y := by
        have h1 : Y ++ (Y ++ X.drop Y.length) = (Y ++ X.drop Y.length) ++ Y := by
          rw [← hXeq]; exact h.symm
        exact List.append_cancel_left (h1.trans (List.append_assoc Y (X.drop Y.length) Y))
      have hshorter : Y.length + (X.drop Y.length).length ≤ N := by
        have h1 : (X.drop Y.length).length = X.length - Y.length := List.length_drop
        have h2 : 0 < Y.length := List.length_pos_of_ne_nil hY
        omega
      obtain ⟨Z, hZ, m, n, hm, hYZ, hXZ⟩ := ih hshorter hY hcancel
      refine ⟨Z, hZ, m + n, m, by omega, ?_, hYZ⟩
      rw [hXeq, hXZ, hYZ, List.replicate_add, List.flatten_append]

/-- **P4.** Two nonempty commuting words in a free monoid are powers of a common word. -/
theorem List.commute_eq_replicate {α : Type*} {X Y : List α} (hX : X ≠ [])
    (h : X ++ Y = Y ++ X) :
    ∃ Z : List α, Z ≠ [] ∧ ∃ m n : ℕ, m ≠ 0 ∧
      X = (List.replicate m Z).flatten ∧ Y = (List.replicate n Z).flatten :=
  List.commute_eq_replicate_aux (X.length + Y.length) le_rfl hX h

/-! ## Part C: preparatory lemmas for P5 (cyclic permutations)

P5b is LS Prop. 2.14, proved by induction on the conjugating word with a single-letter case
  analysis.
Two of its ingredients are cheap and are proved here; the third, the one-step rotation lemma, is
stated in the blueprint (§4) with its plan but is **not** yet proved — see the note at the end of
  this section.
-/

namespace FreeGroup

variable {α : Type*}

/-- The inverse of a single letter. -/
def invLetter (a : α × Bool) : α × Bool := (a.1, !a.2)

/-- **P5, doubled-word form.** A word is cyclically reduced exactly when its double is reduced: the
two copies test the ordinary reducedness and the wrap-around condition at once. -/
theorem isCyclicallyReduced_iff_isReduced_append_self {L : List (α × Bool)} :
    IsCyclicallyReduced L ↔ IsReduced (L ++ L) := by
  simp only [isCyclicallyReduced_iff, IsReduced, List.isChain_append]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h1, ?_⟩
    rcases eq_or_ne L [] with rfl | hL <;> simp_all
  · rintro ⟨h1, -, h3⟩
    refine ⟨h1, ?_⟩
    rcases eq_or_ne L [] with rfl | hL <;> simp_all

/-- **P5, one-step rotation.** A cyclically reduced word stays cyclically reduced when its first
letter is moved to the end.  Both sides say that no two cyclically adjacent letters cancel; the
proof unrolls `isCyclicallyReduced_iff` on both sides and splits off the first letter of the tail.
(This is the missing ingredient of P5b's induction, proved by the run `cyclically-reduced-rotate`.)
-/
theorem rotate_cyclically_reduced {l : List (α × Bool)} {a : α × Bool} :
    IsCyclicallyReduced (a :: l) ↔ IsCyclicallyReduced (l ++ [a]) := by
  match l with
  | [] => simp [IsCyclicallyReduced]
  | b :: l' =>
    rw [isCyclicallyReduced_iff, isCyclicallyReduced_iff]
    have hL : IsReduced (a :: b :: l') ↔
        IsReduced (b :: l') ∧ (a.1 = b.1 → a.2 = b.2) := by
      change ([a] ++ (b :: l')).IsChain (fun a b => a.1 = b.1 → a.2 = b.2) ↔ _
      rw [List.isChain_append]
      simp [IsReduced]
    have hM : IsReduced ((b :: l') ++ [a]) ↔
        IsReduced (b :: l') ∧ (∀ x ∈ (b :: l').getLast?, x.1 = a.1 → x.2 = a.2) := by
      change ((b :: l') ++ [a]).IsChain (fun a b => a.1 = b.1 → a.2 = b.2) ↔ _
      rw [List.isChain_append]
      simp [IsReduced]
    rw [hL, hM]
    simp only [List.getLast?_cons_cons, List.getLast?_append_cons]
    grind

end FreeGroup

/-! ## Part D: the route actually taken — free groups, norms, and commensurability

The blueprint of §§4–7 planned P5b (cyclic permutations) and P6 (commuting cyclically reduced words)
as the crux, following Lyndon–Schupp 2.14–2.19.  That is **not** the route used here: two shortcuts
replace it.

* **A free group that is abelian is cyclic** (`exists_zpow_eq_of_forall_commute`).  This is the rank
  argument of LS 2.17 in the only form needed, and it needs no rank theory: a free group has a basis
  `b : ι → G` with `G ≃* FreeGroup ι`; if `G` is abelian then any two generators of `FreeGroup ι`
  commute, which forces `ι` to be a subsingleton (two distinct generators do not commute), and a
    free
  group on a subsingleton is generated by one element.
  Applied to the subgroup generated by two *commuting* elements it gives **P7** directly
  (`exists_common_zpow`): commuting nontrivial elements are powers of a common element.
* **The norm of a power** (`norm_zpow_eq`): `norm (q ^ m) = 2 * |conjugator| + |m| * |cyclically
  reduced part|`.  Comparing this for two expressions of the same element (or of conjugates) gives
  `natAbs_eq_of_conj_zpow`: conjugate powers have equal exponents up to sign.

With `exists_common_zpow` and `natAbs_eq_of_conj_zpow`, LS 2.19 reduces to the single statement that
*commensurable* elements have a common root (`z ^ m = s ^ q` with `m, n ≠ 0`); the proof of that is
the run `commensurable-commute` (`Tasks/commensurable.lean`), and with it:
`z ^ m = s ^ q` ⟹ `z` and `s` commute (the run's theorem) ⟹ they have a common root (P7 ↦
`exists_zpow_eq_of_forall_commute` on `⟨z, s⟩`).  Then the maximal root `q₀` of `v` (P3 bounds the
exponent, so the maximum exists) satisfies `C(v) = ⟨q₀⟩` exactly as §7 planned.

Lemma 2.7 then needs *no* cyclic-permutation theory at all: if `u`, `x⁻¹ u x` and `y⁻¹ u y` all
commute with `v`, they all lie in the cyclic group `C(v) = ⟨q₀⟩`, say `u = q₀ ^ a` and
`x⁻¹ u x = q₀ ^ b` with `a ≠ 0`; conjugacy of the two powers and `natAbs_eq_of_conj_zpow` give
`b = ±a`, so `x⁻¹ u x = u ^ ±1`, hence `x ^ 2 ∈ C(u)`; likewise `y ^ 2 ∈ C(u)`, and `C(u)` is cyclic
hence abelian, so `x ^ 2 * y ^ 2 = y ^ 2 * x ^ 2`, contradicting
`pow_two_mul_pow_two_of_ne` (`genX ≠ genY`).
-/

namespace FreeGroup

variable {α : Type*}

/-! ### §D1. Elementary word facts: reduced words, distinct generators -/

/-- Two reduced words with the same image in the free group coincide. -/
theorem eq_of_mk_eq_of_isReduced {L M : List (α × Bool)} (hL : IsReduced L)
    (hM : IsReduced M) (h : mk L = mk M) : L = M := by
  classical
  have h2 : reduce L = reduce M := reduce.sound h
  rwa [hL.reduce_eq, hM.reduce_eq] at h2

/-- Distinct generators of a free group do not commute. -/
theorem of_mul_of_ne {x y : α} (h : x ≠ y) :
    of x * of y ≠ of y * of x := by
  classical
  intro heq
  have heq' : mk [(x, true), (y, true)] = mk [(y, true), (x, true)] := heq
  have h2 : [(x, true), (y, true)] = [(y, true), (x, true)] :=
    eq_of_mk_eq_of_isReduced (by simp [IsReduced, List.isChain_cons_cons, h])
      (by simp [IsReduced, List.isChain_cons_cons, Ne.symm h]) heq'
  have h3 : (x, true) = (y, true) := ((List.cons.injEq _ _ _ _).mp h2).1
  exact h ((Prod.mk.injEq _ _ _ _).mp h3).1

/-- Squares of distinct generators do not commute. -/
theorem pow_two_mul_pow_two_of_ne {x y : α} (h : x ≠ y) :
    of x ^ 2 * of y ^ 2 ≠ of y ^ 2 * of x ^ 2 := by
  classical
  intro heq
  have heq' : mk [(x, true), (x, true), (y, true), (y, true)]
      = mk [(y, true), (y, true), (x, true), (x, true)] := heq
  have h2 : [(x, true), (x, true), (y, true), (y, true)]
      = [(y, true), (y, true), (x, true), (x, true)] :=
    eq_of_mk_eq_of_isReduced (by simp [IsReduced, List.isChain_cons_cons, h])
      (by simp [IsReduced, List.isChain_cons_cons, Ne.symm h]) heq'
  have h3 : (x, true) = (y, true) := ((List.cons.injEq _ _ _ _).mp h2).1
  exact h ((Prod.mk.injEq _ _ _ _).mp h3).1

/-! ### §D2. Torsion-freeness in integral form -/

/-- `q ^ j = 1` only when `j = 0` or `q = 1` (free groups are torsion-free). -/
theorem zpow_eq_one_iff {q : FreeGroup α} {j : ℤ} :
    q ^ j = 1 ↔ j = 0 ∨ q = 1 := by
  classical
  refine ⟨fun h => ?_, by rintro (rfl | rfl) <;> simp⟩
  rcases lt_trichotomy j 0 with hlt | heq | hgt
  · right
    have h3 : q ^ (-j) = 1 := by rw [zpow_neg, h, inv_one]
    have hj : (((-j).toNat : ℤ)) = -j := Int.toNat_of_nonneg (by omega)
    have h4 : (-j).toNat ≠ 0 := by omega
    have h5 : q ^ (-j).toNat = (1 : FreeGroup α) ^ (-j).toNat := by
      rw [one_pow, ← zpow_natCast, hj]
      exact h3
    exact IsMulTorsionFree.pow_left_injective h4 h5
  · exact Or.inl heq
  · right
    have hj : (((j.toNat : ℤ)) = j) := Int.toNat_of_nonneg (le_of_lt hgt)
    have h4 : j.toNat ≠ 0 := by omega
    have h5 : q ^ j.toNat = (1 : FreeGroup α) ^ j.toNat := by
      rw [one_pow, ← zpow_natCast, hj]
      exact h
    exact IsMulTorsionFree.pow_left_injective h4 h5

/-! ### §D3. The norm of a power, and conjugate powers -/

/-- **The norm of a nontrivial power**: `q ^ k` has length `2 |conjugator| + k |cyclic reduction|`
for `k ≥ 1`. -/
theorem norm_pow_eq [DecidableEq α] {q : FreeGroup α} {k : ℕ} (hk : 0 < k) :
    FreeGroup.norm (q ^ k) = 2 * (reduceCyclically.conjugator q.toWord).length
      + k * (reduceCyclically q.toWord).length := by
  have hL : IsReduced q.toWord := isReduced_toWord
  rw [show FreeGroup.norm (q ^ k) = (q ^ k).toWord.length from rfl, toWord_pow,
    FreeGroup.reduceCyclically.reduce_flatten_replicate hL k, if_neg (by omega),
    List.length_append, List.length_append, FreeGroup.invRev_length, length_flatten_replicate]
  ring

/-- **The norm of a nontrivial integral power.** -/
theorem norm_zpow_eq [DecidableEq α] {q : FreeGroup α} {m : ℤ} (hm : m ≠ 0) :
    FreeGroup.norm (q ^ m) = 2 * (reduceCyclically.conjugator q.toWord).length
      + m.natAbs * (reduceCyclically q.toWord).length := by
  have hnat : ∀ k : ℕ, 0 < k → FreeGroup.norm (q ^ k) = 2 * (reduceCyclically.conjugator
    q.toWord).length
      + k * (reduceCyclically q.toWord).length := fun k hk => norm_pow_eq hk
  rcases lt_trichotomy m 0 with hlt | heq | hgt
  · have hm' : m = -((m.natAbs : ℤ)) := by
      have h1 : ((m.natAbs : ℤ)) = -m := by
        rw [← Int.natAbs_neg m]
        exact Int.natAbs_of_nonneg (by omega)
      omega
    rw [hm', zpow_neg, FreeGroup.norm_inv_eq, zpow_natCast, hnat m.natAbs (by omega),
      Int.natAbs_neg, Int.natAbs_natCast]
  · exact absurd heq hm
  · have hm' : m = ((m.natAbs : ℤ)) := by
      have h1 : ((m.natAbs : ℤ)) = m := Int.natAbs_of_nonneg (by omega)
      omega
    rw [hm', zpow_natCast, hnat m.natAbs (by omega), Int.natAbs_natCast]

/-- Conjugation changes the norm by at most `2 |g|`. -/
theorem norm_conj_le [DecidableEq α] (g s : FreeGroup α) :
    FreeGroup.norm (g * s * g⁻¹) ≤ FreeGroup.norm s + 2 * FreeGroup.norm g := by
  have h1 : FreeGroup.norm (g * s * g⁻¹) ≤ FreeGroup.norm (g * s) + FreeGroup.norm g⁻¹ :=
    norm_mul_le _ _
  have h2 : FreeGroup.norm (g * s) ≤ FreeGroup.norm g + FreeGroup.norm s := norm_mul_le _ _
  rw [FreeGroup.norm_inv_eq] at h1
  omega

/-- Conjugating back: the norm drops by at most `2 |g|`. -/
theorem norm_le_norm_conj [DecidableEq α] (g s : FreeGroup α) :
    FreeGroup.norm s ≤ FreeGroup.norm (g * s * g⁻¹) + 2 * FreeGroup.norm g := by
  have hkey : g⁻¹ * (g * s * g⁻¹) * g = s := by group
  have h1 : FreeGroup.norm s = FreeGroup.norm (g⁻¹ * (g * s * g⁻¹) * g) := by rw [hkey]
  have h2 : FreeGroup.norm (g⁻¹ * (g * s * g⁻¹) * g)
      ≤ FreeGroup.norm (g⁻¹ * (g * s * g⁻¹)) + FreeGroup.norm g := norm_mul_le _ _
  have h3 : FreeGroup.norm (g⁻¹ * (g * s * g⁻¹))
      ≤ FreeGroup.norm g⁻¹ + FreeGroup.norm (g * s * g⁻¹) := norm_mul_le _ _
  rw [FreeGroup.norm_inv_eq] at h3
  omega

/-- **Conjugate powers have equal exponents up to sign.** -/
theorem natAbs_eq_of_conj_zpow {q : FreeGroup α} (hq : q ≠ 1) {g : FreeGroup α}
    {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) (h : g * q ^ m * g⁻¹ = q ^ n) :
    m.natAbs = n.natAbs := by
  classical
  by_contra hne
  have hcyc : reduceCyclically q.toWord ≠ [] := by
    intro hnil
    apply hq
    have hconj := FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically q.toWord
    rw [hnil, List.append_nil] at hconj
    have hone : mk q.toWord = 1 := by
      conv_lhs => rw [← hconj]
      rw [← mul_mk, ← inv_mk, mul_inv_cancel]
    rwa [mk_toWord] at hone
  set W := (reduceCyclically q.toWord).length with hWdef
  have hWpos : 0 < W := List.length_pos_of_ne_nil hcyc
  set c := (reduceCyclically.conjugator q.toWord).length with hcdef
  set G := FreeGroup.norm g with hGdef
  set K := 2 * G + 1 with hKdef
  have hKpos : 0 < K := by omega
  -- the conjugate relation for the scaled exponents
  have hpow : ∀ k : ℕ, g * q ^ (m * (k : ℤ)) * g⁻¹ = q ^ (n * (k : ℤ)) := by
    intro k
    have h4 : (MulAut.conj g) (q ^ m) = q ^ n := by
      rw [MulAut.conj_apply]
      exact h
    calc g * q ^ (m * (k : ℤ)) * g⁻¹ = (MulAut.conj g) (q ^ (m * (k : ℤ))) :=
          (MulAut.conj_apply g _).symm
      _ = (MulAut.conj g) ((q ^ m) ^ (k : ℤ)) := by rw [zpow_mul]
      _ = ((MulAut.conj g) (q ^ m)) ^ (k : ℤ) := map_zpow (MulAut.conj g) (q ^ m) (k : ℤ)
      _ = q ^ (n * (k : ℤ)) := by rw [h4, zpow_mul]
  -- the two norm inequalities at an arbitrary scale
  have hb : ∀ k : ℕ, FreeGroup.norm (q ^ (n * (k : ℤ)))
      ≤ FreeGroup.norm (q ^ (m * (k : ℤ))) + 2 * G := by
    intro k
    conv_lhs => rw [← hpow k]
    exact norm_conj_le g _
  have ha : ∀ k : ℕ, FreeGroup.norm (q ^ (m * (k : ℤ)))
      ≤ FreeGroup.norm (q ^ (n * (k : ℤ))) + 2 * G := by
    intro k
    conv_rhs => rw [← hpow k]
    exact norm_le_norm_conj g _
  -- evaluate the norms
  have hMnat : ∀ j : ℤ, j ≠ 0 → FreeGroup.norm (q ^ j) = 2 * c + j.natAbs * W :=
    fun j hj => norm_zpow_eq hj
  have hnatK : ∀ j : ℤ, (j * (K : ℤ)).natAbs = j.natAbs * K := by
    intro j
    rw [Int.natAbs_mul, Int.natAbs_natCast]
  have hmK : m * (K : ℤ) ≠ 0 := by
    have h : (K : ℤ) ≠ 0 := by omega
    exact mul_ne_zero hm h
  have hnK : n * (K : ℤ) ≠ 0 := by
    have h : (K : ℤ) ≠ 0 := by omega
    exact mul_ne_zero hn h
  have hbK : n.natAbs * K * W ≤ m.natAbs * K * W + 2 * G := by
    have h1 := hb K
    rw [hMnat (n * (K : ℤ)) hnK, hMnat (m * (K : ℤ)) hmK, hnatK n, hnatK m] at h1
    omega
  have haK : m.natAbs * K * W ≤ n.natAbs * K * W + 2 * G := by
    have h1 := ha K
    rw [hMnat (n * (K : ℤ)) hnK, hMnat (m * (K : ℤ)) hmK, hnatK n, hnatK m] at h1
    omega
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h2 : (n.natAbs - m.natAbs) * (K * W) ≤ 2 * G := by
      have hbK' : n.natAbs * (K * W) ≤ m.natAbs * (K * W) + 2 * G := by
        simpa [Nat.mul_assoc] using hbK
      rw [Nat.sub_mul]
      omega
    have h3 : K ≤ (n.natAbs - m.natAbs) * (K * W) := by
      have h4 : 1 ≤ n.natAbs - m.natAbs := by omega
      have h5 : K ≤ K * W := by
        calc K = K * 1 := (Nat.mul_one K).symm
          _ ≤ K * W := Nat.mul_le_mul_left K hWpos
      calc K ≤ K * W := h5
        _ = 1 * (K * W) := by ring
        _ ≤ (n.natAbs - m.natAbs) * (K * W) := Nat.mul_le_mul_right _ h4
    omega
  · have h2 : (m.natAbs - n.natAbs) * (K * W) ≤ 2 * G := by
      have haK' : m.natAbs * (K * W) ≤ n.natAbs * (K * W) + 2 * G := by
        simpa [Nat.mul_assoc] using haK
      rw [Nat.sub_mul]
      omega
    have h3 : K ≤ (m.natAbs - n.natAbs) * (K * W) := by
      have h4 : 1 ≤ m.natAbs - n.natAbs := by omega
      have h5 : K ≤ K * W := by
        calc K = K * 1 := (Nat.mul_one K).symm
          _ ≤ K * W := Nat.mul_le_mul_left K hWpos
      calc K ≤ K * W := h5
        _ = 1 * (K * W) := by ring
        _ ≤ (m.natAbs - n.natAbs) * (K * W) := Nat.mul_le_mul_right _ h4
    omega

/-! ### §D4. A free group with a single generator is cyclic, and abelian free groups are cyclic -/

/-- In a free group over a subsingleton index type, every element is a power of any generator. -/
theorem exists_zpow_eq_of_subsingleton {ι : Type*} [Subsingleton ι] (a : ι) (g : FreeGroup ι) :
    ∃ n : ℤ, g = of a ^ n := by
  induction g using FreeGroup.induction_on with
  | C1 => exact ⟨0, by simp⟩
  | of x => exact ⟨1, by rw [zpow_one, Subsingleton.elim x a]⟩
  | inv_of x ih => obtain ⟨n, hn⟩ := ih; exact ⟨-n, by rw [hn, zpow_neg]⟩
  | mul x y ihx ihy =>
      obtain ⟨m, hm⟩ := ihx
      obtain ⟨n, hn⟩ := ihy
      exact ⟨m + n, by rw [hm, hn, zpow_add]⟩

/-- **A free group that is abelian is cyclic.** -/
theorem exists_zpow_eq_of_forall_commute {G : Type*} [Group G] [IsFreeGroup G]
    (hcomm : ∀ x y : G, x * y = y * x) : ∃ r : G, ∀ z : G, ∃ n : ℤ, z = r ^ n := by
  classical
  obtain ⟨ι, ⟨b⟩⟩ := IsFreeGroup.nonempty_basis (G := G)
  have hgen : ∀ x y : ι, FreeGroup.of x * FreeGroup.of y = FreeGroup.of y * FreeGroup.of x := by
    intro x y
    have h1 : b.repr (b x * b y) = FreeGroup.of x * FreeGroup.of y := by
      rw [MulEquiv.map_mul b.repr, FreeGroupBasis.repr_apply_coe, FreeGroupBasis.repr_apply_coe]
    have h2 : b.repr (b y * b x) = FreeGroup.of y * FreeGroup.of x := by
      rw [MulEquiv.map_mul b.repr, FreeGroupBasis.repr_apply_coe, FreeGroupBasis.repr_apply_coe]
    rw [← h1, ← h2, hcomm]
  have hsub : Subsingleton ι := by
    refine ⟨fun x y => ?_⟩
    by_contra hne
    exact of_mul_of_ne hne (hgen x y)
  rcases isEmpty_or_nonempty ι with hem | hne
  · refine ⟨1, fun z => ⟨0, ?_⟩⟩
    have hS : Subsingleton (FreeGroup ι) := by
      refine ⟨fun x y => ?_⟩
      have hnil : ∀ g : FreeGroup ι, g.toWord = [] := fun g =>
        List.eq_nil_iff_forall_not_mem.mpr (fun a _ => hem.false a.1)
      calc x = mk x.toWord := (mk_toWord).symm
        _ = mk [] := by rw [hnil x]
        _ = mk y.toWord := by rw [hnil y]
        _ = y := mk_toWord
    have hG : Subsingleton G := @Equiv.subsingleton G (FreeGroup ι) b.repr.toEquiv hS
    rw [hG.elim z 1, zpow_zero]
  · obtain ⟨a⟩ := hne
    refine ⟨b a, fun z => ?_⟩
    obtain ⟨n, hn⟩ := @exists_zpow_eq_of_subsingleton ι hsub a (b.repr z)
    refine ⟨n, ?_⟩
    have h3 : z = b.repr.symm (b.repr z) := (b.repr.symm_apply_apply z).symm
    have h4 : b.repr.symm (FreeGroup.of a) = b a := by
      rw [← FreeGroupBasis.repr_apply_coe b a, MulEquiv.symm_apply_apply]
    rw [h3, hn, map_zpow, h4]

/-! ### §D5. P7 — commuting nontrivial elements are powers of a common element -/

/-- **P7: two commuting nontrivial elements of a free group are powers of a common element.** -/
theorem exists_common_zpow {G : Type*} [Group G] [IsFreeGroup G] {u w : G} (hu : u ≠ 1)
    (hw : w ≠ 1) (h : u * w = w * u) :
    ∃ z : G, ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ u = z ^ a ∧ w = z ^ b := by
  classical
  set K : Subgroup G := Subgroup.closure ({u, w} : Set G) with hK
  have hfree : IsFreeGroup K := subgroupIsFreeOfIsFree K
  have hmem : ({u, w} : Set G) ⊆ (Subgroup.centralizer ({u, w} : Set G) : Set G) := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact rfl
    · exact h.symm
    · exact h
    · exact rfl
  have hle : K ≤ Subgroup.centralizer (K : Set G) := by
    have h1 : Subgroup.closure ({u, w} : Set G) ≤ Subgroup.centralizer ({u, w} : Set G) :=
      (Subgroup.closure_le _).mpr hmem
    rw [hK, Subgroup.centralizer_closure]
    exact h1
  have hcommK : ∀ x y : K, x * y = y * x := by
    intro x y
    have hx : (x : G) ∈ Subgroup.centralizer (K : Set G) := hle x.2
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx) (y : G) y.2).symm
  obtain ⟨r, hr⟩ := @exists_zpow_eq_of_forall_commute K _ hfree hcommK
  have huK : u ∈ K := by
    rw [hK]
    exact Subgroup.subset_closure (by simp)
  have hwK : w ∈ K := by
    rw [hK]
    exact Subgroup.subset_closure (by simp)
  obtain ⟨a, ha⟩ := hr ⟨u, huK⟩
  obtain ⟨b, hb⟩ := hr ⟨w, hwK⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zpow_zero] at ha
    exact hu (by simpa using congrArg Subtype.val ha)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zpow_zero] at hb
    exact hw (by simpa using congrArg Subtype.val hb)
  exact ⟨(r : G), a, b, ha0, hb0, congrArg Subtype.val ha, congrArg Subtype.val hb⟩

/-! ### §D6. Integral powers as positive natural powers -/

/-- A nonzero integral power of `s` is a positive natural power of `s` or of `s⁻¹`. -/
theorem exists_nat_pow_or_inv_of_zpow {q s : FreeGroup α} {ν : ℤ} (h : q = s ^ ν) (hν : ν ≠ 0) :
    (∃ j : ℕ, 0 < j ∧ q = s ^ j) ∨ (∃ j : ℕ, 0 < j ∧ q = s⁻¹ ^ j) := by
  rcases lt_trichotomy ν 0 with hlt | heq | hgt
  · right
    refine ⟨(-ν).toNat, by omega, ?_⟩
    have h1 : (((-ν).toNat : ℤ)) = -ν := Int.toNat_of_nonneg (by omega)
    have h2 : ν = -(((-ν).toNat : ℤ)) := by omega
    calc q = s ^ ν := h
      _ = s ^ (-(((-ν).toNat : ℤ))) := congrArg (fun k : ℤ => s ^ k) h2
      _ = (s ^ (((-ν).toNat : ℤ)))⁻¹ := zpow_neg s _
      _ = (s⁻¹) ^ (((-ν).toNat : ℤ)) := (inv_zpow s _).symm
      _ = s⁻¹ ^ ((-ν).toNat) := zpow_natCast (s⁻¹) ((-ν).toNat)
  · exact absurd heq hν
  · left
    refine ⟨ν.toNat, by omega, ?_⟩
    have h1 : ((ν.toNat : ℤ)) = ν := Int.toNat_of_nonneg (by omega)
    have h2 : ν = ((ν.toNat : ℤ)) := h1.symm
    calc q = s ^ ν := h
      _ = s ^ ((ν.toNat : ℤ)) := congrArg (fun k : ℤ => s ^ k) h2
      _ = s ^ ν.toNat := zpow_natCast s ν.toNat

/-! ### §D7. Commensurable elements have a common root -/

/-- **Commensurable nontrivial elements have a common root.** -/
theorem exists_common_zpow_of_zpow_eq {z s : FreeGroup α} {m n : ℤ}
    (hm : m ≠ 0) (hn : n ≠ 0) (h : z ^ m = s ^ n) :
    ∃ r : FreeGroup α, ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ z = r ^ a ∧ s = r ^ b := by
  classical
  have hcomm : z * s = s * z := commute_of_zpow_eq hm hn h
  rcases eq_or_ne z 1 with hz | hz
  · subst hz
    have hs : s = 1 := by
      simp only [one_zpow, Eq.comm] at h
      rcases (zpow_eq_one_iff (q := s) (j := n)).mp h with h0 | h1
      · exact absurd h0 hn
      · exact h1
    subst hs
    exact ⟨1, 1, 1, one_ne_zero, one_ne_zero, by simp, by simp⟩
  · rcases eq_or_ne s 1 with hs | hs
    · subst hs
      exact absurd (by
        simp only [one_zpow] at h
        rcases (zpow_eq_one_iff (q := z) (j := m)).mp h with h0 | h1
        · exact absurd h0 hm
        · exact h1) hz
    · exact exists_common_zpow hz hs hcomm

/-! ### §D8. LS Prop. 2.19: the centralizer of a nontrivial element is cyclic -/

/-- **LS Prop. 2.19**: the centralizer of a nontrivial element of a free group is cyclic. -/
theorem exists_zpow_eq_of_mul_comm {v : FreeGroup α} (hv : v ≠ 1) :
    ∃ r : FreeGroup α, ∀ z : FreeGroup α, z * v = v * z → ∃ n : ℤ, z = r ^ n := by
  classical
  have hvnorm : 0 < FreeGroup.norm v := by
    rcases Nat.eq_zero_or_pos (FreeGroup.norm v) with h | h
    · exact absurd (FreeGroup.norm_eq_zero.mp h) hv
    · exact h
  -- the finite set of exponents of roots of `v`
  let S : Finset ℕ := (Finset.range (FreeGroup.norm v + 1)).filter
    (fun k => ∃ q : FreeGroup α, v = q ^ k)
  have h1S : (1 : ℕ) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, v, (pow_one v).symm⟩
  have hS : S.Nonempty := ⟨1, h1S⟩
  set k₀ := S.max' hS with hk₀def
  have hk₀pos : 0 < k₀ := by
    have h1 : 1 ≤ k₀ := Finset.le_max' S 1 h1S
    omega
  obtain ⟨-, q₀, hq₀⟩ := Finset.mem_filter.mp (Finset.max'_mem S hS)
  -- maximality of the exponent
  have hmax : ∀ (q : FreeGroup α) (k : ℕ), 0 < k → v = q ^ k → k ≤ k₀ := by
    intro q k hk hq
    have hqne : q ≠ 1 := by
      rintro rfl
      simp only [one_pow] at hq
      exact hv hq
    have hkle : k ≤ FreeGroup.norm v := le_norm_of_pow_eq hk hqne hq.symm
    refine Finset.le_max' S k ?_
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, q, hq⟩
  have hmax' : ∀ (q : FreeGroup α) (k : ℕ), 0 < k → v⁻¹ = q ^ k → k ≤ k₀ := by
    intro q k hk hq
    refine hmax q⁻¹ k hk ?_
    calc v = (v⁻¹)⁻¹ := (inv_inv v).symm
      _ = (q ^ k)⁻¹ := by rw [hq]
      _ = (q⁻¹) ^ k := (inv_pow q k).symm
  have hq₀ne : q₀ ≠ 1 := by
    rintro rfl
    simp only [one_pow] at hq₀
    exact hv hq₀
  refine ⟨q₀, fun z hz => ?_⟩
  rcases eq_or_ne z 1 with rfl | hz1
  · exact ⟨0, by simp⟩
  -- P7: `v` and `z` have a common root
  obtain ⟨w, β, γ, hβ, hγ, hvw, hzw⟩ := exists_common_zpow hv hz1 hz.symm
  have hw : w ≠ 1 := by
    rintro rfl
    simp only [one_zpow] at hvw
    exact hv hvw
  -- `w` and `q₀` are commensurable, hence have a common root
  have hβk : w ^ β = q₀ ^ (k₀ : ℤ) := by rw [← hvw, hq₀, zpow_natCast]
  have hk₀ne : (k₀ : ℤ) ≠ 0 := by omega
  obtain ⟨s, μ, ν, hμ, hν, hws, hq₀s⟩ := exists_common_zpow_of_zpow_eq hβ hk₀ne hβk
  -- `q₀ = s ^ ν` and the maximality of `k₀` force `s = q₀` or `s = q₀⁻¹`
  have hsq : s = q₀ ∨ s = q₀⁻¹ := by
    rcases exists_nat_pow_or_inv_of_zpow hq₀s hν with ⟨j, hj, hq⟩ | ⟨j, hj, hq⟩
    · have hv' : v = s ^ (j * k₀) := by rw [hq₀, hq, ← pow_mul]
      have hle := hmax s (j * k₀) (Nat.mul_pos hj hk₀pos) hv'
      have hj1 : j = 1 := by
        have h2 : j ≤ 1 := Nat.le_of_mul_le_mul_right (by rwa [one_mul]) hk₀pos
        omega
      left
      rw [hq, hj1, pow_one]
    · have hv' : v = s⁻¹ ^ (j * k₀) := by rw [hq₀, hq, ← pow_mul]
      have hle := hmax s⁻¹ (j * k₀) (Nat.mul_pos hj hk₀pos) hv'
      have hj1 : j = 1 := by
        have h2 : j ≤ 1 := Nat.le_of_mul_le_mul_right (by rwa [one_mul]) hk₀pos
        omega
      right
      rw [hq, hj1, pow_one, inv_inv]
  have hzq : z = s ^ (μ * γ) := by rw [hzw, hws, zpow_mul]
  rcases hsq with h1 | h1
  · exact ⟨μ * γ, by rw [hzq, h1]⟩
  · refine ⟨-(μ * γ), ?_⟩
    rw [hzq, h1, inv_zpow, zpow_neg]

end FreeGroup
