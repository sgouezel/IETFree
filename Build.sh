#!/usr/bin/env bash
# Build and check the interval-exchange project without Lake.
#
# The repository is a genuine Lake project (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`),
# and `lake build` is how it is built elsewhere.  In this VM Mathlib lives in a root-owned, read-only,
# prebuilt directory (/opt/mathlib), which Lake cannot use as a package, so this script compiles the
# same modules with plain `lean`, in the same dependency order and with the options of `lakefile.toml`
# (`autoImplicit = false`, the mathlib linter set, ...; `warn.sorry` is *not* disabled here, since the
# sorry count below is computed from those warnings).  It also runs `Comparator/Check.lean`, the local
# stand-in for the comparator.
#
#   ./Build.sh            compile everything, then print the axiom report
#   ./Build.sh --strict   additionally FAIL if any declaration depends on `sorryAx`
set -euo pipefail
cd "$(dirname "$0")"

export TMPDIR="$PWD/.scratch/tmp"
mkdir -p "$TMPDIR"

# one log per module, named after its path: `IETFree/IET` -> `IETFree_IET.log`
logof() { echo "$TMPDIR/$(echo "$1" | tr / _).log"; }

# the options of `lakefile.toml`, except `warn.sorry` (the sorry count needs the warnings)
LEANOPTS=(-DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3
          -Dlinter.mathlibStandardSet=true)

# the library, in dependency order (the first two are the statement files of the comparator setup)
lib="Challenge ChallengeWeak IETFree/CutSet IETFree/CutSetMeasure IETFree/IET IETFree/Diophantine IETFree/Commensurable IETFree/MeasureTools IETFree/TranslationVector IETFree/SingularityBound IETFree/Centralizer IETFree/Irreducible IETFree/ReductionData IETFree/Presentation IETFree/IntegerAffine IETFree/SingularityList IETFree/GoodRegion IETFree/LengthMap IETFree/SubintervalTransfer IETFree/BlockRescaling IETFree/GeneratorChange IETFree/InvariantInterval IETFree/BlockEndpoints IETFree/BlockAETransfer IETFree/BlockDiophantine IETFree/BlockData IETFree/BlockIrreducibility IETFree/BlockAssembly IETFree/BlockDatum IETFree/BlockLemma IETFree/Reduction IETFree/ChallengeWeakSolved IETFree/Check"
mods="$lib"

for f in $mods; do
  LEAN_PATH="$PWD:$LEAN_PATH" lean "${LEANOPTS[@]}" -o "$f.olean" "$f.lean" 2>&1 \
    | tee "$(logof "$f")" | grep -Ev 'declaration uses .sorry.|^$' || true
  if grep -q 'error' "$(logof "$f")"; then
    echo "FAIL $f.lean"
    grep 'error' "$(logof "$f")"
    exit 1
  fi
  echo "ok   $f.lean"
done

echo
echo "=== axiom report (see Check.lean) ==="
grep -E "^'" "$(logof IETFree/Check)" || true

# the root module, which just imports everything
LEAN_PATH="$PWD:$LEAN_PATH" lean "${LEANOPTS[@]}" -o "IETFree.olean" "IETFree.lean" 2>&1 \
  | tee "$TMPDIR/IETFree.log" | grep -Ev 'declaration uses .sorry.|^$' || true
if grep -q 'error' "$TMPDIR/IETFree.log"; then
  echo "FAIL IETFree.lean"; grep 'error' "$TMPDIR/IETFree.log"; exit 1
fi
echo "ok   IETFree.lean"

# the statement files of the discovery runs, and the guard that they match the library
LEAN_PATH="$PWD:$LEAN_PATH" lean "${LEANOPTS[@]}" -o "$TMPDIR/Match.olean" Tasks/Match.lean 2>&1 \
  | tee "$TMPDIR/Match.log" | grep -Ev '^$' || true
if grep -q 'error' "$TMPDIR/Match.log"; then
  echo "FAIL Tasks/Match.lean"; grep 'error' "$TMPDIR/Match.log"; exit 1
fi
echo "ok   Tasks/Match.lean"

echo
echo "=== the comparator pair (Comparator/Check.lean) ==="
if ! LEAN_PATH="$PWD:$LEAN_PATH" lean --run Comparator/Check.lean; then
  echo "FAIL Comparator/Check.lean -- the challenge and the solution do not match"
  exit 1
fi

echo
sorries=$(cat $(for f in $mods; do logof "$f"; done) | grep -c 'declaration uses .sorry.' || true)
echo "declarations still depending on sorryAx: ${sorries:-0}"
# `Challenge.lean` is a *display-only* statement file: its two `sorry`s are statements, not
# gaps in the library, and nothing imports it.
# `ChallengeWeak.lean` is the comparator challenge (`comparator.json`): its three `sorry`s are
# what it asks for — the definition hole `mkIETEquiv`, and the statements `coe_mkIETEquiv` and `main`.
# `IETFree/ChallengeWeakSolved.lean` fills the hole with the library's definition and proves both
# theorems, with a clean axiom report.
stated=$(cat $(logof Challenge) | grep -c 'declaration uses .sorry.' || true)
chals=$(cat $(logof ChallengeWeak) | grep -c 'declaration uses .sorry.' || true)
echo "  of which the display-only statement file (Challenge): ${stated:-0}"
echo "  of which the comparator challenge (ChallengeWeak): ${chals:-0}"
echo "  of which the library (with ChallengeWeakSolved): $(( ${sorries:-0} - ${stated:-0} - ${chals:-0} ))"

if [ "${1:-}" = "--strict" ]; then
  if grep -q 'sorryAx' "$(logof IETFree/Check)"; then
    echo "STRICT: FAIL -- sorryAx still reachable"
    exit 1
  fi
  echo "STRICT: ok"
fi
