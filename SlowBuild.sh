#!/usr/bin/env bash
# The SLOW, thorough check of the interval-exchange project: plain `lean`, one process per module,
# in dependency order, followed by the axiom report, the sorry count and `Comparator/Check.lean`.
#
# **This is not the build.**  `lake build` is: it is incremental (hash-based), parallel across the
# cores, and takes seconds for an ordinary edit and under three minutes from a removed `.lake/build`.
# This script is deliberately the opposite — it recompiles every module every time, sequentially, and
# each `lean` invocation reloads Mathlib, so a full run costs several minutes.  It exists because it
# checks three things a `lake build` does not:
#
#   * it compiles with `warn.sorry` ON (the lakefile has `warn.sorry = false`), so it can count the
#     declarations that still depend on `sorryAx`;
#   * `--strict` fails if `sorryAx` is reachable from the main theorem;
#   * it runs `Comparator/Check.lean`, the local stand-in for the comparator, on the two compiled
#     modules.
#
# Run it only when a thorough check is wanted (an owner's request, a release, a change to the
# challenge/library boundary); use `lake build` for ordinary work.  Its module list is derived from
# the imports of `IETFree.lean` at start-up, so do not run it concurrently with a rename or a move.
#
#   ./SlowBuild.sh            compile everything, then print the axiom report
#   ./SlowBuild.sh --strict   additionally FAIL if any declaration depends on `sorryAx`
set -euo pipefail
cd "$(dirname "$0")"

export TMPDIR="$PWD/.scratch/tmp"
mkdir -p "$TMPDIR"

# one log per module, named after its path: `IETFree/IET` -> `IETFree_IET.log`
logof() { echo "$TMPDIR/$(echo "$1" | tr / _).log"; }

# the options of `lakefile.toml`, except `warn.sorry` (the sorry count needs the warnings)
LEANOPTS=(-DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3
          -Dlinter.mathlibStandardSet=true)

# The library's modules in dependency order.  The list is derived, not maintained by hand: the root
# module `IETFree.lean` imports every module of the library, and a topological sort of the imports
# gives the order (so a new module needs no edit here, only its import in `IETFree.lean`).
lib=$(python3 - <<'PY'
import re, sys
def imports(path):
    return re.findall(r'^import (IETFree[.\w]*)', open(path, encoding='utf-8').read(), re.M)
mods = imports('IETFree.lean')
deps = {m: imports(m.replace('.', '/') + '.lean') for m in mods}
order, state = [], {}
def visit(m):
    st = state.get(m, 0)
    if st == 2:
        return
    if st == 1:
        sys.exit(f'import cycle at {m}')
    state[m] = 1
    for d in deps[m]:
        if d in deps:
            visit(d)
    state[m] = 2
    order.append(m)
for m in mods:
    visit(m)
print('\n'.join(order))
PY
)
mods="Challenge $lib"

for m in $mods; do
  f=${m//.//}
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
echo "=== the axiom check of the main theorem (in IETFree/ChallengeSolved.lean) ==="
grep -E "depends on axioms" "$(logof IETFree/ChallengeSolved)" || true

# the root module, which just imports everything
LEAN_PATH="$PWD:$LEAN_PATH" lean "${LEANOPTS[@]}" -o "IETFree.olean" "IETFree.lean" 2>&1 \
  | tee "$TMPDIR/IETFree.log" | grep -Ev 'declaration uses .sorry.|^$' || true
if grep -q 'error' "$TMPDIR/IETFree.log"; then
  echo "FAIL IETFree.lean"; grep 'error' "$TMPDIR/IETFree.log"; exit 1
fi
echo "ok   IETFree.lean"

echo
echo "=== the comparator pair (Comparator/Check.lean) ==="
if ! LEAN_PATH="$PWD:$LEAN_PATH" lean --run Comparator/Check.lean; then
  echo "FAIL Comparator/Check.lean -- the challenge and the solution do not match"
  exit 1
fi

echo
sorries=$(cat $(for m in $mods; do logof "${m//.//}"; done) | grep -c 'declaration uses .sorry.' || true)
echo "declarations still depending on sorryAx: ${sorries:-0}"
# `Challenge.lean` is the comparator challenge: its three `sorry`s are what it asks for — the
# definition hole `mkIETEquiv`, and the statements `coe_mkIETEquiv` and `main`.
chals=$(cat "$(logof Challenge)" | grep -c 'declaration uses .sorry.' || true)
echo "  of which the comparator challenge (Challenge): ${chals:-0}"
echo "  of which the library (with ChallengeSolved): $(( ${sorries:-0} - ${chals:-0} ))"

if [ "${1:-}" = "--strict" ]; then
  if grep -q 'sorryAx' "$(logof IETFree/ChallengeSolved)"; then
    echo "STRICT: FAIL -- sorryAx still reachable from the main theorem"
    exit 1
  fi
  echo "STRICT: ok"
fi
