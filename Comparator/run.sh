#!/usr/bin/env bash
#
# Run the genuine [leanprover/comparator](https://github.com/leanprover/comparator) on this
# library's comparator pair:
#
#     challenge  `ChallengeWeak`                (ChallengeWeak.lean)
#     solution   `IETFree.ChallengeWeakSolved`  (IETFree/ChallengeWeakSolved.lean)
#     config     `comparator.json`
#
# This is the recipe of `Comparator/README.md` end to end: fetch and build the two tools, build the
# two modules with Lake, export them with `lean4export`, compare them declaration by declaration,
# check the axioms and replay the solution into the kernel.  Everything except the sandbox is the real
# comparator.
#
# Usage:
#
#     ./Comparator/run.sh                        # Mathlib resolved by lakefile.toml (normal machine)
#     MATHLIB=/opt/mathlib ./Comparator/run.sh   # a read-only prebuilt Mathlib (this VM)
#     ./Comparator/run.sh --rebuild              # rebuild the two tools first
#
# Environment:
#
#     COMPARATOR_REV      comparator revision to build.  Default `3927ad3`, the last revision whose
#                         `lean-toolchain` is Lean v4.33 (this library is Lean 4.33.1).  If your Lean
#                         is newer, pass the last revision on your version's toolchain.
#     COMPARATOR_WORK     where the tools and the scratch Lake project live (default `.scratch/cmp`).
#     MATHLIB             path to a Mathlib checkout.  Needed when `lake` cannot resolve Mathlib by
#                         itself, as in this VM, where Mathlib is prebuilt at `/opt/mathlib` and is
#                         not writable; the script then builds in a scratch Lake project that requires
#                         Mathlib by path.
#     COMPARATOR_LANDRUN  the sandbox to use.  Default: `landrun` from PATH if it exists, otherwise
#                         the comparator's own `scripts/fake-landrun.sh`, which runs the commands
#                         unsandboxed (the comparator documents it as its development path).
#
# Exit status: 0 if the comparator accepts the pair, non-zero otherwise.
set -euo pipefail
cd "$(dirname "$0")/.."                                       # -> IET2
ROOT=$PWD

COMPARATOR_REV=${COMPARATOR_REV:-3927ad3}
WORK=${COMPARATOR_WORK:-$ROOT/.scratch/cmp}
MATHLIB=${MATHLIB:-}
REBUILD=0
for arg in "$@"; do
  case "$arg" in
    --rebuild) REBUILD=1 ;;
    -h|--help) sed -n '2,40p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "unknown argument: $arg" >&2; exit 2 ;;
  esac
done

for tool in git lake lean; do
  command -v "$tool" >/dev/null || { echo "missing: $tool" >&2; exit 1; }
done
LEAN_VERSION=$(lean --version | sed -E 's/^.*version ([0-9]+\.[0-9]+\.[0-9]+).*$/\1/')
echo "== Lean $LEAN_VERSION, comparator at $COMPARATOR_REV"

# ---------------------------------------------------------------- the two tools
TOOLS=$WORK/comparator
STAMP=$TOOLS/.lean-version
if [ "$REBUILD" = 1 ] || [ ! -d "$TOOLS/.git" ]; then
  echo "== fetching comparator"
  rm -rf "$TOOLS"
  mkdir -p "$WORK"
  git clone -q https://github.com/leanprover/comparator "$TOOLS"
fi
if [ "$REBUILD" = 1 ] || [ ! -x "$TOOLS/.lake/build/bin/comparator" ] \
   || [ "$(cat "$STAMP" 2>/dev/null || echo)" != "$LEAN_VERSION" ]; then
  echo "== building comparator and lean4export (this needs the network once)"
  git -C "$TOOLS" fetch -q origin
  git -C "$TOOLS" checkout -q -f "$COMPARATOR_REV"
  echo "leanprover/lean4:v$LEAN_VERSION" > "$TOOLS/lean-toolchain"
  ( cd "$TOOLS" && lake build comparator lean4export )
  echo "$LEAN_VERSION" > "$STAMP"
fi
EXPORT=$TOOLS/.lake/packages/lean4export/.lake/build/bin/lean4export
COMPARATOR=$TOOLS/.lake/build/bin/comparator
for f in "$EXPORT" "$COMPARATOR"; do
  [ -x "$f" ] || { echo "not built: $f" >&2; exit 1; }
done

# ---------------------------------------------------------------- the sandbox
if [ -n "${COMPARATOR_LANDRUN:-}" ]; then
  LANDRUN=$COMPARATOR_LANDRUN
elif command -v landrun >/dev/null; then
  LANDRUN=$(command -v landrun)
else
  LANDRUN=$TOOLS/scripts/fake-landrun.sh
  echo "== no landrun in PATH: using the comparator's fake-landrun.sh (no sandbox)"
fi

# ---------------------------------------------------------------- the project Lake builds in
# The comparator runs `lake build <module>` in its working directory, so the pair must be built by
# Lake there.  With MATHLIB set, a scratch project requires Mathlib by path; otherwise the project's
# own lakefile.toml is used.
if [ -n "$MATHLIB" ]; then
  PROJECT=$WORK/lake
  echo "== Lake project in $PROJECT (Mathlib by path: $MATHLIB)"
  mkdir -p "$PROJECT"
  cat > "$PROJECT/lakefile.toml" <<EOF
name = "ietfree_lake"
[[require]]
name = "mathlib"
path = "$MATHLIB"
[[lean_lib]]
name = "ChallengeWeak"
[[lean_lib]]
name = "IETFree"
EOF
  ln -sfn "$ROOT/ChallengeWeak.lean" "$PROJECT/ChallengeWeak.lean"
  ln -sfn "$ROOT/IETFree" "$PROJECT/IETFree"
  # Lake derives the toolchain from the required Mathlib and refuses to continue in the same process
  # when it has to write it, so write it up front.
  echo "leanprover/lean4:v$LEAN_VERSION" > "$PROJECT/lean-toolchain"
else
  PROJECT=$ROOT
  echo "== Lake project in $PROJECT (Mathlib from lakefile.toml)"
fi
if [ "$PROJECT" != "$ROOT" ]; then
  cp "$ROOT/comparator.json" "$PROJECT/comparator.json"
fi

echo "== building the two modules"
if ! ( cd "$PROJECT" && lake build ChallengeWeak IETFree.ChallengeWeakSolved ); then
  # Lake may have needed to create or update the manifest or the toolchain first; one retry.
  echo "== retrying the build"
  ( cd "$PROJECT" && lake build ChallengeWeak IETFree.ChallengeWeakSolved )
fi

# `lean4export` needs to find the oleans: ask Lake for the search path it uses.
LEAN_PATH_LAKE=$( cd "$PROJECT" && lake env printenv LEAN_PATH 2>/dev/null || true )
if [ -z "$LEAN_PATH_LAKE" ]; then
  LEAN_PATH_LAKE="$PROJECT/.lake/build/lib/lean"
fi

# ---------------------------------------------------------------- the run
echo "== running the comparator"
set +e
( cd "$PROJECT" && \
  LEAN_PATH="$LEAN_PATH_LAKE${LEAN_PATH:+:$LEAN_PATH}" \
  COMPARATOR_LANDRUN="$LANDRUN" \
  COMPARATOR_LEAN4EXPORT="$EXPORT" \
  "$COMPARATOR" comparator.json )
status=$?
set -e
if [ "$status" = 0 ]; then
  echo "== accepted: the challenge and the solution are the same statements, and the solution's proofs"
  echo "   use only $(python3 -c 'import json;print(", ".join(json.load(open("comparator.json"))["permitted_axioms"]))' 2>/dev/null || echo 'the permitted axioms')"
else
  echo "== rejected (exit $status) -- see the comparator's message above" >&2
fi
exit "$status"
