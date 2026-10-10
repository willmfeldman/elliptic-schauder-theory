#!/bin/bash
# Local emulation of Comparator's statement and definition-equality check.
#
# For each challenge workspace, prints a structural fingerprint (hashes of types, definition
# values and inductive shapes) of the challenge theorems and of every `BasicElliptic`
# constant their statements depend on, once in the `Challenge` environment and once in the
# `Solution` environment, and diffs the two.  It does not replay proofs or check axioms (the
# release Comparator run does); it catches statement or vocabulary drift, including
# differently named auxiliary `_proof_n` constants and instance-path differences.
#
# Usage: scripts/fingerprint-challenges.sh [workspace...]   (after build-challenges.sh --trusted-all)
set -eu
repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
tool="$repo_root/scripts/challenge_fingerprint.lean"
out=$(mktemp -d)
if [ "$#" -eq 0 ]; then
  set -- $(cd "$repo_root/challenges" && ls -d */ | tr -d /)
fi
status=0
for ws in "$@"; do
  cd "$repo_root/challenges/$ws"
  thms=$(python3 -c "import json;print(' '.join(json.load(open('config.json'))['theorem_names']))")
  lake env lean --run "$tool" Challenge $thms > "$out/$ws.challenge"
  lake env lean --run "$tool" Solution $thms > "$out/$ws.solution"
  if grep -q MISSING "$out/$ws.challenge" "$out/$ws.solution"; then
    echo "MISSING constants in $ws"; status=1
  elif diff "$out/$ws.challenge" "$out/$ws.solution" > "$out/$ws.diff"; then
    echo "IDENTICAL $ws ($(wc -l < "$out/$ws.challenge") constants)"
  else
    echo "DIFFERENT $ws"; cat "$out/$ws.diff"; status=1
  fi
done
exit $status
