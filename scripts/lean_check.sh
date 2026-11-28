#!/usr/bin/env bash
# Build the shared Lean project and check one target's files.
# Usage: scripts/lean_check.sh <Slug>    (files live in lean/Pipeline/<Slug>/, entry point Main.lean)
# PASS requires all three checks:
#   (1) lake build succeeds;
#   (2) no sorry or admit in the target's files;
#   (3) every "#print axioms" line in Main.lean reports only propext, Classical.choice and Quot.sound.
set -uo pipefail
slug="${1:?usage: scripts/lean_check.sh <Slug>}"
root="$(cd "$(dirname "$0")/.." && pwd)"
dir="$root/lean/Pipeline/$slug"
[ -d "$dir" ] || { echo "FAIL: no directory $dir"; exit 1; }
export PATH="$HOME/.elan/bin:$PATH"
cd "$root/lean"

echo "== lake build"
if ! lake build 2>&1 | tee "$dir/build.log" | tail -20; then echo "FAIL: build"; exit 1; fi
if grep -q "error:" "$dir/build.log"; then echo "FAIL: build errors"; exit 1; fi

echo "== sorry / admit scan"
if grep -rnE '\b(sorry|admit)\b' --include=*.lean "$dir"; then echo "FAIL: sorry or admit present"; exit 1; fi

echo "== axioms"
lake env lean "$dir/Main.lean" 2>&1 | tee "$dir/axioms.log"
bad=$(grep -E "depends on axioms" "$dir/axioms.log" | sed 's/.*\[\(.*\)\].*/\1/' | tr ',' '\n' | sed 's/ //g' \
      | grep -vE '^(propext|Classical.choice|Quot.sound)$' | grep -v '^$' || true)
if [ -n "$bad" ]; then echo "FAIL: non-standard axioms: $bad"; exit 1; fi
if grep -q "declaration uses 'sorry'" "$dir/axioms.log" "$dir/build.log"; then echo "FAIL: sorry"; exit 1; fi

echo "PASS lean_check $slug ($(lean --version 2>/dev/null | head -1))"
