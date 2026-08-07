#!/usr/bin/env bash
# JSONTestSuite parsers/ entry for grip.
# Protocol: exit 0 = valid JSON (accept), 1 = invalid (reject), other = crash.
# Usage: test_grip.sh <file>
set -euo pipefail
BIN="$(cd "$(dirname "$0")/.." && pwd)/.lake/build/bin/conformance"
if [ ! -x "$BIN" ]; then
  echo "grip binary not built; run: lake build conformance" >&2
  exit 2
fi
# Deep-nesting inputs recurse on the Lean stack (`fix`); raise the limit rather than
# crashing on them (the official corpus includes 100k-deep nesting cases). Set to the
# numeric hard cap rather than the bare `unlimited` keyword: on Darwin the hard limit is
# itself finite and some bash builds reject `ulimit -s unlimited` with EPERM in that case.
hard="$(ulimit -Hs)"
ulimit -s "$hard" 2>/dev/null || true
exec "$BIN" "$1"
