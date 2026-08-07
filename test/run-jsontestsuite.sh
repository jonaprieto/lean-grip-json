#!/usr/bin/env bash
# Opt-in: run grip's parsers/ entry over a fresh nst/JSONTestSuite clone and
# report per-file verdicts using the official corpus. Requires network + git.
# Not run in CI (CI uses the vendored corpus via `lake exe conformance`).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SCRATCH="${SCRATCH:-$ROOT/.jsontestsuite-scratch}"
WRAP="$ROOT/parsers/test_grip.sh"

lake build conformance
if [ ! -d "$SCRATCH" ]; then
  git clone --depth 1 https://github.com/nst/JSONTestSuite "$SCRATCH"
fi

pass=0; fail=0; crash=0; unexpected=0
for f in "$SCRATCH"/test_parsing/*.json; do
  base="$(basename "$f")"
  set +e; "$WRAP" "$f" >/dev/null 2>&1; code=$?; set -e
  case "$base" in
    y_*) if [ "$code" -eq 0 ]; then pass=$((pass+1));
         elif [ "$code" -gt 1 ]; then crash=$((crash+1)); echo "CRASH on y_: $base";
         else unexpected=$((unexpected+1)); echo "EXPECTED-ACCEPT rejected: $base"; fi ;;
    n_*) [ "$code" -eq 1 ] && pass=$((pass+1)) || { [ "$code" -gt 1 ] && crash=$((crash+1)) || { unexpected=$((unexpected+1)); echo "EXPECTED-REJECT accepted: $base"; }; } ;;
    i_*) [ "$code" -eq 0 ] && pass=$((pass+1)) || fail=$((fail+1)) ;;
  esac
done
echo "grip on official corpus: matched=$pass  i_rejected=$fail  crash=$crash  unexpected=$unexpected"
echo "(unexpected>0 or crash>0 = documented grammar-strict ceiling; compare with bench/RESULTS.md)"
