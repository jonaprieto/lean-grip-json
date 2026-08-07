#!/usr/bin/env bash
# Re-run every locally-available benchmark harness on the three vendored datasets,
# gate the counts, capture raw output to bench/results/<UTC-stamp>/raw.txt, and
# regenerate the numbers block of bench/RESULTS.md (between the bench:begin/end
# markers). Prose in RESULTS.md is hand-written; the tables are machine-produced.
#
# Usage: bench/run-all.sh [--with-upstream]
#   --with-upstream   also run the prim-parser-upstream harness (needs network for
#                     mathlib's cache on first build; slow). Off by default.
set -euo pipefail
cd "$(dirname "$0")/.."

STAMP="$(date -u +%Y-%m-%dT%H%M%SZ)"
OUT="bench/results/$STAMP"
mkdir -p "$OUT"
RAW="$OUT/raw.txt"

have() { command -v "$1" >/dev/null 2>&1; }

# gate <line>: abort if a dataset line carries the wrong leaf count.
gate() {
  local line="$1" want=""
  case "$line" in
    *canada*)  want=111130 ;;
    *citm*)    want=16390 ;;
    *twitter*) want=11600 ;;
  esac
  if [[ -n "$want" ]] && ! grep -q "count=${want}\b" <<<"$line"; then
    echo "COUNT GATE FAILED: ${line} (expected count=${want})" >&2
    exit 1
  fi
}

# run <cmd...>: run a harness, echo its stdout to the terminal and raw log, gated.
# Captures output via command substitution rather than `done < <(cmd)`: process
# substitution runs the harness in a subshell whose exit status the `while` loop never
# sees, so a crashing harness would otherwise look like success under `set -e`.
run() {
  local out status
  set +e
  out="$("$@")"
  status=$?
  set -e
  if [[ $status -ne 0 ]]; then
    echo "HARNESS FAILED (exit $status): $*" >&2
    exit 1
  fi
  local line
  while IFS= read -r line; do
    [[ -z "$line" ]] && continue
    gate "$line"
    echo "$line" | tee -a "$RAW"
  done <<< "$out"
}

{
  echo "# bench session ${STAMP}"
  echo "# machine: $(uname -sm), $(sysctl -n machdep.cpu.brand_string 2>/dev/null || echo unknown-cpu)"
  echo "# lean: $(lean --version 2>/dev/null | paste -sd' ' -)"
  have rustc && echo "# rustc: $(rustc --version)"
  have ghc && echo "# ghc: $(ghc --version)"
  have ocamlfind && echo "# ocaml: $(ocamlfind ocamlopt -version)"
} >> "$RAW"

echo "== Lean rows (grip, grip.json, lean.json) =="
lake build bench >/dev/null
run lake exe bench

ABS_DATA=("$PWD/bench/data/canada.json" "$PWD/bench/data/citm_catalog.json" "$PWD/bench/data/twitter.json")

if have cargo && [[ -f bench/cross-lang/nom/Cargo.toml ]]; then
  echo "== nom =="
  (cd bench/cross-lang/nom && cargo build --release --quiet)
  for f in "${ABS_DATA[@]}"; do run bench/cross-lang/nom/target/release/nom-bench "$f"; done
fi

for hs in atto megaparsec; do
  if have cabal && [[ -d "bench/cross-lang/$hs" ]]; then
    echo "== $hs =="
    (cd "bench/cross-lang/$hs" && cabal build >/dev/null)
    bin="$(cd "bench/cross-lang/$hs" && cabal list-bin "${hs}-bench" | tail -1)"
    for f in "${ABS_DATA[@]}"; do run "$bin" "$f"; done
  fi
done

if have dune && [[ -d bench/cross-lang/angstrom ]]; then
  echo "== angstrom =="
  (cd bench/cross-lang/angstrom && dune build)
  for f in "${ABS_DATA[@]}"; do
    run bash -c "cd bench/cross-lang/angstrom && dune exec ./main.exe -- '$f'"
  done
fi

if [[ -d bench/cross-lang/lean4-parser ]]; then
  echo "== lean4-parser =="
  (cd bench/cross-lang/lean4-parser && lake build >/dev/null)
  for f in "${ABS_DATA[@]}"; do run bench/cross-lang/lean4-parser/.lake/build/bin/L4pBench "$f"; done
fi

if [[ -d bench/cross-lang/prim-parser && -d ../prim-parser ]]; then
  echo "== prim-parser (byte port) =="
  (cd bench/cross-lang/prim-parser && lake build >/dev/null)
  for f in "${ABS_DATA[@]}"; do run bench/cross-lang/prim-parser/.lake/build/bin/gripjson "$f"; done
fi

if [[ "${1:-}" == "--with-upstream" && -d bench/cross-lang/prim-parser-upstream ]]; then
  echo "== prim-parser upstream (context) =="
  (cd bench/cross-lang/prim-parser-upstream && lake exe cache get >/dev/null 2>&1 || true
   lake build >/dev/null)
  run bench/cross-lang/prim-parser-upstream/.lake/build/bin/bench-canada bench/data/canada.json
fi

echo "== regenerating RESULTS.md numbers block =="
python3 bench/mktable.py "$RAW" bench/RESULTS.md
echo "raw log: $RAW"
