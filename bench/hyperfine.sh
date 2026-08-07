#!/bin/sh
# End-to-end wall-clock of a single canada.json parse via hyperfine. This is the
# external cross-check for the self-timed `ms=`/`med=` printed by `lake exe bench`:
# the self-timed number is the pure parse (between two monoNanos, input preloaded);
# hyperfine here times the whole `bench once` command (process startup + file read
# + one parse), sampled with warmup and repeated runs.
#
# `bench once` parses the file exactly once and exits, so each hyperfine run is one
# parse -- do NOT point hyperfine at plain `lake exe bench`, which loops 20x
# in-process over every parser and would make hyperfine measure the entire batch.
#
# Usage: sh bench/hyperfine.sh [file]     (default: bench/data/canada.json)
# Requires: hyperfine (https://github.com/sharkdp/hyperfine).
set -eu

lake build bench
file="${1:-bench/data/canada.json}"
bin=".lake/build/bin/bench"   # run the built binary directly, not `lake exe`,
                              # whose wrapper adds ~170ms of its own startup per run.

if ! command -v hyperfine >/dev/null 2>&1; then
  echo "hyperfine not found; running the single-shot command once instead:"
  "$bin" once "$file"
  exit 0
fi

hyperfine --warmup 3 --min-runs 20 "$bin once $file"
