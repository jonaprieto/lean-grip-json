# Upstream prim-parser benchmark

Validate-and-count on canada.json against the actual upstream prim-parser
(`janmasrovira/prim-parser`), pinned to `0728704` — the latest upstream commit on Lean
v4.28.0 (upstream main moved to v4.32 in #14). Count-only, same task as grip, returns
111130.

Distinct from `bench/cross-lang/prim-parser/`, which benchmarks a local byte-level
deep-embedded reimplementation (`research/prim-parser`'s `G` framework) — not upstream.

## Run

```sh
cd bench/cross-lang/prim-parser-upstream && lake exe cache get && lake build
.lake/build/bin/bench-canada ../../data/canada.json
```

Needs network (fetches upstream prim-parser + mathlib) and a mathlib cache. Prints
`prim-parser-upstream canada.json count=111130`, `parse_best_ms`, `text_build_ms`, and
exits nonzero if the count doesn't match. The dataset defaults to
`bench/data/canada.json` relative to the working directory.

## Result (this machine, Lean v4.28.0)

parse ~583 ms. grip does the same task in ~20 ms → **~29x faster**. The cost is per-token
UTF-8 `Char` decoding, `List`-accumulating `many`/`sepBy`, and the deep-embedded GADT —
not the grade machinery. (The pinned commit already includes upstream's own perf work:
#9 outcome flattening, #11 ByteArray-backed `Text`. At the older `e1f3f7b` the same run
was ~698 ms.)
