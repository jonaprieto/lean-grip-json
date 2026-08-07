# Cross-project JSON leaf-counter benchmarks

Reference implementations of grip's JSON validate-and-count task in other libraries and
languages, so the numbers in `bench/RESULTS.md` are reproducible rather than cited. Every
harness implements the shared spec in `TASK.md` and must return the same leaf counts
(111130 on canada.json) — a different count means a different task.

Not built in CI (they need Rust, Haskell, OCaml, or a sibling checkout); run them by hand:

| harness | command |
|---------|---------|
| nom (Rust) | `cd nom && cargo run --release -- <file>` |
| attoparsec (Haskell) | `cd atto && cabal run atto-bench -- <file>` |
| megaparsec (Haskell) | `cd megaparsec && cabal run megaparsec-bench -- <file>` |
| angstrom (OCaml) | `cd angstrom && dune exec ./main.exe -- <file>` |
| lean4-parser (Lean) | `cd lean4-parser && lake build && .lake/build/bin/L4pBench <file>` |
| prim-parser byte port (Lean) | `cd prim-parser && lake exe cache get && lake build && .lake/build/bin/gripjson <file>` |
| prim-parser upstream (Lean) | `cd prim-parser-upstream && lake exe cache get && lake build && .lake/build/bin/bench-canada ../../data/canada.json` |

`<file>` is one of `bench/data/{canada.json,citm_catalog.json,twitter.json}`. The
prim-parser byte port path-requires the sibling `research/prim-parser` repo; both
prim-parser harnesses pull mathlib from the prebuilt cache.

Two harnesses are *context*, not same-task: lean4-parser is `Char`-level (its byte backend
is broken on Lean v4.28.0) and prim-parser-upstream is `Char`-level with allocating
combinators — both correctly slower for reasons unrelated to combinator quality.

Each harness times the parse only (input preloaded, I/O excluded), best-of-20 in-process,
with a barrier so the optimizer cannot elide the work. Different runtimes (GC, boxing,
reference counting) make cross-language rows context; the controlled comparison is the
Lean set in `bench/RESULTS.md`, which is the source of truth for numbers.
