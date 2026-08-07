# Cross-library JSON benchmark — shared task spec (every harness MUST match this)

All harnesses implement the *same* task so the comparison is fair. Counts are the correctness
gate: a harness whose counts differ is a different (unfair) task and must be fixed.

## The task: strict RFC-8259 validate + count leaf scalars (NO DOM)

Parse one JSON document and return a leaf count. Do NOT build a value tree / DOM — accumulate an
integer count as you parse.

Counting rule:
- number = 1, string = 1, keyword (`true`/`false`/`null`) = 1
- object KEYS are NOT counted
- arrays and objects contribute 0 for themselves; their count = sum of element/member counts
- top level = one value, then optional whitespace, then END OF INPUT (reject trailing garbage)

## Strict grammar (reject these — do NOT write a loose scanner)

- number: `-? ( 0 | [1-9][0-9]* ) ( . [0-9]+ )? ( [eE] [+-]? [0-9]+ )?`
  reject `00`, `1.`, `1e`, `+1`, a lone `-`, leading zeros.
- string: `"..."`, each element either an unescaped byte `>= 0x20` that is not `"` or `\`,
  or an escape: `\` then one of `" \ / b f n r t`, or `\u` then exactly 4 hex digits.
  Reject unescaped control bytes (`< 0x20`), unknown escapes, short `\u`.
  Do NOT validate UTF-8 beyond this — bytes `>= 0x80` inside strings pass opaque (this matches
  grip's grammar-strict ceiling, so the task is identical).
- keyword: exact `true` / `false` / `null`.
- whitespace between tokens: space 0x20, tab 0x09, LF 0x0A, CR 0x0D.

## Datasets (vendored in `bench/data/`) and REQUIRED counts

| file | sha256 | leaves |
|------|--------|-------:|
| `bench/data/canada.json` | `f83b3b354030d5dd58740c68ac4fecef64cb730a0d12a90362a7f23077f50d78` | 111130 |
| `bench/data/citm_catalog.json` | `a73e7a883f6ea8de113dff59702975e60119b4b58d451d518a929f31c92e2059` | 16390 |
| `bench/data/twitter.json` | `a08b769f32b95f426cbc3abafcec65c1a19d3eb544d4ddf320eae142c99efc5d` | 11600 |

The three JSON files are byte-identical to their namesakes in miloyip/nativejson-benchmark
(verified via git blob sha against upstream master).

`bench/data/cargo.lock` (sha256 `f680ad93ac4ac91290becedf85c877108a48fd11af66655970d77aafab21910a`,
307 packages, root package `brainforge` 1.42.1, a Rust TUI project) is vendored as a
real-world TOML input for the TOML example benchmark.

CORRECTNESS GATE: your parser MUST produce exactly those counts. If any differs, your
grammar/counting is wrong — fix it before reporting done.

## Implementation quality

Idiomatic, well-written use of the library's OWN combinators. Not a strawman, and not a
hand-rolled byte scanner that bypasses the library — the point is to benchmark the LIBRARY at its
best on this task. No DOM.

## CLI

Accept the dataset path as `argv[1]`; preload it into memory (bytes), time 20 in-process
runs over the preloaded bytes (one untimed warmup first), and print exactly one line:

    <lib> <basename-of-path> count=<n> best_ms=<f> med_ms=<f>

`best_ms` is the minimum of the 20 samples, `med_ms` the median. Use a monotonic clock
and a barrier / `black_box` / volatile so the optimizer cannot elide the parse. Build
optimized (Haskell `-O2`, Rust `--release`, OCaml dune release; flambda if available).

## Timing note

Timing is SECONDARY here: the controller re-measures every harness sequentially (no concurrent
load) for the official numbers. Your job is a correct, idiomatic, strict harness that prints the
right counts and a plausible best_ms. Do not over-tune; do write real optimized code.
