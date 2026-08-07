# grip-json benchmark

The benchmark validates and counts JSON leaf values on three fixed nativejson-benchmark files,
then compares the same workload across the Grip validator, the Grip DOM parser, and Lean's
standard DOM parser.

| file | bytes | leaves |
|---|---:|---:|
| `canada.json` | 2.1 MB | 111130 |
| `citm_catalog.json` | 1.6 MB | 16390 |
| `twitter.json` | 616 KB | 11600 |

Run `bench/run-all.sh` to regenerate the machine-specific timing table and raw log. Timing is
informational; the leaf counts are the correctness gate.

<!-- bench:begin -->
<!-- bench:end -->
