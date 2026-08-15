# grip-json benchmark

The benchmark validates and counts JSON leaf values on three fixed nativejson-benchmark files,
then compares the validator, the Grip DOM parser, and Lean's standard DOM parser. The strict
no-DOM task applies to the validator; the DOM rows are context rather than the same workload.

| file | bytes | leaves |
|---|---:|---:|
| `canada.json` | 2,251,051 B (2.147 MiB) | 111130 |
| `citm_catalog.json` | 1,727,204 B (1.647 MiB) | 16390 |
| `twitter.json` | 631,514 B (616.713 KiB) | 11600 |

Run `bench/run-all.sh` to regenerate the machine-specific timing table and raw log. Timing is
informational; the leaf counts are the correctness gate.

<!-- bench:begin -->
<!-- bench:end -->
