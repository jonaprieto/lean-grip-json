#!/usr/bin/env python3
"""Regenerate the numbers block of bench/RESULTS.md from a run-all.sh raw log.

Usage: python3 bench/mktable.py <raw.txt> <RESULTS.md>

Reads harness lines (`<lib> <dataset> count=N ms=M med=D` or
`<lib> <file.json> count=N best_ms=M med_ms=D`), groups them into the published
tables, and splices the result between <!-- bench:begin --> and <!-- bench:end -->
in RESULTS.md. Everything outside the markers is hand-written and untouched.
"""
import re
import sys
from datetime import datetime, timezone

DS = {"canada.json": "canada", "citm_catalog.json": "citm", "twitter.json": "twitter"}

# Display name and runtime label for each harness id.
SAME_TASK = [
    ("nom", "nom (Rust)", "rustc"),
    ("hand", "hand-written scanner (Lean, no combinators)", "lean"),
    ("megaparsec", "megaparsec (Haskell)", "ghc"),
    ("attoparsec", "attoparsec (Haskell)", "ghc"),
    ("grip", "**grip** (Lean)", "lean"),
    ("std.parsec", "Std.Internal.Parsec (Lean)", "lean"),
    ("angstrom", "angstrom (OCaml)", "ocaml"),
    ("prim-parser", "prim-parser byte port (deep `G`, local)", "lean"),
]
CONTEXT = [
    ("lean4-parser", "lean4-parser (Lean, char)", "Char-level; byte mode broken on v4.28.0"),
    ("lean.json", "Lean.Json (Lean, DOM)", "builds a `Lean.Json` tree + leaf count"),
    ("grip.json", "grip.json (Lean, DOM)", "builds a `Grip.Json` tree + leaf count"),
]
EXAMPLES = ["sexp", "lambda", "http", "toml", "yaml"]

LINE = re.compile(
    r"^(?P<lib>\S+)\s+(?P<ds>\S+)\s+count=(?P<count>\d+)\s+(?:ms|best_ms)=(?P<min>[\d.]+)\s+(?:med|med_ms)=(?P<med>[\d.]+)"
)
EXAMPLE_LINE = re.compile(
    r"^(?P<lib>\S+)\s+size=(?P<size>\d+)\s+count=(?P<count>\S+)\s+ms=(?P<min>[\d.]+)\s+med=(?P<med>[\d.]+)"
)


def main() -> None:
    raw_path, results_path = sys.argv[1], sys.argv[2]
    rows = {}          # (lib, ds) -> (count, min, med)
    examples = {}      # lib -> (size, count, min, med)
    header = []
    for line in open(raw_path):
        line = line.rstrip("\n")
        if line.startswith("#"):
            header.append(line[2:])
            continue
        m = EXAMPLE_LINE.match(line)
        if m:
            examples[m["lib"]] = (int(m["size"]), m["count"], float(m["min"]), float(m["med"]))
            continue
        m = LINE.match(line)
        if m:
            ds = DS.get(m["ds"], m["ds"])
            rows[(m["lib"], ds)] = (int(m["count"]), float(m["min"]), float(m["med"]))
            continue

    def norm(key: str, raw: str) -> str:
        pats = {
            "rustc": r"rustc ([\d.]+)",
            "ghc": r"version ([\d.]+)",
            "ocaml": r"([\d.]+)",
            "lean": r"version ([\d.]+)",
        }
        m = re.search(pats[key], raw)
        return m.group(1) if m else raw

    versions = {}
    for h in header:
        for key in ("rustc", "ghc", "ocaml", "lean"):
            if h.startswith(key + ": "):
                versions[key] = norm(key, h[len(key) + 2:])
    stamp = next((h[len("bench session "):] for h in header if h.startswith("bench session ")), "unknown")
    machine = next((h[len("machine: "):] for h in header if h.startswith("machine: ")), "unknown")

    def rt(kind: str) -> str:
        v = versions.get(kind, "")
        label = {"rustc": "rustc", "ghc": "GHC", "ocaml": "OCaml", "lean": "Lean"}[kind]
        return f"{label} v{v}" if kind == "lean" and v else (f"{label} {v}" if v else label)

    def table(ids_rows, runtime: bool) -> str:
        out = []
        if runtime:
            out.append("| parser | canada | citm | twitter | runtime |")
            out.append("|--------|-------:|-----:|--------:|---------|")
        else:
            out.append("| parser | canada | citm | twitter |")
            out.append("|--------|-------:|-----:|--------:|")
        for ident, name, label in ids_rows:
            cells, have = [], False
            for ds in ("canada", "citm", "twitter"):
                r = rows.get((ident, ds))
                have = have or r is not None
                cells.append(f"{r[1]:.2f}" if r else "—")
            if not have:
                continue
            suffix = f" {rt(label)}" if runtime and label in ("rustc", "ghc", "ocaml", "lean") else ""
            out.append(f"| {name} | {cells[0]} | {cells[1]} | {cells[2]} |{suffix} |" if runtime
                       else f"| {name} | {cells[0]} | {cells[1]} | {cells[2]} |")
        return "\n".join(out)

    def med_table() -> str:
        out = ["| parser | canada | citm | twitter |",
               "|--------|-------:|-----:|--------:|"]
        for ident, name, _ in SAME_TASK:
            cells, have = [], False
            for ds in ("canada", "citm", "twitter"):
                r = rows.get((ident, ds))
                have = have or r is not None
                cells.append(f"{r[2]:.2f}" if r else "—")
            if have:
                out.append(f"| {name} | {cells[0]} | {cells[1]} | {cells[2]} |")
        return "\n".join(out)

    def ctx_table() -> str:
        out = ["| parser | canada | citm | twitter | note |",
               "|--------|-------:|-----:|--------:|------|"]
        for ident, name, note in CONTEXT:
            cells, have = [], False
            for ds in ("canada", "citm", "twitter"):
                r = rows.get((ident, ds))
                have = have or r is not None
                cells.append(f"{r[1]:.2f}" if r else "—")
            if have:
                out.append(f"| {name} | {cells[0]} | {cells[1]} | {cells[2]} | {note} |")
        return "\n".join(out)

    def ex_table() -> str:
        out = ["| parser | input bytes | count | ms | med |",
               "|--------|------------:|------:|---:|----:|"]
        for lib in EXAMPLES:
            if lib in examples:
                size, count, mn, md = examples[lib]
                out.append(f"| {lib} | {size} | {count} | {mn:.2f} | {md:.2f} |")
        return "\n".join(out)

    lean_v = versions.get("lean", "")
    others = ", ".join(filter(None, [
        f"rustc {versions['rustc']}" if "rustc" in versions else "",
        f"GHC {versions['ghc']}" if "ghc" in versions else "",
        f"OCaml {versions['ocaml']}" if "ocaml" in versions else ""]))
    block = f"""<!-- bench:begin -->
_Generated by bench/run-all.sh on {stamp} · {machine} · Lean v{lean_v}{", " + others if others else ""} · [raw log](results/{stamp}/raw.txt)_

Every cell is the best of 20 in-process runs (min ms). Medians are in the second table.

{table(SAME_TASK, runtime=True)}

**Medians (ms, same runs).** The min table above is the noise floor; the median is the
typical run. Ratios quoted in the prose use the min, matching historical practice here.

{med_table()}

**Different model / task (context only, min ms).** lean4-parser is `Char`-level (its byte
backend mis-backtracks on Lean v4.28.0); the DOM rows build a tree and count its leaves —
a heavier task than validate-and-count. The two DOM rows do identical work.

{ctx_table()}

**All example parsers (grip-only, generated inputs).**

{ex_table()}
<!-- bench:end -->"""

    doc = open(results_path).read()
    begin, end = doc.index("<!-- bench:begin -->"), doc.index("<!-- bench:end -->")
    doc = doc[:begin] + block + doc[end + len("<!-- bench:end -->"):]
    open(results_path, "w").write(doc)
    print(f"updated {results_path} from {raw_path}")


if __name__ == "__main__":
    main()
