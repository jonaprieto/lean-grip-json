/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Json
import GripJson

/-! # JSONTestSuite conformance runner

Dual mode:
* `conformance <file>` -- JSONTestSuite `parsers/` protocol: exit 0 if the file
  is accepted as valid JSON, 1 if rejected. Uses `Grip.Json.parse`, the value-producing
  parser the round-trip theorem (`GripProps.Container.parse_render`) is proved about --
  the API a real consumer of grip actually calls, not the leaf-counting benchmark grammar.
* `conformance` (no args) -- batch CI gate: walk `test/jsontestsuite/`, classify each file
  by name prefix (`y_` accept, `n_` reject, `i_` implementation-defined) against *both*
  `Grip.Examples.Json.json` (the benchmark validator) and `Grip.Json.parse` (the value
  parser), print a summary for each, and exit nonzero on any regression in either or any
  acceptance disagreement between them.

The two parsers are separately hand-written from grip combinators (`examples/Json.lean` vs
`Grip/Json.lean`) sharing no code and no equivalence lemma; only `examples/Json.lean` used to
be gated against this corpus, so a grammar edit to one without the other could silently drift
undetected. Running both here and asserting agreement is the empirical stand-in for that
missing proof -- it does not replace one, but a divergence now fails CI instead of shipping
quietly.

Grammar-strict ceiling (see bench/RESULTS.md):
the validator treats bytes at least 0x80 inside strings as opaque, but the current corpus's
invalid-UTF-8 `n_` files are still rejected. Deep-nesting `n_`/`i_` files need a raised
stack (both `fix` and `Grip.Json.parse` recurse on the Lean stack); the runner
scripts (`parsers/test_grip.sh`, CI) raise it to the process's hard cap rather than excluding
those files, so the corpus runs to completion here.

Known divergence on `i_` files (implementation-defined, so not gated either way): on invalid
UTF-8 *inside a string body* (e.g. `i_string_invalid_utf-8.json`), `Grip.Json.parse` rejects
(`Grip.Json.scanStr` validates the extracted body with `String.fromUTF8?` and errors on
invalid UTF-8). The validator has no UTF-8 check at all (it never materializes a `String`), so
it still accepts these; that is why `i_` disagreements are excluded from the mismatch check
below rather than asserted.
-/

open Grip Grip.Examples.Json

/-- Accept iff the benchmark validator `json` (grammar-strict, leaf-counting, no DOM) parses
the whole input. -/
def acceptsValidator (arr : ByteArray) : Bool :=
  match json.run arr 0 with
  | .ok _ _  => true
  | .error _ => false

/-- Accept iff `Grip.Json.parse` -- the value-producing parser `parse_render` is proved about,
and the one a caller of grip's public API actually invokes -- parses the whole input. -/
def acceptsDom (arr : ByteArray) : Bool :=
  match Grip.Json.parse arr with
  | .ok _    => true
  | .error _ => false

/-- Reserved allow-list for invalid-UTF-8 `n_` files. It is empty for the current corpus:
those files are rejected by both parsers. -/
def nAllowAccept : List String := []

private def classify (name : String) (accepted : Bool) :
    (Nat × Nat × Nat × Nat × Nat × Nat × Bool) :=
  -- returns (yTot,yOk, nTot,nOk, iAcc,iRej, regression)
  if name.startsWith "y_" then
    (1, (if accepted then 1 else 0), 0, 0, 0, 0, !accepted)
  else if name.startsWith "n_" then
    let allowed := nAllowAccept.contains name
    let ok := !accepted || allowed
    (0, 0, 1, (if !accepted then 1 else 0), 0, 0, !ok)
  else
    (0, 0, 0, 0, (if accepted then 1 else 0), (if accepted then 0 else 1), false)

/-- Aggregate counters threaded through one corpus walk for one `accepts` function. -/
structure Stats where
  yTot : Nat := 0
  yOk : Nat := 0
  nTot : Nat := 0
  nOk : Nat := 0
  iAcc : Nat := 0
  iRej : Nat := 0
  regressions : List String := []

private def Stats.step (s : Stats) (name : String) (accepted : Bool) : Stats :=
  let (yt, yo, nt, no, ia, ir, regr) := classify name accepted
  { yTot := s.yTot + yt, yOk := s.yOk + yo
    nTot := s.nTot + nt, nOk := s.nOk + no
    iAcc := s.iAcc + ia, iRej := s.iRej + ir
    regressions := if regr then name :: s.regressions else s.regressions }

private def Stats.summary (s : Stats) : String :=
  s!"y: {s.yOk}/{s.yTot} accepted · n: {s.nOk}/{s.nTot} rejected \
    (allow-accept {nAllowAccept.length}) · i: {s.iAcc} accepted / {s.iRej} rejected"

def batch : IO UInt32 := do
  let dir : System.FilePath := "test/jsontestsuite"
  let entries ← dir.readDir
  let mut validator : Stats := {}
  let mut dom : Stats := {}
  let mut mismatches : List String := []
  for e in entries do
    let name := e.fileName
    if !(name.endsWith ".json") then continue
    let arr ← IO.FS.readBinFile e.path
    let accV := acceptsValidator arr
    let accD := acceptsDom arr
    validator := validator.step name accV
    dom := dom.step name accD
    -- `i_` files are implementation-defined: the two parsers may legitimately disagree there
    -- (e.g. only one panics-to-empty-string on invalid UTF-8 inside a string body); everywhere
    -- else RFC-8259 gives one right answer, so a disagreement there is a real divergence.
    if accV != accD && !(name.startsWith "i_") then
      mismatches := name :: mismatches
  IO.println s!"validator (Grip.Examples.Json.json): {validator.summary}"
  IO.println s!"dom       (Grip.Json.parse):          {dom.summary}"
  let mut ok := true
  if !validator.regressions.isEmpty then
    ok := false
    IO.eprintln s!"validator: {validator.regressions.length} regression(s):"
    for r in validator.regressions.reverse do IO.eprintln s!"  {r}"
  if !dom.regressions.isEmpty then
    ok := false
    IO.eprintln s!"dom: {dom.regressions.length} regression(s):"
    for r in dom.regressions.reverse do IO.eprintln s!"  {r}"
  if !mismatches.isEmpty then
    ok := false
    IO.eprintln s!"validator/dom disagree on {mismatches.length} non-i_ file(s):"
    for r in mismatches.reverse do IO.eprintln s!"  {r}"
  if ok then
    IO.println "conformance: OK"
    return 0
  else
    IO.eprintln "conformance gate failed" -- see per-section detail above
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [file] =>
    let arr ← IO.FS.readBinFile file
    return (if acceptsDom arr then 0 else 1)
  | _ => batch
