/-
  Benchmark harness: validate-and-count on canada.json using prim-parser.

  Count-only JSON parser: returns the number of leaf scalars
  (null, bool, number, string = 1 each; arrays/objects = sum of children).
  Object keys are NOT counted, matching grip's task definition.
  No DOM/tree is allocated.

  Numbers: handles JSON numbers including negatives, decimals, and exponents.
  Strategy: require the first character to be '-' or a digit, then greedily
  consume any remaining "number character" (digit, '.', 'e', 'E', '+', '-').
  Strings: no escape sequences (canada.json doesn't need them).

  Measures:
    text_build_ms    : String → Text (ByteArray) conversion time (trivial since #11)
    parse_best_ms    : best of 20 in-process parse runs (text pre-built)
-/
import PrimParser

open Parser

-- ── Helpers ──────────────────────────────────────────────────────────────

private def keyword (s : String) : Parser Error conditional PUnit :=
  lexeme (string s)

private def stringLit : Parser Error conditional String := gdo
  dquote
  let cs ← many (satisfy (· != '\"'))
  dquote
  return String.ofList cs

-- Characters that can appear inside a JSON number (after the first char).
private def isNumChar (c : Char) : Bool :=
  c.isDigit || c == '.' || c == 'e' || c == 'E' || c == '+' || c == '-'

-- Parse a JSON number: require '-' or digit, then consume all number chars.
-- Grade: conditional (always consumes ≥1 char, possibly fails).
private def jsonNumRaw : Parser Error conditional PUnit := gdo
  satisfy (fun c => c == '-' || c.isDigit)
  skipWhile isNumChar

-- ── Count-only JSON parser ────────────────────────────────────────────────

/-- Parse a JSON value; return its leaf-scalar count. -/
def jsonCount : Parser Error conditional Nat :=
  fix (fun self =>
    let jnull  : Parser Error conditional Nat := 1 <$ᵍ keyword "null"
    let jbool  : Parser Error conditional Nat :=
      oneOf ((1 <$ᵍ keyword "true") ::₁ [1 <$ᵍ keyword "false"])
    let jnum   : Parser Error conditional Nat := 1 <$ᵍ lexeme jsonNumRaw
    let jstring : Parser Error conditional Nat := 1 <$ᵍ lexeme stringLit
    let jarray : Parser Error conditional Nat := gdo
      let items ← brackets (sepBy (lexeme comma) self)
      return items.foldl (· + ·) 0
    let jpair  : Parser Error conditional Nat := gdo
      lexeme stringLit          -- key: consumed, not counted
      lexeme (char ':')
      let v ← self
      return v
    let jobject : Parser Error conditional Nat := gdo
      let kvs ← braces (sepBy (lexeme comma) jpair)
      return kvs.foldl (· + ·) 0
    oneOf (jnull ::₁ [jbool, jnum, jstring, jarray, jobject]))

-- ── Benchmark harness ─────────────────────────────────────────────────────

/-- Convert a String to a length-indexed Text (ByteArray-backed since upstream #11;
Char decoding happens per token in the parser). -/
@[noinline] def toText (s : String) : Text s.toUTF8.size := Text.ofString s

/-- Run one parse from an IO.Ref holding the text; prevents CSE across iterations. -/
@[noinline] def runParseIO {n : Nat} (ref : IO.Ref (Text n)) : IO Nat := do
  let t ← ref.get
  return match jsonCount.runResult? t with
         | some c => c
         | none   => 0

/-- The basename of a path (the part after the last `/`), matching the
`prim-parser <basename> count=<n> ...` line shape the sibling harnesses print, so
`bench/run-all.sh`'s shell-level `gate()` can independently verify this harness's count
by matching on the dataset name in the line, the same way it gates every other harness. -/
def basename (path : String) : String :=
  (path.splitOn "/").getLast?.getD path

def main (args : List String) : IO UInt32 := do
  let path := args.getD 0 "bench/data/canada.json"
  let content ← IO.FS.readFile path

  -- ── Build String → List Char → Text (List.Vector Char n) ──────────────
  -- Lean is eager: binding `text` already forces the list spine. Timing around it
  -- measures the conversion; the IO.Ref below blocks CSE across the parse loop.
  let t0 ← IO.monoNanosNow
  let text := toText content
  let textRef ← IO.mkRef text
  let t1 ← IO.monoNanosNow
  let vecBuildNs : Int := (t1 : Int) - (t0 : Int)

  -- Correctness check on first parse. Exits nonzero on mismatch (not just an eprintln)
  -- so a regression fails the process whether it's invoked directly or through
  -- run-all.sh's `run`, which otherwise only gates on the printed line's dataset name.
  let firstCount ← runParseIO textRef
  IO.println s!"prim-parser-upstream {basename path} count={firstCount}"
  if firstCount != 111130 then
    IO.eprintln s!"ERROR: expected 111130, got {firstCount}"
    return 1

  IO.println s!"text_build_ns={vecBuildNs}"
  IO.println s!"text_build_ms={vecBuildNs / 1_000_000}"

  -- ── Best-of-20 timed parse runs ──────────────────────────────────────────
  -- Using IO.Ref to prevent CSE of runParseIO across iterations.
  let sink ← IO.mkRef (0 : Nat)
  let iters := 20
  let mut best : Int := (4611686018427387903 : Int)
  for _ in List.range iters do
    let s0 ← IO.monoNanosNow
    let c ← runParseIO textRef
    let s1 ← IO.monoNanosNow
    sink.modify (· + c)
    let elapsed : Int := (s1 : Int) - (s0 : Int)
    if elapsed < best then
      best := elapsed
  let _ ← sink.get
  IO.println s!"parse_best_ns={best}"
  IO.println s!"parse_best_ms={best / 1_000_000}"
  IO.println s!"prim-parser commit=0728704 lean=v4.28.0 mathlib=v4.28.0"
  return 0
