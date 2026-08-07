/-
prim-parser JSON validate-and-count benchmark — grip cross-lang harness v3
Uses prim-parser's deep-embedded G (Graded) byte-combinator framework.

IMPORTANT: this is a genuine combinator parser — every grammar rule (number,
string, keyword, array, object) is built from G/Graded combinators
(satisfy, takeWhile1, takeWhile, bchar, starFold, alt, seqR/seqL, map,
bind, grecur). No raw arr[i]! indexing drives the grammar dispatch.
Only `Graded.scanB` is used outside the G grammar, for the trailing-
whitespace EOF check in the harness (same role as `takeWhile` would have
at the top level, but we need the position for the EOF check).

Counting rule (grip's rule):
  - number = 1, string = 1, keyword (true/false/null) = 1
  - object KEYS are NOT counted
  - arrays and objects contribute 0; their count = sum of children
  - top level = one value + optional whitespace + EOF (trailing garbage rejected)

Grammar strictness:
  - Numbers: fully strict RFC 8259: -? (0 | [1-9][0-9]*) (.[0-9]+)? ([eE][+-]?[0-9]+)?
    Rejects 00, 1., 1e, +1, lone -, leading zeros.
  - Strings: strict escape validation: \", \\, \/, \b, \f, \n, \r, \t, \uXXXX (4 hex).
    Rejects unescaped bytes < 0x20, unknown escapes, short \u.
    Bytes >= 0x80 pass opaque (no UTF-8 validation beyond grammar, matching grip).
  - Keywords: exact "true" / "false" / "null" (not prefix match of alpha run).
  - Whitespace: 0x20 0x09 0x0A 0x0D only.
-/
import PrimParser.Graded
open Graded

-- ---------------------------------------------------------------------------
-- gsepFold: p separated by sep, folding results into acc (no intermediate list).
-- Copied from bench/JCanada.lean — the canonical prim-parser sep-fold pattern.
-- ---------------------------------------------------------------------------

@[inline] def gsepFold {ρ γ β ge ge' α} (f : β → α → β) (acc : β)
    (sep : G ρ ⟨ge', always⟩ γ) (p : G ρ ⟨ge, always⟩ α) :=
  G.alt (G.bind p (fun x => G.starFold f (f acc x) (G.seqR sep p))) (G.pure acc)

-- ---------------------------------------------------------------------------
-- Main grammar: G Nat conditional Nat
-- ρ = Nat because grecur (the single fixpoint) returns Nat (leaf count).
-- ---------------------------------------------------------------------------

def gJson : G Nat conditional Nat :=
  -- Byte predicates (inlined for performance)
  let isDigit    : UInt8 → Bool := fun b => 48 ≤ b.toNat && b.toNat ≤ 57
  let isDigit19  : UInt8 → Bool := fun b => 49 ≤ b.toNat && b.toNat ≤ 57
  let isHex      : UInt8 → Bool := fun b =>
    (48 ≤ b.toNat && b.toNat ≤ 57) ||
    (65 ≤ b.toNat && b.toNat ≤ 70) ||
    (97 ≤ b.toNat && b.toNat ≤ 102)
  -- Safe string byte: >= 0x20, not '"' (34), not '\' (92)
  let isSafe : UInt8 → Bool := fun b => 32 ≤ b.toNat && b != 34 && b != 92
  -- Valid single-char escape: " \ / b f n r t
  let isSimpleEsc : UInt8 → Bool := fun b =>
    b == 34 || b == 92 || b == 47 || b == 98 || b == 102 || b == 110 || b == 114 || b == 116

  ---------------------------------------------------------------------------
  -- String body combinators (strict escape validation)
  -- strChunk: one safe run OR one valid escape sequence (always consumes ≥ 1 byte)
  -- ---------------------------------------------------------------------------
  -- \uXXXX: 'u' followed by exactly 4 hex digits
  let uEsc : G Nat conditional PUnit :=
    satisfy (· == 117) *>ᵍ  -- 'u'
    satisfy isHex       *>ᵍ
    satisfy isHex       *>ᵍ
    satisfy isHex       *>ᵍ
    satisfy isHex       *>ᵍ
    G.pure ()
  -- Single-char escape: reads EXACTLY ONE valid escape byte (satisfy, not takeWhile1,
  -- so it does not greedily consume subsequent quote characters or other escape bytes).
  let simpleEsc : G Nat conditional PUnit := (fun _ => ()) <$>ᵍ satisfy isSimpleEsc
  -- After '\': either a simple escape byte or \uXXXX
  let escBody : G Nat conditional PUnit := simpleEsc <|>ᵍ uEsc
  -- Full escape: '\' then escape body
  let escape : G Nat conditional PUnit :=
    satisfy (· == 92) *>ᵍ escBody  -- 92 = '\'
  -- One chunk: safe run of ≥1 bytes, or one escape sequence
  let strChunk : G Nat conditional PUnit := takeWhile1 isSafe <|>ᵍ escape

  ---------------------------------------------------------------------------
  -- String (quoted, strict): parses and validates, returns leaf count 1
  -- jstr_skip: same but returns PUnit (used for object keys, not counted)
  -- ---------------------------------------------------------------------------
  -- String body: zero or more chunks (starFold over strChunk)
  -- strChunk is conditional (⟨possibly, always⟩), satisfying ⟨ge, always⟩ for starFold.
  let strBody : G Nat flexible PUnit :=
    G.starFold (fun _ _ => ()) () strChunk
  let jstr_skip : G Nat conditional PUnit :=
    satisfy (· == 34) *>ᵍ strBody <*ᵍ satisfy (· == 34)  -- 34 = '"'
  let jstr : G Nat conditional Nat :=
    (fun _ => 1) <$>ᵍ jstr_skip

  ---------------------------------------------------------------------------
  -- Number (strict RFC 8259)
  -- optMinus: flexible (grade ⟨never, possibly⟩)
  -- intPart:  conditional (grade ⟨possibly, always⟩)
  -- optFrac:  flexible
  -- optExp:   flexible
  -- Combined: flexible * conditional * flexible * flexible = conditional
  ---------------------------------------------------------------------------
  let optMinus : G Nat flexible PUnit :=
    (fun _ => ()) <$>ᵍ satisfy (· == 45) <|>ᵍ G.pure ()  -- 45 = '-'
  -- Integer part: '0' alone, or [1-9][0-9]*
  let intPart : G Nat conditional PUnit :=
    (fun _ => ()) <$>ᵍ (satisfy (· == 48)) <|>ᵍ          -- '0'
    (satisfy isDigit19 *>ᵍ takeWhile isDigit)              -- [1-9][0-9]*
  -- Optional fraction: .[0-9]+
  let optFrac : G Nat flexible PUnit :=
    (fun _ => ()) <$>ᵍ (satisfy (· == 46) *>ᵍ takeWhile1 isDigit) <|>ᵍ G.pure ()  -- '.'
  -- Optional exponent: [eE][+-]?[0-9]+
  let optSign : G Nat flexible PUnit :=
    (fun _ => ()) <$>ᵍ satisfy (fun b => b == 43 || b == 45) <|>ᵍ G.pure ()  -- '+' or '-'
  let optExp : G Nat flexible PUnit :=
    (fun _ => ()) <$>ᵍ
      (satisfy (fun b => b == 101 || b == 69) *>ᵍ  -- 'e' or 'E'
       optSign *>ᵍ
       takeWhile1 isDigit) <|>ᵍ
    G.pure ()
  let jnum : G Nat conditional Nat :=
    (fun _ => 1) <$>ᵍ (optMinus *>ᵍ intPart *>ᵍ optFrac *>ᵍ optExp)

  ---------------------------------------------------------------------------
  -- Keywords: exact byte sequences (not any alpha run)
  -- true = 116 114 117 101, false = 102 97 108 115 101, null = 110 117 108 108
  ---------------------------------------------------------------------------
  let jkw : G Nat conditional Nat :=
    -- true
    ((fun _ => 1) <$>ᵍ
      (satisfy (· == 116) *>ᵍ satisfy (· == 114) *>ᵍ
       satisfy (· == 117) *>ᵍ satisfy (· == 101))) <|>ᵍ
    -- false
    ((fun _ => 1) <$>ᵍ
      (satisfy (· == 102) *>ᵍ satisfy (· == 97)  *>ᵍ
       satisfy (· == 108) *>ᵍ satisfy (· == 115) *>ᵍ satisfy (· == 101))) <|>ᵍ
    -- null
    ((fun _ => 1) <$>ᵍ
      (satisfy (· == 110) *>ᵍ satisfy (· == 117) *>ᵍ
       satisfy (· == 108) *>ᵍ satisfy (· == 108)))

  ---------------------------------------------------------------------------
  -- Array: [ value (, value)* ] or []
  -- Container contributes 0; count = sum of element leaf counts.
  -- grecur calls gJson (this same parser), which handles leading whitespace.
  ---------------------------------------------------------------------------
  let jarr : G Nat conditional Nat :=
    (fun n => n) <$>ᵍ
      (satisfy (· == 91) *>ᵍ        -- '['
       gsepFold (· + ·) 0 (satisfy (· == 44)) (ws *>ᵍ grecur) <*ᵍ  -- ',' sep
       ws <*ᵍ
       satisfy (· == 93))           -- ']'

  ---------------------------------------------------------------------------
  -- Object: { key: value (, key: value)* } or {}
  -- Keys are strings (validated but not counted).
  -- Container contributes 0; count = sum of member value leaf counts.
  -- jpair: ws "key" ws : value  — ws before key handled here
  ---------------------------------------------------------------------------
  let jpair : G Nat conditional Nat :=
    ws *>ᵍ jstr_skip *>ᵍ ws *>ᵍ satisfy (· == 58) *>ᵍ grecur  -- 58 = ':'
  let jobj : G Nat conditional Nat :=
    (fun n => n) <$>ᵍ
      (satisfy (· == 123) *>ᵍ       -- '{'
       gsepFold (· + ·) 0 (satisfy (· == 44)) jpair <*ᵍ  -- ',' sep
       ws <*ᵍ
       satisfy (· == 125))          -- '}'

  ---------------------------------------------------------------------------
  -- Top-level value: ws then dispatch on first byte
  -- Order: number first (common in canada.json), then string, keyword, array, object.
  -- All five alternatives remain so any valid JSON value parses.
  ---------------------------------------------------------------------------
  ws *>ᵍ (jnum <|>ᵍ jstr <|>ᵍ jkw <|>ᵍ jarr <|>ᵍ jobj)

-- ---------------------------------------------------------------------------
-- Run: parse ByteArray, check EOF (task requires rejecting trailing garbage).
-- After gJson returns, skip trailing whitespace then verify pos == arr.size.
-- Graded.scanB is the library's whitespace scanner (not hand-rolled byte walk).
-- ---------------------------------------------------------------------------

def isWs (b : UInt8) : Bool := b == 32 || b == 9 || b == 10 || b == 13

def runJson (arr : ByteArray) : Option Nat :=
  let fuel := arr.size * 64 + 64
  match G.run arr gJson fuel gJson 0 with
  | .ok v pos =>
    let pos' := Graded.scanB arr isWs fuel pos
    if pos' == arr.size then some v else none
  | .err _ => none

-- ---------------------------------------------------------------------------
-- Timing harness: best-of-20 in-process, IO.Ref sink prevents elision.
-- Use Option to distinguish "parse failed" (none) from "count=0" (some 0).
-- Pattern from JCanada.lean: sink.modify forces `n`, if-check prevents elision.
-- ---------------------------------------------------------------------------

def gripSampleMs (reps : Nat) (arr : ByteArray) : IO (Float × Float) := do
  let sink ← IO.mkRef (0 : Nat)
  let mut samples : Array Nat := #[]
  for _ in [0:reps] do
    let t0 ← IO.monoNanosNow
    let n := (runJson arr).getD 0
    let t1 ← IO.monoNanosNow
    if n == 0 then sink.modify (· + 1) else sink.modify (· + n)
    samples := samples.push (t1 - t0)
  let _ ← sink.get
  let sorted := samples.qsort (· < ·)
  return (Float.ofNat sorted[0]! / 1000000.0,
    Float.ofNat sorted[sorted.size / 2]! / 1000000.0)

def gripBasename (path : String) : String :=
  (path.splitOn "/").getLast?.getD path

def main (args : List String) : IO Unit := do
  let pathStr : String := match args with
    | p :: _ => p
    | [] => "/Users/jonaprieto/research/lean-grip/bench/data/canada.json"
  let arr ← IO.FS.readBinFile (pathStr : System.FilePath)
  match runJson arr with
  | none =>
    IO.eprintln s!"ERROR: parse failed on {pathStr}"
    IO.println s!"prim-parser {gripBasename pathStr} count=0 best_ms=0.0"
  | some count =>
    let (ms, med) ← gripSampleMs 20 arr
    IO.println s!"prim-parser {gripBasename pathStr} count={count} best_ms={ms} med_ms={med}"
