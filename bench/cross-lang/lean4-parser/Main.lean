/-
lean4-parser (fgdorais) JSON validate-and-count benchmark — CHAR-LEVEL.
Stream type : String.Slice Char  (the shipped example's idiom)
Combinators : foldl (non-allocating accumulator), NOT sepBy (allocates Array)
Toolchain   : leanprover/lean4:v4.28.0  (rev d8428e2 of lean4-parser)

NOTE: byte-level ByteSlice backtracking is broken in all v4.28.0-compatible lean4-parser
  revisions: setPosition uses a relative slice offset instead of an absolute byteArray
  offset (bug fixed in commit f6d600f/#127, which requires v4.32.0-rc1 toolchain).
  This Char-level version uses the library's actual intended design — same idiom as the
  shipped examples/JSON.lean example. The tradeoff: String.Slice decodes UTF-8 to chars.
-/
import Parser
import Parser.Char

namespace L4pJsonChar

open Parser Char

/-- Char-level parser monad (the shipped example's idiom) -/
protected abbrev P := SimpleParser String.Slice Char

@[inline] private def isWs (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\r' || c == '\t'
@[inline] private def isNum (c : Char) : Bool :=
  c.isDigit || c == '.' || c == '-' || c == '+' || c == 'e' || c == 'E'
@[inline] private def isAlpha (c : Char) : Bool := c.isAlpha

/-- Skip whitespace (non-allocating: foldl via dropMany) -/
@[inline] def ws : L4pJsonChar.P Unit :=
  dropMany (tokenFilter isWs)

/-- Escape-aware string body: skip chars until an unescaped `"`, treating `\` as escaping the
    next char (so `\"` does not end the string). Needed for citm/twitter, which contain `\"`. -/
partial def skipStrBody : L4pJsonChar.P Unit := do
  let c ← anyToken
  if c == '"' then return ()
  else if c == '\\' then do let _ ← anyToken; skipStrBody
  else skipStrBody

/-- Skip a string: consume the opening '"', then the escape-aware body (which consumes the
    closing '"'). -/
def skipStr : L4pJsonChar.P Unit := do
  drop 1 (token '"')
  skipStrBody

mutual

/-- Parse a JSON value; returns leaf count -/
protected partial def value : L4pJsonChar.P Nat := do
  ws
  let c ← anyToken
  if c == '{' then L4pJsonChar.object
  else if c == '[' then L4pJsonChar.array
  else if c == '"' then do
    skipStrBody
    return 1
  else if c == 't' || c == 'f' || c == 'n' then do
    dropMany (tokenFilter isAlpha)
    return 1
  else if c.isDigit || c == '-' then do
    dropMany (tokenFilter isNum)
    return 1
  else
    throwUnexpected (some c)

/-- Parse members of an object; keys not counted, only values.
    Uses foldl (non-allocating) instead of sepBy (allocates Array).
    After `{` is already consumed by `value`, this reads: ws (} | pair (, pair)*) ws }
-/
protected partial def object : L4pJsonChar.P Nat := do
  ws
  match ← option? (token '}') with
  | some _ => return 0   -- empty object: `}`
  | none =>
    let n0 ← L4pJsonChar.pair
    let total ← foldl (· + ·) n0 do
      ws
      drop 1 (token ',')
      L4pJsonChar.pair
    ws
    drop 1 (token '}')   -- consume closing `}`
    return total

/-- Parse one key:value pair (key string not counted, value counted) -/
protected partial def pair : L4pJsonChar.P Nat := do
  ws
  skipStr       -- key (not counted)
  ws
  drop 1 (token ':')
  L4pJsonChar.value

/-- Parse elements of an array.
    Uses foldl (non-allocating) instead of sepBy (allocates Array).
    After `[` is already consumed by `value`, this reads: ws (] | value (, value)*) ws ]
-/
protected partial def array : L4pJsonChar.P Nat := do
  ws
  match ← option? (token ']') with
  | some _ => return 0   -- empty array: `]`
  | none =>
    let n0 ← L4pJsonChar.value
    let total ← foldl (· + ·) n0 do
      ws
      drop 1 (token ',')
      L4pJsonChar.value
    ws
    drop 1 (token ']')   -- consume closing `]`
    return total

end

/-- Top-level entry: parse one JSON value from a String -/
def parse (s : String) : Option Nat :=
  match (ws *> L4pJsonChar.value).run s.toSlice with
  | .ok _ n => some n
  | .error _ _ => none

end L4pJsonChar

-- ===== Timing harness (mirrors grip's Bench.lean) =====

@[noinline] def barrierStr (_k : Nat) (s : String) : String := s

@[noinline] def parseL4p (s : String) : Nat :=
  match L4pJsonChar.parse s with
  | some n => n
  | none   => 0

def sampleMs (reps : Nat) (act : Nat → Nat) : IO (Float × Float) := do
  let mut samples : Array Float := #[]
  for i in [0:reps] do
    let t0 ← IO.monoNanosNow
    if act i == 0 then IO.eprintln "bench: unexpected zero count"
    let t1 ← IO.monoNanosNow
    samples := samples.push (Float.ofNat (t1 - t0) / 1000000.0)
  let sorted := samples.qsort (· < ·)
  return (sorted[0]!, sorted[sorted.size / 2]!)

def main (args : List String) : IO Unit := do
  -- Read as String (Char-level parser operates on String). Dataset path is argv[1].
  let file := args.getD 0 "/Users/jonaprieto/research/lean-grip/bench/data/canada.json"
  let base := (System.FilePath.mk file).fileName.getD file
  let src ← IO.FS.readFile file
  let count := parseL4p src
  if count == 0 then
    IO.eprintln s!"ERROR: parse failed on {base}"
    return
  let (ms, med) ← sampleMs 20 (fun i => parseL4p (barrierStr i src))
  IO.println s!"lean4-parser {base} count={count} best_ms={ms} med_ms={med}"
