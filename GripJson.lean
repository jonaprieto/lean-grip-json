/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides

The inductive `Json` value type and the peek-then-branch (char-dispatched) recursive
descent are adapted from Examples/Json.lean in prim-parser by Jan Mas Rovira
(https://github.com/janmasrovira/prim-parser, commit d34c6f0, 2026-07-04): the
constructor shape and the dispatch-on-first-character structure.

The number representation follows Lean's `Lean.Data.Json.JsonNumber`: a number is an
exact `mantissa * 10 ^ (-exponent)` with `mantissa : Int` and `exponent : Nat`, so no
value is rounded (unlike a `Float`).

grip keeps the strict RFC-8259 grammar of the `examples/Json.lean` validator and builds
values over the flat byte core, rather than prim-parser's size-indexed vector.
-/

import Grip

/-!
# Grip.Json: a value-producing, RFC-8259 JSON parser

Where the `examples/Json.lean` validator returns a leaf count, this module builds a
real `Json` value (a DOM). `import GripJson`, then `Grip.Json.parse : ByteArray →
Except ParseError Json` (or `parseString` from a `String`).

## Design

The grammar is the same grammar-strict RFC-8259 one as the validator: leading
zeros (`01`), trailing dots (`1.`), bare exponents (`1e`), trailing commas, bad
escapes and trailing garbage are all rejected. Each grammar arm additionally builds a
value:

- numbers are decoded straight from their consumed byte range (`GParser.captureWith?`)
  to an exact `.num mantissa exponent` (the value `mantissa * 10 ^ (-exponent)`); no
  `Float` is involved, so no value is rounded;
- strings are scanned and their escapes decoded in one pass (`scanStr`: `\n`, `\"`,
  `\uXXXX`, and UTF-16 surrogate pairs);
- arrays and objects recurse through `GParser.fix`.

This parser materializes a tree, so it does not keep the flat, allocation-free fast
path of the validator. It is the convenience API; the validator remains the benchmark.
-/

namespace Grip.Json

open Grip

/-- A JSON value. A number is the exact rational `num mantissa exponent`, denoting
`mantissa * 10 ^ (-exponent)` with `mantissa : Int` and `exponent : Nat` (Lean's
`JsonNumber` shape); an integer literal `n` is `num n 0`. Nothing is rounded. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num  (mantissa : Int) (exponent : Nat)
  | str  (s : String)
  | arr  (xs : Array Json)
  | obj  (kvs : Array (String × Json))
  deriving Repr, BEq, Inhabited

namespace Json

/-- Build an integer value: `int n = num n 0`. -/
@[inline] def int (n : Int) : Json := .num n 0

/-- The integer value, if this number has no fractional part. Strict: only `exponent = 0`
matches, so `20e-1` (parsed `num 20 1`, the value `2.0`) is not an integer, mirroring
`Lean.JsonNumber`. -/
def int? : Json → Option Int
  | .num m 0 => some m
  | _        => none

/-- Look up a key in an object (first match); `none` for a non-object or missing key. -/
def get? : Json → String → Option Json
  | .obj kvs, k => (kvs.find? (·.1 == k)).map (·.2)
  | _,       _  => none

/-- Index into an array; `none` for a non-array or an out-of-range index. -/
def at? : Json → Nat → Option Json
  | .arr xs, i => xs[i]?
  | _,       _ => none

end Json

namespace Decode

/-- State threaded through `unescape`'s single left fold. -/
structure UState where
  out   : String := ""
  esc   : Bool := false   -- previous char was a lone backslash
  uLeft : Nat := 0        -- hex digits still expected in a `\uXXXX` (0 = not in one)
  uAcc  : Nat := 0        -- hex value accumulated so far
  hi    : Nat := 0        -- pending high surrogate (0 = none)

/-- One step of `unescape`. Handles simple escapes, `\uXXXX`, and a high/low surrogate
pair combined into one scalar. Assumes a grammar-validated body, so malformed input is
handled leniently rather than rejected. -/
def uStep (st : UState) (c : Char) : UState :=
  if st.uLeft > 0 then
    let acc := st.uAcc * 16 + Grip.Ascii.hexValue (UInt8.ofNat c.toNat)
    if st.uLeft == 1 then
      if st.hi ≠ 0 then
        let full := 0x10000 + (st.hi - 0xD800) * 0x400 + (acc - 0xDC00)
        { st with out := st.out.push (Char.ofNat full), uLeft := 0, uAcc := 0, hi := 0 }
      else if 0xD800 ≤ acc && acc ≤ 0xDBFF then
        { st with uLeft := 0, uAcc := 0, hi := acc }
      else
        { st with out := st.out.push (Char.ofNat acc), uLeft := 0, uAcc := 0 }
    else
      { st with uLeft := st.uLeft - 1, uAcc := acc }
  else if st.esc then
    let st := { st with esc := false }
    if c == 'u' then { st with uLeft := 4, uAcc := 0 }
    else
      let d :=
        if c == 'n' then '\n'
        else if c == 't' then '\t'
        else if c == 'r' then '\r'
        else if c == 'b' then Char.ofNat 8
        else if c == 'f' then Char.ofNat 12
        else c   -- `"` `\` `/` decode to themselves
      { st with out := st.out.push d }
  else if c == '\\' then { st with esc := true }
  else { st with out := st.out.push c }

/-- Decode the escapes in a JSON string body (no surrounding quotes). Folds over `s.toList`
(not `s.foldl`) so the round-trip proof can rewrite with `String.toList_ofList`; this runs only
when a body actually contained a `\`-escape, off the escape-free fast path. -/
def unescape (s : String) : String := (s.toList.foldl uStep {}).out

/-- State threaded through `decodeNumber`'s single fold over the whole lexeme. -/
structure NState where
  mant    : Nat := 0     -- integer and fractional digits as one natural
  fracLen : Nat := 0     -- number of fractional digits
  phase   : Nat := 0     -- 0 = integer part, 1 = fraction, 2 = exponent
  mantNeg : Bool := false
  expNeg  : Bool := false
  expVal  : Nat := 0

/-- One step of the number decode, over a raw input byte. A `-` (45) is the mantissa sign
in phase 0 and the exponent sign in phase 2; `+` (43) only occurs in the exponent. Digit
bytes are `48..57`. -/
@[inline] def numByte (st : NState) (b : UInt8) : NState :=
  if b == 46 then { st with phase := 1 }                    -- '.'
  else if b == 101 || b == 69 then { st with phase := 2 }   -- 'e' / 'E'
  else if b == 43 then st                                   -- '+'
  else if b == 45 then                                      -- '-'
    (if st.phase == 2 then { st with expNeg := true } else { st with mantNeg := true })
  else
    let d := (b - 48).toNat
    if st.phase == 0 then { st with mant := st.mant * 10 + d }
    else if st.phase == 1 then { st with mant := st.mant * 10 + d, fracLen := st.fracLen + 1 }
    else { st with expVal := st.expVal * 10 + d }

/-- The largest net base-10 exponent the decoder folds into the mantissa. A positive net
exponent beyond this is rejected rather than powered: it bounds the widest integer the decoder
will materialize (`10 ^ maxExp`), keeping it far above any real datum yet well below the
`Nat.pow` panic threshold. The renderer also uses this as its largest expanded fractional
exponent, switching to JSON exponent notation beyond it. Without the bound, a pathological but
grammar-valid literal like the 600-digit exponent in `test/jsontestsuite/i_number_huge_exp.json`
aborts the process with `INTERNAL PANIC: Nat.pow exponent is too big`. `i_`-prefixed
JSONTestSuite numbers are implementation-defined, so rejecting them stays RFC-8259-conformant. -/
def maxExp : Nat := 1000000

/-- Decode a validated number lexeme spanning `arr[start .. stop)` to an exact
`.num mantissa exponent`, or `none` when the net positive exponent exceeds `maxExp` (which would
otherwise fold into an unbounded `10 ^ n` and panic). A nonnegative base-10 exponent is folded
into the mantissa (so `2e3` is `num 2000 0`), keeping `exponent : Nat`; a negative one becomes
the exponent (`2.5` is `num 25 1`). Folds `numByte` over the input bytes directly — no `capture`
`String`, no per-char UTF-8 decode. -/
@[inline] def decodeNumberBytes? (arr : ByteArray) (start stop : Nat) : Option Json :=
  let st := arr.foldl numByte {} start stop
  let mant : Int := if st.mantNeg then -(st.mant : Int) else st.mant
  let decExp : Int := (if st.expNeg then -(st.expVal : Int) else (st.expVal : Int)) - st.fracLen
  if decExp ≥ 0 then
    if decExp > (maxExp : Int) then none
    else some (Json.num (mant * (10 ^ decExp.toNat)) 0)
  else some (Json.num mant (-decExp).toNat)

end Decode

open Decode

-- Fused string literal: escape-aware scan + decode in one pass ------------

/-- The offset just past a valid `\`-escape whose backslash is at `q` (`arr[q] == 92`), or
`none` for a malformed one: a simple escape (`\" \\ \/ \b \f \n \r \t`) advances 2, a
`\uXXXX` advances 6. Isolated from `scanStr` so the scan loop stays flat. -/
@[inline] def escEnd (arr : ByteArray) (q : Nat) : Option Nat :=
  if h1 : q + 1 < arr.size then
    if arr[q + 1] == 34 || arr[q + 1] == 92 || arr[q + 1] == 47 || arr[q + 1] == 98
        || arr[q + 1] == 102 || arr[q + 1] == 110 || arr[q + 1] == 114 || arr[q + 1] == 116 then
      some (q + 2)
    else if arr[q + 1] == 117 then
      if h2 : q + 5 < arr.size then
        if Ascii.isHexDigit arr[q + 2] && Ascii.isHexDigit arr[q + 3]
            && Ascii.isHexDigit arr[q + 4] && Ascii.isHexDigit arr[q + 5] then some (q + 6)
        else none
      else none
    else none
  else none

/-- A valid escape strictly advances the scan (simple escape by 2, `\uXXXX` by 6). -/
theorem escEnd_gt (arr : ByteArray) (q q' : Nat) (h : escEnd arr q = some q') : q < q' := by
  rw [escEnd] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; omega
    · split at h
      · split at h
        · split at h
          · simp only [Option.some.injEq] at h; omega
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Scan a strict RFC-8259 string body and produce the decoded `String` in one pass. `q0` is
the opening-quote index and `q` the current scan position; `esc` accumulates whether any `\`
was seen. On the closing quote the body `arr[q0+1 .. q)` is validated and decoded as UTF-8 in
one pass (`String.fromUTF8?`, no separate validation walk) and unescaped only when `esc`;
invalid UTF-8 in the body is rejected rather than silently decoded to an empty string. No
second backslash pass and no intermediate `capture`/escape-flag allocation. Escapes are
validated by `escEnd`, keeping this loop flat. Total (structural on `arr.size - q`). -/
@[specialize] def scanStr (arr : ByteArray) (q0 q : Nat) (esc : Bool) : ParseResult String :=
  if h : q < arr.size then
    if arr[q] == 34 then
      match String.fromUTF8? (arr.extract (q0 + 1) q) with
      | some body => .ok (if esc then unescape body else body) (q + 1)
      | none       => .error ⟨q0, ["a string body in valid UTF-8"]⟩
    else if arr[q] == 92 then
      match hE : escEnd arr q with
      | some q' => scanStr arr q0 q' true
      | none    => .error ⟨q, ["an escape (\\\" \\\\ \\/ \\b \\f \\n \\r \\t \\uXXXX)"]⟩
    else if arr[q] < 32 then .error ⟨q, ["an unescaped string character"]⟩
    else scanStr arr q0 (q + 1) esc
  else .error ⟨q, ["a closing '\"'"]⟩
termination_by arr.size - q
decreasing_by
  · exact Nat.sub_lt_sub_left h (escEnd_gt arr q q' hE)
  · omega

/-- `scanStr` strictly advances past its current position on success. -/
theorem scanStr_gt (arr : ByteArray) (q0 q q' : Nat) (esc : Bool) (a : String)
    (h : scanStr arr q0 q esc = .ok a q') : q < q' := by
  rw [scanStr] at h
  split at h
  · rename_i hq
    split at h
    · split at h
      · simp only [ParseResult.ok.injEq] at h; omega
      · exact absurd h (by simp)
    · split at h
      · split at h
        · next q'' hE =>
            have := escEnd_gt arr q q'' hE
            have := scanStr_gt arr q0 q'' q' true a h
            omega
        · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · have := scanStr_gt arr q0 (q + 1) q' esc a h; omega
  · exact absurd h (by simp)
termination_by arr.size - q
decreasing_by
  all_goals
    first
      | omega
      | exact Nat.sub_lt_sub_left ‹q < arr.size› (escEnd_gt arr q _ ‹escEnd arr q = some _›)

/-- `scanStr` stays within bounds on success. -/
theorem scanStr_le (arr : ByteArray) (q0 q q' : Nat) (esc : Bool) (a : String)
    (h : scanStr arr q0 q esc = .ok a q') : q' ≤ arr.size := by
  rw [scanStr] at h
  split at h
  · rename_i hq
    split at h
    · split at h
      · simp only [ParseResult.ok.injEq] at h; omega
      · exact absurd h (by simp)
    · split at h
      · split at h
        · next q'' hE => exact scanStr_le arr q0 q'' q' true a h
        · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · exact scanStr_le arr q0 (q + 1) q' esc a h
  · exact absurd h (by simp)
termination_by arr.size - q
decreasing_by
  all_goals
    first
      | omega
      | exact Nat.sub_lt_sub_left ‹q < arr.size› (escEnd_gt arr q _ ‹escEnd arr q = some _›)

-- Leaf value parsers -----------------------------------------------------

/-- Fractional part: a `.` then one or more digits. -/
@[inline] def frac : GParser conditional Nat :=
  GParser.seqR (GParser.ch '.') (GParser.takeWhile1 Ascii.isDigit)

/-- Exponent part: `e`/`E`, an optional sign, then one or more digits. -/
@[inline] def expo : GParser conditional Nat :=
  GParser.seqR (GParser.satisfy Ascii.isExp)
    (GParser.seqR (GParser.optional (GParser.satisfy Ascii.isSign))
      (GParser.takeWhile1 Ascii.isDigit))

/-- Integer part: a lone `0`, or a nonzero digit followed by any digits (no leading zeros). -/
@[inline] def intPart : GParser conditional Unit :=
  GParser.alt (GParser.ch '0')
    (GParser.seqR (GParser.satisfy Ascii.isDigit19)
      (GParser.seqR (GParser.takeWhile Ascii.isDigit) (GParser.pure ())))

/-- A JSON number, decoded to `.num` straight from the consumed byte range (no `capture`
`String`). Leading-zero and trailing-garbage rejection come from the grammar and the
top-level EOF check. -/
@[inline] def number : GParser conditional Json :=
  GParser.captureWith? decodeNumberBytes?
    (GParser.seqR (GParser.optional (GParser.ch '-'))
      (GParser.seqL intPart
        (GParser.seqR (GParser.optional frac) (GParser.optional expo)))) <?> "a number"

/-- A validated JSON string literal decoded to its `String` contents in a single scan. The
escape-aware body scan reports whether any `\` occurred, so `unescape` runs only when it
must and there is no separate backslash pass over the body. -/
@[inline] def jstr : GParser conditional String where
  run := fun arr q =>
    if h : q < arr.size then
      (if arr[q] == 34 then scanStr arr q (q + 1) false else .error ⟨q, ["a string"]⟩)
    else .error ⟨q, ["a string"]⟩
  cwit := by
    intro arr q a q' heq
    split at heq
    · split at heq
      · have := scanStr_gt arr q (q + 1) q' false a heq; omega
      · exact absurd heq (by simp)
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)
  bwit := by
    intro arr q a q' hq heq
    split at heq
    · split at heq
      · exact scanStr_le arr q (q + 1) q' false a heq
      · exact absurd heq (by simp)
    · exact absurd heq (by simp)

/-- A JSON string literal as a `Json.str` value. -/
@[inline] def jstring : GParser conditional Json := GParser.map Json.str jstr
/-- The keyword `null` as a `Json` value. -/
@[inline] def jnull  : GParser conditional Json :=
  GParser.map (fun _ => Json.null) (GParser.string "null") <?> "null"
/-- The keyword `true` as a `Json` value. -/
@[inline] def jtrue  : GParser conditional Json :=
  GParser.map (fun _ => Json.bool true) (GParser.string "true") <?> "true"
/-- The keyword `false` as a `Json` value. -/
@[inline] def jfalse : GParser conditional Json :=
  GParser.map (fun _ => Json.bool false) (GParser.string "false") <?> "false"

-- Recursive value via `fix` ----------------------------------------------

/-- Skip leading whitespace, then first-byte dispatch, fused into one primitive. Versus
`seqR ws (dispatch …)` this avoids allocating (and discarding) `ws`'s byte count and the
extra combinator indirection on every value entry. Grade `conditional`: the dispatched
parser consumes, and whitespace only advances the offset further. -/
@[inline] def wsDispatch (select : UInt8 → GParser conditional Json) :
    GParser conditional Json where
  run := fun arr q =>
    let p := scanFwd arr Ascii.isWs q
    if _ : p < arr.size then (select arr[p]).run arr p else .error ⟨p, ["a JSON value"]⟩
  cwit := by
    intro arr q a q' heq
    simp only [] at heq
    split at heq
    · have hge := scanFwd_ge arr Ascii.isWs q
      have hc := (select _).cwit heq
      omega
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)
  bwit := by
    intro arr q a q' hq heq
    simp only [] at heq
    split at heq
    · have hle := scanFwd_le arr Ascii.isWs q hq
      exact (select _).bwit hle heq
    · exact absurd heq (by simp)

/-- Skip leading whitespace, then match the single byte `b`, consuming it. Fused so a
structural token after whitespace costs one scan and one compare with no discarded `ws` count
allocation. `name` is the expected-label reported when the byte is not there. -/
@[inline] def wsByte (b : UInt8) (name : String) : GParser conditional Unit where
  run := fun arr q =>
    let p := scanFwd arr Ascii.isWs q
    if _ : p < arr.size then
      (if arr[p] == b then .ok () (p + 1) else .error ⟨p, [name]⟩)
    else .error ⟨p, [name]⟩
  cwit := by
    intro arr q a q' heq
    simp only [] at heq
    split at heq
    · split at heq
      · have hge := scanFwd_ge arr Ascii.isWs q
        simp only [ParseResult.ok.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        omega
      · exact absurd heq (by simp)
    · exact absurd heq (by simp)
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)
  bwit := by
    intro arr q a q' hq heq
    simp only [] at heq
    split at heq
    · rename_i hb
      split at heq
      · simp only [ParseResult.ok.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        omega
      · exact absurd heq (by simp)
    · exact absurd heq (by simp)

/-- Scan a container body: `elem`s separated by `,`, terminated by the single byte `close`.
`first` is `true` before any element has been parsed, where no separator is expected.

Unlike `GParser.foldMany` this loop is *committed*, which is what makes the reported error
position the position of the real problem:

- in the tail (`first = false`), a `,` obliges an element, and a failure inside it propagates
  unchanged instead of being swallowed by a zero-or-more fold whose type says it never errors;
- at the head (`first = true`), the empty container is a fallback taken only when `elem` fails
  *and* the next non-whitespace byte is `close`. A failed first element followed by anything
  else reports `elem`'s own error rather than "expected `close`" back at the opening bracket.
  No element can start at a `close` byte, so this fallback never masks a real failure.

Total: structural on `arr.size - q`, using `elem`'s `cwit` (it always consumes) to strictly
advance. The `q < q' ∧ q' ≤ arr.size` guard is never false for a graded `elem`, but stating it
here is what makes the measure decrease without a bounds hypothesis on the caller. -/
@[specialize] def bodyFwd {α β : Type} (push : β → α → β) (elem : GParser conditional α)
    (close : UInt8) (closeName : String) (arr : ByteArray) (acc : β) (first : Bool) (q : Nat) :
    ParseResult β :=
  if first then
    match elem.run arr q with
    | .ok x q' =>
      if h : q < q' ∧ q' ≤ arr.size then
        bodyFwd push elem close closeName arr (push acc x) false q'
      else .error ⟨q', []⟩
    | .error e =>
      let p := scanFwd arr Ascii.isWs q
      if _ : p < arr.size then (if arr[p] == close then .ok acc (p + 1) else .error e)
      else .error e
  else
    let p := scanFwd arr Ascii.isWs q
    if _ : p < arr.size then
      if arr[p] == close then .ok acc (p + 1)
      else if arr[p] == Ascii.comma then
        match elem.run arr (p + 1) with
        | .ok x q' =>
          if h2 : q < q' ∧ q' ≤ arr.size then
            bodyFwd push elem close closeName arr (push acc x) false q'
          else .error ⟨q', []⟩
        | .error e => .error e
      else .error ⟨p, ["','", closeName]⟩
    else .error ⟨p, ["','", closeName]⟩
termination_by arr.size - q
decreasing_by
  · omega
  · have := scanFwd_ge arr Ascii.isWs q
    omega

/-- `bodyFwd` strictly advances past its starting offset on success: it always consumes at
least the closing byte. -/
theorem bodyFwd_gt {α β : Type} (push : β → α → β) (elem : GParser conditional α)
    (close : UInt8) (closeName : String) (arr : ByteArray) (acc : β) (first : Bool)
    (q : Nat) (b : β) (q' : Nat)
    (h : bodyFwd push elem close closeName arr acc first q = .ok b q') : q < q' := by
  rw [bodyFwd] at h
  simp only [] at h
  have hge := scanFwd_ge arr Ascii.isWs q
  split at h
  · split at h
    · next x q'' _ =>
        split at h
        · next hg =>
            have := bodyFwd_gt push elem close closeName arr (push acc x) false q'' b q' h
            omega
        · exact absurd h (by simp)
    · split at h
      · split at h
        · simp only [ParseResult.ok.injEq] at h; omega
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  · split at h
    · split at h
      · simp only [ParseResult.ok.injEq] at h; omega
      · split at h
        · split at h
          · next x q'' _ =>
              split at h
              · next hg =>
                  have := bodyFwd_gt push elem close closeName arr (push acc x) false q'' b q' h
                  omega
              · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
    · exact absurd h (by simp)
termination_by arr.size - q
decreasing_by
  · omega
  · have := scanFwd_ge arr Ascii.isWs q
    omega

/-- `bodyFwd` stays within bounds on success. -/
theorem bodyFwd_le {α β : Type} (push : β → α → β) (elem : GParser conditional α)
    (close : UInt8) (closeName : String) (arr : ByteArray) (acc : β) (first : Bool)
    (q : Nat) (b : β) (q' : Nat)
    (h : bodyFwd push elem close closeName arr acc first q = .ok b q') : q' ≤ arr.size := by
  rw [bodyFwd] at h
  simp only [] at h
  have hge := scanFwd_ge arr Ascii.isWs q
  split at h
  · split at h
    · next x q'' _ =>
        split at h
        · next hg => exact bodyFwd_le push elem close closeName arr (push acc x) false q'' b q' h
        · exact absurd h (by simp)
    · split at h
      · rename_i hp
        split at h
        · simp only [ParseResult.ok.injEq] at h; omega
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  · split at h
    · rename_i hp
      split at h
      · simp only [ParseResult.ok.injEq] at h; omega
      · split at h
        · split at h
          · next x q'' _ =>
              split at h
              · next hg =>
                  exact bodyFwd_le push elem close closeName arr (push acc x) false q'' b q' h
              · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
    · exact absurd h (by simp)
termination_by arr.size - q
decreasing_by
  · omega
  · have := scanFwd_ge arr Ascii.isWs q
    omega

/-- A whole container body: `elem`s separated by `,`, terminated by `close`, folded into `acc`
with `push`. Consumes the closing byte, so it is `conditional` (always consumes on success).
Fusing the separator loop and the terminator into one parser is what lets a failure inside an
element reach the caller instead of being turned into "expected `]`" at the separator. -/
@[inline] def containerBody {α β : Type} (push : β → α → β) (elem : GParser conditional α)
    (close : UInt8) (closeName : String) (acc : β) : GParser conditional β where
  run := fun arr q => bodyFwd push elem close closeName arr acc true q
  cwit := by
    intro arr q b q' h; exact bodyFwd_gt push elem close closeName arr acc true q b q' h
  ewit := by intro he; exact absurd he (by decide)
  swit := by intro he; exact absurd he (by decide)
  bwit := by
    intro arr q b q' _ h; exact bodyFwd_le push elem close closeName arr acc true q b q' h

/-- Named body of the recursive JSON value parser. Proofs reference
    `GParser.fixFuel valueBody` directly. -/
def valueBody (rec : GParser conditional Json) : GParser conditional Json :=
  -- The container sub-parsers reference `rec`, so `fix` rebuilds them on every entry.
  -- Building them inside the taken dispatch arm (not eagerly before the dispatch) means a
  -- leaf value (string/number/keyword) constructs no array/object machinery at all.
  wsDispatch
    (fun b =>
      if b == Ascii.lbrace then
        -- `rec` skips its own leading whitespace, so no `ws` before it after `:`; the key
        -- needs one because `jstr` does not, and `containerBody` only skips up to the `,`.
        let pair : GParser conditional (String × Json) :=
          GParser.map2 (fun k v => (k, v)) jstr (GParser.seqR (wsByte Ascii.colon "':'") rec)
        GParser.seqR (GParser.ch '{')
          (GParser.map Json.obj
            (containerBody (fun (a : Array (String × Json)) x => a.push x)
              (GParser.seqR GParser.ws pair) Ascii.rbrace "'}'" #[]))
      else if b == Ascii.lbracket then
        GParser.seqR (GParser.ch '[')
          (GParser.map Json.arr
            (containerBody (fun (a : Array Json) e => a.push e) rec Ascii.rbracket "']'" #[]))
      else if b == Ascii.quote then jstring
      else if b == Ascii.code 't' then jtrue
      else if b == Ascii.code 'f' then jfalse
      else if b == Ascii.code 'n' then jnull
      else if Ascii.isDigit b || b == Ascii.dash then number
      -- A byte that starts no value: always fails (the mapped `null` is unreachable).
      else GParser.map (fun _ => Json.null) (GParser.satisfy (fun _ => false)) <?>
        "a JSON value")

/-- A JSON value of any shape: object, array, string, number, or keyword. Recursion is
tied by `GParser.fix`, so the grammar is total and left recursion fails rather than loops. -/
def value : GParser conditional Json := GParser.fix valueBody

/-- One complete JSON document: a value, optional trailing whitespace, then EOF (so
trailing garbage is rejected). -/
def parser : GParser conditional Json := GParser.seqL value (GParser.seqR GParser.ws GParser.eof)

/-- Parse a complete JSON document from a `ByteArray`, returning the value or a
positioned `ParseError`. -/
def parse (arr : ByteArray) : Except ParseError Json := parser.parse arr

/-- Parse a complete JSON document from a `String`. -/
def parseString (s : String) : Except ParseError Json := parser.parse s.toUTF8

-- Serialization ----------------------------------------------------------

namespace Json

/-- The lowercase hex digit for `n < 16`; `'0'` for larger `n`. -/
def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

/-- The JSON escape of a single character, as the list of output characters: `"`, `\`, and the
named control escapes map to a two-character sequence, other control bytes to `\u00XX`, and every
other character to itself. -/
def escapeChar (c : Char) : List Char :=
  if c == '"' then ['\\', '"']
  else if c == '\\' then ['\\', '\\']
  else if c == '\n' then ['\\', 'n']
  else if c == '\t' then ['\\', 't']
  else if c == '\r' then ['\\', 'r']
  else if c == Char.ofNat 8 then ['\\', 'b']
  else if c == Char.ofNat 12 then ['\\', 'f']
  else if c.toNat < 0x20 then
    ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
  else [c]

/-- Escape a string body for JSON output: `"`, `\`, and control characters. Non-ASCII is
emitted verbatim (valid UTF-8 JSON). Builds the output as one `List Char` (`flatMap`) and
materializes it once, so it is linear rather than quadratic in the escaped length. -/
def escape (s : String) : String := String.ofList (s.toList.flatMap escapeChar)

/-- Render an exact `num mantissa exponent` to a decimal literal, inserting the point
`exponent` digits from the right (`num 25 1` → `"2.5"`, `num 5 3` → `"0.005"`). -/
def renderNum (m : Int) (e : Nat) : String :=
  if e == 0 then (if m < 0 then "-" else "") ++ toString m.natAbs
  else
    let ds := List.replicate (e + 1 - (toString m.natAbs).length) '0' ++ (toString m.natAbs).toList
    let k := ds.length - e
    (if m < 0 then "-" else "") ++ String.ofList (ds.take k) ++ "." ++ String.ofList (ds.drop k)

/-- Render a fractional number using JSON exponent notation. This avoids materializing `e`
zeroes for large scales while preserving the exact `num m e` representation on parse. -/
def renderNumScientific (m : Int) (e : Nat) : String :=
  (if m < 0 then "-" else "") ++ toString m.natAbs ++ "e-" ++ toString e

/-- Serialize a numeric DOM value. Ordinary values retain their canonical expanded decimal form;
large fractional exponents use compact scientific notation so rendering remains proportional to
the exponent's digit count rather than its value. -/
def renderNumber (m : Int) (e : Nat) : String :=
  if e > maxExp then renderNumScientific m e else renderNum m e

/-- Join a list of strings with a separator, proof-friendly alternative to `String.intercalate`.
The output is identical: `joinWith sep ss = String.intercalate sep ss`. -/
def joinWith (sep : String) : List String → String
  | []         => ""
  | [s]        => s
  | s :: rest  => s ++ sep ++ joinWith sep rest

/-- Serialize a value to compact RFC-8259 JSON (no insignificant whitespace). Parsing the result
recovers the exact `Json` value, including the numeric mantissa/exponent representation. Total:
structural on `sizeOf`; `attach` carries the membership proof each recursive call decreases by. -/
def render : Json → String
  | .null       => "null"
  | .bool true  => "true"
  | .bool false => "false"
  | .num m e    => renderNumber m e
  | .str s      => "\"" ++ escape s ++ "\""
  | .arr xs     =>
    "[" ++ joinWith "," (xs.attach.toList.map (fun x => render x.1)) ++ "]"
  | .obj kvs    =>
    "{" ++ joinWith ","
      (kvs.attach.toList.map (fun ⟨(k, j), _h⟩ => "\"" ++ escape k ++ "\":" ++ render j)) ++ "}"
termination_by v => sizeOf v
decreasing_by
  · have := Array.sizeOf_lt_of_mem x.2; simp_wf; omega
  · have hm := Array.sizeOf_lt_of_mem _h
    simp only [Prod.mk.sizeOf_spec] at hm
    simp_wf; omega

instance : ToString Json := ⟨render⟩

end Json

end Grip.Json

/-! ### Sanity guards. -/
section
open Grip Grip.Json

#guard (GParser.run? parser "null".toUTF8) == some Json.null
#guard (GParser.run? parser "true".toUTF8) == some (Json.bool true)
#guard (GParser.run? parser "false".toUTF8) == some (Json.bool false)
-- integers are `num n 0`, full bignum precision, signs handled
#guard (GParser.run? parser "42".toUTF8) == some (Json.num 42 0)
#guard (GParser.run? parser "-42".toUTF8) == some (Json.num (-42) 0)
#guard (GParser.run? parser "0".toUTF8) == some (Json.num 0 0)
#guard (GParser.run? parser "123456789012345678901234567890".toUTF8)
        == some (Json.num 123456789012345678901234567890 0)
-- fraction / exponent / signs => exact mantissa * 10^(-exponent), no rounding
#guard (GParser.run? parser "2.5".toUTF8) == some (Json.num 25 1)
#guard (GParser.run? parser "-2.5e3".toUTF8) == some (Json.num (-2500) 0)
#guard (GParser.run? parser "5e-1".toUTF8) == some (Json.num 5 1)
-- exponent within `maxExp` folds; a huge positive one is rejected, not powered (no panic)
#guard (GParser.run? parser "1e6".toUTF8) == some (Json.num 1000000 0)
#guard (GParser.run? parser "1e999999999999".toUTF8) == none
#guard (GParser.run? parser "1e-999999999999".toUTF8) == some (Json.num 1 999999999999)
#guard Json.renderNumber 1 (Decode.maxExp + 1) == "1e-1000001"
#guard (GParser.run? parser (Json.render (Json.num 1 (Decode.maxExp + 1))).toUTF8) ==
  some (Json.num 1 (Decode.maxExp + 1))
#guard (GParser.run? parser (Json.render (Json.num (-1) (Decode.maxExp + 1))).toUTF8) ==
  some (Json.num (-1) (Decode.maxExp + 1))
-- `int` smart constructor and strict `int?` extractor
#guard Json.int 42 == Json.num 42 0
#guard (Json.num 42 0).int? == some 42
#guard (Json.num 25 1).int? == none
#guard Json.null.int? == none
-- accessors
#guard (Json.obj #[("a", Json.int 1)]).get? "a" == some (Json.int 1)
#guard (Json.obj #[("a", Json.int 1)]).get? "b" == none
#guard Json.null.get? "a" == none
#guard (Json.arr #[Json.int 1, Json.int 2]).at? 1 == some (Json.int 2)
#guard (Json.arr #[Json.int 1]).at? 5 == none
-- strings: escapes and \u decode
#guard (GParser.run? parser "\"a\\nb\"".toUTF8) == some (Json.str "a\nb")
#guard (GParser.run? parser "\"\\u0041\"".toUTF8) == some (Json.str "A")
#guard (GParser.run? parser "\"\\uD834\\uDD1E\"".toUTF8) == some (Json.str "𝄞")
-- containers
#guard (GParser.run? parser "[1,2,3]".toUTF8)
        == some (Json.arr #[Json.num 1 0, Json.num 2 0, Json.num 3 0])
#guard (GParser.run? parser "[]".toUTF8) == some (Json.arr #[])
#guard (GParser.run? parser "[ 1 , 2 ]".toUTF8)               -- whitespace around array elements
        == some (Json.arr #[Json.num 1 0, Json.num 2 0])
#guard (GParser.run? parser "{}".toUTF8) == some (Json.obj #[])
#guard (GParser.run? parser "  { \"a\" : true , \"b\" : [1] }  ".toUTF8)
        == some (Json.obj #[("a", Json.bool true), ("b", Json.arr #[Json.num 1 0])])
-- strict RFC-8259 rejections
#guard (GParser.run? parser "01".toUTF8) == none            -- leading zero
#guard (GParser.run? parser "1.".toUTF8) == none            -- trailing dot
#guard (GParser.run? parser "1e".toUTF8) == none            -- bare exponent
#guard (GParser.run? parser "[1,]".toUTF8) == none          -- trailing comma
#guard (GParser.run? parser "1 2".toUTF8) == none           -- trailing garbage
#guard (GParser.run? parser "\"a\\q\"".toUTF8) == none      -- bad escape

-- serialization: render is compact and round-trips through parse
#guard toString (Json.num 25 1) == "2.5"
#guard toString (Json.num 5 3) == "0.005"
#guard toString (Json.num (-5) 1) == "-0.5"
#guard toString (Json.int 42) == "42"
#guard toString (Json.str "a\nb\"c") == "\"a\\nb\\\"c\""
#guard toString (Json.arr #[Json.int 1, Json.int 2]) == "[1,2]"
#guard toString (Json.obj #[("a", Json.bool true)]) == "{\"a\":true}"
#guard
  (let v := Json.obj #[("a", Json.arr #[Json.num 25 1, Json.null]), ("b", Json.str "x\ty")]
   parseString (toString v) == .ok v)

end
