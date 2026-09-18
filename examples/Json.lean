/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import Grip

/-!
# Examples.Json: grammar-strict RFC-8259 JSON validator

Parses a JSON value and returns the count of JSON leaf-value nodes in its tree:
each number, string, `true`/`false`/`null` contributes 1; arrays and objects
contribute the sum of their element counts (the container itself adds nothing).

canada.json (GeoJSON, ~2.1 MB) uses floating-point coordinates (`-65.613033`).

## Design

This parser is written entirely from grip combinators and is grammar-strict per
RFC 8259: leading zeros (`01`) are rejected, trailing dots (`1.`) are rejected,
bare exponents (`1e`) are rejected, trailing commas are rejected, bad escapes
(`\q`) and bad `\u` sequences are rejected, and trailing garbage after the
top-level value is rejected via an explicit EOF check.

Recursion uses grip's `fix`, which is kernel-total via a fuel bounded by the bytes
remaining. The benchmark measures structural validation plus a leaf-node count.
-/

namespace Grip.Examples.Json

open Grip

-- Leaf parsers (non-recursive) ------------------------------------------

/-- Skip insignificant whitespace. -/
@[inline] private def ws : GParser flexible Nat := GParser.ws

/-- Exact keyword, dispatched by first byte; leaf count 1. -/
@[inline] private def keywordTrue : GParser conditional Nat :=
  (fun _ => 1) <$> GParser.string "true"
@[inline] private def keywordFalse : GParser conditional Nat :=
  (fun _ => 1) <$> GParser.string "false"
@[inline] private def keywordNull : GParser conditional Nat :=
  (fun _ => 1) <$> GParser.string "null"

/-- A `.frac` fragment: `.` then one or more digits. Fails hard if `.` is not
followed by a digit (so `1.` is rejected). -/
@[inline] private def frac : GParser conditional Nat :=
  GParser.seqR (GParser.ch '.') (GParser.takeWhile1 Ascii.isDigit)

/-- An exponent fragment: `[eE]` `[+-]?` digits. Fails hard if no digit follows. -/
@[inline] private def expo : GParser conditional Nat :=
  GParser.seqR (GParser.satisfy Ascii.isExp)
    (GParser.seqR (GParser.optional (GParser.satisfy Ascii.isSign))
      (GParser.takeWhile1 Ascii.isDigit))

/-- The integer part: `0` alone, or `[1-9]` then more digits. -/
@[inline] private def intPart : GParser conditional Unit :=
  GParser.alt (GParser.ch '0')
    (GParser.seqR (GParser.satisfy Ascii.isDigit19)
      (GParser.seqR (GParser.takeWhile Ascii.isDigit) (GParser.pure ())))

/-- A JSON number: `-? int frac? exp?`; leaf count 1. Leading-zero (`01`) and a
lone trailing token (`1 2`) are rejected by the top-level EOF check, not here. -/
@[inline] private def number : GParser conditional Nat :=
  (fun _ => 1) <$>
    (GParser.seqR (GParser.optional (GParser.ch '-'))
      (GParser.seqL intPart
        (GParser.seqR (GParser.optional frac) (GParser.optional expo))))

/-- A validated JSON string literal `"..."`; leaf count 1. One strict single-pass scan
(`GParser.stringLit`) validates escapes (incl. `\uXXXX`) and rejects unescaped control bytes,
replacing the old per-byte `foldMany` over a string-char combinator. -/
@[inline] private def jstring : GParser conditional Nat :=
  (fun _ => 1) <$> GParser.stringLit

-- Recursive value via `fix` ---------------------------------------------

private def value : GParser conditional Nat :=
  GParser.fix fun value =>
    let commaValue : GParser conditional Nat :=
      GParser.seqR ws (GParser.seqR (GParser.ch ',') (GParser.seqR ws value))
    let arrayBody : GParser flexible Nat :=
      GParser.alt
        (GParser.map2 (· + ·) value (GParser.foldMany (· + ·) 0 commaValue))
        (GParser.pure 0)
    let array : GParser conditional Nat :=
      GParser.seqR (GParser.ch '[')
        (GParser.seqR ws
          (GParser.seqL arrayBody (GParser.seqR ws (GParser.ch ']'))))
    let pair : GParser conditional Nat :=
      GParser.seqR jstring
        (GParser.seqR ws (GParser.seqR (GParser.ch ':') (GParser.seqR ws value)))
    let commaPair : GParser conditional Nat :=
      GParser.seqR ws (GParser.seqR (GParser.ch ',') (GParser.seqR ws pair))
    let objectBody : GParser flexible Nat :=
      GParser.alt
        (GParser.map2 (· + ·) pair (GParser.foldMany (· + ·) 0 commaPair))
        (GParser.pure 0)
    let object : GParser conditional Nat :=
      GParser.seqR (GParser.ch '{')
        (GParser.seqR ws
          (GParser.seqL objectBody (GParser.seqR ws (GParser.ch '}'))))
    -- Fallthrough for a byte that starts no value: always fails (the mapped `0` is unreachable).
    let invalid : GParser conditional Nat :=
      (fun _ => 0) <$> GParser.satisfy (fun _ => false)
    GParser.seqR ws
      (GParser.dispatch fun b =>
        if b == Ascii.lbrace then object
        else if b == Ascii.lbracket then array
        else if b == Ascii.quote then jstring
        else if b == 116 then keywordTrue
        else if b == 102 then keywordFalse
        else if b == 110 then keywordNull
        else if Ascii.isDigit b || b == Ascii.dash then number
        else invalid)

/-- Parse one complete JSON document: a value, then optional trailing whitespace,
then end of input. Full consumption is enforced here (neither `run?` nor `parse`
checks it), which is what rejects trailing garbage. -/
def json : Parser Nat :=
  GParser.weakenFallible (GParser.seqL value (GParser.seqR ws GParser.eof))

-- Acceptance guards -------------------------------------------------------

-- Valid: 4 array leaves + 1 string leaf ("x"); keys are not counted.
#guard (GParser.run? json "{\"a\":[1,-2.5e3,true,null],\"b\":\"x\"}".toUTF8) == some 5
#guard (GParser.run? json "{}".toUTF8) == some 0
#guard (GParser.run? json "[]".toUTF8) == some 0
#guard (GParser.run? json "  [ 1 , 2 , 3 ]  ".toUTF8) == some 3
-- Escaped quote inside a string: one leaf.
#guard (GParser.run? json "[\"a\\\"b\", 1]".toUTF8) == some 2
-- Strict rejections that the OLD loose parser accepted:
#guard (GParser.run? json "[truue]".toUTF8) == none         -- not an exact keyword
#guard (GParser.run? json "01".toUTF8) == none              -- leading zero
#guard (GParser.run? json "1.".toUTF8) == none              -- trailing dot, no frac digits
#guard (GParser.run? json "1e".toUTF8) == none              -- exponent, no digits
#guard (GParser.run? json "[1,]".toUTF8) == none            -- trailing comma
#guard (GParser.run? json "{\"a\":}".toUTF8) == none        -- missing value
#guard (GParser.run? json "1 2".toUTF8) == none             -- trailing garbage (EOF)
#guard (GParser.run? json "\"a\\q\"".toUTF8) == none        -- bad escape \q
#guard (GParser.run? json "\"a\\u00zz\"".toUTF8) == none    -- bad \u hex

end Grip.Examples.Json
