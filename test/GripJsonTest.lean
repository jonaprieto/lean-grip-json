/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Grip
import GripJson

/-! Milestone 0 smoke test. `#guard` runs at elaboration, so a false guard is a build
error and turns the `core` CI job red. Real parser tests arrive in Milestone 1. -/

#guard (1 + 1 = 2)

/-! ### Sanity: the graded byte backend parses. -/
section
open Grip

private def digits : GParser conditional Nat :=
  GParser.takeWhile1 (fun b => 48 ≤ b && b ≤ 57)

private def sample :=
  GParser.seqR (GParser.byte 40) (GParser.seqL digits (GParser.byte 41))  -- "(" digits ")"

#guard (GParser.run? digits "123".toUTF8) == some 3        -- 3 digit bytes consumed
#guard (GParser.run? sample "(42)".toUTF8) == some 2       -- 2 digit bytes inside parens
#guard (GParser.run? sample "(42".toUTF8) == none          -- missing ')'
#guard (GParser.run? (GParser.foldMany (· + ·) 0 digits) "".toUTF8) == some 0

/-! ### Incremental migration: recover one precise primitive without grading the caller. -/

private def migratedDigits : GParser conditional Nat :=
  GParser.takeWhile1 Ascii.isDigit

private def migratedGroups : Parser (List Nat) :=
  GParser.many migratedDigits

#guard (GParser.run? migratedGroups "12".toUTF8) == some [2]

-- fix: a recursive nested-parens parser returning the nesting depth. Each level
-- consumes "(" before recursing, so the always-consume clamp never fires on
-- balanced input; unbalanced input fails.
private def parenDepth : GParser conditional Nat :=
  GParser.fix fun self =>
    GParser.map (· + 1)
      (GParser.seqR (GParser.byte 40)
        (GParser.seqL (GParser.alt self (GParser.pure 0)) (GParser.byte 41)))

#guard (GParser.run? parenDepth "()".toUTF8) == some 1
#guard (GParser.run? parenDepth "((()))".toUTF8) == some 3
#guard (GParser.run? parenDepth "(()".toUTF8) == none            -- unbalanced

-- Direct left recursion type-checks, but the input-bounded fuel makes it terminate as a
-- failure instead of looping. Guarded bodies such as `parenDepth` above have the stronger
-- completeness theorem; the `conditional → conditional` transformer type alone is insufficient.
private def directLeft : GParser conditional Unit :=
  GParser.fix fun self => self

#guard (match directLeft.run "x".toUTF8 0 with
  | .error e => e.pos == 0
  | .ok _ _ => false)

-- BEq for ParseResult, needed by the #guard comparisons below.
private instance instBEqParseResult {β : Type} [BEq β] : BEq (ParseResult β) where
  beq
    | .error e1, .error e2 => e1 == e2
    | .ok a p,   .ok b q   => a == b && p == q
    | _,         _         => false

-- Error payload: bare failure records pos; label sets expected.
#guard (digits.run "abc".toUTF8 0 == (.error ⟨0, []⟩ : ParseResult Nat))
#guard ((digits <?> "digit").run "abc".toUTF8 0
        == (.error ⟨0, ["digit"]⟩ : ParseResult Nat))
-- Tie-merge: both branches fail at pos 0; expected sets are unioned.
private def byteA : GParser conditional Unit := GParser.byte 65
private def byteB : GParser conditional Unit := GParser.byte 66
#guard ((GParser.alt (byteA <?> "A") (byteB <?> "B")).run "c".toUTF8 0
        == (.error ⟨0, ["A", "B"]⟩ : ParseResult Unit))

end

/-! ### `Grip.Json` reports where the failure actually is, and what it wanted.

A failure inside `{..}`/`[..]` used to be reported at the opening bracket (backtracking into
the empty-container branch discarded it) or at the separator (`foldMany` cannot propagate a
late element's failure), and every message read "unexpected input". -/
section
open Grip Grip.Json

private def errPos (s : String) : Option (Nat × Nat) :=
  match parseString s with
  | .ok _    => none
  | .error e => some (e.line, e.col)

private def errMsg (s : String) : Option String :=
  match parseString s with
  | .ok _    => none
  | .error e => some e.message

-- The position is the real problem, not the opening bracket and not the separator.
#guard errPos "{\"a\": \"b\\qc\"}" == some (1, 9)   -- bad escape in the first value
#guard errPos "[1, \"b\\qc\"]"     == some (1, 7)   -- bad escape in a later element
#guard errPos "{\"a\" 1}"          == some (1, 6)   -- missing ':'
#guard errPos "{\"a\": }"          == some (1, 7)   -- missing value
#guard errPos "[01]"              == some (1, 3)   -- leading zero
#guard errPos "[1,]"              == some (1, 4)   -- trailing comma
#guard errPos "[1 2]"             == some (1, 4)   -- missing ','
#guard errPos "{\"a\":1,,\"b\":2}"  == some (1, 8)   -- doubled ','
#guard errPos "[1,2"              == some (1, 5)   -- unterminated
#guard errPos "{\"a\":{\"b\":[1,2,tru]}}" == some (1, 16)      -- deep inside nested containers
#guard errPos "[[[1,2],[3,\"x\\uZZ\"]]]"  == some (1, 14)
-- Multi-line input: the line advances with the real failure, not with the opening brace.
#guard errPos "{\n  \"a\": 1,\n  \"b\": tru\n}" == some (3, 8)

-- Messages name what the grammar was looking for.
#guard errMsg "{\"a\" 1}" == some "expected ':'"
#guard errMsg "[1 2]"    == some "expected ',' or ']'"
#guard errMsg "{\"a\":1,,\"b\":2}" == some "expected a string"
#guard errMsg "{\"a\": }" == some "expected a JSON value"
#guard errMsg "nul"      == some "expected null"
#guard errMsg "[1,2"     == some "expected ',' or ']'"

-- Trailing garbage is reported at the first byte past the value, naming what was wanted.
#guard errMsg "1 2"        == some "expected end of input"
#guard errPos "1 2"        == some (1, 3)
#guard errPos "null null"  == some (1, 6)
#guard errPos "[1] x"      == some (1, 5)
#guard errPos "12abc"      == some (1, 3)
-- A bare exponent parses as `1` followed by garbage, so it lands here rather than in `number`.
#guard errMsg "1e"         == some "expected end of input"

-- Empty containers, whitespace and all, are still accepted.
#guard parseString "[]"    == .ok (Json.arr #[])
#guard parseString "[  ]"  == .ok (Json.arr #[])
#guard parseString "{}"    == .ok (Json.obj #[])
#guard parseString "{\n}"  == .ok (Json.obj #[])

end
