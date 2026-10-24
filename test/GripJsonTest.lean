/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Grip
import GripJson

/-! Compile-time checks for grip-json. `#guard` runs at elaboration, so a false guard fails the
build of this library. -/

/-! ### Values: what each document parses to, and what `render` prints. -/
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
   (parseString (toString v)).toOption == some v)

end

/-! ### `Grip.Json` reports where the failure actually is, and what it wanted.

A failure inside `{..}`/`[..]` used to be reported at the opening bracket (backtracking into
the empty-container branch discarded it) or at the separator (`foldMany` cannot propagate a
late element's failure), and every message read "unexpected input". -/
section
open Grip Grip.Json

private
def errPos
    (s : String)
    : Option (Nat × Nat)
    :=
  match parseString s with
  | .ok _    => none
  | .error e => some (e.line, e.col)

private
def errMsg
    (s : String)
    : Option String
    :=
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
#guard (parseString "[]").toOption == some (Json.arr #[])
#guard (parseString "[  ]").toOption == some (Json.arr #[])
#guard (parseString "{}").toOption == some (Json.obj #[])
#guard (parseString "{\n}").toOption == some (Json.obj #[])

end
