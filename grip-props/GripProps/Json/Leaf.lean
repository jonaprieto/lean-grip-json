/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Mathlib
import GripJson

/-!
# Leaf inverse: `unescape (escape s) = s`

The string-escaping round-trip: JSON-escaping a string (`escape`) and decoding the escapes
(`unescape`) returns the original string. This is the leaf the round-trip proof rests on for
string values, and the part Dafny's high-level JSON API leaves unverified ("the most complex part
is the string escaping code").

The proof stays at the `List Char` level: `escape s = String.ofList (s.toList.flatMap escapeChar)`
and `unescape` folds `uStep` over `.toList`, so `String.toList_ofList` turns the whole thing into a
`List.foldl` characterised one escaped character at a time (`foldl_escapeChar`).
-/

set_option maxHeartbeats 1000000

open Grip.Json.Decode Grip.Json.Json

namespace GripProps.Leaf

/-- `foldl` over a `flatMap`: fold `f`, for each element, over that element's expansion. -/
theorem foldl_flatMap {α β γ : Type} (f : β → α → β) (init : β) (l : List γ)
    (g : γ → List α) :
    (l.flatMap g).foldl f init = l.foldl (fun a x => (g x).foldl f a) init := by
  induction l generalizing init with
  | nil => simp
  | cons h t ih => simp [List.flatMap_cons, List.foldl_append, ih]

/-- `hexValue` inverts `hexDigit` on a single hex-digit value. -/
theorem hexValue_hexDigit (k : Nat) (hk : k < 16) :
    Grip.Ascii.hexValue (UInt8.ofNat (hexDigit k).toNat) = k := by
  interval_cases k <;> decide

/-- Folding `uStep` over the escape of one character, from a clean state, appends exactly that
character to the output and leaves the state clean. The `\u00XX` arm resets `uAcc`, so a clean
`uAcc` (`ha`) is part of the precondition threaded through the fold. -/
theorem foldl_escapeChar (st : UState) (c : Char)
    (he : st.esc = false) (hu : st.uLeft = 0) (hh : st.hi = 0) (ha : st.uAcc = 0) :
    List.foldl uStep st (escapeChar c) = { st with out := st.out.push c } := by
  unfold escapeChar
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;>
    simp_all [uStep, List.foldl_cons, List.foldl_nil]
  -- sole remaining goal: the `\u00XX` control-character arm
  rw [hexValue_hexDigit (c.toNat / 16) (by omega), hexValue_hexDigit (c.toNat % 16) (by omega)]
  have h48 : Grip.Ascii.hexValue 48 = 0 := by decide
  have harg :
      ((Grip.Ascii.hexValue 48 * 16 + Grip.Ascii.hexValue 48) * 16 + c.toNat / 16) * 16
          + c.toNat % 16 = c.toNat := by
    rw [h48]; omega
  rw [harg, if_neg (by omega : ¬ (55296 ≤ c.toNat ∧ c.toNat ≤ 56319)), Char.ofNat_toNat]

/-- The core invariant: folding the per-character escape-decode over `cs`, from a clean state,
appends exactly `cs` to the output (tracked through `String.toList`). -/
theorem out_toList_foldl (cs : List Char) (st : UState)
    (he : st.esc = false) (hu : st.uLeft = 0) (hh : st.hi = 0) (ha : st.uAcc = 0) :
    (cs.foldl (fun st c => (escapeChar c).foldl uStep st) st).out.toList = st.out.toList ++ cs := by
  induction cs generalizing st with
  | nil => simp
  | cons c cs ih =>
    have hk := foldl_escapeChar st c he hu hh ha
    simp only [List.foldl_cons, hk]
    rw [ih _ (by simp [he]) (by simp [hu]) (by simp [hh]) (by simp [ha])]
    simp [String.toList_push]

/-- **String-escaping round-trip.** Escaping a string and decoding the escapes is the identity.
This is the leaf Dafny's high-level JSON API leaves unverified. -/
theorem unescape_escape (s : String) : unescape (escape s) = s := by
  unfold unescape escape
  rw [String.toList_ofList, foldl_flatMap]
  apply String.toList_inj.mp
  rw [out_toList_foldl _ _ rfl rfl rfl rfl]
  simp

end GripProps.Leaf
