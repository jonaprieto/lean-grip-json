/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Mathlib
import GripJson
import GripProps.Json.Bytes
import GripProps.Json.Leaf

/-!
# `scanStr` walk denotation

`scanStr` scans a JSON string body byte-by-byte until the closing quote, validating `\`-escapes
via `escEnd` and accumulating whether any escape occurred. This file gives its step lemmas (one
normal byte, one escape, the closing quote) and, on top of them, the walk over a rendered body
`(escape s).toUTF8`, culminating in `scanStr` returning `s` — the string leaf of the JSON
round-trip.
-/

set_option maxHeartbeats 1000000

open Grip Grip.Json Grip.Json.Decode Grip.Json.Json

namespace GripProps.ScanStr

/-- The UTF-8 bytes a single character contributes to a rendered string body. -/
def cbytes (c : Char) : List UInt8 := (escapeChar c).flatMap String.utf8EncodeChar

/-- The UTF-8 bytes of a whole rendered string body (`escape`'s output). -/
def ebytes (cs : List Char) : List UInt8 := (cs.flatMap escapeChar).flatMap String.utf8EncodeChar

/-- `ebytes` peels one character off the front as `cbytes`. -/
theorem ebytes_cons (c : Char) (cs : List Char) : ebytes (c :: cs) = cbytes c ++ ebytes cs := by
  simp only [ebytes, cbytes, List.flatMap_cons, List.flatMap_append]

/-- Every `hexDigit` output is one of the sixteen hex characters. -/
theorem hexDigit_mem (n : Nat) : hexDigit n ∈ "0123456789abcdef".toList := by
  unfold hexDigit
  rcases Nat.lt_or_ge n "0123456789abcdef".toList.length with h | h
  · rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem _
  · rw [List.getD_eq_default _ _ h]; decide

/-- `Ascii.isHexDigit` accepts every `hexDigit` output: each is one of `0-9a-f`, all hex. -/
theorem isHexDigit_hexDigit (n : Nat) : Ascii.isHexDigit ((hexDigit n).val.toUInt8) = true := by
  have key : ∀ c ∈ "0123456789abcdef".toList, Ascii.isHexDigit (c.val.toUInt8) = true := by
    intro c hc; fin_cases hc <;> rfl
  exact key _ (hexDigit_mem n)

/-- Inverting `escapeChar c = [c]`: the character fell through every escape branch, so it is
`≥ 0x20` and neither `"` nor `\`. -/
theorem passthrough_props (c : Char) (h : escapeChar c = [c]) :
    32 ≤ c.toNat ∧ c.val ≠ 34 ∧ c.val ≠ 92 := by
  unfold escapeChar at h
  by_cases h34 : c = '"'
  · simp [h34] at h
  by_cases h92 : c = '\\'
  · simp [h92] at h
  by_cases hn : c = '\n'
  · simp [hn] at h
  by_cases ht : c = '\t'
  · simp [ht] at h
  by_cases hr : c = '\r'
  · simp [hr] at h
  by_cases hb8 : c = Char.ofNat 8
  · simp [hb8] at h
  by_cases hf12 : c = Char.ofNat 12
  · simp [hf12] at h
  by_cases hctrl : c.toNat < 0x20
  · simp [h34, h92, hn, ht, hr, hb8, hf12, hctrl] at h
  refine ⟨by omega, ?_, ?_⟩
  · intro he; exact h34 (Char.eq_of_val_eq (he.trans (by decide)))
  · intro he; exact h92 (Char.eq_of_val_eq (he.trans (by decide)))

/-- Decoding the UTF-8 bytes of a string recovers it: `fromUTF8!` inverts `toUTF8`. The body that
`scanStr` extracts at the closing quote is exactly `(escape s).toUTF8`, so this turns it back into
`escape s`. -/
theorem fromUTF8!_toUTF8 (s : String) : String.fromUTF8! s.toUTF8 = s := by
  have hv : s.toUTF8.IsValidUTF8 := by
    rw [show s.toUTF8 = s.toList.utf8Encode from by
      rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList]]
    exact ByteArray.isValidUTF8_utf8Encode
  unfold String.fromUTF8!
  rw [dif_pos hv]
  apply String.toByteArray_inj.mp
  exact ByteArray.ext rfl

/-- `String.fromUTF8?` on a genuine (valid) UTF-8 byte array agrees with the panicking
`String.fromUTF8!`: both take the same `dif_pos` branch. Bridges `scanStr`'s validated decode
(`fromUTF8?`) back to the `fromUTF8!`-phrased round-trip equations below, given the extracted
range is known valid (always true when it is `(escape s).toUTF8` for a real `s`). -/
theorem fromUTF8?_of_isValidUTF8 {b : ByteArray} (hv : b.IsValidUTF8) :
    String.fromUTF8? b = some (String.fromUTF8! b) := by
  unfold String.fromUTF8? String.fromUTF8!
  rw [dif_pos hv, dif_pos hv]

private theorem scanNormal_of_ge_128 (b : UInt8) (h : 128 ≤ b.toNat) :
    b ≠ 34 ∧ b ≠ 92 ∧ ¬ b < 32 := by
  refine ⟨?_, ?_, ?_⟩
  · intro hb
    have := congrArg UInt8.toNat hb
    rw [show (34 : UInt8).toNat = 34 from by decide] at this
    omega
  · intro hb
    have := congrArg UInt8.toNat hb
    rw [show (92 : UInt8).toNat = 92 from by decide] at this
    omega
  · rw [UInt8.lt_iff_toNat_lt, show (32 : UInt8).toNat = 32 from by decide]
    omega

private theorem scanNormal_of_high_prefix (b p : UInt8)
    (hp : p.toBitVec.msb = true) :
    (b ||| p) ≠ 34 ∧ (b ||| p) ≠ 92 ∧ ¬ (b ||| p) < 32 := by
  apply scanNormal_of_ge_128
  have hmsb : (b ||| p).toBitVec.msb = true := by
    simp [hp]
  have hge := BitVec.toNat_ge_of_msb_true hmsb
  simpa using hge

/-- Every UTF-8 byte of a passthrough character (`≥ 0x20`, not `"` or `\`) is scan-normal: it is
not the closing quote, not a backslash, and not a control byte. Single-byte chars carry their
codepoint (in `[0x20, 0x7F] \ {34, 92}`); every byte of a multi-byte char has its high bit set
(`≥ 0x80`), so all bounds hold. This lets `scanStr` walk a passthrough char's bytes one by one. -/
theorem passthrough_bytes_normal (c : Char) (h32 : 32 ≤ c.toNat) (hq : c.val ≠ 34)
    (hbs : c.val ≠ 92) (b : UInt8) (hb : b ∈ String.utf8EncodeChar c) :
    b ≠ 34 ∧ b ≠ 92 ∧ ¬ b < 32 := by
  have hpos := Char.utf8Size_pos c
  have hle4 := Char.utf8Size_le_four c
  rcases (show c.utf8Size = 1 ∨ c.utf8Size = 2 ∨ c.utf8Size = 3 ∨ c.utf8Size = 4 from by omega)
    with h | h | h | h
  · rw [String.utf8EncodeChar_eq_singleton h, List.mem_singleton] at hb
    subst hb
    have hle : c.val ≤ 0x7F := Char.utf8Size_eq_one_iff.mp h
    have hvn : c.val.toNat = c.toNat := Char.toNat_val
    have hbb : c.val.toUInt8.toNat = c.toNat := by
      rw [UInt32.toNat_toUInt8, hvn]
      have : c.toNat ≤ 127 := by rw [← hvn]; exact UInt32.le_iff_toNat_le.mp hle
      omega
    have h34 : c.toNat ≠ 34 := fun he => hq (UInt32.toNat_inj.mp (by rw [hvn, he]; decide))
    have h92 : c.toNat ≠ 92 := fun he => hbs (UInt32.toNat_inj.mp (by rw [hvn, he]; decide))
    refine ⟨?_, ?_, ?_⟩
    · intro he; rw [← UInt8.toNat_inj, hbb, show (34 : UInt8).toNat = 34 from by decide] at he
      exact h34 he
    · intro he; rw [← UInt8.toNat_inj, hbb, show (92 : UInt8).toNat = 92 from by decide] at he
      exact h92 he
    · rw [UInt8.lt_iff_toNat_lt, hbb, show (32 : UInt8).toNat = 32 from by decide]; omega
  · rw [String.utf8EncodeChar_eq_cons_cons h] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> exact scanNormal_of_high_prefix _ _ (by decide)
  · rw [String.utf8EncodeChar_eq_cons_cons_cons h] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> exact scanNormal_of_high_prefix _ _ (by decide)
  · rw [String.utf8EncodeChar_eq_cons_cons_cons_cons h] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> exact scanNormal_of_high_prefix _ _ (by decide)

/-- At the closing quote, `scanStr` finishes: it builds the body `arr[q0+1 .. q)` and unescapes
it exactly when an escape was seen -- given the body is valid UTF-8 (always true of a rendered
body; `scanStr` rejects the string otherwise, see `Grip.Json.scanStr`). -/
theorem scanStr_close (arr : ByteArray) (q0 q : Nat) (esc : Bool) (hq : q < arr.size)
    (h34 : arr[q]! = 34) (hv : (arr.extract (q0 + 1) q).IsValidUTF8) :
    scanStr arr q0 q esc =
      .ok (if esc then unescape (String.fromUTF8! (arr.extract (q0 + 1) q))
        else String.fromUTF8! (arr.extract (q0 + 1) q)) (q + 1) := by
  rw [getElem!_pos arr q hq] at h34
  rw [scanStr]
  simp only [dif_pos hq, h34, beq_self_eq_true, if_true, fromUTF8?_of_isValidUTF8 hv]

/-- On a normal body byte (not quote, not backslash, not a control byte), `scanStr` advances one
byte with the escape flag unchanged. -/
theorem scanStr_normal_step (arr : ByteArray) (q0 q : Nat) (esc : Bool) (hq : q < arr.size)
    (h34 : arr[q]! ≠ 34) (h92 : arr[q]! ≠ 92) (hlt : ¬ arr[q]! < 32) :
    scanStr arr q0 q esc = scanStr arr q0 (q + 1) esc := by
  rw [getElem!_pos arr q hq] at h34 h92 hlt
  rw [scanStr]
  rw [dif_pos hq, if_neg (by simpa [beq_iff_eq] using h34),
    if_neg (by simpa [beq_iff_eq] using h92), if_neg hlt]

/-- `scanStr` walks a run of `k` consecutive scan-normal bytes, advancing `k` with the escape flag
unchanged. Iterates `scanStr_normal_step`. -/
theorem scanStr_normal_run (arr : ByteArray) (q0 q : Nat) (esc : Bool) : ∀ (k : Nat),
    (∀ i, i < k → q + i < arr.size ∧ arr[q + i]! ≠ 34 ∧ arr[q + i]! ≠ 92 ∧ ¬ arr[q + i]! < 32) →
    scanStr arr q0 q esc = scanStr arr q0 (q + k) esc := by
  intro k
  induction k generalizing q with
  | zero => intro _; rw [Nat.add_zero]
  | succ n ih =>
    intro hall
    obtain ⟨hq, h34, h92, hlt⟩ := hall 0 (by omega)
    rw [Nat.add_zero] at hq h34 h92 hlt
    rw [scanStr_normal_step arr q0 q esc hq h34 h92 hlt]
    rw [ih (q + 1) (fun i hi => by
      have := hall (i + 1) (by omega)
      rwa [show q + (i + 1) = q + 1 + i from by omega] at this)]
    rw [show q + 1 + n = q + (n + 1) from by omega]

/-- On a backslash starting a valid escape (`escEnd = some q'`), `scanStr` skips to `q'` and marks
the escape flag. -/
theorem scanStr_esc_step (arr : ByteArray) (q0 q q' : Nat) (esc : Bool) (hq : q < arr.size)
    (h92 : arr[q]! = 92) (hE : escEnd arr q = some q') :
    scanStr arr q0 q esc = scanStr arr q0 q' true := by
  rw [getElem!_pos arr q hq] at h92
  have c34 : (arr[q] == 34) = false := by simp [h92]
  have c92 : (arr[q] == 92) = true := by simp [h92]
  rw [scanStr]
  simp only [dif_pos hq, c34, c92, Bool.false_eq_true, if_false, if_true]
  split
  · rename_i q'' heq
    rw [hE] at heq; injection heq with h; rw [h]
  · rename_i heq
    rw [hE] at heq; exact absurd heq (by simp)

/-- `escEnd` accepts a simple two-byte escape: a backslash whose successor is one of the named
escape bytes advances by two. -/
theorem escEnd_simple (arr : ByteArray) (q : Nat) (hq : q + 1 < arr.size)
    (hset : (arr[q + 1]! == 34 || arr[q + 1]! == 92 || arr[q + 1]! == 47 || arr[q + 1]! == 98 ||
      arr[q + 1]! == 102 || arr[q + 1]! == 110 || arr[q + 1]! == 114 ||
      arr[q + 1]! == 116) = true) :
    escEnd arr q = some (q + 2) := by
  rw [getElem!_pos arr (q + 1) hq] at hset
  rw [escEnd, dif_pos hq, if_pos hset]

/-- `escEnd` accepts a `\uXXXX` escape: `\`, `u`, then four hex bytes, advancing by six. -/
theorem escEnd_u (arr : ByteArray) (q : Nat) (hq1 : q + 1 < arr.size) (hq5 : q + 5 < arr.size)
    (hu : arr[q + 1]! = 117)
    (hhex : (Ascii.isHexDigit arr[q + 2]! && Ascii.isHexDigit arr[q + 3]! &&
      Ascii.isHexDigit arr[q + 4]! && Ascii.isHexDigit arr[q + 5]!) = true) :
    escEnd arr q = some (q + 6) := by
  rw [getElem!_pos arr (q + 1) hq1] at hu
  rw [getElem!_pos arr (q + 2) (by omega), getElem!_pos arr (q + 3) (by omega),
    getElem!_pos arr (q + 4) (by omega), getElem!_pos arr (q + 5) hq5] at hhex
  rw [escEnd, dif_pos hq1, if_neg (by rw [hu]; decide), if_pos (by rw [hu]; decide),
    dif_pos hq5, if_pos hhex]

/-- A passthrough character (`escapeChar c = [c]`) is walked by `scanStr` over exactly its
`utf8Size` bytes, escape flag unchanged. -/
theorem scanStr_char_passthrough (arr : ByteArray) (q0 q : Nat) (esc : Bool) (c : Char)
    (hpass : escapeChar c = [c])
    (hcontent : ∀ j, j < c.utf8Size → arr[q + j]! = (String.utf8EncodeChar c)[j]!)
    (hbound : q + c.utf8Size ≤ arr.size) :
    scanStr arr q0 q esc = scanStr arr q0 (q + c.utf8Size) esc := by
  obtain ⟨h32, hq34, hq92⟩ := passthrough_props c hpass
  apply scanStr_normal_run arr q0 q esc c.utf8Size
  intro i hi
  have hlen : (String.utf8EncodeChar c).length = c.utf8Size := String.length_utf8EncodeChar c
  have hmem : (String.utf8EncodeChar c)[i]! ∈ String.utf8EncodeChar c := by
    rw [getElem!_pos _ i (by rw [hlen]; exact hi)]; exact List.getElem_mem _
  obtain ⟨hn34, hn92, hnlt⟩ := passthrough_bytes_normal c h32 hq34 hq92 _ hmem
  rw [hcontent i hi]
  exact ⟨by omega, hn34, hn92, hnlt⟩

/-- Every `hexDigit` output is ASCII (`≤ 0x7F`). -/
theorem hexDigit_val_le (k : Nat) : (hexDigit k).val ≤ 0x7F := by
  have key : ∀ c ∈ "0123456789abcdef".toList, c.val ≤ 0x7F := by
    intro c hc; fin_cases hc <;> decide
  exact key _ (hexDigit_mem k)

/-- A `hexDigit` char is single-byte in UTF-8, carrying its codepoint. -/
theorem hexDigit_utf8 (k : Nat) :
    String.utf8EncodeChar (hexDigit k) = [(hexDigit k).val.toUInt8] :=
  String.utf8EncodeChar_eq_singleton (Char.utf8Size_eq_one_iff.mpr (hexDigit_val_le k))

/-- A two-byte escape (`\` then a named escape byte) is walked in two, marking `esc`. -/
theorem scanStr_char_escape2 (arr : ByteArray) (q0 q : Nat) (esc : Bool) (Xb : UInt8)
    (hq1 : q + 1 < arr.size) (h92 : arr[q]! = 92) (hX : arr[q + 1]! = Xb)
    (hset : (Xb == 34 || Xb == 92 || Xb == 47 || Xb == 98 || Xb == 102 || Xb == 110 ||
      Xb == 114 || Xb == 116) = true) :
    scanStr arr q0 q esc = scanStr arr q0 (q + 2) true :=
  scanStr_esc_step arr q0 q (q + 2) esc (by omega) h92
    (escEnd_simple arr q hq1 (by rw [hX]; exact hset))

/-- A `\uXXXX` escape (a control character's rendering) is walked in six, marking `esc`. -/
theorem scanStr_char_escapeU (arr : ByteArray) (q0 q : Nat) (esc : Bool) (hq5 : q + 5 < arr.size)
    (h92 : arr[q]! = 92) (hu : arr[q + 1]! = 117)
    (hhex : (Ascii.isHexDigit arr[q + 2]! && Ascii.isHexDigit arr[q + 3]! &&
      Ascii.isHexDigit arr[q + 4]! && Ascii.isHexDigit arr[q + 5]!) = true) :
    scanStr arr q0 q esc = scanStr arr q0 (q + 6) true :=
  scanStr_esc_step arr q0 q (q + 6) esc (by omega) h92 (escEnd_u arr q (by omega) hq5 hu hhex)

/-- A named two-byte escape, given its byte layout `[92, Xb]`, is walked in two. -/
theorem escape2_of (arr : ByteArray) (q0 q : Nat) (esc : Bool) (c : Char) (Xb : UInt8)
    (hcb : cbytes c = [92, Xb])
    (hset : (Xb == 34 || Xb == 92 || Xb == 47 || Xb == 98 || Xb == 102 || Xb == 110 ||
      Xb == 114 || Xb == 116) = true)
    (hcontent : ∀ j, j < (cbytes c).length → arr[q + j]! = (cbytes c)[j]!)
    (hbound : q + (cbytes c).length ≤ arr.size) :
    scanStr arr q0 q esc = scanStr arr q0 (q + (cbytes c).length) true := by
  have hlen : (cbytes c).length = 2 := by rw [hcb]; rfl
  rw [hlen]
  have h92 : arr[q]! = 92 := by
    have := hcontent 0 (by rw [hlen]; omega); rw [hcb] at this; simpa using this
  have hX : arr[q + 1]! = Xb := by
    have := hcontent 1 (by rw [hlen]; omega); rw [hcb] at this; simpa using this
  exact scanStr_char_escape2 arr q0 q esc Xb (by rw [hlen] at hbound; omega) h92 hX hset

/-- A `\uXXXX` escape, given its byte layout `[92, 117, 48, 48, b4, b5]` with `b4 b5` hex, is
walked in six. -/
theorem escapeU_of (arr : ByteArray) (q0 q : Nat) (esc : Bool) (c : Char) (b4 b5 : UInt8)
    (hcb : cbytes c = [92, 117, 48, 48, b4, b5]) (hb4 : Ascii.isHexDigit b4 = true)
    (hb5 : Ascii.isHexDigit b5 = true)
    (hcontent : ∀ j, j < (cbytes c).length → arr[q + j]! = (cbytes c)[j]!)
    (hbound : q + (cbytes c).length ≤ arr.size) :
    scanStr arr q0 q esc = scanStr arr q0 (q + (cbytes c).length) true := by
  have hlen : (cbytes c).length = 6 := by rw [hcb]; rfl
  rw [hlen]
  have g92 : arr[q]! = 92 := by
    have := hcontent 0 (by rw [hlen]; omega); rw [hcb] at this; simpa using this
  have gu : arr[q + 1]! = 117 := by
    have := hcontent 1 (by rw [hlen]; omega); rw [hcb] at this; simpa using this
  have g2 : arr[q + 2]! = 48 := by
    have := hcontent 2 (by rw [hlen]; omega); rw [hcb] at this; simpa using this
  have g3 : arr[q + 3]! = 48 := by
    have := hcontent 3 (by rw [hlen]; omega); rw [hcb] at this; simpa using this
  have g4 : arr[q + 4]! = b4 := by
    have := hcontent 4 (by rw [hlen]; omega); rw [hcb] at this; simpa using this
  have g5 : arr[q + 5]! = b5 := by
    have := hcontent 5 (by rw [hlen]; omega); rw [hcb] at this; simpa using this
  have hhex : (Ascii.isHexDigit arr[q + 2]! && Ascii.isHexDigit arr[q + 3]! &&
      Ascii.isHexDigit arr[q + 4]! && Ascii.isHexDigit arr[q + 5]!) = true := by
    rw [g2, g3, g4, g5, hb4, hb5]; decide
  exact scanStr_char_escapeU arr q0 q esc (by rw [hlen] at hbound; omega) g92 gu hhex

/-- Any escaped character (`escapeChar c ≠ [c]`) is walked by `scanStr` over exactly its `cbytes`,
marking the escape flag. Dispatches the seven named escapes to `escape2_of` and every other control
character to `escapeU_of`. -/
theorem scanStr_char_escape (arr : ByteArray) (q0 q : Nat) (esc : Bool) (c : Char)
    (hesc : escapeChar c ≠ [c])
    (hcontent : ∀ j, j < (cbytes c).length → arr[q + j]! = (cbytes c)[j]!)
    (hbound : q + (cbytes c).length ≤ arr.size) :
    scanStr arr q0 q esc = scanStr arr q0 (q + (cbytes c).length) true := by
  by_cases h : c = '"'
  · exact escape2_of arr q0 q esc c 34 (by rw [h]; decide) (by decide) hcontent hbound
  by_cases h2 : c = '\\'
  · exact escape2_of arr q0 q esc c 92 (by rw [h2]; decide) (by decide) hcontent hbound
  by_cases h3 : c = '\n'
  · exact escape2_of arr q0 q esc c 110 (by rw [h3]; decide) (by decide) hcontent hbound
  by_cases h4 : c = '\t'
  · exact escape2_of arr q0 q esc c 116 (by rw [h4]; decide) (by decide) hcontent hbound
  by_cases h5 : c = '\r'
  · exact escape2_of arr q0 q esc c 114 (by rw [h5]; decide) (by decide) hcontent hbound
  by_cases h6 : c = Char.ofNat 8
  · exact escape2_of arr q0 q esc c 98 (by rw [h6]; decide) (by decide) hcontent hbound
  by_cases h7 : c = Char.ofNat 12
  · exact escape2_of arr q0 q esc c 102 (by rw [h7]; decide) (by decide) hcontent hbound
  by_cases hctrl : c.toNat < 0x20
  · -- control character: `\u00XX`
    have hec : escapeChar c =
        ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)] := by
      unfold escapeChar
      simp only [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h2, beq_eq_false_iff_ne.mpr h3,
        beq_eq_false_iff_ne.mpr h4, beq_eq_false_iff_ne.mpr h5, beq_eq_false_iff_ne.mpr h6,
        beq_eq_false_iff_ne.mpr h7, Bool.false_eq_true, if_false, if_pos hctrl]
    have hcb : cbytes c = [92, 117, 48, 48, (hexDigit (c.toNat / 16)).val.toUInt8,
        (hexDigit (c.toNat % 16)).val.toUInt8] := by
      unfold cbytes; rw [hec]
      simp only [List.flatMap_cons, List.flatMap_nil, hexDigit_utf8,
        show String.utf8EncodeChar '\\' = [92] from by decide,
        show String.utf8EncodeChar 'u' = [117] from by decide,
        show String.utf8EncodeChar '0' = [48] from by decide, List.append_assoc,
        List.nil_append, List.cons_append]
    exact escapeU_of arr q0 q esc c _ _ hcb (isHexDigit_hexDigit _) (isHexDigit_hexDigit _)
      hcontent hbound
  · exact absurd (by unfold escapeChar; simp only [beq_eq_false_iff_ne.mpr h,
      beq_eq_false_iff_ne.mpr h2, beq_eq_false_iff_ne.mpr h3, beq_eq_false_iff_ne.mpr h4,
      beq_eq_false_iff_ne.mpr h5, beq_eq_false_iff_ne.mpr h6, beq_eq_false_iff_ne.mpr h7,
      Bool.false_eq_true, if_false, if_neg hctrl]) hesc

/-- `getElem!` on the left part of an append. -/
theorem getElem!_append_left (l1 l2 : List UInt8) (j : Nat) (h : j < l1.length) :
    (l1 ++ l2)[j]! = l1[j]! := by
  rw [getElem!_pos l1 j h, getElem!_pos (l1 ++ l2) j (by rw [List.length_append]; omega)]
  rw [List.getElem_append_left]

/-- `getElem!` on the right part of an append. -/
theorem getElem!_append_right (l1 l2 : List UInt8) (j : Nat) (h : l1.length ≤ j)
    (h2 : j < l1.length + l2.length) : (l1 ++ l2)[j]! = l2[j - l1.length]! := by
  rw [getElem!_pos (l1 ++ l2) j (by rw [List.length_append]; omega),
    getElem!_pos l2 (j - l1.length) (by omega)]
  rw [List.getElem_append_right h]

/-- **One character of a rendered body.** `scanStr` walks a single character's `cbytes`, advancing
by their length and setting the escape flag iff the character was escaped. Unifies the passthrough
and escape steps. -/
theorem scanStr_char_step (arr : ByteArray) (q0 q : Nat) (esc : Bool) (c : Char)
    (hcontent : ∀ j, j < (cbytes c).length → arr[q + j]! = (cbytes c)[j]!)
    (hbound : q + (cbytes c).length ≤ arr.size) :
    scanStr arr q0 q esc =
      scanStr arr q0 (q + (cbytes c).length) (esc || !(escapeChar c == [c])) := by
  by_cases hp : escapeChar c = [c]
  · have hbeq : (escapeChar c == [c]) = true := by rw [hp]; exact beq_self_eq_true _
    rw [hbeq]; simp only [Bool.not_true, Bool.or_false]
    have hcbc : cbytes c = String.utf8EncodeChar c := by
      simp only [cbytes, hp, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hn1 : (cbytes c).length = c.utf8Size := by rw [hcbc, String.length_utf8EncodeChar]
    rw [show (cbytes c).length = c.utf8Size from hn1]
    exact scanStr_char_passthrough arr q0 q esc c hp
      (fun j hj => by
        have hc := hcontent j (by rw [hn1]; exact hj); rw [hcbc] at hc; exact hc)
      (by rw [hn1] at hbound; exact hbound)
  · have hbeq : (escapeChar c == [c]) = false := by rw [beq_eq_false_iff_ne]; exact hp
    rw [hbeq]; simp only [Bool.not_false, Bool.or_true]
    exact scanStr_char_escape arr q0 q esc c hp hcontent hbound

/-- **The rendered-body walk.** Over a body whose bytes are `ebytes cs` (`escape`'s output for the
characters `cs`), followed by the closing quote, `scanStr` returns the decoded string: it decodes
the whole body and unescapes exactly when some character was escaped. Proved by induction on `cs`
via `scanStr_char_step`. -/
theorem scanStr_walk (arr : ByteArray) (q0 : Nat) (body : String) :
    ∀ (cs : List Char) (q : Nat) (esc : Bool),
      (∀ j, j < (ebytes cs).length → arr[q + j]! = (ebytes cs)[j]!) →
      arr[q + (ebytes cs).length]! = 34 →
      q + (ebytes cs).length < arr.size →
      body = String.fromUTF8! (arr.extract (q0 + 1) (q + (ebytes cs).length)) →
      (arr.extract (q0 + 1) (q + (ebytes cs).length)).IsValidUTF8 →
      scanStr arr q0 q esc =
        .ok (if (esc || cs.any (fun c => !(escapeChar c == [c]))) then unescape body else body)
          (q + (ebytes cs).length + 1) := by
  intro cs
  induction cs with
  | nil =>
    intro q esc hcontent hquote hqb hbody hvalid
    simp only [ebytes, List.flatMap_nil, List.length_nil, Nat.add_zero] at hquote hqb hbody hvalid ⊢
    rw [scanStr_close arr q0 q esc hqb hquote hvalid]
    simp only [List.any_nil, Bool.or_false]
    rw [hbody]
  | cons c rest ih =>
    intro q esc hcontent hquote hqb hbody hvalid
    rw [ebytes_cons, List.length_append] at hcontent hquote hqb hbody hvalid ⊢
    have hstep := scanStr_char_step arr q0 q esc c
      (fun j hj => by
        have hc := hcontent j (by omega)
        rwa [getElem!_append_left (cbytes c) (ebytes rest) j hj] at hc)
      (by omega)
    rw [hstep, ih (q + (cbytes c).length) (esc || !(escapeChar c == [c]))
      (fun j hj => by
        have hc := hcontent ((cbytes c).length + j) (by omega)
        rw [getElem!_append_right (cbytes c) (ebytes rest) ((cbytes c).length + j)
          (by omega) (by omega), Nat.add_sub_cancel_left,
          show q + ((cbytes c).length + j) = q + (cbytes c).length + j from by omega] at hc
        exact hc)
      (by rw [show q + (cbytes c).length + (ebytes rest).length
          = q + ((cbytes c).length + (ebytes rest).length) from by omega]; exact hquote)
      (by rw [show q + (cbytes c).length + (ebytes rest).length
          = q + ((cbytes c).length + (ebytes rest).length) from by omega]; exact hqb)
      (by rw [show q + (cbytes c).length + (ebytes rest).length
          = q + ((cbytes c).length + (ebytes rest).length) from by omega]; exact hbody)
      (by rw [show q + (cbytes c).length + (ebytes rest).length
          = q + ((cbytes c).length + (ebytes rest).length) from by omega]; exact hvalid)]
    congr 1
    · simp only [List.any_cons]; rw [Bool.or_assoc]; rfl
    · omega

/-- The data-list of `(escape s).toUTF8` equals `ebytes s.toList`. -/
theorem escape_toUTF8_data_toList (s : String) :
    (escape s).toUTF8.data.toList = ebytes s.toList := by
  rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList,
      GripProps.Bytes.utf8Encode_data_toList]
  simp only [escape, String.toList_ofList, ebytes]

/-- `(escape s).toUTF8.size = (ebytes s.toList).length`. -/
theorem escape_toUTF8_size (s : String) :
    (escape s).toUTF8.size = (ebytes s.toList).length := by
  rw [← ByteArray.size_data, ← Array.length_toList, escape_toUTF8_data_toList]

/-- `getElem!` on `(escape s).toUTF8` at `i` equals `(ebytes s.toList)[i]!`. -/
theorem escape_toUTF8_getElem! (s : String) (i : Nat)
    (hi : i < (ebytes s.toList).length) :
    (escape s).toUTF8[i]! = (ebytes s.toList)[i]! := by
  rw [GripProps.Bytes.getElem!_eq_toList, escape_toUTF8_data_toList]

/-- Two ByteArrays are equal when their sizes and `getElem!` values agree element-wise. -/
private theorem bytearray_eq_of_getElem! {a b : ByteArray} (hsize : a.size = b.size)
    (h : ∀ i, i < a.size → a[i]! = b[i]!) : a = b := by
  apply ByteArray.ext_getElem hsize
  intro i hi hi'
  rw [← getElem!_pos a i hi, ← getElem!_pos b i hi']
  exact h i hi

/-- `getElem!` on `arr.extract s e` at `i` (in range) equals `arr[s + i]!`. -/
theorem getElem!_extract (arr : ByteArray) (s e i : Nat)
    (he : e ≤ arr.size) (hi : i < e - s) :
    (arr.extract s e)[i]! = arr[s + i]! := by
  have hext : i < (arr.extract s e).size := by
    simp [ByteArray.size_extract, Nat.min_eq_left he]; omega
  have h2 : s + i < arr.size := by omega
  have step : (arr.extract s e)[i]'hext = arr[s + i]'h2 := by
    rw [ByteArray.getElem_extract hext]
  rw [getElem!_pos _ i hext, getElem!_pos arr (s + i) h2, step]

/-- When `arr[q+1+j]! = (ebytes s.toList)[j]!` for all `j` in range, the extract
`arr[q+1..q+1+k)` equals `(escape s).toUTF8`. Used to show `scanStr` extracts the right
body string. -/
theorem extract_eq_escape_toUTF8 (arr : ByteArray) (q : Nat) (s : String)
    (hbound : q + 1 + (ebytes s.toList).length < arr.size)
    (hcontent : ∀ j, j < (ebytes s.toList).length →
        arr[q + 1 + j]! = (ebytes s.toList)[j]!) :
    arr.extract (q + 1) (q + 1 + (ebytes s.toList).length) = (escape s).toUTF8 := by
  set k := (ebytes s.toList).length
  apply bytearray_eq_of_getElem!
  · rw [ByteArray.size_extract,
        Nat.min_eq_left (show q + 1 + k ≤ arr.size by omega),
        escape_toUTF8_size]
    omega
  · intro i hi
    rw [ByteArray.size_extract,
        Nat.min_eq_left (show q + 1 + k ≤ arr.size by omega)] at hi
    rw [getElem!_extract arr (q + 1) (q + 1 + k) i (by omega) (by omega)]
    rw [hcontent i (by omega)]
    exact (escape_toUTF8_getElem! s i (by omega)).symm

end GripProps.ScanStr
