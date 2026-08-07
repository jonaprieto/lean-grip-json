/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Mathlib

/-!
# ByteArray fold bridge

Lean 4.28's `ByteArray.foldl` is a bespoke monadic index loop with no library
characterization. This file bridges a full-range `ByteArray.foldl` to a `List.foldl` over the
underlying byte list (`arr.data.toList`), routing through the `Array` (`.data`) lemma set. It is
the foundation the `ByteArray`-level JSON round-trip lemmas rest on.
-/

set_option maxHeartbeats 1000000

namespace GripProps.Bytes

/-- The internal `foldlM` loop, in `Id`, computes the `List.foldl` over the remaining bytes. -/
theorem foldlM_loop_eq {β : Type} (f : β → UInt8 → β) (arr : ByteArray)
    (h : arr.size ≤ arr.size) :
    ∀ (i j : Nat) (b : β), j + i = arr.size →
      ByteArray.foldlM.loop (m := Id) (fun x y => pure (f x y)) arr arr.size h i j b
        = (arr.data.toList.drop j).foldl f b := by
  intro i
  induction i with
  | zero =>
    intro j b hj
    have hlen : arr.data.toList.length ≤ j := by
      rw [Array.length_toList, ByteArray.size_data]; omega
    unfold ByteArray.foldlM.loop
    have hnlt : ¬ j < arr.size := by omega
    rw [dif_neg hnlt, List.drop_eq_nil_of_le hlen]
    rfl
  | succ n ih =>
    intro j b hj
    have hjt : j < arr.data.toList.length := by
      rw [Array.length_toList, ByteArray.size_data]; omega
    unfold ByteArray.foldlM.loop
    have hlt : j < arr.size := by omega
    have hget : arr[j] = arr.data.toList[j]'hjt := by
      rw [ByteArray.getElem_eq_getElem_data, Array.getElem_toList]
      rfl
    rw [dif_pos hlt]
    show ByteArray.foldlM.loop (m := Id) (fun x y => pure (f x y)) arr arr.size h n (j + 1)
        (f b arr[j]) = _
    rw [hget, List.drop_eq_getElem_cons hjt, List.foldl_cons]
    exact ih (j + 1) _ (by omega)

/-- A full-range `ByteArray.foldl` is the `List.foldl` over its byte list. -/
theorem foldl_eq_data_toList {β : Type} (f : β → UInt8 → β) (b : β) (arr : ByteArray) :
    arr.foldl f b 0 arr.size = arr.data.toList.foldl f b := by
  show (ByteArray.foldlM (m := Id) (fun x y => pure (f x y)) b arr 0 arr.size).run
      = arr.data.toList.foldl f b
  unfold ByteArray.foldlM
  simp only [Nat.le_refl, ↓reduceDIte, Nat.sub_zero]
  exact foldlM_loop_eq f arr (Nat.le_refl _) arr.size 0 b (by omega)

/-- The internal loop over a bounded range computes the `List.foldl` over that slice of bytes. -/
theorem foldlM_loop_range {β : Type} (f : β → UInt8 → β) (arr : ByteArray) (stop : Nat)
    (h : stop ≤ arr.size) :
    ∀ (i j : Nat) (b : β), j + i = stop →
      ByteArray.foldlM.loop (m := Id) (fun x y => pure (f x y)) arr stop h i j b
        = ((arr.data.toList.drop j).take i).foldl f b := by
  intro i
  induction i with
  | zero =>
    intro j b hj; unfold ByteArray.foldlM.loop
    simp only [List.take_zero, List.foldl_nil]; split <;> rfl
  | succ n ih =>
    intro j b hj
    have hjt : j < arr.data.toList.length := by
      rw [Array.length_toList, ByteArray.size_data]; omega
    have hget : arr[j] = arr.data.toList[j]'hjt := by
      rw [ByteArray.getElem_eq_getElem_data, Array.getElem_toList]
    unfold ByteArray.foldlM.loop
    rw [dif_pos (show j < stop by omega)]
    show ByteArray.foldlM.loop (m := Id) (fun x y => pure (f x y)) arr stop h n (j + 1)
        (f b arr[j]) = _
    rw [hget, List.drop_eq_getElem_cons hjt, List.take_succ_cons, List.foldl_cons]
    exact ih (j + 1) _ (by omega)

/-- A bounded-range `ByteArray.foldl` is the `List.foldl` over that byte slice. -/
theorem foldl_range_data {β : Type} (f : β → UInt8 → β) (b : β) (arr : ByteArray) (q q' : Nat)
    (hq' : q' ≤ arr.size) (hqq : q ≤ q') :
    arr.foldl f b q q' = ((arr.data.toList.drop q).take (q' - q)).foldl f b := by
  show (ByteArray.foldlM (m := Id) (fun x y => pure (f x y)) b arr q q').run
      = ((arr.data.toList.drop q).take (q' - q)).foldl f b
  unfold ByteArray.foldlM
  simp only [dif_pos hq']
  exact foldlM_loop_range f arr q' hq' (q' - q) q b (by omega)

/-- `arr[j]!` equals the `j`-th element of `arr.data.toList` (with `!`). -/
theorem getElem!_eq_toList (arr : ByteArray) (j : Nat) : arr[j]! = arr.data.toList[j]! := by
  rcases Nat.lt_or_ge j arr.size with h | h
  · have hj : j < arr.data.toList.length := by rw [Array.length_toList, ByteArray.size_data]; omega
    rw [getElem!_pos arr j h, ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList,
      getElem!_pos _ j hj]
    rfl
  · have hj : ¬ j < arr.data.toList.length := by
      rw [Array.length_toList, ByteArray.size_data]; omega
    rw [getElem!_neg arr j (by omega), getElem!_neg _ j hj]

/-- Two byte ranges with matching bytes fold to the same value. -/
theorem foldl_congr_match {β : Type} (f : β → UInt8 → β) (b : β) (arr1 arr2 : ByteArray)
    (q1 q2 n : Nat) (h1 : q1 + n ≤ arr1.size) (h2 : q2 + n ≤ arr2.size)
    (hm : ∀ i, i < n → arr1[q1 + i]! = arr2[q2 + i]!) :
    arr1.foldl f b q1 (q1 + n) = arr2.foldl f b q2 (q2 + n) := by
  rw [foldl_range_data f b arr1 q1 (q1 + n) (by omega) (by omega),
    foldl_range_data f b arr2 q2 (q2 + n) (by omega) (by omega)]
  congr 1
  apply List.ext_getElem
  · rw [List.length_take, List.length_take, List.length_drop, List.length_drop,
      Array.length_toList, Array.length_toList, ByteArray.size_data, ByteArray.size_data]
    omega
  · intro i hi1 hi2
    rw [List.length_take, List.length_drop, Array.length_toList, ByteArray.size_data] at hi1
    -- Go through `getElem!` rather than `ByteArray.getElem_eq_getElem_data` backwards: rewriting
    -- a list index into `arr[..]` would hand the `ByteArray` `getElem` a `.data.toList.length`
    -- bound where it wants a `.size` one, which no longer typechecks at `instances` transparency.
    have hb1 : q1 + i < arr1.data.toList.length := by
      rw [Array.length_toList, ByteArray.size_data]; omega
    have hb2 : q2 + i < arr2.data.toList.length := by
      rw [Array.length_toList, ByteArray.size_data]; omega
    rw [List.getElem_take, List.getElem_take, List.getElem_drop, List.getElem_drop,
      ← getElem!_pos _ (q1 + i) hb1, ← getElem!_pos _ (q2 + i) hb2,
      ← getElem!_eq_toList, ← getElem!_eq_toList]
    exact hm i (by omega)

/-- The byte list of a `List Char`'s UTF-8 encoding is the per-character encodings concatenated. -/
theorem utf8Encode_data_toList (cs : List Char) :
    (List.utf8Encode cs).data.toList = cs.flatMap String.utf8EncodeChar := by
  induction cs with
  | nil => simp [List.utf8Encode_nil]
  | cons c cs ih =>
    rw [List.utf8Encode_cons, ByteArray.toList_data_append, ih, List.flatMap_cons]
    congr 1
    simp [List.utf8Encode]

/-- String append commutes with UTF-8 encoding. -/
theorem toUTF8_append (s t : String) :
    (s ++ t).toUTF8 = s.toUTF8 ++ t.toUTF8 := by
  simp [String.toUTF8_eq_toByteArray, String.toByteArray_append]

/-- In-bounds index into an appended array reads from the left part. -/
theorem ba_get!_append_left {i : Nat} {a b : ByteArray} (h : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  rw [getElem!_pos (a ++ b) i (by rw [ByteArray.size_append]; omega),
      ByteArray.getElem_append_left h,
      getElem!_pos a i h]

/-- Out-of-left-range index into an appended array reads from the right part. -/
theorem ba_get!_append_right {i : Nat} {a b : ByteArray} (h : a.size ≤ i)
    (hi : i < (a ++ b).size) :
    (a ++ b)[i]! = b[i - a.size]! := by
  rw [getElem!_pos (a ++ b) i hi,
      ByteArray.getElem_append_right h,
      getElem!_pos b (i - a.size) (by rw [ByteArray.size_append] at hi; omega)]

/-- An ASCII character encodes to a single byte, its code point. -/
theorem ascii_encode (c : Char) (h : c.toNat ≤ 127) :
    String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  have hval : c.val ≤ 127 := by rw [UInt32.le_iff_toNat_le]; exact h
  have hbyte : c.val.toUInt8 = UInt8.ofNat c.toNat := by
    rw [Char.toNat]; exact UInt8.toNat_inj.mp rfl
  rw [String.utf8EncodeChar_eq_singleton (Char.utf8Size_eq_one_iff.mpr hval), hbyte]

/-- Over ASCII characters, `flatMap`-encoding is `map`ping each to its byte. -/
theorem flatMap_ascii (cs : List Char) (h : ∀ c ∈ cs, c.toNat ≤ 127) :
    cs.flatMap String.utf8EncodeChar = cs.map (fun c => UInt8.ofNat c.toNat) := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.flatMap_cons, List.map_cons, ascii_encode c (h c (by simp)),
      ih (fun c hc => h c (by simp [hc]))]
    simp

/-- The byte list of an ASCII `String.ofList`'s UTF-8 encoding is the characters' byte values. -/
theorem ofList_ascii_toUTF8_data_eq (cs : List Char)
    (h : ∀ c ∈ cs, c.toNat ≤ 127) :
    (String.ofList cs).toUTF8.data.toList = cs.map (fun c => UInt8.ofNat c.toNat) := by
  rw [show (String.ofList cs).toUTF8 = cs.utf8Encode from by
    rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList, String.toList_ofList]]
  rw [utf8Encode_data_toList]
  apply flatMap_ascii
  exact h

/-- An ASCII `String.ofList`'s UTF-8 size is the character count. -/
theorem ofList_ascii_toUTF8_size (cs : List Char) (h : ∀ c ∈ cs, c.toNat ≤ 127) :
    (String.ofList cs).toUTF8.size = cs.length := by
  rw [← ByteArray.size_data, ← Array.length_toList, ofList_ascii_toUTF8_data_eq cs h,
      List.length_map]

/-- The `i`-th byte of an ASCII `String.ofList`'s UTF-8 encoding is the `i`-th character's
byte value. -/
theorem ofList_ascii_toUTF8_getElem! (cs : List Char) (i : Nat)
    (h : ∀ c ∈ cs, c.toNat ≤ 127) (hi : i < cs.length) :
    (String.ofList cs).toUTF8[i]! = UInt8.ofNat cs[i]!.toNat := by
  rw [getElem!_eq_toList, ofList_ascii_toUTF8_data_eq cs h,
      getElem!_pos _ i (by rw [List.length_map]; exact hi),
      getElem!_pos _ i hi, List.getElem_map]

/-- **String-bytes fold bridge.** Folding over a string's UTF-8 bytes is folding over the byte
list obtained by encoding each character. This turns any `ByteArray.foldl` over `s.toUTF8` (as in
`decodeNumberBytes?` and the parser) into a `List.foldl` over `s.toList`'s encoded bytes. -/
theorem toUTF8_foldl {β : Type} (f : β → UInt8 → β) (b : β) (s : String) :
    s.toUTF8.foldl f b 0 s.toUTF8.size
      = (s.toList.flatMap String.utf8EncodeChar).foldl f b := by
  rw [foldl_eq_data_toList,
    show s.toUTF8 = s.toList.utf8Encode from by
      rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList],
    utf8Encode_data_toList]

end GripProps.Bytes
