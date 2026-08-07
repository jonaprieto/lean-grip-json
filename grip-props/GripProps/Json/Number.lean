/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Mathlib
import GripJson
import GripProps.Json.Bytes
import GripProps.Json.NatDigits

/-!
# JSON number round-trip (integers)

`decodeNumberBytes?` over `(renderNum m 0).toUTF8` recovers `num m 0`. Glues the ByteArray/toUTF8
fold bridge and the decimal-digit fold inversion through `numByte`'s state machine on the
digit bytes rendered for an integer.
-/

set_option maxHeartbeats 1000000

open Grip.Json Grip.Json.Decode Grip.Json.Json
open GripProps.Bytes

namespace GripProps.Number

/-- Single `numByte` step on a decimal digit, phase 0 or 1: accumulate the mantissa (and, in
phase 1, count a fractional digit); other fields unchanged. -/
theorem numByte_digit (st : NState) (c : Char) (hc1 : 48 ≤ c.toNat) (hc2 : c.toNat ≤ 57) :
    numByte st (UInt8.ofNat c.toNat) =
      (if st.phase = 1 then
        { st with mant := st.mant * 10 + (c.toNat - 48), fracLen := st.fracLen + 1 }
       else if st.phase = 0 then { st with mant := st.mant * 10 + (c.toNat - 48) }
       else { st with expVal := st.expVal * 10 + (c.toNat - 48) }) := by
  have hsize : UInt8.size = 256 := by decide
  have hb : (UInt8.ofNat c.toNat).toNat = c.toNat := UInt8.toNat_ofNat_of_lt' (by omega)
  have h48 : ((48 : UInt8)).toNat = 48 := by decide
  have key : ∀ k : Nat, k < 256 → k ≠ c.toNat →
      (UInt8.ofNat c.toNat == UInt8.ofNat k) = false := by
    intro k hk256 hk
    rw [beq_eq_false_iff_ne, ne_eq]; intro h
    have hkb : (UInt8.ofNat k).toNat = k := UInt8.toNat_ofNat_of_lt' (by omega)
    have := congrArg UInt8.toNat h; rw [hb, hkb] at this; exact hk this.symm
  have hle : (48 : UInt8) ≤ UInt8.ofNat c.toNat := by
    rw [UInt8.le_iff_toNat_le, hb, h48]; omega
  have hd48 : (UInt8.ofNat c.toNat - 48).toNat = c.toNat - 48 := by
    rw [UInt8.toNat_sub_of_le _ _ hle, hb, h48]
  simp only [numByte, show (46 : UInt8) = UInt8.ofNat 46 from rfl,
    show (101 : UInt8) = UInt8.ofNat 101 from rfl, show (69 : UInt8) = UInt8.ofNat 69 from rfl,
    show (43 : UInt8) = UInt8.ofNat 43 from rfl, show (45 : UInt8) = UInt8.ofNat 45 from rfl,
    key 46 (by omega) (by omega), key 101 (by omega) (by omega), key 69 (by omega) (by omega),
    key 43 (by omega) (by omega), key 45 (by omega) (by omega)]
  simp only [Bool.or_self, hd48]
  rcases Nat.lt_trichotomy st.phase 1 with h | h | h
  · have : st.phase = 0 := by omega
    simp [this]
  · simp [h]
  · simp [show ¬ st.phase = 0 from by omega, show ¬ st.phase = 1 from by omega]

/-- A decimal digit character's byte is none of the structural bytes `numByte` special-cases, so
`numByte` takes the digit branch and, in phase 0, folds it into the mantissa. -/
theorem foldl_numByte_digits (ds : List Char) (st : NState) (hp : st.phase = 0)
    (hd : ∀ c ∈ ds, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    ds.foldl (fun s c => numByte s (UInt8.ofNat c.toNat)) st
      = { st with mant := ds.foldl (fun a c => a * 10 + (c.toNat - 48)) st.mant } := by
  induction ds generalizing st with
  | nil => simp
  | cons c cs ih =>
    obtain ⟨hc1, hc2⟩ := hd c (by simp)
    rw [List.foldl_cons, numByte_digit st c hc1 hc2]
    simp only [hp, ↓reduceIte]
    rw [ih _ (by simp [hp]) (fun c hc => hd c (by simp [hc]))]
    simp [List.foldl_cons]

/-- Phase-1 (fractional) `numByte` fold: accumulate the mantissa and count each digit. -/
theorem foldl_numByte_frac (ds : List Char) (st : NState) (hp : st.phase = 1)
    (hd : ∀ c ∈ ds, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    ds.foldl (fun s c => numByte s (UInt8.ofNat c.toNat)) st
      = { st with mant := ds.foldl (fun a c => a * 10 + (c.toNat - 48)) st.mant,
                  fracLen := st.fracLen + ds.length } := by
  induction ds generalizing st with
  | nil => simp
  | cons c cs ih =>
    obtain ⟨hc1, hc2⟩ := hd c (by simp)
    rw [List.foldl_cons, numByte_digit st c hc1 hc2]
    simp only [hp, ↓reduceIte]
    rw [ih _ (by simp) (fun c hc => hd c (by simp [hc]))]
    simp [List.foldl_cons, Nat.add_assoc, Nat.add_comm 1]

/-- Folding `numByte` over an ASCII digit string's UTF-8 bytes accumulates the mantissa. -/
theorem foldl_numByte_ascii (cs : List Char) (st : NState) (hp : st.phase = 0)
    (hd : ∀ c ∈ cs, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    (cs.flatMap String.utf8EncodeChar).foldl numByte st
      = { st with mant := cs.foldl (fun a c => a * 10 + (c.toNat - 48)) st.mant } := by
  rw [flatMap_ascii cs (fun c hc => by have := hd c hc; omega), List.foldl_map]
  exact foldl_numByte_digits cs st hp hd

/-- Phase-1 byte-form fold: over an ASCII digit string's UTF-8 bytes, accumulate mantissa and
count fractional digits. -/
theorem foldl_numByte_frac_ascii (cs : List Char) (st : NState) (hp : st.phase = 1)
    (hd : ∀ c ∈ cs, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    (cs.flatMap String.utf8EncodeChar).foldl numByte st
      = { st with mant := cs.foldl (fun a c => a * 10 + (c.toNat - 48)) st.mant,
                  fracLen := st.fracLen + cs.length } := by
  rw [flatMap_ascii cs (fun c hc => by have := hd c hc; omega), List.foldl_map]
  exact foldl_numByte_frac cs st hp hd

/-- Phase-2 (exponent) `numByte` fold: accumulate the decimal exponent and preserve all
other decoder state. -/
theorem foldl_numByte_exp_ascii (cs : List Char) (st : NState) (hp : st.phase = 2)
    (hd : ∀ c ∈ cs, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    (cs.flatMap String.utf8EncodeChar).foldl numByte st
      = { st with expVal := cs.foldl (fun a c => a * 10 + (c.toNat - 48)) st.expVal } := by
  rw [flatMap_ascii cs (fun c hc => by have := hd c hc; omega), List.foldl_map]
  induction cs generalizing st with
  | nil => simp
  | cons c cs ih =>
    obtain ⟨hc1, hc2⟩ := hd c (by simp)
    rw [List.foldl_cons, numByte_digit st c hc1 hc2]
    simp only [hp]
    rw [ih _ (by simp) (fun c hc => hd c (by simp [hc]))]
    simp [List.foldl_cons]

/-- The decimal-point byte switches the decoder to the fractional phase. -/
theorem numByte_dot (st : NState) : numByte st (UInt8.ofNat ('.').toNat) = { st with phase := 1 } :=
  rfl

/-- The Horner fold over leading zeros starting from `0` stays `0`. -/
theorem foldl_H_zeros (n : Nat) :
    (List.replicate n '0').foldl (fun a c => a * 10 + (c.toNat - 48)) 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.foldl_cons]; norm_num; exact ih

/-- The `numByte` fold over an integer part, the point, and a fractional part yields the mantissa
of all digits together (starting from `st`) and a fractional length equal to the fractional part;
other `NState` fields (e.g. the sign) are preserved. -/
theorem fold_frac_chars (intg fracg : List Char) (st : NState) (hp : st.phase = 0)
    (hi : ∀ c ∈ intg, 48 ≤ c.toNat ∧ c.toNat ≤ 57)
    (hf : ∀ c ∈ fracg, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    (intg.flatMap String.utf8EncodeChar ++ String.utf8EncodeChar '.'
        ++ fracg.flatMap String.utf8EncodeChar).foldl numByte st
      = { st with
          mant := (intg ++ fracg).foldl (fun a c => a * 10 + (c.toNat - 48)) st.mant
          fracLen := st.fracLen + fracg.length
          phase := 1 } := by
  rw [List.append_assoc, List.foldl_append, foldl_numByte_ascii _ _ hp hi,
    ascii_encode '.' (by decide), List.foldl_append, List.foldl_cons, List.foldl_nil,
    numByte_dot, foldl_numByte_frac_ascii _ _ rfl hf]
  simp [List.foldl_append]

/-- **Fractional number round-trip.** For a nonnegative `m` and `e > 0`, decoding the bytes of
`renderNum m e` recovers `num m e`. The zero-padding contributes nothing to the mantissa and the
fractional length equals `e`. -/
theorem decode_renderNum_frac (m : Int) (hm : 0 ≤ m) (e : Nat) (he : 0 < e) :
    decodeNumberBytes? (renderNum m e).toUTF8 0 (renderNum m e).toUTF8.size
      = some (Json.num m e) := by
  have hna : m.natAbs = m.toNat := by omega
  have htl : (toString m.natAbs).toList = Nat.toDigits 10 m.toNat := by
    rw [hna]; exact GripProps.NatDigits.repr_toList _
  set len := (toString m.natAbs).length with hlen
  have hlenL : len = (Nat.toDigits 10 m.toNat).length := by
    rw [hlen, hna]; exact GripProps.NatDigits.repr_length _
  set ds := List.replicate (e + 1 - len) '0' ++ Nat.toDigits 10 m.toNat with hds
  set k := ds.length - e with hk
  have hds_dig : ∀ c ∈ ds, 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · rw [List.eq_of_mem_replicate h]; decide
    · exact GripProps.NatDigits.mem_toDigits_bound m.toNat c h
  have hdslen : e ≤ ds.length := by
    rw [hds, List.length_append, List.length_replicate, ← hlenL]; omega
  have hrn : (renderNum m e).toList = ds.take k ++ '.' :: ds.drop k := by
    unfold renderNum
    simp only [show (e == 0) = false from by simp [he.ne'],
      Bool.false_eq_true, if_false,
      if_neg (show ¬ m < 0 by omega), String.empty_append, String.toList_append,
      String.toList_ofList, show ("." : String).toList = ['.'] from by decide]
    rw [htl, ← hlen]
    simp [hds, hk, List.length_append, List.length_replicate]
  have hst : (renderNum m e).toUTF8.foldl numByte {} 0 (renderNum m e).toUTF8.size
      = ({ mant := m.toNat, fracLen := e, phase := 1 } : NState) := by
    rw [GripProps.Bytes.toUTF8_foldl, hrn, List.flatMap_append, List.flatMap_cons,
      ← List.append_assoc,
      fold_frac_chars _ _ {} rfl (fun c hc => hds_dig c (List.mem_of_mem_take hc))
        (fun c hc => hds_dig c (List.mem_of_mem_drop hc))]
    have hmant : (ds.take k ++ ds.drop k).foldl (fun a c => a * 10 + (c.toNat - 48)) 0
        = m.toNat := by
      rw [List.take_append_drop, hds, List.foldl_append, foldl_H_zeros]
      exact GripProps.NatDigits.foldl_toDigits _
    have hfrac : (ds.drop k).length = e := by rw [List.length_drop]; omega
    rw [show ({} : NState).mant = 0 from rfl, hmant, hfrac]
    simp
  unfold decodeNumberBytes?
  rw [hst]
  simp only [Bool.false_eq_true, if_false, CharP.cast_eq_zero, zero_sub, ge_iff_le,
    Left.nonneg_neg_iff, Int.natCast_nonpos_iff]
  rw [if_neg (show ¬ e = 0 by omega), neg_neg, Int.toNat_natCast, Int.toNat_of_nonneg hm]

/-- **Negative fractional number round-trip.** For `m < 0` and `e > 0`. The leading `-` sets the
sign flag before the fractional decode; the sign literal uses ordinary `++`, so unlike the
integer case there is no `String.Internal.append` obstruction. -/
theorem decode_renderNum_frac_neg (m : Int) (hm : m < 0) (e : Nat) (he : 0 < e) :
    decodeNumberBytes? (renderNum m e).toUTF8 0 (renderNum m e).toUTF8.size
      = some (Json.num m e) := by
  have htl : (toString m.natAbs).toList = Nat.toDigits 10 m.natAbs :=
    GripProps.NatDigits.repr_toList _
  set len := (toString m.natAbs).length with hlen
  have hlenL : len = (Nat.toDigits 10 m.natAbs).length := by
    rw [hlen]; exact GripProps.NatDigits.repr_length _
  set ds := List.replicate (e + 1 - len) '0' ++ Nat.toDigits 10 m.natAbs with hds
  set k := ds.length - e with hk
  have hds_dig : ∀ c ∈ ds, 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · rw [List.eq_of_mem_replicate h]; decide
    · exact GripProps.NatDigits.mem_toDigits_bound m.natAbs c h
  have hdslen : e ≤ ds.length := by
    rw [hds, List.length_append, List.length_replicate, ← hlenL]; omega
  have hrn : (renderNum m e).toList = '-' :: (ds.take k ++ '.' :: ds.drop k) := by
    unfold renderNum
    simp only [show (e == 0) = false from by simp [he.ne'],
      Bool.false_eq_true, if_false, if_pos hm, String.toList_append,
      String.toList_ofList, show ("." : String).toList = ['.'] from by decide,
      show ("-" : String).toList = ['-'] from by decide]
    rw [htl, ← hlen]
    simp [hds, hk, List.length_append, List.length_replicate, List.append_assoc]
  have hst : (renderNum m e).toUTF8.foldl numByte {} 0 (renderNum m e).toUTF8.size
      = ({ mant := m.natAbs, fracLen := e, phase := 1, mantNeg := true } : NState) := by
    rw [GripProps.Bytes.toUTF8_foldl, hrn, List.flatMap_cons, ascii_encode '-' (by decide),
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      show numByte {} (UInt8.ofNat ('-').toNat) = ({ mantNeg := true } : NState) from rfl,
      List.flatMap_append, List.flatMap_cons, ← List.append_assoc,
      fold_frac_chars _ _ _ rfl (fun c hc => hds_dig c (List.mem_of_mem_take hc))
        (fun c hc => hds_dig c (List.mem_of_mem_drop hc))]
    have hmant : (ds.take k ++ ds.drop k).foldl (fun a c => a * 10 + (c.toNat - 48))
        ({ mantNeg := true } : NState).mant = m.natAbs := by
      rw [List.take_append_drop, hds, List.foldl_append, foldl_H_zeros]
      exact GripProps.NatDigits.foldl_toDigits _
    have hfrac : (ds.drop k).length = e := by rw [List.length_drop]; omega
    rw [hmant, hfrac]; simp
  unfold decodeNumberBytes?
  rw [hst]
  simp only [Bool.false_eq_true, if_false, if_true, CharP.cast_eq_zero, zero_sub,
    ge_iff_le, Left.nonneg_neg_iff, Int.natCast_nonpos_iff]
  rw [if_neg (show ¬ e = 0 by omega), neg_neg, Int.toNat_natCast,
    show -(m.natAbs : Int) = m from by omega]

/-- **Integer number round-trip.** For a nonnegative integer, decoding the bytes of its rendering
recovers it. Composes the ByteArray/toUTF8 fold bridge, the digit-fold inversion, and the numByte
accumulation. -/
theorem decode_renderNum_int (m : Int) (hm : 0 ≤ m) :
    decodeNumberBytes? (renderNum m 0).toUTF8 0 (renderNum m 0).toUTF8.size
      = some (Json.num m 0) := by
  have hna : m.natAbs = m.toNat := by omega
  have hrn0 : renderNum m 0 = toString m.natAbs := by
    unfold renderNum; rw [if_neg (show ¬ m < 0 from by omega)]; simp
  have hchars : (renderNum m 0).toList = Nat.toDigits 10 m.toNat := by
    rw [hrn0, hna]; exact GripProps.NatDigits.repr_toList _
  have hst : (renderNum m 0).toUTF8.foldl numByte {} 0 (renderNum m 0).toUTF8.size
      = ({ mant := m.toNat } : NState) := by
    rw [GripProps.Bytes.toUTF8_foldl, hchars,
      foldl_numByte_ascii _ _ rfl (GripProps.NatDigits.mem_toDigits_bound m.toNat)]
    have hfold : (Nat.toDigits 10 m.toNat).foldl (fun a c => a * 10 + (c.toNat - 48)) 0
        = m.toNat := GripProps.NatDigits.foldl_toDigits _
    simp only [hfold]
  unfold decodeNumberBytes?
  rw [hst]
  simp [Int.toNat_of_nonneg hm, maxExp]

/-- **Negative-integer round-trip.** Restructuring `renderNum`'s `e = 0` case as
`"-" ++ toString m.natAbs` (instead of `Int.repr`, whose `String.Internal.append` has no `toList`
characterization in Lean 4.28) makes the negative branch decodable too. -/
theorem decode_renderNum_int_neg (m : Int) (hm : m < 0) :
    decodeNumberBytes? (renderNum m 0).toUTF8 0 (renderNum m 0).toUTF8.size
      = some (Json.num m 0) := by
  have hrn0 : renderNum m 0 = "-" ++ toString m.natAbs := by
    unfold renderNum; rw [if_pos (show m < 0 from hm)]; simp
  have hrn : (renderNum m 0).toList = '-' :: Nat.toDigits 10 m.natAbs := by
    rw [hrn0, String.toList_append, show ("-" : String).toList = ['-'] from by decide,
      show (toString m.natAbs).toList = Nat.toDigits 10 m.natAbs from
        GripProps.NatDigits.repr_toList _]
    rfl
  have hst : (renderNum m 0).toUTF8.foldl numByte {} 0 (renderNum m 0).toUTF8.size
      = ({ mant := m.natAbs, mantNeg := true } : NState) := by
    rw [GripProps.Bytes.toUTF8_foldl, hrn, List.flatMap_cons, ascii_encode '-' (by decide),
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      show numByte {} (UInt8.ofNat ('-').toNat) = ({ mantNeg := true } : NState) from rfl,
      foldl_numByte_ascii _ _ rfl (GripProps.NatDigits.mem_toDigits_bound m.natAbs)]
    have hfold : (Nat.toDigits 10 m.natAbs).foldl (fun a c => a * 10 + (c.toNat - 48))
        ({ mantNeg := true } : NState).mant = m.natAbs :=
      GripProps.NatDigits.foldl_toDigits _
    rw [hfold]
  unfold decodeNumberBytes?
  rw [hst]
  norm_num [maxExp]
  rw [abs_of_neg hm, neg_neg]

/-- Scientific notation round-trip for large fractional exponents. The mantissa is rendered as
an integer followed by `e-<exponent>`, so decoding produces the same exact `num m e` without
materializing the fractional zero padding. -/
theorem decode_renderNumScientific (m : Int) (e : Nat) (he : 0 < e) :
    decodeNumberBytes? (renderNumScientific m e).toUTF8 0 (renderNumScientific m e).toUTF8.size
      = some (Json.num m e) := by
  have hdigits : (toString m.natAbs).toList = Nat.toDigits 10 m.natAbs :=
    GripProps.NatDigits.repr_toList _
  have hexp : (toString e).toList = Nat.toDigits 10 e :=
    GripProps.NatDigits.repr_toList _
  have hmant : ∀ (st : NState), st.phase = 0 → st.mant = 0 →
      ((toString m.natAbs).toList.flatMap String.utf8EncodeChar).foldl numByte st =
        { st with mant := m.natAbs } := by
    intro st hp hz
    rw [hdigits, foldl_numByte_ascii _ _ hp
      (GripProps.NatDigits.mem_toDigits_bound m.natAbs)]
    have hfold : (Nat.toDigits 10 m.natAbs).foldl
        (fun a c => a * 10 + (c.toNat - 48)) st.mant = m.natAbs := by
      rw [hz]; exact GripProps.NatDigits.foldl_toDigits _
    rw [hfold]
  have hexpFold : ∀ (st : NState), st.phase = 2 → st.expVal = 0 →
      ((toString e).toList.flatMap String.utf8EncodeChar).foldl numByte st =
        { st with expVal := e } := by
    intro st hp hz
    rw [hexp,
      foldl_numByte_exp_ascii _ _ hp (GripProps.NatDigits.mem_toDigits_bound e)]
    have hfold : (Nat.toDigits 10 e).foldl
        (fun a c => a * 10 + (c.toNat - 48)) st.expVal = e := by
      rw [hz]; exact GripProps.NatDigits.foldl_toDigits _
    rw [hfold]
  by_cases hm : m < 0
  · have hchars : (renderNumScientific m e).toList =
        '-' :: ((toString m.natAbs).toList ++ ('e' :: '-' :: (toString e).toList)) := by
      unfold renderNumScientific
      simp only [if_pos hm, String.toList_append,
        show ("-" : String).toList = ['-'] from by decide,
        show ("e-" : String).toList = ['e', '-'] from by decide]
      simp [List.append_assoc]
    have hst : (renderNumScientific m e).toUTF8.foldl numByte {}
          0 (renderNumScientific m e).toUTF8.size =
        ({ mant := m.natAbs, mantNeg := true, expVal := e, expNeg := true,
            phase := 2 } : NState) := by
      rw [GripProps.Bytes.toUTF8_foldl, hchars, List.flatMap_cons,
        ascii_encode '-' (by decide), List.flatMap_append, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      rw [show numByte {} (UInt8.ofNat ('-').toNat) = ({ mantNeg := true } : NState) from rfl,
        List.foldl_append,
        hmant ({ mantNeg := true } : NState) rfl (by rfl),
        List.flatMap_cons, ascii_encode 'e' (by decide),
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [show numByte { mant := m.natAbs, mantNeg := true } (UInt8.ofNat ('e').toNat) =
          ({ mant := m.natAbs, mantNeg := true, phase := 2 } : NState) from rfl,
        List.flatMap_cons, ascii_encode '-' (by decide), List.foldl_append,
        List.foldl_cons, List.foldl_nil,
        show numByte { mant := m.natAbs, mantNeg := true, phase := 2 }
          (UInt8.ofNat ('-').toNat) =
          ({ mant := m.natAbs, mantNeg := true, expNeg := true, phase := 2 } : NState) from rfl,
        hexpFold _ rfl rfl]
    unfold decodeNumberBytes?
    rw [hst]
    simp only [if_true, CharP.cast_eq_zero, ge_iff_le]
    rw [show -(m.natAbs : Int) = m by omega]
    have hexp : 0 ≤ -(-(e : Int) - 0) := by omega
    norm_num [Int.toNat_of_nonneg hexp]
    intro h; omega
  · have hchars : (renderNumScientific m e).toList =
        (toString m.natAbs).toList ++ ('e' :: '-' :: (toString e).toList) := by
      unfold renderNumScientific
      simp only [if_neg hm, String.toList_append,
        show ("e-" : String).toList = ['e', '-'] from by decide]
      simp [List.append_assoc]
    have hst : (renderNumScientific m e).toUTF8.foldl numByte {}
          0 (renderNumScientific m e).toUTF8.size =
        ({ mant := m.natAbs, expVal := e, expNeg := true, phase := 2 } : NState) := by
      rw [GripProps.Bytes.toUTF8_foldl, hchars, List.flatMap_append, List.foldl_append,
        hmant _ rfl rfl, List.flatMap_cons, ascii_encode 'e' (by decide),
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [show numByte { mant := m.natAbs } (UInt8.ofNat ('e').toNat) =
          ({ mant := m.natAbs, phase := 2 } : NState) from rfl,
        List.flatMap_cons, ascii_encode '-' (by decide), List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      rw [show numByte { mant := m.natAbs, phase := 2 } (UInt8.ofNat ('-').toNat) =
          ({ mant := m.natAbs, expNeg := true, phase := 2 } : NState) from rfl,
        hexpFold _ rfl rfl]
    unfold decodeNumberBytes?
    rw [hst]
    simp only [Bool.false_eq_true, if_false, if_true, CharP.cast_eq_zero, ge_iff_le]
    rw [show (m.natAbs : Int) = m by omega]
    have hexp : 0 ≤ -(-(e : Int) - 0) := by omega
    norm_num [Int.toNat_of_nonneg hexp]
    intro h; omega

/-- `decodeNumberBytes?` depends only on the folded state, so equal folds decode equally. -/
theorem decodeNumberBytes?_congr {arr1 arr2 : ByteArray} {q1 q1' q2 q2' : Nat}
    (h : arr1.foldl numByte {} q1 q1' = arr2.foldl numByte {} q2 q2') :
    decodeNumberBytes? arr1 q1 q1' = decodeNumberBytes? arr2 q2 q2' := by
  unfold decodeNumberBytes?; rw [h]

/-- Lift a whole-lexeme decode result through any byte slice matching that lexeme. -/
theorem decode_at (s : String) (v : Json) (arr : ByteArray) (q : Nat)
    (hsize : q + s.toUTF8.size ≤ arr.size)
    (hm : ∀ j, j < s.toUTF8.size → arr[q + j]! = s.toUTF8[j]!)
    (hd : decodeNumberBytes? s.toUTF8 0 s.toUTF8.size = some v) :
    decodeNumberBytes? arr q (q + s.toUTF8.size) = some v := by
  rw [decodeNumberBytes?_congr
    (GripProps.Bytes.foldl_congr_match numByte {} arr s.toUTF8 q 0
      s.toUTF8.size hsize (by omega)
      (fun i hi => by rw [Nat.zero_add]; exact hm i hi))]
  simpa using hd

/-- Decoding a number that matches `renderNum m e` at offset `q` recovers `num m e`, given the
whole-array decode result. -/
theorem decode_renderNum_at (arr : ByteArray) (q : Nat) (m : Int) (e : Nat)
    (hsize : q + (renderNum m e).toUTF8.size ≤ arr.size)
    (hm : ∀ j, j < (renderNum m e).toUTF8.size → arr[q + j]! = (renderNum m e).toUTF8[j]!)
    (hd : decodeNumberBytes? (renderNum m e).toUTF8 0 (renderNum m e).toUTF8.size
      = some (Json.num m e)) :
    decodeNumberBytes? arr q (q + (renderNum m e).toUTF8.size) = some (Json.num m e) :=
  decode_at _ _ arr q hsize hm hd

/-- Lift the scientific-notation decoder lemma through an arbitrary matching byte slice. -/
theorem decode_renderNumScientific_at (arr : ByteArray) (q : Nat) (m : Int) (e : Nat)
    (hsize : q + (renderNumScientific m e).toUTF8.size ≤ arr.size)
    (hm : ∀ j, j < (renderNumScientific m e).toUTF8.size →
      arr[q + j]! = (renderNumScientific m e).toUTF8[j]!)
    (hd : decodeNumberBytes? (renderNumScientific m e).toUTF8 0
      (renderNumScientific m e).toUTF8.size = some (Json.num m e)) :
    decodeNumberBytes? arr q (q + (renderNumScientific m e).toUTF8.size) = some (Json.num m e) :=
  decode_at _ _ arr q hsize hm hd
