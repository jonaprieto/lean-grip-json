/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Mathlib
import GripJson
import GripProps.Json.ScanStr
import GripProps.Json.Number

/-!
# Parser run-denotation over a serialized prefix

The `parse ∘ render = id` proof runs the parser on `render v`'s bytes followed by an arbitrary
suffix, so each combinator needs a `run`-characterization on inputs of the form `sv ++ rest`.
This file supplies those characterizations from the primitive byte parsers through strings,
numbers, and the recursive `value` parser.
-/

set_option maxHeartbeats 1000000

open Grip
open GripProps.Bytes GripProps.NatDigits

namespace GripProps.Parse

/-- At the end of the whole input, `eof` succeeds consuming nothing. -/
theorem eof_run_end (arr : ByteArray) (q : Nat) (hq : arr.size ≤ q) :
    (GParser.eof).run arr q = .ok () q := by
  simp only [GParser.eof, GParser.label, GParser.notFollowedBy, GParser.satisfy]
  rw [dif_neg (by omega : ¬ q < arr.size)]

/-- `scanFwd` consumes exactly a maximal run of `n` matching bytes ending at a non-match or EOF. -/
theorem scanFwd_run (arr : ByteArray) (f : UInt8 → Bool) (q n : Nat)
    (hall : ∀ i, i < n → f arr[q + i]! = true)
    (hstop : q + n = arr.size ∨ (q + n < arr.size ∧ f arr[q + n]! = false)) :
    scanFwd arr f q = q + n := by
  induction n generalizing q with
  | zero =>
    simp only [Nat.add_zero] at hstop ⊢
    rw [scanFwd]
    rcases hstop with h | ⟨h, hf⟩
    · rw [dif_neg (by omega)]
    · rw [dif_pos h, if_neg (by rw [← getElem!_pos arr q h]; simp [hf])]
  | succ n ih =>
    have hqs : q < arr.size := by omega
    have hf0 : f arr[q] = true := by
      rw [← getElem!_pos arr q hqs]; simpa using hall 0 (by omega)
    rw [scanFwd, dif_pos hqs, if_pos hf0,
      ih (q + 1)
        (fun i hi => by
          have := hall (i + 1) (by omega)
          rwa [show q + (i + 1) = q + 1 + i from by omega] at this)
        (by rcases hstop with h | ⟨h, hf⟩
            · exact Or.inl (by omega)
            · refine Or.inr ⟨by omega, ?_⟩
              rwa [show q + 1 + n = q + (n + 1) from by omega])]
    omega

/-- `takeWhile f` consumes a maximal run of `n` matching bytes. -/
theorem takeWhile_run (f : UInt8 → Bool) (arr : ByteArray) (q n : Nat)
    (hall : ∀ i, i < n → f arr[q + i]! = true)
    (hstop : q + n = arr.size ∨ (q + n < arr.size ∧ f arr[q + n]! = false)) :
    (GParser.takeWhile f).run arr q = .ok n (q + n) := by
  simp only [GParser.takeWhile, scanFwd_run arr f q n hall hstop, Nat.add_sub_cancel_left]

variable {α β γ : Type} {g g' : Grade}

/-- `map` on a successful sub-parse. -/
theorem map_run_ok (h : α → β) (x : GParser g α) (arr : ByteArray) (q : Nat) (a : α) (q' : Nat)
    (hx : x.run arr q = .ok a q') : (GParser.map h x).run arr q = .ok (h a) q' := by
  simp only [GParser.map, hx]

/-- `seqR` on two successes keeps the right value. -/
theorem seqR_run (x : GParser g α) (y : GParser g' β) (arr : ByteArray) (q : Nat) (a : α) (q' : Nat)
    (b : β) (q'' : Nat) (hx : x.run arr q = .ok a q') (hy : y.run arr q' = .ok b q'') :
    (GParser.seqR x y).run arr q = .ok b q'' := by
  simp only [GParser.seqR, hx, hy]

/-- `seqL` on two successes keeps the left value. -/
theorem seqL_run (x : GParser g α) (y : GParser g' β) (arr : ByteArray) (q : Nat) (a : α) (q' : Nat)
    (b : β) (q'' : Nat) (hx : x.run arr q = .ok a q') (hy : y.run arr q' = .ok b q'') :
    (GParser.seqL x y).run arr q = .ok a q'' := by
  simp only [GParser.seqL, hx, hy]

/-- `map2` on two successes combines the values. -/
theorem map2_run (f : α → β → γ) (x : GParser g α) (y : GParser g' β) (arr : ByteArray) (q : Nat)
    (a : α) (q' : Nat) (b : β) (q'' : Nat)
    (hx : x.run arr q = .ok a q') (hy : y.run arr q' = .ok b q'') :
    (GParser.map2 f x y).run arr q = .ok (f a b) q'' := by
  simp only [GParser.map2, hx, hy]

/-- `captureWith? f p`: `p` succeeds and `f` accepts the consumed range. -/
theorem captureWith?_run {δ : Type} (f : ByteArray → Nat → Nat → Option δ) (p : GParser g α)
    (arr : ByteArray) (q : Nat) (a : α) (q' : Nat) (d : δ)
    (hp : p.run arr q = .ok a q') (hf : f arr q q' = some d) :
    (GParser.captureWith? f p).run arr q = .ok d q' := by
  simp only [GParser.captureWith?, hp, hf]

/-- `alt`, left branch succeeds. -/
theorem alt_run_left {ge gc ge' gc' : Modality} (x : GParser ⟨ge, gc⟩ α) (y : GParser ⟨ge', gc'⟩ α)
    (arr : ByteArray) (q : Nat) (a : α) (q' : Nat) (hx : x.run arr q = .ok a q') :
    (GParser.alt x y).run arr q = .ok a q' := by
  simp only [GParser.alt, hx]

/-- `alt`, left fails, right succeeds. -/
theorem alt_run_right {ge gc ge' gc' : Modality} (x : GParser ⟨ge, gc⟩ α)
    (y : GParser ⟨ge', gc'⟩ α) (arr : ByteArray) (q : Nat) (ex : Err) (a : α) (q' : Nat)
    (hx : x.run arr q = .error ex) (hy : y.run arr q = .ok a q') :
    (GParser.alt x y).run arr q = .ok a q' := by
  simp only [GParser.alt, hx, hy]

/-- `satisfy f` on an in-bounds byte satisfying `f` (stated with `getElem!`). -/
theorem satisfy_run! (f : UInt8 → Bool) (arr : ByteArray) (q : Nat) (hq : q < arr.size)
    (hf : f arr[q]! = true) : (GParser.satisfy f).run arr q = .ok arr[q]! (q + 1) := by
  rw [getElem!_pos arr q hq] at hf ⊢
  simp only [GParser.satisfy, dif_pos hq, hf, if_true]

/-- `byte c` on a matching in-bounds byte (stated with `getElem!`). -/
theorem byte_run! (c : UInt8) (arr : ByteArray) (q : Nat) (hq : q < arr.size)
    (hc : arr[q]! = c) : (GParser.byte c).run arr q = .ok () (q + 1) := by
  rw [getElem!_pos arr q hq] at hc
  simp only [GParser.byte, dif_pos hq, hc, beq_self_eq_true, if_true]

/-- `byte c` fails at an in-bounds non-matching byte. -/
theorem byte_run_fail! (c : UInt8) (arr : ByteArray) (q : Nat) (hq : q < arr.size)
    (hc : arr[q]! ≠ c) : (GParser.byte c).run arr q = .error ⟨q, []⟩ := by
  rw [getElem!_pos arr q hq] at hc
  simp only [GParser.byte, dif_pos hq]
  rw [if_neg (by simpa [beq_iff_eq] using hc)]

/-- `byte c` fails at end of input. -/
theorem byte_run_end (c : UInt8) (arr : ByteArray) (q : Nat) (hq : arr.size ≤ q) :
    (GParser.byte c).run arr q = .error ⟨q, []⟩ := by
  simp only [GParser.byte, dif_neg (Nat.not_lt.mpr hq)]

/-- `satisfy f` fails at an in-bounds non-satisfying byte. -/
theorem satisfy_run_fail! (f : UInt8 → Bool) (arr : ByteArray) (q : Nat) (hq : q < arr.size)
    (hf : f arr[q]! = false) : (GParser.satisfy f).run arr q = .error ⟨q, []⟩ := by
  rw [getElem!_pos arr q hq] at hf
  simp only [GParser.satisfy, dif_pos hq]; rw [if_neg (by simp [hf])]

/-- `satisfy f` fails at end of input. -/
theorem satisfy_run_end (f : UInt8 → Bool) (arr : ByteArray) (q : Nat) (hq : arr.size ≤ q) :
    (GParser.satisfy f).run arr q = .error ⟨q, []⟩ := by
  simp only [GParser.satisfy, dif_neg (Nat.not_lt.mpr hq)]

/-- `seqR`, left fails. -/
theorem seqR_run_fail_left (x : GParser g α) (y : GParser g' β) (arr : ByteArray) (q : Nat)
    (e : Err) (hx : x.run arr q = .error e) : (GParser.seqR x y).run arr q = .error e := by
  simp only [GParser.seqR, hx]

/-- `matchBytes` succeeds when `arr`'s bytes from `q` match `bs` from `i`. -/
theorem matchBytes_true (arr bs : ByteArray) (q i : Nat)
    (hsize : q + (bs.size - i) ≤ arr.size)
    (hmatch : ∀ j, i ≤ j → j < bs.size → arr[q + (j - i)]! = bs[j]!) :
    Grip.matchBytes arr bs i q = true := by
  rw [Grip.matchBytes]
  split
  · rename_i hi
    rw [if_pos (show q < arr.size by omega), Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [beq_iff_eq]; simpa using hmatch i (le_refl i) hi
    · exact matchBytes_true arr bs (q + 1) (i + 1) (by omega) (fun j hj hjs => by
        have := hmatch j (by omega) hjs
        have he : q + 1 + (j - (i + 1)) = q + (j - i) := by omega
        rwa [he])
  · rfl
termination_by bs.size - i
decreasing_by omega

/-- `string s` (nonempty) succeeds when `arr`'s bytes from `q` match `s`'s UTF-8. -/
theorem string_run (s : String) (arr : ByteArray) (q : Nat)
    (hne : 0 < s.toUTF8.size) (hsize : q + s.toUTF8.size ≤ arr.size)
    (hmatch : ∀ j, j < s.toUTF8.size → arr[q + j]! = s.toUTF8[j]!) :
    (GParser.string s).run arr q = .ok () (q + s.toUTF8.size) := by
  have hmb : Grip.matchBytes arr s.toUTF8 0 q = true :=
    matchBytes_true arr s.toUTF8 q 0 (by simpa using hsize)
      (fun j _ hj => by simpa using hmatch j hj)
  simp only [GParser.string, hmb, if_true, if_pos (show q < q + s.toUTF8.size by omega)]

/-- `optional p`, `p` succeeds. -/
theorem optional_run_some (p : GParser g α) (arr : ByteArray) (q : Nat) (a : α) (q' : Nat)
    (hp : p.run arr q = .ok a q') : (GParser.optional p).run arr q = .ok (some a) q' := by
  simp only [GParser.optional]
  exact alt_run_left _ _ arr q (some a) q' (map_run_ok some p arr q a q' hp)

/-- `optional p`, `p` fails without consuming (grade forces same-offset failure); result `none`. -/
theorem optional_run_none (p : GParser g α) (arr : ByteArray) (q : Nat) (e : Err)
    (hp : p.run arr q = .error e) : (GParser.optional p).run arr q = .ok none q := by
  simp only [GParser.optional, GParser.alt, GParser.map, hp, GParser.pure]

/-- `ws` consumes nothing at a non-whitespace in-bounds byte. -/
theorem ws_run_stop (arr : ByteArray) (q : Nat) (hq : q < arr.size)
    (hw : Ascii.isWs arr[q] = false) :
    (GParser.ws).run arr q = .ok 0 q := by
  have : scanFwd arr Ascii.isWs q = q := by rw [scanFwd, dif_pos hq, if_neg (by simp [hw])]
  simp only [GParser.ws, GParser.takeWhile, this, Nat.sub_self]

/-- `ws` consumes nothing at end of input. -/
theorem ws_run_end (arr : ByteArray) (q : Nat) (hq : arr.size ≤ q) :
    (GParser.ws).run arr q = .ok 0 q := by
  have : scanFwd arr Ascii.isWs q = q := by rw [scanFwd, dif_neg (by omega)]
  simp only [GParser.ws, GParser.takeWhile, this, Nat.sub_self]

/-- `wsDispatch`, with no leading whitespace, runs the parser its `select` picks for the
current byte. -/
theorem wsDispatch_run_stop (select : UInt8 → GParser conditional Grip.Json.Json)
    (arr : ByteArray) (q : Nat) (hq : q < arr.size) (hw : Ascii.isWs arr[q] = false) :
    (Grip.Json.wsDispatch select).run arr q = (select arr[q]).run arr q := by
  have hs : scanFwd arr Ascii.isWs q = q := by rw [scanFwd, dif_pos hq, if_neg (by simp [hw])]
  simp only [Grip.Json.wsDispatch, hs, dif_pos hq]

/-- `wsByte b`, no leading whitespace, matching byte: consume it. -/
theorem wsByte_run_stop (b : UInt8) (name : String) (arr : ByteArray) (q : Nat)
    (hq : q < arr.size)
    (hw : Ascii.isWs arr[q] = false) (hb : arr[q] = b) :
    (Grip.Json.wsByte b name).run arr q = .ok () (q + 1) := by
  have hs : scanFwd arr Ascii.isWs q = q := by rw [scanFwd, dif_pos hq, if_neg (by simp [hw])]
  simp only [Grip.Json.wsByte, hs, dif_pos hq, hb, beq_self_eq_true, if_true]

/-- One-step unfolding of `fix`: its run is the body applied to the clamped self at the
bytes-remaining fuel, behind the advance clamp. -/
theorem fix_run_unroll (f : GParser conditional α → GParser conditional α) (arr : ByteArray)
    (q : Nat) :
    (GParser.fix f).run arr q
      = clampAdvance arr q ((f (GParser.fixSelf f (arr.size - q))).run arr q) := by
  show clampAdvance arr q (GParser.fixFuel f (arr.size - q + 1) arr q) = _
  rw [GParser.fixFuel_succ]

/-- The advance clamp is the identity on a success that advances within bounds. -/
theorem clampAdvance_ok (arr : ByteArray) (q : Nat) {v : Grip.Json.Json} {q' : Nat}
    (h1 : q < q') (h2 : q' ≤ arr.size) :
    clampAdvance arr q (.ok v q') = .ok v q' := by
  have h : q < q' ∧ q' ≤ arr.size := ⟨h1, h2⟩
  simp only [clampAdvance, if_pos h]

open Grip.Json Grip.Json.Decode Grip.Json.Json

/-- A `1-9` digit byte is a digit byte. -/
theorem isDigit19_isDigit {b : UInt8} (h : Ascii.isDigit19 b = true) : Ascii.isDigit b = true := by
  have h48 : ((48 : UInt8)).toNat = 48 := by decide
  have h49 : ((49 : UInt8)).toNat = 49 := by decide
  have h57 : ((57 : UInt8)).toNat = 57 := by decide
  simp only [Ascii.isDigit19, Ascii.isDigit, Bool.and_eq_true, decide_eq_true_eq,
    UInt8.le_iff_toNat_le, h48, h49, h57] at h ⊢
  omega

/-- A digit byte is not whitespace. -/
theorem isDigit_not_ws {b : UInt8} (h : Ascii.isDigit b = true) : Ascii.isWs b = false := by
  have hb : 48 ≤ b.toNat := by
    have h48 : ((48 : UInt8)).toNat = 48 := by decide
    simp only [Ascii.isDigit, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le, h48] at h
    exact h.1
  have e : ∀ c : UInt8, c.toNat < 48 → (b == c) = false := fun c hc => by
    rw [beq_eq_false_iff_ne, ne_eq, ← UInt8.toNat_inj]; omega
  simp only [Ascii.isWs, e 32 (by decide), e 10 (by decide), e 9 (by decide), e 13 (by decide),
    Bool.or_self]

/-- `takeWhile1 f`: a nonempty maximal run of matching bytes. -/
theorem takeWhile1_run (f : UInt8 → Bool) (arr : ByteArray) (q n : Nat) (hq : q < arr.size)
    (hn : 1 ≤ n) (hall : ∀ i, i < n → f arr[q + i]! = true)
    (hstop : q + n = arr.size ∨ (q + n < arr.size ∧ f arr[q + n]! = false)) :
    (GParser.takeWhile1 f).run arr q = .ok n (q + n) := by
  have hf0 : f arr[q] = true := by
    rw [← getElem!_pos arr q hq]; simpa using hall 0 (by omega)
  show (if h : q < arr.size then
      if f arr[q] then (GParser.takeWhile f).run arr q else .error ⟨q, []⟩ else .error ⟨q, []⟩)
      = _
  rw [dif_pos hq, if_pos hf0]
  exact takeWhile_run f arr q n hall hstop

/-- `intPart` consumes a single leading `0`. -/
theorem intPart_run_zero (arr : ByteArray) (q : Nat) (hq : q < arr.size) (h0 : arr[q]! = 48) :
    intPart.run arr q = .ok () (q + 1) := by
  simp only [intPart]
  exact alt_run_left _ _ arr q () (q + 1) (byte_run! (Ascii.code '0') arr q hq (by rw [h0]; decide))

/-- `intPart` consumes a nonzero-leading integer (digit 1-9 then more digits). -/
theorem intPart_run_nonzero (arr : ByteArray) (q n : Nat) (hq : q < arr.size) (hn : 1 ≤ n)
    (h19 : Ascii.isDigit19 arr[q]! = true)
    (hall : ∀ i, 1 ≤ i → i < n → Ascii.isDigit arr[q + i]! = true)
    (hstop : q + n = arr.size ∨ (q + n < arr.size ∧ Ascii.isDigit arr[q + n]! = false)) :
    intPart.run arr q = .ok () (q + n) := by
  have hne : arr[q]! ≠ (48 : UInt8) := by
    intro he; rw [he] at h19; exact absurd h19 (by decide)
  simp only [intPart]
  refine alt_run_right _ _ arr q ⟨q, []⟩ () (q + n) (byte_run_fail! (Ascii.code '0') arr q hq ?_) ?_
  · simpa [show Ascii.code '0' = (48 : UInt8) from by decide] using hne
  · have hsat : (GParser.satisfy Ascii.isDigit19).run arr q = .ok arr[q]! (q + 1) :=
      satisfy_run! _ arr q hq h19
    have htw : (GParser.takeWhile Ascii.isDigit).run arr (q + 1) = .ok (n - 1) (q + n) := by
      have := takeWhile_run Ascii.isDigit arr (q + 1) (n - 1)
        (fun i hi => by have := hall (i + 1) (by omega) (by omega)
                        rwa [show q + (i + 1) = q + 1 + i from by omega] at this)
        (by rcases hstop with h | ⟨h, hf⟩
            · exact Or.inl (by omega)
            · exact Or.inr ⟨by omega, by rwa [show q + 1 + (n - 1) = q + n from by omega]⟩)
      rwa [show q + 1 + (n - 1) = q + n from by omega] at this
    exact seqR_run _ _ arr q _ (q + 1) () (q + n) hsat
      (seqR_run _ _ arr (q + 1) (n - 1) (q + n) () (q + n) htw rfl)

/-- `frac` consumes `.` then a nonempty digit run. -/
theorem frac_run (arr : ByteArray) (q n : Nat) (hq : q < arr.size) (hdot : arr[q]! = 46)
    (hq1 : q + 1 < arr.size) (hn : 2 ≤ n)
    (hall : ∀ i, 1 ≤ i → i < n → Ascii.isDigit arr[q + i]! = true)
    (hstop : q + n = arr.size ∨ (q + n < arr.size ∧ Ascii.isDigit arr[q + n]! = false)) :
    frac.run arr q = .ok (n - 1) (q + n) := by
  simp only [frac]
  have hch : (GParser.ch '.').run arr q = .ok () (q + 1) :=
    byte_run! (Ascii.code '.') arr q hq (by rw [hdot]; decide)
  have htw1 : (GParser.takeWhile1 Ascii.isDigit).run arr (q + 1) = .ok (n - 1) (q + n) := by
    have := takeWhile1_run Ascii.isDigit arr (q + 1) (n - 1) hq1 (by omega)
      (fun i hi => by have := hall (i + 1) (by omega) (by omega)
                      rwa [show q + (i + 1) = q + 1 + i from by omega] at this)
      (by rcases hstop with h | ⟨h, hf⟩
          · exact Or.inl (by omega)
          · exact Or.inr ⟨by omega, by rwa [show q + 1 + (n - 1) = q + n from by omega]⟩)
    rwa [show q + 1 + (n - 1) = q + n from by omega] at this
  exact seqR_run _ _ arr q () (q + 1) (n - 1) (q + n) hch htw1

/-- Unfold a `<?>`-labelled parser on a successful sub-parse: the label rewrites failures only. -/
theorem label_run_ok {g : Grade} {α : Type} (name : String) (p : GParser g α) (arr : ByteArray)
    (q : Nat) (a : α) (q' : Nat) (h : p.run arr q = .ok a q') :
    (GParser.label name p).run arr q = .ok a q' := by
  simp only [GParser.label, h]

/-- Lift an already-established `number` parse through `value`'s byte dispatch. This keeps
specialized render-shape proofs focused on the number grammar rather than duplicating dispatch
reasoning. -/
theorem value_run_number (arr : ByteArray) (q : Nat) (m : Int) (e n : Nat)
    (hq : q < arr.size)
    (hstart : Ascii.isDigit arr[q] = true ∨ arr[q] = Ascii.dash)
    (hnum : number.run arr q = .ok (Json.num m e) (q + n)) :
    value.run arr q = .ok (Json.num m e) (q + n) := by
  rcases hstart with hdigit | hdash
  · have hne : ∀ c : UInt8, Ascii.isDigit c = false → ¬ ((arr[q] == c) = true) := fun c hc => by
      rw [beq_iff_eq]
      intro he
      rw [he, hc] at hdigit
      exact absurd hdigit (by decide)
    rw [value, fix_run_unroll]
    simp only [valueBody]
    rw [wsDispatch_run_stop _ arr q hq (isDigit_not_ws hdigit)]
    simp only [Ascii.lbrace, Ascii.lbracket, Ascii.quote, Ascii.dash]
    rw [if_neg (hne 123 (by decide)), if_neg (hne 91 (by decide)), if_neg (hne 34 (by decide)),
      if_neg (hne (Ascii.code 't') (by decide)), if_neg (hne (Ascii.code 'f') (by decide)),
      if_neg (hne (Ascii.code 'n') (by decide)),
      if_pos (by rw [hdigit]; rfl), hnum]
    exact clampAdvance_ok arr q (number.cwit hnum) (number.bwit (Nat.le_of_lt hq) hnum)
  · have hne : ∀ c : UInt8, c ≠ 45 → ¬ ((arr[q] == c) = true) := fun c hc => by
      rw [beq_iff_eq]
      intro he
      exact hc (he.symm.trans hdash)
    have hws : Ascii.isWs arr[q] = false := by rw [hdash]; decide
    rw [value, fix_run_unroll]
    simp only [valueBody]
    rw [wsDispatch_run_stop _ arr q hq hws]
    simp only [Ascii.lbrace, Ascii.lbracket, Ascii.quote, Ascii.dash]
    rw [if_neg (hne 123 (by decide)), if_neg (hne 91 (by decide)), if_neg (hne 34 (by decide)),
      if_neg (hne (Ascii.code 't') (by decide)), if_neg (hne (Ascii.code 'f') (by decide)),
      if_neg (hne (Ascii.code 'n') (by decide)),
      if_pos (by rw [hdash]; decide), hnum]
    exact clampAdvance_ok arr q (number.cwit hnum) (number.bwit (Nat.le_of_lt hq) hnum)

/-- `value` parses a nonnegative integer number (`e = 0`). The `hstop` byte after the number is a
delimiter (not a digit, `.`, or `e`), so the optional fraction/exponent parsers correctly fail. -/
theorem value_run_num_int (arr : ByteArray) (q : Nat) (m : Int) (_hm : 0 ≤ m) (n : Nat)
    (hn : 1 ≤ n) (hsize : q + n ≤ arr.size)
    (hstruct : (n = 1 ∧ arr[q]! = 48) ∨
      (Ascii.isDigit19 arr[q]! = true ∧ ∀ i, 1 ≤ i → i < n → Ascii.isDigit arr[q + i]! = true))
    (hstop : q + n = arr.size ∨ (q + n < arr.size ∧ Ascii.isDigit arr[q + n]! = false ∧
      arr[q + n]! ≠ 46 ∧ Ascii.isExp arr[q + n]! = false))
    (hdecode : decodeNumberBytes? arr q (q + n) = some (Json.num m 0)) :
    value.run arr q = .ok (Json.num m 0) (q + n) := by
  have hqs : q < arr.size := by omega
  have hd! : Ascii.isDigit arr[q]! = true := by
    rcases hstruct with ⟨_, h0⟩ | ⟨h19, _⟩
    · rw [h0]; decide
    · exact isDigit19_isDigit h19
  have hb : Ascii.isDigit arr[q] = true := by rwa [getElem!_pos arr q hqs] at hd!
  -- innerP consumes exactly [q, q+n)
  have hsign : (GParser.optional (GParser.ch '-')).run arr q = .ok none q :=
    optional_run_none _ arr q ⟨q, []⟩ (byte_run_fail! (Ascii.code '-') arr q hqs
      (by intro he; rw [show Ascii.code '-' = (45 : UInt8) from by decide] at he
          exact absurd (he ▸ hd! : Ascii.isDigit 45 = true) (by decide)))
  have hint : intPart.run arr q = .ok () (q + n) := by
    rcases hstruct with ⟨hn1, h0⟩ | ⟨h19, hds⟩
    · subst hn1; exact intPart_run_zero arr q hqs h0
    · refine intPart_run_nonzero arr q n hqs hn h19 hds ?_
      rcases hstop with h | ⟨h1, h2, _, _⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2⟩
  have hfrac : (GParser.optional frac).run arr (q + n) = .ok none (q + n) := by
    refine optional_run_none _ _ _ ⟨q + n, []⟩ (seqR_run_fail_left _ _ arr (q + n) _ ?_)
    rcases hstop with h | ⟨h1, _, hdot, _⟩
    · exact byte_run_end (Ascii.code '.') arr (q + n) (by omega)
    · exact byte_run_fail! (Ascii.code '.') arr (q + n) h1
        (by rwa [show Ascii.code '.' = (46 : UInt8) from by decide])
  have hexp : (GParser.optional expo).run arr (q + n) = .ok none (q + n) := by
    refine optional_run_none _ _ _ ⟨q + n, []⟩ (seqR_run_fail_left _ _ arr (q + n) _ ?_)
    rcases hstop with h | ⟨h1, _, _, hexp'⟩
    · exact satisfy_run_end _ arr (q + n) (by omega)
    · exact satisfy_run_fail! _ arr (q + n) h1 hexp'
  have hnum : number.run arr q = .ok (Json.num m 0) (q + n) := by
    simp only [number]
    refine label_run_ok "a number" _ arr q _ _ ?_
    exact captureWith?_run decodeNumberBytes? _ arr q () (q + n) (Json.num m 0)
      (seqR_run _ _ arr q none q () (q + n) hsign
        (seqL_run _ _ arr q () (q + n) none (q + n) hint
          (seqR_run _ _ arr (q + n) none (q + n) none (q + n) hfrac hexp))) hdecode
  exact value_run_number arr q m 0 n hqs (Or.inl hb) hnum

/-- `value` parses a nonnegative fractional number (`e > 0`): integer part of length `ip`, `.`,
then a nonempty fractional part, total length `n`. -/
theorem value_run_num_frac (arr : ByteArray) (q : Nat) (m : Int) (e ip n : Nat) (_hm : 0 ≤ m)
    (hip : 1 ≤ ip) (hn : ip + 2 ≤ n) (hsize : q + n ≤ arr.size)
    (hintstruct : (ip = 1 ∧ arr[q]! = 48) ∨
      (Ascii.isDigit19 arr[q]! = true ∧ ∀ i, 1 ≤ i → i < ip → Ascii.isDigit arr[q + i]! = true))
    (hdot : arr[q + ip]! = 46)
    (hfrac : ∀ i, ip + 1 ≤ i → i < n → Ascii.isDigit arr[q + i]! = true)
    (hstop : q + n = arr.size ∨ (q + n < arr.size ∧ Ascii.isDigit arr[q + n]! = false ∧
      arr[q + n]! ≠ 46 ∧ Ascii.isExp arr[q + n]! = false))
    (hdecode : decodeNumberBytes? arr q (q + n) = some (Json.num m e)) :
    value.run arr q = .ok (Json.num m e) (q + n) := by
  have hqs : q < arr.size := by omega
  have hd! : Ascii.isDigit arr[q]! = true := by
    rcases hintstruct with ⟨_, h0⟩ | ⟨h19, _⟩
    · rw [h0]; decide
    · exact isDigit19_isDigit h19
  have hb : Ascii.isDigit arr[q] = true := by rwa [getElem!_pos arr q hqs] at hd!
  have hsign : (GParser.optional (GParser.ch '-')).run arr q = .ok none q :=
    optional_run_none _ arr q ⟨q, []⟩ (byte_run_fail! (Ascii.code '-') arr q hqs
      (by intro he; rw [show Ascii.code '-' = (45 : UInt8) from by decide] at he
          exact absurd (he ▸ hd! : Ascii.isDigit 45 = true) (by decide)))
  -- intPart consumes [q, q+ip), stopping at the '.'
  have hint : intPart.run arr q = .ok () (q + ip) := by
    rcases hintstruct with ⟨hip1, h0⟩ | ⟨h19, hds⟩
    · subst hip1; exact intPart_run_zero arr q hqs h0
    · refine intPart_run_nonzero arr q ip hqs hip h19 hds (Or.inr ⟨by omega, ?_⟩)
      rw [hdot]; decide
  -- frac consumes [q+ip, q+n)
  have hfr : frac.run arr (q + ip) = .ok (n - ip - 1) (q + n) := by
    have := frac_run arr (q + ip) (n - ip) (by omega) hdot (by omega)
      (by omega)
      (fun i hi1 hi2 => by
        have := hfrac (ip + i) (by omega) (by omega)
        rwa [show q + (ip + i) = q + ip + i from by omega] at this)
      (by rcases hstop with h | ⟨h1, h2, _, _⟩
          · exact Or.inl (by omega)
          · exact Or.inr ⟨by omega, by rwa [show q + ip + (n - ip) = q + n from by omega]⟩)
    rwa [show q + ip + (n - ip) = q + n from by omega] at this
  have hexp : (GParser.optional expo).run arr (q + n) = .ok none (q + n) := by
    refine optional_run_none _ _ _ ⟨q + n, []⟩ (seqR_run_fail_left _ _ arr (q + n) _ ?_)
    rcases hstop with h | ⟨h1, _, _, hexp'⟩
    · exact satisfy_run_end _ arr (q + n) (by omega)
    · exact satisfy_run_fail! _ arr (q + n) h1 hexp'
  have hnum : number.run arr q = .ok (Json.num m e) (q + n) := by
    simp only [number]
    refine label_run_ok "a number" _ arr q _ _ ?_
    exact captureWith?_run decodeNumberBytes? _ arr q () (q + n) (Json.num m e)
      (seqR_run _ _ arr q none q () (q + n) hsign
        (seqL_run _ _ arr q () (q + ip) none (q + n) hint
          (seqR_run _ _ arr (q + ip) (some (n - ip - 1)) (q + n) none (q + n)
            (optional_run_some frac arr (q + ip) (n - ip - 1) (q + n) hfr) hexp))) hdecode
  exact value_run_number arr q m e n hqs (Or.inl hb) hnum

/-- `value` parses a negative integer (`m < 0`, `e = 0`): a `-` sign then an integer part of
length `ip`. Dispatch routes `-` to `number` via the `dash` branch. -/
theorem value_run_num_int_neg (arr : ByteArray) (q : Nat) (m : Int) (_hm : m < 0) (ip : Nat)
    (hip : 1 ≤ ip) (hsize : q + 1 + ip ≤ arr.size) (hdash : arr[q]! = 45)
    (hstruct : (ip = 1 ∧ arr[q + 1]! = 48) ∨
      (Ascii.isDigit19 arr[q + 1]! = true ∧
        ∀ i, 1 ≤ i → i < ip → Ascii.isDigit arr[q + 1 + i]! = true))
    (hstop : q + 1 + ip = arr.size ∨ (q + 1 + ip < arr.size ∧
      Ascii.isDigit arr[q + 1 + ip]! = false ∧ arr[q + 1 + ip]! ≠ 46 ∧
      Ascii.isExp arr[q + 1 + ip]! = false))
    (hdecode : decodeNumberBytes? arr q (q + 1 + ip) = some (Json.num m 0)) :
    value.run arr q = .ok (Json.num m 0) (q + 1 + ip) := by
  have hqs : q < arr.size := by omega
  have hq1 : q + 1 < arr.size := by omega
  have hb : arr[q] = 45 := by rw [getElem!_pos arr q hqs] at hdash; exact hdash
  have hsign : (GParser.optional (GParser.ch '-')).run arr q = .ok (some ()) (q + 1) :=
    optional_run_some _ arr q () (q + 1)
      (byte_run! (Ascii.code '-') arr q hqs (by rw [hdash]; decide))
  have hint : intPart.run arr (q + 1) = .ok () (q + 1 + ip) := by
    rcases hstruct with ⟨hip1, h0⟩ | ⟨h19, hds⟩
    · subst hip1; exact intPart_run_zero arr (q + 1) hq1 h0
    · refine intPart_run_nonzero arr (q + 1) ip hq1 hip h19 hds ?_
      rcases hstop with h | ⟨h1, h2, _, _⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, h2⟩
  have hfrac : (GParser.optional frac).run arr (q + 1 + ip) = .ok none (q + 1 + ip) := by
    refine optional_run_none _ _ _ ⟨q + 1 + ip, []⟩ (seqR_run_fail_left _ _ arr (q + 1 + ip) _ ?_)
    rcases hstop with h | ⟨h1, _, hdot, _⟩
    · exact byte_run_end (Ascii.code '.') arr (q + 1 + ip) (by omega)
    · exact byte_run_fail! (Ascii.code '.') arr (q + 1 + ip) h1
        (by rwa [show Ascii.code '.' = (46 : UInt8) from by decide])
  have hexp : (GParser.optional expo).run arr (q + 1 + ip) = .ok none (q + 1 + ip) := by
    refine optional_run_none _ _ _ ⟨q + 1 + ip, []⟩ (seqR_run_fail_left _ _ arr (q + 1 + ip) _ ?_)
    rcases hstop with h | ⟨h1, _, _, hexp'⟩
    · exact satisfy_run_end _ arr (q + 1 + ip) (by omega)
    · exact satisfy_run_fail! _ arr (q + 1 + ip) h1 hexp'
  have hnum : number.run arr q = .ok (Json.num m 0) (q + 1 + ip) := by
    simp only [number]
    refine label_run_ok "a number" _ arr q _ _ ?_
    exact captureWith?_run decodeNumberBytes? _ arr q () (q + 1 + ip) (Json.num m 0)
      (seqR_run _ _ arr q (some ()) (q + 1) () (q + 1 + ip) hsign
        (seqL_run _ _ arr (q + 1) () (q + 1 + ip) none (q + 1 + ip) hint
          (seqR_run _ _ arr (q + 1 + ip) none (q + 1 + ip) none (q + 1 + ip) hfrac hexp)))
      hdecode
  rw [Nat.add_assoc] at hnum ⊢
  exact value_run_number arr q m 0 (1 + ip) hqs (Or.inr hb) hnum

/-- `value` parses a negative fractional number (`m < 0`, `e > 0`): `-`, integer part of length
`ip`, `.`, then a nonempty fractional part, total length `n`. -/
theorem value_run_num_frac_neg (arr : ByteArray) (q : Nat) (m : Int) (e ip n : Nat) (_hm : m < 0)
    (hip : 1 ≤ ip) (hn : ip + 3 ≤ n) (hsize : q + n ≤ arr.size) (hdash : arr[q]! = 45)
    (hintstruct : (ip = 1 ∧ arr[q + 1]! = 48) ∨
      (Ascii.isDigit19 arr[q + 1]! = true ∧
        ∀ i, 1 ≤ i → i < ip → Ascii.isDigit arr[q + 1 + i]! = true))
    (hdot : arr[q + 1 + ip]! = 46)
    (hfrac : ∀ i, ip + 2 ≤ i → i < n → Ascii.isDigit arr[q + i]! = true)
    (hstop : q + n = arr.size ∨ (q + n < arr.size ∧ Ascii.isDigit arr[q + n]! = false ∧
      arr[q + n]! ≠ 46 ∧ Ascii.isExp arr[q + n]! = false))
    (hdecode : decodeNumberBytes? arr q (q + n) = some (Json.num m e)) :
    value.run arr q = .ok (Json.num m e) (q + n) := by
  have hqs : q < arr.size := by omega
  have hq1 : q + 1 < arr.size := by omega
  have hb : arr[q] = 45 := by rw [getElem!_pos arr q hqs] at hdash; exact hdash
  have hsign : (GParser.optional (GParser.ch '-')).run arr q = .ok (some ()) (q + 1) :=
    optional_run_some _ arr q () (q + 1)
      (byte_run! (Ascii.code '-') arr q hqs (by rw [hdash]; decide))
  have hint : intPart.run arr (q + 1) = .ok () (q + 1 + ip) := by
    rcases hintstruct with ⟨hip1, h0⟩ | ⟨h19, hds⟩
    · subst hip1; exact intPart_run_zero arr (q + 1) hq1 h0
    · refine intPart_run_nonzero arr (q + 1) ip hq1 hip h19 hds (Or.inr ⟨by omega, ?_⟩)
      rw [hdot]; decide
  have hfr : frac.run arr (q + 1 + ip) = .ok (n - 1 - ip - 1) (q + n) := by
    have := frac_run arr (q + 1 + ip) (n - 1 - ip) (by omega) hdot (by omega) (by omega)
      (fun i hi1 hi2 => by
        have := hfrac (ip + 1 + i) (by omega) (by omega)
        rwa [show q + (ip + 1 + i) = q + 1 + ip + i from by omega] at this)
      (by rcases hstop with h | ⟨h1, h2, _, _⟩
          · exact Or.inl (by omega)
          · exact Or.inr ⟨by omega, by rwa [show q + 1 + ip + (n - 1 - ip) = q + n from by omega]⟩)
    rwa [show q + 1 + ip + (n - 1 - ip) = q + n from by omega] at this
  have hexp : (GParser.optional expo).run arr (q + n) = .ok none (q + n) := by
    refine optional_run_none _ _ _ ⟨q + n, []⟩ (seqR_run_fail_left _ _ arr (q + n) _ ?_)
    rcases hstop with h | ⟨h1, _, _, hexp'⟩
    · exact satisfy_run_end _ arr (q + n) (by omega)
    · exact satisfy_run_fail! _ arr (q + n) h1 hexp'
  have hnum : number.run arr q = .ok (Json.num m e) (q + n) := by
    simp only [number]
    refine label_run_ok "a number" _ arr q _ _ ?_
    exact captureWith?_run decodeNumberBytes? _ arr q () (q + n) (Json.num m e)
      (seqR_run _ _ arr q (some ()) (q + 1) () (q + n) hsign
        (seqL_run _ _ arr (q + 1) () (q + 1 + ip) none (q + n) hint
          (seqR_run _ _ arr (q + 1 + ip) (some (n - 1 - ip - 1)) (q + n) none (q + n)
            (optional_run_some frac arr (q + 1 + ip) (n - 1 - ip - 1) (q + n) hfr) hexp)))
      hdecode
  exact value_run_number arr q m e n hqs (Or.inr hb) hnum

/-- `value` parses the `null` keyword. -/
theorem value_run_null (arr : ByteArray) (q : Nat) (hq : q + 4 ≤ arr.size)
    (hm : ∀ j, j < 4 → arr[q + j]! = "null".toUTF8[j]!) :
    value.run arr q = .ok Json.null (q + 4) := by
  have hs : q < arr.size := by omega
  have hb : arr[q] = 110 := by
    have h0 := hm 0 (by norm_num)
    rw [Nat.add_zero, getElem!_pos arr q hs] at h0
    rw [h0]; decide
  have hstr : (GParser.string "null").run arr q = .ok () (q + 4) := by
    -- `simp` no longer computes `"null".utf8ByteSize` down to a numeral, so state it.
    have hlit : "null".utf8ByteSize = 4 := by decide
    have := string_run "null" arr q (by decide) (by simpa [hlit] using hq)
      (fun j hj => by have := hm j (by simpa [hlit] using hj); simpa using this)
    simpa [hlit] using this
  rw [value, fix_run_unroll]; simp only [valueBody]
  rw [wsDispatch_run_stop _ arr q hs (by rw [hb]; decide), hb]
  simp only [Ascii.lbrace, Ascii.lbracket, Ascii.quote]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos (by decide)]
  simp only [jnull, GParser.label, GParser.map, hstr]
  exact clampAdvance_ok arr q (by omega) (by omega)

/-- `value` parses the `true` keyword. -/
theorem value_run_true (arr : ByteArray) (q : Nat) (hq : q + 4 ≤ arr.size)
    (hm : ∀ j, j < 4 → arr[q + j]! = "true".toUTF8[j]!) :
    value.run arr q = .ok (Json.bool true) (q + 4) := by
  have hs : q < arr.size := by omega
  have hb : arr[q] = 116 := by
    have h0 := hm 0 (by norm_num); rw [Nat.add_zero, getElem!_pos arr q hs] at h0; rw [h0]; decide
  have hstr : (GParser.string "true").run arr q = .ok () (q + 4) := by
    -- `simp` no longer computes `"true".utf8ByteSize` down to a numeral, so state it.
    have hlit : "true".utf8ByteSize = 4 := by decide
    have := string_run "true" arr q (by decide) (by simpa [hlit] using hq)
      (fun j hj => by have := hm j (by simpa [hlit] using hj); simpa using this)
    simpa [hlit] using this
  rw [value, fix_run_unroll]; simp only [valueBody]
  rw [wsDispatch_run_stop _ arr q hs (by rw [hb]; decide), hb]
  simp only [Ascii.lbrace, Ascii.lbracket, Ascii.quote]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  simp only [jtrue, GParser.label, GParser.map, hstr]
  exact clampAdvance_ok arr q (by omega) (by omega)

/-- `value` parses the `false` keyword. -/
theorem value_run_false (arr : ByteArray) (q : Nat) (hq : q + 5 ≤ arr.size)
    (hm : ∀ j, j < 5 → arr[q + j]! = "false".toUTF8[j]!) :
    value.run arr q = .ok (Json.bool false) (q + 5) := by
  have hs : q < arr.size := by omega
  have hb : arr[q] = 102 := by
    have h0 := hm 0 (by norm_num); rw [Nat.add_zero, getElem!_pos arr q hs] at h0; rw [h0]; decide
  have hstr : (GParser.string "false").run arr q = .ok () (q + 5) := by
    -- `simp` no longer computes `"false".utf8ByteSize` down to a numeral, so state it.
    have hlit : "false".utf8ByteSize = 5 := by decide
    have := string_run "false" arr q (by decide) (by simpa [hlit] using hq)
      (fun j hj => by have := hm j (by simpa [hlit] using hj); simpa using this)
    simpa [hlit] using this
  rw [value, fix_run_unroll]; simp only [valueBody]
  rw [wsDispatch_run_stop _ arr q hs (by rw [hb]; decide), hb]
  simp only [Ascii.lbrace, Ascii.lbracket, Ascii.quote]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos (by decide)]
  simp only [jfalse, GParser.label, GParser.map, hstr]
  exact clampAdvance_ok arr q (by omega) (by omega)

open GripProps.ScanStr

/-- `jstr` on a rendered string: opening `"`, then `ebytes s.toList` body bytes, then closing
`"`. Returns `s` at the position after the closing quote. -/
theorem jstr_run (arr : ByteArray) (q : Nat) (s : String)
    (hbound : q + 1 + (ebytes s.toList).length < arr.size)
    (h34 : arr[q]! = 34)
    (hcontent : ∀ j, j < (ebytes s.toList).length →
        arr[q + 1 + j]! = (ebytes s.toList)[j]!)
    (hclose : arr[q + 1 + (ebytes s.toList).length]! = 34) :
    jstr.run arr q = .ok s (q + 1 + (ebytes s.toList).length + 1) := by
  set k := (ebytes s.toList).length
  have hqs : q < arr.size := by omega
  have hq34 : arr[q] = 34 := by rwa [getElem!_pos arr q hqs] at h34
  -- unfold jstr
  show (if _ : q < arr.size then
      (if arr[q] == 34 then scanStr arr q (q + 1) false else .error ⟨q, ["a string"]⟩)
    else .error ⟨q, ["a string"]⟩) = _
  rw [dif_pos hqs, if_pos (by simp [hq34])]
  -- apply scanStr_walk: body = escape s
  have hextract_eq : arr.extract (q + 1) (q + 1 + k) = (escape s).toUTF8 :=
    extract_eq_escape_toUTF8 arr q s (by omega) hcontent
  have hbody_eq : escape s =
      String.fromUTF8! (arr.extract (q + 1) (q + 1 + k)) := by
    rw [hextract_eq, fromUTF8!_toUTF8]
  have hvalid_eq : (arr.extract (q + 1) (q + 1 + k)).IsValidUTF8 := by
    rw [hextract_eq, String.toUTF8_eq_toByteArray]
    exact (escape s).isValidUTF8
  rw [scanStr_walk arr q (escape s) s.toList (q + 1) false
    (fun j hj => hcontent j hj)
    hclose
    (by omega) hbody_eq hvalid_eq]
  -- goal: .ok (if false || s.toList.any ... then unescape (escape s) else escape s) _ = .ok s _
  congr 1
  simp only [Bool.false_or]
  split_ifs with h
  · exact GripProps.Leaf.unescape_escape s
  · have hfalse : s.toList.any (fun c => !(escapeChar c == [c])) = false :=
      Bool.of_not_eq_true h
    have hall : ∀ c ∈ s.toList, escapeChar c = [c] := fun c hc => by
      have hec := List.any_eq_false.mp hfalse c hc
      have hec' : (escapeChar c == [c]) = true := by
        cases h : (escapeChar c == [c]) with
        | true => rfl
        | false => simp [h] at hec
      rwa [beq_iff_eq] at hec'
    have hfm : s.toList.flatMap escapeChar = s.toList := by
      have aux : ∀ l : List Char, (∀ c ∈ l, escapeChar c = [c]) →
          l.flatMap escapeChar = l := by
        intro l hl
        induction l with
        | nil => simp
        | cons c cs ih =>
          rw [List.flatMap_cons, hl c List.mem_cons_self,
              List.singleton_append]
          exact congrArg (c :: ·)
            (ih (fun c' hc' => hl c' (List.mem_cons_of_mem c hc')))
      exact aux s.toList hall
    simp only [escape]; rw [hfm]; exact String.ofList_toList

/-- `value` parses a string literal `s`. The array holds `"`, `ebytes s.toList`, `"` at `q`.
Dispatch routes byte 34 (Ascii.quote) to `jstring`, which wraps `jstr` in `Json.str`. -/
theorem value_run_str (arr : ByteArray) (q : Nat) (s : String)
    (hbound : q + 1 + (ebytes s.toList).length < arr.size)
    (h34 : arr[q]! = 34)
    (hcontent : ∀ j, j < (ebytes s.toList).length →
        arr[q + 1 + j]! = (ebytes s.toList)[j]!)
    (hclose : arr[q + 1 + (ebytes s.toList).length]! = 34) :
    value.run arr q = .ok (Json.str s) (q + 1 + (ebytes s.toList).length + 1) := by
  have hqs : q < arr.size := by omega
  have hq34 : arr[q] = 34 := by rwa [getElem!_pos arr q hqs] at h34
  have hws : Ascii.isWs arr[q] = false := by rw [hq34]; decide
  rw [value, fix_run_unroll]; simp only [valueBody]; rw [wsDispatch_run_stop _ arr q hqs hws, hq34]
  simp only [Ascii.lbrace, Ascii.lbracket, Ascii.quote]
  rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  simp only [jstring]
  rw [map_run_ok Json.str jstr arr q s _
    (jstr_run arr q s hbound h34 hcontent hclose)]
  exact clampAdvance_ok arr q (by omega) (by omega)

private theorem renderNumScientific_append (m : Int) (e : Nat) :
    renderNumScientific m e =
      (if m < 0 then "-" else "") ++ toString m.natAbs ++ "e-" ++ toString e := by
  by_cases hm : m < 0
  · apply String.ext
    simp [renderNumScientific, hm, String.toList_append,
      List.append_assoc, show ("-" : String).toList = ['-'] from by decide,
      show ("e-" : String).toList = ['e', '-'] from by decide]
  · apply String.ext
    simp [renderNumScientific, hm, String.toList_append,
      List.append_assoc, show ("e-" : String).toList = ['e', '-'] from by decide]

/-- The `expo` parser consumes a `e-<digits>` exponent: marker, mandatory `-` sign, then `ep`
digits, ending at a non-digit or end of input. -/
private theorem expo_run_scientific (arr : ByteArray) (q ep : Nat)
    (hq : q < arr.size) (hexp : Ascii.isExp arr[q]! = true)
    (hsign : arr[q + 1]! = 45) (hq1 : q + 1 < arr.size) (hep : 1 ≤ ep)
    (hdigits : ∀ i, i < ep → Ascii.isDigit arr[q + 2 + i]! = true)
    (hstop : q + 2 + ep = arr.size ∨
      (q + 2 + ep < arr.size ∧ Ascii.isDigit arr[q + 2 + ep]! = false)) :
    expo.run arr q = .ok ep (q + 2 + ep) := by
  have he : (GParser.satisfy Ascii.isExp).run arr q = .ok arr[q]! (q + 1) :=
    satisfy_run! _ arr q hq hexp
  have hs : (GParser.optional (GParser.satisfy Ascii.isSign)).run arr (q + 1) =
      .ok (some arr[q + 1]!) (q + 2) :=
    optional_run_some _ arr (q + 1) _ (q + 2)
      (satisfy_run! _ arr (q + 1) hq1 (by rw [hsign]; decide))
  have ht : (GParser.takeWhile1 Ascii.isDigit).run arr (q + 2) =
      .ok ep (q + 2 + ep) := by
    apply takeWhile1_run Ascii.isDigit arr (q + 2) ep (by omega) hep
    · intro i hi
      exact hdigits i hi
    · rcases hstop with h | ⟨h, hf⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, hf⟩
  simp only [expo]
  exact seqR_run _ _ arr q _ (q + 1) _ (q + 2 + ep) he
    (seqR_run _ _ arr (q + 1) _ (q + 2) ep (q + 2 + ep) hs ht)

/-- Byte view of a `pre ++ "e-" ++ post` string's UTF-8 encoding: the prefix bytes, then `e`
(101), `-` (45), then the suffix bytes. One home for the append-index arithmetic the
scientific-notation round-trips need. -/
private theorem eMinus_append_bytes (pre post : String) :
    (∀ i, i < pre.toUTF8.size → (pre ++ "e-" ++ post).toUTF8[i]! = pre.toUTF8[i]!) ∧
    (pre ++ "e-" ++ post).toUTF8[pre.toUTF8.size]! = 101 ∧
    (pre ++ "e-" ++ post).toUTF8[pre.toUTF8.size + 1]! = 45 ∧
    (∀ i, i < post.toUTF8.size →
      (pre ++ "e-" ++ post).toUTF8[pre.toUTF8.size + 2 + i]! = post.toUTF8[i]!) := by
  have hE : ("e-" : String).toUTF8.size = 2 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [toUTF8_append, toUTF8_append,
      ba_get!_append_left (by rw [ByteArray.size_append, hE]; omega),
      ba_get!_append_left hi]
  · rw [toUTF8_append, toUTF8_append,
      ba_get!_append_left (by rw [ByteArray.size_append, hE]; omega),
      ba_get!_append_right (Nat.le_refl _) (by rw [ByteArray.size_append, hE]; omega),
      Nat.sub_self]
    decide
  · rw [toUTF8_append, toUTF8_append,
      ba_get!_append_left (by rw [ByteArray.size_append, hE]; omega),
      ba_get!_append_right (by omega) (by rw [ByteArray.size_append, hE]; omega),
      show pre.toUTF8.size + 1 - pre.toUTF8.size = 1 from by omega]
    decide
  · intro i hi
    rw [toUTF8_append, toUTF8_append,
      ba_get!_append_right (by rw [ByteArray.size_append, hE]; omega)
        (by rw [ByteArray.size_append, ByteArray.size_append, hE]; omega),
      show pre.toUTF8.size + 2 + i - (pre.toUTF8 ++ ("e-" : String).toUTF8).size = i from by
        rw [ByteArray.size_append, hE]; omega]

/-- Byte view of a `"-" ++ s` string's UTF-8 encoding: `-` (45), then `s`'s bytes. -/
private theorem neg_prepend_bytes (s : String) :
    ("-" ++ s).toUTF8[0]! = 45 ∧
    (∀ i, i < s.toUTF8.size → ("-" ++ s).toUTF8[1 + i]! = s.toUTF8[i]!) := by
  refine ⟨?_, ?_⟩
  · rw [toUTF8_append, ba_get!_append_left (by decide)]
    decide
  · intro i hi
    rw [toUTF8_append,
      ba_get!_append_right (by rw [show ("-" : String).toUTF8.size = 1 from by decide]; omega)
        (by rw [ByteArray.size_append, show ("-" : String).toUTF8.size = 1 from by decide]; omega),
      show 1 + i - ("-" : String).toUTF8.size = i from by
        rw [show ("-" : String).toUTF8.size = 1 from by decide]; omega]

/-- Byte view of an `ip ++ "." ++ fp` string's UTF-8 encoding: the integer-part bytes, the `.`
(46) at `|ip|`, then the fractional-part bytes. -/
private theorem dot_append_bytes (ip fp : String) :
    (∀ i, i < ip.toUTF8.size → (ip ++ "." ++ fp).toUTF8[i]! = ip.toUTF8[i]!) ∧
    (ip ++ "." ++ fp).toUTF8[ip.toUTF8.size]! = 46 ∧
    (∀ i, i < fp.toUTF8.size →
      (ip ++ "." ++ fp).toUTF8[ip.toUTF8.size + 1 + i]! = fp.toUTF8[i]!) := by
  have hD : ("." : String).toUTF8.size = 1 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [toUTF8_append, toUTF8_append,
      ba_get!_append_left (by rw [ByteArray.size_append, hD]; omega),
      ba_get!_append_left hi]
  · rw [toUTF8_append, toUTF8_append,
      ba_get!_append_left (by rw [ByteArray.size_append, hD]; omega),
      ba_get!_append_right (Nat.le_refl _) (by rw [ByteArray.size_append, hD]; omega),
      Nat.sub_self]
    decide
  · intro i hi
    rw [toUTF8_append, toUTF8_append,
      ba_get!_append_right (by rw [ByteArray.size_append, hD]; omega)
        (by rw [ByteArray.size_append, ByteArray.size_append, hD]; omega),
      show ip.toUTF8.size + 1 + i - (ip.toUTF8 ++ ("." : String).toUTF8).size = i from by
        rw [ByteArray.size_append, hD]; omega]

/-- An element of a decimal-digit character list, viewed as a byte, is `Ascii.isDigit`. -/
private theorem isDigit_byte_of_mem {ds : List Char} {c : Char}
    (hds_dig : ∀ c ∈ ds, 48 ≤ c.toNat ∧ c.toNat ≤ 57) (hmem : c ∈ ds) :
    Ascii.isDigit (UInt8.ofNat c.toNat) = true := by
  have hbounds := hds_dig c hmem
  have hlt256 : c.toNat < 256 := Nat.lt_of_le_of_lt hbounds.2 (by decide)
  exact isDigit_of_toNat_bounds _
    (by rw [UInt8.toNat_ofNat_of_lt' hlt256]; exact hbounds.1)
    (by rw [UInt8.toNat_ofNat_of_lt' hlt256]; exact hbounds.2)

/-- `value` parses any occurrence of the scientific rendering `renderNumScientific m e` (used
for fractional exponents above `maxExp`) at offset `q`, consuming exactly the rendering. -/
theorem value_run_num_scientific (m : Int) (e : Nat) (buf : ByteArray) (q : Nat)
    (he : maxExp < e)
    (hq : q + (renderNumScientific m e).toUTF8.size ≤ buf.size)
    (hmatch : ∀ i, i < (renderNumScientific m e).toUTF8.size →
      buf[q + i]! = (renderNumScientific m e).toUTF8[i]!)
    (hstop : q + (renderNumScientific m e).toUTF8.size = buf.size ∨
      q + (renderNumScientific m e).toUTF8.size < buf.size ∧
        Ascii.isDigit buf[q + (renderNumScientific m e).toUTF8.size]! = false ∧
        buf[q + (renderNumScientific m e).toUTF8.size]! ≠ 46 ∧
        Ascii.isExp buf[q + (renderNumScientific m e).toUTF8.size]! = false) :
    value.run buf q = .ok (Json.num m e) (q + (renderNumScientific m e).toUTF8.size) := by
  have he_pos : 0 < e := by omega
  have hep_size : (toString e).toUTF8.size = (Nat.toDigits 10 e).length := by
    show (Nat.repr e).toUTF8.size = _
    exact repr_toUTF8_size e
  have hep : 1 ≤ (Nat.toDigits 10 e).length :=
    List.length_pos_of_ne_nil (GripProps.NatDigits.toDigits_nonempty e (by omega))
  by_cases hm : 0 ≤ m
  · set ip := (Nat.toDigits 10 m.natAbs).length
    set ep := (Nat.toDigits 10 e).length
    have hip : 1 ≤ ip := by
      rcases Nat.eq_zero_or_pos m.natAbs with hm0 | hmpos
      · have hzero : Nat.toDigits 10 0 = ['0'] := by decide
        simp [ip, hm0, hzero]
      · exact List.length_pos_of_ne_nil
          (GripProps.NatDigits.toDigits_nonempty m.natAbs hmpos)
    have hip_size : (toString m.natAbs).toUTF8.size = ip := by
      show (Nat.repr m.natAbs).toUTF8.size = _
      exact repr_toUTF8_size m.natAbs
    have hrender : renderNumScientific m e = toString m.natAbs ++ "e-" ++ toString e := by
      rw [renderNumScientific_append]
      simp [show ¬ m < 0 by omega]
    have hsize : (renderNumScientific m e).toUTF8.size = ip + 2 + ep := by
      rw [hrender, toUTF8_append, toUTF8_append, ByteArray.size_append,
        ByteArray.size_append, hip_size, hep_size,
        show ("e-" : String).toUTF8.size = 2 from by decide]
    have hdigits_rn : ∀ i, i < ip →
        (renderNumScientific m e).toUTF8[i]! = (toString m.natAbs).toUTF8[i]! := by
      intro i hi
      rw [hrender]
      exact (eMinus_append_bytes (toString m.natAbs) (toString e)).1 i (by rw [hip_size]; exact hi)
    have hexp_rn : (renderNumScientific m e).toUTF8[ip]! = 101 := by
      rw [hrender]
      have h := (eMinus_append_bytes (toString m.natAbs) (toString e)).2.1
      rwa [hip_size] at h
    have hsign_rn : (renderNumScientific m e).toUTF8[ip + 1]! = 45 := by
      rw [hrender]
      have h := (eMinus_append_bytes (toString m.natAbs) (toString e)).2.2.1
      rwa [hip_size] at h
    have hexp_digits_rn : ∀ i, i < ep →
        (renderNumScientific m e).toUTF8[ip + 2 + i]! = (toString e).toUTF8[i]! := by
      intro i hi
      rw [hrender]
      have h := (eMinus_append_bytes (toString m.natAbs) (toString e)).2.2.2 i
        (by rw [hep_size]; exact hi)
      rwa [hip_size] at h
    have hq' : q + ip + 2 + ep ≤ buf.size := by
      have := hq
      rw [hsize] at this
      omega
    have hstop' : q + ip + 2 + ep = buf.size ∨
        (q + ip + 2 + ep < buf.size ∧ Ascii.isDigit buf[q + ip + 2 + ep]! = false) := by
      have hs := hstop
      simp only [hsize] at hs
      rcases hs with h | ⟨h, hd, _, _⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, by simpa [Nat.add_assoc] using hd⟩
    have hmatch_digits : ∀ i, i < ip → buf[q + i]! = (toString m.natAbs).toUTF8[i]! := by
      intro i hi
      rw [hmatch i (by rw [hsize]; omega), hdigits_rn i hi]
    have hmatch_exp : ∀ i, i < ep →
        buf[q + ip + 2 + i]! = (toString e).toUTF8[i]! := by
      intro i hi
      have hh := hmatch (ip + 2 + i) (by rw [hsize]; omega)
      have hh' : buf[q + ip + 2 + i]! =
          (renderNumScientific m e).toUTF8[ip + 2 + i]! := by
        simpa [Nat.add_assoc] using hh
      rw [hh', hexp_digits_rn i hi]
    have hstart : Ascii.isDigit buf[q]! = true := by
      have h0 : buf[q]! = (renderNumScientific m e).toUTF8[0]! := by
        exact hmatch 0 (by rw [hsize]; omega)
      rcases Nat.eq_zero_or_pos m.natAbs with hm0 | hmpos
      · have hmz : m = 0 := Int.natAbs_eq_zero.mp hm0
        have hzero : Nat.toDigits 10 0 = ['0'] := by decide
        rw [h0, hdigits_rn 0 (by simp [ip, hm0, hzero]), hmz]
        decide
      · rw [h0, hdigits_rn 0 (by omega)]
        exact isDigit19_isDigit (by
          simpa using repr_toUTF8_head_isDigit19 m.natAbs hmpos)
    have hstruct : (ip = 1 ∧ buf[q]! = 48) ∨
        (Ascii.isDigit19 buf[q]! = true ∧
          ∀ i, 1 ≤ i → i < ip → Ascii.isDigit buf[q + i]! = true) := by
      rcases Nat.eq_zero_or_pos m.natAbs with hm0 | hmpos
      · left
        have hmz : m = 0 := Int.natAbs_eq_zero.mp hm0
        rw [hmz] at hrender
        refine ⟨?_, ?_⟩
        · have hzero : Nat.toDigits 10 0 = ['0'] := by decide
          simp [ip, hm0, hzero]
        · have hzero : Nat.toDigits 10 0 = ['0'] := by decide
          have h0 := hmatch_digits 0 (by simp [ip, hm0, hzero])
          -- `simp` no longer evaluates the digit literal, so state its byte.
          have hd0 : (Nat.repr 0).toByteArray[0]! = 48 := by decide
          simpa [hmz, hd0] using h0
      · right
        have h0 := hmatch_digits 0 (by omega)
        have h0' : buf[q]! = (toString m.natAbs).toUTF8[0]! := by simpa using h0
        exact ⟨by rw [h0']; exact repr_toUTF8_head_isDigit19 m.natAbs hmpos,
          fun i hi1 hi2 => by
            rw [hmatch_digits i hi2]
            exact repr_toUTF8_getElem_isDigit m.natAbs i (by simpa using hi2)⟩
    have hint : intPart.run buf q = .ok () (q + ip) := by
      rcases hstruct with ⟨hip1, h0⟩ | ⟨h19, hds⟩
      · simpa [hip1] using intPart_run_zero buf q (by omega) h0
      · refine intPart_run_nonzero buf q ip (by omega) hip h19 hds ?_
        have hh := hmatch ip (by rw [hsize]; omega)
        have hh' : buf[q + ip]! = (renderNumScientific m e).toUTF8[ip]! := by
          simpa [Nat.add_assoc] using hh
        exact Or.inr ⟨by omega, by rw [hh', hexp_rn]; decide⟩
    have hfrac : (GParser.optional frac).run buf (q + ip) = .ok none (q + ip) := by
      refine optional_run_none _ _ _ ⟨q + ip, []⟩ (seqR_run_fail_left _ _ _ _ _ ?_)
      exact byte_run_fail! (Ascii.code '.') buf (q + ip) (by omega)
        (by rw [hmatch ip (by rw [hsize]; omega), hexp_rn]; decide)
    have hexp : (GParser.optional expo).run buf (q + ip) =
        .ok (some ep) (q + ip + 2 + ep) := by
      apply optional_run_some
      apply expo_run_scientific buf (q + ip) ep (by omega)
        (by
          have hh := hmatch ip (by rw [hsize]; omega)
          rw [hh, hexp_rn]
          decide)
        (by
          have hh := hmatch (ip + 1) (by rw [hsize]; omega)
          have hh' : buf[q + ip + 1]! =
              (renderNumScientific m e).toUTF8[ip + 1]! := by
            simpa [Nat.add_assoc] using hh
          rw [hh', hsign_rn]) (by omega) hep
      · intro i hi
        rw [hmatch_exp i hi]
        exact repr_toUTF8_getElem_isDigit e i (by simpa using hi)
      · exact hstop'
    have hdecode : decodeNumberBytes? buf q (q + ip + 2 + ep) = some (Json.num m e) := by
      have h := GripProps.Number.decode_renderNumScientific_at buf q m e hq
        (fun i hi => hmatch i hi)
        (GripProps.Number.decode_renderNumScientific m e he_pos)
      rw [hsize] at h
      simpa only [Nat.add_assoc] using h
    have hsign : (GParser.optional (GParser.ch '-')).run buf q = .ok none q := by
      refine optional_run_none _ _ _ ⟨q, []⟩ (byte_run_fail! (Ascii.code '-') buf q (by omega) ?_)
      intro h
      have hbad := hstart
      rw [h, show Ascii.isDigit (Ascii.code '-') = false by decide] at hbad
      exact Bool.noConfusion hbad
    have hnum : number.run buf q = .ok (Json.num m e) (q + ip + 2 + ep) := by
      simp only [number]
      refine label_run_ok "a number" _ buf q _ _ ?_
      exact captureWith?_run decodeNumberBytes? _ buf q () (q + ip + 2 + ep) (Json.num m e)
        (seqR_run _ _ buf q none q () (q + ip + 2 + ep)
          hsign
          (seqL_run _ _ buf q () (q + ip) (some ep) (q + ip + 2 + ep) hint
            (seqR_run _ _ buf (q + ip) none (q + ip) (some ep) (q + ip + 2 + ep)
              hfrac hexp))) hdecode
    have hstart' : Ascii.isDigit buf[q] = true := by
      rwa [getElem!_pos buf q (by omega)] at hstart
    have hnum' : number.run buf q = .ok (Json.num m e) (q + (ip + 2 + ep)) := by
      simpa [Nat.add_assoc] using hnum
    rw [hsize]
    exact value_run_number buf q m e (ip + 2 + ep) (by omega) (Or.inl hstart') hnum'
  · push_neg at hm
    set ip := (Nat.toDigits 10 m.natAbs).length
    set ep := (Nat.toDigits 10 e).length
    have hip_size : (toString m.natAbs).toUTF8.size = ip := by
      show (Nat.repr m.natAbs).toUTF8.size = _
      exact repr_toUTF8_size m.natAbs
    have hrender : renderNumScientific m e = ("-" ++ toString m.natAbs) ++ "e-" ++ toString e := by
      rw [renderNumScientific_append]
      simp [hm]
    have hip : 1 ≤ ip := by
      exact List.length_pos_of_ne_nil
        (GripProps.NatDigits.toDigits_nonempty m.natAbs (Int.natAbs_pos.mpr (by omega)))
    have hpre_size : ("-" ++ toString m.natAbs).toUTF8.size = 1 + ip := by
      rw [toUTF8_append, ByteArray.size_append, hip_size,
        show ("-" : String).toUTF8.size = 1 from by decide]
    have hsize : (renderNumScientific m e).toUTF8.size = 1 + ip + 2 + ep := by
      rw [hrender, toUTF8_append, toUTF8_append,
        ByteArray.size_append, ByteArray.size_append, hpre_size, hep_size,
        show ("e-" : String).toUTF8.size = 2 from by decide]
    have hdash_rn : (renderNumScientific m e).toUTF8[0]! = 45 := by
      rw [hrender, (eMinus_append_bytes ("-" ++ toString m.natAbs) (toString e)).1 0
        (by rw [hpre_size]; omega), (neg_prepend_bytes _).1]
    have hdigits_rn : ∀ i, i < ip →
        (renderNumScientific m e).toUTF8[1 + i]! = (toString m.natAbs).toUTF8[i]! := by
      intro i hi
      rw [hrender, (eMinus_append_bytes ("-" ++ toString m.natAbs) (toString e)).1 (1 + i)
        (by rw [hpre_size]; omega), (neg_prepend_bytes _).2 i (by rw [hip_size]; exact hi)]
    have hexp_rn : (renderNumScientific m e).toUTF8[1 + ip]! = 101 := by
      rw [hrender]
      have h := (eMinus_append_bytes ("-" ++ toString m.natAbs) (toString e)).2.1
      rwa [hpre_size] at h
    have hsign_rn : (renderNumScientific m e).toUTF8[1 + ip + 1]! = 45 := by
      rw [hrender]
      have h := (eMinus_append_bytes ("-" ++ toString m.natAbs) (toString e)).2.2.1
      rwa [hpre_size] at h
    have hexp_digits_rn : ∀ i, i < ep →
        (renderNumScientific m e).toUTF8[1 + ip + 2 + i]! = (toString e).toUTF8[i]! := by
      intro i hi
      rw [hrender]
      have h := (eMinus_append_bytes ("-" ++ toString m.natAbs) (toString e)).2.2.2 i
        (by rw [hep_size]; exact hi)
      rwa [hpre_size] at h
    have hq' : q + 1 + ip + 2 + ep ≤ buf.size := by
      have := hq
      rw [hsize] at this
      omega
    have hstop' : q + 1 + ip + 2 + ep = buf.size ∨
        (q + 1 + ip + 2 + ep < buf.size ∧ Ascii.isDigit buf[q + 1 + ip + 2 + ep]! = false) := by
      have hs := hstop
      simp only [hsize] at hs
      rcases hs with h | ⟨h, hd, _, _⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, by simpa [Nat.add_assoc] using hd⟩
    have hmatch_digits : ∀ i, i < ip →
        buf[q + 1 + i]! = (toString m.natAbs).toUTF8[i]! := by
      intro i hi
      have hh := hmatch (1 + i) (by rw [hsize]; omega)
      have hh' : buf[q + 1 + i]! = (renderNumScientific m e).toUTF8[1 + i]! := by
        simpa [Nat.add_assoc] using hh
      rw [hh', hdigits_rn i hi]
    have hmatch_exp : ∀ i, i < ep →
        buf[q + 1 + ip + 2 + i]! = (toString e).toUTF8[i]! := by
      intro i hi
      have hh := hmatch (1 + ip + 2 + i) (by rw [hsize]; omega)
      have hh' : buf[q + 1 + ip + 2 + i]! =
          (renderNumScientific m e).toUTF8[1 + ip + 2 + i]! := by
        simpa [Nat.add_assoc] using hh
      rw [hh', hexp_digits_rn i hi]
    have hstart : buf[q] = Ascii.dash := by
      have hh := hmatch 0 (by rw [hsize]; omega)
      rw [show q + 0 = q from rfl, getElem!_pos buf q (by omega)] at hh
      rw [hh, hdash_rn]
      decide
    have hstruct : (ip = 1 ∧ buf[q + 1]! = 48) ∨
        (Ascii.isDigit19 buf[q + 1]! = true ∧
          ∀ i, 1 ≤ i → i < ip → Ascii.isDigit buf[q + 1 + i]! = true) := by
      rcases Nat.eq_zero_or_pos m.natAbs with hm0 | hmpos
      · left
        have hmz : m = 0 := Int.natAbs_eq_zero.mp hm0
        refine ⟨?_, ?_⟩
        · have hzero : Nat.toDigits 10 0 = ['0'] := by decide
          simp [ip, hm0, hzero]
        · have hzero : Nat.toDigits 10 0 = ['0'] := by decide
          have h0 := hmatch_digits 0 (by simp [ip, hm0, hzero])
          -- `simp` no longer evaluates the digit literal, so state its byte.
          have hd0 : (Nat.repr 0).toByteArray[0]! = 48 := by decide
          simpa [hmz, hd0] using h0
      · right
        have hh := hmatch_digits 0 (by omega)
        have hh' : buf[q + 1]! = (toString m.natAbs).toUTF8[0]! := by simpa using hh
        exact ⟨by rw [hh']; exact repr_toUTF8_head_isDigit19 m.natAbs hmpos,
          fun i hi1 hi2 => by
            rw [hmatch_digits i hi2]
            exact repr_toUTF8_getElem_isDigit m.natAbs i (by simpa using hi2)⟩
    have hint : intPart.run buf (q + 1) = .ok () (q + 1 + ip) := by
      rcases hstruct with ⟨hip1, h0⟩ | ⟨h19, hds⟩
      · simpa [hip1] using intPart_run_zero buf (q + 1) (by omega) h0
      · refine intPart_run_nonzero buf (q + 1) ip (by omega) hip h19 hds ?_
        have hh := hmatch (1 + ip) (by rw [hsize]; omega)
        have hh' : buf[q + 1 + ip]! = (renderNumScientific m e).toUTF8[1 + ip]! := by
          simpa [Nat.add_assoc] using hh
        exact Or.inr ⟨by omega, by rw [hh', hexp_rn]; decide⟩
    have hfrac : (GParser.optional frac).run buf (q + 1 + ip) = .ok none (q + 1 + ip) := by
      refine optional_run_none _ _ _ ⟨q + 1 + ip, []⟩ (seqR_run_fail_left _ _ _ _ _ ?_)
      exact byte_run_fail! (Ascii.code '.') buf (q + 1 + ip) (by omega)
        (by
          have hh := hmatch (1 + ip) (by rw [hsize]; omega)
          have hh' : buf[q + 1 + ip]! = (renderNumScientific m e).toUTF8[1 + ip]! := by
            simpa [Nat.add_assoc] using hh
          rw [hh', hexp_rn]
          decide)
    have hexp : (GParser.optional expo).run buf (q + 1 + ip) =
        .ok (some ep) (q + 1 + ip + 2 + ep) := by
      apply optional_run_some
      apply expo_run_scientific buf (q + 1 + ip) ep (by omega)
        (by
          have hh := hmatch (1 + ip) (by rw [hsize]; omega)
          have hh' : buf[q + 1 + ip]! = (renderNumScientific m e).toUTF8[1 + ip]! := by
            simpa [Nat.add_assoc] using hh
          rw [hh', hexp_rn]
          decide)
        (by
          have hh := hmatch (1 + ip + 1) (by rw [hsize]; omega)
          have hh' : buf[q + 1 + ip + 1]! =
              (renderNumScientific m e).toUTF8[1 + ip + 1]! := by
            simpa [Nat.add_assoc] using hh
          rw [hh', hsign_rn]) (by omega) hep
      · intro i hi
        rw [hmatch_exp i hi]
        exact repr_toUTF8_getElem_isDigit e i (by simpa using hi)
      · exact hstop'
    have hdecode : decodeNumberBytes? buf q (q + 1 + ip + 2 + ep) = some (Json.num m e) := by
      have h := GripProps.Number.decode_renderNumScientific_at buf q m e hq
        (fun i hi => hmatch i hi)
        (GripProps.Number.decode_renderNumScientific m e he_pos)
      rw [hsize] at h
      simpa [Nat.add_assoc] using h
    have hnum : number.run buf q = .ok (Json.num m e) (q + 1 + ip + 2 + ep) := by
      simp only [number]
      refine label_run_ok "a number" _ buf q _ _ ?_
      exact captureWith?_run decodeNumberBytes? _ buf q () (q + 1 + ip + 2 + ep) (Json.num m e)
        (seqR_run _ _ buf q (some ()) (q + 1) () (q + 1 + ip + 2 + ep)
          (optional_run_some _ buf q () (q + 1)
            (byte_run! (Ascii.code '-') buf q (by omega) (by
              have hstart! : buf[q]! = Ascii.code '-' := by
                rw [getElem!_pos buf q (by omega)]
                simpa [show Ascii.dash = Ascii.code '-' from by decide] using hstart
              exact hstart!)))
          (seqL_run _ _ buf (q + 1) () (q + 1 + ip) (some ep) (q + 1 + ip + 2 + ep) hint
            (seqR_run _ _ buf (q + 1 + ip) none (q + 1 + ip) (some ep) (q + 1 + ip + 2 + ep)
              hfrac hexp))) hdecode
    have hnum' : number.run buf q = .ok (Json.num m e) (q + (1 + (ip + 2 + ep))) := by
      simpa [Nat.add_assoc] using hnum
    have hv := value_run_number buf q m e (1 + (ip + 2 + ep)) (by omega)
      (Or.inr hstart) hnum'
    rw [hsize]
    simpa [Nat.add_assoc] using hv

/-- `value` parses any occurrence of the expanded decimal rendering `renderNum m e` at offset
`q`: dispatch and the number grammar consume exactly the rendering. The `hstop` byte after it
must be a delimiter (not a digit, `.`, or `e`) so the optional fraction/exponent parsers fail. -/
theorem value_run_num_at (m : Int) (e : Nat) (buf : ByteArray) (q : Nat)
    (hq : q + (renderNum m e).toUTF8.size ≤ buf.size)
    (hmatch : ∀ i, i < (renderNum m e).toUTF8.size → buf[q + i]! = (renderNum m e).toUTF8[i]!)
    (hstop : q + (renderNum m e).toUTF8.size = buf.size ∨
             q + (renderNum m e).toUTF8.size < buf.size ∧
               Ascii.isDigit buf[q + (renderNum m e).toUTF8.size]! = false ∧
               buf[q + (renderNum m e).toUTF8.size]! ≠ 46 ∧
               Ascii.isExp buf[q + (renderNum m e).toUTF8.size]! = false) :
    Grip.Json.value.run buf q = .ok (Json.num m e) (q + (renderNum m e).toUTF8.size) := by
  by_cases he : e = 0
  · subst he
    by_cases hm : 0 ≤ m
    · -- e = 0, m ≥ 0 (non-negative integer)
      have hrn : renderNum m 0 = Nat.repr m.natAbs := by
        have h : renderNum m 0 = toString m.natAbs := by
          unfold renderNum; rw [if_neg (show ¬ m < 0 from by omega)]; simp
        exact h
      have hsize_eq : (renderNum m 0).toUTF8.size = (Nat.toDigits 10 m.natAbs).length := by
        rw [hrn]; exact repr_toUTF8_size m.natAbs
      have hn : 1 ≤ (renderNum m 0).toUTF8.size := by
        rw [hsize_eq]
        rcases Nat.eq_zero_or_pos m.natAbs with hm0 | hm_pos
        · rw [show Nat.toDigits 10 m.natAbs = ['0'] from by rw [hm0]; decide]; decide
        · exact List.length_pos_of_ne_nil (GripProps.NatDigits.toDigits_nonempty m.natAbs hm_pos)
      have hmatch0 : buf[q]! = (renderNum m 0).toUTF8[0]! := by
        have h := hmatch 0 (by omega); simpa using h
      have hstruct : ((renderNum m 0).toUTF8.size = 1 ∧ buf[q]! = 48) ∨
          (Ascii.isDigit19 buf[q]! = true ∧
           ∀ i, 1 ≤ i → i < (renderNum m 0).toUTF8.size → Ascii.isDigit buf[q + i]! = true) := by
        rcases Nat.eq_zero_or_pos m.natAbs with hm0 | hm_pos
        · have hrn0 : renderNum m 0 = "0" := by
            have hm_zero : m = 0 := Int.natAbs_eq_zero.mp hm0; rw [hm_zero]; decide
          exact Or.inl ⟨by rw [hrn0]; decide, by rw [hmatch0, hrn0]; decide⟩
        · exact Or.inr ⟨by
              rw [hmatch0, hrn]; exact repr_toUTF8_head_isDigit19 m.natAbs hm_pos,
            fun i _ h2i => by
              rw [hmatch i h2i, hrn]
              exact repr_toUTF8_getElem_isDigit m.natAbs i (by rw [← hsize_eq]; exact h2i)⟩
      have hdec :
          decodeNumberBytes? buf q (q + (renderNum m 0).toUTF8.size) = some (Json.num m 0) :=
        GripProps.Number.decode_renderNum_at buf q m 0 hq hmatch
          (GripProps.Number.decode_renderNum_int m hm)
      exact value_run_num_int buf q m hm _ hn hq hstruct hstop hdec
    · -- e = 0, m < 0: negative integer
      push_neg at hm
      have hrn : renderNum m 0 = "-" ++ toString m.natAbs := by
        unfold renderNum; simp [if_pos (show m < 0 from hm)]
      set ip := (Nat.toDigits 10 m.natAbs).length with hip_def
      have hipa : (toString m.natAbs).toUTF8.size = ip :=
        show (Nat.repr m.natAbs).toUTF8.size = _ from repr_toUTF8_size m.natAbs
      have hsize : (renderNum m 0).toUTF8.size = 1 + ip := by
        rw [hrn, toUTF8_append, ByteArray.size_append,
            show ("-" : String).toUTF8.size = 1 from by decide, hipa]
      have hip : 1 ≤ ip :=
        Nat.succ_le_of_lt (List.length_pos_of_ne_nil
          (GripProps.NatDigits.toDigits_nonempty m.natAbs (Int.natAbs_pos.mpr (by omega))))
      have hq' : q + 1 + ip ≤ buf.size := by linarith [hsize ▸ hq]
      have hstop' : q + 1 + ip = buf.size ∨ (q + 1 + ip < buf.size ∧
          Ascii.isDigit buf[q + 1 + ip]! = false ∧ buf[q + 1 + ip]! ≠ 46 ∧
          Ascii.isExp buf[q + 1 + ip]! = false) := by
        have h := hsize ▸ hstop
        rcases h with h | ⟨h1, h2, h3, h4⟩
        · exact Or.inl (by omega)
        · exact Or.inr ⟨by omega,
            by rwa [show q + (1 + ip) = q + 1 + ip from by omega] at h2,
            by rwa [show q + (1 + ip) = q + 1 + ip from by omega] at h3,
            by rwa [show q + (1 + ip) = q + 1 + ip from by omega] at h4⟩
      have hdash_buf : buf[q]! = 45 := by
        have h := hmatch 0 (hsize ▸ by omega); simp only [Nat.add_zero] at h
        rw [h, hrn, toUTF8_append, ba_get!_append_left (by decide)]; decide
      have hstruct_rn : (ip = 1 ∧ (renderNum m 0).toUTF8[1]! = 48) ∨
          (Ascii.isDigit19 (renderNum m 0).toUTF8[1]! = true ∧
           ∀ i, 1 ≤ i → i < ip → Ascii.isDigit (renderNum m 0).toUTF8[1 + i]! = true) := by
        rw [hrn]
        have hsplit :
            (("-" ++ toString m.natAbs) : String).toUTF8 =
              "-".toUTF8 ++ (toString m.natAbs).toUTF8 :=
          toUTF8_append _ _
        have hdash_size : ("-" : String).toUTF8.size = 1 := by decide
        rcases Nat.eq_zero_or_pos m.natAbs with hm0 | hm_pos
        · have h0 : Nat.toDigits 10 m.natAbs = ['0'] := by rw [hm0]; decide
          have hip0 : ip = 1 := by change (Nat.toDigits 10 m.natAbs).length = 1; rw [h0]; decide
          exact Or.inl ⟨hip0, by
            rw [hsplit, ba_get!_append_right (by decide)
                (by rw [ByteArray.size_append, hdash_size, hipa, hip0]; omega),
                show (1 : Nat) - "-".toUTF8.size = 0 from by rw [hdash_size],
                show (toString m.natAbs).toUTF8[0]! = (Nat.repr m.natAbs).toUTF8[0]! from rfl,
                repr_toUTF8_getElem! m.natAbs 0 (by rw [h0]; decide), h0]; decide⟩
        · exact Or.inr ⟨by
              rw [hsplit, ba_get!_append_right (by decide)
                  (by rw [ByteArray.size_append, hdash_size, hipa]; omega),
                  show (1 : Nat) - "-".toUTF8.size = 0 from by rw [hdash_size],
                  show (toString m.natAbs).toUTF8[0]! = (Nat.repr m.natAbs).toUTF8[0]! from rfl]
              exact repr_toUTF8_head_isDigit19 m.natAbs hm_pos,
            fun i _ hi2 => by
              rw [show 1 + i = 0 + 1 + i from by omega, hsplit,
                  ba_get!_append_right (by rw [hdash_size]; omega)
                    (by rw [ByteArray.size_append, hdash_size, hipa]; omega),
                  show 0 + 1 + i - "-".toUTF8.size = i from by rw [hdash_size]; omega,
                  show (toString m.natAbs).toUTF8[i]! = (Nat.repr m.natAbs).toUTF8[i]! from rfl]
              exact repr_toUTF8_getElem_isDigit m.natAbs i hi2⟩
      have hstruct_buf : (ip = 1 ∧ buf[q + 1]! = 48) ∨
          (Ascii.isDigit19 buf[q + 1]! = true ∧
           ∀ i, 1 ≤ i → i < ip → Ascii.isDigit buf[q + 1 + i]! = true) := by
        have hm1 : ∀ j, j < 1 + ip → buf[q + j]! = (renderNum m 0).toUTF8[j]! := fun j hj =>
          hmatch j (hsize ▸ hj)
        rcases hstruct_rn with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, by rw [hm1 1 (by omega)]; exact h2⟩
        · exact Or.inr ⟨by rw [hm1 1 (by omega)]; exact h1,
            fun i h1i h2i => by
              rw [show q + 1 + i = q + (1 + i) from by omega, hm1 (1 + i) (by omega)]
              exact h2 i h1i h2i⟩
      have hdec : decodeNumberBytes? buf q (q + 1 + ip) = some (Json.num m 0) := by
        have h := GripProps.Number.decode_renderNum_at buf q m 0 hq hmatch
          (GripProps.Number.decode_renderNum_int_neg m hm)
        simp only [hsize, show q + (1 + ip) = q + 1 + ip from by omega] at h
        exact h
      rw [show q + (renderNum m 0).toUTF8.size = q + 1 + ip from by rw [hsize]; omega]
      exact value_run_num_int_neg buf q m hm ip hip hq' hdash_buf hstruct_buf hstop' hdec
  · -- e > 0: fractional number
    have he_pos : 0 < e := by push_neg at he; omega
    by_cases hm : 0 ≤ m
    · -- e > 0, m ≥ 0: non-negative fractional
      set len := (toString m.natAbs).length with hlen_def
      set ds := List.replicate (e + 1 - len) '0' ++ (toString m.natAbs).toList with hds_def
      set k := ds.length - e with hk_def
      have hds_dig : ∀ c ∈ ds, 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
        intro c hc
        rcases List.mem_append.mp hc with h | h
        · rw [List.eq_of_mem_replicate h]; decide
        · have htl : (toString m.natAbs).toList = Nat.toDigits 10 m.natAbs := by
            show (Nat.repr m.natAbs).toList = _; rw [Nat.repr, String.toList_ofList]
          exact GripProps.NatDigits.mem_toDigits_bound m.natAbs c (htl ▸ h)
      have hlen_pos : 1 ≤ len := by
        rw [hlen_def]
        have hll : (toString m.natAbs).length = (Nat.toDigits 10 m.natAbs).length := by
          show (Nat.repr m.natAbs).length = _; rw [Nat.repr, String.length_ofList]
        rw [hll]
        rcases Nat.eq_zero_or_pos m.natAbs with h0 | hpos
        · have : Nat.toDigits 10 m.natAbs = ['0'] := by rw [h0]; decide
          rw [this]; decide
        · exact List.length_pos_of_ne_nil (GripProps.NatDigits.toDigits_nonempty m.natAbs hpos)
      have hdslen : e + 1 ≤ ds.length := by
        have hlenL : (toString m.natAbs).toList.length = len := by
          have htl : (toString m.natAbs).toList = Nat.toDigits 10 m.natAbs := by
            show (Nat.repr m.natAbs).toList = _; rw [Nat.repr, String.toList_ofList]
          have hll : (Nat.toDigits 10 m.natAbs).length = len := by
            rw [hlen_def]; show (Nat.toDigits 10 m.natAbs).length = (Nat.repr m.natAbs).length
            rw [Nat.repr, String.length_ofList]
          rw [htl, hll]
        rw [hds_def, List.length_append, List.length_replicate, hlenL]; omega
      have hk_pos : 1 ≤ k := by rw [hk_def]; omega
      have hfrac_len : (ds.drop k).length = e := by rw [List.length_drop, hk_def]; omega
      have hrn_str : renderNum m e =
          String.ofList (ds.take k) ++ "." ++ String.ofList (ds.drop k) := by
        unfold renderNum
        simp only [show (e == 0) = false from by simp [he_pos.ne'], Bool.false_eq_true,
          if_false, if_neg (show ¬ m < 0 from by omega), String.empty_append]
        rfl
      have hint_size : (String.ofList (ds.take k)).toUTF8.size = k := by
        rw [ofList_ascii_toUTF8_size _ (fun c hc => by
              have := hds_dig c (List.mem_of_mem_take hc); omega),
            List.length_take, Nat.min_eq_left (by omega)]
      have hfrac_str_size : (String.ofList (ds.drop k)).toUTF8.size = e := by
        rw [ofList_ascii_toUTF8_size _ (fun c hc => by
              have := hds_dig c (List.mem_of_mem_drop hc); omega), hfrac_len]
      have harr_size : (renderNum m e).toUTF8.size = k + 1 + e := by
        rw [hrn_str, toUTF8_append, toUTF8_append,
            ByteArray.size_append, ByteArray.size_append, hint_size, hfrac_str_size,
            show (".":String).toUTF8.size = 1 from by decide]
      -- hintstruct_rn about (renderNum m e).toUTF8
      have hintstruct_rn :
          (k = 1 ∧ (renderNum m e).toUTF8[0]! = 48) ∨
          (Ascii.isDigit19 (renderNum m e).toUTF8[0]! = true ∧
           ∀ i, 1 ≤ i → i < k → Ascii.isDigit (renderNum m e).toUTF8[0 + i]! = true) := by
        rcases Nat.eq_zero_or_pos (e + 1 - len) with hpads0 | hpads_pos
        · have hna_pos : 0 < m.natAbs := by
            rcases Nat.eq_zero_or_pos m.natAbs with h0 | hpos
            · have : len = 1 := by rw [hlen_def, h0]; show (Nat.repr 0).length = 1; decide
              omega
            · exact hpos
          have htl : (toString m.natAbs).toList = Nat.toDigits 10 m.natAbs := by
            show (Nat.repr m.natAbs).toList = _; rw [Nat.repr, String.toList_ofList]
          have hne : Nat.toDigits 10 m.natAbs ≠ [] :=
            GripProps.NatDigits.toDigits_nonempty m.natAbs hna_pos
          have hbounds0 := GripProps.NatDigits.toDigits_head_pos m.natAbs hna_pos
          have hlt256_0 : (Nat.toDigits 10 m.natAbs).head!.toNat < 256 := by omega
          have hds_eq : ds = Nat.toDigits 10 m.natAbs := by simp [hds_def, hpads0, htl]
          have hh : 0 < (ds.take k).length := by
            rw [List.length_take, Nat.min_eq_left (by omega)]; omega
          have harr0 : (renderNum m e).toUTF8[0]! =
              UInt8.ofNat (Nat.toDigits 10 m.natAbs).head!.toNat := by
            rw [hrn_str,
              (dot_append_bytes (String.ofList (ds.take k)) (String.ofList (ds.drop k))).1 0
                (by rw [hint_size]; omega),
              ofList_ascii_toUTF8_getElem! (ds.take k) 0 (fun c hc => by
                have := hds_dig c (List.mem_of_mem_take hc); omega) hh]
            congr 1
            rw [getElem!_pos (ds.take k) 0 hh, List.getElem_take,
              ← getElem!_pos ds 0 (by omega), hds_eq]
            match Nat.toDigits 10 m.natAbs, hne with | d :: _, _ => rfl
          exact Or.inr ⟨by
            rw [harr0]
            exact isDigit19_of_toNat_bounds _
              (by rw [UInt8.toNat_ofNat_of_lt' hlt256_0]; exact hbounds0.1)
              (by rw [UInt8.toNat_ofNat_of_lt' hlt256_0]; exact hbounds0.2),
            fun i h1i h2i => by
              rw [Nat.zero_add, hrn_str,
                (dot_append_bytes (String.ofList (ds.take k)) (String.ofList (ds.drop k))).1 i
                  (by rw [hint_size]; omega)]
              have h_lt : i < (ds.take k).length := by
                rw [List.length_take, Nat.min_eq_left (by omega)]; omega
              rw [ofList_ascii_toUTF8_getElem! (ds.take k) i (fun c hc => by
                    have := hds_dig c (List.mem_of_mem_take hc); omega) h_lt]
              exact isDigit_byte_of_mem hds_dig (by
                rw [getElem!_pos _ i h_lt]
                exact List.mem_of_mem_take (List.getElem_mem h_lt))⟩
        · have hk1 : k = 1 := by
            have hlenL : (toString m.natAbs).toList.length = len := by
              have htl : (toString m.natAbs).toList = Nat.toDigits 10 m.natAbs := by
                show (Nat.repr m.natAbs).toList = _; rw [Nat.repr, String.toList_ofList]
              have hll : (Nat.toDigits 10 m.natAbs).length = len := by
                rw [hlen_def]; show (Nat.toDigits 10 m.natAbs).length = (Nat.repr m.natAbs).length
                rw [Nat.repr, String.length_ofList]
              rw [htl, hll]
            rw [hk_def, hds_def, List.length_append, List.length_replicate, hlenL]; omega
          have htake1 : ds.take 1 = ['0'] := by
            rw [hds_def, List.take_append_of_le_length (by rw [List.length_replicate]; omega),
                List.take_replicate, Nat.min_eq_left (by omega)]; simp
          exact Or.inl ⟨hk1, by
            have h0size : (String.ofList ['0']).toUTF8.size = 1 :=
              ofList_ascii_toUTF8_size _ (fun c hc => by cases (List.mem_singleton.mp hc); decide)
            rw [hrn_str, hk1, htake1, toUTF8_append, toUTF8_append,
                ba_get!_append_left (by rw [ByteArray.size_append, h0size,
                  show (".":String).toUTF8.size = 1 from by decide]; omega),
                ba_get!_append_left (by rw [h0size]; omega)]; decide⟩
      -- hdot_rn: dot at position k
      have hdot_rn : (renderNum m e).toUTF8[k]! = 46 := by
        rw [hrn_str]
        have h := (dot_append_bytes (String.ofList (ds.take k)) (String.ofList (ds.drop k))).2.1
        rwa [hint_size] at h
      -- hfrac_rn: frac digits
      have hfrac_rn : ∀ i, k + 1 ≤ i → i < k + 1 + e →
          Ascii.isDigit (renderNum m e).toUTF8[0 + i]! = true := by
        intro i h1i h2i
        rw [Nat.zero_add, hrn_str]
        have h := (dot_append_bytes (String.ofList (ds.take k)) (String.ofList (ds.drop k))).2.2
          (i - k - 1) (by rw [hfrac_str_size]; omega)
        rw [hint_size, show k + 1 + (i - k - 1) = i from by omega] at h
        rw [h, ofList_ascii_toUTF8_getElem! _ (i - k - 1) (fun c hc => by
              have := hds_dig c (List.mem_of_mem_drop hc); omega) (by rw [hfrac_len]; omega)]
        exact isDigit_byte_of_mem hds_dig (by
          rw [getElem!_pos (ds.drop k) (i - k - 1) (by rw [hfrac_len]; omega)]
          exact List.mem_of_mem_drop (List.getElem_mem (by rw [hfrac_len]; omega)))
      -- transfer to buf
      have hintstruct_buf : (k = 1 ∧ buf[q]! = 48) ∨
          (Ascii.isDigit19 buf[q]! = true ∧
           ∀ i, 1 ≤ i → i < k → Ascii.isDigit buf[q + i]! = true) := by
        rcases hintstruct_rn with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hq0 := hmatch 0 (by rw [harr_size]; omega)
          simp only [Nat.add_zero] at hq0
          exact Or.inl ⟨h1, by rw [hq0]; simpa [Nat.zero_add] using h2⟩
        · have hq0 := hmatch 0 (by rw [harr_size]; omega)
          simp only [Nat.add_zero] at hq0
          exact Or.inr ⟨by rw [hq0]; exact h1,
            fun i h1i h2i => by
              rw [hmatch i (by rw [harr_size]; omega)]
              simpa [Nat.zero_add] using h2 i h1i h2i⟩
      have hdot_buf : buf[q + k]! = 46 := by
        rw [hmatch k (by rw [harr_size]; omega)]; exact hdot_rn
      have hfrac_buf : ∀ i, k + 1 ≤ i → i < k + 1 + e → Ascii.isDigit buf[q + i]! = true := by
        intro i h1i h2i
        rw [hmatch i (by rw [harr_size]; omega)]
        simpa [Nat.zero_add] using hfrac_rn i h1i h2i
      have hdec : decodeNumberBytes? buf q (q + (k + 1 + e)) = some (Json.num m e) := by
        have h := GripProps.Number.decode_renderNum_at buf q m e hq hmatch
          (GripProps.Number.decode_renderNum_frac m hm e he_pos)
        rw [harr_size] at h; exact h
      have hstop' : q + (k + 1 + e) = buf.size ∨ (q + (k + 1 + e) < buf.size ∧
          Ascii.isDigit buf[q + (k + 1 + e)]! = false ∧ buf[q + (k + 1 + e)]! ≠ 46 ∧
          Ascii.isExp buf[q + (k + 1 + e)]! = false) := harr_size ▸ hstop
      rw [harr_size]
      exact value_run_num_frac buf q m e k (k + 1 + e) hm hk_pos (by omega) (harr_size ▸ hq)
        hintstruct_buf hdot_buf hfrac_buf hstop' hdec
    · -- e > 0, m < 0: negative fractional
      push_neg at hm
      set len := (toString m.natAbs).length with hlen_def
      set ds := List.replicate (e + 1 - len) '0' ++ (toString m.natAbs).toList with hds_def
      set k := ds.length - e with hk_def
      have hds_dig : ∀ c ∈ ds, 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
        intro c hc
        rcases List.mem_append.mp hc with h | h
        · rw [List.eq_of_mem_replicate h]; decide
        · have htl : (toString m.natAbs).toList = Nat.toDigits 10 m.natAbs := by
            show (Nat.repr m.natAbs).toList = _; rw [Nat.repr, String.toList_ofList]
          exact GripProps.NatDigits.mem_toDigits_bound m.natAbs c (htl ▸ h)
      have hna_pos : 0 < m.natAbs := Int.natAbs_pos.mpr (by omega)
      have hlen_pos : 1 ≤ len := by
        rw [hlen_def]
        have hll : (toString m.natAbs).length = (Nat.toDigits 10 m.natAbs).length := by
          show (Nat.repr m.natAbs).length = _; rw [Nat.repr, String.length_ofList]
        rw [hll]
        exact List.length_pos_of_ne_nil (GripProps.NatDigits.toDigits_nonempty m.natAbs hna_pos)
      have hdslen : e + 1 ≤ ds.length := by
        have hlenL : (toString m.natAbs).toList.length = len := by
          have htl : (toString m.natAbs).toList = Nat.toDigits 10 m.natAbs := by
            show (Nat.repr m.natAbs).toList = _; rw [Nat.repr, String.toList_ofList]
          have hll : (Nat.toDigits 10 m.natAbs).length = len := by
            rw [hlen_def]; show (Nat.toDigits 10 m.natAbs).length = (Nat.repr m.natAbs).length
            rw [Nat.repr, String.length_ofList]
          rw [htl, hll]
        rw [hds_def, List.length_append, List.length_replicate, hlenL]; omega
      have hk_pos : 1 ≤ k := by rw [hk_def]; omega
      have hfrac_len : (ds.drop k).length = e := by rw [List.length_drop, hk_def]; omega
      have hrn_str : renderNum m e =
          "-" ++ String.ofList (ds.take k) ++ "." ++ String.ofList (ds.drop k) := by
        unfold renderNum
        simp only [show (e == 0) = false from by simp [he_pos.ne'], Bool.false_eq_true,
          if_false, if_pos (show m < 0 from hm)]
        rfl
      have hint_size : (String.ofList (ds.take k)).toUTF8.size = k := by
        rw [ofList_ascii_toUTF8_size _ (fun c hc => by
              have := hds_dig c (List.mem_of_mem_take hc); omega),
            List.length_take, Nat.min_eq_left (by omega)]
      have hfrac_str_size : (String.ofList (ds.drop k)).toUTF8.size = e := by
        rw [ofList_ascii_toUTF8_size _ (fun c hc => by
              have := hds_dig c (List.mem_of_mem_drop hc); omega), hfrac_len]
      have hpre_int_size : ("-" ++ String.ofList (ds.take k)).toUTF8.size = 1 + k := by
        rw [toUTF8_append, ByteArray.size_append, hint_size,
          show ("-" : String).toUTF8.size = 1 from by decide]
      have harr_size : (renderNum m e).toUTF8.size = k + e + 2 := by
        rw [hrn_str, toUTF8_append, toUTF8_append, toUTF8_append,
            ByteArray.size_append, ByteArray.size_append, ByteArray.size_append,
            hint_size, hfrac_str_size,
            show ("-":String).toUTF8.size = 1 from by decide,
            show (".":String).toUTF8.size = 1 from by decide]; omega
      -- dash at position 0
      have hdash_rn : (renderNum m e).toUTF8[0]! = 45 := by
        rw [hrn_str,
          (dot_append_bytes ("-" ++ String.ofList (ds.take k)) (String.ofList (ds.drop k))).1 0
            (by rw [hpre_int_size]; omega),
          (neg_prepend_bytes _).1]
      -- hintstruct_rn: digit structure at positions 1..k
      have hintstruct_rn :
          (k = 1 ∧ (renderNum m e).toUTF8[1]! = 48) ∨
          (Ascii.isDigit19 (renderNum m e).toUTF8[1]! = true ∧
           ∀ i, 1 ≤ i → i < k → Ascii.isDigit (renderNum m e).toUTF8[1 + i]! = true) := by
        rcases Nat.eq_zero_or_pos (e + 1 - len) with hpads0 | hpads_pos
        · have htl : (toString m.natAbs).toList = Nat.toDigits 10 m.natAbs := by
            show (Nat.repr m.natAbs).toList = _; rw [Nat.repr, String.toList_ofList]
          have hne : Nat.toDigits 10 m.natAbs ≠ [] :=
            GripProps.NatDigits.toDigits_nonempty m.natAbs hna_pos
          have hbounds0 := GripProps.NatDigits.toDigits_head_pos m.natAbs hna_pos
          have hlt256_0 : (Nat.toDigits 10 m.natAbs).head!.toNat < 256 := by omega
          have hds_eq : ds = Nat.toDigits 10 m.natAbs := by simp [hds_def, hpads0, htl]
          have hh : 0 < (ds.take k).length := by
            rw [List.length_take, Nat.min_eq_left (by omega)]; omega
          have harr1 : (renderNum m e).toUTF8[1]! =
              UInt8.ofNat (Nat.toDigits 10 m.natAbs).head!.toNat := by
            rw [hrn_str,
              (dot_append_bytes ("-" ++ String.ofList (ds.take k)) (String.ofList (ds.drop k))).1 1
                (by rw [hpre_int_size]; omega),
              (neg_prepend_bytes _).2 0 (by rw [hint_size]; omega),
              ofList_ascii_toUTF8_getElem! (ds.take k) 0 (fun c hc => by
                have := hds_dig c (List.mem_of_mem_take hc); omega) hh]
            congr 1
            rw [getElem!_pos (ds.take k) 0 hh, List.getElem_take,
              ← getElem!_pos ds 0 (by omega), hds_eq]
            match Nat.toDigits 10 m.natAbs, hne with | d :: _, _ => rfl
          exact Or.inr ⟨by
            rw [harr1]
            exact isDigit19_of_toNat_bounds _
              (by rw [UInt8.toNat_ofNat_of_lt' hlt256_0]; exact hbounds0.1)
              (by rw [UInt8.toNat_ofNat_of_lt' hlt256_0]; exact hbounds0.2),
            fun i h1i h2i => by
              rw [hrn_str,
                (dot_append_bytes ("-" ++ String.ofList (ds.take k)) (String.ofList (ds.drop k))).1
                  (1 + i) (by rw [hpre_int_size]; omega),
                (neg_prepend_bytes _).2 i (by rw [hint_size]; omega)]
              have h_lt : i < (ds.take k).length := by
                rw [List.length_take, Nat.min_eq_left (by omega)]; omega
              rw [ofList_ascii_toUTF8_getElem! (ds.take k) i (fun c hc => by
                    have := hds_dig c (List.mem_of_mem_take hc); omega) h_lt]
              exact isDigit_byte_of_mem hds_dig (by
                rw [getElem!_pos _ i h_lt]
                exact List.mem_of_mem_take (List.getElem_mem h_lt))⟩
        · have hk1 : k = 1 := by
            have hlenL : (toString m.natAbs).toList.length = len := by
              have htl : (toString m.natAbs).toList = Nat.toDigits 10 m.natAbs := by
                show (Nat.repr m.natAbs).toList = _; rw [Nat.repr, String.toList_ofList]
              have hll : (Nat.toDigits 10 m.natAbs).length = len := by
                rw [hlen_def]; show (Nat.toDigits 10 m.natAbs).length = (Nat.repr m.natAbs).length
                rw [Nat.repr, String.length_ofList]
              rw [htl, hll]
            rw [hk_def, hds_def, List.length_append, List.length_replicate, hlenL]; omega
          have htake1 : ds.take 1 = ['0'] := by
            rw [hds_def, List.take_append_of_le_length (by rw [List.length_replicate]; omega),
                List.take_replicate, Nat.min_eq_left (by omega)]; simp
          exact Or.inl ⟨hk1, by
            have h0size : (String.ofList ['0']).toUTF8.size = 1 :=
              ofList_ascii_toUTF8_size _ (fun c hc => by cases (List.mem_singleton.mp hc); decide)
            rw [hrn_str, hk1, htake1, toUTF8_append, toUTF8_append, toUTF8_append,
                ba_get!_append_left (by rw [ByteArray.size_append, ByteArray.size_append,
                  show ("-":String).toUTF8.size = 1 from by decide]; omega),
                ba_get!_append_left (by rw [ByteArray.size_append,
                  show ("-":String).toUTF8.size = 1 from by decide, h0size]; omega),
                ba_get!_append_right (by decide)
                  (by rw [ByteArray.size_append,
                    show ("-":String).toUTF8.size = 1 from by decide, h0size]; omega),
                show (1 : Nat) - ("-":String).toUTF8.size = 0 from by decide]; decide⟩
      have hpre_int_size : ("-" ++ String.ofList (ds.take k)).toUTF8.size = 1 + k := by
        rw [toUTF8_append, ByteArray.size_append, hint_size,
          show ("-" : String).toUTF8.size = 1 from by decide]
      -- hdot_rn: dot at position 1 + k
      have hdot_rn : (renderNum m e).toUTF8[1 + k]! = 46 := by
        rw [hrn_str]
        have h := (dot_append_bytes ("-" ++ String.ofList (ds.take k))
          (String.ofList (ds.drop k))).2.1
        rwa [hpre_int_size] at h
      -- hfrac_rn: frac digits at positions k+2..k+e+1
      have hfrac_rn : ∀ i, k + 2 ≤ i → i < k + e + 2 →
          Ascii.isDigit (renderNum m e).toUTF8[i]! = true := by
        intro i h1i h2i
        rw [hrn_str]
        have h := (dot_append_bytes ("-" ++ String.ofList (ds.take k))
          (String.ofList (ds.drop k))).2.2 (i - k - 2) (by rw [hfrac_str_size]; omega)
        rw [hpre_int_size, show 1 + k + 1 + (i - k - 2) = i from by omega] at h
        rw [h, ofList_ascii_toUTF8_getElem! _ (i - k - 2) (fun c hc => by
              have := hds_dig c (List.mem_of_mem_drop hc); omega) (by rw [hfrac_len]; omega)]
        exact isDigit_byte_of_mem hds_dig (by
          rw [getElem!_pos (ds.drop k) (i - k - 2) (by rw [hfrac_len]; omega)]
          exact List.mem_of_mem_drop (List.getElem_mem (by rw [hfrac_len]; omega)))
      -- transfer to buf
      have hdash_buf : buf[q]! = 45 := by
        have h := hmatch 0 (by rw [harr_size]; omega)
        simp only [Nat.add_zero] at h
        rw [h]; exact hdash_rn
      have hintstruct_buf : (k = 1 ∧ buf[q + 1]! = 48) ∨
          (Ascii.isDigit19 buf[q + 1]! = true ∧
           ∀ i, 1 ≤ i → i < k → Ascii.isDigit buf[q + 1 + i]! = true) := by
        rcases hintstruct_rn with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, by rw [hmatch 1 (by rw [harr_size]; omega)]; exact h2⟩
        · exact Or.inr ⟨by rw [hmatch 1 (by rw [harr_size]; omega)]; exact h1,
            fun i h1i h2i => by
              rw [show q + 1 + i = q + (1 + i) from by omega,
                hmatch (1 + i) (by rw [harr_size]; omega)]
              exact h2 i h1i h2i⟩
      have hdot_buf : buf[q + 1 + k]! = 46 := by
        rw [show q + 1 + k = q + (1 + k) from by omega, hmatch (1 + k) (by rw [harr_size]; omega)]
        exact hdot_rn
      have hfrac_buf : ∀ i, k + 2 ≤ i → i < k + e + 2 → Ascii.isDigit buf[q + i]! = true := by
        intro i h1i h2i; rw [hmatch i (by rw [harr_size]; omega)]; exact hfrac_rn i h1i h2i
      have hdec : decodeNumberBytes? buf q (q + (k + e + 2)) = some (Json.num m e) := by
        have h := GripProps.Number.decode_renderNum_at buf q m e hq hmatch
          (GripProps.Number.decode_renderNum_frac_neg m hm e he_pos)
        rw [harr_size] at h; exact h
      have hstop' : q + (k + e + 2) = buf.size ∨ (q + (k + e + 2) < buf.size ∧
          Ascii.isDigit buf[q + (k + e + 2)]! = false ∧ buf[q + (k + e + 2)]! ≠ 46 ∧
          Ascii.isExp buf[q + (k + e + 2)]! = false) := harr_size ▸ hstop
      rw [harr_size]
      exact value_run_num_frac_neg buf q m e k (k + e + 2) hm hk_pos (by omega) (harr_size ▸ hq)
        hdash_buf hintstruct_buf hdot_buf hfrac_buf hstop' hdec
end GripProps.Parse
