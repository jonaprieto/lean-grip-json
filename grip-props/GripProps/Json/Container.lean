/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import GripProps.FixComplete
import GripProps.Json.Parse
import GripProps.Json.ScanStr

/-!
# Container round-trip lemmas and the JSON round-trip theorem

The array and object cases of the round-trip, and the theorem itself:
- `valueBody_guarded` – `Grip.Json.valueBody` is `Guarded`
- `fixSelf_eq_value_of_gt` – `fixSelf valueBody (arr.size - q)` at offsets `> q` agrees with `value`
- `value_run_at` – general embedding: `value` parses any occurrence of `render v` in a byte array
- `parse_render` – the headline theorem: `Grip.Json.parse (render v).toUTF8 = .ok v` for all `v`
-/

open Grip Grip.Json Grip.Json.Json
open GripProps.Parse GripProps.ScanStr GripProps.Bytes
open Grip.FixComplete

set_option maxHeartbeats 1600000

namespace GripProps.Container

-- ---------------------------------------------------------------------------
-- 1. Guarded valueBody
-- ---------------------------------------------------------------------------

-- Helper: pair si at pos agrees
private theorem pair_agree (s1 s2 : GParser conditional Json)
    (arr : ByteArray) (q pos : Nat) (hpos : q < pos)
    (hpre : ∀ q', q < q' → AgreeOk (s1.run arr q') (s2.run arr q')) :
    AgreeOk
      ((GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
          (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'") s1)).run arr pos)
      ((GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
          (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'") s2)).run arr pos) := by
  simp only [GParser.map2, GParser.seqR]
  cases hjstr : Grip.Json.jstr.run arr pos with
  | error _ => exact AgreeOk.refl _
  | ok k qk =>
    dsimp only
    have hqk : pos < qk := Grip.Json.jstr.cwit hjstr
    cases hcolon : (Grip.Json.wsByte Ascii.colon "':'").run arr qk with
    | error _ => exact AgreeOk.refl _
    | ok _ qc =>
      dsimp only
      have hqc_q : q < qc :=
          lt_trans hpos (lt_trans hqk ((Grip.Json.wsByte Ascii.colon "':'").cwit hcolon))
      have ha := hpre qc hqc_q
      cases hv1 : s1.run arr qc with
      | error e1 =>
        cases hv2 : s2.run arr qc with
        | error _ => dsimp only; trivial
        | ok v2 qv2 => rw [hv1, hv2] at ha; simp [AgreeOk] at ha
      | ok v1 qv1 =>
        cases hv2 : s2.run arr qc with
        | error _ => rw [hv1, hv2] at ha; simp [AgreeOk] at ha
        | ok v2 qv2 =>
          dsimp only
          rw [hv1, hv2] at ha; simp only [AgreeOk] at ha
          obtain ⟨hv, hq⟩ := ha; subst hv; subst hq
          exact AgreeOk.refl _

-- Helper: seqR ws (pair si) at r ≥ pos > q agrees
private theorem seqR_ws_pair_agree (s1 s2 : GParser conditional Json)
    (arr : ByteArray) (q r : Nat) (hr : q < r)
    (hpre : ∀ q', q < q' → AgreeOk (s1.run arr q') (s2.run arr q')) :
    AgreeOk
      ((GParser.seqR GParser.ws
          (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
            (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'") s1))).run arr r)
      ((GParser.seqR GParser.ws
          (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
            (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'") s2))).run arr r) := by
  simp only [GParser.seqR]
  cases hws : GParser.ws.run arr r with
  | error _ => exact AgreeOk.refl _
  | ok _ rw =>
    dsimp only
    exact pair_agree s1 s2 arr q rw (lt_of_lt_of_le hr (GParser.ws.cwit hws)) hpre

/-- If two element parsers agree on acceptance at every position at or after `pos`, the
committed container loop gives the same result for both. The loop only ever runs its element
at positions `≥ pos`, so this is the agreement hypothesis `Guarded` supplies. -/
private theorem bodyFwd_agree {α β : Type} (push : β → α → β)
    (elem1 elem2 : GParser conditional α) (close : UInt8) (closeName : String)
    (arr : ByteArray) (acc : β) (first : Bool) (pos : Nat)
    (hagree : ∀ r, pos ≤ r → AgreeOk (elem1.run arr r) (elem2.run arr r)) :
    AgreeOk (Grip.Json.bodyFwd push elem1 close closeName arr acc first pos)
            (Grip.Json.bodyFwd push elem2 close closeName arr acc first pos) := by
  rw [Grip.Json.bodyFwd, Grip.Json.bodyFwd]
  have hge := scanFwd_ge arr Ascii.isWs pos
  split
  · -- head: the element is attempted at `pos` itself
    have ha := hagree pos le_rfl
    cases h1 : elem1.run arr pos with
    | ok x1 q1 =>
      cases h2 : elem2.run arr pos with
      | ok x2 q2 =>
        rw [h1, h2] at ha; simp only [AgreeOk] at ha
        obtain ⟨hx, hq⟩ := ha; subst hx; subst hq
        dsimp only
        split
        · next hguard =>
          exact bodyFwd_agree push elem1 elem2 close closeName arr (push acc x1) false q1
            (fun r hr => hagree r (le_trans (le_of_lt hguard.1) hr))
        · exact AgreeOk.refl _
      | error e2 => rw [h1, h2] at ha; simp [AgreeOk] at ha
    | error e1 =>
      cases h2 : elem2.run arr pos with
      | ok x2 q2 => rw [h1, h2] at ha; simp [AgreeOk] at ha
      | error e2 =>
        -- Both fall back to the empty-container test, which does not look at the element.
        dsimp only
        split
        · split
          · exact AgreeOk.refl _
          · exact True.intro
        · exact True.intro
  · -- tail: the element is attempted just past the separator
    simp only []
    split
    · split
      · exact AgreeOk.refl _
      · split
        · have ha := hagree (scanFwd arr Ascii.isWs pos + 1) (by omega)
          cases h1 : elem1.run arr (scanFwd arr Ascii.isWs pos + 1) with
          | ok x1 q1 =>
            cases h2 : elem2.run arr (scanFwd arr Ascii.isWs pos + 1) with
            | ok x2 q2 =>
              rw [h1, h2] at ha; simp only [AgreeOk] at ha
              obtain ⟨hx, hq⟩ := ha; subst hx; subst hq
              dsimp only
              split
              · next hguard =>
                exact bodyFwd_agree push elem1 elem2 close closeName arr (push acc x1) false q1
                  (fun r hr => hagree r (le_trans (le_of_lt hguard.1) hr))
              · exact AgreeOk.refl _
            | error e2 => rw [h1, h2] at ha; simp [AgreeOk] at ha
          | error e1 =>
            cases h2 : elem2.run arr (scanFwd arr Ascii.isWs pos + 1) with
            | ok x2 q2 => rw [h1, h2] at ha; simp [AgreeOk] at ha
            | error e2 => exact True.intro
        · exact AgreeOk.refl _
    · exact AgreeOk.refl _
termination_by arr.size - pos
decreasing_by
  · omega
  · have := scanFwd_ge arr Ascii.isWs pos
    omega

/-- Agreement lifted to the `containerBody` parser: the array and object arms of `valueBody`
differ only in their element parser, so one lemma covers both. -/
private theorem containerBody_agree {α β : Type} (push : β → α → β)
    (elem1 elem2 : GParser conditional α) (close : UInt8) (closeName : String) (acc : β)
    (arr : ByteArray) (pos : Nat)
    (hagree : ∀ r, pos ≤ r → AgreeOk (elem1.run arr r) (elem2.run arr r)) :
    AgreeOk ((Grip.Json.containerBody push elem1 close closeName acc).run arr pos)
            ((Grip.Json.containerBody push elem2 close closeName acc).run arr pos) := by
  simp only [Grip.Json.containerBody]
  exact bodyFwd_agree push elem1 elem2 close closeName arr acc true pos hagree

/-- `valueBody` is Guarded. -/
theorem valueBody_guarded : Guarded Grip.Json.valueBody := by
  intro s1 s2 arr q hpre
  simp only [Grip.Json.valueBody, Grip.Json.wsDispatch]
  have hpq : q ≤ scanFwd arr Ascii.isWs q := scanFwd_ge arr Ascii.isWs q
  set p := scanFwd arr Ascii.isWs q
  by_cases hplt : p < arr.size
  · simp only [hplt]
    by_cases hbrace : arr[p] == Ascii.lbrace
    · simp only [hbrace, ↓reduceIte]
      -- Set ob1/ob2 before unfolding seqR/map so they stay opaque in the goal simp.
      set ob1 := Grip.Json.containerBody (fun (a : Array (String × Json)) x => a.push x)
          (GParser.seqR GParser.ws
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'") s1))) Ascii.rbrace "'}'" #[]
      set ob2 := Grip.Json.containerBody (fun (a : Array (String × Json)) x => a.push x)
          (GParser.seqR GParser.ws
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'") s2))) Ascii.rbrace "'}'" #[]
      simp only [GParser.seqR, GParser.map]
      cases hch : (GParser.ch '{').run arr p with
      | error _ => exact AgreeOk.refl _
      | ok _ p1 =>
        dsimp only
        have hp1q : q < p1 := Nat.lt_of_le_of_lt hpq ((GParser.ch '{').cwit hch)
        have hob : AgreeOk (ob1.run arr p1) (ob2.run arr p1) :=
          containerBody_agree _ _ _ Ascii.rbrace "'}'" #[] arr p1
            (fun r hr => seqR_ws_pair_agree s1 s2 arr q r (lt_of_lt_of_le hp1q hr) hpre)
        cases h1 : ob1.run arr p1 with
        | error e1 =>
          dsimp only
          cases h2 : ob2.run arr p1 with
          | error _ => dsimp only; trivial
          | ok xs2 q2 => rw [h1, h2] at hob; simp [AgreeOk] at hob
        | ok xs1 q1 =>
          dsimp only
          cases h2 : ob2.run arr p1 with
          | error _ => rw [h1, h2] at hob; simp [AgreeOk] at hob
          | ok xs2 q2 =>
            dsimp only
            rw [h1, h2] at hob; simp only [AgreeOk] at hob
            obtain ⟨hxs, hq⟩ := hob; subst hxs; subst hq
            exact AgreeOk.refl _
    · by_cases hbracket : arr[p] == Ascii.lbracket
      · simp only [hbrace, Bool.false_eq_true, ↓reduceIte, hbracket, ↓reduceIte]
        set ab1 := Grip.Json.containerBody (fun (a : Array Json) e => a.push e)
            s1 Ascii.rbracket "']'" #[]
        set ab2 := Grip.Json.containerBody (fun (a : Array Json) e => a.push e)
            s2 Ascii.rbracket "']'" #[]
        simp only [GParser.seqR, GParser.map]
        cases hch : (GParser.ch '[').run arr p with
        | error _ => exact AgreeOk.refl _
        | ok _ p1 =>
          dsimp only
          have hp1q : q < p1 := Nat.lt_of_le_of_lt hpq ((GParser.ch '[').cwit hch)
          have hab : AgreeOk (ab1.run arr p1) (ab2.run arr p1) :=
            containerBody_agree _ _ _ Ascii.rbracket "']'" #[] arr p1
              (fun r hr => hpre r (lt_of_lt_of_le hp1q hr))
          cases h1 : ab1.run arr p1 with
          | error e1 =>
            dsimp only
            cases h2 : ab2.run arr p1 with
            | error _ => dsimp only; trivial
            | ok xs2 q2 => rw [h1, h2] at hab; simp [AgreeOk] at hab
          | ok xs1 q1 =>
            dsimp only
            cases h2 : ab2.run arr p1 with
            | error _ => rw [h1, h2] at hab; simp [AgreeOk] at hab
            | ok xs2 q2 =>
              dsimp only
              rw [h1, h2] at hab; simp only [AgreeOk] at hab
              obtain ⟨hxs, hq⟩ := hab; subst hxs; subst hq
              exact AgreeOk.refl _
      · simp only [hbrace, Bool.false_eq_true, ↓reduceIte, hbracket, Bool.false_eq_true, ↓reduceIte]
        exact AgreeOk.refl _
  · simp only [show ¬ p < arr.size from hplt]
    exact True.intro

-- ---------------------------------------------------------------------------
-- 2. fixSelf agrees with value at positions > q
-- ---------------------------------------------------------------------------

/-- At positions `q' > q`, `fixSelf valueBody (arr.size - q)` agrees with `value`. -/
theorem fixSelf_eq_value_of_gt (arr : ByteArray) (q q' : Nat) (hqq' : q < q') :
    AgreeOk ((GParser.fixSelf Grip.Json.valueBody (arr.size - q)).run arr q')
            (Grip.Json.value.run arr q') := by
  simp only [GParser.fixSelf_run, Grip.Json.value, GParser.fix]
  by_cases hq'le : q' ≤ arr.size
  · apply clamp_agree
    have hag := agree_add Grip.Json.valueBody valueBody_guarded arr q' (q' - q - 1)
    rwa [show arr.size - q' + 1 + (q' - q - 1) = arr.size - q from by omega] at hag
  · exact clamp_oob arr q' (by omega)

-- ---------------------------------------------------------------------------
-- 3. Structural byte facts for render (.str s)
-- ---------------------------------------------------------------------------

private theorem render_str_size (s : String) :
    (render (.str s)).toUTF8.size = 2 + (ebytes s.toList).length := by
  simp only [render, String.toUTF8_eq_toByteArray, String.toByteArray_append, ByteArray.size_append]
  have hqs : ("\"" : String).toByteArray.size = 1 := by decide
  have hes : (escape s).toByteArray.size = (ebytes s.toList).length := escape_toUTF8_size s
  omega

private theorem render_str_byte0 (s : String) :
    (render (.str s)).toUTF8[0]! = 34 := by
  simp only [render, String.toUTF8_eq_toByteArray, String.toByteArray_append]
  have hqs : ("\"" : String).toByteArray.size = 1 := by decide
  have hes : (escape s).toByteArray.size = (ebytes s.toList).length := escape_toUTF8_size s
  rw [ba_get!_append_left (by rw [ByteArray.size_append]; omega)]
  rw [ba_get!_append_left (by omega)]
  decide

private theorem render_str_byte_mid (s : String) (j : Nat)
    (hj : j < (ebytes s.toList).length) :
    (render (.str s)).toUTF8[1 + j]! = (ebytes s.toList)[j]! := by
  simp only [render, String.toUTF8_eq_toByteArray, String.toByteArray_append]
  have hqs : ("\"" : String).toByteArray.size = 1 := by decide
  have hes : (escape s).toByteArray.size = (ebytes s.toList).length := escape_toUTF8_size s
  rw [ba_get!_append_left (by rw [ByteArray.size_append]; omega)]
  rw [ba_get!_append_right (by omega) (by rw [ByteArray.size_append]; omega)]
  simp only [show 1 + j - ("\"" : String).toByteArray.size = j from by omega]
  exact escape_toUTF8_getElem! s j (hes ▸ hj)

private theorem render_str_byte_close (s : String) :
    (render (.str s)).toUTF8[1 + (ebytes s.toList).length]! = 34 := by
  simp only [render, String.toUTF8_eq_toByteArray, String.toByteArray_append]
  have hqs : ("\"" : String).toByteArray.size = 1 := by decide
  have hes : (escape s).toByteArray.size = (ebytes s.toList).length := escape_toUTF8_size s
  have hmid : ("\"" : String).toByteArray.size + (escape s).toByteArray.size =
      1 + (ebytes s.toList).length := by omega
  rw [ba_get!_append_right (by rw [ByteArray.size_append, hqs, hes])
    (by rw [ByteArray.size_append, ByteArray.size_append, hqs, hes]; omega)]
  simp only [ByteArray.size_append, hqs, hes, Nat.sub_self]
  decide

-- ---------------------------------------------------------------------------
-- 4. Helper byte-position lemmas for array/object round-trips
-- ---------------------------------------------------------------------------

private theorem lbracket_last_byte (body : String) :
    ("[" ++ body ++ "]").toUTF8[("[" ++ body ++ "]").toUTF8.size - 1]! = 93 := by
  have h1 : ("]" : String).toUTF8.size = 1 := by decide
  rw [toUTF8_append, ByteArray.size_append, h1,
      ba_get!_append_right (by omega) (by rw [ByteArray.size_append, h1]; omega)]
  simp only [show ("[" ++ body).toUTF8.size + 1 - 1 - ("[" ++ body).toUTF8.size = 0 from by omega]
  decide

private theorem lbrace_last_byte (body : String) :
    ("{" ++ body ++ "}").toUTF8[("{" ++ body ++ "}").toUTF8.size - 1]! = 125 := by
  have h1 : ("}" : String).toUTF8.size = 1 := by decide
  rw [toUTF8_append, ByteArray.size_append, h1,
      ba_get!_append_right (by omega) (by rw [ByteArray.size_append, h1]; omega)]
  simp only [show ("{" ++ body).toUTF8.size + 1 - 1 - ("{" ++ body).toUTF8.size = 0 from by omega]
  decide

-- First byte of "\""-prefixed string's UTF8 is 34
private theorem str_prepend_byte0 (s : String) : ("\"" ++ s).toUTF8[0]! = 34 := by
  rw [toUTF8_append, ba_get!_append_left (by decide)]
  decide

-- Byte 1+j of "o"++body++"c" equals body[j] when |o|=1
private theorem body_byte_j (open_b close_b : String) (ho : open_b.toUTF8.size = 1) (body : String)
    (j : Nat) (hj : j < body.toUTF8.size) :
    (open_b ++ body ++ close_b).toUTF8[1 + j]! = body.toUTF8[j]! := by
  rw [toUTF8_append, ba_get!_append_left (by rw [toUTF8_append, ByteArray.size_append, ho]; omega),
      toUTF8_append, ba_get!_append_right (by omega) (by rw [ByteArray.size_append]; omega)]
  simp only [show 1 + j - open_b.toUTF8.size = j from by omega]

-- ---------------------------------------------------------------------------
-- 5. Comma-prefixed tail helper for array/object body round-trips
-- ---------------------------------------------------------------------------

-- "," ++ render x₀ ++ "," ++ render x₁ ++ ... for the tail elements
private def commaPrefix : List Json → String
  | []        => ""
  | x :: rest => "," ++ render x ++ commaPrefix rest

private theorem commaPrefix_cons_size (x : Json) (rest : List Json) :
    (commaPrefix (x :: rest)).toUTF8.size =
    1 + (render x).toUTF8.size + (commaPrefix rest).toUTF8.size := by
  simp only [commaPrefix, toUTF8_append, ByteArray.size_append]
  have h : (",":String).toUTF8.size = 1 := by decide
  omega

-- Byte 0 of commaPrefix (x :: rest) is ',' (44)
private theorem commaPrefix_byte_comma (x : Json) (rest : List Json) :
    (commaPrefix (x :: rest)).toUTF8[0]! = 44 := by
  simp only [commaPrefix, toUTF8_append]
  have hc : (",":String).toUTF8.size = 1 := by decide
  rw [ba_get!_append_left (by rw [ByteArray.size_append]; omega)]
  rw [ba_get!_append_left (by omega)]
  decide

-- Byte (1 + j) of commaPrefix (x :: rest) equals (render x)[j] for j < |render x|
private theorem commaPrefix_byte_x (x : Json) (rest : List Json) (j : Nat)
    (hj : j < (render x).toUTF8.size) :
    (commaPrefix (x :: rest)).toUTF8[1 + j]! = (render x).toUTF8[j]! := by
  simp only [commaPrefix, toUTF8_append]
  have hc : (",":String).toUTF8.size = 1 := by decide
  rw [ba_get!_append_left (by rw [ByteArray.size_append]; omega)]
  rw [ba_get!_append_right (by omega) (by rw [ByteArray.size_append]; omega)]
  simp only [show 1 + j - (",":String).toUTF8.size = j from by simp only [hc]; omega]

-- Byte (1 + |render x| + j) of commaPrefix (x :: rest) equals (commaPrefix rest)[j]
private theorem commaPrefix_byte_rest (x : Json) (rest : List Json) (j : Nat)
    (hj : j < (commaPrefix rest).toUTF8.size) :
    (commaPrefix (x :: rest)).toUTF8[1 + (render x).toUTF8.size + j]! =
        (commaPrefix rest).toUTF8[j]! := by
  simp only [commaPrefix, toUTF8_append]
  have hc : (",":String).toUTF8.size = 1 := by decide
  rw [ba_get!_append_right
      (by rw [ByteArray.size_append]; omega)
      (by rw [ByteArray.size_append, ByteArray.size_append]; omega)]
  simp only [show 1 + (render x).toUTF8.size + j - ((",":String).toUTF8 ++ (render x).toUTF8).size =
      j from by simp only [ByteArray.size_append, hc]; omega]

-- joinWith "," ((x :: rest).map render) = render x ++ commaPrefix rest
private theorem joinWith_map_render_eq (x : Json) (rest : List Json) :
    joinWith "," ((x :: rest).map render) = render x ++ commaPrefix rest := by
  induction rest generalizing x with
  | nil => simp [joinWith, commaPrefix]
  | cons y ys ih =>
    simp only [List.map, joinWith]
    cases ys with
    | nil => simp [joinWith, commaPrefix, String.append_assoc]
    | cons z zs =>
      rw [show joinWith "," (render y :: List.map render (z :: zs)) =
          render y ++ commaPrefix (z :: zs) from ih y]
      simp [commaPrefix, String.append_assoc]

-- ---------------------------------------------------------------------------
-- 6. Key-value rendering and comma-prefixed tail for object body round-trips
-- ---------------------------------------------------------------------------

-- renderKV (k, v) = render (.str k) ++ ":" ++ render v
private def renderKV : String × Json → String
  | (k, v) => render (.str k) ++ ":" ++ render v

private def commaPrefixKV : List (String × Json) → String
  | []         => ""
  | kv :: rest => "," ++ renderKV kv ++ commaPrefixKV rest

private theorem renderKV_size (k : String) (v : Json) :
    (renderKV (k, v)).toUTF8.size =
    2 + (ebytes k.toList).length + 1 + (render v).toUTF8.size := by
  simp only [renderKV, toUTF8_append, ByteArray.size_append]
  rw [render_str_size k]
  have h : (":":String).toUTF8.size = 1 := by decide
  omega

private theorem renderKV_byte0 (kv : String × Json) :
    (renderKV kv).toUTF8[0]! = 34 := by
  simp only [renderKV, toUTF8_append]
  rw [ba_get!_append_left (by
    rw [ByteArray.size_append]
    have h := render_str_size kv.1
    have hc : (":":String).toUTF8.size = 1 := by decide
    omega)]
  rw [ba_get!_append_left (by
    have h := render_str_size kv.1; omega)]
  exact render_str_byte0 kv.1

private theorem renderKV_pos (kv : String × Json) : 0 < (renderKV kv).toUTF8.size := by
  simp only [renderKV, toUTF8_append, ByteArray.size_append]
  have h := render_str_size kv.1
  have hc : (":":String).toUTF8.size = 1 := by decide
  omega

private theorem commaPrefixKV_cons_size (kv : String × Json) (rest : List (String × Json)) :
    (commaPrefixKV (kv :: rest)).toUTF8.size =
    1 + (renderKV kv).toUTF8.size + (commaPrefixKV rest).toUTF8.size := by
  simp only [commaPrefixKV, toUTF8_append, ByteArray.size_append]
  have h : (",":String).toUTF8.size = 1 := by decide
  omega

private theorem commaPrefixKV_byte_comma (kv : String × Json) (rest : List (String × Json)) :
    (commaPrefixKV (kv :: rest)).toUTF8[0]! = 44 := by
  simp only [commaPrefixKV, toUTF8_append]
  have hc : (",":String).toUTF8.size = 1 := by decide
  rw [ba_get!_append_left (by rw [ByteArray.size_append]; omega)]
  rw [ba_get!_append_left (by omega)]
  decide

private theorem commaPrefixKV_byte_kv (kv : String × Json) (rest : List (String × Json))
    (j : Nat) (hj : j < (renderKV kv).toUTF8.size) :
    (commaPrefixKV (kv :: rest)).toUTF8[1 + j]! = (renderKV kv).toUTF8[j]! := by
  simp only [commaPrefixKV, toUTF8_append]
  have hc : (",":String).toUTF8.size = 1 := by decide
  rw [ba_get!_append_left (by rw [ByteArray.size_append]; omega)]
  rw [ba_get!_append_right (by omega) (by rw [ByteArray.size_append]; omega)]
  simp only [show 1 + j - (",":String).toUTF8.size = j from by simp only [hc]; omega]

private theorem commaPrefixKV_byte_rest (kv : String × Json) (rest : List (String × Json))
    (j : Nat) (hj : j < (commaPrefixKV rest).toUTF8.size) :
    (commaPrefixKV (kv :: rest)).toUTF8[1 + (renderKV kv).toUTF8.size + j]! =
    (commaPrefixKV rest).toUTF8[j]! := by
  simp only [commaPrefixKV, toUTF8_append]
  have hc : (",":String).toUTF8.size = 1 := by decide
  rw [ba_get!_append_right
      (by rw [ByteArray.size_append]; omega)
      (by rw [ByteArray.size_append, ByteArray.size_append]; omega)]
  simp only [show 1 + (renderKV kv).toUTF8.size + j -
      ((",":String).toUTF8 ++ (renderKV kv).toUTF8).size = j
      from by simp only [ByteArray.size_append, hc]; omega]

private theorem joinWith_map_renderKV_eq (kv : String × Json) (rest : List (String × Json)) :
    joinWith "," ((kv :: rest).map renderKV) = renderKV kv ++ commaPrefixKV rest := by
  induction rest generalizing kv with
  | nil => simp [joinWith, commaPrefixKV]
  | cons kv2 rest2 ih =>
    simp only [List.map, joinWith]
    cases rest2 with
    | nil => simp [joinWith, commaPrefixKV, String.append_assoc]
    | cons kv3 rest3 =>
      rw [show joinWith "," (renderKV kv2 :: List.map renderKV (kv3 :: rest3)) =
          renderKV kv2 ++ commaPrefixKV (kv3 :: rest3) from ih kv2]
      simp [commaPrefixKV, String.append_assoc]

/-- The committed tail loop over a comma-prefixed key/value list, exiting on the closing `}`
and consuming it. The element parser is `ws` then the pair parser, since a key literal (unlike
a value) does not skip its own leading whitespace. -/
private theorem bodyFwd_comma_kv_run
    (kv_parser : GParser conditional (String × Json))
    (lst : List (String × Json)) (buf : ByteArray) (acc : Array (String × Json)) (base : Nat)
    (h_bound : base + (commaPrefixKV lst).toUTF8.size < buf.size)
    (h_match : ∀ j, j < (commaPrefixKV lst).toUTF8.size →
        buf[base + j]! = (commaPrefixKV lst).toUTF8[j]!)
    (h_close : buf[base + (commaPrefixKV lst).toUTF8.size]! = 125)
    (h_kvp : ∀ kv ∈ lst, ∀ (p : Nat),
        p + (renderKV kv).toUTF8.size ≤ buf.size →
        (∀ j, j < (renderKV kv).toUTF8.size → buf[p + j]! = (renderKV kv).toUTF8[j]!) →
        (p + (renderKV kv).toUTF8.size = buf.size ∨
         (p + (renderKV kv).toUTF8.size < buf.size ∧
          Ascii.isDigit buf[p + (renderKV kv).toUTF8.size]! = false ∧
          buf[p + (renderKV kv).toUTF8.size]! ≠ 46 ∧
          Ascii.isExp buf[p + (renderKV kv).toUTF8.size]! = false)) →
        kv_parser.run buf p = .ok kv (p + (renderKV kv).toUTF8.size)) :
    Grip.Json.bodyFwd (fun (a : Array (String × Json)) x => a.push x)
        (GParser.seqR GParser.ws kv_parser) Ascii.rbrace "'}'" buf acc false base =
      .ok (acc ++ lst.toArray) (base + (commaPrefixKV lst).toUTF8.size + 1) := by
  induction lst generalizing base acc with
  | nil =>
    have h_cp_nil : (commaPrefixKV ([] : List (String × Json))).toUTF8.size = 0 := by
      simp [commaPrefixKV]
    simp only [h_cp_nil, Nat.add_zero] at h_bound h_close ⊢
    have hbase : buf[base] = (125 : UInt8) := by rwa [← getElem!_pos buf base h_bound]
    have hs : scanFwd buf Ascii.isWs base = base := by
      rw [scanFwd, dif_pos h_bound, if_neg (by rw [hbase]; decide)]
    rw [Grip.Json.bodyFwd]
    simp only [Bool.false_eq_true, ↓reduceIte, hs, dif_pos h_bound,
      if_pos (show (buf[base] == Ascii.rbrace) = true from by rw [hbase]; decide)]
    simp
  | cons kv rest ih =>
    simp only [commaPrefixKV_cons_size] at h_bound h_match h_close
    have hrkv_pos : 0 < (renderKV kv).toUTF8.size := renderKV_pos kv
    have hbase_lt : base < buf.size := by omega
    have hbase_byte! : buf[base]! = 44 := by
      have h0 := h_match 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [h0]; exact commaPrefixKV_byte_comma kv rest
    have hbase_byte : buf[base] = (44 : UInt8) := by rwa [← getElem!_pos buf base hbase_lt]
    have hs : scanFwd buf Ascii.isWs base = base := by
      rw [scanFwd, dif_pos hbase_lt, if_neg (by rw [hbase_byte]; decide)]
    -- The key's opening quote sits at base + 1, so the element's leading `ws` consumes nothing.
    have hbase1_lt : base + 1 < buf.size := by omega
    have hbase1_byte! : buf[base + 1]! = 34 := by
      have h1 := h_match 1 (by omega)
      rw [h1, commaPrefixKV_byte_kv kv rest 0 hrkv_pos, renderKV_byte0 kv]
    have hbase1_byte : buf[base + 1] = (34 : UInt8) := by
      rwa [← getElem!_pos buf _ hbase1_lt]
    have h_ws_ok : GParser.ws.run buf (base + 1) = .ok 0 (base + 1) :=
      ws_run_stop buf (base + 1) hbase1_lt (by rw [hbase1_byte]; decide)
    -- Bytes for `renderKV kv` at base + 1
    have hkv_bound : (base + 1) + (renderKV kv).toUTF8.size ≤ buf.size := by omega
    have hkv_match : ∀ j, j < (renderKV kv).toUTF8.size →
        buf[(base + 1) + j]! = (renderKV kv).toUTF8[j]! := by
      intro j hj
      have hmj := h_match (1 + j) (by omega)
      rw [show base + (1 + j) = (base + 1) + j from by ring] at hmj
      rw [hmj]; exact commaPrefixKV_byte_kv kv rest j hj
    -- The byte after the pair is ',' (rest non-empty) or '}' (rest empty).
    have hkv_byte : buf[(base + 1) + (renderKV kv).toUTF8.size]! = 44 ∨
        buf[(base + 1) + (renderKV kv).toUTF8.size]! = 125 := by
      cases hrest : rest with
      | nil =>
        right
        have h_cp_nil : (commaPrefixKV ([] : List (String × Json))).toUTF8.size = 0 := by
          simp [commaPrefixKV]
        rw [hrest, h_cp_nil, Nat.add_zero] at h_close
        rw [show (base + 1) + (renderKV kv).toUTF8.size =
            base + (1 + (renderKV kv).toUTF8.size) from by ring]
        exact h_close
      | cons r rs =>
        left
        have hcp_pos : 0 < (commaPrefixKV rest).toUTF8.size := by
          rw [hrest, commaPrefixKV_cons_size]; omega
        have hmj := h_match (1 + (renderKV kv).toUTF8.size) (by omega)
        rw [show base + (1 + (renderKV kv).toUTF8.size) =
            (base + 1) + (renderKV kv).toUTF8.size from by ring] at hmj
        rw [hmj]
        have h_rest_byte := commaPrefixKV_byte_rest kv rest 0 hcp_pos
        rw [Nat.add_zero] at h_rest_byte
        rw [h_rest_byte, hrest]
        exact commaPrefixKV_byte_comma r rs
    have hkv_stop : (base + 1) + (renderKV kv).toUTF8.size = buf.size ∨
        ((base + 1) + (renderKV kv).toUTF8.size < buf.size ∧
         Ascii.isDigit buf[(base + 1) + (renderKV kv).toUTF8.size]! = false ∧
         buf[(base + 1) + (renderKV kv).toUTF8.size]! ≠ 46 ∧
         Ascii.isExp buf[(base + 1) + (renderKV kv).toUTF8.size]! = false) := by
      right
      rcases hkv_byte with h | h
      · exact ⟨by omega, by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
      · exact ⟨by omega, by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
    have hkv_val := h_kvp kv List.mem_cons_self (base + 1) hkv_bound hkv_match hkv_stop
    have h_elem : (GParser.seqR GParser.ws kv_parser).run buf (base + 1) =
        .ok kv (base + 1 + (renderKV kv).toUTF8.size) :=
      seqR_run _ _ _ _ 0 (base + 1) kv _ h_ws_ok hkv_val
    -- IH arguments for the rest of the tail
    have h_rest_bound : (base + 1 + (renderKV kv).toUTF8.size) +
        (commaPrefixKV rest).toUTF8.size < buf.size := by omega
    have h_rest_match : ∀ j, j < (commaPrefixKV rest).toUTF8.size →
        buf[(base + 1 + (renderKV kv).toUTF8.size) + j]! = (commaPrefixKV rest).toUTF8[j]! := by
      intro j hj
      have hmj := h_match (1 + (renderKV kv).toUTF8.size + j) (by omega)
      rw [show base + (1 + (renderKV kv).toUTF8.size + j) =
          (base + 1 + (renderKV kv).toUTF8.size) + j from by ring] at hmj
      rw [hmj]; exact commaPrefixKV_byte_rest kv rest j hj
    have h_rest_close : buf[(base + 1 + (renderKV kv).toUTF8.size) +
        (commaPrefixKV rest).toUTF8.size]! = 125 := by
      rw [show (base + 1 + (renderKV kv).toUTF8.size) + (commaPrefixKV rest).toUTF8.size =
          base + (1 + (renderKV kv).toUTF8.size + (commaPrefixKV rest).toUTF8.size) from by ring]
      exact h_close
    have h_rest_kvp : ∀ kv2 ∈ rest, ∀ (p : Nat),
        p + (renderKV kv2).toUTF8.size ≤ buf.size →
        (∀ j, j < (renderKV kv2).toUTF8.size → buf[p + j]! = (renderKV kv2).toUTF8[j]!) →
        (p + (renderKV kv2).toUTF8.size = buf.size ∨
         (p + (renderKV kv2).toUTF8.size < buf.size ∧
          Ascii.isDigit buf[p + (renderKV kv2).toUTF8.size]! = false ∧
          buf[p + (renderKV kv2).toUTF8.size]! ≠ 46 ∧
          Ascii.isExp buf[p + (renderKV kv2).toUTF8.size]! = false)) →
        kv_parser.run buf p = .ok kv2 (p + (renderKV kv2).toUTF8.size) :=
      fun kv2 hkv2 => h_kvp kv2 (List.mem_cons.mpr (Or.inr hkv2))
    rw [Grip.Json.bodyFwd]
    simp only [Bool.false_eq_true, ↓reduceIte, hs, dif_pos hbase_lt,
      if_neg (show ¬ ((buf[base] == Ascii.rbrace) = true) from by rw [hbase_byte]; decide),
      if_pos (show (buf[base] == Ascii.comma) = true from by rw [hbase_byte]; decide), h_elem]
    rw [dif_pos (show base < base + 1 + (renderKV kv).toUTF8.size ∧
        base + 1 + (renderKV kv).toUTF8.size ≤ buf.size from ⟨by omega, by omega⟩)]
    rw [ih (acc.push kv) (base + 1 + (renderKV kv).toUTF8.size)
        h_rest_bound h_rest_match h_rest_close h_rest_kvp]
    simp only [ParseResult.ok.injEq]
    constructor
    · rw [Array.push_eq_append, List.toArray_cons]; simp
    · rw [commaPrefixKV_cons_size]; omega


/-- The committed tail loop over a comma-prefixed element list. Each `,` obliges an element,
and the loop exits on the closing `]`, consuming it — so the returned offset is one past the
bracket, where the old `foldFwd` stopped short of it. -/
private theorem bodyFwd_comma_value_run (lst : List Json) (buf : ByteArray) (acc : Array Json)
    (base : Nat)
    (h_bound : base + (commaPrefix lst).toUTF8.size < buf.size)
    (h_match : ∀ j, j < (commaPrefix lst).toUTF8.size → buf[base + j]! =
        (commaPrefix lst).toUTF8[j]!)
    (h_close : buf[base + (commaPrefix lst).toUTF8.size]! = 93)
    (h_vp : ∀ x ∈ lst, ∀ (p : Nat),
        p + (render x).toUTF8.size ≤ buf.size →
        (∀ j, j < (render x).toUTF8.size → buf[p + j]! = (render x).toUTF8[j]!) →
        (p + (render x).toUTF8.size = buf.size ∨
         p + (render x).toUTF8.size < buf.size ∧
           Ascii.isDigit buf[p + (render x).toUTF8.size]! = false ∧
           buf[p + (render x).toUTF8.size]! ≠ 46 ∧
           Ascii.isExp buf[p + (render x).toUTF8.size]! = false) →
        Grip.Json.value.run buf p = .ok x (p + (render x).toUTF8.size)) :
    Grip.Json.bodyFwd (fun (a : Array Json) e => a.push e) Grip.Json.value Ascii.rbracket "']'"
        buf acc false base =
      .ok (acc ++ lst.toArray) (base + (commaPrefix lst).toUTF8.size + 1) := by
  induction lst generalizing base acc with
  | nil =>
    have h_cp_nil : (commaPrefix ([] : List Json)).toUTF8.size = 0 := rfl
    simp only [h_cp_nil, Nat.add_zero] at h_bound h_close ⊢
    have hbase : buf[base] = (93 : UInt8) := by rwa [← getElem!_pos buf base h_bound]
    have hs : scanFwd buf Ascii.isWs base = base := by
      rw [scanFwd, dif_pos h_bound, if_neg (by rw [hbase]; decide)]
    rw [Grip.Json.bodyFwd]
    simp only [Bool.false_eq_true, ↓reduceIte, hs, dif_pos h_bound,
      if_pos (show (buf[base] == Ascii.rbracket) = true from by rw [hbase]; decide)]
    simp
  | cons x rest ih =>
    simp only [commaPrefix_cons_size] at h_bound h_match h_close
    have hbase_lt : base < buf.size := by omega
    have hbase_byte! : buf[base]! = 44 := by
      have h0 := h_match 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [h0]; exact commaPrefix_byte_comma x rest
    have hbase_byte : buf[base] = (44 : UInt8) := by rwa [← getElem!_pos buf base hbase_lt]
    have hs : scanFwd buf Ascii.isWs base = base := by
      rw [scanFwd, dif_pos hbase_lt, if_neg (by rw [hbase_byte]; decide)]
    -- Bytes for `render x` at base + 1
    have hx_bound : (base + 1) + (render x).toUTF8.size ≤ buf.size := by omega
    have hx_match : ∀ j, j < (render x).toUTF8.size → buf[(base + 1) + j]! =
        (render x).toUTF8[j]! := by
      intro j hj
      have hmj := h_match (1 + j) (by omega)
      rw [show base + (1 + j) = (base + 1) + j from by ring] at hmj
      rw [hmj]; exact commaPrefix_byte_x x rest j hj
    -- The byte after `render x` is ',' (rest non-empty) or ']' (rest empty); neither continues
    -- a number, so `value` stops exactly at the end of the element.
    have hx_byte : buf[(base + 1) + (render x).toUTF8.size]! = 44 ∨
        buf[(base + 1) + (render x).toUTF8.size]! = 93 := by
      cases hrest : rest with
      | nil =>
        right
        have h_cp_nil : (commaPrefix ([] : List Json)).toUTF8.size = 0 := rfl
        rw [hrest, h_cp_nil, Nat.add_zero] at h_close
        rw [show (base + 1) + (render x).toUTF8.size =
            base + (1 + (render x).toUTF8.size) from by ring]
        exact h_close
      | cons r rs =>
        left
        have hcp_pos : 0 < (commaPrefix rest).toUTF8.size := by
          rw [hrest, commaPrefix_cons_size]; omega
        have hmj := h_match (1 + (render x).toUTF8.size) (by omega)
        rw [show base + (1 + (render x).toUTF8.size) =
            (base + 1) + (render x).toUTF8.size from by ring] at hmj
        rw [hmj]
        have h_rest_byte := commaPrefix_byte_rest x rest 0 hcp_pos
        rw [Nat.add_zero] at h_rest_byte
        rw [h_rest_byte, hrest]
        exact commaPrefix_byte_comma r rs
    have hx_stop : (base + 1) + (render x).toUTF8.size = buf.size ∨
        (base + 1) + (render x).toUTF8.size < buf.size ∧
          Ascii.isDigit buf[(base + 1) + (render x).toUTF8.size]! = false ∧
          buf[(base + 1) + (render x).toUTF8.size]! ≠ 46 ∧
          Ascii.isExp buf[(base + 1) + (render x).toUTF8.size]! = false := by
      right
      rcases hx_byte with h | h
      · exact ⟨by omega, by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
      · exact ⟨by omega, by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
    have hx_val := h_vp x List.mem_cons_self (base + 1) hx_bound hx_match hx_stop
    -- IH arguments for the rest of the tail
    have h_rest_bound : (base + 1 + (render x).toUTF8.size) + (commaPrefix rest).toUTF8.size <
        buf.size := by omega
    have h_rest_match : ∀ j, j < (commaPrefix rest).toUTF8.size →
        buf[(base + 1 + (render x).toUTF8.size) + j]! = (commaPrefix rest).toUTF8[j]! := by
      intro j hj
      have hmj := h_match (1 + (render x).toUTF8.size + j) (by omega)
      rw [show base + (1 + (render x).toUTF8.size + j) =
          (base + 1 + (render x).toUTF8.size) + j from by ring] at hmj
      rw [hmj]; exact commaPrefix_byte_rest x rest j hj
    have h_rest_close : buf[(base + 1 + (render x).toUTF8.size) +
        (commaPrefix rest).toUTF8.size]! = 93 := by
      rw [show (base + 1 + (render x).toUTF8.size) + (commaPrefix rest).toUTF8.size =
          base + (1 + (render x).toUTF8.size + (commaPrefix rest).toUTF8.size) from by ring]
      exact h_close
    have h_rest_vp : ∀ y ∈ rest, ∀ (p : Nat),
        p + (render y).toUTF8.size ≤ buf.size →
        (∀ j, j < (render y).toUTF8.size → buf[p + j]! = (render y).toUTF8[j]!) →
        (p + (render y).toUTF8.size = buf.size ∨
         p + (render y).toUTF8.size < buf.size ∧
           Ascii.isDigit buf[p + (render y).toUTF8.size]! = false ∧
           buf[p + (render y).toUTF8.size]! ≠ 46 ∧
           Ascii.isExp buf[p + (render y).toUTF8.size]! = false) →
        Grip.Json.value.run buf p = .ok y (p + (render y).toUTF8.size) :=
      fun y hy => h_vp y (List.mem_cons.mpr (Or.inr hy))
    rw [Grip.Json.bodyFwd]
    simp only [Bool.false_eq_true, ↓reduceIte, hs, dif_pos hbase_lt,
      if_neg (show ¬ ((buf[base] == Ascii.rbracket) = true) from by rw [hbase_byte]; decide),
      if_pos (show (buf[base] == Ascii.comma) = true from by rw [hbase_byte]; decide), hx_val]
    rw [dif_pos (show base < base + 1 + (render x).toUTF8.size ∧
        base + 1 + (render x).toUTF8.size ≤ buf.size from ⟨by omega, by omega⟩)]
    rw [ih (acc.push x) (base + 1 + (render x).toUTF8.size)
        h_rest_bound h_rest_match h_rest_close h_rest_vp]
    simp only [ParseResult.ok.injEq]
    constructor
    · rw [Array.push_eq_append, List.toArray_cons]; simp
    · rw [commaPrefix_cons_size]; omega


-- Note: the ByteArray parameter is named `buf` (not `arr`) throughout
-- because `Json.arr` is in scope and would shadow a bare `arr` in patterns.

/-- If bytes `buf[q..]` match `(render v).toUTF8`, then `value` parses `v` there.
The `hstop` hypothesis says the byte immediately after the rendered value is not a number
continuation (digit / `.` / `e`/`E`); it is needed only for the `.num` case but carried
uniformly to enable structural recursion for the `.arr` and `.obj` cases. -/
theorem value_run_at : ∀ (v : Json) (buf : ByteArray) (q : Nat),
    q + (render v).toUTF8.size ≤ buf.size →
    (∀ i, i < (render v).toUTF8.size → buf[q + i]! = (render v).toUTF8[i]!) →
    (q + (render v).toUTF8.size = buf.size ∨
     q + (render v).toUTF8.size < buf.size ∧
       Ascii.isDigit buf[q + (render v).toUTF8.size]! = false ∧
       buf[q + (render v).toUTF8.size]! ≠ 46 ∧
       Ascii.isExp buf[q + (render v).toUTF8.size]! = false) →
    Grip.Json.value.run buf q = .ok v (q + (render v).toUTF8.size)
  | .null, buf, q, hq, hmatch, _ => by
    have hrend : render Json.null = "null" := by simp [render]
    simp only [hrend, show ("null" : String).toUTF8.size = 4 from by decide] at hq hmatch ⊢
    exact value_run_null buf q hq hmatch
  | .bool true, buf, q, hq, hmatch, _ => by
    have hrend : render (Json.bool true) = "true" := by simp [render]
    simp only [hrend, show ("true" : String).toUTF8.size = 4 from by decide] at hq hmatch ⊢
    exact value_run_true buf q hq hmatch
  | .bool false, buf, q, hq, hmatch, _ => by
    have hrend : render (Json.bool false) = "false" := by simp [render]
    simp only [hrend, show ("false" : String).toUTF8.size = 5 from by decide] at hq hmatch ⊢
    exact value_run_false buf q hq hmatch
  | .str s, buf, q, hq, hmatch, _ => by
    have hsize : (render (.str s)).toUTF8.size = 2 + (ebytes s.toList).length :=
      render_str_size s
    rw [hsize] at hq ⊢
    rw [show q + (2 + (ebytes s.toList).length) = q + 1 + (ebytes s.toList).length + 1 from by ring]
    refine value_run_str buf q s (by omega) ?_ ?_ ?_
    · have h0 := hmatch 0 (by omega)
      simp only [Nat.add_zero] at h0
      rwa [render_str_byte0] at h0
    · intro j hj
      have hj' := hmatch (1 + j) (by omega)
      simp only [show q + (1 + j) = q + 1 + j from by ring] at hj'
      rwa [render_str_byte_mid s j hj] at hj'
    · have hn := hmatch (1 + (ebytes s.toList).length) (by omega)
      simp only [show q + (1 + (ebytes s.toList).length) = q + 1 + (ebytes s.toList).length
          from by ring] at hn
      rwa [render_str_byte_close] at hn
  | .num m e, buf, q, hq, hmatch, hstop => by
    have hrn : render (Json.num m e) = renderNumber m e := by simp [render]
    simp only [hrn] at hq hmatch hstop ⊢
    by_cases he : e > Decode.maxExp
    · have hlarge : renderNumber m e = renderNumScientific m e := by
        simp [renderNumber, he]
      rw [hlarge] at hq hmatch hstop ⊢
      exact value_run_num_scientific m e buf q he hq hmatch hstop
    · have hsmall : renderNumber m e = renderNum m e := by simp [renderNumber, he]
      rw [hsmall] at hq hmatch hstop ⊢
      exact value_run_num_at m e buf q hq hmatch hstop
  | .arr xs, buf, q, hq, hmatch, hstop => by
    have hrend : render (Json.arr xs) =
        "[" ++ joinWith "," (xs.attach.toList.map (fun x => render x.1)) ++ "]" := by
      simp [render]
    have hN2 : 2 ≤ (render (Json.arr xs)).toUTF8.size := by
      rw [hrend, toUTF8_append, ByteArray.size_append, toUTF8_append, ByteArray.size_append]
      have h1 : ("[" : String).toUTF8.size = 1 := by decide
      have h2 : ("]" : String).toUTF8.size = 1 := by decide
      omega
    have hqlt : q < buf.size := by omega
    have hbufq! : buf[q]! = 91 := by
      have h0 := hmatch 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [h0, hrend]
      simp only [toUTF8_append]
      have h1 : ("[" : String).toUTF8.size = 1 := by decide
      rw [ba_get!_append_left (by simp only [ByteArray.size_append]; omega)]
      rw [ba_get!_append_left (by decide)]
      decide
    have hbufq : buf[q] = 91 := by rwa [← getElem!_pos buf q hqlt]
    have hws_buf : Ascii.isWs buf[q] = false := by rw [hbufq]; decide
    -- last byte of render arr is ']' = 93; proved by byte position arithmetic
    have hbufN! : buf[q + (render (Json.arr xs)).toUTF8.size - 1]! = 93 := by
      have hNm := hmatch ((render (Json.arr xs)).toUTF8.size - 1) (by omega)
      rw [show q + ((render (Json.arr xs)).toUTF8.size - 1) =
          q + (render (Json.arr xs)).toUTF8.size - 1 from by omega] at hNm
      rw [hNm, hrend]; exact lbracket_last_byte _
    have hch : (GParser.ch '[').run buf q = .ok () (q + 1) :=
      byte_run! 91 buf q hqlt hbufq!
    -- the container body parses xs, closing bracket included
    have harr_body : (Grip.Json.containerBody (fun (a : Array Json) e => a.push e)
        (GParser.fixSelf Grip.Json.valueBody (buf.size - q)) Ascii.rbracket "']'" #[]).run
        buf (q + 1) = .ok xs (q + (render (Json.arr xs)).toUTF8.size) := by
      -- Transfer fixSelf → value via containerBody_agree + fixSelf_eq_value_of_gt
      have h_agree := containerBody_agree (fun (a : Array Json) e => a.push e)
          (GParser.fixSelf Grip.Json.valueBody (buf.size - q)) Grip.Json.value
          Ascii.rbracket "']'" #[] buf (q + 1)
          (fun r hr => fixSelf_eq_value_of_gt buf q r (by omega))
      suffices h_val : (Grip.Json.containerBody (fun (a : Array Json) e => a.push e)
          Grip.Json.value Ascii.rbracket "']'" #[]).run buf (q + 1) =
          .ok xs (q + (render (Json.arr xs)).toUTF8.size) by
        rcases h_fix : (Grip.Json.containerBody (fun (a : Array Json) e => a.push e)
            (GParser.fixSelf Grip.Json.valueBody (buf.size - q))
            Ascii.rbracket "']'" #[]).run buf (q + 1) with ⟨xs', q'⟩ | e
        · rw [h_fix, h_val] at h_agree
          simp only [AgreeOk] at h_agree; obtain ⟨rfl, rfl⟩ := h_agree; rfl
        · rw [h_fix, h_val] at h_agree; exact absurd h_agree (by simp [AgreeOk])
      -- Establish body = joinWith "," (xs.toList.map render)
      have hatt_render : xs.attach.toList.map (fun x => render x.1) = xs.toList.map render := by
        have hcomp : (fun x : {x // x ∈ xs} => render x.1) = render ∘ (fun x => x.1) := by
          ext; rfl
        rw [hcomp, ← List.map_map]; congr 1; simp [Array.attach]
      set body := joinWith "," (xs.toList.map render) with h_body_def
      have hbody_eq : joinWith "," (xs.attach.toList.map (fun x => render x.1)) = body := by
        rw [hatt_render]
      have hbody_size : (render (Json.arr xs)).toUTF8.size = 1 + body.toUTF8.size + 1 := by
        rw [hrend, hbody_eq, toUTF8_append, ByteArray.size_append, toUTF8_append,
            ByteArray.size_append]
        simp only [show ("[":String).toUTF8.size = 1 from by decide,
                   show ("]":String).toUTF8.size = 1 from by decide]
      have hend : q + (render (Json.arr xs)).toUTF8.size = q + 1 + body.toUTF8.size + 1 := by
        omega
      rw [hend]
      -- Body bytes
      have hmatch_body : ∀ j, j < body.toUTF8.size → buf[q + 1 + j]! = body.toUTF8[j]! := by
        intro j hj
        have h := hmatch (1 + j) (by rw [hbody_size]; omega)
        rw [show q + (1 + j) = q + 1 + j from by ring] at h
        rw [h, hrend, hbody_eq]; exact body_byte_j "[" "]" (by decide) body j hj
      -- Byte after body = ']' = 93
      have hbyte_last : buf[q + 1 + body.toUTF8.size]! = 93 := by
        rw [show q + 1 + body.toUTF8.size = q + (render (Json.arr xs)).toUTF8.size - 1
            from by omega]
        exact hbufN!
      have hq1body_lt : q + 1 + body.toUTF8.size < buf.size := by omega
      -- Case on xs.toList
      rcases hxl : xs.toList with _ | ⟨xi, rest_l⟩
      · -- Empty: xs = #[], body = "", value errors at q+1 (byte = ']' = 93)
        have hxs_empty : xs = #[] := by apply Array.ext'; simp [← hxl]
        have hbody_empty : body.toUTF8.size = 0 := by
          rw [h_body_def, hxl, List.map_nil, joinWith]; rfl
        subst hxs_empty
        simp only [hbody_empty, Nat.add_zero]
        have hq1lt : q + 1 < buf.size := by omega
        have hbuf1 : buf[q + 1] = (93 : UInt8) := by
          have h := hbyte_last
          rw [hbody_empty, Nat.add_zero] at h
          rw [← getElem!_pos buf _ hq1lt]; exact h
        have hws1 : Ascii.isWs buf[q + 1] = false := by rw [hbuf1]; decide
        obtain ⟨e, hval_err⟩ : ∃ e, Grip.Json.value.run buf (q + 1) = .error e := by
          rw [Grip.Json.value, fix_run_unroll]; simp only [Grip.Json.valueBody]
          rw [wsDispatch_run_stop _ buf (q + 1) hq1lt hws1, hbuf1]
          simp only [Ascii.lbrace, Ascii.lbracket, Ascii.quote, Ascii.dash]
          rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
            if_neg (by decide), if_neg (by decide), if_neg (by decide),
            if_neg (by decide)]
          simp [clampAdvance, GParser.label, GParser.map, GParser.satisfy]
        have hs1 : scanFwd buf Ascii.isWs (q + 1) = q + 1 := by
          rw [scanFwd, dif_pos hq1lt, if_neg (by rw [hws1]; decide)]
        simp only [Grip.Json.containerBody]
        rw [Grip.Json.bodyFwd]
        simp only [↓reduceIte, hval_err, hs1, dif_pos hq1lt,
          if_pos (show (buf[q + 1] == Ascii.rbracket) = true from by rw [hbuf1]; decide)]
      · -- Non-empty: xs.toList = xi :: rest_l
        -- body = render xi ++ commaPrefix rest_l
        have h_body_cons : body = render xi ++ commaPrefix rest_l := by
          rw [h_body_def, hxl]; exact joinWith_map_render_eq xi rest_l
        -- xs = (xi :: rest_l).toArray = #[xi] ++ rest_l.toArray
        have hxs_eq : xs = #[xi] ++ rest_l.toArray := by apply Array.ext'; simp [hxl]
        -- Match bytes for xi: buf[q+1+j]! = (render xi)[j]!
        have hmatch_xi : ∀ j, j < (render xi).toUTF8.size →
            buf[q + 1 + j]! = (render xi).toUTF8[j]! := by
          intro j hj
          rw [hmatch_body j (by rw [h_body_cons, toUTF8_append, ByteArray.size_append]; omega)]
          rw [h_body_cons, toUTF8_append, ba_get!_append_left hj]
        -- Stop condition for xi (next byte is ',' or ']', both pass)
        have hxi_bound : q + 1 + (render xi).toUTF8.size ≤ buf.size := by
          have h_sz : body.toUTF8.size = (render xi).toUTF8.size +
              (commaPrefix rest_l).toUTF8.size := by
            rw [h_body_cons, toUTF8_append, ByteArray.size_append]
          omega
        have hstop_xi : q + 1 + (render xi).toUTF8.size = buf.size ∨
            (q + 1 + (render xi).toUTF8.size < buf.size ∧
             Ascii.isDigit buf[q + 1 + (render xi).toUTF8.size]! = false ∧
             buf[q + 1 + (render xi).toUTF8.size]! ≠ 46 ∧
             Ascii.isExp buf[q + 1 + (render xi).toUTF8.size]! = false) := by
          have hcp_size : body.toUTF8.size = (render xi).toUTF8.size +
              (commaPrefix rest_l).toUTF8.size := by
            rw [h_body_cons, toUTF8_append, ByteArray.size_append]
          have hpos_lt : q + 1 + (render xi).toUTF8.size < buf.size := by omega
          -- Determine the byte at the stop position
          have hbyte : buf[q + 1 + (render xi).toUTF8.size]! = 44 ∨
                       buf[q + 1 + (render xi).toUTF8.size]! = 93 := by
            rcases hrl : rest_l with _ | ⟨w, ws⟩
            · -- rest_l = []: stop pos = q+1+body.size, byte is ']' = 93
              right
              have : q + 1 + (render xi).toUTF8.size = q + 1 + body.toUTF8.size := by
                have : (commaPrefix ([] : List Json)).toUTF8.size = 0 := rfl
                rw [hrl] at hcp_size; simp only [this, Nat.add_zero] at hcp_size; omega
              rw [this]; exact hbyte_last
            · -- rest_l = w :: ws: byte is ',' = 44
              left
              have hconspos : 0 < (commaPrefix (w :: ws)).toUTF8.size := by
                rw [commaPrefix_cons_size]; omega
              have hbound_xi : (render xi).toUTF8.size < body.toUTF8.size := by
                rw [hrl] at hcp_size; omega
              rw [hmatch_body (render xi).toUTF8.size hbound_xi,
                  h_body_cons, hrl, toUTF8_append,
                  ba_get!_append_right (le_refl _)
                    (by rw [ByteArray.size_append]; rw [hrl] at hcp_size; omega),
                  Nat.sub_self]
              exact commaPrefix_byte_comma w ws
          rcases hbyte with h | h
          · right; exact ⟨hpos_lt, by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
          · right; exact ⟨hpos_lt, by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
        -- value parses xi
        have hxi_val := value_run_at xi buf (q + 1) hxi_bound hmatch_xi hstop_xi
        -- commaPrefix rest_l bytes
        have hcp_size : (render xi).toUTF8.size + (commaPrefix rest_l).toUTF8.size =
            body.toUTF8.size := by
          rw [h_body_cons, toUTF8_append, ByteArray.size_append]
        have hrest_bound : q + 1 + (render xi).toUTF8.size + (commaPrefix rest_l).toUTF8.size ≤
            buf.size := by omega
        have hrest_match : ∀ j, j < (commaPrefix rest_l).toUTF8.size →
            buf[q + 1 + (render xi).toUTF8.size + j]! = (commaPrefix rest_l).toUTF8[j]! := by
          intro j hj
          have hm := hmatch_body ((render xi).toUTF8.size + j) (by omega)
          rw [show q + 1 + ((render xi).toUTF8.size + j) = q + 1 + (render xi).toUTF8.size + j
              from by ring] at hm
          rw [hm, h_body_cons, toUTF8_append,
              ba_get!_append_right (by omega) (by rw [ByteArray.size_append]; omega),
              Nat.add_sub_cancel_left]
        have hrest_close : buf[q + 1 + (render xi).toUTF8.size +
            (commaPrefix rest_l).toUTF8.size]! = 93 := by
          rw [show q + 1 + (render xi).toUTF8.size + (commaPrefix rest_l).toUTF8.size =
              q + 1 + body.toUTF8.size from by omega]
          exact hbyte_last
        -- h_vp: for each y ∈ rest_l, value parses y
        have hrest_vp : ∀ y ∈ rest_l, ∀ (p : Nat),
            p + (render y).toUTF8.size ≤ buf.size →
            (∀ j, j < (render y).toUTF8.size → buf[p + j]! = (render y).toUTF8[j]!) →
            (p + (render y).toUTF8.size = buf.size ∨
             p + (render y).toUTF8.size < buf.size ∧
               Ascii.isDigit buf[p + (render y).toUTF8.size]! = false ∧
               buf[p + (render y).toUTF8.size]! ≠ 46 ∧
               Ascii.isExp buf[p + (render y).toUTF8.size]! = false) →
            Grip.Json.value.run buf p = .ok y (p + (render y).toUTF8.size) := by
          intro y hy p hp hm hsp
          exact value_run_at y buf p hp hm hsp
        -- Head element, then the committed tail loop through the closing bracket
        simp only [Grip.Json.containerBody]
        rw [Grip.Json.bodyFwd]
        simp only [↓reduceIte, hxi_val]
        rw [dif_pos (show q + 1 < q + 1 + (render xi).toUTF8.size ∧
            q + 1 + (render xi).toUTF8.size ≤ buf.size from
              ⟨Grip.Json.value.cwit hxi_val, hxi_bound⟩)]
        rw [bodyFwd_comma_value_run rest_l buf (#[].push xi) (q + 1 + (render xi).toUTF8.size)
            (by omega) hrest_match hrest_close hrest_vp]
        simp only [ParseResult.ok.injEq]
        refine ⟨?_, by omega⟩
        rw [hxs_eq]; rfl
    have harr_map := map_run_ok Json.arr _ buf (q + 1) xs
        (q + (render (Json.arr xs)).toUTF8.size) harr_body
    rw [value, fix_run_unroll]
    simp only [valueBody]
    rw [wsDispatch_run_stop _ buf q hqlt hws_buf]
    simp only [Ascii.lbrace, Ascii.lbracket]
    have h_notbrace : ¬ ((buf[q] == (123 : UInt8)) = true) := by rw [hbufq]; decide
    have h_bracket  :   ((buf[q] == (91  : UInt8)) = true) := by rw [hbufq]; decide
    rw [if_neg h_notbrace, if_pos h_bracket]
    rw [seqR_run _ _ buf q () (q + 1) (Json.arr xs) _ hch harr_map]
    exact clampAdvance_ok buf q (by omega) (by omega)
  | .obj kvs, buf, q, hq, hmatch, hstop => by
    have hrend : render (Json.obj kvs) =
        "{" ++ joinWith ","
          (kvs.attach.toList.map (fun ⟨(k, j), _h⟩ =>
            "\"" ++ escape k ++ "\":" ++ render j)) ++ "}" := by
      simp [render]
    have hN2 : 2 ≤ (render (Json.obj kvs)).toUTF8.size := by
      rw [hrend, toUTF8_append, ByteArray.size_append, toUTF8_append, ByteArray.size_append]
      have h1 : ("{" : String).toUTF8.size = 1 := by decide
      have h2 : ("}" : String).toUTF8.size = 1 := by decide
      omega
    have hqlt : q < buf.size := by omega
    have hbufq! : buf[q]! = 123 := by
      have h0 := hmatch 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [h0, hrend]
      simp only [toUTF8_append]
      have h1 : ("{" : String).toUTF8.size = 1 := by decide
      rw [ba_get!_append_left (by simp only [ByteArray.size_append]; omega)]
      rw [ba_get!_append_left (by decide)]
      decide
    have hbufq : buf[q] = 123 := by rwa [← getElem!_pos buf q hqlt]
    have hws_buf : Ascii.isWs buf[q] = false := by rw [hbufq]; decide
    -- last byte of render obj is '}' = 125
    have hbufN! : buf[q + (render (Json.obj kvs)).toUTF8.size - 1]! = 125 := by
      have hNm := hmatch ((render (Json.obj kvs)).toUTF8.size - 1) (by omega)
      rw [show q + ((render (Json.obj kvs)).toUTF8.size - 1) =
          q + (render (Json.obj kvs)).toUTF8.size - 1 from by omega] at hNm
      rw [hNm, hrend]; exact lbrace_last_byte _
    have hch : (GParser.ch '{').run buf q = .ok () (q + 1) :=
      byte_run! 123 buf q hqlt hbufq!
    -- ws after '{': render has no whitespace, so ws consumes 0 bytes
    have hws_step : (GParser.ws).run buf (q + 1) = .ok 0 (q + 1) := by
      simp only [GParser.ws]
      apply takeWhile_run
      · intro i hi; omega
      · right; refine ⟨by omega, ?_⟩
        -- buf[q+1] is '"' (non-empty obj) or '}' (empty obj); neither is whitespace
        simp only [Nat.add_zero]
        rw [hmatch 1 (by omega), hrend]
        -- helper: first byte of joinWith "," (s :: tail) = first byte of s
        have hjw0 : ∀ (s : String) (tail : List String),
            0 < s.toUTF8.size →
            (joinWith "," (s :: tail)).toUTF8[0]! = s.toUTF8[0]! := by
          intro s tail hs
          cases tail with
          | nil => simp [joinWith]
          | cons t more =>
            simp only [joinWith]
            rw [String.append_assoc, toUTF8_append, ba_get!_append_left hs]
        rcases kvs.attach.toList with _ | ⟨⟨⟨k0, v0⟩, _⟩, rest⟩
        · simp only [List.map_nil, joinWith]; decide
        · simp only [List.map_cons]
          set e0 := "\"" ++ escape k0 ++ "\":" ++ render v0
          have he0_pos : 0 < e0.toUTF8.size := by
            simp only [e0, toUTF8_append, ByteArray.size_append]
            have : ("\"" : String).toUTF8.size = 1 := by decide
            omega
          have hbody_pos : 0 < (joinWith ","
              (e0 :: rest.map (fun ⟨(k, j), _h⟩ =>
                "\"" ++ escape k ++ "\":" ++ render j))).toUTF8.size := by
            cases rest.map (fun ⟨(k, j), _h⟩ => "\"" ++ escape k ++ "\":" ++ render j) with
            | nil =>
              simp only [joinWith]
              have hc : (",":String).toUTF8.size = 1 := by decide
              have he : ("":String).toUTF8.size = 0 := by decide
              omega
            | cons e1 more => simp only [joinWith, toUTF8_append, ByteArray.size_append]; omega
          rw [body_byte_j "{" "}" (by decide) _ 0 hbody_pos,
              hjw0 e0 _ he0_pos]
          simp only [e0, String.append_assoc]
          rw [str_prepend_byte0]; decide
    -- the container body parses kvs, closing brace included
    have hobj_body : (Grip.Json.containerBody (fun (a : Array (String × Json)) x => a.push x)
        (GParser.seqR GParser.ws
          (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
            (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'")
              (GParser.fixSelf Grip.Json.valueBody (buf.size - q)))))
        Ascii.rbrace "'}'" #[]).run buf (q + 1) =
        .ok kvs (q + (render (Json.obj kvs)).toUTF8.size) := by
      -- Transfer fixSelf → value via containerBody_agree + fixSelf_eq_value_of_gt
      have h_agree := containerBody_agree (fun (a : Array (String × Json)) x => a.push x)
          (GParser.seqR GParser.ws
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'")
                (GParser.fixSelf Grip.Json.valueBody (buf.size - q)))))
          (GParser.seqR GParser.ws
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'") Grip.Json.value)))
          Ascii.rbrace "'}'" #[] buf (q + 1)
          (fun r hr => seqR_ws_pair_agree _ _ buf q r (by omega)
            (fun q' hq' => fixSelf_eq_value_of_gt buf q q' hq'))
      suffices h_val : (Grip.Json.containerBody (fun (a : Array (String × Json)) x => a.push x)
          (GParser.seqR GParser.ws
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'") Grip.Json.value)))
          Ascii.rbrace "'}'" #[]).run buf (q + 1) =
          .ok kvs (q + (render (Json.obj kvs)).toUTF8.size) by
        rcases h_fix : (Grip.Json.containerBody (fun (a : Array (String × Json)) x => a.push x)
            (GParser.seqR GParser.ws
              (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
                (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'")
                  (GParser.fixSelf Grip.Json.valueBody (buf.size - q)))))
            Ascii.rbrace "'}'" #[]).run buf (q + 1) with ⟨kvs', q'⟩ | e
        · rw [h_fix, h_val] at h_agree
          simp only [AgreeOk] at h_agree; obtain ⟨rfl, rfl⟩ := h_agree; rfl
        · rw [h_fix, h_val] at h_agree; exact absurd h_agree (by simp [AgreeOk])
      -- Simplify attach.toList.map to kvs.toList.map renderKV
      have hatt_renderKV : kvs.attach.toList.map (fun ⟨(k, j), _h⟩ =>
          "\"" ++ escape k ++ "\":" ++ render j)
          = kvs.toList.map renderKV := by
        have hmap_eq : kvs.attach.toList.map (fun ⟨(k, j), _h⟩ =>
            "\"" ++ escape k ++ "\":" ++ render j) =
            kvs.attach.toList.map (fun x : {x : String × Json // x ∈ kvs} => renderKV x) :=
          List.map_congr_left (fun ⟨⟨k, j⟩, _⟩ _ => by
            simp [renderKV, render, show ("\":" : String) = "\"" ++ ":" from by decide,
                  String.append_assoc])
        rw [hmap_eq, Array.toList_attach, List.attachWith_map_val]
      set body := joinWith "," (kvs.toList.map renderKV) with h_body_def
      have hbody_eq : joinWith "," (kvs.attach.toList.map (fun ⟨(k, j), _h⟩ =>
          "\"" ++ escape k ++ "\":" ++ render j)) = body := by rw [hatt_renderKV]
      have hbody_size : (render (Json.obj kvs)).toUTF8.size = 1 + body.toUTF8.size + 1 := by
        rw [hrend, hbody_eq, toUTF8_append, ByteArray.size_append, toUTF8_append,
            ByteArray.size_append]
        simp only [show ("{":String).toUTF8.size = 1 from by decide,
                   show ("}":String).toUTF8.size = 1 from by decide]
      have hend : q + (render (Json.obj kvs)).toUTF8.size = q + 1 + body.toUTF8.size + 1 := by
        omega
      rw [hend]
      have hmatch_body : ∀ j, j < body.toUTF8.size → buf[q + 1 + j]! = body.toUTF8[j]! := by
        intro j hj
        have h := hmatch (1 + j) (by rw [hbody_size]; omega)
        rw [show q + (1 + j) = q + 1 + j from by ring] at h
        rw [h, hrend, hbody_eq]; exact body_byte_j "{" "}" (by decide) body j hj
      have hbyte_last : buf[q + 1 + body.toUTF8.size]! = 125 := by
        rw [show q + 1 + body.toUTF8.size = q + (render (Json.obj kvs)).toUTF8.size - 1
            from by omega]
        exact hbufN!
      have hq1body_lt : q + 1 + body.toUTF8.size < buf.size := by omega
      -- Case on kvs.toList
      rcases hkvl : kvs.toList with _ | ⟨⟨k0, v0⟩, rest_kvs⟩
      · -- Empty kvs: pure #[] branch
        have hkvs_empty : kvs = #[] := by apply Array.ext'; simp [← hkvl]
        have hbody_empty : body.toUTF8.size = 0 := by
          rw [h_body_def, hkvl, List.map_nil, joinWith]; rfl
        subst hkvs_empty
        simp only [hbody_empty, Nat.add_zero]
        have hq1lt : q + 1 < buf.size := by omega
        have hbuf1 : buf[q + 1] = (125 : UInt8) := by
          have h := hbyte_last; rw [hbody_empty, Nat.add_zero] at h
          rw [← getElem!_pos buf _ hq1lt]; exact h
        obtain ⟨e, hjstr_err⟩ : ∃ e, Grip.Json.jstr.run buf (q + 1) = .error e := by
          simp only [Grip.Json.jstr]; rw [dif_pos hq1lt]
          have hne34 : ¬ (buf[q + 1] == (34 : UInt8)) = true := by rw [hbuf1]; decide
          rw [if_neg hne34]; exact ⟨_, rfl⟩
        have helem_err : (GParser.seqR GParser.ws
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'") Grip.Json.value))).run
            buf (q + 1) =
            .error e := by
          simp only [GParser.seqR, GParser.map2, hws_step, hjstr_err]
        have hs1 : scanFwd buf Ascii.isWs (q + 1) = q + 1 := by
          rw [scanFwd, dif_pos hq1lt, if_neg (by rw [hbuf1]; decide)]
        simp only [Grip.Json.containerBody]
        rw [Grip.Json.bodyFwd]
        simp only [↓reduceIte, helem_err, hs1, dif_pos hq1lt,
          if_pos (show (buf[q + 1] == Ascii.rbrace) = true from by rw [hbuf1]; decide)]
      · -- Non-empty: kvs.toList = (k0, v0) :: rest_kvs
        have h_body_cons : body = renderKV (k0, v0) ++ commaPrefixKV rest_kvs := by
          rw [h_body_def, hkvl]; exact joinWith_map_renderKV_eq (k0, v0) rest_kvs
        have hkvs_eq : kvs = #[(k0, v0)] ++ rest_kvs.toArray := by
          apply Array.ext'; simp [hkvl]
        have hrkv_size : (renderKV (k0, v0)).toUTF8.size =
            2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size :=
          renderKV_size k0 v0
        have hsk_size : (render (.str k0)).toUTF8.size = 2 + (ebytes k0.toList).length :=
          render_str_size k0
        have hbody_sz : body.toUTF8.size =
            (renderKV (k0, v0)).toUTF8.size + (commaPrefixKV rest_kvs).toUTF8.size := by
          rw [h_body_cons, toUTF8_append, ByteArray.size_append]
        -- Bytes of renderKV (k0, v0) at buf[q+1+j]
        have hmatch_kv : ∀ j, j < (renderKV (k0, v0)).toUTF8.size →
            buf[q + 1 + j]! = (renderKV (k0, v0)).toUTF8[j]! := by
          intro j hj
          rw [hmatch_body j (by omega), h_body_cons, toUTF8_append, ba_get!_append_left hj]
        have hkv_bound : q + 1 + (renderKV (k0, v0)).toUTF8.size ≤ buf.size := by omega
        -- buf[q+1]! = 34 (opening quote)
        have hq1_byte! : buf[q + 1]! = 34 := by
          rw [hmatch_kv 0 (by rw [hrkv_size]; omega)]; exact renderKV_byte0 (k0, v0)
        -- Key body bytes
        have hcontent_k : ∀ j, j < (ebytes k0.toList).length →
            buf[q + 1 + 1 + j]! = (ebytes k0.toList)[j]! := by
          intro j hj
          rw [show q + 1 + 1 + j = q + 1 + (1 + j) from by ring,
              hmatch_kv (1 + j) (by rw [hrkv_size]; omega)]
          simp only [renderKV, toUTF8_append]
          rw [ba_get!_append_left (by rw [ByteArray.size_append, hsk_size]; omega)]
          rw [ba_get!_append_left (by rw [hsk_size]; omega)]
          exact render_str_byte_mid k0 j hj
        -- Closing quote
        have hclose_k : buf[q + 1 + 1 + (ebytes k0.toList).length]! = 34 := by
          rw [show q + 1 + 1 + (ebytes k0.toList).length =
              q + 1 + (1 + (ebytes k0.toList).length) from by ring,
              hmatch_kv (1 + (ebytes k0.toList).length) (by rw [hrkv_size]; omega)]
          simp only [renderKV, toUTF8_append]
          rw [ba_get!_append_left (by rw [ByteArray.size_append, hsk_size]; omega)]
          rw [ba_get!_append_left (by rw [hsk_size]; omega)]
          exact render_str_byte_close k0
        -- jstr bound and parse
        have hjstr_bound : q + 1 + 1 + (ebytes k0.toList).length < buf.size := by
          rw [hrkv_size] at hkv_bound; omega
        have hjstr_ok : Grip.Json.jstr.run buf (q + 1) =
            .ok k0 (q + 1 + 1 + (ebytes k0.toList).length + 1) :=
          jstr_run buf (q + 1) k0 hjstr_bound hq1_byte! hcontent_k hclose_k
        -- Colon position: q + 1 + 2 + (ebytes k0.toList).length
        have hcolon_pos_lt : q + 1 + 2 + (ebytes k0.toList).length < buf.size := by
          rw [hrkv_size] at hkv_bound; omega
        have hcolon_byte! : buf[q + 1 + 2 + (ebytes k0.toList).length]! = 58 := by
          rw [show q + 1 + 2 + (ebytes k0.toList).length =
              q + 1 + (2 + (ebytes k0.toList).length) from by ring,
              hmatch_kv (2 + (ebytes k0.toList).length) (by rw [hrkv_size]; omega)]
          simp only [renderKV, toUTF8_append]
          have hc0 : (":":String).toUTF8.size = 1 := by decide
          rw [ba_get!_append_left (by rw [ByteArray.size_append, hsk_size, hc0]; omega)]
          rw [ba_get!_append_right (by omega) (by rw [ByteArray.size_append, hsk_size, hc0]; omega)]
          rw [hsk_size, Nat.sub_self]
          decide
        have hcolon_byte : buf[q + 1 + 2 + (ebytes k0.toList).length] = (58 : UInt8) := by
          rwa [← getElem!_pos buf _ hcolon_pos_lt]
        have hcolon_ws : Ascii.isWs buf[q + 1 + 2 + (ebytes k0.toList).length] = false := by
          rw [hcolon_byte]; decide
        -- wsByte colon succeeds
        have hwscolon : (Grip.Json.wsByte Ascii.colon "':'").run buf (q + 1 + 2 +
            (ebytes k0.toList).length) =
            .ok () (q + 1 + 2 + (ebytes k0.toList).length + 1) :=
          wsByte_run_stop Ascii.colon "':'" buf _ hcolon_pos_lt hcolon_ws (by rw [hcolon_byte]; rfl)
        -- Value bytes at q + 1 + 3 + (ebytes k0.toList).length
        have hv0_start : q + 1 + 2 + (ebytes k0.toList).length + 1 =
            q + 1 + (2 + (ebytes k0.toList).length + 1) := by ring
        have hv0_bound : q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size ≤
            buf.size := by
          rw [hrkv_size] at hkv_bound; omega
        have hmatch_v0 : ∀ j, j < (render v0).toUTF8.size →
            buf[q + 1 + 2 + (ebytes k0.toList).length + 1 + j]! = (render v0).toUTF8[j]! := by
          intro j hj
          rw [show q + 1 + 2 + (ebytes k0.toList).length + 1 + j =
              q + 1 + (2 + (ebytes k0.toList).length + 1 + j) from by ring,
              hmatch_kv (2 + (ebytes k0.toList).length + 1 + j) (by rw [hrkv_size]; omega)]
          simp only [renderKV, toUTF8_append]
          have hc0 : (":":String).toUTF8.size = 1 := by decide
          rw [ba_get!_append_right (by rw [ByteArray.size_append, hsk_size, hc0]; omega)
                                   (by rw [ByteArray.size_append, ByteArray.size_append, hsk_size,
                                       hc0]; omega)]
          congr 1
          rw [ByteArray.size_append, hsk_size, hc0]
          omega
        -- Stop condition for v0 (next byte is ',' or '}', not digit/dot/exp)
        have hstop_v0 : q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size =
            buf.size ∨
            (q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size < buf.size ∧
             Ascii.isDigit buf[q + 1 + 2 + (ebytes k0.toList).length + 1 +
                 (render v0).toUTF8.size]! = false ∧
             buf[q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size]! ≠ 46 ∧
             Ascii.isExp buf[q + 1 + 2 + (ebytes k0.toList).length + 1 +
                 (render v0).toUTF8.size]! = false) := by
          have hpos_eq : q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size =
              q + 1 + (renderKV (k0, v0)).toUTF8.size := by rw [hrkv_size]; ring
          have hpos_lt : q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size <
              buf.size := by
            omega
          have hbyte_after : buf[q + 1 + 2 + (ebytes k0.toList).length + 1 +
              (render v0).toUTF8.size]! =
              44 ∨ buf[q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size]! =
                  125 := by
            rcases hrest : rest_kvs with _ | ⟨kv2, rest2⟩
            · -- rest_kvs = []: byte is '}' (125)
              right; rw [hpos_eq]
              have : q + 1 + (renderKV (k0, v0)).toUTF8.size = q + 1 + body.toUTF8.size := by
                rw [hbody_sz, hrest, commaPrefixKV]; simp
              rw [this]; exact hbyte_last
            · -- rest_kvs non-empty: byte is ',' (44)
              left; rw [hpos_eq]
              have hcp_pos : 0 < (commaPrefixKV rest_kvs).toUTF8.size := by
                rw [hrest, commaPrefixKV_cons_size]; omega
              rw [hmatch_body (renderKV (k0, v0)).toUTF8.size (by rw [hbody_sz]; omega),
                  h_body_cons, toUTF8_append,
                  ba_get!_append_right (le_refl _) (by rw [ByteArray.size_append]; omega),
                  Nat.sub_self, hrest]
              exact commaPrefixKV_byte_comma kv2 rest2
          rcases hbyte_after with h | h
          · right; exact ⟨hpos_lt, by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
          · right; exact ⟨hpos_lt, by rw [h]; decide, by rw [h]; decide, by rw [h]; decide⟩
        -- value parses v0
        have hv0_val := value_run_at v0 buf (q + 1 + 2 + (ebytes k0.toList).length + 1)
            hv0_bound hmatch_v0 hstop_v0
        -- map2 jstr (seqR colon value) parses (k0, v0)
        have hkv0_val : (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
            (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'") Grip.Json.value)).run buf (q + 1) =
            .ok (k0, v0) (q + 1 + (renderKV (k0, v0)).toUTF8.size) := by
          have hq1_lt_buf : q + 1 + 1 + (ebytes k0.toList).length + 1 ≤ buf.size := by omega
          rw [show q + 1 + (renderKV (k0, v0)).toUTF8.size =
              q + 1 + 2 + (ebytes k0.toList).length + 1 + (render v0).toUTF8.size from by
            rw [hrkv_size]; ring]
          have h_seqR := seqR_run (Grip.Json.wsByte Ascii.colon "':'") Grip.Json.value
              buf (q + 1 + 2 + (ebytes k0.toList).length)
              () (q + 1 + 2 + (ebytes k0.toList).length + 1)
              v0 _ hwscolon hv0_val
          exact map2_run (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'") Grip.Json.value)
              buf (q + 1) k0 (q + 1 + 2 + (ebytes k0.toList).length) v0 _
              (by convert hjstr_ok using 2; ring) h_seqR
        -- commaPrefixKV rest_kvs bytes
        have hcp_bound :
            (q + 1 + (renderKV (k0, v0)).toUTF8.size) + (commaPrefixKV rest_kvs).toUTF8.size ≤
                buf.size :=
          by omega
        have hmatch_cp : ∀ j, j < (commaPrefixKV rest_kvs).toUTF8.size →
            buf[(q + 1 + (renderKV (k0, v0)).toUTF8.size) + j]! =
                (commaPrefixKV rest_kvs).toUTF8[j]! := by
          intro j hj
          rw [show (q + 1 + (renderKV (k0, v0)).toUTF8.size) + j = q + 1 + ((renderKV (k0,
              v0)).toUTF8.size + j) from by ring]
          rw [hmatch_body ((renderKV (k0, v0)).toUTF8.size + j) (by omega)]
          rw [h_body_cons, toUTF8_append,
              ba_get!_append_right (by omega) (by rw [ByteArray.size_append]; omega),
              Nat.add_sub_cancel_left]
        have hcp_close : buf[(q + 1 + (renderKV (k0, v0)).toUTF8.size) +
            (commaPrefixKV rest_kvs).toUTF8.size]! = 125 := by
          rw [show (q + 1 + (renderKV (k0, v0)).toUTF8.size) +
              (commaPrefixKV rest_kvs).toUTF8.size = q + 1 + body.toUTF8.size from by omega]
          exact hbyte_last
        -- h_kvp: for each kv2 ∈ rest_kvs, (map2 jstr (seqR colon value)) parses kv2
        have h_kvp : ∀ kv2 ∈ rest_kvs, ∀ (p : Nat),
            p + (renderKV kv2).toUTF8.size ≤ buf.size →
            (∀ j, j < (renderKV kv2).toUTF8.size → buf[p + j]! = (renderKV kv2).toUTF8[j]!) →
            (p + (renderKV kv2).toUTF8.size = buf.size ∨
             (p + (renderKV kv2).toUTF8.size < buf.size ∧
              Ascii.isDigit buf[p + (renderKV kv2).toUTF8.size]! = false ∧
              buf[p + (renderKV kv2).toUTF8.size]! ≠ 46 ∧
              Ascii.isExp buf[p + (renderKV kv2).toUTF8.size]! = false)) →
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'") Grip.Json.value)).run buf p =
              .ok kv2 (p + (renderKV kv2).toUTF8.size) := by
          intro ⟨k2, v2⟩ hkv2 p hp hmatch2 hstop_kv2
          have hrk2 : renderKV (k2, v2) = render (.str k2) ++ ":" ++ render v2 := rfl
          have hsk2 : (render (.str k2)).toUTF8.size = 2 + (ebytes k2.toList).length :=
              render_str_size k2
          have hrk2_size : (renderKV (k2, v2)).toUTF8.size = 2 + (ebytes k2.toList).length + 1 +
              (render v2).toUTF8.size :=
            renderKV_size k2 v2
          have hq2! : p + (2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size) ≤
              buf.size := by
            rwa [← hrk2_size]
          have hbound2 : p + 1 + (ebytes k2.toList).length < buf.size := by omega
          have h34_2 : buf[p]! = 34 := by
            have h := hmatch2 0 (by rw [hrk2_size]; omega)
            simp only [Nat.add_zero] at h
            rw [h]; exact renderKV_byte0 (k2, v2)
          have hcont2 : ∀ j, j < (ebytes k2.toList).length → buf[p + 1 + j]! =
              (ebytes k2.toList)[j]! := by
            intro j hj
            rw [show p + 1 + j = p + (1 + j) from by ring,
                hmatch2 (1 + j) (by rw [hrk2_size]; omega)]
            simp only [renderKV, toUTF8_append]
            rw [ba_get!_append_left (by rw [ByteArray.size_append, hsk2]; omega)]
            rw [ba_get!_append_left (by rw [hsk2]; omega)]
            exact render_str_byte_mid k2 j hj
          have hclose2 : buf[p + 1 + (ebytes k2.toList).length]! = 34 := by
            rw [show p + 1 + (ebytes k2.toList).length = p + (1 + (ebytes k2.toList).length) from
                by ring,
                hmatch2 (1 + (ebytes k2.toList).length) (by rw [hrk2_size]; omega)]
            simp only [renderKV, toUTF8_append]
            rw [ba_get!_append_left (by rw [ByteArray.size_append, hsk2]; omega)]
            rw [ba_get!_append_left (by rw [hsk2]; omega)]
            exact render_str_byte_close k2
          have hjstr2 : Grip.Json.jstr.run buf p = .ok k2 (p + 1 + (ebytes k2.toList).length + 1) :=
            jstr_run buf p k2 hbound2 h34_2 hcont2 hclose2
          have hcolon2_lt : p + 2 + (ebytes k2.toList).length < buf.size := by omega
          have hcolon2! : buf[p + 2 + (ebytes k2.toList).length]! = 58 := by
            rw [show p + 2 + (ebytes k2.toList).length = p + (2 + (ebytes k2.toList).length) from
                by ring,
                hmatch2 (2 + (ebytes k2.toList).length) (by rw [hrk2_size]; omega)]
            simp only [renderKV, toUTF8_append]
            have hc2 : (":":String).toUTF8.size = 1 := by decide
            rw [ba_get!_append_left (by rw [ByteArray.size_append, hsk2, hc2]; omega)]
            rw [ba_get!_append_right (by omega) (by rw [ByteArray.size_append, hsk2, hc2]; omega)]
            rw [hsk2, Nat.sub_self]
            decide
          have hcolon2 : buf[p + 2 + (ebytes k2.toList).length] = (58 : UInt8) := by
            rwa [← getElem!_pos buf _ hcolon2_lt]
          have hwscolon2 : (Grip.Json.wsByte Ascii.colon "':'").run buf (p + 2 +
              (ebytes k2.toList).length) =
              .ok () (p + 2 + (ebytes k2.toList).length + 1) :=
            wsByte_run_stop Ascii.colon "':'" buf _ hcolon2_lt (by rw [hcolon2]; decide)
              (by rw [hcolon2]; rfl)
          have hv2_bound : p + 2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size ≤
              buf.size := by
            omega
          have hmatch_v2 : ∀ j, j < (render v2).toUTF8.size →
              buf[p + 2 + (ebytes k2.toList).length + 1 + j]! = (render v2).toUTF8[j]! := by
            intro j hj
            rw [show p + 2 + (ebytes k2.toList).length + 1 + j =
                p + (2 + (ebytes k2.toList).length + 1 + j) from by ring,
                hmatch2 (2 + (ebytes k2.toList).length + 1 + j) (by rw [hrk2_size]; omega)]
            simp only [renderKV, toUTF8_append]
            have hc2 : (":":String).toUTF8.size = 1 := by decide
            rw [ba_get!_append_right (by rw [ByteArray.size_append, hsk2, hc2]; omega)
                                     (by rw [ByteArray.size_append, ByteArray.size_append, hsk2,
                                         hc2]; omega)]
            congr 1
            rw [ByteArray.size_append, hsk2, hc2]
            omega
          have hstop_v2 : p + 2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size =
              buf.size ∨
              (p + 2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size < buf.size ∧
               Ascii.isDigit buf[p + 2 + (ebytes k2.toList).length + 1 +
                   (render v2).toUTF8.size]! = false ∧
               buf[p + 2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size]! ≠ 46 ∧
               Ascii.isExp buf[p + 2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size]! =
                   false) := by
            rw [show p + 2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size =
                p + (renderKV (k2, v2)).toUTF8.size from by rw [hrk2_size]; ring]
            exact hstop_kv2
          have hv2_val := value_run_at v2 buf (p + 2 + (ebytes k2.toList).length + 1)
              hv2_bound hmatch_v2 hstop_v2
          rw [show p + (renderKV (k2, v2)).toUTF8.size =
              p + 2 + (ebytes k2.toList).length + 1 + (render v2).toUTF8.size from by
            rw [hrk2_size]; ring]
          have h_seqR2 := seqR_run (Grip.Json.wsByte Ascii.colon "':'") Grip.Json.value
              buf (p + 2 + (ebytes k2.toList).length)
              () (p + 2 + (ebytes k2.toList).length + 1)
              v2 _ hwscolon2 hv2_val
          exact map2_run (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'") Grip.Json.value)
              buf p k2 (p + 2 + (ebytes k2.toList).length) v2 _
              (by convert hjstr2 using 2; ring) h_seqR2
        -- Head pair, then the committed tail loop through the closing brace
        have helem0 : (GParser.seqR GParser.ws
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'") Grip.Json.value))).run
            buf (q + 1) =
            .ok (k0, v0) (q + 1 + (renderKV (k0, v0)).toUTF8.size) :=
          seqR_run _ _ _ _ 0 (q + 1) (k0, v0) _ hws_step hkv0_val
        simp only [Grip.Json.containerBody]
        rw [Grip.Json.bodyFwd]
        simp only [↓reduceIte, helem0]
        rw [dif_pos (show q + 1 < q + 1 + (renderKV (k0, v0)).toUTF8.size ∧
            q + 1 + (renderKV (k0, v0)).toUTF8.size ≤ buf.size from
              ⟨by rw [hrkv_size]; omega, by omega⟩)]
        rw [bodyFwd_comma_kv_run
            (GParser.map2 (fun k v => (k, v)) Grip.Json.jstr
              (GParser.seqR (Grip.Json.wsByte Ascii.colon "':'") Grip.Json.value))
            rest_kvs buf (#[].push (k0, v0)) (q + 1 + (renderKV (k0, v0)).toUTF8.size)
            (by omega) hmatch_cp hcp_close h_kvp]
        simp only [ParseResult.ok.injEq]
        refine ⟨?_, by omega⟩
        rw [hkvs_eq]; rfl
    have hobj_map := map_run_ok Json.obj _ buf (q + 1) kvs
        (q + (render (Json.obj kvs)).toUTF8.size) hobj_body
    rw [value, fix_run_unroll]
    simp only [valueBody]
    rw [wsDispatch_run_stop _ buf q hqlt hws_buf]
    simp only [Ascii.lbrace]
    have h_brace : ((buf[q] == (123 : UInt8)) = true) := by rw [hbufq]; decide
    rw [if_pos h_brace]
    rw [seqR_run _ _ buf q () (q + 1) (Json.obj kvs) _ hch hobj_map]
    exact clampAdvance_ok buf q (by omega) (by omega)
termination_by v => sizeOf v
decreasing_by
  · -- arr case xi: xi ∈ xs.toList, hence sizeOf xi < sizeOf (arr xs)
    have hxi_xs : xi ∈ xs := Array.mem_toList_iff.mp (hxl ▸ List.mem_cons.mpr (Or.inl rfl))
    have := Array.sizeOf_lt_of_mem hxi_xs; simp_wf; omega
  · -- arr case y: y ∈ rest_l ⊆ xs.toList, hence sizeOf y < sizeOf (arr xs)
    have hy_xs : y ∈ xs := Array.mem_toList_iff.mp (hxl ▸ List.mem_cons.mpr (Or.inr hy))
    have := Array.sizeOf_lt_of_mem hy_xs; simp_wf; omega
  · -- obj case v0: (k0, v0) is head of kvs.toList, so sizeOf v0 < sizeOf (obj kvs)
    have hkv0_kvs : (k0, v0) ∈ kvs :=
      Array.mem_toList_iff.mp (hkvl ▸ List.mem_cons.mpr (Or.inl rfl))
    have h1 := Array.sizeOf_lt_of_mem hkv0_kvs
    have h2 : sizeOf v0 < sizeOf (k0, v0) := by
      have := @Prod.mk.sizeOf_spec _ _ _ _ k0 v0; omega
    simp_wf; omega
  · -- obj case v2: (k2, v2) ∈ rest_kvs ⊆ kvs.toList, so sizeOf v2 < sizeOf (obj kvs)
    have hkv2_kvs : (k2, v2) ∈ kvs :=
      Array.mem_toList_iff.mp (hkvl ▸ List.mem_cons.mpr (Or.inr hkv2))
    have h1 := Array.sizeOf_lt_of_mem hkv2_kvs
    have h2 : sizeOf v2 < sizeOf (k2, v2) := by
      have := @Prod.mk.sizeOf_spec _ _ _ _ k2 v2; omega
    simp_wf; omega

-- ---------------------------------------------------------------------------
-- 7. parse_render: parse (render v) = ok v for all v
-- ---------------------------------------------------------------------------

/-- Round-trip: parsing the rendering of any JSON value returns that value. -/
theorem parse_render (v : Json) :
    Grip.Json.parse (render v).toUTF8 = .ok v := by
  simp only [Grip.Json.parse, Grip.Json.parser, GParser.parse]
  let arr := (render v).toUTF8
  have hval : Grip.Json.value.run arr 0 = .ok v arr.size := by
    have h := value_run_at v arr 0 (by simp [arr])
        (by intro i hi; simp only [arr, Nat.zero_add]) (Or.inl (by simp [arr]))
    simpa [arr] using h
  have hws : (GParser.ws).run arr arr.size = .ok 0 arr.size :=
    ws_run_end arr arr.size (le_refl _)
  have heof : (GParser.eof).run arr arr.size = .ok () arr.size :=
    eof_run_end arr arr.size (le_refl _)
  rw [seqL_run _ _ arr 0 v arr.size () arr.size hval
    (seqR_run _ _ arr arr.size 0 arr.size () arr.size hws heof)]

end GripProps.Container
