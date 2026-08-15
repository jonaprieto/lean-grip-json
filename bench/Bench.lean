/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import Json
import GripJson
import Lean.Data.Json

/-!
# grip-json benchmark harness

The JSON matrix keeps the two important Grip measurements together: the allocation-light
`Grip.Examples.Json.json` validator built from core combinators, and the value-producing
`Grip.Json` DOM parser. Lean's standard DOM parser is the reference for the heavier task.
-/

open Grip

-- partiality: these traversals deliberately mirror the two DOM implementations being measured;
-- changing them to a different traversal would change the benchmark's work profile.
partial def leanJsonLeaves : Lean.Json → Nat
  | .null | .bool _ | .num _ | .str _ => 1
  | .arr xs  => xs.foldl (fun a j => a + leanJsonLeaves j) 0
  | .obj kvs => kvs.foldl (fun a _ v => a + leanJsonLeaves v) 0

-- partiality: this mirrors Grip's DOM traversal for the benchmark's like-for-like comparison.
partial def jsonLeaves : Grip.Json.Json → Nat
  | .null | .bool _ | .num _ _ | .str _ => 1
  | .arr xs  => xs.foldl (fun a j => a + jsonLeaves j) 0
  | .obj kvs => kvs.foldl (fun a kv => a + jsonLeaves kv.2) 0

@[noinline] def parseJson (arr : ByteArray) : Nat :=
  match Grip.Examples.Json.json.run arr 0 with
  | .ok n _  => n
  | .error _ => 0

@[noinline] def parseGripJson (arr : ByteArray) : Nat :=
  match Grip.Json.parser.run arr 0 with
  | .ok j _  => jsonLeaves j
  | .error _ => 0

@[noinline] def parseLeanJson (s : String) : Nat :=
  match Lean.Json.parse s with
  | .ok j    => leanJsonLeaves j
  | .error _ => 0

@[noinline] def barrier (_k : Nat) (b : ByteArray) : ByteArray := b

@[noinline] def barrierStr (_k : Nat) (s : String) : String := s

structure Stats where
  min : Float
  median : Float

-- Report the conventional median: for an even sample count, average the two middle values.
def sampleMs (reps : Nat) (act : Nat → Nat) : IO Stats := do
  let mut samples : Array Float := #[]
  for i in [0:reps] do
    let t0 ← IO.monoNanosNow
    if act i == 0 then IO.eprintln "bench: unexpected zero count"
    let t1 ← IO.monoNanosNow
    samples := samples.push (Float.ofNat (t1 - t0) / 1000000.0)
  let sorted := samples.qsort (· < ·)
  if sorted.isEmpty then return { min := 0.0, median := 0.0 }
  let mid := sorted.size / 2
  let median := if sorted.size % 2 == 0 then
    (sorted[mid - 1]! + sorted[mid]!) / 2.0
  else
    sorted[mid]!
  return { min := sorted[0]!, median := median }

def benchJson
    (name : String)
    (src : ByteArray)
    (expected : Nat)
    (p : ByteArray → Nat) : IO Unit := do
  let count := p src
  if count != expected then
    throw <| IO.userError s!"{name}: expected {expected}, got {count}"
  let s ← sampleMs 20 (fun i => p (barrier i src))
  IO.println s!"{name} count={count} ms={s.min} med={s.median}"

def benchJsonString
    (name : String)
    (src : String)
    (expected : Nat)
    (p : String → Nat) : IO Unit := do
  let count := p src
  if count != expected then
    throw <| IO.userError s!"{name}: expected {expected}, got {count}"
  let s ← sampleMs 20 (fun i => p (barrierStr i src))
  IO.println s!"{name} count={count} ms={s.min} med={s.median} (DOM build)"

def main (args : List String) : IO Unit := do
  let file := args.getD 1 "bench/data/canada.json"
  if args.head? == some "once" then
    let src ← IO.FS.readBinFile file
    IO.println s!"count={parseJson src}"
    return
  for (name, path, expected) in [("canada", "bench/data/canada.json", 111130),
                                 ("citm", "bench/data/citm_catalog.json", 16390),
                                 ("twitter", "bench/data/twitter.json", 11600)] do
    let bytes ← IO.FS.readBinFile path
    let string ← IO.FS.readFile path
    benchJson s!"grip {name}" bytes expected parseJson
    benchJson s!"grip.json {name}" bytes expected parseGripJson
    benchJsonString s!"lean.json {name}" string expected parseLeanJson
