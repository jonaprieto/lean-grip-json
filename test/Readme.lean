/-
Copyright (c) 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/
import GripJson

def main : IO Unit := do
  let parsed := Grip.Json.parseString "{\"answer\": 42}"
  if parsed.isOk then pure () else throw <| IO.userError "README example failed"
