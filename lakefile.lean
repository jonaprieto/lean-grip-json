import Lake
open Lake DSL

package «grip-json» where
  version := v!"0.1.6"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require grip from git
  "https://github.com/jonaprieto/lean-grip.git" @ "v0.3.5"

@[default_target]
lean_lib «GripJson» where
  roots := #[`GripJson]

lean_lib «Examples» where
  srcDir := "examples"
  roots := #[`Json]

lean_lib «GripJsonTest» where
  srcDir := "test"
  roots := #[`GripJsonTest]

@[test_driver]
lean_exe «tests» where
  root := `Tests
  srcDir := "test"

lean_exe «demo» where
  root := `Demo
  srcDir := "examples"

lean_exe «readme» where
  root := `Readme
  srcDir := "test"

lean_exe «conformance» where
  root := `Conformance
  srcDir := "test"

lean_exe «bench» where
  root := `Bench
  srcDir := "bench"
