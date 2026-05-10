import Lake
open Lake DSL

package «climbing-calc» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «ClimbingCalc» where
  srcDir := "."

lean_exe «smoke» where
  root := `Smoke
