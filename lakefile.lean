import Lake
open Lake DSL

package «VERSEIM-2025» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here
  -- srcDir := "VERSEIM2025"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"928758ac3743dc7f171fc66f450506723896f1c5"

@[default_target]
lean_lib «VERSEIM2025» where
  -- add any library configuration options here
