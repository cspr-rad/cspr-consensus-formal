import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

require leantest from git
  "https://github.com/cspr-rad/leantest"

package «cspr-consensus» where
  -- add package configuration options here

lean_lib «CsprConsensus» where
  -- add library configuration options here

@[default_target]
lean_exe «cspr-consensus» where
  root := `Main
