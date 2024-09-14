import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

require LSpec from git
  "https://github.com/argumentcomputer/LSpec"@"main"

package «zug» where
  -- add package configuration options here

lean_lib «Zug» where
  -- add library configuration options here
