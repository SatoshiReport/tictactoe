import Lake
open Lake DSL

package «tictactoe» where
  -- add package configuration options here

@[default_target]
lean_lib «Tictactoe» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
