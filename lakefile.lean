import Lake
open Lake DSL
open System

package «tictactoe» where
  -- add package configuration options here

lean_lib «Tictactoe» where

lean_exe «demo» {
  root := `scripts.demo_standalone
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
