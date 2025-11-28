import Lake
open Lake DSL
open System

package «tictactoe» where
  -- add package configuration options here

@[default_target]
lean_lib «Tictactoe» where

@[test_driver]
script test do
  let result ← IO.Process.output
    { cmd := "lake", args := #["env", "lean", "Tests/Main.lean"] }
  IO.print result.stdout
  IO.eprint result.stderr
  pure result.exitCode

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
