import Tictactoe.Main

open IO
open Tictactoe
open Classical

noncomputable section

#eval do
  println "Ply 0: initial state"
  Demo.showState initialState
  match step xCenterBlockStrategy greedyAny [] initialState with
  | none =>
      println "X strategy produced no move (unexpected)."
  | some s1 => do
      println "Ply 1: X move by strategy"
      Demo.showState s1
      match step xCenterBlockStrategy greedyAny [s1] s1 with
      | none =>
          println "O strategy produced no move (possible when board is full)."
      | some s2 => do
          println "Ply 2: O move by strategy"
          Demo.showState s2

end
