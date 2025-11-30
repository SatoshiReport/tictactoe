import Tictactoe.Game
import Tictactoe.Strategy

open IO
-- NOTE: Do not use "open Tictactoe" as it causes runtime code generation issues
open Classical

namespace Demo

instance : ToString Tictactoe.Player where
  toString
  | Tictactoe.Player.X => "X"
  | Tictactoe.Player.O => "O"

/-- Render a board as rows of characters. -/
def boardToString (b : Tictactoe.Board) : String :=
  let cellToChar (c : Tictactoe.Cell) : Char :=
    match c with
    | some Tictactoe.Player.X => 'X'
    | some Tictactoe.Player.O => 'O'
    | none => '.'
  let rowString (i : Fin 3) : String :=
    let cells := List.ofFn fun j : Fin 3 => cellToChar (b i j)
    String.ofList cells
  String.intercalate "\n" (List.ofFn rowString)

def showState (s : Tictactoe.GameState) : IO Unit := do
  IO.println s!"Turn: {s.turn}"
  IO.println (boardToString s.board)

/-- Play xCenterBlockStrategy (X) vs greedyAny (O) until terminal outcome or fuel runs out. -/
def playDemo (fuel : Nat := Tictactoe.fuelRemaining Tictactoe.initialState) : IO Unit := do
  let xStrat := Tictactoe.xCenterBlockStrategy
  let oStrat := Tictactoe.greedyAny
  let rec loop (n : Nat) (ply : Nat) (hist : Tictactoe.History) (s : Tictactoe.GameState) : IO Unit := do
    IO.println s!"Ply {ply} / {fuel}"
    showState s
    match Tictactoe.boardOutcome s.board with
    | Tictactoe.Outcome.ongoing =>
        if n = 0 then
          IO.println "Fuel exhausted."
        else
          match Tictactoe.step xStrat oStrat hist s with
          | none =>
              IO.println "Strategy returned no move or illegal move. Stopping."
          | some s' =>
              loop (n - 1) (ply + 1) (s' :: hist) s'
    | Tictactoe.Outcome.wins p => IO.println s!"Outcome: {p} wins"
    | Tictactoe.Outcome.draw => IO.println "Outcome: draw"
  loop fuel 0 [] Tictactoe.initialState

end Demo -- End of Demo namespace


