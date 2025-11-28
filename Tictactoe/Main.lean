import Tictactoe

open Tictactoe
open Classical

namespace Demo

instance : ToString Player where
  toString
  | Player.X => "X"
  | Player.O => "O"

/-- Render a board as rows of characters. -/
def boardToString (b : Board) : String :=
  let cellToChar (c : Cell) : Char :=
    match c with
    | some Player.X => 'X'
    | some Player.O => 'O'
    | none => '.'
  let rowString (i : Fin 3) : String :=
    let cells := List.ofFn fun j : Fin 3 => cellToChar (b i j)
    String.ofList cells
  String.intercalate "\n" (List.ofFn rowString)

def showState (s : GameState) : IO Unit := do
  IO.println s!"Turn: {s.turn}"
  IO.println (boardToString s.board)

/-- Play xCenterBlockStrategy (X) vs greedyAny (O) until terminal outcome or fuel runs out. -/
noncomputable def playDemo (fuel : Nat := fuelRemaining initialState) : IO Unit := do
  let xStrat := xCenterBlockStrategy
  let oStrat := greedyAny
  let rec loop (n : Nat) (ply : Nat) (hist : History) (s : GameState) : IO Unit := do
    IO.println s!"Ply {ply} / {fuel}"
    showState s
    match boardOutcome s.board with
    | Outcome.ongoing =>
        if n = 0 then
          IO.println "Fuel exhausted."
        else
          match step xStrat oStrat hist s with
          | none =>
              IO.println "Strategy returned no move or illegal move. Stopping."
          | some s' =>
              loop (n - 1) (ply + 1) (s' :: hist) s'
    | Outcome.wins p => IO.println s!"Outcome: {p} wins"
    | Outcome.draw => IO.println "Outcome: draw"
  loop fuel 0 [] initialState

end Demo
