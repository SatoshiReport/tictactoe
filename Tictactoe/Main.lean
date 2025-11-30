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

/-- Get move explanation for the current player's move. -/
def getMoveExplanation (hist : Tictactoe.History) (s : Tictactoe.GameState) (pos : Tictactoe.Coord) : String :=
  match s.turn with
  | Tictactoe.Player.X =>
    if pos = Tictactoe.centerCoord then
      "X plays CENTER (optimal opening)"
    else
      -- Check if blocking a threat
      let opponent_threats := Tictactoe.winningLines.filter (fun line =>
        Tictactoe.isImmediateThreat s.board Tictactoe.Player.O line ∧
        pos ∈ Tictactoe.emptiesInLine s.board line)
      if opponent_threats.card > 0 then
        "X BLOCKS O's immediate threat"
      else
        "X plays opportunistically"
  | Tictactoe.Player.O =>
    "O plays greedily (first legal move)"

/-- Play xCenterBlockStrategy (X) vs greedyAny (O) with move explanations. -/
def playDemo (fuel : Nat := Tictactoe.fuelRemaining Tictactoe.initialState) : IO Unit := do
  let xStrat := Tictactoe.xCenterBlockStrategy
  let oStrat := Tictactoe.greedyAny
  IO.println "╔════════════════════════════════════════════╗"
  IO.println "║   Tic-Tac-Toe Game with Formal Proofs    ║"
  IO.println "║  X (center-block) vs O (greedy)           ║"
  IO.println "╚════════════════════════════════════════════╝"
  IO.println ""
  let rec loop (n : Nat) (ply : Nat) (hist : Tictactoe.History) (s : Tictactoe.GameState) : IO Unit := do
    IO.println s!"─── Move {ply} (Remaining: {n}) ───"
    showState s
    IO.println ""
    match Tictactoe.boardOutcome s.board with
    | Tictactoe.Outcome.ongoing =>
        if n = 0 then
          IO.println "Fuel exhausted."
        else
          match Tictactoe.step xStrat oStrat hist s with
          | none =>
              IO.println "Strategy returned no move or illegal move. Stopping."
          | some s' =>
              -- Determine which move was made
              match s.turn with
              | Tictactoe.Player.X =>
                match xStrat hist s with
                | some pos =>
                  IO.println s!"{getMoveExplanation hist s pos}"
                  IO.println ""
                | none => IO.println "X made no move"
              | Tictactoe.Player.O =>
                match oStrat hist s with
                | some pos =>
                  IO.println s!"{getMoveExplanation hist s pos}"
                  IO.println ""
                | none => IO.println "O made no move"
              loop (n - 1) (ply + 1) (s' :: hist) s'
    | Tictactoe.Outcome.wins p =>
      IO.println s!"╔════════════════════════════════════════════╗"
      IO.println s!"║ 🎉 {p} WINS! 🎉"
      IO.println s!"╚════════════════════════════════════════════╝"
    | Tictactoe.Outcome.draw =>
      IO.println s!"╔════════════════════════════════════════════╗"
      IO.println s!"║ 🤝 DRAW - Perfect play from both sides 🤝"
      IO.println s!"╚════════════════════════════════════════════╝"
  loop fuel 0 [] Tictactoe.initialState

end Demo -- End of Demo namespace


