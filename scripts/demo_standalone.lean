/-
  Standalone Tic-Tac-Toe demo - no formalization imports
  This avoids the classical logic IR compilation issues
-/

inductive Player
  | X
  | O
  deriving DecidableEq, Repr

instance : ToString Player where
  toString
  | Player.X => "X"
  | Player.O => "O"

abbrev Cell := Option Player
abbrev Board := Fin 3 → Fin 3 → Cell
abbrev Coord := Fin 3 × Fin 3

structure GameState where
  board : Board
  turn : Player

def emptyBoard : Board := fun _ _ => none

def initialState : GameState := { board := emptyBoard, turn := Player.X }

def otherPlayer : Player → Player
  | Player.X => Player.O
  | Player.O => Player.X

def setCell (b : Board) (pos : Coord) (p : Player) : Board :=
  fun i j => if (i, j) = pos then some p else b i j

def playMove (s : GameState) (pos : Coord) : Option GameState :=
  if s.board pos.1 pos.2 = none then
    some { board := setCell s.board pos s.turn, turn := otherPlayer s.turn }
  else
    none

def boardCellsList : List Coord :=
  (List.finRange 3).flatMap (fun i => (List.finRange 3).map (fun j => (i, j)))

def legalMovesList (b : Board) : List Coord :=
  boardCellsList.filter (fun pos => b pos.1 pos.2 = none)

-- Winning lines
def row (i : Fin 3) : List Coord := (List.finRange 3).map (fun j => (i, j))
def col (j : Fin 3) : List Coord := (List.finRange 3).map (fun i => (i, j))
def mainDiag : List Coord := (List.finRange 3).map (fun i => (i, i))
def antiDiag : List Coord := (List.finRange 3).map (fun i => (i, ⟨2 - i.val, by omega⟩))

def winningLinesList : List (List Coord) :=
  (List.finRange 3).map row ++ (List.finRange 3).map col ++ [mainDiag, antiDiag]

def lineFilledBy (b : Board) (p : Player) (line : List Coord) : Bool :=
  line.all (fun pos => b pos.1 pos.2 = some p)

def wins (p : Player) (b : Board) : Bool :=
  winningLinesList.any (lineFilledBy b p)

def moveCount (b : Board) : Nat :=
  (boardCellsList.filter (fun pos => b pos.1 pos.2 ≠ none)).length

inductive Outcome
  | wins (p : Player)
  | draw
  | ongoing
  deriving Repr

def boardOutcome (b : Board) : Outcome :=
  if wins Player.X b then Outcome.wins Player.X
  else if wins Player.O b then Outcome.wins Player.O
  else if moveCount b = 9 then Outcome.draw
  else Outcome.ongoing

-- Strategy: pick first legal move
def greedyAny (b : Board) : Option Coord :=
  (legalMovesList b).head?

-- Strategy: center first, then block, then any
def centerCoord : Coord := (⟨1, by decide⟩, ⟨1, by decide⟩)

def marksInLine (b : Board) (p : Player) (line : List Coord) : Nat :=
  (line.filter (fun pos => b pos.1 pos.2 = some p)).length

def emptiesInLine (b : Board) (line : List Coord) : List Coord :=
  line.filter (fun pos => b pos.1 pos.2 = none)

def findBlockingMove (b : Board) (opponent : Player) : Option Coord :=
  let rec go : List (List Coord) → Option Coord
    | [] => none
    | line :: rest =>
      let oppMarks := marksInLine b opponent line
      let empties := emptiesInLine b line
      if oppMarks = 2 ∧ empties.length = 1 then
        empties.head?
      else
        go rest
  go winningLinesList

def xCenterBlockStrategy (s : GameState) : Option Coord :=
  if s.turn = Player.X then
    let b := s.board
    if b centerCoord.1 centerCoord.2 = none then
      some centerCoord
    else
      match findBlockingMove b Player.O with
      | some pos => some pos
      | none => greedyAny b
  else
    none

-- Game loop
def step (s : GameState) : Option GameState :=
  let strat := if s.turn = Player.X then xCenterBlockStrategy s else greedyAny s.board
  match strat with
  | none => none
  | some pos => playMove s pos

-- Rendering
def boardToString (b : Board) : String :=
  let cellToChar (c : Cell) : Char :=
    match c with
    | some Player.X => 'X'
    | some Player.O => 'O'
    | none => '.'
  let rowString (i : Fin 3) : String :=
    let cells := (List.finRange 3).map fun j => cellToChar (b i j)
    String.ofList cells
  String.intercalate "\n" ((List.finRange 3).map rowString)

def showState (s : GameState) : IO Unit := do
  IO.println s!"Turn: {s.turn}"
  IO.println (boardToString s.board)
  IO.println ""

def playDemo : IO Unit := do
  IO.println "=== Tic-Tac-Toe Demo ==="
  IO.println "X uses center-block strategy, O plays greedily"
  IO.println ""
  let rec loop (fuel : Nat) (ply : Nat) (s : GameState) : IO Unit := do
    IO.println s!"--- Ply {ply} ---"
    showState s
    match boardOutcome s.board with
    | Outcome.ongoing =>
        if fuel = 0 then
          IO.println "Fuel exhausted."
        else
          match step s with
          | none => IO.println "No legal move available. Stopping."
          | some s' => loop (fuel - 1) (ply + 1) s'
    | Outcome.wins p => IO.println s!"=== {p} wins! ==="
    | Outcome.draw => IO.println "=== Draw! ==="
  loop 10 0 initialState

def main : IO Unit := playDemo
