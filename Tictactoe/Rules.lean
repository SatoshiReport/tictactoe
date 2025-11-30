import Mathlib

namespace Tictactoe

/-- Board coordinates (row, column). -/
abbrev Coord := Fin 3 × Fin 3

/-- Player markers for tic-tac-toe. -/
inductive Player
  | X
  | O
  deriving DecidableEq, Repr

/-- Board cells may be empty or marked by a player. -/
abbrev Cell := Option Player

/-- A 3×3 board indexed by row/column in `Fin 3`. -/
abbrev Board := Fin 3 → Fin 3 → Cell

/-- All coordinates on the board as a finset. -/
def boardCells : Finset Coord :=
  Finset.univ.product Finset.univ

def boardCellsList : List Coord :=
  (List.finRange 3).flatMap (fun i => (List.finRange 3).map (fun j => (i, j)))

/-- The subset of coordinates that are already filled. -/
def filledCells (b : Board) : Finset Coord :=
  boardCells.filter (fun pos => b pos.1 pos.2 ≠ none)

/-- Number of placed marks on the board. -/
def moveCount (b : Board) : Nat :=
  (filledCells b).card

lemma moveCount_le_card_boardCells (b : Board) :
    moveCount b ≤ boardCells.card := by
  classical
  simpa [moveCount, filledCells] using
    (Finset.card_filter_le (s := boardCells)
      (p := fun pos => b pos.1 pos.2 ≠ none))

lemma boardCells_card : boardCells.card = 9 := by
  classical
  have h :
      boardCells.card =
        ((Finset.univ : Finset (Fin 3)).card *
          (Finset.univ : Finset (Fin 3)).card) := by
    simp [boardCells]
  norm_num [Finset.card_univ, Fintype.card_fin] at h
  simpa using h

/-- A tic-tac-toe board can have at most nine marks placed. -/
lemma moveCount_le_nine (b : Board) : moveCount b ≤ 9 := by
  classical
  have h := moveCount_le_card_boardCells b
  simpa [boardCells_card] using h

/-- Switch to the other player. -/
def otherPlayer : Player → Player
  | Player.X => Player.O
  | Player.O => Player.X

/-- A game state is a board with a turn indicator and optional last move record. -/
structure GameState where
  board : Board
  turn : Player
  lastMove : Option (Player × Coord)  -- Track who moved last and where
  deriving Repr

/-- Game histories for strategies (most-recent state at head). -/
abbrev History := List GameState

/-- Empty board with all cells set to `none`. -/
def emptyBoard : Board := fun _ _ => none

/-- Initial state with X to move and no last move. -/
def initialState : GameState := { board := emptyBoard, turn := Player.X, lastMove := none }

/-- The empty cells on a board (legal moves). -/
def emptyCells (b : Board) : Finset Coord :=
  boardCells.filter (fun pos => b pos.1 pos.2 = none)

abbrev legalMoves := emptyCells

def legalMovesList (b : Board) : List Coord :=
  boardCellsList.filter (fun pos => b pos.1 pos.2 = none)

lemma emptyCells_card_le_nine (b : Board) : (emptyCells b).card ≤ 9 := by
  classical
  have h := Finset.card_filter_le
      (s := boardCells) (p := fun pos => b pos.1 pos.2 = none)
  simpa [emptyCells] using h

/-- Update a single cell, overwriting any previous value. -/
def setCell (b : Board) (pos : Coord) (p : Player) : Board :=
  fun i j => if (i, j) = pos then some p else b i j

/-- Attempt to play a move; fails (`none`) if the target cell is occupied. -/
def playMove (s : GameState) (pos : Coord) : Option GameState :=
  if s.board pos.1 pos.2 = none then
    some
      { board := setCell s.board pos s.turn
        turn := otherPlayer s.turn
        lastMove := some (s.turn, pos) }
  else
    none

/-- A move is legal when the target cell is empty. -/
def legal (s : GameState) (pos : Coord) : Prop :=
  pos ∈ legalMoves s.board

instance (s : GameState) (pos : Coord) : Decidable (legal s pos) :=
  Finset.decidableMem pos (legalMoves s.board)

lemma legal_iff_empty {s : GameState} {pos : Coord} :
    legal s pos ↔ s.board pos.1 pos.2 = none := by
  classical
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨_, hnone⟩
    simpa using hnone
  · intro hnone
    have hpos : pos ∈ boardCells := by
      simp [boardCells]
    exact Finset.mem_filter.mpr ⟨hpos, hnone⟩

lemma playMove_some_of_legal {s : GameState} {pos : Coord}
    (hlegal : legal s pos) :
    ∃ s', playMove s pos = some s' := by
  classical
  rcases (legal_iff_empty).mp hlegal with hnone
  refine ⟨{ board := setCell s.board pos s.turn
            turn := otherPlayer s.turn
            lastMove := some (s.turn, pos) }, ?_⟩
  simp [playMove, hnone]

lemma playMove_some_implies_legal {s s' : GameState} {pos : Coord}
    (h : playMove s pos = some s') : legal s pos := by
  classical
  unfold playMove at h
  by_cases hnone : s.board pos.1 pos.2 = none
  · exact (legal_iff_empty).2 hnone
  · simp [hnone] at h

lemma filledCells_setCell_insert {b : Board} {pos : Coord} {p : Player}
    (h : b pos.1 pos.2 = none) :
    filledCells (setCell b pos p) =
      insert pos (filledCells b) := by
  classical
  ext q
  constructor
  · intro hmem
    rcases Finset.mem_filter.mp hmem with ⟨hqcell, hqval⟩
    by_cases hqp : q = pos
    · subst hqp
      exact Finset.mem_insert_self _ _
    · have hval : b q.1 q.2 ≠ none := by
        simpa [setCell, hqp] using hqval
      exact Finset.mem_insert.mpr <|
        Or.inr (Finset.mem_filter.mpr ⟨hqcell, hval⟩)
  · intro hmem
    rcases Finset.mem_insert.mp hmem with hqp | hmem
    · subst hqp
      simp [filledCells, boardCells, setCell]
    · rcases Finset.mem_filter.mp hmem with ⟨hqcell, hqval⟩
      have hqp : q ≠ pos := by
        intro hqp'
        subst hqp'
        exact (hqval (by simpa using h)).elim
      have hval' : setCell b pos p q.1 q.2 ≠ none := by
        simpa [setCell, hqp] using hqval
      exact Finset.mem_filter.mpr ⟨hqcell, hval'⟩

lemma moveCount_playMove {s s' : GameState} {pos : Coord}
    (hlegal : legal s pos)
    (hplay : playMove s pos = some s') :
    moveCount s'.board = moveCount s.board + 1 := by
  classical
  rcases (legal_iff_empty).mp hlegal with hnone
  have hnotfilled : pos ∉ filledCells s.board := by
    intro hmem
    have := (Finset.mem_filter.mp hmem).2
    exact this hnone
  have hstate :
      { board := setCell s.board pos s.turn
        turn := otherPlayer s.turn
        lastMove := some (s.turn, pos) } = s' := by
    simpa [playMove, hnone] using hplay
  cases hstate
  have hfilled := filledCells_setCell_insert (b := s.board) (pos := pos)
      (p := s.turn) hnone
  simp [moveCount, hfilled, hnotfilled, Nat.add_comm]

end Tictactoe
