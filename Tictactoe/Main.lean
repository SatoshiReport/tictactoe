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
  -- There are three rows and three columns, so 3 × 3 positions.
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

/-! ### Winning lines and wins predicate -/

/-- All coordinates in a given row. -/
def row (i : Fin 3) : Finset Coord :=
  Finset.univ.image (fun j => (i, j))

/-- All coordinates in a given column. -/
def col (j : Fin 3) : Finset Coord :=
  Finset.univ.image (fun i => (i, j))

/-- Main and anti-diagonal coordinates. -/
def mainDiag : Finset Coord :=
  Finset.univ.image (fun i => (i, i))

def antiDiag : Finset Coord :=
  Finset.univ.image (fun i => (i, Fin.rev i))

def rows : Finset (Finset Coord) :=
  Finset.univ.image row

def cols : Finset (Finset Coord) :=
  Finset.univ.image col

def diagonals : Finset (Finset Coord) :=
  ([mainDiag, antiDiag] : List (Finset Coord)).toFinset

/-- The eight winning lines: three rows, three columns, two diagonals. -/
def winningLines : Finset (Finset Coord) :=
  rows ∪ cols ∪ diagonals

/-- Player `p` wins on board `b` if some winning line is filled with `p`. -/
def wins (p : Player) (b : Board) : Prop :=
  ∃ line ∈ winningLines, ∀ pos ∈ line, b pos.1 pos.2 = some p

/-- If every main-diagonal cell is marked by `p`, then `p` wins. -/
lemma wins_mainDiag {b : Board} {p : Player}
    (h : ∀ i, b i i = some p) : wins p b := by
  classical
  refine ⟨mainDiag, ?_, ?_⟩
  · simp [winningLines, diagonals]
  · intro pos hpos
    rcases Finset.mem_image.mp hpos with ⟨i, _, rfl⟩
    simp [h]

/-- Switch to the other player. -/
def otherPlayer : Player → Player
  | Player.X => Player.O
  | Player.O => Player.X

/-- A game state is a board with a turn indicator. -/
structure GameState where
  board : Board
  turn : Player
  deriving Repr

/-- Game histories for strategies (most-recent state at head). -/
abbrev History := List GameState

/-- A strategy suggests a coordinate (if any) given history and current state. -/
abbrev Strategy := History → GameState → Option Coord

/-- Empty board with all cells set to `none`. -/
def emptyBoard : Board := fun _ _ => none

/-- Initial state with X to move. -/
def initialState : GameState := { board := emptyBoard, turn := Player.X }

/-- The empty cells on a board (legal moves). -/
def emptyCells (b : Board) : Finset Coord :=
  boardCells.filter (fun pos => b pos.1 pos.2 = none)

abbrev legalMoves := emptyCells

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
        turn := otherPlayer s.turn }
  else
    none

/-- A move is legal when the target cell is empty. -/
def legal (s : GameState) (pos : Coord) : Prop :=
  pos ∈ legalMoves s.board

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
            turn := otherPlayer s.turn }, ?_⟩
  simp [playMove, hnone]

lemma playMove_some_implies_legal {s s' : GameState} {pos : Coord}
    (h : playMove s pos = some s') : legal s pos := by
  classical
  unfold playMove at h
  by_cases hnone : s.board pos.1 pos.2 = none
  · exact (legal_iff_empty).2 hnone
  · have hfalse : False := by simpa [hnone] using h
    contradiction

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
  -- identify the resulting board
  have hstate :
      { board := setCell s.board pos s.turn
        turn := otherPlayer s.turn } = s' := by
    simpa [playMove, hnone] using hplay
  cases hstate
  have hfilled := filledCells_setCell_insert (b := s.board) (pos := pos)
      (p := s.turn) hnone
  simp [moveCount, hfilled, hnotfilled, Nat.add_comm] -- add_comm for nice order

/-- Board center coordinate. -/
def centerCoord : Coord := (⟨1, by decide⟩, ⟨1, by decide⟩)

/-- Count of a player's marks on a line. -/
def marksInLine (b : Board) (p : Player) (line : Finset Coord) : Nat :=
  (line.filter (fun pos => b pos.1 pos.2 = some p)).card

/-- Empty cells on a line. -/
def emptiesInLine (b : Board) (line : Finset Coord) : Finset Coord :=
  line.filter (fun pos => b pos.1 pos.2 = none)

noncomputable def findBlockingMove (b : Board) (opponent : Player) : Option Coord := by
  classical
  let rec go : List (Finset Coord) → Option Coord
    | [] => none
    | line :: rest =>
      let oppMarks := marksInLine b opponent line
      let empties := emptiesInLine b line
      if hcount : oppMarks = 2 ∧ empties.card = 1 then
        match empties.toList.head? with
        | some pos => some pos
        | none => go rest -- should not occur if `card = 1`
      else
        go rest
  exact go winningLines.toList

noncomputable def chooseAnyLegal (b : Board) : Option Coord :=
  (legalMoves b).toList.head?

/-- X strategy: center first, otherwise block O's immediate win, otherwise pick any legal move. -/
noncomputable def xCenterBlockStrategy : Strategy :=
  fun _hist s =>
    if s.turn = Player.X then
      if centerCoord ∈ legalMoves s.board then
        some centerCoord
      else
        match findBlockingMove s.board Player.O with
        | some pos => some pos
        | none => chooseAnyLegal s.board
    else
      none

lemma row_nonempty (i : Fin 3) : (row i).Nonempty := by
  classical
  refine ⟨(i, ⟨0, by decide⟩), ?_⟩
  simp [row]

lemma col_nonempty (j : Fin 3) : (col j).Nonempty := by
  classical
  refine ⟨(⟨0, by decide⟩, j), ?_⟩
  simp [col]

lemma mainDiag_nonempty : mainDiag.Nonempty := by
  classical
  refine ⟨(⟨0, by decide⟩, ⟨0, by decide⟩), ?_⟩
  simp [mainDiag]

lemma antiDiag_nonempty : antiDiag.Nonempty := by
  classical
  refine ⟨(⟨0, by decide⟩, Fin.rev ⟨0, by decide⟩), ?_⟩
  simp [antiDiag]

lemma winningLines_nonempty {line : Finset Coord} (h : line ∈ winningLines) :
    line.Nonempty := by
  classical
  rcases Finset.mem_union.mp h with hrc | hdiag
  · rcases Finset.mem_union.mp hrc with hrow | hcol
    · rcases Finset.mem_image.mp hrow with ⟨i, _, rfl⟩
      exact row_nonempty _
    · rcases Finset.mem_image.mp hcol with ⟨j, _, rfl⟩
      exact col_nonempty _
  · have hdiag' : line = mainDiag ∨ line = antiDiag := by
      simpa [diagonals] using hdiag
    rcases hdiag' with rfl | rfl
    · exact mainDiag_nonempty
    · exact antiDiag_nonempty

/-- Safety invariant: O has not won on the current board. -/
def safetyInvariant (s : GameState) : Prop :=
  ¬ wins Player.O s.board

lemma safety_initial : safetyInvariant initialState := by
  classical
  unfold safetyInvariant initialState emptyBoard
  intro hwin
  rcases hwin with ⟨line, hline, hfilled⟩
  have hne := winningLines_nonempty hline
  rcases hne with ⟨pos, hpos⟩
  specialize hfilled pos hpos
  simp at hfilled

end Tictactoe

/-- Example lemma using mathlib to confirm the dependency is available. -/
lemma add_even (a b : ℤ) (ha : Even a) (hb : Even b) : Even (a + b) := by
  simpa using ha.add hb
