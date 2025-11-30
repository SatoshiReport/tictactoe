import Tictactoe.WinningLines
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic

namespace Tictactoe

/-- Board center coordinate. -/
def centerCoord : Coord := (⟨1, by decide⟩, ⟨1, by decide⟩)

/-- Count of a player's marks on a line. -/
def marksInLine (b : Board) (p : Player) (line : Finset Coord) : Nat :=
  (line.filter (fun pos => b pos.1 pos.2 = some p)).card

/-- Empty cells on a line. -/
def emptiesInLine (b : Board) (line : Finset Coord) : Finset Coord :=
  line.filter (fun pos => b pos.1 pos.2 = none)

def findBlockingMove (b : Board) (opponent : Player) : Option Coord :=
  let rec go : List (Finset Coord) → Option Coord
    | [] => none
    | line :: rest =>
      let oppMarks := marksInLine b opponent line
      let empties := emptiesInLine b line
      if oppMarks = 2 ∧ empties.card = 1 then
        -- Find the first empty cell in the line
        let rec findFirstInLine : List Coord → Option Coord
          | [] => none
          | coord :: rest' =>
            if coord ∈ empties then some coord else findFirstInLine rest'
        -- Try to find an empty cell by checking each cell in boardCellsList
        -- that belongs to this line
        let rec checkAll : List Coord → Option Coord
          | [] => none
          | (i, j) :: rest' =>
            if (i, j) ∈ line ∧ b i j = none then some (i, j)
            else checkAll rest'
        checkAll boardCellsList
      else
        go rest
  go winningLinesList

def chooseAnyLegal (b : Board) : Option Coord :=
  (legalMovesList b).head?

/-- A strategy suggests a coordinate (if any) given history and current state. -/
abbrev Strategy := History → GameState → Option Coord

/-- Play any available legal move (if one exists). -/
def greedyAny : Strategy :=
  fun _ s => chooseAnyLegal s.board

/-- X strategy: center first, otherwise block O's immediate win, otherwise pick any legal move. -/
def xCenterBlockStrategy : Strategy :=
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

-- Strategy analysis lemmas

/-- Immediate threat detection: opponent can win in one move on the given line. -/
def isImmediateThreat (b : Board) (opponent : Player) (line : Finset Coord) : Prop :=
  marksInLine b opponent line = 2 ∧ (emptiesInLine b line).card = 1

/-- If opponent has an immediate threat on a line, blocking prevents that win. -/
lemma blockingMove_prevents_win {b : Board} {pos : Coord} {line : Finset Coord}
    (h_threat : isImmediateThreat b Player.O line)
    (h_pos : pos ∈ emptiesInLine b line) :
    ¬ wins Player.O (setCell b pos Player.X) := by
  classical
  unfold isImmediateThreat emptiesInLine marksInLine at h_threat
  intro hwin
  rcases hwin with ⟨win_line, _, hfilled⟩
  by_cases h : line = win_line
  · subst h
    -- pos is empty before the move
    have h_pos_none : b pos.1 pos.2 = none := by
      simp [Finset.mem_filter] at h_pos
      exact h_pos.2
    -- After placing X at pos, all cells on the line must have O by hfilled
    -- But pos now has X, so O can't fill all three cells
    have contra : setCell b pos Player.X pos.1 pos.2 = some Player.O := by
      exact hfilled pos (Finset.mem_filter.mp h_pos).1
    simp [setCell] at contra
  · sorry

/-- Center strategy correctness: playing center on empty board is a valid opening move. -/
lemma centerCoord_on_empty_valid : centerCoord ∈ legalMoves emptyBoard := by
  classical
  simp [legalMoves, emptyCells, boardCells, emptyBoard, centerCoord]

/-- Finding a blocking move returns a legal move if a threat exists. -/
lemma findBlockingMove_legal {b : Board}
    (h : findBlockingMove b Player.O ≠ none) :
    ∃ pos, findBlockingMove b Player.O = some pos ∧ pos ∈ legalMoves b := by
  sorry

end Tictactoe
