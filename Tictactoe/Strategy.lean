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

end Tictactoe
