import Tictactoe.WinningLines

namespace Tictactoe

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

/-- A strategy suggests a coordinate (if any) given history and current state. -/
abbrev Strategy := History → GameState → Option Coord

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

end Tictactoe
