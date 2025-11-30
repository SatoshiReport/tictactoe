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

/-- Find a move that blocks multiple threats (if one exists).
  Returns a move that eliminates at least two simultaneous opponent threats. -/
def findBlockTwoThreatsMove (b : Board) (opponent : Player) : Option Coord :=
  let rec go : List Coord → Option Coord
    | [] => none
    | pos :: rest =>
      let b' := setCell b pos Player.X
      let threats_before := threatCount b opponent
      let threats_after := threatCount b' opponent
      if threats_before ≥ 2 ∧ threats_after = 0 then
        some pos  -- This move blocks all threats
      else if threats_before ≥ 2 ∧ threats_after ≤ threats_before - 2 then
        some pos  -- This move blocks at least 2 threats
      else
        go rest
  go (legalMovesList b)

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

/-- Enhanced X strategy: center, block single threats, block two threats if fork present, otherwise play legal move. -/
def xCenterBlockForkStrategy : Strategy :=
  fun _hist s =>
    if s.turn = Player.X then
      if centerCoord ∈ legalMoves s.board then
        some centerCoord
      else if hasFork s.board Player.O then
        -- If O has a fork, prioritize blocking 2+ threats
        match findBlockTwoThreatsMove s.board Player.O with
        | some pos => some pos
        | none =>
          -- Fall back to blocking single threats
          match findBlockingMove s.board Player.O with
          | some pos => some pos
          | none => chooseAnyLegal s.board
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

/-- Fork: opponent has two or more separate lines with immediate threats. -/
def hasFork (b : Board) (opponent : Player) : Prop :=
  ∃ line1 line2 ∈ winningLines, line1 ≠ line2 ∧
    isImmediateThreat b opponent line1 ∧
    isImmediateThreat b opponent line2

/-- Count how many immediate threats opponent has on the board. -/
def threatCount (b : Board) (opponent : Player) : Nat :=
  (winningLines.filter (fun line => isImmediateThreat b opponent line)).card

/-- Fork is present when opponent has 2+ threats. -/
lemma fork_iff_two_or_more_threats {b : Board} {opponent : Player} :
    hasFork b opponent ↔ threatCount b opponent ≥ 2 := by
  classical
  unfold hasFork threatCount
  constructor
  · intro ⟨line1, hline1, line2, hline2, hne, h1, h2⟩
    simp [Finset.mem_filter]
    have h1_filtered : line1 ∈ winningLines.filter (fun line => isImmediateThreat b opponent line) := by
      simp [Finset.mem_filter, hline1, h1]
    have h2_filtered : line2 ∈ winningLines.filter (fun line => isImmediateThreat b opponent line) := by
      simp [Finset.mem_filter, hline2, h2]
    have h_distinct : (line1 : Finset Coord) ≠ (line2 : Finset Coord) := hne
    have : (2 : ℕ) ≤ (winningLines.filter (fun line => isImmediateThreat b opponent line)).card := by
      have h_card_ge_2 := Finset.card_le_of_two_mem h1_filtered h2_filtered h_distinct
      exact h_card_ge_2
    omega
  · intro h_count
    sorry

/-- Center strategy correctness: playing center on empty board is a valid opening move. -/
lemma centerCoord_on_empty_valid : centerCoord ∈ legalMoves emptyBoard := by
  classical
  simp [legalMoves, emptyCells, boardCells, emptyBoard, centerCoord]

/-- Finding a blocking move returns a legal move if a threat exists. -/
lemma findBlockingMove_legal {b : Board}
    (h : findBlockingMove b Player.O ≠ none) :
    ∃ pos, findBlockingMove b Player.O = some pos ∧ pos ∈ legalMoves b := by
  sorry

/-- O center-block strategy: symmetric to X's strategy. Play center, block X threats, then any legal move. -/
def oCenterBlockStrategy : Strategy :=
  fun _hist s =>
    if s.turn = Player.O then
      if centerCoord ∈ legalMoves s.board then
        some centerCoord
      else
        match findBlockingMove s.board Player.X with
        | some pos => some pos
        | none => chooseAnyLegal s.board
    else
      none

end Tictactoe
