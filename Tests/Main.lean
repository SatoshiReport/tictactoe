import Tictactoe

open Tictactoe

namespace Tests

def diagXBoard : Board :=
  fun i j => if _ : i = j then some Player.X else none

example : wins Player.X diagXBoard := by
  classical
  have hdiag : ∀ i, diagXBoard i i = some Player.X := by
    intro i
    simp [diagXBoard]
  exact wins_mainDiag (b := diagXBoard) (p := Player.X) hdiag

example : boardOutcome diagXBoard = Outcome.wins Player.X := by
  classical
  unfold boardOutcome
  simp [diagXBoard, wins_mainDiag]

example : ¬ wins Player.X emptyBoard := by
  classical
  intro h
  rcases h with ⟨line, hline, hfilled⟩
  rcases winningLines_nonempty hline with ⟨pos, hpos⟩
  specialize hfilled pos hpos
  simp [emptyBoard] at hfilled

example : ¬ wins Player.O emptyBoard := by
  classical
  intro h
  rcases h with ⟨line, hline, hfilled⟩
  rcases winningLines_nonempty hline with ⟨pos, hpos⟩
  specialize hfilled pos hpos
  simp [emptyBoard] at hfilled

example : boardOutcome emptyBoard = Outcome.ongoing := by
  classical
  have hX : ¬ wins Player.X emptyBoard := by
    intro h
    rcases h with ⟨line, hline, hfilled⟩
    rcases winningLines_nonempty hline with ⟨pos, hpos⟩
    specialize hfilled pos hpos
    simp [emptyBoard] at hfilled
  have hO : ¬ wins Player.O emptyBoard := by
    intro h
    rcases h with ⟨line, hline, hfilled⟩
    rcases winningLines_nonempty hline with ⟨pos, hpos⟩
    specialize hfilled pos hpos
    simp [emptyBoard] at hfilled
  have hcount : moveCount emptyBoard = 0 := by
    simp [emptyBoard, moveCount, filledCells, boardCells]
  simp [boardOutcome, hX, hO, hcount]

example : moveCount initialState.board = 0 := by
  classical
  simp [initialState, emptyBoard, moveCount, filledCells, boardCells]

example :
    ∃ s', playMove initialState centerCoord = some s' ∧
      moveCount s'.board = 1 := by
  classical
  have hnone : initialState.board centerCoord.1 centerCoord.2 = none := by
    simp [initialState, emptyBoard, centerCoord]
  have hlegal : legal initialState centerCoord :=
    (legal_iff_empty).2 hnone
  obtain ⟨s', hplay⟩ :=
    playMove_some_of_legal (s := initialState) (pos := centerCoord) hlegal
  have hcount := moveCount_playMove
      (s := initialState) (s' := s') (pos := centerCoord) hlegal hplay
  have hempty : moveCount initialState.board = 0 := by
    classical
    simp [initialState, emptyBoard, moveCount, filledCells, boardCells]
  refine ⟨s', hplay, ?_⟩
  simpa [hempty] using hcount

example : xCenterBlockStrategy [] initialState = some centerCoord := by
  classical
  have hlegal : centerCoord ∈ legalMoves emptyBoard := by
    have hlegal' : legal initialState centerCoord := by
      have hnone : initialState.board centerCoord.1 centerCoord.2 = none := by
        simp [initialState, emptyBoard, centerCoord]
      exact (legal_iff_empty).2 hnone
    simpa [initialState, legal, legalMoves] using hlegal'
  simp [xCenterBlockStrategy, initialState, hlegal]

example :
    playToOutcome xCenterBlockStrategy greedyAny 0 [] initialState =
      some (boardOutcome initialState.board) := by
  simp [playToOutcome]

end Tests

def main : IO Unit :=
  pure ()
