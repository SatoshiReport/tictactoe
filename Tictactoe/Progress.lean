/-
Progress invariants: properties showing that game state advances toward a terminal condition.
-/

import Tictactoe.Game

namespace Tictactoe

/-- Progress: the number of marked cells increases with each move. -/
lemma moveCount_increases {s s' : GameState} {pos : Coord}
    (h_legal : legal s pos)
    (h_play : playMove s pos = some s') :
    moveCount s'.board = moveCount s.board + 1 := by
  classical
  exact moveCount_playMove h_legal h_play

/-- The game must eventually reach a terminal state (at most 9 moves total). -/
lemma moveCount_bounded (b : Board) : moveCount b ≤ 9 :=
  moveCount_le_nine b

/-- On a full board (9 moves), the game is terminal. -/
lemma full_board_terminal (b : Board) (h : moveCount b = 9) :
    boardOutcome b ≠ Outcome.ongoing := by
  classical
  unfold boardOutcome
  intro h_ongoing
  split at h_ongoing
  · simp at h_ongoing
  · split at h_ongoing
    · simp at h_ongoing
    · split at h_ongoing
      simp [h] at h_ongoing

/-- If the board is not full, there exists at least one legal move. -/
lemma not_full_has_legal (b : Board) (h : moveCount b < 9) :
    (legalMoves b).Nonempty := by
  classical
  have hcard : (legalMoves b).card > 0 := by
    have h_total : (legalMoves b).card + moveCount b = 9 := by
      have h_board : boardCells.card = 9 := boardCells_card
      have h_disj : Disjoint (filledCells b) (legalMoves b) := by
        simp [filledCells, legalMoves, emptyCells, Finset.disjoint_iff_inf_le]
      have h_cover : filledCells b ∪ legalMoves b = boardCells := by
        simp [filledCells, legalMoves, emptyCells]
      have := Finset.card_union_of_disjoint h_disj
      simp [h_cover, h_board, moveCount] at this
      omega
    omega
  exact Finset.nonempty_iff_ne_empty.mpr (Finset.card_pos.mp hcard)

/-- Game progress measures: moveCount is a natural progress metric. -/
def gameProgress (s : GameState) : Nat :=
  moveCount s.board

/-- Play advances progress monotonically. -/
lemma step_advances_progress (xStrat oStrat : Strategy) (hist : History) (s s' : GameState)
    (h_step : step xStrat oStrat hist s = some s') :
    gameProgress s' > gameProgress s := by
  classical
  unfold step at h_step
  split at h_step
  · simp at h_step
  · split at h_step
    · simp at h_step
    · have hplay := (playMove_some_implies_legal h_step)
      have = moveCount_increases hplay h_step
      unfold gameProgress
      omega

end Tictactoe
