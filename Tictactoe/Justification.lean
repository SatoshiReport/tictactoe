/-
Move justification system: extract human-readable reasoning from proofs.
Each move should have a justification explaining why it was chosen.
-/

import Tictactoe.Strategy

namespace Tictactoe

/-- Justification types for moves in tic-tac-toe strategy. -/
inductive MoveJustification
  | centerOpening : MoveJustification
  | blockImmediateThreat : MoveJustification
  | blockTwoThreats : MoveJustification
  | forceOutcome : MoveJustification
  | opportunistic : MoveJustification
  deriving Repr, DecidableEq, ToString

/-- Extract why the X strategy chose a particular move. -/
def justifyXMove (s : GameState) (pos : Coord) : Option MoveJustification :=
  if s.turn = Player.X then
    if pos = centerCoord then
      -- Center move on empty board
      if (legalMoves s.board).card = 9 then
        some MoveJustification.centerOpening
      else if (legalMoves s.board).card > 8 then
        -- Center available early
        some MoveJustification.centerOpening
      else
        none
    else
      -- Check if this blocks an immediate threat
      if ∃ line ∈ winningLines,
          isImmediateThreat s.board Player.O line ∧ pos ∈ emptiesInLine s.board line then
        some MoveJustification.blockImmediateThreat
      else
        -- Otherwise it's an opportunistic move
        some MoveJustification.opportunistic
  else
    none

/-- All moves should have justifiable reasons. -/
lemma xMove_has_justification {s : GameState} {pos : Coord}
    (h_turn : s.turn = Player.X)
    (h_legal : pos ∈ legalMoves s.board)
    (h_from_strat : xCenterBlockStrategy [] s = some pos) :
    ∃ j, justifyXMove s pos = some j := by
  classical
  unfold justifyXMove xCenterBlockStrategy at *
  simp [h_turn] at h_from_strat
  by_cases hc : centerCoord ∈ legalMoves s.board
  · simp [hc] at h_from_strat
    subst h_from_strat
    refine ⟨MoveJustification.centerOpening, ?_⟩
    simp [justifyXMove, h_turn, h_legal]
  · simp [hc] at h_from_strat
    match h_from_strat with
    | rfl =>
      match findBlockingMove s.board Player.O with
      | some bpos =>
        subst h_from_strat
        refine ⟨MoveJustification.blockImmediateThreat, ?_⟩
        simp [justifyXMove, h_turn]
        sorry
      | none =>
        subst h_from_strat
        refine ⟨MoveJustification.opportunistic, ?_⟩
        simp [justifyXMove, h_turn]

end Tictactoe
