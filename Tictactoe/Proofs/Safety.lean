import Tictactoe.Strategy

namespace Tictactoe

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
