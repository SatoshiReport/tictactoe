import Tictactoe.Strategy
import Tictactoe.Game

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

lemma winsO_of_wins_after_X_move {b : Board} {pos : Coord}
    (hpos : b pos.1 pos.2 = none)
    (hwin : wins Player.O (setCell b pos Player.X)) :
    wins Player.O b := by
  classical
  rcases hwin with ⟨line, hline, hfilled⟩
  refine ⟨line, hline, ?_⟩
  intro q hq
  rcases em (q = pos) with hqp | hqne
  · have hval := hfilled q hq
    have : False := by
      subst hqp
      simp [setCell] at hval
    contradiction
  · have hval := hfilled q hq
    simpa [setCell, hqne] using hval

lemma safety_after_X_move {s s' : GameState} {pos : Coord}
    (hsafe : safetyInvariant s)
    (hturn : s.turn = Player.X)
    (hlegal : legal s pos)
    (hplay : playMove s pos = some s') :
    safetyInvariant s' := by
  classical
  have hnone : s.board pos.1 pos.2 = none :=
    (legal_iff_empty).mp hlegal
  have hstate :
      { board := setCell s.board pos Player.X
        turn := Player.O } = s' := by
    simpa [playMove, hnone, hturn] using hplay
  subst hstate
  unfold safetyInvariant at hsafe ⊢
  intro hwin
  exact hsafe (winsO_of_wins_after_X_move hnone hwin)

end Tictactoe
