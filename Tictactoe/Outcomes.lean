/-
Outcome analysis: Classify and reason about possible game endings.
-/

import Tictactoe.Game

namespace Tictactoe

/-- O can never win against X's center-block strategy with perfect play. -/
def o_cannot_win : Prop :=
  ∀ s : GameState,
    playToOutcomeFull xCenterBlockStrategy greedyAny s ≠ some (Outcome.wins Player.O)

/-- X can force at least a draw with the center-block strategy. -/
def x_achieves_draw_or_win : Prop :=
  ∀ s : GameState,
    (playToOutcomeFull xCenterBlockStrategy greedyAny s = some (Outcome.wins Player.X) ∨
     playToOutcomeFull xCenterBlockStrategy greedyAny s = some Outcome.draw)

/-- The game outcome against greedy O strategy. -/
theorem game_outcome_with_greedy_O :
    o_cannot_win ∧ x_achieves_draw_or_win := by
  constructor
  · unfold o_cannot_win
    intro s
    sorry
  · unfold x_achieves_draw_or_win
    intro s
    sorry

/-- Outcome distribution: with both players playing optimally from empty board. -/
def optimal_outcome : Option Outcome :=
  playToOutcomeFull xCenterBlockStrategy greedyAny initialState

/-- Optimal play results in a draw. -/
theorem optimal_play_is_draw :
    optimal_outcome = some Outcome.draw := by
  classical
  unfold optimal_outcome
  sorry

/-- X has a clear path to draw even against optimal O. -/
theorem x_draw_guaranteed :
    ∃ (xStrat : Strategy),
      ∀ (oStrat : Strategy),
        playToOutcomeFull xStrat oStrat initialState = some Outcome.draw ∨
        playToOutcomeFull xStrat oStrat initialState = some (Outcome.wins Player.X) := by
  refine ⟨xCenterBlockStrategy, fun oStrat => ?_⟩
  sorry

/-- Outcome is deterministic given strategies. -/
lemma outcome_deterministic {xStrat oStrat : Strategy} {s : GameState} :
    (∃ o, playToOutcomeFull xStrat oStrat s = some o) := by
  classical
  unfold playToOutcomeFull fuelRemaining
  omega

/-- X strategy guarantees no losses. -/
theorem x_never_loses_with_center_block :
    ∀ s : GameState,
      playToOutcomeFull xCenterBlockStrategy greedyAny s ≠ some (Outcome.wins Player.O) := by
  intro s
  sorry

end Tictactoe
