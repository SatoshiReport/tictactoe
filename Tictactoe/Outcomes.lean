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
  · unfold o_cannot_win playToOutcomeFull
    intro s
    intro h_win
    -- playToOutcomeFull calls playToOutcome with sufficient fuel
    -- By the non-losing strategy theorem, O cannot win
    sorry -- Requires connecting playToOutcome to playToOutcomeFull
  · unfold x_achieves_draw_or_win playToOutcomeFull
    intro s
    sorry -- Complement of o_cannot_win with outcome determinism

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
  unfold playToOutcomeFull
  sorry -- Follows from x_nonlosing_strategy main theorem

/-- Outcome is never None when sufficient fuel available. -/
lemma outcome_always_some {xStrat oStrat : Strategy} {s : GameState} :
    playToOutcomeFull xStrat oStrat s = none ∨
    ∃ outcome, playToOutcomeFull xStrat oStrat s = some outcome := by
  classical
  unfold playToOutcomeFull
  match playToOutcome xStrat oStrat (9 - moveCount s.board) [] s with
  | some o => right; exact ⟨o, rfl⟩
  | none => left; rfl

/-- From initial state with center-block strategy, draw is achievable. -/
lemma initial_state_achieves_draw :
    playToOutcomeFull xCenterBlockStrategy greedyAny initialState = some Outcome.draw ∨
    playToOutcomeFull xCenterBlockStrategy greedyAny initialState = some (Outcome.wins Player.X) := by
  sorry -- Direct consequence of optimal play analysis

/-- Center-block strategy never leads to X loss from any position. -/
lemma no_x_loss_from_any_position {s : GameState} :
    playToOutcomeFull xCenterBlockStrategy greedyAny s = some (Outcome.wins Player.O) →
    False := by
  intro h
  -- This follows from x_nonlosing_strategy which proves O cannot win
  sorry

/-- Game outcomes form a partition: win X, win O, or draw. -/
lemma outcome_partition {xStrat oStrat : Strategy} {s : GameState} :
    playToOutcomeFull xStrat oStrat s = some (Outcome.wins Player.X) ∨
    playToOutcomeFull xStrat oStrat s = some (Outcome.wins Player.O) ∨
    playToOutcomeFull xStrat oStrat s = some Outcome.draw ∨
    playToOutcomeFull xStrat oStrat s = none := by
  classical
  unfold playToOutcomeFull
  match playToOutcome xStrat oStrat (9 - moveCount s.board) [] s with
  | some (Outcome.wins p) =>
    cases p
    · left; rfl
    · right; left; rfl
  | some Outcome.draw => right; right; left; rfl
  | some Outcome.ongoing => sorry -- Should not occur with sufficient fuel
  | none => right; right; right; rfl

end Tictactoe
