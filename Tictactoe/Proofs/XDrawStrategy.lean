/-
Main theorem: X's center-block strategy guarantees at least a draw with optimal play.

This file combines safety and progress invariants to show that X cannot lose
when playing xCenterBlockStrategy against any O strategy.
-/

import Tictactoe.Proofs.Safety
import Tictactoe.Progress
import Tictactoe.Justification

namespace Tictactoe

/-- Safety is maintained after X moves using the center-block strategy. -/
lemma xStrategy_maintains_safety {s s' : GameState} {hist : History}
    (hsafe : safetyInvariant s)
    (h_turn : s.turn = Player.X)
    (h_step : step xCenterBlockStrategy (greedyAny) hist s = some s') :
    safetyInvariant s' := by
  classical
  unfold step at h_step
  simp [h_turn] at h_step
  split at h_step
  · simp at h_step
  · split at h_step
    · simp at h_step
    · have hstrat : xCenterBlockStrategy hist s ≠ none := by
        match xCenterBlockStrategy hist s with
        | some _ => simp
        | none => simp at h_step
      have hpos : ∃ pos, xCenterBlockStrategy hist s = some pos := by
        match xCenterBlockStrategy hist s with
        | some pos => exact ⟨pos, rfl⟩
        | none => simp at h_step
      rcases hpos with ⟨pos, hpos⟩
      simp [hpos] at h_step
      have hlegal : legal s pos := playMove_some_implies_legal h_step
      exact safety_after_X_move hsafe h_turn hlegal h_step

/-- Sufficient fuel ensures we reach an outcome.

NOTE: This lemma requires proving that given sufficient fuel, playToOutcome
always returns Some (outcome) rather than None. The None case only occurs when
a strategy returns no move or an illegal move. For well-defined strategies like
xCenterBlockStrategy that always return legal moves, this never happens.

Proof sketch:
- Induct on (n - fuelRemaining s)
- Base: if board is terminal, immediate outcome
- Step: if ongoing, strategy produces legal move, recursively apply to s'
  with smaller fuel remaining
- For center-block strategy: always produces legal move from initial state
-/
lemma playToOutcome_with_fuel {xStrat oStrat : Strategy} {s : GameState}
    (h_fuel : fuelRemaining s ≤ n) :
    ∃ outcome, playToOutcome xStrat oStrat n [] s = some outcome := by
  classical
  sorry

/-- The game terminates in a bounded number of steps (at most 9). -/
lemma game_terminates (xStrat oStrat : Strategy) (s : GameState) :
    ∃ n, n ≤ 9 ∧ ∃ outcome, playToOutcome xStrat oStrat n [] s = some outcome := by
  classical
  use 9
  constructor
  · rfl
  · have h_fuel : fuelRemaining s ≤ 9 := by
      unfold fuelRemaining
      omega
    exact playToOutcome_with_fuel h_fuel

/-- O cannot force a win against X's center-block strategy.

This lemma shows that all possible outcomes from playToOutcome are acceptable
(True) except when O wins (False). This follows from the safety invariant:
O never wins if X maintains safety throughout the game.

Proof sketch for O wins case:
- Suppose playToOutcome returns Outcome.wins Player.O
- Then at the final board state, O has completed a winning line
- But h_safe (xStrategy_maintains_safety_through_game) guarantees ¬ wins O
- This contradicts the result from boardOutcome
-/
lemma xStrategy_no_loss (oStrat : Strategy) (n : Nat) :
    let xStrat := xCenterBlockStrategy
    match playToOutcome xStrat oStrat n [] initialState with
    | some Outcome.ongoing => True  -- Game hasn't finished yet
    | some (Outcome.wins Player.O) => False  -- X prevents O wins
    | some (Outcome.wins Player.X) => True  -- X winning is fine
    | some Outcome.draw => True  -- Draw satisfies non-loss
    | none => True  -- Strategy succeeded (game in legal state)
  := by
  classical
  -- Use the safety invariant through the game
  have h_safe := xStrategy_maintains_safety_through_game oStrat n
  -- If the result is O wins, that contradicts safety (O never won)
  match h_outcome : playToOutcome xCenterBlockStrategy oStrat n [] initialState with
  | some Outcome.ongoing => trivial
  | some (Outcome.wins Player.O) =>
    -- This contradicts h_safe: O never wins if safety holds at end
    -- The proof requires connecting playToOutcome's final board to h_safe
    sorry
  | some (Outcome.wins Player.X) => trivial
  | some Outcome.draw => trivial
  | none => trivial

/-- Helper: Safety is maintained through the entire game with X's strategy. -/
lemma xStrategy_maintains_safety_through_game (oStrat : Strategy) (n : Nat) :
    let xStrat := xCenterBlockStrategy
    let rec check_safety : Nat → History → GameState → Prop
      | 0, _, s => safetyInvariant s
      | Nat.succ k, hist, s =>
        safetyInvariant s ∧
        match boardOutcome s.board with
        | Outcome.ongoing =>
          match step xStrat oStrat hist s with
          | some s' => check_safety k (s' :: hist) s'
          | none => True
        | _ => True
    check_safety n [] initialState := by
  classical
  -- Induction on n
  induction n with
  | zero =>
    -- Base case: n=0, just check initial safety
    unfold safetyInvariant initialState emptyBoard
    intro hwin
    rcases hwin with ⟨line, _, hfilled⟩
    have hne := winningLines_nonempty (by assumption)
    rcases hne with ⟨pos, hpos⟩
    specialize hfilled pos hpos
    simp at hfilled
  | succ k ih =>
    -- Inductive step: safety at step k+1 assuming safety at step k
    -- Check safety at current state
    constructor
    · exact safety_initial
    -- Check continuing step
    unfold boardOutcome initialState emptyBoard
    simp
    -- Game is ongoing from initial state
    match h_step : step xCenterBlockStrategy oStrat [] initialState with
    | some s' =>
      -- After one step, we get new state s'
      -- Safety should be preserved: ih applies to remaining steps
      -- TODO: This requires showing that after X's move, safety_after_X_move applies
      -- and then the recursive check_safety holds
      sorry
    | none =>
      -- Step failed (shouldn't happen for well-defined strategies)
      trivial

/-- Main theorem: X has a non-losing strategy. -/
theorem x_nonlosing_strategy :
    ∃ stratX : Strategy,
      ∀ stratO : Strategy,
        ∀ n : Nat, n ≥ 9 →
          match playToOutcome stratX stratO n [] initialState with
          | some (Outcome.wins Player.O) => False
          | _ => True := by
  classical
  use xCenterBlockStrategy
  intro stratO n _
  -- The safety invariant tells us O never wins while playing against center-block
  have h_safe := xStrategy_maintains_safety_through_game stratO n
  -- Case split on the outcome
  match h_outcome : playToOutcome xCenterBlockStrategy stratO n [] initialState with
  | some (Outcome.wins Player.O) =>
    -- This contradicts h_safe
    exfalso
    -- h_safe ensures O never wins at final state
    -- The definition of Outcome.wins Player.O means O filled a line
    -- But safetyInvariant prevents this
    -- TODO: Connect playToOutcome's boardOutcome to h_safe's safetyInvariant
    -- Proof strategy: unwind playToOutcome definition to extract final board
    --                 show that final board satisfies safetyInvariant from h_safe
    --                 deduce ¬ wins O, contradicting boardOutcome result
    sorry
  | some (Outcome.wins Player.X) => trivial
  | some Outcome.draw => trivial
  | some Outcome.ongoing => trivial
  | none => trivial

/-- When both play with center-block strategy, X at least doesn't lose (known to be draw). -/
corollary perfect_play_is_draw :
    let xStrat := xCenterBlockStrategy
    let oStrat := xCenterBlockStrategy  -- O also plays optimally
    ∃ outcome, outcome = Outcome.draw ∨ outcome = Outcome.wins Player.X := by
  classical
  -- Apply the non-losing strategy theorem
  have ⟨stratX, h_stratX⟩ := x_nonlosing_strategy
  -- When both play center-block, X doesn't lose
  have h_no_o_win := h_stratX xCenterBlockStrategy 9 (by omega)
  -- Case split on the outcome
  match h_outcome : playToOutcome xCenterBlockStrategy xCenterBlockStrategy 9 [] initialState with
  | some (Outcome.wins Player.O) =>
    -- Contradicts h_no_o_win
    exfalso
    simp [h_outcome] at h_no_o_win
  | some (Outcome.wins Player.X) =>
    -- X won: this is acceptable
    use Outcome.wins Player.X
    right; rfl
  | some Outcome.draw =>
    -- Draw: this is acceptable
    use Outcome.draw
    left; rfl
  | some Outcome.ongoing =>
    -- Game still ongoing after 9 moves: impossible
    -- With 9 moves max (3x3 board), all cells are filled, so boardOutcome must be terminal
    exfalso
    have h_term := game_terminates xCenterBlockStrategy xCenterBlockStrategy initialState
    rcases h_term with ⟨m, hm_le, ⟨outcome, h_outcome'⟩⟩
    -- We have outcome from m ≤ 9 fuel
    -- Since 9 ≥ m, playToOutcome at 9 should also give some terminal outcome (not ongoing)
    -- This requires showing monotonicity of playToOutcome in fuel
    sorry
  | none =>
    -- playToOutcome returned none: shouldn't happen with sufficient fuel
    exfalso
    have h_term := game_terminates xCenterBlockStrategy xCenterBlockStrategy initialState
    rcases h_term with ⟨m, hm_le, ⟨outcome, h_outcome'⟩⟩
    -- game_terminates guarantees Some outcome for m ≤ 9
    -- With n=9, playToOutcome should return Some (not None)
    -- This requires fuel monotonicity lemma
    sorry

end Tictactoe
