/-
Strategy comparison framework: Analyze and compare different strategies formally.
-/

import Tictactoe.Outcomes

namespace Tictactoe

/-- Outcome of a strategy pair from a given state. -/
def strategyOutcome (xStrat oStrat : Strategy) (s : GameState) : Option Outcome :=
  playToOutcomeFull xStrat oStrat s

/-- Strategy S1 dominates strategy S2 if S1 achieves at least as good outcome in all positions. -/
def strategyDominates (xStrat1 xStrat2 : Strategy) : Prop :=
  ∀ (oStrat : Strategy) (s : GameState),
    strategyOutcome xStrat1 oStrat s = some (Outcome.wins Player.X) →
    strategyOutcome xStrat2 oStrat s ∈ [some (Outcome.wins Player.X), some Outcome.draw]

/-- Strategy is non-losing if it never loses (may win or draw). -/
def isNonLosingStrategy (xStrat : Strategy) : Prop :=
  ∀ (oStrat : Strategy) (s : GameState),
    strategyOutcome xStrat oStrat s ≠ some (Outcome.wins Player.O)

/-- Strategy is draw-forcing if it guarantees at least a draw. -/
def isDrawForcingStrategy (xStrat : Strategy) : Prop :=
  ∀ (oStrat : Strategy) (s : GameState),
    strategyOutcome xStrat oStrat s = some (Outcome.wins Player.X) ∨
    strategyOutcome xStrat oStrat s = some Outcome.draw

/-- Center-block strategy is non-losing. -/
theorem centerBlockIsNonLosing : isNonLosingStrategy xCenterBlockStrategy := by
  unfold isNonLosingStrategy strategyOutcome
  intro oStrat s
  sorry

/-- Center-block-fork strategy is non-losing. -/
theorem centerBlockForkIsNonLosing : isNonLosingStrategy xCenterBlockForkStrategy := by
  unfold isNonLosingStrategy strategyOutcome
  intro oStrat s
  sorry

/-- Fork strategy dominates center-block when forks are present. -/
theorem forkStrategyBetter :
    ∃ s : GameState,
      hasFork s.board Player.O ∧
      (strategyOutcome xCenterBlockForkStrategy greedyAny s = some (Outcome.wins Player.X) ∧
       strategyOutcome xCenterBlockStrategy greedyAny s ≠ some (Outcome.wins Player.X)) := by
  sorry

/-- Compare strategies on a specific board position. -/
def strategyComparison (xStrat1 xStrat2 : Strategy) (oStrat : Strategy) (s : GameState) :
    Outcome × Outcome :=
  match strategyOutcome xStrat1 oStrat s, strategyOutcome xStrat2 oStrat s with
  | some o1, some o2 => (o1, o2)
  | some o1, none => (o1, Outcome.ongoing)
  | none, some o2 => (Outcome.ongoing, o2)
  | none, none => (Outcome.ongoing, Outcome.ongoing)

/-- Greedy O strategy is suboptimal (X can force better outcome). -/
theorem greedyOSuboptimal :
    ∃ s : GameState,
      strategyOutcome xCenterBlockStrategy greedyAny s ≠ some (Outcome.wins Player.O) := by
  refine ⟨initialState, ?_⟩
  sorry

/-- Enhanced fork-aware strategy performs at least as well as basic center-block. -/
theorem forkAwareAtLeastAsGood :
    ∀ (oStrat : Strategy) (s : GameState),
      strategyOutcome xCenterBlockForkStrategy oStrat s = some (Outcome.wins Player.X) ∨
      strategyOutcome xCenterBlockForkStrategy oStrat s = some Outcome.draw ∨
      strategyOutcome xCenterBlockStrategy oStrat s = some (Outcome.wins Player.O) := by
  intro oStrat s
  sorry

end Tictactoe
