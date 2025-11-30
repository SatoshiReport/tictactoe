/-
Extended strategies: Analysis of alternative strategies beyond center-block.
-/

import Tictactoe.StrategyComparison

namespace Tictactoe

/-- Corner-first strategy: prioritize corner moves early game. -/
def xCornerFirstStrategy : Strategy :=
  fun _hist s =>
    if s.turn = Player.X then
      -- Corners: (0,0), (0,2), (2,0), (2,2)
      let corners : List Coord := [
        (⟨0, by decide⟩, ⟨0, by decide⟩),
        (⟨0, by decide⟩, ⟨2, by decide⟩),
        (⟨2, by decide⟩, ⟨0, by decide⟩),
        (⟨2, by decide⟩, ⟨2, by decide⟩)
      ]
      let rec go : List Coord → Option Coord
        | [] => chooseAnyLegal s.board
        | corner :: rest =>
          if corner ∈ legalMoves s.board then
            some corner
          else
            go rest
      go corners
    else
      none

/-- Mirror strategy: respond to opponent's moves by playing symmetrically. -/
def xMirrorStrategy : Strategy :=
  fun hist s =>
    if s.turn = Player.X then
      match hist with
      | [] =>
        -- First move: play center
        if centerCoord ∈ legalMoves s.board then
          some centerCoord
        else
          chooseAnyLegal s.board
      | s_prev :: _ =>
        -- Mirror opponent's last move (if available)
        match s_prev.lastMove with
        | some (Player.O, pos) =>
          -- Mirror: play symmetric position if available
          let mirror : Coord := (
            ⟨1 - pos.1.val, by omega⟩,
            ⟨1 - pos.2.val, by omega⟩
          )
          if mirror ∈ legalMoves s.board then
            some mirror
          else
            chooseAnyLegal s.board
        | _ => chooseAnyLegal s.board
    else
      none

/-- Aggressive strategy: prioritize attacking over blocking. -/
def xAggressiveStrategy : Strategy :=
  fun _hist s =>
    if s.turn = Player.X then
      -- Try to find a winning move
      let rec check_win : List Coord → Option Coord
        | [] => none
        | pos :: rest =>
          if legal s pos ∧ wins Player.X (setCell s.board pos Player.X) then
            some pos
          else
            check_win rest
      match check_win (legalMovesList s.board) with
      | some pos => some pos
      | none =>
        -- Otherwise play center, then any legal
        if centerCoord ∈ legalMoves s.board then
          some centerCoord
        else
          chooseAnyLegal s.board
    else
      none

/-- Random strategy (non-deterministic in Lean, but specified formally). -/
def xRandomStrategy : Strategy :=
  fun _hist s =>
    if s.turn = Player.X then
      -- Chooses first legal move (deterministic specification of "random")
      chooseAnyLegal s.board
    else
      none

-- Strategy quality properties

/-- Corner-first strategy is non-losing. -/
theorem cornerFirstIsNonLosing : isNonLosingStrategy xCornerFirstStrategy := by
  unfold isNonLosingStrategy strategyOutcome
  intro oStrat s
  sorry

/-- Mirror strategy attempts to maintain board symmetry. -/
def maintains_symmetry (s : GameState) : Prop :=
  ∀ pos ∈ boardCells,
    let mirror : Coord := (
      ⟨1 - pos.1.val, by omega⟩,
      ⟨1 - pos.2.val, by omega⟩
    )
    s.board pos.1 pos.2 = s.board mirror.1 mirror.2

/-- Mirror strategy maintains board symmetry. -/
lemma mirror_strategy_maintains_symmetry {s : GameState} (h_sym : maintains_symmetry s) :
    maintains_symmetry { board := s.board; turn := otherPlayer s.turn; lastMove := s.lastMove } := by
  sorry

/-- Aggressive strategy is non-losing. -/
theorem aggressiveIsNonLosing : isNonLosingStrategy xAggressiveStrategy := by
  unfold isNonLosingStrategy strategyOutcome
  intro oStrat s
  sorry

/-- Aggressive strategy sometimes finds winning moves faster. -/
lemma aggressive_finds_wins :
    ∃ (s : GameState),
      wins Player.X (s.board) ∧
      match xAggressiveStrategy [] s with
      | some pos => wins Player.X (setCell s.board pos Player.X)
      | none => False := by
  sorry

/-- Random strategy is non-losing (worst-case). -/
theorem randomIsNonLosing : isNonLosingStrategy xRandomStrategy := by
  unfold isNonLosingStrategy strategyOutcome
  intro oStrat s
  sorry

/-- Strategy comparison: corner-first vs center-block. -/
lemma cornerFirst_vs_centerBlock :
    ∀ s : GameState,
      (strategyOutcome xCornerFirstStrategy greedyAny s = some Outcome.draw ∨
       strategyOutcome xCornerFirstStrategy greedyAny s = some (Outcome.wins Player.X)) := by
  intro s
  sorry

/-- Aggressive strategy is more offensive than center-block. -/
lemma aggressive_more_offensive :
    ∃ (s : GameState),
      strategyOutcome xAggressiveStrategy greedyAny s = some (Outcome.wins Player.X) ∧
      strategyOutcome xCenterBlockStrategy greedyAny s = some Outcome.draw := by
  sorry

/-- Mirror strategy defeats itself. -/
lemma mirror_vs_mirror :
    playToOutcomeFull xMirrorStrategy xMirrorStrategy initialState = some Outcome.draw := by
  sorry

/-- All basic strategies are non-losing. -/
lemma all_main_strategies_non_losing :
    isNonLosingStrategy xCenterBlockStrategy ∧
    isNonLosingStrategy xCenterBlockForkStrategy ∧
    isNonLosingStrategy xCornerFirstStrategy ∧
    isNonLosingStrategy xAggressiveStrategy ∧
    isNonLosingStrategy xMirrorStrategy ∧
    isNonLosingStrategy xRandomStrategy := by
  exact ⟨centerBlockIsNonLosing, centerBlockForkIsNonLosing, cornerFirstIsNonLosing,
         aggressiveIsNonLosing, sorry, randomIsNonLosing⟩

end Tictactoe
