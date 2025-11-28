import Tictactoe.Strategy

namespace Tictactoe

open Classical

/-- Terminal game outcomes. -/
inductive Outcome
  | wins (p : Player)
  | draw
  | ongoing
  deriving Repr, DecidableEq

/-- Classify a board without looking at future moves. -/
noncomputable def boardOutcome (b : Board) : Outcome :=
  if wins Player.X b then
    Outcome.wins Player.X
  else if wins Player.O b then
    Outcome.wins Player.O
  else if moveCount b = 9 then
    Outcome.draw
  else
    Outcome.ongoing

/-- Apply the current player's strategy for one turn, if it produces a legal move. -/
noncomputable def step (xStrat oStrat : Strategy) (hist : History) (s : GameState) :
    Option GameState :=
  let strat := if s.turn = Player.X then xStrat else oStrat
  match strat hist s with
  | none => none
  | some pos =>
    if _ : legal s pos then
      playMove s pos
    else
      none

/-- Run at most `n` turns, threading history as most-recent-first. -/
noncomputable def playN (xStrat oStrat : Strategy) : Nat → History → GameState → Option GameState
  | Nat.zero, _, s => some s
  | Nat.succ n, hist, s =>
    match step xStrat oStrat hist s with
    | none => none
    | some s' => playN xStrat oStrat n (s' :: hist) s'

/-- Run until a terminal outcome or until the fuel `n` is exhausted. -/
noncomputable def playToOutcome (xStrat oStrat : Strategy) :
    Nat → History → GameState → Option Outcome
  | Nat.zero, _, s => some (boardOutcome s.board)
  | Nat.succ n, hist, s =>
    match boardOutcome s.board with
    | Outcome.ongoing =>
        match step xStrat oStrat hist s with
        | none => none
        | some s' => playToOutcome xStrat oStrat n (s' :: hist) s'
    | outcome => some outcome

end Tictactoe
