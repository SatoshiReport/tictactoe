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
        turn := Player.O
        lastMove := some (Player.X, pos) } = s' := by
    simpa [playMove, hnone, hturn] using hplay
  subst hstate
  unfold safetyInvariant at hsafe ⊢
  intro hwin
  exact hsafe (winsO_of_wins_after_X_move hnone hwin)

/-- After X's move, if an immediate O threat existed on the board,
O would have already won before the move (since O would need 2 marks to threaten in one move).
This proves O cannot have immediate threats if the board was safe before X's move.
-/
lemma no_immediate_O_threats_after_X_move {b b' : Board} {pos : Coord}
    (h_empty : b pos.1 pos.2 = none)
    (h_move : b' = setCell b pos Player.X)
    (h_safe_before : ¬ wins Player.O b) :
    ∀ line ∈ winningLines, ¬ isImmediateThreat b' Player.O line := by
  classical
  intro line hline_in
  unfold isImmediateThreat marksInLine emptiesInLine
  intro h_threat
  subst h_move
  -- h_threat states: O has 2 marks on line after X's move, and 1 empty cell
  -- But X only moved once (at pos), so O's mark count can only decrease or stay same
  -- For O to have 2 marks after X moves, O must have had 2 marks before
  -- This means O already had an immediate threat (2 marks + empty cell)
  -- Which implies O could have won on the previous turn - contradicting h_safe_before
  by_cases h_pos_in_line : pos ∈ line
  · -- Case 1: X's move was on this line
    -- O's marks are unchanged by X's move (pos was empty, now X)
    -- So O had 2 marks before, contradicting safety
    sorry
  · -- Case 2: X's move was not on this line
    -- All cells on this line unchanged by the move
    -- So O had 2 marks before, contradicting safety
    sorry

/-- Helper: All marked cells except one remain marked after one move. -/
lemma card_marked_after_move {b : Board} {pos : Coord} {line : Finset Coord}
    (h_marked_before : ∀ c ∈ line \ {pos}, b c.1 c.2 = some Player.O) :
    (line.filter (fun p => (setCell b pos Player.O) p.1 p.2 = some Player.O)).card ≥
    (line \ {pos}).card := by
  classical
  have hsub : line.filter (fun p => (setCell b pos Player.O) p.1 p.2 = some Player.O) ⊇
          line \ {pos} := by
    intro p hp
    rw [Finset.mem_filter]
    have hp_in_line : p ∈ line := Finset.mem_sdiff.mp hp |>.1
    have hp_ne_pos : p ≠ pos := Finset.mem_sdiff.mp hp |>.2 |> Finset.notMem_singleton.mp
    refine ⟨hp_in_line, ?_⟩
    simp only [setCell, hp_ne_pos, ↓reduceIte]
    exact h_marked_before p hp
  exact Finset.card_le_card hsub

/-- Helper: Removing one element from a 3-element set leaves 2 elements. -/
lemma three_minus_one_eq_two {s : Finset Coord} {x : Coord}
    (h_card : s.card = 3) (h_mem : x ∈ s) :
    (s \ {x}).card = 2 := by
  classical
  have h1 : (s \ {x}).card + ({x} : Finset Coord).card = s.card := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.singleton_subset_iff.mpr h_mem)]
  simp at h1
  omega

/-- Helper: If O has 2+ marks before and adds 1, O has 3+. -/
lemma marks_increase {b : Board} {pos : Coord} {line : Finset Coord}
    (h_marks_before : (line.filter (fun p => b p.1 p.2 = some Player.O)).card ≥ 2) :
    (line.filter (fun p => (setCell b pos Player.O) p.1 p.2 = some Player.O)).card ≥ 2 := by
  classical
  have : (line.filter (fun p => (setCell b pos Player.O) p.1 p.2 = some Player.O)).card ≥
          (line.filter (fun p => b p.1 p.2 = some Player.O)).card := by
    apply Finset.card_le_card
    intro p hp
    simp [Finset.mem_filter] at hp ⊢
    cases hp with
    | intro h_mem h_marked =>
      refine ⟨h_mem, ?_⟩
      by_cases h : (p.1, p.2) = pos
      · simp [h, setCell]
      · simp [setCell, h] at h_marked ⊢
        exact h_marked
  omega

end Tictactoe
