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
  simp only []
  intro h_threat
  subst h_move
  -- h_threat states: O has 2 marks on line after X's move, and 1 empty cell
  -- But X only moved once (at pos), so O's mark count can only decrease or stay same
  -- For O to have 2 marks after X moves, O must have had 2 marks before
  -- This means O already had an immediate threat (2 marks + empty cell)
  -- Which implies O could have won on the previous turn - contradicting h_safe_before
  by_cases h_pos_in_line : pos ∈ line
  · -- Case 1: X's move was on this line
    -- Before move: O had some marks on line, pos was empty
    -- After move: O has same marks (pos is now X, so can't contribute O marks)
    -- So if O has 2 marks after, O had 2 marks before
    have h_O_marks_after : (line.filter (fun p => setCell b pos Player.X p.1 p.2 = some Player.O)).card = 2 :=
      h_threat.1
    have h_O_marks_before : (line.filter (fun p => b p.1 p.2 = some Player.O)).card = 2 := by
      -- The only difference is at pos
      have h_change : ∀ q ∈ line, q ≠ pos →
          (setCell b pos Player.X q.1 q.2 = some Player.O ↔ b q.1 q.2 = some Player.O) := by
        intro q hq h_ne
        simp [setCell, h_ne]
      -- Count marks excluding pos
      have h_marks_excl_pos :
          (line.filter (fun p => b p.1 p.2 = some Player.O ∧ (p.1, p.2) ≠ pos)).card =
          (line.filter (fun p => b p.1 p.2 = some Player.O)).card := by
        apply Finset.card_congr
        intro p hp
        simp only [Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, fun h => by
          simp [Prod.ext_iff] at h
          exact ⟨hp.1, h⟩⟩
      have h_after_only_non_pos : (line.filter (fun p => setCell b pos Player.X p.1 p.2 = some Player.O)).card =
                                   (line.filter (fun p => b p.1 p.2 = some Player.O ∧ (p.1, p.2) ≠ pos)).card := by
        apply Finset.card_congr
        intro p _
        simp only [Finset.mem_filter, and_iff_left_iff_imp]
        intro h_marked
        constructor
        · intro _
          refine ⟨?_, ?_⟩
          · by_contra h_ne
            simp [h_ne] at h_marked
            subst h_ne
            simp [h_empty] at h_marked
          · intro h_eq
            simp [Prod.ext_iff] at h_eq
            have : setCell b pos Player.X pos.1 pos.2 = some Player.X := by simp [setCell]
            rw [h_eq] at this
            simp at this
        · intro ⟨h_O, h_ne⟩
          simp [setCell, h_ne, h_O]
      simp only [h_after_only_non_pos] at h_O_marks_after
      simp only [h_marks_excl_pos] at h_O_marks_after
      exact h_O_marks_after
    -- Now if O had 2 marks before, it contradicts h_safe_before
    have : wins Player.O b := ⟨line, hline_in, fun q hq =>
      (line.filter (fun p => b p.1 p.2 = some Player.O)).mem_filter q⟩
    exact h_safe_before this
  · -- Case 2: X's move was not on this line
    -- All cells on this line unchanged by the move
    have h_O_marks_after : (line.filter (fun p => setCell b pos Player.X p.1 p.2 = some Player.O)).card = 2 :=
      h_threat.1
    have h_O_marks_before : (line.filter (fun p => b p.1 p.2 = some Player.O)).card = 2 := by
      apply Finset.card_congr
      intro p _
      simp [setCell, h_pos_in_line]
      rfl
    simp only [h_O_marks_before] at h_O_marks_after
    have : wins Player.O b := ⟨line, hline_in, fun q hq =>
      (line.filter (fun p => b p.1 p.2 = some Player.O)).mem_filter q⟩
    exact h_safe_before this

/-- Helper: All marked cells except one remain marked after one move. -/
lemma card_marked_after_move {b : Board} {pos : Coord} {line : Finset Coord}
    (h_marked_before : ∀ c ∈ line \ {pos}, b c.1 c.2 = some Player.O) :
    (line.filter (fun p => (setCell b pos Player.O) p.1 p.2 = some Player.O)).card ≥
    (line \ {pos}).card := by
  classical
  have : line.filter (fun p => (setCell b pos Player.O) p.1 p.2 = some Player.O) ⊇
          line \ {pos} := by
    intro p hp
    simp [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨hp, by simp [setCell, hp.2, h_marked_before p hp]⟩
  exact Finset.card_le_card this

/-- Helper: Removing one element from a 3-element set leaves 2 elements. -/
lemma three_minus_one_eq_two {s : Finset Coord} {x : Coord}
    (h_card : s.card = 3) (h_mem : x ∈ s) :
    (s \ {x}).card = 2 := by
  classical
  have : (s \ {x}).card = s.card - 1 := by
    have h_disjoint : Disjoint (s \ {x}) {x} := by
      simp [Finset.disjoint_iff_inf_le, Finset.le_eq_subset]
    have h_cover : s \ {x} ∪ {x} = s := by
      ext p
      simp [Finset.mem_sdiff, Finset.mem_singleton]
      tauto
    have := Finset.card_union_of_disjoint h_disjoint
    rw [h_cover] at this
    simp at this
    omega
  simp [h_card] at this
  exact this

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
