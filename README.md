# Tic-Tac-Toe Formalization (Lean)

Goal: formalize tic-tac-toe in Lean and prove that with perfect play the game is a draw (X has a non-losing strategy) without brute force enumeration. We will:
- Model players, boards, legal moves, and winning lines.
- Define strategies as functions from histories to moves.
- Specify a concrete draw-forcing strategy for X (center-first, then block threats/forks).
- Prove safety and progress invariants showing O cannot force a win against this strategy.
- Conclude `∃ stratX, ∀ stratO, outcome (play stratX stratO emptyBoard) ≠ wins O`, establishing perfect play yields at worst a draw for X.

We will lean on the Novita prover MCP tool for proof sketches while keeping the formalization human-guided (no brute force search).
