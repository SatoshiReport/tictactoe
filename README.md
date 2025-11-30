# Tic-Tac-Toe Formalization (Lean)

## Quick Start

```bash
# Build and verify all proofs
lake build

# Run tests
lake test

# Build and run the demo executable
lake build demo && lake env ./.lake/build/bin/demo
```

## Goal

Formalize tic-tac-toe in Lean and prove that with perfect play the game is a draw (X has a non-losing strategy) without brute force enumeration. We will:
- Model players, boards, legal moves, and winning lines.
- Define strategies as functions from histories to moves.
- Specify a concrete draw-forcing strategy for X (center-first, then block threats/forks).
- Prove safety and progress invariants showing O cannot force a win against this strategy.
- Conclude `∃ stratX, ∀ stratO, outcome (play stratX stratO emptyBoard) ≠ wins O`, establishing perfect play yields at worst a draw for X.

We will lean on the prover MCP tool for proof sketches while keeping the formalization human-guided (no brute force search).

Next, we want to turn the proof into an engine that plays and justifies each move to the user. The engine should surface the exact invariant or case split that motivates a move (e.g., "blocks the only fork; maintains no-double-threat invariant") so players see the reasoning, not just the move.

Why Lean proofs over other approaches:
- Proof-driven: guarantees cover all game states; no hidden failure cases unlike ML models trained on samples.
- Search-light: avoids brute-force enumeration; proofs shrink the game tree with reusable lemmas and invariants.
- Explainable: the same lemmas used in the proof produce human-readable reasons per move, instead of opaque model logits.
- Portable: once proved, the certified strategy and explanations are stable across platforms without re-tuning.

User benefit and theory:
- Users get both optimal play and transparent rationale, learning core tic-tac-toe theory (center control, threat blocking, fork prevention).
- The formal strategy mirrors the known solved-state theory: perfect play yields a draw, and every engine action maintains that theoretical guarantee.
