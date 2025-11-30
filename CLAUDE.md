# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Lean 4 project formalizing tic-tac-toe with the goal of proving that with perfect play, the game is a draw (X has a non-losing strategy) without brute force enumeration.

## Build Commands

```bash
# Build the project
lake build

# Run tests
lake test

# Build and run demo executable
lake build demo && lake env ./.lake/build/bin/demo

# Update dependencies (mathlib)
lake update

# Download mathlib cache (speeds up builds significantly)
lake exe cache get
```

## MCP Servers

- **stockfish**: available for search/evaluation; use when move-quality exploration helps a proof or example.
- **solve (Novita prover)**: use for proof sketches or tactic hints; keep final Lean proof minimal and readable.

## Architecture

The formalization lives in `Tictactoe/Main.lean` and includes:

- **Board representation**: 3×3 board as `Fin 3 → Fin 3 → Cell` where `Cell := Option Player`
- **Game state**: `GameState` struct containing board and turn indicator
- **Winning conditions**: Eight winning lines (3 rows, 3 cols, 2 diagonals) defined via `winningLines`
- **Strategy type**: `Strategy := History → GameState → Option Coord` - functions from game history to moves
- **X's strategy**: `xCenterBlockStrategy` - center-first, then block O's threats, then any legal move

Key types:
- `Coord := Fin 3 × Fin 3` - board positions
- `Player` - inductive type with `X` and `O` constructors
- `Board := Fin 3 → Fin 3 → Cell` - game board
- `GameState` - board plus whose turn

The approach proves safety invariants showing O cannot force a win against X's strategy, concluding that perfect play yields at worst a draw for X.

## Dependencies

- Lean 4 (v4.26.0-rc2)
- Mathlib4 (from master)

## Known Issues

### Classical Logic and Native Compilation

The formalization uses `classical` logic tactics extensively in proofs (especially in WinningLines.lean and Rules.lean). Lean 4's IR code generator cannot compile these to native code, causing "INTERNAL PANIC: unreachable code has been reached" at runtime.

**Solution**: The demo executable (`scripts/demo_standalone.lean`) is a self-contained implementation that does not import the formalization. This allows native compilation while the formalization proofs remain available for verification via `lake build`.

The formalization can still be run as an interpreted script if needed:
```bash
lake env lean --run scripts/some_script.lean
```
