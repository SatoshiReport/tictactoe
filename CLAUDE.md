# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Lean 4 project formalizing tic-tac-toe with the goal of proving that with perfect play, the game is a draw (X has a non-losing strategy) without brute force enumeration.

## Build Commands

```bash
# Build the project
lake build

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

### Runtime Panic with `open Tictactoe`

The formalization includes extensive use of `classical` logic tactics in proofs (especially in WinningLines.lean and Rules.lean). When these proofs are imported at runtime and the Tictactoe namespace is opened, Lean 4's IR code generation fails with "INTERNAL PANIC: unreachable code has been reached".

**Workaround**: Do not use `open Tictactoe` in executable code. Instead:
- Use fully qualified names (e.g., `Tictactoe.Player.X` instead of `Player.X`)
- Import the modules as needed
- Keep the executable entry point minimal

This allows `lake build demo` to work correctly while avoiding the runtime panic.
