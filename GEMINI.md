# Project: Tic-Tac-Toe Formalization (Lean)

## Overview
This project formalizes the game of Tic-Tac-Toe in Lean 4 using Mathlib. The primary goal is to mathematically prove that with perfect play, the game is a draw (specifically, that Player X has a non-losing strategy). The project also aims to produce an "explainable engine" where moves are justified by the formal proofs (e.g., "blocking a threat").

**Key Objectives:**
- Model the game (players, board, moves, rules).
- Define strategies (functions from game history to moves).
- Prove safety invariants (Player O cannot force a win against Player X's strategy).
- Create an engine that outputs moves with human-readable justifications based on the proofs.

## Technology Stack
- **Language:** Lean 4
- **Build System:** Lake
- **Dependencies:** Mathlib4 (git dependency)
- **Scripting:** Python (helper scripts in `scripts/`)

## Directory Structure
- **`Tictactoe/`**: Contains the Lean source code.
    - **`Game.lean`**: Core game definitions (Board, Player, Outcome).
    - **`Rules.lean`**: Game rules and legal moves.
    - **`WinningLines.lean`**: Definitions of winning conditions.
    - **`Strategy.lean`**: Strategy definitions (e.g., `xCenterBlockStrategy`).
    - **`Proofs/`**: Formal proofs (e.g., `Safety.lean` for safety invariants).
    - **`Main.lean`**: Demo/CLI logic (currently contains `playDemo`).
- **`scripts/`**: Helper scripts.
    - **`ci.sh`**: CI script for building, linting, testing, and committing.
    - **`stockfish_mcp.py`**, **`novita_mcp.py`**: MCP (Model Context Protocol) server wrappers.
- **`Tests/`**: Lean test files.
- **`lakefile.lean`**: Lake build configuration.
- **`AGENTS.md`**: Detailed guidelines for AI agents working on this codebase.

## Build & Run Instructions

### Prerequisites
- Lean 4 and Lake must be installed.
- Python (for scripts).

### Core Commands
*   **Build Project:**
    ```bash
    lake build
    ```
*   **Run Tests:**
    ```bash
    lake test
    ```
*   **Format Code:**
    ```bash
    lake fmt
    ```
*   **Linting:**
    ```bash
    # Run mathlib style lints
    lake env lean --run .lake/packages/mathlib/scripts/lint-style.lean
    ```
*   **CI Helper:**
    ```bash
    ./ci.sh
    ```
    *(Note: `ci.sh` stages changes, asks Claude for a commit message, and pushes. Use with caution or adapted for local checks.)*

## Development Conventions
*   **Style:** Adhere to Lean 4 conventions (two-space indentation in proofs, descriptive names).
*   **Module Organization:** Keep definitions in `Tictactoe/` and proofs in `Tictactoe/Proofs/` or separate files where appropriate.
*   **Documentation:** Use docstrings for public definitions.
*   **Testing:** Add tests for new logic. Tests should be registered in `Tests/Main.lean` (or similar) to run with `lake test`.
*   **External Tools:** The project uses MCP servers (`stockfish`, `novita`) for search/proof assistance as documented in `AGENTS.md`.

## Key Context for Agents
*   **`AGENTS.md`** is the authoritative source for style, structure, and workflow guidelines. **Read it first.**
*   **Mathlib Usage:** The project depends on Mathlib. Familiarity with Mathlib tactics (`simp`, `aesop`, `linarith`) is assumed.
*   **Formalization vs. Implementation:** The focus is on *formal verification*. Changes should prioritize correctness and provability over raw performance, though the "engine" aspect cares about explainability.
