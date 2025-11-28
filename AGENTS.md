# Repository Guidelines

## Project Structure & Module Organization
- Lean code lives in `Tictactoe/`; keep modules focused (`Rules.lean`, `Strategy.lean`, `Proofs/Draw.lean`, etc.) and expose via `Tictactoe.lean`.
- Build configuration is in `lakefile.lean`; mathlib is the external dependency.
- CLI entry points (if added) live in `Tictactoe/Main.lean` and wire with `lake exe`.
- Tooling/MCP scripts are in `scripts/`; keep them Python-only with docstrings.
- Long-form notes in `docs/`; prefer proof sketches or strategy outlines there.

## Build, Test, and Development Commands
- `lake build` — compile all Lean modules and fetch dependencies.
- `lake env lean Tictactoe/Main.lean` — typecheck a single file in the project environment.
- `lake test` — run any registered Lean tests; add new tests to make this meaningful before PRs.
- `make lint` / `make fmt` — if you add these targets, wrap `lake exe lint`/`lake exe fmt` or `leanfmt` for consistency.
- MCP helpers: run `python scripts/novita_mcp.py` or `python scripts/stockfish_mcp.py` only after installing Python deps.

## MCP Servers
- `stockfish`: use for search/evaluation when move quality or symmetry cases matter; cite its lines in notes.
- `solve` (Novita prover): use for proof sketches or tactic hints; keep final Lean proofs readable and minimal.

## Coding Style & Naming Conventions
- Lean 4 style: two-space indentation in proofs, descriptive lemma names (`moveCount_le_nine`), explicit imports; avoid wide `open`.
- Prefer pure definitions in `Tictactoe/` with small lemmas; keep tactics light (`simp`, `aesop`, `linarith`) and structure proofs instead of long `by` blobs.
- Use docstrings for public defs/lemmas; favor `namespace Tictactoe` and sub-namespaces for clarity.

## Testing Guidelines
- Add proof-style tests/lemmas near the code they exercise; for executable tests, mirror module layout under `tests/` and register with Lake so `lake test` runs them.
- Name tests descriptively (`test_playMove_rejects_filled_cell`) and cover corner cases (occupied cells, draw detection, symmetry/fork scenarios).
- Run `lake build` (and `lake test` if present) before pushing; avoid slowing the build with heavy proofs.

## Commit & Pull Request Guidelines
- Commit messages: short present tense (`feat: add winningLines`, `fix: reject illegal move`); reference issues in the body when relevant.
- PRs: include a brief summary, commands run (`lake build`, `lake test`), and proof sketches or strategy notes that justify the change; add screenshots only if you introduce CLI/visual output.
- Keep changes scoped; leave TODOs with follow-up intent (`-- TODO: prove optimality of blocking strategy`).
