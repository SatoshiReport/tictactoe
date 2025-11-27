# Repository Guidelines

## Project Structure & Module Organization
- Keep application code in `src/`, grouping modules by concern (e.g., `src/engine/` for chess rules, `src/ui/` for any interface layer, `src/utils/` for helpers).
- Place automated tests in `tests/` mirroring the `src/` layout (`tests/engine/test_moves.py` for `src/engine/moves.py`).
- Store non-code assets in `assets/` (SVG pieces, sample PGN files) and long-form notes in `docs/`.
- Add one-off scripts in `scripts/` and prefer `Makefile` targets to wrap repeatable tasks.

## Build, Test, and Development Commands
- Install dependencies when they are added: `pip install -r requirements.txt` (use a tool like `pipx` or your preferred environment manager if needed).
- Run the test suite: `pytest` (add `-q` for compact output, `-k "<pattern>"` to target specific areas).
- Lint and format before pushing: `make lint` (expected to wrap tools like `ruff` and `black`) and `make fmt` if defined; otherwise run `ruff check src tests` and `black src tests`.
- If you add a CLI or service entry point, expose it via `python -m src.<module>` and document the usage in `README.md`.

## Coding Style & Naming Conventions
- Use 4-space indentation, type hints throughout, and explicit imports (avoid wildcard imports).
- Name modules and files in `snake_case`; classes in `CapWords`; constants in `UPPER_SNAKE_CASE`.
- Keep functions small; prefer pure functions in `src/engine` for move generation/validation to simplify testing.
- Run formatters before committing; do not hand-edit generated files.

## Testing Guidelines
- Write `pytest` tests named `test_*.py` with functions `test_<behavior>`. Co-locate fixtures in `conftest.py`.
- Aim for high coverage on core rules logic (move legality, check detection, draw rules). Add regression tests for discovered bugs.
- When adding features, provide table-driven tests where practical to cover edge cases (castling, en passant, stalemate).

## Commit & Pull Request Guidelines
- Use concise, present-tense commit messages (`feat: add rook move validator`, `fix: prevent illegal castle through check`).
- Reference issues in the body when applicable (`Refs #123`). Squash locally if the history is noisy.
- In pull requests, include a short summary, testing commands run, and screenshots or PGN samples if UI/output changes are involved.
- Keep changes scoped; split large efforts into reviewable chunks and mark TODOs with a clear follow-up plan.
