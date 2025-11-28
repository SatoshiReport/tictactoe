#!/usr/bin/env bash
# Lightweight CI helper inspired by ~/ci_shared/ci_tools/scripts/ci.sh.
# Stages all changes, asks Claude for a commit message from the staged diff, then pushes.
set -euo pipefail

ROOT_DIR="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "${ROOT_DIR}"

if ! command -v claude >/dev/null 2>&1; then
  echo "claude CLI is required to generate the commit message." >&2
  exit 1
fi

if ! command -v lake >/dev/null 2>&1; then
  echo "lake is required to run formatting, build, lint, and tests." >&2
  exit 1
fi

REMOTE="${REMOTE:-origin}"
BRANCH="${BRANCH:-$(git rev-parse --abbrev-ref HEAD)}"
MAX_DIFF_LINES="${MAX_DIFF_LINES:-1200}"
CLAUDE_MODEL="${CLAUDE_MODEL:-claude-haiku-4-5-20251001}"

if lake --help 2>/dev/null | grep -qE '^[[:space:]]+fmt[[:space:]]'; then
  echo "Running Lean formatter (lake fmt)..."
  lake fmt
else
  echo "lake fmt unavailable; skipping formatting. Consider upgrading Lean/Lake." >&2
fi

echo "Building Lean project (lake build)..."
lake build

if lake exe --help 2>/dev/null | grep -qE '(^|[[:space:]])lint([[:space:]]|$)'; then
  echo "Running mathlib lints (lake exe lint)..."
  lake exe lint
elif lake exe --help 2>/dev/null | grep -qE '(^|[[:space:]])lint-style([[:space:]]|$)'; then
  echo "Running mathlib style lints (lake exe lint-style)..."
  lake exe lint-style
elif lake exe mathlib:lint-style --help >/dev/null 2>&1; then
  echo "Running mathlib style lints (lake exe mathlib:lint-style)..."
  lake exe mathlib:lint-style
else
  echo "lake exe lint unavailable; skipping lints. Add a lint executable or upgrade mathlib to enable." >&2
fi

echo "Running tests (lake test)..."
lake test

echo "Staging changes..."
git add -A

if git diff --cached --quiet; then
  echo "No staged changes to commit."
  exit 0
fi

TMP_DIFF="$(mktemp)"
TRUNCATED_DIFF=""
trap 'rm -f "${TMP_DIFF}" "${TRUNCATED_DIFF:-}"' EXIT

git diff --cached > "${TMP_DIFF}"
DIFF_LINES="$(wc -l < "${TMP_DIFF}")"
DIFF_FILE="${TMP_DIFF}"

if [[ "${DIFF_LINES}" -gt "${MAX_DIFF_LINES}" ]]; then
  TRUNCATED_DIFF="$(mktemp)"
  head -n "${MAX_DIFF_LINES}" "${TMP_DIFF}" > "${TRUNCATED_DIFF}"
  {
    echo ""
    echo "[diff truncated to ${MAX_DIFF_LINES} of ${DIFF_LINES} lines]"
  } >> "${TRUNCATED_DIFF}"
  DIFF_FILE="${TRUNCATED_DIFF}"
  echo "Diff truncated for prompt: ${MAX_DIFF_LINES}/${DIFF_LINES} lines."
fi

PROMPT=$(cat <<'EOF'
Write a concise git commit message for this Lean TicTacToe formalization.
- Subject: present tense, <= 72 chars, no trailing period.
- Body: only if essential; keep short bullets or sentences.
- Note key Lean modules or scripts touched and testing if relevant.
- Output format: first line is subject only. If body is needed, add a blank line then bullet lines. No preamble or commentary.
Diff to summarize:
EOF
)

CLAUDE_CMD=(claude --model "${CLAUDE_MODEL}" -p -)

echo "Requesting commit message from Claude..."
COMMIT_RAW="$(
  {
    printf "%s\n\n" "${PROMPT}"
    cat "${DIFF_FILE}"
  } | "${CLAUDE_CMD[@]}"
)"

# Normalize subject/body. Use the first non-empty line as subject.
SUBJECT="$(printf "%s" "${COMMIT_RAW}" | sed '/^[[:space:]]*$/d' | head -n 1 | sed 's/^[[:space:]-]*//')"
BODY="$(printf "%s" "${COMMIT_RAW}" | sed '/^[[:space:]]*$/d' | sed '1d')"

if [[ -z "${SUBJECT//[[:space:]]/}" ]]; then
  echo "Claude returned an empty commit subject; aborting." >&2
  exit 1
fi

echo "Committing with message: ${SUBJECT}"
if [[ -n "${BODY//[[:space:]]/}" ]]; then
  git commit -m "${SUBJECT}" -m "${BODY}"
else
  git commit -m "${SUBJECT}"
fi

echo "Pushing to ${REMOTE}/${BRANCH}..."
git push "${REMOTE}" "${BRANCH}"

echo "Done."
