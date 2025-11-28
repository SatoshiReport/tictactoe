#!/usr/bin/env python3
"""Wrapper to launch the Stockfish MCP server with predictable env and logging."""

from __future__ import annotations

import os
import subprocess
import sys
import time
from pathlib import Path


LOG_FILE = Path("/tmp/stockfish_wrapper.log")
SERVER_SCRIPT = Path("/Users/mahrens917/tictactoe/scripts/stockfish_mcp.py")


def log(*args: object) -> None:
  ts = time.strftime("%Y-%m-%d %H:%M:%S")
  message = " ".join(str(a) for a in args)
  try:
    LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
    with LOG_FILE.open("a", encoding="utf-8") as fh:
      fh.write(f"[{ts}] {message}\n")
  except OSError:
    pass


def main() -> None:
  log("wrapper starting")
  log("cwd", os.getcwd())
  log("argv", sys.argv)

  env = os.environ.copy()
  env.setdefault("STOCKFISH_CMD", "/usr/local/bin/stockfish")
  env.setdefault("STOCKFISH_MCP_FRAMING", "newline")
  env.setdefault("PATH", "/usr/local/bin:/opt/homebrew/bin:/usr/bin:/bin")

  for key in ("STOCKFISH_CMD", "STOCKFISH_MCP_FRAMING", "PATH"):
    if key in env:
      log("env", key, env[key])

  if not SERVER_SCRIPT.exists():
    log("server script missing", SERVER_SCRIPT)
    sys.exit(1)

  cmd = [sys.executable, str(SERVER_SCRIPT)]
  log("spawning", cmd)
  proc = subprocess.Popen(
    cmd,
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE,
    env=env,
    cwd=str(SERVER_SCRIPT.parent),
  )
  if proc.stdout is None or proc.stderr is None or proc.stdin is None:
    log("failed to open pipes")
    sys.exit(1)

  def forward_once() -> bool:
    """Forward one request/response, logging full response."""
    line = sys.stdin.buffer.readline()
    if not line:
      return False
    log("[stdin]", line.decode("utf-8", errors="replace").rstrip("\n"))
    proc.stdin.write(line)
    proc.stdin.flush()

    # Read all available lines for this response (newline-framed).
    resp_chunks = []
    while True:
      resp = proc.stdout.readline()
      if not resp:
        break
      resp_chunks.append(resp)
      if resp.endswith(b"\n"):
        break
    if resp_chunks:
      joined = b"".join(resp_chunks)
      log("[stdout-chunk]", joined.decode("utf-8", errors="replace").rstrip("\n"))
      sys.stdout.write(joined.decode("utf-8", errors="replace"))
      sys.stdout.flush()
    return True

  while forward_once():
    pass

  for line in proc.stderr:
    log("[child-stderr]", line.decode("utf-8", errors="replace").rstrip("\n"))
  exit_code = proc.wait()
  log("child exited", exit_code)


if __name__ == "__main__":
  main()
