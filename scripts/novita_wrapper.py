#!/usr/bin/env python3
"""Lightweight wrapper to trace how Codex launches the Novita MCP server.

Writes launch/debug info to /tmp/novita_wrapper.log and then execs the real
server with stdio passthrough. This helps confirm whether Codex actually
spawns the process and whether it closes stdin early.
"""

from __future__ import annotations

import os
import subprocess
import sys
import threading
import time
from pathlib import Path
from typing import Iterable


LOG_FILE = Path("/tmp/novita_wrapper.log")
SERVER_SCRIPT = Path("/Users/mahrens917/tictactoe/scripts/novita_mcp.py")
SAFE_ENV_KEYS: Iterable[str] = ("NOVITA_MCP_LOG", "NOVITA_MCP_FRAMING", "NOVITA_BASE_URL")


def log(*args: object) -> None:
    """Append a timestamped line to the wrapper log."""
    ts = time.strftime("%Y-%m-%d %H:%M:%S")
    message = " ".join(str(a) for a in args)
    try:
        LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
        with LOG_FILE.open("a", encoding="utf-8") as fh:
            fh.write(f"[{ts}] {message}\n")
    except OSError:
        pass


def stream_stderr(proc: subprocess.Popen[bytes]) -> None:
    """Forward child stderr into the wrapper log."""
    if proc.stderr is None:
        return
    for line in proc.stderr:
        try:
            text = line.decode("utf-8", errors="replace").rstrip("\n")
        except AttributeError:
            text = str(line).rstrip("\n")
        log("[child-stderr]", text)


def main() -> None:
    log("wrapper starting")
    log("cwd", os.getcwd())
    log("argv", sys.argv)

    env = os.environ.copy()
    env.setdefault("NOVITA_MCP_LOG", "/tmp/novita_mcp.log")
    env.setdefault("NOVITA_MCP_FRAMING", "auto")

    for key in SAFE_ENV_KEYS:
        if key in env:
            log("env", key, env[key])
    log("env NOVITA_API_KEY present" if "NOVITA_API_KEY" in env else "env NOVITA_API_KEY missing")

    if not SERVER_SCRIPT.exists():
        log("server script missing", SERVER_SCRIPT)
        sys.exit(1)

    cmd = [sys.executable, str(SERVER_SCRIPT)]
    log("spawning", cmd)
    proc = subprocess.Popen(
        cmd,
        stdin=sys.stdin.buffer,
        stdout=sys.stdout.buffer,
        stderr=subprocess.PIPE,
        env=env,
        cwd=str(SERVER_SCRIPT.parent),
    )

    stderr_thread = threading.Thread(target=stream_stderr, args=(proc,), daemon=True)
    stderr_thread.start()

    exit_code = proc.wait()
    stderr_thread.join(timeout=1)
    log("child exited", exit_code)


if __name__ == "__main__":
    main()
