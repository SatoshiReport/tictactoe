#!/usr/bin/env python3
"""
Minimal MCP server that exposes a single `bestmove` tool backed by Stockfish.

Input: a FEN string (required), optional depth (default 12) or movetime (ms).
Output: the best move Stockfish reports, plus info lines for traceability.
"""

from __future__ import annotations

import json
import subprocess
import sys
import time
import traceback
from pathlib import Path
import os
from typing import Any, Dict, Iterable, List, Optional

LOG_PATH = Path("/tmp/stockfish_mcp.log")


def log_debug(message: str) -> None:
    try:
        LOG_PATH.parent.mkdir(parents=True, exist_ok=True)
        ts = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        with open(LOG_PATH, "a", encoding="utf-8") as log:
            log.write(f"[{ts}] {message}\n")
    except OSError:
        pass


# Response framing mirrors the client: newline-delimited JSON or Content-Length.
FRAMING_MODE = os.getenv("STOCKFISH_MCP_FRAMING", "auto").lower()
SUPPORTED_PROTOCOL_VERSIONS = [
    "2024-11-05",
    "0.1.0",
    "0.1",
    "2025-03-26",
    "2025-06-18",
    "2025-11-25",
]
SERVER_INFO = {"name": "stockfish-mcp", "version": "0.1.0"}
INSTRUCTIONS = (
    "This MCP server exposes a single `bestmove` tool backed by Stockfish. "
    "Call tools/list to discover it, then tools/call with `fen` (required), "
    "`depth` (optional, default 12), or `movetime` (optional, ms)."
)
STOCKFISH_CMD = os.getenv("STOCKFISH_CMD", "stockfish")


def write_response(obj: Dict[str, Any]) -> None:
    data = json.dumps(obj, separators=(",", ":"))
    if FRAMING_MODE == "newline":
        log_debug(f"write_response newline len={len(data)} data={data}")
        sys.stdout.write(data + "\n")
    else:
        log_debug(f"write_response content-length len={len(data)} data={data}")
        sys.stdout.write(f"Content-Length: {len(data)}\r\n\r\n{data}")
    sys.stdout.flush()


def read_messages() -> Iterable[Any]:
    """Yield JSON messages from stdin, supporting Content-Length or newline framing."""
    buffer = ""
    while True:
        chunk = sys.stdin.readline()
        log_debug(f"read chunk: {chunk!r}")
        if not chunk:
            break
        buffer += chunk
        while True:
            if buffer.startswith("Content-Length:"):
                header, _, rest = buffer.partition("\r\n\r\n")
                if not rest:
                    break
                try:
                    length = int(header.split("Content-Length:")[1].strip().splitlines()[0])
                except Exception:
                    log_debug(f"failed to parse Content-Length from header {header!r}")
                    break
                if len(rest) < length:
                    break
                message, buffer = rest[:length], rest[length:]
            else:
                if "\n" not in buffer:
                    break
                message, buffer = buffer.split("\n", 1)
            if not message.strip():
                continue
            try:
                yield json.loads(message)
                log_debug(f"read message: {message}")
            except json.JSONDecodeError as e:
                log_debug(f"json decode error {e} on {message!r}")
                continue


def call_stockfish(fen: str, depth: int = 12, movetime: Optional[int] = None) -> Dict[str, Any]:
    if not fen.strip():
        raise ValueError("fen must be a non-empty string")
    depth = max(1, min(depth, 99))
    go_cmd = f"go depth {depth}"
    if movetime is not None:
        movetime = max(1, int(movetime))
        go_cmd = f"go movetime {movetime}"
    commands = ["uci", "isready", "ucinewgame", f"position fen {fen}", go_cmd, "quit"]
    payload = "\n".join(commands) + "\n"
    log_debug(f"invoking stockfish: {STOCKFISH_CMD} depth={depth} movetime={movetime}")
    proc = subprocess.run([STOCKFISH_CMD], input=payload, text=True, capture_output=True, timeout=20)
    output_lines = proc.stdout.splitlines()
    bestmove = None
    ponder = None
    infos: List[str] = []
    for line in output_lines:
        if line.startswith("info"):
            infos.append(line)
        if line.startswith("bestmove"):
            parts = line.split()
            if len(parts) >= 2:
                bestmove = parts[1]
            if len(parts) >= 4 and parts[2] == "ponder":
                ponder = parts[3]
    if bestmove is None:
        raise RuntimeError(f"No bestmove found. stdout: {proc.stdout!r}, stderr: {proc.stderr!r}")
    return {"bestmove": bestmove, "ponder": ponder, "info": infos, "raw": output_lines}


def handle_initialize(req_id: Any, params: Dict[str, Any]) -> None:
    log_debug(f"initialize params={params}")
    client_version = params.get("protocolVersion") if isinstance(params, dict) else None
    protocol_version = (
        client_version if client_version in SUPPORTED_PROTOCOL_VERSIONS else SUPPORTED_PROTOCOL_VERSIONS[0]
    )
    capabilities = {
        "tools": {"listChanged": False},
        "resources": {"listChanged": False, "subscribe": False},
        "prompts": {"listChanged": False},
        "logging": {},
    }
    write_response(
        {
            "jsonrpc": "2.0",
            "id": req_id,
            "result": {
                "protocolVersion": protocol_version,
                "serverInfo": SERVER_INFO,
                "capabilities": capabilities,
                "instructions": INSTRUCTIONS,
            },
        }
    )


def handle_list_tools(req_id: Any) -> None:
    log_debug("list_tools")
    write_response(
        {
            "jsonrpc": "2.0",
            "id": req_id,
            "result": {
                "tools": [
                    {
                        "name": "bestmove",
                        "description": "Query Stockfish for the best move of a position (UCI).",
                        "inputSchema": {
                            "type": "object",
                            "properties": {
                                "fen": {"type": "string", "description": "FEN string (required)"},
                                "depth": {"type": "integer", "description": "Search depth (default 12)"},
                                "movetime": {"type": "integer", "description": "Search time in ms (alternative to depth)"},
                            },
                            "required": ["fen"],
                        },
                    }
                ]
            },
        }
    )


def handle_list_resources(req_id: Any) -> None:
    log_debug("list_resources")
    write_response({"jsonrpc": "2.0", "id": req_id, "result": {"resources": []}})


def handle_list_resource_templates(req_id: Any) -> None:
    log_debug("list_resource_templates")
    write_response({"jsonrpc": "2.0", "id": req_id, "result": {"resourceTemplates": []}})


def handle_read_resource(req_id: Any, params: Dict[str, Any]) -> None:
    log_debug(f"read_resource params={params}")
    uri = params.get("uri")
    write_response(
        {
            "jsonrpc": "2.0",
            "id": req_id,
            "error": {"code": -32004, "message": f"No resources are available (requested {uri!r})"},
        }
    )


def handle_call_tool(req_id: Any, params: Dict[str, Any]) -> None:
    log_debug(f"call_tool params={params}")
    name = params.get("name")
    args = params.get("arguments", {}) or {}
    if name != "bestmove":
        write_response(
            {
                "jsonrpc": "2.0",
                "id": req_id,
                "error": {"code": -32602, "message": f"Unknown tool: {name}"},
            }
        )
        return

    fen = args.get("fen")
    if not isinstance(fen, str) or not fen.strip():
        write_response(
            {
                "jsonrpc": "2.0",
                "id": req_id,
                "error": {"code": -32602, "message": "fen is required and must be a non-empty string"},
            }
        )
        return
    depth = int(args.get("depth") or 12)
    movetime = args.get("movetime")
    movetime = int(movetime) if movetime is not None else None

    started = time.time()
    try:
        result = call_stockfish(fen, depth=depth, movetime=movetime)
        write_response(
            {
                "jsonrpc": "2.0",
                "id": req_id,
                "result": {
                    "content": [{"type": "text", "text": result["bestmove"]}],
                    "metadata": {
                        "ponder": result.get("ponder"),
                        "info": result.get("info"),
                        "latency_s": round(time.time() - started, 3),
                        "raw_output": result.get("raw"),
                    },
                },
            }
        )
    except Exception as e:  # noqa: BLE001
        sys.stderr.write(f"stockfish_mcp error: {e}\n")
        traceback.print_exc(file=sys.stderr)
        sys.stderr.flush()
        write_response(
            {
                "jsonrpc": "2.0",
                "id": req_id,
                "error": {"code": -32000, "message": str(e)},
            }
        )


def main() -> None:
    for msg in read_messages():
        if not isinstance(msg, dict):
            continue
        method = msg.get("method")
        req_id = msg.get("id")
        params = msg.get("params") or {}
        if req_id is None:
            continue
        if method == "initialize":
            handle_initialize(req_id, params)
        elif method in ("list_tools", "tools/list"):
            handle_list_tools(req_id)
        elif method in ("call_tool", "tools/call"):
            handle_call_tool(req_id, params)
        elif method in ("list_resources", "resources/list"):
            handle_list_resources(req_id)
        elif method in (
            "list_resource_templates",
            "resources/listTemplates",
            "resources/templates/list",
        ):
            handle_list_resource_templates(req_id)
        elif method in ("read_resource", "resources/read"):
            handle_read_resource(req_id, params)
        elif method == "shutdown":
            write_response({"jsonrpc": "2.0", "id": req_id, "result": None})
            break
        else:
            write_response(
                {
                    "jsonrpc": "2.0",
                    "id": req_id,
                    "error": {"code": -32601, "message": f"Unknown method {method}"},
                }
            )


if __name__ == "__main__":
    main()
