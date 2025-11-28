# MCP setup for Codex

This repo includes a minimal MCP server at `scripts/novita_mcp.py` that exposes a single `prove` tool backed by Novita's DeepSeek Prover model. Codex can launch it over stdio using the MCP config below. A companion server `scripts/stockfish_mcp.py` exposes a `bestmove` tool backed by Stockfish for chess positions.

## What changed (why Codex handshakes were failing)
- The server now mirrors whatever framing the client uses: if Codex sends `Content-Length` headers, responses are `Content-Length` framed; if it sends newline-delimited JSON, responses stay newline-delimited. Previously responses were always newline-delimited, which could cause clients that expect `Content-Length` frames to close the transport after `tools/list`.
- The default `protocolVersion` advertised is pinned to `2024-11-05`, which is the widest supported revision in current clients. Newer schema dates are still accepted if the client requests them.

## Config file placed for you
- Created `~/.config/codex/mcp.json` with the following entry:
  ```json
  {
    "mcpServers": {
      "solve": {
        "command": "python3",
        "args": ["/Users/mahrens917/tictactoe/scripts/novita_mcp.py"],
        "env": {
          "NOVITA_BASE_URL": "https://api.novita.ai/openai"
        },
        "autoRestart": true
      },
      "stockfish": {
        "command": "python3",
        "args": ["/Users/mahrens917/tictactoe/scripts/stockfish_mcp.py"],
        "autoRestart": true
      }
    }
  }
  ```
- The server speaks the MCP protocol up to the `2025-11-25` revision and understands the newer method names (`tools/list`, `resources/templates/list`, `prompts/*`, `logging/setLevel`, `roots/list`, `ping`, etc.), so it should handshake cleanly with recent Codex builds.
- If you need to force framing for debugging, set `NOVITA_MCP_FRAMING=content-length` (or `newline`) in the environment used to launch Codex; the default is auto-detect.

## Required secrets
- Set `NOVITA_API_KEY` in your shell (or add `NOVITA_API_KEY=...` to `~/.env` which the server reads). Without it, tool calls will fail with an auth error.

## Using it in Codex
- Restart Codex so it reloads `~/.config/codex/mcp.json`.
- In the MCP panel you should see a `solve` server with the `prove` tool. Invoke it with a `prompt` argument (optional `system`, `model`, `max_tokens`, `temperature`).
- You should also see a `stockfish` server with a `bestmove` tool. Invoke it with `fen` (required) and optionally `depth` or `movetime` (ms). It returns the UCI best move and Stockfish info lines.

## Optional local smoke test
Run the server directly and send MCP JSON-RPC over stdio (press Ctrl+D to end input):
```bash
python3 scripts/novita_mcp.py <<'EOF'
{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}
{"jsonrpc":"2.0","id":2,"method":"list_tools","params":{}}
EOF
```
You should see JSON responses. To test the tool, send a `call_tool` request with a `prompt` after initializing.

To exercise Content-Length framing explicitly:
```bash
python - <<'PY'
import json, subprocess
proc = subprocess.Popen(
    ["python3", "scripts/novita_mcp.py"],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    text=True,
)
messages = [
    {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}},
    {"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}},
]
for msg in messages:
    data = json.dumps(msg)
    proc.stdin.write(f"Content-Length: {len(data)}\\r\\n\\r\\n{data}")
    proc.stdin.flush()
proc.stdin.close()
print(proc.stdout.read())
PY
```

## Troubleshooting
- If Codex still reports a transport close on `initialize` or `tools/list`, confirm the running server binary is this repo's `scripts/novita_mcp.py` (which now mirrors `Content-Length` or newline framing) and not an older copy. Restart Codex after updating.
- If tool calls fail, check that `NOVITA_API_KEY` is present in your environment or `~/.env`.
