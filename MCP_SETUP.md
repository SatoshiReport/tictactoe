# MCP setup: Stockfish + Solve (Novita) for Codex

This repo includes two MCP servers:
- `scripts/novita_mcp.py` (exposed as the `solve` server) for Lean proof assistance via Novita/DeepSeek.
- `scripts/stockfish_mcp.py` for chess best-move queries via Stockfish.

This guide documents how to configure Codex and troubleshoot startup to avoid repeating the investigation.

## Prerequisites
- Stockfish installed (Homebrew: `brew install stockfish`). Binary at `/usr/local/bin/stockfish`.
- Python 3.12 available (the repo scripts assume `/usr/local/bin/python3` or `/opt/homebrew/opt/python@3.12/bin/python3.12`).
- Environment variable `NOVITA_API_KEY` set for the `solve` server.

## Configuration files

### User-level Codex config (`~/.codex/config.toml`)
Use table entries under `mcp_servers.*`. Example:
```toml
[mcp_servers.solve]
command = "python3"
args = ["/Users/mahrens917/tictactoe/scripts/novita_wrapper.py"]

[mcp_servers.solve.env]
NOVITA_BASE_URL = "https://api.novita.ai/openai"
NOVITA_MCP_FRAMING = "auto"
NOVITA_MCP_LOG = "/tmp/novita_mcp.log"

[mcp_servers.stockfish]
command = "python3"
args = ["/Users/mahrens917/tictactoe/scripts/stockfish_mcp.py"]

[mcp_servers.stockfish.env]
STOCKFISH_MCP_FRAMING = "newline"
STOCKFISH_CMD = "/usr/local/bin/stockfish"
PATH = "/usr/local/bin:/opt/homebrew/bin:/usr/bin:/bin"
```

### MCP override file (`~/.mcp.json`)
Codex can also read a JSON config via `CODEX_MCP_CONFIG=...`. Example:
```json
{
  "mcpServers": {
    "solve": {
      "command": "python3",
      "args": ["/Users/mahrens917/tictactoe/scripts/novita_wrapper.py"],
      "env": {
        "NOVITA_BASE_URL": "https://api.novita.ai/openai",
        "NOVITA_MCP_FRAMING": "auto",
        "NOVITA_MCP_LOG": "/tmp/novita_mcp.log"
      },
      "autoRestart": true
    },
    "stockfish": {
      "command": "python3",
      "args": ["/Users/mahrens917/tictactoe/scripts/stockfish_mcp.py"],
      "env": {
        "STOCKFISH_MCP_FRAMING": "newline",
        "STOCKFISH_CMD": "/usr/local/bin/stockfish",
        "PATH": "/usr/local/bin:/opt/homebrew/bin:/usr/bin:/bin"
      },
      "autoRestart": true
    }
  }
}
```

### Repo-level convenience (`.mcp.json`)
The repo keeps a similar config for reference:
```json
{
  "mcpServers": {
    "solve": {
      "command": "/Users/mahrens917/tictactoe/scripts/novita_wrapper.py",
      "args": [],
      "env": {
        "NOVITA_BASE_URL": "https://api.novita.ai/openai",
        "NOVITA_MCP_FRAMING": "auto",
        "NOVITA_MCP_LOG": "/tmp/novita_mcp.log"
      },
      "disabled": false
    },
    "stockfish": {
      "command": "python3",
      "args": ["/Users/mahrens917/tictactoe/scripts/stockfish_mcp.py"],
      "env": {
        "STOCKFISH_MCP_FRAMING": "newline",
        "STOCKFISH_CMD": "/usr/local/bin/stockfish",
        "PATH": "/usr/local/bin:/opt/homebrew/bin:/usr/bin:/bin"
      },
      "disabled": false
    }
  }
}
```

## Framing and environment
- Solve (Novita): `NOVITA_MCP_FRAMING=auto` works; it mirrors client framing.
- Stockfish: Codex handshake succeeded with `STOCKFISH_MCP_FRAMING=newline`. Content-Length framing caused Codex to close after `initialize`.
- Ensure `STOCKFISH_CMD` points to the actual binary. Set a minimal PATH so the Codex sandbox finds the binary.

## Logs and troubleshooting
- Novita wrapper log: `/tmp/novita_wrapper.log`
- Novita MCP log (if `NOVITA_MCP_LOG` set): `/tmp/novita_mcp.log`
- Stockfish MCP log: `/tmp/stockfish_mcp.log` (added logging inside `stockfish_mcp.py`).

What we saw during debugging:
- When framing mismatched, Codex closed after `initialize` without `tools/list`.
- With newline framing, Codex proceeded.
- If Codex keeps showing an old server name, check `~/.codex/config.toml` for stale entries (e.g., `novita`) and remove/rename.
- Clearing Codex caches can help: `rm -rf ~/Library/Caches/codex ~/Library/Caches/openai-codex ~/.cache/codex ~/.cache/openai-codex`

## Smoke tests (local)
Run the Stockfish server directly:
```bash
python3 scripts/stockfish_mcp.py <<'EOF'
{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}
{"jsonrpc":"2.0","id":2,"method":"tools/list","params":{}}
EOF
```
You should see JSON responses and `Content-Length` headers.

## Codex launch tips
- Ensure `~/.codex/config.toml` matches the desired MCP servers.
- Optionally force a config: `CODEX_MCP_CONFIG=$HOME/.mcp.json codex`
- If Codex shows only the old `novita` entry, edit `~/.codex/config.toml` to remove it and re-add `solve`/`stockfish`.

