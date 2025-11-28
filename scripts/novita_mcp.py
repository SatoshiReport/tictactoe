#!/usr/bin/env python3
"""
Minimal MCP server that exposes a single tool `prove` backed by Novita's
OpenAI-compatible chat endpoint for the DeepSeek Prover model.

Usage: the client (e.g., Codex) launches this script as an MCP server over stdio.
It requires `NOVITA_API_KEY` (preferably set in the environment). If not set,
the script will try to read it from ~/.env.
"""

import json
import os
import sys
import time
import traceback
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any, Dict, Optional


DEFAULT_BASE_URL = "https://api.novita.ai/openai"
DEFAULT_MODEL = "deepseek/deepseek-prover-v2-671b"
DEFAULT_MAX_TOKENS = 4096
DEFAULT_TEMPERATURE = 0.2
MAX_ALLOWED_TOKENS = 200_000
# Response framing defaults to auto-detecting the incoming transport. Set NOVITA_MCP_FRAMING
# to "content-length" or "newline" to force a specific framing style.
FRAMING_MODE = os.getenv("NOVITA_MCP_FRAMING", "auto").lower()
SUPPORTED_PROTOCOL_VERSIONS = [
    # Prefer the broadly supported 2024-11-05 revision for compatibility with current clients.
    "2024-11-05",
    "0.1.0",
    "0.1",
    "2025-03-26",
    "2025-06-18",
    "2025-11-25",
]
SERVER_INFO = {"name": "novita-mcp", "version": "0.1.0"}
INSTRUCTIONS = (
    "This MCP server exposes a single `prove` tool backed by Novita's DeepSeek Prover. "
    "Call tools/list to discover it, then tools/call with a `prompt` containing Lean code or a "
    "proof request. Optional fields: system, model, max_tokens, temperature."
)
LOG_PATH = os.getenv("NOVITA_MCP_LOG")
RESPONSE_FRAMING: Optional[str]
if FRAMING_MODE in ("content-length", "newline"):
    RESPONSE_FRAMING = FRAMING_MODE
else:
    FRAMING_MODE = "auto"
    RESPONSE_FRAMING = None


def log_debug(message: str) -> None:
    if not LOG_PATH:
        return
    try:
        Path(LOG_PATH).parent.mkdir(parents=True, exist_ok=True)
        ts = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        with open(LOG_PATH, "a", encoding="utf-8") as log:
            log.write(f"[{ts}] {message}\n")
    except OSError:
        pass


def load_api_key() -> Optional[str]:
    """Fetch NOVITA_API_KEY from the environment or fall back to ~/.env."""
    key = os.getenv("NOVITA_API_KEY")
    if key:
        return key
    env_path = os.path.expanduser("~/.env")
    if not os.path.exists(env_path):
        return None
    try:
        with open(env_path, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith("#"):
                    continue
                if line.startswith("NOVITA_API_KEY="):
                    return line.split("=", 1)[1].strip()
    except OSError:
        return None
    return None


def call_novita(
    prompt: str,
    model: str,
    max_tokens: int,
    temperature: float,
    system: Optional[str] = None,
) -> Dict[str, Any]:
    """Call Novita's OpenAI-style chat endpoint and return the parsed JSON."""
    api_key = load_api_key()
    if not api_key:
        raise RuntimeError("NOVITA_API_KEY not found (set env var or put it in ~/.env)")

    base_url = os.getenv("NOVITA_BASE_URL", DEFAULT_BASE_URL).rstrip("/")
    api_url = f"{base_url}/v1/chat/completions"

    messages = []
    if system:
        messages.append({"role": "system", "content": system})
    messages.append({"role": "user", "content": prompt})

    payload = {
        "model": model,
        "messages": messages,
        "max_tokens": max_tokens,
        "temperature": temperature,
    }
    data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(
        api_url,
        data=data,
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=120) as resp:
            body = resp.read().decode("utf-8")
            return json.loads(body)
    except urllib.error.HTTPError as e:
        msg = e.read().decode("utf-8", errors="ignore")
        raise RuntimeError(f"Novita HTTP error {e.code}: {msg}") from e
    except urllib.error.URLError as e:
        raise RuntimeError(f"Novita connection error: {e}") from e


def write_response(message: Dict[str, Any]) -> None:
    """Send a JSON-RPC response using either Content-Length or newline framing."""
    global RESPONSE_FRAMING
    payload = json.dumps(message, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    framing = RESPONSE_FRAMING or "newline"
    log_debug(
        f"sending response id={message.get('id')} framing={framing} "
        f"bytes={len(payload)} method={message.get('result') and 'result' or message.get('error') and 'error'}"
    )
    if framing == "content-length":
        header = f"Content-Length: {len(payload)}\r\n\r\n".encode("ascii")
        sys.stdout.buffer.write(header + payload)
    else:
        sys.stdout.buffer.write(payload + b"\n")
    sys.stdout.buffer.flush()


def read_messages():
    """Yield JSON-RPC messages supporting both newline-delimited and Content-Length framing."""
    global RESPONSE_FRAMING
    buf = sys.stdin.buffer
    while True:
        header = buf.readline()
        if not header:
            break
        header_str = header.decode("utf-8", errors="ignore")
        log_debug(f"header: {header_str!r}")

        # If framing was forced to content-length but we see a JSON line, fall back to newline framing.
        if FRAMING_MODE == "content-length" and not header_str.lower().startswith("content-length:"):
            try:
                msg = json.loads(header_str.strip())
            except json.JSONDecodeError:
                msg = None
            if msg is not None:
                RESPONSE_FRAMING = "newline"
                log_debug("content-length requested but newline payload detected; falling back to newline framing")
                log_debug(f"received message via newline: method={msg.get('method')} id={msg.get('id')}")
                yield msg
                continue

        # Content-Length framing
        if header_str.lower().startswith("content-length:"):
            if FRAMING_MODE == "auto" and RESPONSE_FRAMING is None:
                RESPONSE_FRAMING = "content-length"
            try:
                length = int(header_str.split(":", 1)[1].strip())
            except (ValueError, IndexError):
                log_debug(f"invalid Content-Length line: {header_str!r}")
                continue
            # Consume headers until blank line
            while True:
                sep = buf.readline()
                if sep:
                    log_debug(f"sub-header: {sep!r}")
                if not sep or sep in (b"\n", b"\r\n"):
                    break
            if length <= 0:
                log_debug(f"empty Content-Length {length}")
                continue
            body = b""
            while len(body) < length:
                chunk = buf.read(length - len(body))
                if not chunk:
                    break
                body += chunk
            if len(body) < length:
                log_debug(f"short read, expected {length} bytes got {len(body)}")
                break
            try:
                msg = json.loads(body)
            except json.JSONDecodeError:
                log_debug(f"failed to decode Content-Length body: {body!r}")
                continue
            log_debug(f"received message via content-length: method={msg.get('method')} id={msg.get('id')}")
            yield msg
            continue

        line = header_str.strip()
        if not line:
            continue

        # If we are still auto-detecting and the line looks like a header (e.g., Content-Type),
        # skip it so we don't incorrectly lock into newline framing before seeing Content-Length.
        if (
            FRAMING_MODE == "auto"
            and RESPONSE_FRAMING is None
            and ":" in line
            and line.split(":", 1)[0].replace("-", "").isalpha()
        ):
            log_debug(f"skipping stray header while auto-detecting framing: {line!r}")
            continue

        try:
            msg = json.loads(line)
            if FRAMING_MODE == "auto" and RESPONSE_FRAMING is None:
                RESPONSE_FRAMING = "newline"
                log_debug("auto-detected newline framing")
            log_debug(f"received message via newline: method={msg.get('method')} id={msg.get('id')}")
            yield msg
        except json.JSONDecodeError:
            log_debug(f"failed to decode newline-delimited payload: {line!r}")
            continue


def handle_initialize(req_id: Any, params: Dict[str, Any]) -> None:
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
    write_response(
        {
            "jsonrpc": "2.0",
            "id": req_id,
            "result": {
                "tools": [
                    {
                        "name": "prove",
                        "description": "Send a prompt to Novita DeepSeek Prover (OpenAI-compatible chat).",
                        "inputSchema": {
                            "type": "object",
                            "properties": {
                                "prompt": {"type": "string", "description": "Lean code or proof request"},
                                "system": {
                                    "type": "string",
                                    "description": "Optional system prompt (e.g., proof style or constraints)",
                                },
                                "model": {
                                    "type": "string",
                                    "description": f"Model name (default {DEFAULT_MODEL})",
                                },
                                "max_tokens": {
                                    "type": "integer",
                                    "minimum": 1,
                                    "maximum": MAX_ALLOWED_TOKENS,
                                    "description": "Response token limit",
                                },
                                "temperature": {
                                    "type": "number",
                                    "minimum": 0,
                                    "maximum": 2,
                                    "description": "Sampling temperature",
                                },
                            },
                            "required": ["prompt"],
                        },
                    }
                ]
            },
        }
    )


def handle_list_resources(req_id: Any) -> None:
    write_response({"jsonrpc": "2.0", "id": req_id, "result": {"resources": []}})


def handle_list_resource_templates(req_id: Any) -> None:
    write_response({"jsonrpc": "2.0", "id": req_id, "result": {"resourceTemplates": []}})


def handle_read_resource(req_id: Any, params: Dict[str, Any]) -> None:
    uri = params.get("uri")
    write_response(
        {
            "jsonrpc": "2.0",
            "id": req_id,
            "error": {"code": -32004, "message": f"No resources are available (requested {uri!r})"},
        }
    )


def handle_subscribe_resource(req_id: Any, params: Dict[str, Any]) -> None:
    uri = params.get("uri")
    write_response(
        {
            "jsonrpc": "2.0",
            "id": req_id,
            "error": {"code": -32004, "message": f"Resource subscriptions are not supported (requested {uri!r})"},
        }
    )


def handle_unsubscribe_resource(req_id: Any, params: Dict[str, Any]) -> None:
    uri = params.get("uri")
    write_response(
        {
            "jsonrpc": "2.0",
            "id": req_id,
            "error": {"code": -32004, "message": f"Resource subscriptions are not supported (requested {uri!r})"},
        }
    )


def handle_list_prompts(req_id: Any) -> None:
    write_response({"jsonrpc": "2.0", "id": req_id, "result": {"prompts": []}})


def handle_get_prompt(req_id: Any, params: Dict[str, Any]) -> None:
    prompt_name = params.get("name")
    write_response(
        {
            "jsonrpc": "2.0",
            "id": req_id,
            "error": {"code": -32004, "message": f"Prompt {prompt_name!r} not found"},
        }
    )


def handle_ping(req_id: Any) -> None:
    write_response({"jsonrpc": "2.0", "id": req_id, "result": {}})


def handle_set_logging_level(req_id: Any) -> None:
    write_response({"jsonrpc": "2.0", "id": req_id, "result": {}})


def handle_list_roots(req_id: Any) -> None:
    repo_root = Path(__file__).resolve().parent.parent
    write_response(
        {
            "jsonrpc": "2.0",
            "id": req_id,
            "result": {"roots": [{"uri": repo_root.as_uri(), "name": repo_root.name}]},
        }
    )


def handle_call_tool(req_id: Any, params: Dict[str, Any]) -> None:
    name = params.get("name")
    args = params.get("arguments", {}) or {}
    if name != "prove":
        write_response(
            {
                "jsonrpc": "2.0",
                "id": req_id,
                "error": {"code": -32602, "message": f"Unknown tool: {name}"},
            }
        )
        return

    prompt = args.get("prompt")
    if not isinstance(prompt, str) or not prompt.strip():
        write_response(
            {
                "jsonrpc": "2.0",
                "id": req_id,
                "error": {"code": -32602, "message": "prompt is required and must be a non-empty string"},
            }
        )
        return

    model = args.get("model") or DEFAULT_MODEL
    max_tokens = int(args.get("max_tokens") or DEFAULT_MAX_TOKENS)
    max_tokens = max(1, min(MAX_ALLOWED_TOKENS, max_tokens))
    temperature = float(args.get("temperature") or DEFAULT_TEMPERATURE)
    system_msg = args.get("system")

    started = time.time()
    try:
        novita_resp = call_novita(prompt, model, max_tokens, temperature, system=system_msg)
        choices = novita_resp.get("choices") or []
        content = None
        finish_reason = None
        if choices:
            content = choices[0].get("message", {}).get("content")
            finish_reason = choices[0].get("finish_reason")

        # MCP tool results expect a content array of blocks.
        text_content = content if isinstance(content, str) else json.dumps(content) if content is not None else ""
        result_payload = {
            "content": [{"type": "text", "text": text_content}],
            "metadata": {
                "finish_reason": finish_reason,
                "latency_s": round(time.time() - started, 3),
            },
        }
        # Include the raw provider response for debugging/traceability.
        result_payload["metadata"]["raw_response"] = novita_resp

        write_response(
            {
                "jsonrpc": "2.0",
                "id": req_id,
                "result": result_payload,
            }
        )
    except Exception as e:  # noqa: BLE001
        # Emit details to stderr so CLI logs surface the failure reason.
        sys.stderr.write(f"novita_mcp error: {e}\n")
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
    log_debug(
        f"starting novita_mcp: framing_mode={FRAMING_MODE}, "
        f"response_framing={RESPONSE_FRAMING}, log_path={LOG_PATH}"
    )
    for msg in read_messages():
        if not isinstance(msg, dict):
            continue

        method = msg.get("method")
        req_id = msg.get("id")
        params = msg.get("params") or {}

        # Ignore JSON-RPC notifications (no id), e.g., notifications/initialized from Codex.
        if req_id is None:
            log_debug(f"ignoring notification method={method}")
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
        elif method in ("resources/subscribe", "subscribe_resource"):
            handle_subscribe_resource(req_id, params)
        elif method in ("resources/unsubscribe", "unsubscribe_resource"):
            handle_unsubscribe_resource(req_id, params)
        elif method in ("prompts/list", "list_prompts"):
            handle_list_prompts(req_id)
        elif method in ("prompts/get", "get_prompt"):
            handle_get_prompt(req_id, params)
        elif method == "ping":
            handle_ping(req_id)
        elif method == "logging/setLevel":
            handle_set_logging_level(req_id)
        elif method in ("roots/list", "list_roots"):
            handle_list_roots(req_id)
        elif method in ("shutdown", "exit"):
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
    log_debug("stdin closed; shutting down")


if __name__ == "__main__":
    main()
