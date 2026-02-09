"""
CLI client for the Lean LSP bridge daemon.

Usage:
    python lsp/client.py open <file>
    python lsp/client.py update <file>
    python lsp/client.py diagnostics <file> [--timeout=120]
    python lsp/client.py hover <file> <line> <col>
    python lsp/client.py goal <file> <line> <col>
    python lsp/client.py completion <file> <line> <col>
    python lsp/client.py shutdown
    python lsp/client.py status

Lines and columns are 1-indexed on the CLI (human-friendly),
converted to 0-indexed for LSP internally.
"""

import argparse
import json
import pathlib
import socket
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import protocol


def connect_to_daemon() -> socket.socket | None:
    """Connect to the running daemon. Returns socket or None."""
    state = protocol.read_state()
    if state is None:
        return None

    port = state["port"]
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        sock.connect(("127.0.0.1", port))
        sock.settimeout(300)
        return sock
    except (ConnectionRefusedError, OSError):
        return None


def send_command(cmd: dict) -> dict:
    """Send a command to the daemon and return the response."""
    sock = connect_to_daemon()
    if sock is None:
        return {"ok": False, "error": "Daemon not running. Start it with: python lsp/session.py start"}

    try:
        protocol.send_json(sock, cmd)
        result = protocol.recv_json(sock)
        if result is None:
            return {"ok": False, "error": "Daemon closed connection unexpectedly"}
        return result
    finally:
        sock.close()


def main():
    parser = argparse.ArgumentParser(description="Lean LSP bridge client")
    sub = parser.add_subparsers(dest="command", required=True)

    # open
    p_open = sub.add_parser("open", help="Open a file in the LSP")
    p_open.add_argument("file", help="Path to .lean file")

    # update
    p_update = sub.add_parser("update", help="Re-send file contents (after edit)")
    p_update.add_argument("file", help="Path to .lean file")

    # diagnostics
    p_diag = sub.add_parser("diagnostics", help="Get diagnostics for a file")
    p_diag.add_argument("file", help="Path to .lean file")
    p_diag.add_argument("--timeout", type=float, default=120, help="Timeout in seconds (default 120)")

    # hover
    p_hover = sub.add_parser("hover", help="Get hover info at position")
    p_hover.add_argument("file", help="Path to .lean file")
    p_hover.add_argument("line", type=int, help="Line number (1-indexed)")
    p_hover.add_argument("col", type=int, help="Column number (1-indexed)")

    # goal
    p_goal = sub.add_parser("goal", help="Get tactic goal state")
    p_goal.add_argument("file", help="Path to .lean file")
    p_goal.add_argument("line", type=int, help="Line number (1-indexed)")
    p_goal.add_argument("col", type=int, help="Column number (1-indexed)")

    # completion
    p_comp = sub.add_parser("completion", help="Get completions at position")
    p_comp.add_argument("file", help="Path to .lean file")
    p_comp.add_argument("line", type=int, help="Line number (1-indexed)")
    p_comp.add_argument("col", type=int, help="Column number (1-indexed)")

    # shutdown
    sub.add_parser("shutdown", help="Shut down the daemon")

    # status
    sub.add_parser("status", help="Check daemon status")

    args = parser.parse_args()

    # Build command dict
    cmd = {"command": args.command}

    if args.command in ("open", "update", "diagnostics", "hover", "goal", "completion"):
        cmd["file"] = args.file

    if args.command == "diagnostics":
        cmd["timeout"] = args.timeout

    if args.command in ("hover", "goal", "completion"):
        # Convert 1-indexed CLI to 0-indexed LSP
        cmd["line"] = args.line - 1
        cmd["col"] = args.col - 1

    result = send_command(cmd)
    print(json.dumps(result, indent=2))

    # Exit with non-zero if not ok
    if not result.get("ok", False):
        sys.exit(1)


if __name__ == "__main__":
    main()
