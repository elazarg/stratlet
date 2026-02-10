"""
Lean LSP bridge session manager.

Manages the daemon lifecycle: start, stop, status.

Usage:
    python lsp/session.py start [--timeout=1800]
    python lsp/session.py status
    python lsp/session.py stop
"""

import argparse
import json
import os
import pathlib
import socket
import subprocess
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import protocol


def is_daemon_alive() -> bool:
    """Check if the daemon is reachable via TCP."""
    state = protocol.read_state()
    if state is None:
        return False

    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        sock.settimeout(2)
        sock.connect(("127.0.0.1", state["port"]))
        # Send a status command to verify it's our daemon
        protocol.send_json(sock, {"command": "status"})
        resp = protocol.recv_json(sock)
        return resp is not None and resp.get("ok", False)
    except (ConnectionRefusedError, OSError, socket.timeout):
        return False
    finally:
        sock.close()


def _cleanup_stale_pids():
    """Kill any stale daemon/lean PIDs from a previous crashed session."""
    state = protocol.read_state()
    if state is None:
        return

    killed = []
    for key in ("pid", "lean_pid"):
        pid = state.get(key)
        if pid and protocol.is_pid_alive(pid):
            protocol.kill_process_tree(pid)
            killed.append(f"{key}={pid}")

    if killed:
        print(json.dumps({"info": f"Cleaned up stale processes: {', '.join(killed)}"}),
              file=sys.stderr)

    protocol.remove_state()


def cmd_start(idle_timeout: int = 1800):
    """Start the daemon if not already running."""
    # Check if already running
    if is_daemon_alive():
        state = protocol.read_state()
        print(json.dumps({"ok": True, "message": "Daemon already running",
                          "port": state["port"], "pid": state["pid"]}))
        return

    # Layer 3: Kill stale PIDs from previous crashed session
    _cleanup_stale_pids()

    # Launch daemon as detached process
    daemon_script = pathlib.Path(__file__).resolve().parent / "daemon.py"
    cmd = [sys.executable, str(daemon_script), "--timeout", str(idle_timeout)]

    if sys.platform == "win32":
        # Fully detach on Windows
        CREATE_NEW_PROCESS_GROUP = 0x00000200
        DETACHED_PROCESS = 0x00000008
        CREATE_NO_WINDOW = 0x08000000
        flags = CREATE_NEW_PROCESS_GROUP | DETACHED_PROCESS | CREATE_NO_WINDOW
        proc = subprocess.Popen(
            cmd,
            creationflags=flags,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            close_fds=True,
        )
    else:
        proc = subprocess.Popen(
            cmd,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            start_new_session=True,
        )

    # Wait for state file to appear (daemon writes it when ready)
    deadline = time.time() + 120  # 120s for lake serve to start (mathlib imports are slow)
    while time.time() < deadline:
        time.sleep(0.5)
        state = protocol.read_state()
        if state is not None:
            # Verify it's alive
            if is_daemon_alive():
                print(json.dumps({"ok": True, "message": "Daemon started",
                                  "port": state["port"], "pid": state["pid"]}))
                return

    print(json.dumps({"ok": False, "error": "Daemon failed to start within 120s. Check lsp/daemon.log"}))
    sys.exit(1)


def cmd_status():
    """Check daemon status."""
    if is_daemon_alive():
        state = protocol.read_state()
        # Get detailed status from daemon
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        try:
            sock.settimeout(5)
            sock.connect(("127.0.0.1", state["port"]))
            protocol.send_json(sock, {"command": "status"})
            resp = protocol.recv_json(sock)
            resp["port"] = state["port"]
            resp["pid"] = state["pid"]
            print(json.dumps(resp, indent=2))
        except Exception as e:
            print(json.dumps({"ok": True, "message": "Daemon reachable",
                              "port": state["port"], "pid": state["pid"]}))
        finally:
            sock.close()
    else:
        protocol.remove_state()  # Clean up stale state
        print(json.dumps({"ok": False, "message": "Daemon not running"}))
        sys.exit(1)


def cmd_stop():
    """Stop the daemon gracefully, with force-kill fallback."""
    state = protocol.read_state()
    if state is None:
        print(json.dumps({"ok": True, "message": "Daemon not running (no state file)"}))
        return

    # Try graceful TCP shutdown first
    graceful_ok = False
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        sock.settimeout(5)
        sock.connect(("127.0.0.1", state["port"]))
        protocol.send_json(sock, {"command": "shutdown"})
        resp = protocol.recv_json(sock)
        print(json.dumps(resp))
        graceful_ok = True
    except (ConnectionRefusedError, OSError):
        print(json.dumps({"ok": True, "message": "Daemon not reachable, will force kill"}),
              file=sys.stderr)
    finally:
        sock.close()

    if graceful_ok:
        # Wait for state file to disappear
        for _ in range(20):
            time.sleep(0.5)
            if not protocol.STATE_FILE.exists():
                break

    # Force-kill fallback: if processes are still alive, kill them
    for key in ("pid", "lean_pid"):
        pid = state.get(key)
        if pid and protocol.is_pid_alive(pid):
            protocol.kill_process_tree(pid)
            print(json.dumps({"info": f"Force-killed {key}={pid}"}), file=sys.stderr)

    protocol.remove_state()  # Ensure cleanup


def main():
    parser = argparse.ArgumentParser(description="Lean LSP bridge session manager")
    sub = parser.add_subparsers(dest="command", required=True)

    p_start = sub.add_parser("start", help="Start the daemon")
    p_start.add_argument("--timeout", type=int, default=1800, help="Idle timeout in seconds (default 1800)")

    sub.add_parser("status", help="Check daemon status")
    sub.add_parser("stop", help="Stop the daemon")

    args = parser.parse_args()

    if args.command == "start":
        cmd_start(idle_timeout=args.timeout)
    elif args.command == "status":
        cmd_status()
    elif args.command == "stop":
        cmd_stop()


if __name__ == "__main__":
    main()
