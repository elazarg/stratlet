"""
Lean LSP bridge daemon.

Spawns `lake serve`, manages the LSP lifecycle, and serves client requests
over TCP on localhost. Clients connect, send newline-delimited JSON commands,
receive a JSON response, and disconnect.

Usage (normally launched by session.py):
    python lsp/daemon.py [--port PORT] [--timeout SECONDS] [--log LOG_FILE]
"""

import argparse
import json
import logging
import os
import pathlib
import socket
import subprocess
import sys
import threading
import time

# Add parent so we can import protocol as sibling
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import protocol

logger = logging.getLogger("lsp-daemon")


class LeanLSPDaemon:
    """Manages a Lean LSP server process and multiplexes client requests."""

    def __init__(self, project_root: pathlib.Path, idle_timeout: float = 1800):
        self.project_root = project_root
        self.idle_timeout = idle_timeout

        # LSP state
        self.next_id = 1
        self.id_lock = threading.Lock()
        self.lsp_write_lock = threading.Lock()
        self.pending: dict[int, threading.Event] = {}
        self.responses: dict[int, dict] = {}

        # Document tracking
        self.doc_versions: dict[str, int] = {}      # uri → version
        self.doc_diagnostics: dict[str, list] = {}   # uri → diagnostics list
        self.doc_ready: dict[str, threading.Event] = {}  # uri → elaboration done

        # Process state
        self.lean_proc: subprocess.Popen | None = None
        self.lean_dead = False
        self.lean_dead_reason = ""
        self.shutdown_flag = threading.Event()

    # ------------------------------------------------------------------
    # LSP process management
    # ------------------------------------------------------------------

    def start_lean(self):
        """Spawn lake serve and perform the LSP handshake."""
        logger.info("Starting lake serve in %s", self.project_root)
        self.lean_proc = subprocess.Popen(
            ["lake", "serve"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            cwd=str(self.project_root),
            # On Windows, avoid inheriting console
            creationflags=subprocess.CREATE_NO_WINDOW if sys.platform == "win32" else 0,
        )

        # Start reader thread
        reader = threading.Thread(target=self._reader_loop, daemon=True)
        reader.start()

        # Start stderr drainer
        stderr_drainer = threading.Thread(target=self._drain_stderr, daemon=True)
        stderr_drainer.start()

        # Initialize handshake
        resp = self._send_request("initialize", {
            "processId": os.getpid(),
            "rootUri": protocol.path_to_uri(self.project_root),
            "capabilities": {
                "textDocument": {
                    "hover": {"contentFormat": ["markdown", "plaintext"]},
                    "completion": {"completionItem": {"snippetSupport": False}},
                }
            },
        }, timeout=300)  # lake serve can take minutes to load mathlib

        if resp is None:
            raise RuntimeError("LSP initialize failed — no response")
        if "error" in resp:
            raise RuntimeError(f"LSP initialize error: {resp['error']}")

        logger.info("LSP initialized, server capabilities received")
        self._send_notification("initialized", {})

    def shutdown_lean(self):
        """Graceful LSP shutdown."""
        if self.lean_dead or self.lean_proc is None:
            return
        logger.info("Sending LSP shutdown + exit")
        try:
            self._send_request("shutdown", None, timeout=10)
        except Exception:
            pass
        try:
            self._send_notification("exit", None)
        except Exception:
            pass
        try:
            self.lean_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            self.lean_proc.kill()

    # ------------------------------------------------------------------
    # LSP read loop (runs in background thread)
    # ------------------------------------------------------------------

    def _reader_loop(self):
        """Read LSP messages from lean's stdout and dispatch them."""
        try:
            while not self.shutdown_flag.is_set():
                msg = protocol.lsp_read_message(self.lean_proc.stdout)
                if msg is None:
                    logger.warning("Lean stdout EOF")
                    self.lean_dead = True
                    self.lean_dead_reason = "Lean process exited unexpectedly"
                    self._unblock_all_pending()
                    return
                self._dispatch_message(msg)
        except Exception as e:
            logger.exception("Reader loop error: %s", e)
            self.lean_dead = True
            self.lean_dead_reason = str(e)
            self._unblock_all_pending()

    def _drain_stderr(self):
        """Drain lean's stderr to prevent pipe deadlock."""
        try:
            for line in self.lean_proc.stderr:
                logger.debug("lean stderr: %s", line.decode("utf-8", errors="replace").rstrip())
        except Exception:
            pass

    def _dispatch_message(self, msg: dict):
        """Route an incoming LSP message to the right handler."""
        if "id" in msg and "method" not in msg:
            # Response to a request we sent
            req_id = msg["id"]
            self.responses[req_id] = msg
            evt = self.pending.get(req_id)
            if evt:
                evt.set()
        elif msg.get("method") == "textDocument/publishDiagnostics":
            params = msg.get("params", {})
            uri = params.get("uri", "")
            self.doc_diagnostics[uri] = params.get("diagnostics", [])
            logger.debug("Diagnostics for %s: %d items", uri, len(self.doc_diagnostics[uri]))
        elif msg.get("method") == "$/lean/fileProgress":
            params = msg.get("params", {})
            uri = params.get("textDocument", {}).get("uri", "")
            processing = params.get("processing", [])
            if not processing:
                # Elaboration complete for this file
                logger.info("Elaboration complete for %s", uri)
                evt = self.doc_ready.get(uri)
                if evt:
                    evt.set()
        else:
            method = msg.get("method", "unknown")
            logger.debug("Unhandled LSP message: %s", method)

    def _unblock_all_pending(self):
        """Unblock all pending requests (on Lean crash)."""
        for evt in self.pending.values():
            evt.set()

    # ------------------------------------------------------------------
    # LSP writing helpers
    # ------------------------------------------------------------------

    def _alloc_id(self) -> int:
        with self.id_lock:
            rid = self.next_id
            self.next_id += 1
            return rid

    def _send_request(self, method: str, params, timeout: float = 60) -> dict | None:
        """Send an LSP request and wait for its response."""
        if self.lean_dead:
            return {"error": {"code": -1, "message": self.lean_dead_reason}}

        rid = self._alloc_id()
        evt = threading.Event()
        self.pending[rid] = evt

        msg = {"jsonrpc": "2.0", "id": rid, "method": method}
        if params is not None:
            msg["params"] = params

        with self.lsp_write_lock:
            data = protocol.lsp_encode(msg)
            try:
                self.lean_proc.stdin.write(data)
                self.lean_proc.stdin.flush()
            except (BrokenPipeError, OSError) as e:
                self.lean_dead = True
                self.lean_dead_reason = f"Write to Lean failed: {e}"
                return {"error": {"code": -1, "message": self.lean_dead_reason}}

        if not evt.wait(timeout=timeout):
            logger.warning("Request %s (id=%d) timed out after %ds", method, rid, timeout)
            return None

        resp = self.responses.pop(rid, None)
        self.pending.pop(rid, None)
        return resp

    def _send_notification(self, method: str, params):
        """Send an LSP notification (no response expected)."""
        if self.lean_dead:
            return

        msg = {"jsonrpc": "2.0", "method": method}
        if params is not None:
            msg["params"] = params

        with self.lsp_write_lock:
            try:
                self.lean_proc.stdin.write(protocol.lsp_encode(msg))
                self.lean_proc.stdin.flush()
            except (BrokenPipeError, OSError) as e:
                self.lean_dead = True
                self.lean_dead_reason = f"Write to Lean failed: {e}"

    # ------------------------------------------------------------------
    # Document operations
    # ------------------------------------------------------------------

    def _ensure_open(self, file_path: pathlib.Path) -> str:
        """Open a file in the LSP if not already open. Returns the URI."""
        uri = protocol.path_to_uri(file_path)
        if uri in self.doc_versions:
            return uri
        return self._do_open(file_path, uri)

    def _do_open(self, file_path: pathlib.Path, uri: str | None = None) -> str:
        """Open (or re-open) a file in the LSP. Returns the URI."""
        if uri is None:
            uri = protocol.path_to_uri(file_path)

        # Close first if already open
        if uri in self.doc_versions:
            self._send_notification("textDocument/didClose", {
                "textDocument": {"uri": uri}
            })

        text = file_path.read_text(encoding="utf-8")
        version = 1
        self.doc_versions[uri] = version
        self.doc_diagnostics[uri] = []
        self.doc_ready[uri] = threading.Event()

        self._send_notification("textDocument/didOpen", {
            "textDocument": {
                "uri": uri,
                "languageId": "lean4",
                "version": version,
                "text": text,
            }
        })
        logger.info("Opened %s (version %d)", file_path.name, version)
        return uri

    def _do_update(self, file_path: pathlib.Path) -> str:
        """Re-send file contents via didChange. Returns the URI."""
        uri = protocol.path_to_uri(file_path)

        if uri not in self.doc_versions:
            return self._do_open(file_path, uri)

        text = file_path.read_text(encoding="utf-8")
        version = self.doc_versions[uri] + 1
        self.doc_versions[uri] = version
        self.doc_ready[uri] = threading.Event()
        self.doc_diagnostics[uri] = []

        self._send_notification("textDocument/didChange", {
            "textDocument": {"uri": uri, "version": version},
            "contentChanges": [{"text": text}],
        })
        logger.info("Updated %s (version %d)", file_path.name, version)
        return uri

    def _wait_diagnostics(self, uri: str, timeout: float = 120) -> dict:
        """Wait for elaboration to complete and return diagnostics."""
        evt = self.doc_ready.get(uri)
        if evt is None:
            return {"ok": False, "error": f"File not open: {uri}"}

        timed_out = False
        if not evt.is_set():
            if not evt.wait(timeout=timeout):
                timed_out = True

        # Small delay to catch trailing diagnostics
        time.sleep(0.3)

        diags = self.doc_diagnostics.get(uri, [])
        errors = [d for d in diags if d.get("severity") == 1]
        warnings = [d for d in diags if d.get("severity") == 2]

        result = {
            "ok": True,
            "diagnostics": diags,
            "errors": len(errors),
            "warnings": len(warnings),
            "summary": f"{len(errors)} errors, {len(warnings)} warnings",
        }
        if timed_out:
            result["warning"] = f"Timed out after {timeout}s — diagnostics may be partial"
        return result

    # ------------------------------------------------------------------
    # Client command handlers
    # ------------------------------------------------------------------

    def handle_command(self, cmd: dict) -> dict:
        """Process a command from a client and return a response dict."""
        action = cmd.get("command", "")

        if self.lean_dead and action != "shutdown":
            return {"ok": False, "error": f"Lean is dead: {self.lean_dead_reason}"}

        try:
            if action == "open":
                return self._cmd_open(cmd)
            elif action == "update":
                return self._cmd_update(cmd)
            elif action == "diagnostics":
                return self._cmd_diagnostics(cmd)
            elif action == "hover":
                return self._cmd_hover(cmd)
            elif action == "goal":
                return self._cmd_goal(cmd)
            elif action == "completion":
                return self._cmd_completion(cmd)
            elif action == "shutdown":
                return self._cmd_shutdown()
            elif action == "status":
                return self._cmd_status()
            else:
                return {"ok": False, "error": f"Unknown command: {action}"}
        except Exception as e:
            logger.exception("Error handling command %s", action)
            return {"ok": False, "error": str(e)}

    def _cmd_open(self, cmd: dict) -> dict:
        file_path = protocol.resolve_file(cmd["file"])
        if not file_path.exists():
            return {"ok": False, "error": f"File not found: {file_path}"}
        uri = self._do_open(file_path)
        return {"ok": True, "uri": uri}

    def _cmd_update(self, cmd: dict) -> dict:
        file_path = protocol.resolve_file(cmd["file"])
        if not file_path.exists():
            return {"ok": False, "error": f"File not found: {file_path}"}
        uri = self._do_update(file_path)
        return {"ok": True, "uri": uri}

    def _cmd_diagnostics(self, cmd: dict) -> dict:
        file_path = protocol.resolve_file(cmd["file"])
        if not file_path.exists():
            return {"ok": False, "error": f"File not found: {file_path}"}
        timeout = cmd.get("timeout", 120)
        uri = self._ensure_open(file_path)
        return self._wait_diagnostics(uri, timeout=timeout)

    def _cmd_hover(self, cmd: dict) -> dict:
        file_path = protocol.resolve_file(cmd["file"])
        if not file_path.exists():
            return {"ok": False, "error": f"File not found: {file_path}"}
        uri = self._ensure_open(file_path)
        line = cmd["line"]  # already 0-indexed by client
        col = cmd["col"]

        resp = self._send_request("textDocument/hover", {
            "textDocument": {"uri": uri},
            "position": {"line": line, "character": col},
        })

        if resp is None:
            return {"ok": False, "error": "Hover request timed out"}
        if "error" in resp:
            return {"ok": False, "error": resp["error"].get("message", str(resp["error"]))}

        result = resp.get("result")
        if result is None:
            return {"ok": True, "result": None, "info": "No hover info at this position"}

        # Extract text from MarkupContent or plain string
        contents = result.get("contents", "")
        if isinstance(contents, dict):
            text = contents.get("value", "")
        else:
            text = str(contents)

        return {"ok": True, "result": text, "range": result.get("range")}

    def _cmd_goal(self, cmd: dict) -> dict:
        file_path = protocol.resolve_file(cmd["file"])
        if not file_path.exists():
            return {"ok": False, "error": f"File not found: {file_path}"}
        uri = self._ensure_open(file_path)
        line = cmd["line"]
        col = cmd["col"]

        resp = self._send_request("$/lean/plainGoal", {
            "textDocument": {"uri": uri},
            "position": {"line": line, "character": col},
        })

        if resp is None:
            return {"ok": False, "error": "Goal request timed out"}
        if "error" in resp:
            return {"ok": False, "error": resp["error"].get("message", str(resp["error"]))}

        result = resp.get("result")
        if result is None:
            return {"ok": True, "result": None, "info": "No goal at this position"}

        return {"ok": True, "goals": result.get("goals", []), "rendered": result.get("rendered")}

    def _cmd_completion(self, cmd: dict) -> dict:
        file_path = protocol.resolve_file(cmd["file"])
        if not file_path.exists():
            return {"ok": False, "error": f"File not found: {file_path}"}
        uri = self._ensure_open(file_path)
        line = cmd["line"]
        col = cmd["col"]

        resp = self._send_request("textDocument/completion", {
            "textDocument": {"uri": uri},
            "position": {"line": line, "character": col},
        })

        if resp is None:
            return {"ok": False, "error": "Completion request timed out"}
        if "error" in resp:
            return {"ok": False, "error": resp["error"].get("message", str(resp["error"]))}

        result = resp.get("result")
        if result is None:
            return {"ok": True, "items": []}

        # result can be CompletionList or list of CompletionItem
        if isinstance(result, dict):
            items = result.get("items", [])
        else:
            items = result

        # Simplify: extract just label and detail
        simplified = []
        for item in items[:50]:  # limit to 50
            simplified.append({
                "label": item.get("label", ""),
                "detail": item.get("detail", ""),
                "kind": item.get("kind"),
            })

        return {"ok": True, "items": simplified, "total": len(items)}

    def _cmd_shutdown(self) -> dict:
        self.shutdown_flag.set()
        return {"ok": True, "message": "Daemon shutting down"}

    def _cmd_status(self) -> dict:
        return {
            "ok": True,
            "lean_alive": not self.lean_dead,
            "open_files": list(self.doc_versions.keys()),
            "next_id": self.next_id,
        }

    # ------------------------------------------------------------------
    # TCP server
    # ------------------------------------------------------------------

    def serve(self, port: int = 0) -> int:
        """Start the TCP server. Returns the actual port used."""
        server = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        server.bind(("127.0.0.1", port))
        server.listen(5)
        actual_port = server.getsockname()[1]
        logger.info("TCP server listening on 127.0.0.1:%d", actual_port)

        # Write state file
        protocol.write_state(actual_port, os.getpid())
        logger.info("State file written to %s", protocol.STATE_FILE)

        self.last_activity = time.time()

        try:
            while not self.shutdown_flag.is_set():
                # Timeout relative to last meaningful interaction
                elapsed = time.time() - self.last_activity
                remaining = self.idle_timeout - elapsed
                if remaining <= 0:
                    logger.info("Idle timeout reached (%ds), shutting down", self.idle_timeout)
                    break
                server.settimeout(remaining)
                try:
                    conn, addr = server.accept()
                    self.last_activity = time.time()
                except socket.timeout:
                    logger.info("Idle timeout reached (%ds since last activity), shutting down",
                                self.idle_timeout)
                    break
                except OSError:
                    if self.shutdown_flag.is_set():
                        break
                    raise

                # Handle client in a thread
                t = threading.Thread(target=self._handle_client, args=(conn, addr), daemon=True)
                t.start()
        finally:
            logger.info("Server shutting down")
            self.shutdown_lean()
            protocol.remove_state()
            server.close()

        return actual_port

    def _handle_client(self, conn: socket.socket, addr):
        """Handle a single client connection."""
        logger.debug("Client connected from %s", addr)
        try:
            conn.settimeout(300)  # 5 min per-client timeout
            msg = protocol.recv_json(conn)
            if msg is None:
                return

            logger.debug("Command: %s", msg.get("command", "?"))
            result = self.handle_command(msg)
            protocol.send_json(conn, result)
            self.last_activity = time.time()  # Reset idle timer after interaction
        except Exception as e:
            logger.exception("Client handler error: %s", e)
            try:
                protocol.send_json(conn, {"ok": False, "error": str(e)})
            except Exception:
                pass
        finally:
            conn.close()


# ------------------------------------------------------------------
# Main entry point
# ------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="Lean LSP bridge daemon")
    parser.add_argument("--port", type=int, default=0, help="TCP port (0 = auto)")
    parser.add_argument("--timeout", type=int, default=1800, help="Idle timeout in seconds")
    parser.add_argument("--log", type=str, default=str(pathlib.Path(__file__).resolve().parent / "daemon.log"),
                        help="Log file path")
    args = parser.parse_args()

    # Configure logging
    logging.basicConfig(
        level=logging.DEBUG,
        format="%(asctime)s [%(levelname)s] %(message)s",
        handlers=[
            logging.FileHandler(args.log, mode="w"),
            logging.StreamHandler(sys.stderr),
        ],
    )

    project_root = protocol.PROJECT_ROOT
    logger.info("Project root: %s", project_root)

    daemon = LeanLSPDaemon(project_root, idle_timeout=args.timeout)
    try:
        daemon.start_lean()
        daemon.serve(port=args.port)
    except Exception:
        logger.exception("Daemon fatal error")
        protocol.remove_state()
        sys.exit(1)


if __name__ == "__main__":
    main()
