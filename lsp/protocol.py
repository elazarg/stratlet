"""
LSP framing helpers and URI/path conversion for the Lean LSP bridge.

LSP uses Content-Length framing between daemon↔lean:
    Content-Length: N\r\n\r\n{json-bytes}

Internal protocol between client↔daemon uses newline-delimited JSON over TCP.
"""

import json
import logging
import os
import pathlib
import subprocess
import sys
import urllib.parse
import urllib.request

PROJECT_ROOT = pathlib.Path(__file__).resolve().parent.parent
STATE_FILE = pathlib.Path(".lsp-state.json").resolve()


# ---------------------------------------------------------------------------
# LSP Content-Length framing (daemon ↔ lean)
# ---------------------------------------------------------------------------

def lsp_encode(obj: dict) -> bytes:
    """Encode a dict as an LSP Content-Length framed message."""
    body = json.dumps(obj).encode("utf-8")
    header = f"Content-Length: {len(body)}\r\n\r\n".encode("ascii")
    return header + body


def lsp_read_message(stream) -> dict | None:
    """Read one LSP message from a binary stream. Returns None on EOF."""
    # Read headers until blank line
    content_length = None
    while True:
        line = stream.readline()
        if not line:
            return None  # EOF
        line = line.decode("ascii").strip()
        if not line:
            break  # End of headers
        if line.lower().startswith("content-length:"):
            content_length = int(line.split(":", 1)[1].strip())

    if content_length is None:
        return None

    body = b""
    while len(body) < content_length:
        chunk = stream.read(content_length - len(body))
        if not chunk:
            return None  # EOF mid-message
        body += chunk

    return json.loads(body.decode("utf-8"))


# ---------------------------------------------------------------------------
# URI ↔ path conversion
# ---------------------------------------------------------------------------

def path_to_uri(path: str | pathlib.Path) -> str:
    """Convert a filesystem path to a file:// URI."""
    p = pathlib.Path(path).resolve()
    # On Windows: file:///D:/workspace/...
    return pathlib.Path(p).as_uri()


def uri_to_path(uri: str) -> pathlib.Path:
    """Convert a file:// URI to a filesystem path."""
    parsed = urllib.parse.urlparse(uri)
    # url2pathname handles Windows drive letters correctly
    return pathlib.Path(urllib.request.url2pathname(parsed.path))


def resolve_file(file_arg: str) -> pathlib.Path:
    """Resolve a file argument (possibly relative) to an absolute path."""
    p = pathlib.Path(file_arg)
    if not p.is_absolute():
        p = PROJECT_ROOT / p
    return p.resolve()


# ---------------------------------------------------------------------------
# Internal protocol (client ↔ daemon over TCP)
# ---------------------------------------------------------------------------

def send_json(sock, obj: dict):
    """Send a newline-delimited JSON message over a socket."""
    data = json.dumps(obj).encode("utf-8") + b"\n"
    sock.sendall(data)


def recv_json(sock) -> dict | None:
    """Receive a newline-delimited JSON message from a socket.
    Returns None on connection close."""
    buf = b""
    while True:
        chunk = sock.recv(4096)
        if not chunk:
            return None
        buf += chunk
        if b"\n" in buf:
            line, _ = buf.split(b"\n", 1)
            return json.loads(line.decode("utf-8"))


def read_state() -> dict | None:
    """Read the daemon state file. Returns None if not found or invalid."""
    try:
        return json.loads(STATE_FILE.read_text())
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return None


def write_state(port: int, pid: int, lean_pid: int | None = None):
    """Write daemon state (port, pid, lean_pid) to the state file."""
    STATE_FILE.parent.mkdir(parents=True, exist_ok=True)
    data = {"port": port, "pid": pid}
    if lean_pid is not None:
        data["lean_pid"] = lean_pid
    STATE_FILE.write_text(json.dumps(data))


def remove_state():
    """Remove the daemon state file."""
    try:
        STATE_FILE.unlink()
    except FileNotFoundError:
        pass


# ---------------------------------------------------------------------------
# Process management helpers
# ---------------------------------------------------------------------------

logger = logging.getLogger("lsp-protocol")


def is_pid_alive(pid: int) -> bool:
    """Check if a process with the given PID is still running."""
    if pid <= 0:
        return False

    if sys.platform == "win32":
        try:
            # OpenProcess with PROCESS_QUERY_LIMITED_INFORMATION (0x1000)
            import ctypes
            kernel32 = ctypes.windll.kernel32
            handle = kernel32.OpenProcess(0x1000, False, pid)
            if not handle:
                return False
            try:
                exit_code = ctypes.c_ulong()
                kernel32.GetExitCodeProcess(handle, ctypes.byref(exit_code))
                # STILL_ACTIVE = 259
                return exit_code.value == 259
            finally:
                kernel32.CloseHandle(handle)
        except Exception:
            return False
    else:
        try:
            os.kill(pid, 0)
            return True
        except ProcessLookupError:
            return False
        except PermissionError:
            return True  # Process exists but we can't signal it


def kill_process_tree(pid: int) -> bool:
    """Kill a process and all its children.

    Returns True if the kill was attempted (not necessarily successful).
    """
    if pid <= 0:
        return False

    if sys.platform == "win32":
        try:
            # taskkill /F /T /PID kills the process tree
            subprocess.run(
                ["taskkill", "/F", "/T", "/PID", str(pid)],
                capture_output=True, timeout=10,
            )
            return True
        except Exception as e:
            logger.debug("kill_process_tree(%d) failed: %s", pid, e)
            return False
    else:
        try:
            os.killpg(os.getpgid(pid), 9)  # SIGKILL the process group
            return True
        except (ProcessLookupError, PermissionError):
            # Try single-process kill as fallback
            try:
                os.kill(pid, 9)
                return True
            except Exception:
                return False
        except Exception as e:
            logger.debug("kill_process_tree(%d) failed: %s", pid, e)
            return False
