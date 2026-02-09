# Lean LSP Bridge

CLI tools for querying the Lean 4 language server from shell scripts (designed for Claude Code but usable standalone).

## Architecture

```
client.py  ──TCP──>  daemon.py  ──stdin/stdout──>  lake serve (Lean LSP)
```

- **daemon.py** — long-running process that spawns `lake serve`, manages LSP state, serves requests over TCP on localhost.
- **client.py** — one-shot CLI. Connects to the daemon, sends a command, prints JSON result, disconnects.
- **session.py** — lifecycle manager. Starts/stops the daemon as a detached background process.
- **protocol.py** — shared helpers: LSP Content-Length framing, URI/path conversion, TCP JSON protocol, state file management.
- **ask_gpt.py** — unrelated to LSP. Sends a query file to OpenAI's API (reads key from `.env`).

## Quick start

```bash
# Start the daemon (takes ~60-120s first time — mathlib imports are slow)
python lsp/session.py start

# Check a file for errors
python lsp/client.py diagnostics Vegas/ProtoLetLemmas.lean --timeout=300

# Get tactic goal state at a position (line/col are 1-indexed)
python lsp/client.py goal Vegas/ProtoLetLemmas.lean 42 5

# Hover info
python lsp/client.py hover Vegas/ProtoLetLemmas.lean 13 8

# After editing a file on disk, tell the daemon to re-read it
python lsp/client.py update Vegas/ProtoLetLemmas.lean

# Completions
python lsp/client.py completion Vegas/ProtoLetLemmas.lean 50 10

# Stop the daemon
python lsp/session.py stop
```

## Typical edit-check cycle

```bash
# 1. Edit the file (Write tool, editor, etc.)
# 2. Tell the daemon about the change
python lsp/client.py update Vegas/ProtoLetLemmas.lean
# 3. Wait for elaboration and get errors
python lsp/client.py diagnostics Vegas/ProtoLetLemmas.lean --timeout=300
# 4. Inspect goal state at a sorry
python lsp/client.py goal Vegas/ProtoLetLemmas.lean 42 5
```

## Gotchas

- **First start is slow.** `lake serve` loads mathlib, which takes 60-120s. The daemon waits up to 300s for initialization.
- **Diagnostics can time out.** Large files take time to elaborate. Use `--timeout=300` (5min) for safety. A timeout returns whatever diagnostics are available so far.
- **After external edits, always `update`.** The daemon caches file contents. If you edit on disk (or another session does), run `update` before querying.
- **Lines and columns are 1-indexed** on the CLI. They're converted to 0-indexed internally for LSP.
- **Idle timeout.** The daemon auto-shuts down after 30 minutes of no client interaction. Just `session.py start` again.
- **State file.** The daemon writes its port/PID to a JSON state file so clients can find it. `session.py` manages this. If things get stuck, `session.py stop` cleans up.
- **Parallel sessions.** The LSP daemon is read-only w.r.t. the filesystem — it doesn't interfere with `lake build` or other tools. Multiple CLI clients can connect sequentially (not concurrently to the same daemon).

## Files not committed

- `daemon.log` — runtime log (in .gitignore)
- `__pycache__/` — Python bytecode (in .gitignore)
- `query.md` — scratch file for ChatGPT queries (not gitignored, but ephemeral)

## Dependencies

Python 3 stdlib only. No pip packages needed. Requires `lake serve` (comes with elan/Lake).
