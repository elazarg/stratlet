#!/usr/bin/env python3
"""Check the active paper's claim-to-Lean registry, not mathematical English.

Numbered theorem/lemma/corollary/proposition environments require labels and
registry entries. Unnumbered results are tagged with '% lean-claim: ID'. Every
entry must name an axiom-pinned theorem in the paper audit modules. Only files
reachable through the active main.tex inputs are checked, not archived drafts.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


AUDIT_FILES = ("Paper/General.lean", "Paper/Source.lean", "Paper.lean")
SNAPSHOT_FILE = "paper-snapshot.json"
THEOREM = re.compile(
    r"\\begin\{(theorem|lemma|corollary|proposition)\}(.*?)\\end\{\1\}", re.S
)
LABEL = re.compile(r"\\label\{([^}]+)\}")
TAG = re.compile(r"^\s*%\s*lean-claim:\s*(\S+)\s*$", re.M)
INPUT = re.compile(r"\\(?:input|include)\{([^}]+)\}")


def strip_lean_comments(text: str) -> str:
    """Keep line boundaries and strings while removing nested Lean comments."""
    result = []
    depth = 0
    quoted = False
    pos = 0
    while pos < len(text):
        pair = text[pos:pos + 2]
        char = text[pos]
        if depth:
            if pair == "/-":
                depth += 1
                pos += 2
            elif pair == "-/":
                depth -= 1
                pos += 2
            else:
                result.append("\n" if char == "\n" else " ")
                pos += 1
        elif quoted:
            result.append(char)
            pos += 1
            if char == "\\" and pos < len(text):
                result.append(text[pos])
                pos += 1
            elif char == '"':
                quoted = False
        elif pair == "/-":
            depth = 1
            result.append(" ")
            pos += 2
        elif pair == "--":
            end = text.find("\n", pos)
            pos = len(text) if end < 0 else end
        else:
            result.append(char)
            quoted = char == '"'
            pos += 1
    return "".join(result)


def audit_names(text: str) -> tuple[set[str], set[str]]:
    clean = strip_lean_comments(text)
    scopes = []
    names = set()
    for line in clean.splitlines():
        if match := re.match(r"^namespace\s+(\S+)", line):
            scopes.append(match[1])
        elif re.match(r"^(?:noncomputable\s+)?section\b", line):
            scopes.append("")
        elif re.match(r"^end(?:\s|$)", line):
            if scopes:
                scopes.pop()
        elif match := re.match(r"^theorem\s+(\S+)", line):
            names.add(".".join([scope for scope in scopes if scope] + [match[1]]))
    pins = set(re.findall(
        r"#guard_msgs\s+\(whitespace\s*:=\s*lax\)\s+in\s+#print axioms\s+(\S+)", clean
    ))
    return names, pins


def active_sources(paper: Path) -> dict[Path, str]:
    paper = paper.resolve()
    result = {}

    def visit(path: Path) -> None:
        path = path.resolve()
        if not path.is_relative_to(paper):
            raise ValueError(f"Paper input escapes checkout: {path}")
        if path in result:
            return
        text = path.read_text(encoding="utf-8")
        result[path] = text
        uncommented = re.sub(r"(?<!\\)%[^\n]*", "", text)
        for name in INPUT.findall(uncommented):
            child = paper / name
            visit(child if child.suffix else child.with_suffix(".tex"))

    visit(paper / "main.tex")
    return result


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob_sha256(paper: Path, revision: str, name: str) -> str:
    blob = subprocess.run(
        ["git", "-C", str(paper), "show", f"{revision}:{name}"],
        check=True, capture_output=True,
    ).stdout
    return hashlib.sha256(blob).hexdigest()


def git_checkout_revision(paper: Path) -> str | None:
    """Return HEAD for a clean standalone checkout, or None for a plain export."""
    try:
        top = subprocess.run(
            ["git", "-C", str(paper), "rev-parse", "--show-toplevel"],
            check=True, capture_output=True, text=True,
        )
    except (OSError, subprocess.CalledProcessError):
        return None
    if not Path(top.stdout.strip()).samefile(paper):
        return None
    status = subprocess.run(
        ["git", "-C", str(paper), "status", "--porcelain", "--untracked-files=no"],
        check=True, capture_output=True, text=True,
    )
    if status.stdout.strip():
        raise ValueError("Paper checkout has tracked modifications; validate a clean revision")
    return subprocess.run(
        ["git", "-C", str(paper), "rev-parse", "HEAD"],
        check=True, capture_output=True, text=True,
    ).stdout.strip()


def make_snapshot(paper: Path) -> dict[str, object]:
    """Describe every tracked byte in a clean standalone manuscript checkout."""
    revision = git_checkout_revision(paper)
    if revision is None:
        raise ValueError("Snapshot refresh requires a standalone Git checkout")
    output = subprocess.run(
        ["git", "-C", str(paper), "ls-files", "-z"],
        check=True, capture_output=True,
    ).stdout
    names = [name.decode("utf-8") for name in output.split(b"\0") if name]
    return {
        "revision": revision,
        "files": {
            name: git_blob_sha256(paper, revision, name) for name in sorted(names)
        },
    }


def validate_snapshot(root: Path, paper: Path) -> tuple[dict[str, str], list[str]]:
    snapshot = json.loads((root / SNAPSHOT_FILE).read_text(encoding="utf-8"))
    revision = snapshot.get("revision")
    files = snapshot.get("files")
    if not isinstance(revision, str) or not revision or not isinstance(files, dict):
        return {}, [f"Malformed {SNAPSHOT_FILE}"]
    failures = []
    checkout_revision = git_checkout_revision(paper)
    if checkout_revision is not None and checkout_revision != revision:
        failures.append(
            f"Paper revision mismatch: expected {revision}, got {checkout_revision}"
        )
    valid_files: dict[str, str] = {}
    for name, expected in files.items():
        relative = Path(name)
        if (not isinstance(name, str) or not isinstance(expected, str)
                or relative.is_absolute() or ".." in relative.parts):
            failures.append(f"Invalid paper snapshot entry: {name!r}")
            continue
        valid_files[relative.as_posix()] = expected
        path = paper / relative
        if not path.is_file():
            failures.append(f"Paper snapshot file missing: {name}")
        elif ((git_blob_sha256(paper, checkout_revision, name)
               if checkout_revision is not None else sha256(path)) != expected):
            failures.append(f"Paper snapshot digest mismatch: {name}")
    return valid_files, failures


def check(root: Path, paper: Path, allow_missing: bool = False) -> list[str]:
    registry = json.loads((root / "paper-claims.json").read_text(encoding="utf-8"))
    names, pins = set(), set()
    for filename in AUDIT_FILES:
        declared, pinned = audit_names((root / filename).read_text(encoding="utf-8"))
        names.update(declared)
        pins.update(pinned)
    failures = []
    for claim, references in registry.items():
        if not references or not isinstance(references, list):
            failures.append(f"{claim}: expected a nonempty list of Lean theorems")
            continue
        for name in references:
            if name not in names:
                failures.append(f"{claim}: no audit theorem {name}")
            elif name not in pins:
                failures.append(f"{claim}: no guarded axiom pin for {name}")
    for name in sorted(names - pins):
        failures.append(f"Audit theorem has no guarded axiom pin: {name}")
    if not (paper / "main.tex").is_file():
        if allow_missing:
            print("Paper checkout absent: checking Lean registry only, not prose coverage.")
        else:
            failures.append(f"Missing active paper: {paper / 'main.tex'}")
        return failures
    try:
        snapshot_files, snapshot_failures = validate_snapshot(root, paper)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        failures.append(str(error))
        return failures
    failures.extend(snapshot_failures)
    claims = []
    sources = active_sources(paper)
    for path, text in sources.items():
        relative = path.relative_to(paper.resolve()).as_posix()
        if relative not in snapshot_files:
            failures.append(f"Active paper input is absent from snapshot manifest: {relative}")
        claims.extend(TAG.findall(text))
        uncommented = re.sub(r"(?<!\\)%[^\n]*", "", text)
        for databases in re.findall(r"\\bibliography\{([^}]+)\}", uncommented):
            for database in databases.split(","):
                name = database.strip()
                name = name if name.endswith(".bib") else name + ".bib"
                if name not in snapshot_files:
                    failures.append(f"Active bibliography absent from snapshot manifest: {name}")
                # Recursive bibliography search must not select an archived
                # database with the same unqualified filename.
                if "/" not in name:
                    matches = sorted(file for file in snapshot_files if Path(file).name == name)
                    if len(matches) > 1:
                        failures.append(
                            f"Ambiguous bibliography filename {name}: {', '.join(matches)}"
                        )
        for match in THEOREM.finditer(uncommented):
            labels = LABEL.findall(match[2])
            if len(labels) != 1:
                failures.append(f"{path.name}: {match[1]} needs exactly one claim label")
            else:
                claims.append(labels[0])
    counts = Counter(claims)
    for claim, count in counts.items():
        if count != 1:
            failures.append(f"Duplicate paper claim: {claim}")
        if claim not in registry:
            failures.append(f"Paper claim has no Lean mapping: {claim}")
    for claim in registry.keys() - counts.keys():
        failures.append(f"Stale registry entry absent from active paper: {claim}")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper-dir", type=Path)
    parser.add_argument("--allow-missing-paper", action="store_true",
                        help="CI without the separate Overleaf checkout checks only the Lean registry")
    parser.add_argument("--refresh-snapshot", action="store_true",
                        help=f"replace {SNAPSHOT_FILE} from a clean manuscript Git checkout")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    paper = args.paper_dir or root / "overleaf"
    if args.refresh_snapshot:
        try:
            snapshot = make_snapshot(paper.resolve())
            (root / SNAPSHOT_FILE).write_text(
                json.dumps(snapshot, indent=2, sort_keys=True) + "\n",
                encoding="utf-8", newline="\n"
            )
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            print(error)
            return 1
        print(f"Refreshed {SNAPSHOT_FILE} at {snapshot['revision']}.")
        return 0
    try:
        failures = check(root, paper, args.allow_missing_paper)
    except (OSError, ValueError) as error:
        failures = [str(error)]
    if failures:
        print("\n".join(failures))
        return 1
    print("Paper claim registry checks passed. Prose/Lean semantic agreement requires review.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
