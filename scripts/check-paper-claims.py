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
import json
from pathlib import Path
import re
import sys


AUDIT_FILES = ("Vegas/Paper.lean", "Paper.lean")
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
    claims = []
    for path, text in active_sources(paper).items():
        claims.extend(TAG.findall(text))
        uncommented = re.sub(r"(?<!\\)%[^\n]*", "", text)
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
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    try:
        failures = check(root, args.paper_dir or root / "overleaf", args.allow_missing_paper)
    except (OSError, ValueError) as error:
        failures = [str(error)]
    if failures:
        print("\n".join(failures))
        return 1
    print("Paper claim registry checks passed. Prose/Lean semantic agreement requires review.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
