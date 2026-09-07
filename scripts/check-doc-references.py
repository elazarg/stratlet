#!/usr/bin/env python3
"""Fail if a Lean docstring cites a name that does not exist.

Docstrings in this development carry a lot of load: they say which theorem does
the real work, which hypothesis a result depends on, and which witness refutes a
converse. A citation that silently stops resolving -- because the target was
renamed, or was never written -- turns that guidance into misdirection, and
nothing in the build notices. This checks the ones shaped like our own names.

A token is checked when its final component is lower-case and it either contains
an underscore or is qualified. Those are the shapes of theorem and definition names
here. Type names, tactics, and prose survive that filter untouched; `ALLOWED`
carries the few lower-case underscored names that are legitimately not
declarations.
"""

from __future__ import annotations

import io
import os
import re
import sys

ROOTS_DEFINING = ("Vegas", "VegasEVM", "Paper", "GameTheory/GameTheory")
ROOTS_CITING = ("Vegas", "VegasEVM", "Paper")

# Lean tactics and attributes that look like our identifiers but are not
# declarations we can index.
ALLOWED = {
    "native_decide",
    "decide_eq_true",
    "simp_all",
    "norm_num",
    "push_neg",
    "omega_nat",
}

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'!?]*)"
)
# A structure or class field: indented, an identifier, then a colon.
FIELD = re.compile(r"^\s+([a-z][A-Za-z0-9_']*)\s*:[^=]")
CITED = re.compile(r"`([A-Za-z_][A-Za-z0-9_.']*)`")
CONSTRUCTOR = re.compile(
    r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)(?:\s*(?::|\(|\{)|\s*$)"
)


def lean_files(roots):
    for root in roots:
        for dirpath, _dirnames, filenames in os.walk(root):
            for filename in sorted(filenames):
                if filename.endswith(".lean"):
                    yield os.path.join(dirpath, filename)


def index_declarations():
    """Every name a docstring may legitimately cite."""
    names = set()
    for path in lean_files(ROOTS_DEFINING):
        for line in io.open(path, encoding="utf-8"):
            match = DECL.match(line)
            if match:
                name = match.group(1)
                names.add(name)
                names.add(name.split(".")[-1])
                continue
            match = FIELD.match(line)
            if match:
                names.add(match.group(1))
            match = CONSTRUCTOR.match(line)
            if match:
                names.add(match.group(1))
    return names


def dangling(names):
    findings = []
    for path in lean_files(ROOTS_CITING):
        for number, line in enumerate(io.open(path, encoding="utf-8"), 1):
            for cited in CITED.findall(line):
                if cited.endswith(".lean"):
                    continue
                last = cited.split(".")[-1]
                if last in names or cited in names or last in ALLOWED:
                    continue
                if last.islower() and ("_" in last or "." in cited):
                    findings.append((path.replace(os.sep, "/"), number, cited))
    return findings


def main():
    names = index_declarations()
    findings = dangling(names)
    for path, number, cited in findings:
        print("%s:%d: docstring cites unknown name `%s`" % (path, number, cited))
    if findings:
        print("\n%d dangling documentation reference(s); %d names indexed."
              % (len(findings), len(names)))
        return 1
    print("No dangling documentation references (%d names indexed)." % len(names))
    return 0


if __name__ == "__main__":
    sys.exit(main())
