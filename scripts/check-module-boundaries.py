#!/usr/bin/env python3
"""Check local Lean imports, build-root coverage, and architectural boundaries.

Only configured library source trees are inspected, not temporary directories
or separately managed dependencies. This is a structural check, not a Lean
parser or substitute for building the modules.
"""

from __future__ import annotations

from pathlib import Path
import re
import subprocess
import sys
import tomllib


def imports(text: str) -> list[str]:
    """Remove nested block comments and line comments before reading imports."""
    clean: list[str] = []
    depth = 0
    pos = 0
    while pos < len(text):
        pair = text[pos:pos + 2]
        if pair == "/-":
            depth += 1
            pos += 2
        elif depth and pair == "-/":
            depth -= 1
            pos += 2
            clean.append(" ")
        elif not depth and pair == "--":
            end = text.find("\n", pos)
            pos = len(text) if end < 0 else end
        else:
            if not depth or text[pos] == "\n":
                clean.append(text[pos])
            pos += 1
    return [module for line in re.findall(
        r"(?m)^\s*(?:(?:public|private)\s+)?import\s+([^\n]+)", "".join(clean)
    ) for module in line.split()]


def under(module: str, root: str) -> bool:
    return module == root or module.startswith(root + ".")


def check(root: Path) -> list[str]:
    config = tomllib.loads((root / "lakefile.toml").read_text(encoding="utf-8"))
    libraries = config.get("lean_lib", [])
    modules: dict[str, list[str]] = {}
    owners: dict[str, str] = {}
    source_paths: set[Path] = set()
    library_roots: dict[str, list[str]] = {}
    failures: list[str] = []
    for library in libraries:
        name = library["name"]
        roots = library.get("roots", [name])
        if library.get("globs", roots) != roots:
            failures.append(f"{name}: custom build globs need explicit coverage-check support")
        library_roots[name] = roots
        source = root / library.get("srcDir", ".")
        for module_root in roots:
            stem = source.joinpath(*module_root.split("."))
            paths = ([stem.with_suffix(".lean")] if stem.with_suffix(".lean").is_file() else [])
            if stem.is_dir():
                paths.extend(sorted(stem.rglob("*.lean")))
            for path in paths:
                module = ".".join(path.relative_to(source).with_suffix("").parts)
                if module in owners and owners[module] != name:
                    failures.append(f"{module}: belongs to both {owners[module]} and {name}")
                owners[module] = name
                source_paths.add(path.resolve())
                modules[module] = imports(path.read_text(encoding="utf-8"))

    # A tracked source outside the configured libraries is also an orphan.
    # Git submodules are gitlinks, so this does not enumerate dependency trees.
    if (root / ".git").exists():
        tracked = subprocess.run(
            ["git", "-C", str(root), "ls-files", "-z", "--", "*.lean"],
            check=True, capture_output=True, text=True,
        ).stdout.split("\0")
        for filename in filter(None, tracked):
            path = root / filename
            if path.is_file() and path.resolve() not in source_paths:
                failures.append(f"{filename}: tracked source outside configured libraries")

    local_roots = [item for roots in library_roots.values() for item in roots]
    for module, dependencies in modules.items():
        for dependency in dependencies:
            if any(under(dependency, prefix) for prefix in local_roots) and dependency not in modules:
                failures.append(f"{module}: missing local import {dependency}")
            if under(module, "Vegas") and any(under(dependency, prefix) for prefix in
                    ("VegasEVM", "VegasTests", "Paper")):
                failures.append(f"{module}: core imports downstream module {dependency}")
            if under(module, "VegasEVM") and any(under(dependency, prefix) for prefix in
                    ("VegasTests", "Paper")):
                failures.append(f"{module}: backend imports downstream module {dependency}")
            if under(module, "VegasTests") and under(dependency, "Paper"):
                failures.append(f"{module}: test imports paper audit {dependency}")
            if under(module, "Vegas.Machine") and under(dependency, "Vegas.Compile"):
                failures.append(f"{module}: machine carrier imports compiler {dependency}")
            if under(module, "Vegas.Runtime") and any(under(dependency, prefix) for prefix in
                    ("Vegas.Game", "Vegas.Compile", "Vegas.Machine", "Vegas.Scheduled")):
                failures.append(f"{module}: runtime-general interface imports {dependency}")

    def reachable(starts: list[str]) -> set[str]:
        seen: set[str] = set()
        pending = list(starts)
        while pending:
            module = pending.pop()
            if module not in seen and module in modules:
                seen.add(module)
                pending.extend(modules[module])
        return seen

    starts: list[str] = []
    for target in config.get("defaultTargets", []):
        starts.extend(library_roots.get(target, [target]))
    covered = reachable(starts)
    for module in sorted(modules.keys() - covered):
        failures.append(f"{module}: unreachable from default build roots")

    # These public aggregators promise their complete subtree, not only a
    # subset incidentally reached through the paper audit or test suite.
    for aggregator in ("Vegas.Game", "Vegas.Runtime"):
        covered = reachable([aggregator])
        for module in sorted(modules):
            if under(module, aggregator) and module not in covered:
                failures.append(f"{module}: absent from {aggregator} aggregator")
    return failures


if __name__ == "__main__":
    errors = check(Path(__file__).resolve().parent.parent)
    for error in errors:
        print(error, file=sys.stderr)
    if errors:
        sys.exit(1)
    print("Local imports, build-root coverage, and module boundaries check out.")
