"""Keep elaboration and lint policy in the package configuration."""

from pathlib import Path
import re
import sys


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    local_option = re.compile(r"^\s*set_option\b")
    failures = []
    paths = list(root.glob("*.lean"))
    for directory in ("Interaction", "InteractionTests", "Vegas", "VegasEVM", "VegasTests", "Paper"):
        paths.extend((root / directory).rglob("*.lean"))
    for path in sorted(paths):
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if local_option.match(line):
                failures.append(f"{path.relative_to(root)}:{number}: {line.strip()}")
    if failures:
        print("Configure Lean options in lakefile.toml, not in source files:")
        print("\n".join(failures))
        return 1
    print("No source-local Lean option directives in project Lean sources.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
