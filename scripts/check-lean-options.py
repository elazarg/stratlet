"""Keep elaboration and lint policy in the package configuration."""

from pathlib import Path
import re
import sys
import tomllib


def check_central_options(options: dict) -> list[str]:
    """Require explicit theorem binders and warning-strict compilation."""
    required = {
        "autoImplicit": False,
        "relaxedAutoImplicit": False,
        "warningAsError": True,
    }
    return [
        f"lakefile.toml: leanOptions.{name} must be {str(value).lower()}"
        for name, value in required.items()
        if options.get(name) is not value
    ]


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    local_option = re.compile(r"^\s*set_option\b")
    with (root / "lakefile.toml").open("rb") as config:
        failures = check_central_options(tomllib.load(config).get("leanOptions", {}))
    paths = list(root.glob("*.lean"))
    for directory in ("Interaction", "InteractionTests", "Vegas", "VegasEVM", "VegasTests", "Paper"):
        paths.extend((root / directory).rglob("*.lean"))
    for path in sorted(paths):
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if local_option.match(line):
                failures.append(f"{path.relative_to(root)}:{number}: {line.strip()}")
    if failures:
        print("Lean option policy violations:")
        print("\n".join(failures))
        return 1
    print("Explicit binders and warning-strict compilation configured centrally; "
          "no source-local Lean option directives.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
