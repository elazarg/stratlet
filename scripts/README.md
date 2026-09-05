# Maintenance scripts

Run these tools from the repository root.

- `python scripts/check-lean-options.py` rejects source-local `set_option`
  directives in Vegas and VegasTests. Shared elaboration and lint settings
  belong in `lakefile.toml`; separately managed dependencies keep their own
  package configuration.
- `scripts/bump-lean-mathlib.sh v4.32.0` updates the Lean toolchain and
  Mathlib pins, advances the recursive `GameTheory` submodule, refreshes Lake
  manifests, and verifies that the dependency pins agree. Review the resulting
  changes and run `lake build` afterward.
- `python lean-defs.py Vegas` prints the Lean declaration surface below the
  supplied files or directories while omitting imports and proof bodies. With
  no arguments it scans the current directory recursively. It is a reading and
  review aid; it does not participate in the build.
- `python scripts/check-doc-references.py` fails if a Lean docstring cites a
  name that does not exist. Docstrings here carry real load -- which theorem
  does the work, which hypothesis a result needs, which witness refutes a
  converse -- and a citation that stops resolving after a rename turns that
  guidance into misdirection with nothing in the build noticing. It checks
  backticked tokens shaped like our own names (lower-case, underscored), so
  type names, tactics, and prose are untouched.
