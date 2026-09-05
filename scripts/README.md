# Maintenance scripts

Run these tools from the repository root.

- `lake --wfail build Paper` checks the paper audit, including the generic
  claims in `Vegas/Paper.lean` and the concrete witnesses in root `Paper.lean`.
  This is also a default build target. Every audit theorem has an axiom pin.
- `python scripts/check-paper-claims.py` checks the active `overleaf/main.tex`
  and its inputs against `paper-claims.json`. Every numbered mathematical
  statement needs a label and a mapping; unnumbered results use a
  `% lean-claim: ID` comment. Add or update the corresponding Lean statements
  and axiom pins when editing a claim, review their mathematical agreement,
  then run this check and the warning-free build before committing both repos.
  The checker verifies structural coverage, not equivalence of English and
  Lean. CI without the separately managed Overleaf checkout explicitly uses
  `--allow-missing-paper` and checks only the Lean side of the registry; the
  full local check is required for paper edits.
- `python -m unittest discover -s scripts -p 'test_*.py'` checks the maintenance
  tooling, including missing claims, stale mappings, missing axiom pins, and
  active-paper input discovery.

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
