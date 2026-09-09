# Maintenance scripts

Run these tools from the repository root.

- `python scripts/check-module-boundaries.py` checks local import resolution,
  default-build reachability, complete game/runtime aggregators, cycles in the
  module and sibling-directory dependency graphs, and the
  interaction/core/backend/test/audit dependency directions. Cycle reports include witness
  imports; acyclicity supplements rather than replaces the direction rules.

- `lake --wfail build Paper` checks the paper audit, including the generic
  claims in `Paper/General.lean`, independent-source claims in `Paper/Source.lean`,
  and concrete witnesses in root `Paper.lean`.
  This is also a default build target. Every audit theorem has an axiom pin.
- `python scripts/check-paper-claims.py --paper-dir PATH` checks the supplied
  manuscript's `main.tex`
  and its inputs against `paper-claims.json`. Every numbered mathematical
  statement needs a label and a mapping; unnumbered results use a
  `% lean-claim: ID` comment. Add or update the corresponding Lean statements
  and axiom pins when editing a claim, review their mathematical agreement,
  then run this check and the warning-free build before committing both repos.
  The checker verifies structural coverage, not equivalence of English and
  Lean. CI without the separately managed Overleaf checkout explicitly uses
  `--allow-missing-paper` and checks only the Lean side of the registry; the
  full check is required for paper edits. `paper-snapshot.json` binds every
  tracked manuscript file to its Git revision by SHA-256. A clean checkout at
  that revision and a plain `git archive` both validate; untracked active
  inputs do not. Authors explicitly refresh the manifest from a clean checkout
  with `--refresh-snapshot`.
  Active bibliography databases must be in the snapshot. Unqualified database
  filenames must also be unique across it, including archived directories, so
  recursive BibTeX lookup cannot silently select a different bibliography.
- `python -m unittest discover -s scripts -p 'test_*.py'` checks the maintenance
  tooling, including missing claims, stale mappings, missing axiom pins, and
  active-paper input discovery.

- `python scripts/check-lean-options.py` rejects source-local `set_option`
  directives in every project Lean source tree and checks that both implicit-binder
  options are disabled and warnings are errors. Shared elaboration and lint settings
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
  backticked tokens whose last component is lower-case and whose name is
  qualified or underscored; type names, tactics, and prose are untouched.
  In tracked Markdown it also checks exact root-qualified Lean file paths in
  inline code and relative `.md`/`.lean` links. Abbreviated paths, link anchors,
  and external resources are outside this check; it is not a full Markdown
  parser or a line-number accuracy audit.
  A non-Git export explicitly reports that the tracked Markdown inventory is
  unavailable; a Git inventory failure in a checkout is an error.
