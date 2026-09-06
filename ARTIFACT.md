# Vegas: proof and artifact guide

This artifact supports the finite-model compiler results in *Vegas: Preserving
Strategic Behavior through Compilation*. It is not an end-to-end verification
of the Kotlin compiler or deployed contracts. For the research assessment see
[docs/submission-assessment.md](docs/submission-assessment.md); for public
delivery and deadline obligations see [docs/runtime-models.md](docs/runtime-models.md).

## Reproduction

Prerequisites are Git, Python 3.10 or later, and Lean's `elan`/Lake toolchain
manager. The repository pins Lean 4.33.1 in `lean-toolchain`; Lake uses
`lake-manifest.json` for dependency revisions. Network access is needed to
obtain the toolchain, submodules, and dependency/cache downloads. No EVM node,
wallet, credentials, or Kotlin build is needed to check the Lean theorem.

From a fresh clone of `https://github.com/elazarg/VegasCore.git`, check out the
revision accompanying the manuscript, then run:

```text
git submodule update --init --recursive
lake exe cache get
python scripts/check-doc-references.py
python scripts/check-lean-options.py
python -m unittest discover -s scripts -p "test_*.py"
lake --wfail build
```

The full default build includes `Vegas`, `VegasTests`, and `Paper`.
`lake --wfail build Paper` is the focused paper-proof build. Do not run `lake
update` to reproduce a pinned revision: it may resolve different dependencies.
The cache download is a build optimization, not evidence that our theorem
statements have been checked; run the build afterward.

On memory-constrained or busy machines, limit the build process's worker pool.
In PowerShell, run `$env:LEAN_NUM_THREADS = '2'` before `lake --wfail build`;
in a POSIX shell, run `LEAN_NUM_THREADS=2 lake --wfail build`. This controls
build concurrency, not proof limits or warning suppression. A parallel clean
build can exhaust memory even when the incremental development build passes.

The manuscript is a **separate repository**, not a submodule fetched by those
commands. Authors should provide its matching source snapshot under `overleaf/`
or as a separate directory. Reviewers should not need an Overleaf account.
With that snapshot available, run:

```text
python scripts/check-paper-claims.py
```

For a differently placed snapshot, use `--paper-dir PATH`. The explicit
`--allow-missing-paper` mode checks the Lean registry only; it is not a passing
manuscript-coverage check. With an ACM-compatible LaTeX installation, rebuild
the reading copy from inside the manuscript directory:

```text
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

## Proof-reading route

Start with `paper-claims.json`, then read the indicated explicit statement in
`Vegas/Paper.lean` or root `Paper.lean`. Audit proofs delegate to the owning
module; inspect its definitions and proof, not only the theorem name.

| Question | Main file or declaration |
| --- | --- |
| What is a checked program? | `Vegas/Core/WellFormed.lean`, `Vegas/Compile/Compiler.lean` |
| How is source information derived? | `Vegas/EventGraph/Protocol.lean`, `toInfoSignals_perfectRecall`; `Vegas/Machine/Program.lean`, `perfectRecall` |
| Which game is analyzed? | `Vegas/Game.lean`; graph-derived frontier semantics, not an independent source game-tree input |
| What does written-order source adequacy prove? | `Vegas/Compile/SourceAdequacy.lean`; endpoint and supported-run reconstruction |
| What is the uniform certificate? | `Vegas/Runtime/DeviationAdequacy.lean`; `DeviationAdequacyOn`, unrestricted `DeviationAdequacy`, composition |
| How are outcomes and utilities separated? | `Vegas/Runtime/OutcomeSimulation.lean`; `Machine.Program.outcomeGame`, `Vegas/Scheduled/Valuation.lean` |
| What if opponents value runtime traces? | `Vegas/Runtime/TraceUtility.lean`, `VegasTests/TraceUtility.lean`; see [outcome and utility boundaries](docs/outcomes-and-utilities.md) |
| Where is request memory reconstructed? | `Vegas/Runtime/RequestCompiler.lean`; `past_eq`, `replay`, `run_law`, `mixed_play_law` |
| How are pure/mixed/behavioral policies connected? | `Vegas/Game/Kuhn.lean`; checked GameTheory laws plus Vegas-specific finite-site coverage |
| How are order-aware deviations handled? | `Vegas/Scheduled/Replay.lean`, `Predraw.lean`, `Equilibrium.lean` |
| What closes the main composition? | `Vegas/Scheduled/Request.lean`; `serializedRequestInterface`, `serializedRequestAdequacy`, `serialized_request_deviation_law`, `serialized_request_approximate_nash_iff` |
| Where are concrete integration witnesses? | `VegasTests/ScheduledRequest.lean`, `QuittingImplementation.lean`, `QuittingWindow.lean`, root `Paper.lean` |
| Where does an independent disclosure game reach the runtime? | `VegasTests/DisclosureCorrespondence.lean`, `DisclosurePayoff.lean`, `SealedOfferEquilibrium.lean`, `SealedOfferRuntime.lean` |

The registry includes the finite disclosure case study and quitting appendix.
The mapping checks structural coverage, not English/Lean semantic equivalence.
Definitions, modeling adequacy, literature comparisons, and prose descriptions
of implementations still require human review.

## Trust and dependency boundary

### Validation snapshot

The full 3,264-job default build passes with `--wfail`, including the independent
outcome-valuation interface, trace-utility boundary, adversarial bound transfer,
and the allocation/transfer example through requests and serialization.
Validation used `LEAN_NUM_THREADS=4` in the development checkout with pinned
dependency caches. The claim registry, documentation-reference and local-option
audits, and all 11 maintenance tests pass. The manuscript is rebuilt and its
affected pages visually checked; its final log has no LaTeX warnings or
overfull boxes.

This validation checks the dependency-tracked build in the development
environment. Fresh-machine reproduction, a cold dependency download, an offline
bundle, and performance benchmarking are separate checks. The worker-pool
setting controls resource use without changing Lean proof-checking options.

### Dependencies

GameTheory is the author's own separately maintained, unpublished GitHub
software library, not a separately published premise and not the subject of
this paper. The artifact pins revision
`c79aec2f08a508bf81ea7ad3a3ebdbc34b83e312` in the submodule. Its relevant
probability, game, information, and generic strategy-correspondence proofs are
rebuilt as dependencies. `Vegas/Game/Kuhn.lean` packages those laws rather than
claiming a new Kuhn theorem. Mathlib's pinned revision is
`0df444a360eaa60ab8c11dca51a86af692955474`; remaining revisions are in the Lake
manifest and recursive submodule records.

The paper audit pins the axioms of every restated theorem. The central results
use `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, project axiom,
or `native_decide` extension occurs in their reported dependencies. This is a
statement about those proof terms, not an audit of every unused module in every
dependency. Lean's kernel and the correctness of the mathematical specifications
remain trusted. Noncomputable strategy translations prove existence/law
correspondence; they are not runnable equilibrium synthesis.

Warning and elaboration options are centralized in `lakefile.toml`. The audit
uses guarded axiom reports intentionally; do not suppress warnings locally to
make a build pass.

## Reading the main result accurately

For each finite-domain checked core, legal request interface, and behavioral
public-data scheduler, the compiler preserves the honest terminal-configuration
law. Every unilateral original-player target controller mixture has a terminal
law that is a finite mixture of source behavioral-deviation laws, with other
players unchanged. Nash and same-error approximate Nash equivalence concern
**compiled profiles**. There is no claim that every target equilibrium is a
compiled source equilibrium.

Request windows admit finite independently sampled private mixtures of complete
controllers, with persistent retry memory. This is not a separately proved
theorem for arbitrary fresh behavioral randomization over an unrestricted
request alphabet. The scheduler sees prior public data and orders, not current
private requests or resolved payloads. Its policy is compiled by an immediately
accepted encoding, and its optimality is never required. It does not control
delivery, censorship, or expiration. Source timeout consequences are retained
even when quitting is profitable.

## Preparing a review bundle

Include the tracked main-repository sources and licenses, the GameTheory
submodule sources and its required recursive submodules, the matching active
manuscript sources, this guide, and the exact revision records. Do not assume
`git archive HEAD` includes submodule contents: it does not. Likewise, the
Overleaf checkout must be exported separately. Do not include `.git/`, `.lake/`,
personal editor state, `tmp/`, credentials, or unrelated Overleaf previews.
Offline reproduction additionally needs the pinned toolchain and all Lake
dependencies; the source bundle alone is network-assisted, not offline-ready.

Record versions using `git rev-parse HEAD`, `git submodule status --recursive`,
and `git -C overleaf rev-parse HEAD`. Supply both repository revisions; one SHA
does not identify this artifact. A fresh-machine reproduction and resource
measurement remain release checks, not claims established by the development
build. Follow the selected venue's anonymity policy in a separate review copy;
keep dependency attribution and the substantive proof boundary intact.
