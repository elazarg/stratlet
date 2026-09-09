# Vegas: proof and artifact guide

This artifact supports the finite-model compiler results in *Vegas: Preserving
Strategic Behavior through Compilation to Blockchain*. It is not an end-to-end verification
of the Kotlin compiler or deployed contracts. For the research assessment see
[docs/submission-assessment.md](docs/submission-assessment.md); for public
delivery and deadline obligations see [docs/runtime-models.md](docs/runtime-models.md).

## Reproduction

Prerequisites are Git, Python 3.11 or later, and Lean's `elan`/Lake toolchain
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
python scripts/check-module-boundaries.py
python -m unittest discover -s scripts -p "test_*.py"
lake --wfail build
```

The full default build includes `Interaction`, `InteractionTests`, `Vegas`,
`VegasEVM`, `VegasTests`, and `Paper`. The independent interaction experiments
are not part of the manuscript's source-compiler preservation claim.
The public-message compiler fragment in `Vegas/Compile/SealedSource.lean`
additionally proves support-level correctness for completed native runs.
`Vegas/Game/SealedMessages.lean` applies it to the bounded native policy game;
the associated ideal hiding and rebroadcast comparisons are separate from
the manuscript's source-deviation theorem. The checked scope and native
execution fixtures are documented in
[runtime models](docs/runtime-models.md).
`Vegas/Compile/ApplicationPlanOutcome.lean` additionally checks generated
binding/public-choice/conditional-publication images. From canonical native
initialization, every completed supported raw or randomized-policy run has
the public outcome of an actual written-order source execution. The explicit
backend plan is a premise; progress, sealed-input provisioning, and strategic
correspondence for public messages are not conclusions. These support claims
are audited in `Paper/Source.lean` separately from the private-window laws.
`Vegas/Compile/ApplicationForwardLaw.lean` additionally proves the independent
source profile's public-terminal law for the generated serial reference run,
including completion. Initial controller reads must be public and conditional
endpoints must have earlier generated binding origins. The theorem retains the
original source profile throughout the shared policy runner; it does not
simulate arbitrary public-message deviations. The mixed-feature regression is
`VegasTests/GeneratedApplicationSourceLaw.lean`, and the paper-facing statement
is `Paper.Source.public_application_reference_law` in the `Vegas` namespace.
`lake --wfail build Paper` is the focused paper-proof build. Do not run `lake
update` to reproduce a pinned revision: it may resolve different dependencies.
The cache download is a build optimization, not evidence that our theorem
statements have been checked; run the build afterward.

Build concurrency is a machine-specific resource setting. The commands above
use the defaults; lower concurrency may help when a rebuild exhausts available
memory.

The manuscript is a **separate repository**, not a submodule fetched by those
commands. `paper-snapshot.json` pins the manuscript revision and SHA-256 digest
of every tracked file paired with this artifact. Authors should provide either
a clean Git checkout at that revision or a plain `git archive` export of it.
Reviewers should not need an Overleaf account or credentials. To create the
export, substitute the manifest's `revision` and the manuscript checkout path:

```text
git -C MANUSCRIPT archive --format=zip --output=paper-source.zip REVISION
```

Extract that archive into `PATH`; it needs no added marker file. Authors update
the committed manifest explicitly from a clean standalone checkout with:

```text
python scripts/check-paper-claims.py --paper-dir MANUSCRIPT --refresh-snapshot
```

With the source available, run:

```text
python scripts/check-paper-claims.py --paper-dir PATH
```

The default paper directory is `overleaf/`. The explicit `--allow-missing-paper` mode
checks the Lean registry only; it is not a passing manuscript-coverage or
revision check and must not be used for full artifact validation. With an
ACM-compatible LaTeX installation, rebuild
the reading copy from inside the manuscript directory:

```text
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

## Proof-reading route

Start with `paper-claims.json`, then read the indicated explicit statement in
`Paper/General.lean`, `Paper/Source.lean`, or root `Paper.lean`. Audit proofs delegate to the owning
module; inspect its definitions and proof, not only the theorem name.

| Question | Main file or declaration |
| --- | --- |
| What is a checked program? | `Vegas/Core/WellFormed.lean`, `Vegas/Compile/Compiler.lean` |
| How is source information derived? | `Vegas/EventGraph/Protocol.lean`, `toInfoSignals_perfectRecall`; `Vegas/Machine/Program.lean`, `perfectRecall` |
| Which source game is analyzed? | `Vegas/Core/Strategy.lean`; `sourceGameForm` and independent written-order `denoteSource` |
| How does the compiler preserve that game? | `Vegas/Game/SourceCorrespondence.lean`; exact source outcome laws and unilateral policy simulation into native graph play |
| How are execution orders compared? | `Vegas/Compile/SourceExecutionLaw.lean`, `Vegas/EventGraph/KernelBehavioral.lean`; actual probabilistic source and batched graph execution |
| What is the uniform certificate? | `Vegas/Runtime/DeviationAdequacy.lean`; `DeviationAdequacyOn`, unrestricted `DeviationAdequacy`, composition |
| How are outcomes and utilities separated? | `Vegas/Runtime/OutcomeSimulation.lean`; `Machine.Program.boundedOutcomeGame`, `Vegas/Scheduled/Valuation.lean` |
| What if opponents value runtime traces? | `Vegas/Runtime/TraceUtility.lean`, `VegasTests/TraceUtility.lean`; see [outcome and utility boundaries](docs/outcomes-and-utilities.md) |
| Where is request memory reconstructed? | `Vegas/Runtime/RequestCompiler.lean`; `past_eq`, `replay`, `run_law`, `mixed_play_law` |
| How are pure/mixed/behavioral policies connected? | `Vegas/Game/Kuhn.lean`; checked GameTheory laws plus Vegas-specific finite-site coverage |
| How are order-aware deviations handled? | `Vegas/Scheduled/Replay.lean`, `Predraw.lean`, `Equilibrium.lean` |
| What closes the main composition? | `Vegas/Scheduled/SourceCorrespondence.lean`; independent-source laws, deviation mixtures, and same-error equilibrium correspondence through serialization and requests |
| Which whole-program law reaches public messages? | `Vegas/Compile/ApplicationForwardLaw.lean`; generated reference-service completion and the independent source public-outcome law, with explicit backend eligibility |
| Where are concrete integration witnesses? | `VegasTests/ScheduledRequest.lean`, `QuittingImplementation.lean`, `QuittingWindow.lean`, root `Paper.lean` |
| Where does an independent disclosure game reach the runtime? | `VegasTests/DisclosureCorrespondence.lean`, `DisclosurePayoff.lean`, `SealedOfferEquilibrium.lean`, `SealedOfferRuntime.lean` |

The registry includes the finite disclosure case study and quitting appendix.
The mapping checks structural coverage, not English/Lean semantic equivalence.
Definitions, modeling adequacy, literature comparisons, and prose descriptions
of implementations still require human review.

## Trust and dependency boundary

### Validation snapshot

The full default build is checked with `--wfail`, including the independent
written-order source interpreter, whole-program source/native law and deviation
correspondence, native CE/CCE transport, and source-to-scheduled/request results.
Validation uses the development checkout with pinned dependency caches. The
claim registry, module-boundary, documentation-reference, and local-option
audits and maintenance tests accompany the Lean build. Rebuild the manuscript
separately to check typesetting and citations; the registry does not validate
the PDF layout.

This validation checks the dependency-tracked build in the development
environment. Fresh-machine reproduction, a cold dependency download, an offline
bundle, and performance benchmarking are separate checks. On memory-constrained
machines, build dependency targets separately before the full default build;
all targets use the same centralized checking options.

### Dependencies

GameTheory is the author's own separately maintained, unpublished GitHub
software library, not a separately published premise and not the subject of
this paper. The artifact pins revision
`3dd93bf05286e5c6996fdf3e991d96a386156d4d` in the submodule. Its relevant
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

Warning and elaboration options are centralized in `lakefile.toml`. Both
`autoImplicit` and `relaxedAutoImplicit` are disabled: theorem and definition
parameters must be declared explicitly. The audit
uses guarded axiom reports intentionally; do not suppress warnings locally to
make a build pass.

## Reading the main result accurately

For each finite-domain checked core, legal request interface, and behavioral
public-data scheduler, the compiler preserves the terminal-environment law of
the independent written-order source semantics. Every unilateral original-player
target controller mixture has a decoded law that is a finite mixture of
source behavioral-deviation laws, with other players unchanged.
Nash and same-error approximate Nash equivalence concern
**compiled profiles**. There is no claim that every target equilibrium is a
compiled source equilibrium.

The source-to-native bridge proves whole-policy information reconstruction,
actual probability-law linearization, and terminal-environment decoding.
It supplies a uniform unilateral outcome simulation; the behavioral scheduler
composition instead supplies profile-local finite mixtures. See
[Source strategic correspondence](docs/source-correspondence.md).

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
