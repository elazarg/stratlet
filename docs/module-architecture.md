# Library and proof boundaries

This is the implemented module inventory. The
[compilation design](compilation-design.md) specifies semantic ownership and
the [implementation plan](ledger-expansion-plan.md) gives the extraction and
public-message-runtime gates. Proposed ownership is not implemented separation.

The package has six build targets. `lake --wfail build` checks all six;
`lake --wfail build Vegas` checks the Vegas library without the backend or the
independent message-interaction experiments.

| Target | Contents | Local dependencies |
| --- | --- | --- |
| `Interaction` | Native pending-message kernel, ideal commitment service, sealed application rules, bounded policies and hiding | none |
| `InteractionTests` | Bounded native interaction games and commitment-traffic tests | `Interaction` |
| `Vegas` | Core and surface syntax, event graphs, machine semantics, games, abstract runtimes, public serialization, sealed-message compiler fragment | `Interaction` |
| `VegasEVM` | Contract representations, deployment and instruction semantics, backend compilation, local code-generation proofs | `Vegas` |
| `VegasTests` | Concrete witnesses and regression tests | `Vegas`, `VegasEVM` |
| `Paper` | Axiom-pinned general claims and concrete paper witnesses | `Vegas`, `VegasEVM`, `VegasTests` |

Mathematical modules also use the pinned external dependencies; the
`Interaction` operational kernel itself imports none; its policy interpretation
uses GameTheory's existing `GameForm` and finite laws. The table describes local
library dependencies, not additional logical axioms.

## Message-interaction boundary

`Interaction/MessagePool.lean` is an executable kernel: submit, deliver to any
selected observer, and append a selected pending message to a shared public
ledger. Sender-local serials avoid exposing an unrelated global submission
counter. A submission carries a caller label; a principal-scoped controller
interface must supply and enforce that identity. The raw operation alone does
not authenticate the caller. There is no application
validation, fee, deadline, finality, or progress assumption in this carrier.
Replay copies an envelope from the broadcaster's own view, preserving the
original author and admitting duplicate pending/ledger copies.
`Interaction/MessageReplay.lean` proves observation-locality and exact copying.
There is no transaction-nonce filter or multi-instance replay protection.

`InteractionTests/Pending.lean` interprets a bounded two-player script directly
as a GameTheory `GameForm`. Its play uses the same native pool operations and
its responder receives only its local view. Delivery and inclusion-order
parameters specify a fixed environment; this example does not define the
general class of adaptive network controllers.

`Interaction/IdealCommitments.lean` is explicit private write-once storage
indexed by owner and slot. It specifies an ideal functionality, not a
cryptographic implementation. `InteractionTests/Commitment.lean` exercises
observable pending handles, legal cleartext, authenticated opening checks,
and value-bearing openings that disclose before inclusion. The hiding test
gives continuations the pool, not the ideal table or its verifier; the service
file alone defines no strategic interface enforcing that restriction. No Vegas compiler edge
or equilibrium-preservation claim is established by these tests.

The boundary checker forbids these runtime modules and their independent
tests from importing Vegas, its backend, or its paper audit. The native
kernel and ideal service themselves need no GameTheory imports; policy
interpretations use GameTheory's existing strategic and probability interfaces.

`Interaction/SealedProgram.lean` defines runtime-general commitment/opening
rules, public application events, validation, and a public-state opening
controller. `Interaction/SealedExecution.lean` runs registration, raw
submission, local delivery, replay, and inclusion using those same operations.
`SealedExecutionLaws` lifts application-node uniqueness over arbitrary native
action lists, independently of message duplication.
`Vegas/Compile/SealedMessages.lean` emits rules from a certified graph fragment;
the `SealedDecode`, `SealedRules`, `SealedExecution`, and `SealedRefinement`
modules prove the actual graph-step correspondence. `SealedSource` composes it
with source-support correctness. `Interaction/SealedPolicies.lean` supplies a
bounded principal-scoped policy interpretation of this same runner, with
sampled local memories and an explicit wire-observing environment.
`SealedPolicyLaws` proves exact-law embedding of the no-rebroadcast instance
and a native action-trace witness for every supported policy execution.
`Vegas/Game/SealedMessages.lean` connects those executions to the checked source
at support level. `SealedHiding` and `SealedPolicyHiding` prove ideal
pre-disclosure observation-law equality; the precise observation and invocation
conditions are in the [runtime inventory](runtime-models.md).
None of these modules imports the EVM backend. Source-policy backtranslation
under public delivery remains a separate obligation.

## Backend correctness

`VegasEVM/Compile/EVMRefinement.lean` defines `BooleanCompilationCorrect`, the
whole-backend instruction-level simulation obligation. It is not discharged.
The checked expression and handler lemmas in the backend do not imply that
obligation, nor do they establish strategic preservation on deployed bytecode.
Keeping the backend in the full default build checks its existing proofs while
allowing consumers of `Vegas` to avoid importing this development.

`VegasEVM/Contract/EVMExecution.lean` supplies a gas-free semantics for the
emitted instruction subset. It is not validated against Ethereum's conformance
suite; code-generation proofs are relative to that model. `IdealVisibility`
supplies semantic hiding, not cryptographic commitments in public EVM storage.
Terminal payout readout does not prove asset movement. These modeling and
deployment obligations remain even after local handler proofs are checked.

## Carrier definitions and compiler edges

`Vegas/Machine/Program.lean` defines the backend-neutral machine carrier and
its execution model. `Vegas/Compile/Machine.lean` constructs it from checked
source programs and proves source-support and terminal-payout adequacy.
The machine carrier does not import its compiler.

`Vegas/Game/Basic.lean` defines bounded analyses of native execution and
information objects and their graph-derived instances. It does not import
FOSG. `Vegas/Game/FOSG.lean` supplies the optional presentation export using
the same objects and no additional runner.
`Vegas/Game/Kuhn.lean` supplies strategy-representation certificates, and
`Vegas/Game/Request.lean` instantiates generic request compilation for games.
`Vegas/Game/SourceRequest.lean` specializes the request certificates to checked
source programs. The `SourceCorrespondence`, `SourceRequestCorrespondence`, and
`SourceCorrelated` modules connect independent source policies to those games.
`Vegas/Game.lean` reaches all these modules. These strategic adapters
depend on source-to-machine lowering; the lowering does not depend on games.
The runtime interfaces do not import the game-specific adapters.

`Vegas/Language/Basic.lean` owns surface syntax; `Vegas/Language/ToCore.lean`
owns its typed lowering. The lowering returns core syntax, not a `WFProgram`
certificate. The language regression tests check specific lowering equations
and nullable-guard behavior. General admission and semantic-preservation
theorems for that surface language remain separate obligations.

## Ownership and maintenance

Declarations extending graph execution live in `Vegas.EventGraph`, even when
their files are under `Vegas/Scheduled/`. Public modules group related results;
declaration namespaces identify the objects or constructions they concern.
The graph serialization implementation uses the existing graph write lemmas
directly instead of re-exporting copies under a compiler grouping namespace.
Player-only equilibrium notions and independent-signal constructions live
under `Vegas.Participant`; the public-submission counterexample has its own
`Vegas.PublicSubmission` namespace. Generic finite-law composition and product
projection belong to GameTheory's `FinDist` API; bounded execution and
one-participant predrawing belong to its protocol layer. The scheduled-runtime
proofs use those APIs and supply the scheduler-specific information and
profile facts.

Use `private` for helpers whose role is confined to a proof or implementation.
Usage counts alone are insufficient: typeclass instances, simplification
lemmas, theorem-statement dependencies, and intentional analysis APIs may have
no explicit callers outside their defining file.

`scripts/check-module-boundaries.py` checks local import resolution, default-root
coverage, complete game/runtime aggregators, and the dependency directions
above. It also rejects cycles in the local module graph and between sibling
directory layers at every nesting depth, reporting the imports that form each
cycle. Aggregators belong to the directory they represent; imports between
ancestors and descendants stay within that layer. The direction rules remain
necessary because an acyclic import can still cross an architectural boundary.
The checker scans configured library trees, not temporary research checkouts.
The warning-free Lean build remains the check that imports and proofs elaborate.

`scripts/check-doc-references.py` also checks exact Lean file paths in tracked
Markdown and relative Markdown/Lean links, separately from declaration-name
citations in Lean sources. A valid namespace does not establish that a cited
file exists.

The paper audit lives in `Paper/General.lean`, `Paper/Source.lean`, and root
`Paper.lean`; tests use
the owning mathematical theorems directly rather than importing audit wrappers.
The live manuscript is separately revision-pinned as described in `ARTIFACT.md`.
