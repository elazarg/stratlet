# Semantics spine

This document states the semantic ownership and proof boundaries of VegasCore.

## Objects and ownership

| Layer | Canonical object | Owns |
|---|---|---|
| Source | `VegasCore P L Γ` | typed protocol syntax and visibility |
| Written-order source game | `sourceGameForm prog env` | source-site policies, visible environments, exact terminal-environment law |
| Checked source | `WFProgram P L` | freshness, reveals, live guards |
| Machine IR | `Machine.Program P L` | typed graph, reified node/payoff code, primitive graph execution |
| Exact probability | `IExpr.evalLaw`, `EventDist.evalLaw` | normalized rational tables retained through compilation |
| Payoff compilation | `Machine.compile_sourcePayoffOfTerminal` | exact terminal source/machine payoff equality |
| Source support | `Machine.compile_sourceStar` | terminal graph runs reconstruct written-order source runs |
| Strategic execution | `ExecutionProtocol P` | active players, legal joint actions, chance, terminality |
| Strategic information | `InformationModel execution` | signals, local information, local menus |
| Vegas game | `Vegas.Game P` | FOSG arena, history utility, bounded horizon, pure/behavioral/mixed-pure forms |
| Kuhn bridge | `Vegas.Game.Kuhn` | opponent-preserving behavioral/mixed deviation certificates |
| Lowering stage | `Machine.System` | one concrete operational command/state surface |
| Step projection | `Machine.Refinement` | visible abstract steps and administrative stuttering |
| Contract manifest | `Machine.Contract.Manifest` | finite lossless storage/action inventory for emitters |
| Storage layout | `Machine.Contract.Layout` | bounded collision-free physical keys for logical slots |
| Logical ABI | `Machine.Contract.Request` | executable raw-envelope and valid-command acceptance |
| Storage words | `Machine.Contract.StorageCodec` | typed target-word round trips and slot noninterference |
| Stored state | `Machine.Contract.RawStore` | executable snapshot round trip and reachable-state injectivity |
| Stored ABI | `Machine.Contract.Request.acceptsStore` | raw-storage validation equal to semantic availability |
| Logical execution | `Machine.Contract.Request.executeConfig?` | exact reachability-erased machine step law |
| Stored execution | `Machine.Contract.Request.executeStore?` | exact machine law transported through raw storage |
| Player authentication | `Machine.Contract.PlayerCall` | injective caller roles plus exact semantic validity |
| Player transaction | `Machine.Contract.PlayerCalldata` | word decoding, caller authentication, and exact stored execution |
| Internal transaction | `Machine.Contract.InternalCalldata` | explicit trigger authorization and exact stored execution |
| Contract lifecycle | `Machine.Contract.initialStore`, `terminalPayout?` | exact deployment state and terminal source-payoff readout |
| Configured contract | `Machine.Contract.ConfiguredContract` | whole typed word-call target with exact dispatch laws |
| Wire transactions | `Machine.Contract.WireCodec` | lossless serialization and exact call-law transport |
| Trusted oracle | `Machine.Contract.OracleProtocol` | deterministic request/callback sampling with exact fixed-policy law |
| Classical contract | `Machine.Contract.ClassicalContract` | complete deterministic typed transaction endpoint |
| Ideal visibility | `Machine.Contract.IdealVisibility` | exact source observations with raw sealed and administrative state hidden |
| Atomic frontier | `Machine.Contract.FrontierBatch` | simultaneous source round serialized without intermediate observations |
| Classical compiler | `ClassicalCompiler.Backend.compile` | checked-source assembly with source terminal certificate |
| Classical EVM ABI | `Machine.Contract.EVM.ClassicalABI` | four-selector 36/68/100-byte deterministic calldata framing |
| EVM-byte artifact | `ClassicalCompiler.EVMByteBackend.compile` | checked source to executable deterministic byte-calldata contract |
| Strategic certificate | `Runtime.DeviationAdequacy` | unilateral target-strategy back-translation |
| Trusted roles | `Runtime.TrustedRoleAdequacy` | Nash adequacy for real players with fixed runtime-only roles |
| Known mediator | `Runtime.KnownMediator` | exact externalization of stochastic play to one fixed contingent strategy |
| Same-strategy endpoint | `Runtime.Implementation` | decoded trace-law equality |

The written-order source game interprets the source AST directly. The machine
IR has a separate graph-derived strategic interpretation, obtained as an
informed protocol. Runtime compilation lowers its reified code through explicit
operational stages. Identifying these two strategic interpretations requires a
compiler theorem; it is not a definitional equality.

## Reified code and denotation

Every sample, commit guard, and payoff retains the typed embedded-language term
and a proof-indexed mapping from its variables to graph storage fields. The same
node also exposes a dependency-local denotation used by graph proofs.

The event-graph compilation result retains the terminal source context and
payoff expressions rather than discarding them after code generation. At every
terminal reachable machine store, store coherence and the compiler field map
reconstruct a complete typed source environment, including sealed bindings.
Compiled payoff evaluation is proved equal to source `evalPayoffs` in that
environment.

This separation permits a backend to translate syntax while correctness proofs
relate the translated code to the existing denotation. The abstract `IExpr`
interface does not promise that every embedded language has every backend; a
backend provides a lowering for the concrete expression language it supports.

`Machine.compile_sourceStar` additionally proves support-level adequacy. From
the semantic validity invariant of every completed graph node, it reconstructs
a written-order `SmallStep.Star`: samples remain in source support, commitments
satisfy their source guards, reveals copy the same sealed values, and the final
payoff agrees. This coarsens away the graph schedule. It does not prove equality
of quantitative run laws, intermediate observations, or strategic behavior.

`Vegas/Core/Strategy.lean` defines the independent quantitative source
semantics. A policy receives a structural commitment site and exactly the
erased `viewVCtx` environment at that site. The interpreter executes the AST in
written order and returns a finite law over terminal environments; utilities
can be attached separately. Its supported results satisfy `SmallStep.Star`.

The compiler's local decision interface has an exact correspondence:
`sourceViewEquiv` identifies the declared graph reads with the source view,
using field-allocation injectivity. `compileSourceDecision` and
`backtranslateSourceDecision` preserve guarded probability laws and are mutual
inverses. Sample code also retains its exact source law. These statements do
not yet connect an entire source profile to the graph game's history-dependent
policy carrier. The remaining obligation is recorded in
[Source strategic correspondence](source-correspondence.md).

## Probability

`FinDist` is the probability monad throughout graph execution, protocol
transitions, strategic play, machine refinement laws, and runtime adequacy.
`RationalLaw` is an intrinsically normalized rational table retained by
`IExpr.evalLaw` and graph-local `EventDist.evalLaw`; its semantic denotation
uses `FinDist.ofWeights`. Source-to-graph compilation proves equality of the
tables themselves, not only equality after denotation.

There is no subprobability in the semantic spine. Checked programs terminate
within a proved bound. A concrete chance mechanism must nevertheless prove its
law; on-chain entropy is not exact merely because the source law is exact.

## Graph-to-protocol interpretation

The execution state is a reachable graph configuration. Internal sample and
reveal nodes execute as idle protocol rounds. At a strategic checkpoint, each
active player supplies a `FrontierAction` containing values for its ready commit
nodes. The joint frontier is simultaneous in the strategic semantics; its
independent writes commute.

The canonical interpretation is noncomputable: when internal nodes are ready,
`EventGraph.toExecutionProtocol` selects one with `Classical.choose`. Its
strategic guarantees concern this mathematical execution model. Executable
node selection and a proof-producing syntax-to-`WFProgram` checker are separate
implementation obligations.

Availability is state- and guard-dependent. Illegal values are absent from the
menu and therefore absent from the strategy and deviation space. Guard
liveness proves progress. Every realized round strictly grows the completed
downset, so `graph.nodeCount` is a uniform `BoundedHorizon`.

Public/private snapshots prove menu adequacy: indistinguishable states have the
same activity and legal options. The information state retains the latest
snapshot and exactly the player's own earlier decision record, not unrelated
transition ordering. This representation has proved perfect recall. Menus at
unreachable information values use an idle fallback so total policy carriers
remain inhabited.

## Why MAID is not the denotation

Vegas decision sites have state-dependent guarded menus and may combine several
ready commitments in one simultaneous joint decision. A fixed-domain MAID node
does not natively express that surface. Totalizing invalid choices would change
the strategy and deviation spaces.

A MAID can be an export for a fragment with a proved strategic correspondence;
it is not the canonical denotation. The FOSG is exact because it packages the
accepted execution and information objects directly.

## Gradual runtime interpretation

A lowering pass should introduce one implementation concern at a time.
`Machine.Refinement` proves only the functional stochastic projection:
concrete commands decode to an abstract command or to an abstract stutter, and
the projected laws agree exactly. These certificates compose.

`Machine.AdministrativeLayer` realizes the first reusable pass in this chain.
It adds a metadata component and metadata-only stochastic commands, while
deriving exact step projection and terminality preservation. An optional lifted
observation hides the metadata by construction. That lifted model applies only
when the intended runtime exposure really omits the metadata.

`Machine.Instrumentation` handles metadata changed atomically by semantic
steps, rather than by target-only commands. Its exact projection covers such
concerns as completion flags, sequence counters, and receipts. The reference
`executionLog` records realized step order; exposing that log would change the
observation model and therefore requires an explicit companion theorem.

`Machine.Contract.Manifest` then exposes the lossless logical inventory an
emitter needs: typed value slots, completion slots, stable actions, direct
dependencies, authority, player input types, and node code. It intentionally
stops before choosing physical storage, ABI scheduling, participant addresses,
entropy, cryptography, timeout behavior, settlement, or bounded target
arithmetic.

`Machine.Contract.Layout` isolates the physical-key decision. Its canonical
instance is dense and injective, placing typed value slots before action
completion slots. A target value codec and its arithmetic semantics are still
required before these keys describe executable EVM storage.

`Machine.Contract.Request` erases a valid dependent command to a stable node
id, logical authority, and optional typed value. `Request.accepts` computes
node bounds, authority/payload shape, readiness, typed-read availability, and
commit guards. Its adequacy theorem says that it accepts exactly the envelopes
represented by currently valid machine commands, matching the classical
reference decoder. Address authentication, concrete calldata/storage decoding,
revert traces, gas, and a concrete internal-action trigger policy remain
separate lowering decisions.

`Machine.Contract.StorageCodec` isolates target-word encoding. Typed reads and
writes over any certified layout have same-slot round trips; writes to distinct
value or completion slots are proved noninterfering. Its reference codec is a
lossless semantic model rather than a serializable backend format. Since
`simpleExpr` interprets integers as unbounded Lean `Int`, VegasCore cannot
provide an exact 256-bit EVM codec without adding bounded integers, proving a
range restriction, or selecting modular/checked-overflow behavior. That is a
source/compiler design obligation, not functionality inherited from
GameTheory.

`Machine.Contract.RawStore.encodeSnapshot` stores the finite graph snapshot in
the canonical layout, leaving absent graph values uninitialized and writing
every completion bit explicitly. `decodeSnapshot` is executable and a proved
left inverse; `encodeState` is injective on reachable machine states. Decoding
arbitrary storage establishes structural well-typedness, not semantic
reachability, which remains a transition invariant for a concrete runtime.

`Machine.Contract.Request.acceptsStore` composes canonical storage decoding
with the executable logical validator. For any encoded reachable state, it is
proved to return exactly semantic command availability. The boundary still
receives a typed logical request; concrete word/calldata decoding and address
authentication have not been silently folded into it.

`Machine.Contract.Request.executeConfig?` adds the exact next-state law after
the same finite checks. It succeeds exactly when `acceptsConfig` does, and an
encoded valid command produces precisely the raw-configuration projection of
`Machine.step`. Distribution compilation retains more than that semantic
result: `IExpr.evalLaw` produces an exact normalized `RationalLaw`,
`EventDist.evalLaw` exposes the graph-local table, and the compiler proves
table equality with source evaluation. The denoted `FinDist` is still a
noncomputable PMF used for analysis. A backend therefore has exact finite
probability data, but still needs an entropy/sampling implementation and a
proof that its physical output law realizes that table; GameTheory does not
choose that target policy.

`Machine.Contract.Request.executeStore?` composes that law with storage
decoding and successor re-encoding. On an encoded reachable state and valid
command envelope, it is exactly `Machine.step` pushed through the injective
raw-state encoding. The converse theorem starts from an arbitrary accepted
request: it reconstructs a valid semantic command and identifies the full
successor law with that command's encoded machine step. Accepted hostile input
therefore preserves encoded reachability. This closes the logical state
representation path, not the backend entropy implementation.

`Machine.Contract.PlayerRegistry` assigns distinct target caller identities to
semantic players. `PlayerCall.acceptsStore` is true exactly when the physical
caller owns the claimed role and the logical commit request denotes a valid
machine command. It covers player commits only; selecting who may trigger
internal chance and reveal work remains a separate runtime-policy pass.

`Machine.Contract.PlayerCalldata` lowers a player commit to caller identity,
claimed player, node id, and one target word. The graph row supplies the
expected language type; decoding rejects non-commit nodes, wrong owners, and
ill-typed words. Encoding any valid semantic commit decodes to the same logical
request and is accepted over the encoded state. The adjacent word-call
executor composes this decoder with caller authentication and stored execution.
For every valid semantic commit, its successor law is exactly `Machine.step`
transported through `RawStore.encodeState`. This is not yet an extractable
transaction processor because the result is expressed as a semantic
`FinDist`, though player commits are deterministic. Byte-level ABI selectors
and gas are still target concerns; finite sampling is needed only when the
internal path realizes a retained probability table.

`Machine.Contract.InternalCalldata` gives samples and reveals a distinct
caller-bearing entry point. Its decoder excludes player commits, while an
explicit `TriggerPolicy` decides which `(caller, node)` pairs are authorized,
allowing sample and reveal nodes to use different authorities. Encoding an
available internal event for an authorized caller produces exactly the same
stored successor law as the corresponding `Machine.step`. This is a local
one-step theorem, not scheduler preservation: caller choice among concurrent
nodes, transaction ordering, observable failed calls, and sample realization
remain explicit target behaviors requiring additional operational and
strategic results.

`Machine.Contract.initialStore` is the canonical constructor state: the raw
encoding of `Machine.init`, with every action completion bit false.
`terminalPayout?` decodes raw storage, performs a finite all-nodes-complete
check, and only then evaluates retained payoff code. On reachable encoded
states it is exactly the machine payoff evaluator. For a compiled source
program, a terminal result is additionally proved equal to source payoff
evaluation in an actual reconstructed terminal environment. The outcome is
data for a later settlement pass; VegasCore still has no asset, transfer,
withdrawal, or failure semantics to justify such effects.

`Machine.Contract.ConfiguredContract` assembles the certified pieces without
adding another semantic decision: manifest, canonical layout, word codec,
player registry, trigger policy, constructor storage, terminal readout, and a
typed sum of player/internal calldata. Its dispatcher succeeds exactly when
the selected entry-point validator accepts, and both valid transaction forms
retain their exact raw-store `Machine.step` laws. This is the object a concrete
backend lowers further; it is not byte ABI, EVM code, or a scheduler.

`Machine.Contract.WireCodec` then isolates transaction serialization. A codec
encodes the full typed call sum into a target wire carrier, decodes arbitrary
inputs with failure, and proves a left inverse on emitted calls. Validation
and execution agree after decoding, and both player/internal one-step laws
transport through encoding. Starting instead from any accepted arbitrary wire
value, the converse theorem reconstructs some valid semantic command and its
exact encoded successor law. A concrete ABI must still choose selector bytes,
address representation, word representation, and malformed-input behavior;
the reference identity codec makes none of those choices.

`Machine.Contract.OraclePolicy` gives every evaluated exact rational table a
canonical law on its retained entry indices. `OracleCalldata` deterministically
executes an authenticated index callback, and the fixed index policy is proved
to recover the original machine sample law on both graph state and canonical
storage. `OracleProtocol` separates that callback from a preceding request:
request emission is a storage-level stutter plus pending metadata, the pending
phase locks further sample requests, and the callback returns to idle. This is
a classical trusted-role theorem. It assumes the oracle policy and eventual
response; it does not establish unpredictability, non-withholding, or strategic
adequacy for observable request timing.

`Machine.Contract.DeterministicExecutor` removes the remaining semantic point
laws from commits and reveals. `ClassicalContract` composes those direct paths
with the oracle protocol, pending-phase lock, outbound requests, rollback-ready
results, constructor state, and terminal outcome. `ClassicalCompiler.Backend`
then assembles that contract directly from `Machine.compile source` plus
deployment choices and retains the source terminal-run/payoff theorem. This is
the complete ordinary typed compiler endpoint. Public commitment transport,
trusted-role removal, target signal adequacy, bounded expression lowering, and
EVM emission are subsequent refinements rather than hidden assumptions of this
endpoint.

That law alone is insufficient when a pass changes what a player or scheduler
can do or observe. Required companion results depend on the pass:

- added deterministic bookkeeping: stuttering projection may suffice;
- added randomness/noise: independence and observation laws are required;
- chosen ordering or concurrency: linearizability and schedule-information
  results are required;
- added target actions: a strategy/context back-translation is required;
- cryptographic hiding: a computational or idealized noninterference theorem is
  required;
- timeouts and nonparticipation: liveness and utility semantics are required.

`Runtime.DeviationAdequacy` is one exact, deliberately limited game-level
certificate. Honest compiled profiles preserve decoded laws, and every
unilateral target replacement has a law-equivalent source replacement. This
proves Nash equivalence at compiled profiles. It says nothing about
coalitions, arbitrary linked contexts, or scheduler hyperproperties.

`Runtime.Implementation` applies only when no new strategy carrier remains. Its
profile-uniform decoded-law equality is then a special case of deviation
adequacy, not a substitute for earlier pass proofs.

## Blockchain obligations

A concrete chain path still needs certified layers for expression lowering,
target-level scheduling/ABI lowering, a finite target codec, authentication,
commitment/reveal, randomness, time and failure, settlement, and bytecode.
Source actions can represent quitting explicitly, including option-valued
disclosure and its continuation. Private request windows account for invalid
requests and exhaustion by selecting designated actions of the graph-derived
game. Public delivery, censorship, concrete deadlines, and monetary settlement
still require target models and proofs.

The existing readability-fence theorem constrains the order of readable output
values. It explicitly does not prove indistinguishability of complete observed
traces, whose event occurrences remain public. It is useful groundwork for a
strong-linearizability proof, not that final proof.

## Upstream boundary

GameTheory supplies the strategic objects and exact transformations used by
Vegas. In particular, its `InformationModel` has opponent-preserving
unilateral Kuhn laws. `Vegas.Game.Kuhn` packages those laws as deviation
adequacy in both directions. Compiled programs discharge perfect recall.
Finite source domains also construct a full-support finite counterfactual site
cover, so the unilateral certificates apply without assuming a globally finite
information-history carrier.

GameTheory does not supply a general secure-compilation or runtime
hyperproperty framework; that boundary is domain-specific and remains in
VegasCore. Its MAID surface also uses fixed decision domains, so exporting a
guarded Vegas game to MAID requires a fragment restriction or a proved
strategic encoding.
