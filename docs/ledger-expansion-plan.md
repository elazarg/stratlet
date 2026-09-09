# Compilation tower: implementation plan

This is the implementation plan for [compilation through operational games](compilation-design.md).
The [ledger design](ledger-expansion-design.md) specifies detailed event,
service, and security obligations. [Runtime models](runtime-models.md) records
what is proved. The plan is not a theorem inventory or a promise that the
strongest proposed preservation claim will hold.
The non-binding [road ahead](a-road-ahead.md) discusses alternatives for
factoring features and reaching the concrete target; its proposals can change
without being treated as completed gates.

## Scope and work order

The implementation objective is at least the draft's feature breadth and
strategic depth through faithful public interaction, with a visible path to
concrete runtimes. The private-window manuscript is an existing checked
baseline, not a substitute endpoint for this objective. In particular, a
single homogeneous commitment example does not recover the draft's guarded,
finite-domain, chance-bearing, multistage compiler result.

The acceptance inventory has two axes:

| Requirement | Public-message path | Required endpoint |
| --- | --- | --- |
| Independent source meaning | Checked source-to-graph connection, terminal native support, and local conditional-publication correspondence; whole-program quitting integration remains open | The actual supported source's choices, information, nonresponse consequences, and outcomes are the comparison endpoint. |
| Source coverage | Homogeneous unrestricted commit/reveal full-run fragment; general certified-site resolution components | General supported finite typed programs with guards, chance, and multistage dependencies; implementation conditions are explicit and exercised. |
| Hostile interaction | Raw traffic, local delivery, replay, public inclusion, ideal binding/hiding; timed final-expiration instance | Whole interaction, failure, deadline and observation behavior under the theorem's complete player/environment policy classes. |
| Strategic comparison | Release-time hiding/choice independence and selective-publication obstruction | Compiled-profile law plus arbitrary unilateral-deviation comparison, with the corresponding source-outcome bounds and equilibrium results. |
| Substantive application | The private-window sealed offer and a public-message compiled-prefix fixture | The application, its emitted controllers/handlers, and its guarantees use the same public-message compiler path. |
| Further lowering | Separate local backend proofs | A named generated-handler path instantiates that application semantics; subsequent realization obligations are explicit. |

An obstruction must identify the incompatible property/model pair and guide
an implemented alternative, supported fragment, or weaker guarantee. It does
not by itself satisfy a missing positive compiler or application requirement.
Do not make eligibility circular by requiring the claimed deviation theorem
as an input certificate. Do not promise exact preservation for a model whose
admitted censorship or withholding contradicts it.

Build the shared operational/strategic runtime connection before expanding
backend breadth. Keep the minimal Vegas core and its well-formedness discipline.
Do not reproduce the rich Kotlin language in Lean.

The first delivery is a public-message model with recipient-local observations,
a real core-to-model compiler slice, and checked strategic evidence about that
execution. A weaker positive result or a precise obstruction is acceptable
evidence at a research gate. A disconnected runtime, a restated preservation
hypothesis, or a trace example alone is not completion.

Prefer focused replacement and extraction to a rewrite without a demonstrated
semantic need. There is no API compatibility requirement: update all consumers
and remove obsolete definitions when their replacements are checked. Keep the
existing valid proofs and default warning-free build throughout the work.

## R0. Establish semantic ownership

**Deliverables**

- Refactor the general Vegas game wrapper so its semantic ownership is not
  FOSG syntax. Keep bounded horizon and utility as analysis data or explicit
  capabilities, not requirements on every future operational target.
- Keep the independent source game as the source endpoint. Update names that
  call the compiled graph game the source game where that is not the meaning.
- Make the FOSG adapter a format export using the existing execution and
  information objects, with no new runner. Preserve current source/native,
  request, and serialization results under the refactor.
- Inventory generic game/protocol transformations currently in Vegas, compare
  them with GameTheory's existing APIs, and obtain the appropriate upstream
  architecture decision for additions. Generic backtranslation, outcome-law
  comparison, preference transport, and their composition belong there.
  Concrete Vegas field/decision reconstruction remains in Vegas.
- Move accepted abstractions with their generic tests into the separately
  managed GameTheory repository, then update Vegas callers and its pin.
  No duplicated stable definitions or compatibility wrappers. This plan does
  not authorize changing a GameTheory architectural decision by fiat.

**Gate**

The existing source and native-game audit statements still compile with the
same mathematical endpoints. FOSG is unnecessary for defining those endpoints.
Every proposed extraction has a named owner, actual clients, and a migration
of callers rather than an extra layer of aliases.

**Concurrency**

The API inventory and bounded public-message experiment can run alongside
this refactor. Freeze the shared runtime interface only after R1's hostile
tests; upstream approval must not block learning whether the model is sound.

## R1. Define the smallest faithful message interaction

Implement a runtime-general model with a parameterized application transition.
Use existing probability and protocol machinery where appropriate. The native
event semantics owns all execution; its GameTheory adapter reuses that law.

Initial state and event surface:

- Raw messages with sender-local identifiers and arbitrary payloads.
  Application destinations and encodings can be carried in the payload.
- Recipient-local delivered views and sender receipts; submission does not
  imply delivery to anyone else.
- A pending-message inventory separate from accepted application state.
- Submission, recipient-local delivery, and public inclusion of an existing
  pending message. Inclusion does not invoke its sender's policy. Start with
  a shared published ledger; delayed block receipt is a later refinement.
- Missing-message lookup has an explicit failure result. Application
  validation, withholding policies, clocks, and resolution drivers are
  separate additions when the positive compiler slice requires them.
- Principal-indexed controls. A principal may have several capabilities;
  environmental policies are explicit, and equilibrium concerns the chosen
  game-player principals.
- Explicit finite resource parameters for the first experiments, without
  making finite state or termination fields of the general runtime carrier.

No privacy assumption is attached to the message pool. An event's recipient
projection determines the signal; prove that unrelated hidden state cannot
affect that signal. Unobserved events leave local information unchanged.
Do not append a hidden global step counter or silently broadcast the clock.

The first bounded scripts use enumerated principals and a finite raw payload
alphabet containing malformed inputs. Do not impose globally finite state on
the kernel or add clocks and fees to obtain a finite test. When a theorem
actually requires finite strategy sites, prove a finite reachable cover for
the fields present, including sender-local serials. Bounded event count alone
does not establish that cover for arbitrary payload or information carriers.

Use the design's player-only game family: bundle capabilities by principal,
fix local policies for external principals, and assemble them with the player
profile for the native runner. Policies receive only their native local views.
Use `InformationModel` where its activation and menu interface fits; a direct
`GameForm` interpretation carries the same locality obligation. Public message
inclusion itself creates no hidden sender-activation problem.

**Required hostile tests**

| Test | Required evidence |
| --- | --- |
| A message reaches A but not B | Distinct local views; B cannot distinguish it from non-delivery unless another modeled event informs B. |
| One extra undelivered event | No new information, event count, or clock tick for an uninformed principal. |
| Inclusion of an existing message | The scheduler publishes it without obtaining another action from the sender. |
| Public malformed or duplicate input | Still a possible controller action; execution produces the specified failure and observations. |
| Failed/reverted execution after delivery | The recipient retains what it learned despite unchanged application state. |
| Two messages with different inclusion orders | Both operational traces exist and expose exactly their declared local effects. |
| One actor controls player and builder capabilities | A single principal deviation can change both. |
| A run reaches the test horizon without settlement | The result remains pending, not source quitting or successful completion. |

Compare the operational model and adapter on these executions. Finite testing
fuel must not create a fictional observed terminal event. Application-specific
tests enter with their corresponding layers, rather than expanding the first
pool carrier with unused capabilities.

The first commitment experiment must also admit cleartext submission and
show that inspecting it can reveal a protected value. For compiled traffic,
prove prefix observation equivalence under an explicit ideal service, accepted
opening consistency, and successful opening traces for distinct values.
No forced opening or settlement guarantee follows from these properties.

**Gate**

Executable traces, observation/noninterference lemmas, and a derived game form
all describe this same model. The adapter does not reduce the native adversary
space to satisfy its typing requirements. This gate does not claim source
preservation or a complete ledger.

## R2. Compile a checked core program into that model

**Implemented execution and bounded hiding slices; gate still open**

`SealedFragment.compile` emits a homogeneous unrestricted-commit/reveal
application from actual graph metadata. `SealedFragment.step_refines` and
`run_refines` cover every finite raw native action sequence, and
`WFProgram.sealed_run_source` reconstructs a written-order source execution
with matching terminal bindings and decoded payout evaluation whenever its
decoded graph prefix is terminal.
The `PendingSource`/`PendingExecution` fixtures exercise this compiler path,
including nullable values, opaque pending traffic, graph-derived opening
barriers, and both commitment inclusion orders.
`PendingOutcome` checks completed graph outcomes against native execution for
every nullable input pair and instantiates the terminal source-execution theorem.
The executable fixture uses checked elaboration-time
specialization of the source compiler; a standalone extracted emitter remains
an additional implementation obligation.

`PendingReplay` exercises unchanged-envelope rebroadcast by another player,
duplicate inclusion, and a rejected opening that becomes valid after its
prerequisites complete. Native run refinement covers these actions.
At-most-once application execution holds independently of traffic duplication;
it does not erase the extra public traffic or promise cross-instance isolation.

The bounded policy interface supplies principal-scoped controls and polling
memories over this runner. Its two explicit-rebroadcast capability selections
have an exact-law embedding, and its ideal pre-disclosure hiding theorem
permits adaptive opponent and wire-observing environment policies. The finite
invocation list remains fixed. `PendingPolicies` handles continuations without
owner invocations and retains a distinguishing cleartext response.
`PendingRelease` includes the owner's register/submit/open controller from
empty and permits further owner invocations. It compares the first public
release-enabled snapshot of each full native trace; execution continues after
that snapshot. The generic compiled-controller theorem checks all graph
prerequisites before submitting an opening. The release readout is not a
different stopped runtime or conditioning on successful release.
`WFProgram.sealed_policy_source` transports native source-support correctness
to every supported policy-game execution.

`PendingChoiceLock` identifies the opponent's extracted release-time value
with its compiled source field, proves its law independent of the honest
input, and carries that value through later execution and any accepted
opening. Unreached release remains a separate outcome marker.
`PendingWithholdingSource` proves a concrete publication-law obstruction
against every independent source profile: the bound opponent can selectively
withhold after learning the honest opening, while every terminal source result
contains its public binding. A canonical-controller continuation succeeds at
the same reached prefix and service horizon. This is an obstruction for the
specified publication readout, not a universal failure of weaker comparisons.

These comparisons do not complete the gate. The next compiler theorem must
compare unilateral replacements with source policies across the whole
interaction, including post-release behavior, and
account for withheld openings and observable failure. The untimed sealed-message
application has no timeout transition; its timed extension below does not
convert pending execution to source quitting.
General asynchronous activation and player-owned network/builder capabilities
also remain outside the fixed-invocation instance; the precise scope is in
the [runtime inventory](runtime-models.md).

The [timeout compilation design](timeout-compilation.md) specifies the next
component integration. A checked dependency gate exposes the shared mutable
timer's within-call interference and proves progress for immutable deadlines.
Atomic inclusion preserves public messages and prior deliveries when the
application rejects. `SealedTimeout` integrates the original sealed-message
validator with a permissionless expiration call at one named disclosure
checkpoint, a public monotone clock, receipts, and a native bounded policy
game. Its chosen failure policy stops further protocol-event acceptance; it neither assigns
a source value nor implements the richer source's persistent role-specific
abandonment and handler semantics. This real runtime instance still needs
the source-resolution and whole-interaction strategic comparisons.

`WFProgram.sealed_timeout_run_source` and `sealed_timeout_policy_source`
extend the reachable-prefix/source-support result over timed native execution
and its policy game. Terminal decoded graph prefixes reconstruct source
bindings and payout evaluation; checkpoint completion or expiration alone
does not imply source termination. These theorems do not erase the extra
information in traffic, receipts, or clock observations.

Before a terminal-law claim, implement and analyze resolution rather than
defaulting unfinished traces to source values in a readout. Preserve the
already-bound choice and distinguish later withholding from an earlier
nullable decline. Choose a source/backend eligibility condition or weaker
strategic comparison that accounts for that difference; adding a deadline
alone does not prove its adequacy. Utility-dependent quitting conditions and
explicit source continuation choices are candidate proof routes, with distinct
claims. Neither requires extending the minimal source syntax speculatively.

The persistent-quitting source gate has an executable two-checkpoint probe:
existing guards eliminate later freedom, and `PublicForcedChoice` proves that
a publicly determined source choice can be selected without consulting its
owner's current policy. The actual written-order source law is checked in
`PersistentDisclosureSource`, including arbitrary whole-program profiles.
This does not complete runtime resolution. `CommitmentAccounting` admits the
retained binding through its certified conditional-publication site. The
remaining obligations are owner-independent execution of forced steps with
correct observations and a runtime codec preserving the same-owner typed
binding. Accounting alone supplies neither mechanism.

The conditional-publication compiler component supplies the local resolution
edge: generated metadata, source/validator correspondence in both directions,
and execution by the actual paired graph kernels. It still needs integration
into the whole public application and its controllers. The next strategic
gate includes the prefix establishing the original binding, all subsequent
player choices, persistent quitting, and settlement under the stated services;
starting a proof at an already represented disclosure checkpoint does not
complete that gate.

`MessageApplication` supplies the common receipt-bearing execution and
observation-local policy boundary, with fixed application chance kernels.
The timed sealed instance has exact state/action/observation/run correspondence,
and its shared policy game retains checked source-prefix support. A separately
specified lottery exercises the same machinery without Vegas imports. These
clients establish runtime reuse, not the full non-Vegas strategic comparison
required by R3.

Integrate conditional publication and source continuation through this shared
application boundary. Do not add a separate optional-disclosure runner or
policy evaluator. Chance triggers must invoke the source's fixed law, check
readiness, and prevent rerolling; environment control of their timing does not
give it control of their sampled value. For every potentially silent source
decision, supply an executable legal fallback or preserve unresolved execution.
Uniqueness of a legal action is sufficient for one resolution technique, not a
necessary condition for implementing a designated fallback.
The emitted controller must check disclosure fences before submitting an
opening, not only before its application effect is accepted: recipient delivery
can reveal the payload before inclusion. Retain the actual clock, receipts,
and local message histories in the policy game while proving the comparison.

Choose a finite checked core program with two real players, source-defined
nonresponse outcomes, and a later decision that can expose an information
mistake. The pending-commitment experiment motivates a sealed-choice slice:
public handles precede source-authorized disclosure, and opening packets carry
their claimed values while pending. Choose the exact admitted source program
before adding a general protocol/phase language; the independent one-slot
experiment is not such a program and does not discharge this gate.

Prove the release discipline from the emitted controller and application.
Source textual order alone does not imply that both parties' choices become
irrevocable before either opening packet can be observed. An owner/slot binding
check must reject handles used for a different owner/node and replacement after
acceptance, while raw copying and malformed submissions remain possible. A
rebroadcast retaining its original author and context need not be rejected
before its first successful execution. Private registration with
an ideal service is explicit; unrestricted access to its hidden table or
verification oracle is not an admitted opponent capability. Concrete
cryptographic realization is a further compiler edge, not part of this slice.

Provide an actual `WFProgram` term using the existing constructors. Represent
nonresponse by a designated legal source value with explicit continuation and
payout semantics, for example `none` in an optional choice whose legality is
proved. The minimal core has no timeout constructor; the interface's timeout
action must select that value, not manufacture a new source branch.

Keep the concrete emitted controller and application transition available for
execution. Prove their connection to the independent source game, not merely
to a new hand-defined runtime-aware game. Any graph-level example that does not
satisfy core admission must be labeled as such and cannot discharge this gate.

Use a named service instance, with nonzero delivery delay and at least two
admissible inclusion orders. A zero-cost instance is acceptable if explicit.
Give source timeout resolution a real transition and controller/driver. The
service assumptions must be feasible and must hold under all deviations in
the statement, including allowed spam and late submissions.

The first positive instance uses disjoint player and external builder/network
principals; fix that ownership map in its theorem. R1's combined-capability
test does not make this theorem cover player-owned builders. Use explicit
per-principal resource budgets and reserved service capacity for the initial
bounded inclusion instance. Define how over-quota traffic is rejected or
charged; it must not consume another principal's promised capacity silently.
These are model assumptions, not claims about Ethereum's service guarantees.

Prove settlement within the chosen bound for every admitted unilateral player
replacement and fixed adaptive environment satisfying the service contract.
Account for invisible withhold/wait events in the bound, not just successful
application steps. If this cannot be proved, the endpoint remains a
prefix/pending theorem and cannot be presented as an unconditional terminal law.

**Proof obligations**

1. The compiler's emitted requests and controller actions are executable and
   information-local; the controller uses no hidden scheduler state.
2. Actual application execution and decoding agree with the source outcome
   interpretation on completed runs.
3. Compiled-profile law correspondence holds under the stated services.
4. Analyze all target unilateral replacements at the same fixed environment
   policy, retaining other compiled principals. Prove a uniform translation,
   a precisely scoped mixture/quantitative statement, or a concrete obstruction.
5. Derive the corresponding source-outcome bound and equilibrium consequence
   only when the established relation supports them.

Include deliberate failure controls: censor a valid request past its cutoff;
expose information before another relevant choice is fixed; change a fee while
holding decoded settlement constant. State which guarantee each behavior
refutes and which assumption excludes it in the positive instance. Do not
assume that every negative control refutes every solution concept.

**Gate**

One actual core-to-public-message compiler path has checked strategic evidence,
with full controller quantifiers for the property claimed. If exact law or
Nash preservation fails, record the necessary condition or weaker result.
Do not replace the source meaning or declare all failures equivalent to quit.
If the only result is an obstruction, choose and test a revised service
discipline, supported fragment, or useful weaker property in the same model.
Positive compiler composition and generalization in R3/R4 require an actual
proved comparison; a negative result does not supply that premise. Independent
runtime reuse can still proceed from R1.

## R3. Validate composition, extensibility, and independent reuse

Insert one useful intermediate representation in the working R2 path, such as
raw-envelope validation or an explicit inclusion/receipt layer. Do not create
a dummy wrapper solely to count a layer.

Prove both adjacent edges and recover the original end-to-end statement using
the relevant composition results. Check equality or semantic correspondence
of the final artifact, not just matching theorem types. Include one test in
which exposing new receipt information defeats an overly strong abstraction.
The gate names the exact comparison recovered; finite mixtures cannot stand
in for a uniform translator or a continuation/recommendation correspondence.

Build a second, directly specified non-Vegas protocol using the same runtime
and game adapter, for example a two-party escrow/release protocol with
competing requests. Prove an operational invariant and a strategic comparison
with the same generic machinery. It must compile without importing Vegas.

Enforce the exercised library boundaries in the import checker:

- no Vegas or ledger/VM dependencies in GameTheory;
- no Vegas or EVM dependencies in generic interaction/ledger semantics;
- no game-core dependencies in game-free runtime modules;
- no compiler imports in target-carrier definitions;
- no audit/test imports into production roots.

**Gate**

The new layer composes without rewriting unrelated semantic owners; the
non-Vegas client proves actual reuse. Add physical library targets only for
the modules exercised by these clients. Do not create empty package trees.

## R4. Generalize the supported compiler and information discipline

Generalize the concrete R2 construction only along the dimensions its proof
uses. State core eligibility separately from source well-formedness. The
compiler may reject an unsupported target/fragment pairing without weakening
the programmer's source discipline.

Exercise hidden selection and later disclosure using explicit ideal services.
Before using existing quitting results, relate the service's real public
events, validation, and retry rights to the source decision. Commitments need
explicit handling of invalid openings, copying/related commitments, selective
opening, and payload-dependent extra traffic. Hiding alone is insufficient.

For guards over sealed information, establish implementable validation or
identify the supported fragment. Deferred validation requires the right
source consequences; it must not silently add an invalid-value outcome.
A proof-of-validity service is a separate assumption, not part of ordinary
commitment functionality by default.

Prove arbitrary supported-program statements through the public-message model.
Keep uniform backtranslation, profile-local mixtures, coalition/context
results, and continuation-sensitive results distinct. A finite-domain
counterexample is useful but is not a general completeness classification.

**Gate**

A checked core eligibility theorem, generated target, source-to-target
strategic theorem, and substantive application all use the same semantics.
The runtime may still have explicit ideal services; no deployment claim follows.

## R5. Reconnect contract and EVM lowering to the shared runtime

Extract runtime-neutral and VM-specific semantics from the existing backend
according to dependency, not directory name. Keep Vegas expression/code
compilation and its instances in the Vegas backend integration.

Instantiate the application-execution port with the existing contract
transition, including authentication, validation, rejection/rollback, and
observable results. Then connect storage and wire encodings, oracle interaction,
and a complete generated-handler path to that same target. A single-invocation
contract interface is not a message-pool or ledger model.
Use the existing transition as the port definition or prove a direct
transition-law equivalence if representation requires an adapter; do not add
an independently maintained contract evaluator for the strategic proof.

Whole-handler simulation and independent validation of the EVM model remain
explicit requirements. Existing local instruction proofs can be reused but do
not discharge either automatically. Introduce gas, transfers, external calls,
and other effects as real observations/outcomes when claimed. Rerun strategic
comparisons rather than inheriting them from a state projection.

**Gate**

At least one generated path is related to the public-message execution and its
derived game. The public theorem lists remaining VM/service/crypto assumptions.
A later whole-backend result extends that same path, not a separate tower.

## R6. Add chain realization and quantitative/unbounded analyses

Add named ledger, dissemination, consensus/finality, and cryptographic
realizations as actual clients of the runtime interfaces. Intermediate layers
can be inserted wherever a proof needs them; the tower has no fixed level enum.

Retain observations across reorgs and distinguish dissemination, inclusion,
execution, and confirmation. Account for who can force or prevent a timeout
call and for the resources funding its inclusion. Arbitrary outside contracts
or shared principal roles require the corresponding context/deviation scope.

For probabilistic service failure, compare unconditional laws and derive
explicit utility/error budgets. Do not condition away adversarially selected
failures. Computational security requires a security parameter and efficient
adversaries/tests; do not identify it with exact equality or total variation.

Prefix results remain meaningful without termination. Infinite-path
probability, eventual settlement, and utilities of unresolved runs require
their own semantics and proofs. These are later extensions, not hidden
premises of the finite model.

**Gate**

Each additional result identifies the operational realization and discharges
or narrows an existing requirement. A complete Ethereum model can eventually
instantiate these interfaces only after proving its control, information,
execution, and service correspondence.

## Frontend and manuscript work

Kotlin owns the rich surface language and its handler elaboration. The
[frontend/core contract](compiler-boundary.md) specifies its separate checked
integration boundary. Frontend integration may proceed independently; it is
not a prerequisite to modeling public delivery of an already checked core
program.

Keep the paper written as one coherent account of the current results.
Synchronize formal endpoints, audit statements/pins, registry, and prose when
a result changes. Planned stages are never included in the proved tower.
Do not expand the paper with every architectural helper or elementary witness.

## Verification and handoff at every gate

- Run narrow Lean targets during development and the full default build with
  warnings treated as errors at integration.
- Keep axioms pinned for public claims; no placeholders or local option escapes.
- Run import/direction/cycle, source-option, documentation, and claim checks.
- Maintain executable positive/negative controls alongside general theorems.
- State what changed, the precise checked result, remaining requirements, and
  the next bounded task. Do not mark a gate complete for a conditional theorem
  whose advertised premises have not been supplied by the intended instance.
- Commit and push relevant repositories independently; do not mix generated
  manuscript artifacts or unrelated working-tree changes into commits.
