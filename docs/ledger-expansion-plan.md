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
| Independent source meaning | Source-to-graph connection, terminal native support, and an exact completion/public-outcome law for every eligible application plan under arbitrary source profiles and the generated reference service | The actual supported source's choices, information, nonresponse consequences, and outcomes are the comparison endpoint. |
| Source coverage | Structural binding/chance/public-choice/conditional-publication compilation, arbitrary-traffic support refinement, whole-source strategy lifting and reference execution, with explicit initial-read and binding-origin eligibility | General supported finite typed programs with guards, chance, and multistage dependencies; implementation conditions are explicit and exercised. |
| Hostile interaction | Raw traffic, local delivery, replay, addressed public inclusion, ideal binding/hiding; initialized disclosure settlement against arbitrary opposing policies under the stated slotted service | Whole interaction, failure, deadline and observation behavior under the theorem's complete player/environment policy classes. |
| Strategic comparison | Release-time hiding/choice independence and selective-publication obstruction | Compiled-profile law plus arbitrary unilateral-deviation comparison, with the corresponding source-outcome bounds and equilibrium results. |
| Substantive application | The private-window sealed offer and a public-message compiled-prefix fixture | The generated protocol application and handlers use the same public-message compiler path; reference strategies and their guarantees are related separately. |
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

The compiled artifact tower consists of protocol representations: graphs,
public-message applications, contracts, wire formats, and target code. Lifting a
source profile constructs reference runtime strategies for proofs in parallel
with that tower. It neither emits client software nor removes arbitrary native
policies from the deviation space.

The first delivery is a public-message model with recipient-local observations,
a real core-to-model compiler slice, and checked strategic evidence about that
execution. A weaker positive result or a precise obstruction is acceptable
evidence at a research gate. A disconnected runtime, a restated preservation
hypothesis, or a trace example alone is not completion.

### Whole-program forward-law checkpoint

`ApplicationPlan.service_source_public_law` relates the independent source
denotation to the shared application's completion and public terminal readout
for every eligible `ApplicationPlan`. Its proof-side `ForwardCheckpoint` carries:

- The original plan/profile's `ProfileContinuation` to the current suffix.
- The exact source/graph prefix (`CoupledAt`) and native `State.Refines`.
- Support in an initialized run under the same original lifted profile.
- Alignment of the service's actual environment-history length with the
  unexecuted emitted-instruction suffix.
- `RemainingCachesEmpty` for the unexecuted suffix.
- `AcceptedBindingPrefix`: canonical accepted handles for every generated
  binding before the current source prefix.

The initialized-run witness supplies message-identifier freshness, memory
coverage, registration consistency, and typed registration provenance; these
are derived rather than stored again in the checkpoint. Static binding
origins locate an earlier binding for each conditional; the dynamic accepted
prefix supplies its handle. The checked snapshot bridge then recovers the
source value without a separate evolving snapshot-value invariant.

The chance, binding, public-choice, and conditional head theorems preserve this
checkpoint on every supported successor. Structural induction composes them
with the existing `denoteSource` equations and the shared runner's append/bind
laws. The result compares the joint `(finished, readPublicTerminal?)` law with
the source law mapped to `(true, some public outcome)`. `readPublicTerminal?`
alone remains only a field reader; `CoupledAt.finished_public_readout` supplies
both termination and the exact public projection. Sealed source values remain
proof witnesses and are not decoded from public runtime memory.

The entry theorem assumes `InitialControllerReadsPublic`: only source-initial
fields in generated player-controller footprints must be public. This is a
backend condition, not source well-formedness, and does not provision sealed
initial inputs. It also assumes `HasBindingOrigins`, because a conditional
endpoint needs an actual earlier generated binding; an ordinary public write
does not synthesize a commitment handle.

`ApplicationImage.serialService` and `serviceInvocations` supply a concrete
source-ordered reference service on the shared runner. The service indexes
emitted instructions by its own environment-history length. It invokes chance
at sample heads and otherwise includes the instruction owner's most recent
submission if it remains pending, without inspecting payload contents. Its exact
post-submission command and history-count laws are checked. The forward proof
establishes their premises from empty environment history and the image-derived
invocation list while retaining the same original lifted source profile.

This finite service advances its index even after a wait or rejected request;
it is not a fairness, retry, or withholding-resolution mechanism. Those need a
separate service and its proof, rather than additional invocation steps silently
inserted into this exact script.
Arbitrary environments retain the safety guarantees for runs that finish;
they do not imply completion or equality with the terminating source law.

### Resolution and open deviations

`ApplicationPlan.withholding_no_source_public_law` establishes a code-level
obstruction to upgrading the reference law by service assumptions alone.
Generated binding and ordinary-public-choice nodes require an owner-authored
message. Replacing that owner by permanent waiting leaves the program unfinished
under every environment policy and finite invocation schedule. The theorem
retains completion in the outcome; it does not rule out weaker observations or
an extended implementation with genuine source-certified fallbacks.

Conditional publication already supplies such an entry point.
`ConditionalPublicationSite.expiry_include_source_coupling` relates an actual
included, overdue expiry packet from any sender to the existing source decline
and exact source continuation. The packet must actually be submitted: the
environment's inclusion capability cannot author it.

The implementation order is:

1. Generate fallback metadata for a supported binding/public-choice slice from
   an explicit source-resolution certificate. `Legal` provides some legal
   action, not the programmer's specified nonresponse consequence. Keep this
   certificate and backend eligibility separate from core syntax and WF.
2. Represent an accepted opaque commitment and a public fallback as distinct
   dispositions. A fallback neither forges an owner's message nor overwrites
   its private preparation. Adapt opening verification and reference readout
   to the accepted disposition, including recovery from an unsubmitted cache.
3. Prove handler/source continuation for those fallbacks. Couple this with
   observation-local request production, a public clock, and admitted inclusion
   capacity. Specify who supplies permissionless transactions and what happens
   when a valid ordinary request competes with expiry.
4. Compare arbitrary player replacements on that same execution. Start with a
   final conditional disclosure under an actual resolving phase, then compose
   across prior bindings, chance, and later decisions. A support witness for
   each terminal result does not provide one legal source-policy law.

No point in this sequence restricts deviators to canonical payloads or lifted
policies. Unopenable bindings, malformed requests, replay, and silence must be
handled by the implementation and the comparison. The observation issue for
an opening delivered before a losing inclusion is recorded in
[timeout compilation](timeout-compilation.md#deviation-law-proof-targets).

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
`PendingRelease` supplies the owner's register/submit/open reference policy from
empty and permits further owner invocations. It compares the first public
release-enabled snapshot of each full native trace; execution continues after
that snapshot. The generic reference-policy theorem checks all graph
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
contains its public binding. A canonical reference-policy continuation succeeds
at
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
retained binding through its certified conditional-publication site. Generated
conditional instructions preserve its same-owner typed identity and validate
later openings against the retained snapshot and source guard. Owner-independent
execution of forced steps with correct observations and whole-program strategy
correspondence remain obligations beyond accounting and these local mechanisms.

The conditional-publication compiler component supplies the local resolution
edge: generated metadata, source/validator correspondence in both directions,
and execution by the actual paired graph kernels. Structural application plans
integrate these instructions, with arbitrary-traffic support refinement and
source public-outcome witnesses for completed executions. Structural source-profile
lifting supplies reference runtime strategies. Its exact randomized law under
the generated serial reference service now covers every eligible plan and source
profile, including completion and the public terminal readout. The next
strategic gate still compares arbitrary target deviations under the stated
service class; the reference law alone does not discharge that comparison.

Conditional endpoint generation is independent of the original binding's
accounting discharge. `ConditionalPublicationSite` combines an adjacent
public-choice occurrence with its opening-or-decline certificate;
`ApplicationPlan.conditionalCopy` uses it for an ordinarily accounted later
copy. The native update preserves the original accepted handle and frozen
snapshot. `GeneratedPersistentDisclosure` supplies the ten-node derivation,
an exact opening execution law from empty-pool initialization, a check that
decline blocks later opening, and completed-run source public-outcome witnesses.
`ApplicationImageReadout` reconstructs the full declared choice footprint from
public memory and private registration history. Its graph/source correspondence
requires cached originals to match their accepted snapshots; compiled source
occurrences supply the typed field metadata. Earlier paired choices come from
their resolved public values, not cached attempted requests: an opening overtaken
by expiration can leave an intended `some value` in history while the accepted
transaction represents `none`.

`GeneratedPersistentDisclosureController` instantiates that readout and the
conditional reference-policy combinator at the second site. The local laws
recover the arbitrary randomized source decision at the concrete opened and declined native
checkpoints, under the original-registration and empty-second-cache premises.
They also check endpoint separation and waiting after a recorded second choice.
These local laws take supplied histories; the separate forward-checkpoint
induction establishes their histories and checkpoints in the generated serial
reference run.

The forward composition establishes private registration before binding
acceptance, then maintains cache/snapshot correspondence and availability of
every source-visible field. Acceptance of an unprepared handle followed by
registration remains permitted operationally and does not satisfy that
reference invariant.
`ApplicationImageRegistration` supplies the unconditional history/preparation
invariant and preservation of an already cached-and-bound snapshot under all
later policy commands. `BindingImageController` and `BindingImageExecution`
construct the two-phase reference policy and prove the full law of consecutive
registration and submission invocations. `ApplicationImageBindingInclusion`
connects actual recorded inclusion to the cached snapshot. The initialized
`GeneratedBindingPolicy` prefix has the exact arbitrary randomized source
snapshot law and a draw-independent environment observation under its specified
inclusion script. `ApplicationPlan.liftProfile` supplies structural source-order
dispatch in the full image, and `ApplicationPolicyLocality` proves coordinatewise
dependence on source policies. `GeneratedApplicationPolicy` composes the binding,
the forced marker, and chance under that same lifted whole-source profile, with
successful inclusions and an exact six-invocation joint law. These are reference
strategies for the open protocol, not generated player software.
`ApplicationPolicyProvenance` establishes the cache/snapshot component generally:
if one player follows the lift, every
accepted handle belonging to it retains its first private registration, under
arbitrary opponents, environment, and finite invocation list. It also supplies
cache existence and graph-field type agreement for accepted bindings.
`ApplicationImageCoverage` proves that completed event fields have stored data
or accepted canonical handles under arbitrary policies. `SourceReadoutAvailability`
combines these execution invariants with native refinement and graph readiness:
the lifted owner can load the complete choice footprint, provided its initial
fields are public. The loader receives no source environment. Sealed initial-input
provisioning remains separate. The forward checkpoint supplies the proof-only
source environment whose view the readout reconstructs, while policies still
receive only native histories and observations.

The exact-law induction uses `ApplicationPlan.ForwardCheckpoint`, retaining the
original plan/profile, its structural suffix, `CoupledAt`, native refinement,
membership in the actual initialized policy run, service-index alignment,
remaining-cache freshness, and the accepted-binding prefix. Coverage, typed
registration provenance, and fresh envelope identifiers follow from run
membership rather than becoming inputs to a second evaluator.
`ApplicationSampleExecution` supplies the source-coupled native chance phase.
`PublicChoiceImageExecution` supplies the source-kernel submission/inclusion law,
and `PublicChoiceSourceCoupling` advances the exact source continuation through
the actual public-choice handler. `BindingSourceCoupling` and
`ConditionalSourceCoupling` supply the corresponding actual-inclusion continuations:
a prepared binding adds its chosen source value, and an opening or decline adds
the chosen optional value and its publication. Readiness follows from the
completed source prefix. The conditional endpoint additionally needs an accepted
binding identity; only opening needs a recoverable frozen value.

`ApplicationBindingOrigins` gives a decidable metadata condition for those
identities: each commitment-backed conditional instruction has an earlier
binding with the matching field, owner, and slot. This is not enforced by the
`ApplicationPlan` index and does not imply that the earlier binding was included.
In particular, publishing a source field through `publicChoice` does not create
a commitment handle. The reference realization theorem therefore consumes a
binding-origin certificate; another backend could instead select a different
representation for already-public values. This is a backend condition, not a
source-WF restriction.
`PublicConditionalOrigin` checks the distinction on a valid source and generated
plan, not just a hand-written image: the first public inclusion stores the value,
but the later commitment-backed endpoint has no accepted handle.

`ApplicationPhaseCaches` lifts codec separation through each full phase;
`ProfileContinuation` keeps the original lifted profile installed while moving
to its `afterSample`, `afterCommit`, and `afterReveal` suffixes. The binding,
public-choice, and conditional phase laws join source kernels to actual
submission and inclusion on complete policy executions. Structural induction
then derives the joint terminal distribution, rather than merely collecting
unrelated per-phase support witnesses.

What remains is the strategic edge: compare arbitrary player replacements and
admitted adaptive environment policies against this reference execution, using
the same opponents and external policy on both sides. The serial witness is not
a fairness contract and does not resolve withholding, retries, or competing
expiry under deviations.

The checked forward theorem uses a serial service under which a competing
expiration does not resolve an endpoint before its chosen owner request is
included. Clock advancement alone
does not reject an opening: the handler accepts it after the deadline if the
endpoint remains unresolved. Arbitrary withholding and resolution service need
their own whole-interaction argument; the forward service script must not be
presented as covering those deviations. Initially sealed owner-visible inputs
also require provisioning beyond the current public-only initializer.

Ordinary adjacent choice/reveal sites have a corresponding local component:
`PublicChoiceSite` derives metadata and guard code from `SourceDecisionSite`,
and the shared `PublicChoice` endpoint performs authentication, readiness, and
validation. The disclosure response handler directly instantiates it, with
checked local source steps and equality of the decoded native and graph
updates. Validation uses only actual guard dependencies, whose publicness and
native store agreement are separate obligations. `PublicChoiceSite.controller`,
used by the proof-level strategy lift, adapts arbitrary source decision kernels
to a shared sample-once controller, with an exact first-submission law at matching
source observations. Its first
real submission records the draw in own command history; subsequent polls can
wait or retry that value. Disclosure's reference native responder policy uses
this component, and its first ready invocation records the source response law. The existing
deterministic settlement guarantees remain checked specializations.
The shared sample-once mechanism also handles private registration commands.
Choice encodings enforce canonicality; endpoint tags separately establish
disjoint decoding and dispatch. `ConditionalOpeningController` composes the
certified source value equivalence with addressed opening/decline requests and
proves their local source law and acceptance conditions. The concrete disclosure
reference owner strategy composes source-profile-derived private registration,
opaque binding submission, and this addressed opening policy. It retains the
initial value in its own
command history, reconstructs the opening view from that cache or an accepted
public default, and reconstructs the complete declared source view. Native routing admits
wrong-tag raw messages and rejects their application effect. The complete pure
benchmark and initialized service proofs use this assembly, with all three
strategic kernels projected from the written source profile.
The application-plan forward theorem supplies the randomized reference-profile
law under `serialService`. The public-runtime strategic comparison remains open:
that law does not establish intermediate-observation equivalence for arbitrary
target deviations.

Generated chance instructions use the exact `EventDist.eval` kernel, with an
address-only environment command and no reroll after completion. This assumes
ideal unbiased entropy, to be realized by a separate target edge.
Conditional endpoints are certified independently of whether a site performs
the unique accounting discharge. Their private guard dependencies prevent
treating later optional copies as ordinary publicly validated choices. The
persistent-disclosure instance exercises the generated repeated endpoints and
whole-run support invariant. When its initial-read and binding-origin
certificates are supplied, the general forward theorem covers its structurally
lifted randomized profile through both disclosure sites.
Initial sealed-input provisioning/defaults and automatic execution of publicly
forced choices remain additional gates, not assumptions supplied by accounting.

`MessageApplication` supplies the common receipt-bearing execution and
observation-local policy boundary, with fixed application chance kernels.
The timed sealed instance has exact state/action/observation/run correspondence,
and its shared policy game retains checked source-prefix support. A separately
specified lottery exercises the same machinery without Vegas imports. These
clients establish runtime reuse, not the full non-Vegas strategic comparison
required by R3.

Policy execution must have one implementation per operational carrier.
`SealedPolicies` and `SealedTimeoutPolicies` still implement their own policy
runners alongside `MessageApplicationPolicies`. The timed native bridge is
exact but does not yet transport policy histories and games. Consolidate that
layer through checked policy transport before extending it; for the untimed
model, account explicitly for its weaker receipt observations. A native-run
correspondence alone does not justify equating these policy games.

Integrate conditional publication and source continuation through this shared
application boundary. Do not add a separate optional-disclosure runner or
policy evaluator. Chance triggers must invoke the source's fixed law, check
readiness, and prevent rerolling; environment control of their timing does not
give it control of their sampled value. For every potentially silent source
decision, supply an executable legal fallback or preserve unresolved execution.
Uniqueness of a legal action is sufficient for one resolution technique, not a
necessary condition for implementing a designated fallback.
The lifted reference strategy must check disclosure fences before submitting an
opening, not only before its application effect is accepted: recipient delivery
can reveal the payload before inclusion. Retain the actual clock, receipts,
and local message histories in the policy game while proving the comparison.

The concrete `DisclosureApplication` specialization exercises these stages
through the shared runner, with an armed publication window and a continuation
after decline or expiry. Its all-policy invariant gives reachable decoded
prefixes, exact completion flags, and written-source support for completed
outcomes. The complete run from empty also has the independent AST's exact
terminal-environment law for pure source rules and a specified inclusion
script, with the retained secret included in the readout. This proves
settlement for those scripted compiled runs, not under arbitrary native policies
or service policies. Initial and response nonparticipation have source-correct
permissionless expiration handlers, with complete native execution laws for
an absent owner and an absent responder. Initial expiration records a public
default without changing private preparation. Concrete pure reference policies
drive these expirations and recover from public defaults. The slotted service
admits
player reactions after delivery and before inclusion, and its capacity theorem
drains the pool under arbitrary player policies. Under this service and a
positive window, initialized settlement and exact unchanged-player choices are
checked with either deterministic reference policy unchanged. This meets
the [operational integration gate](compilation-design.md#disclosure-integration-exit-gate).
Generate the public protocol application from checked programs and separately
construct and relate reference strategy lifts, keeping disclosure as a regression
instance. Randomized source-profile laws and
unilateral-deviation simulation belong at that reusable compilation edge and
remain unproved for the public service. The
[initial-default design](timeout-compilation.md#initial-defaults-and-privately-prepared-commitments)
separates unsubmitted private preparation, accepted binding, public defaults,
and permanently unopenable commitments. The instance accepts unopenable handles
without a validity signal and freezes their verifier at inclusion. Arbitrary
native continuations cannot repair them; a checked failed-opening/expiration
execution reaches the responder and retains the failed traffic. Creation-time
cryptographic binding remains a realization obligation. The whole-interaction
strategic comparison is still required to complete the strategic gate.

Choose a finite checked core program with two real players, source-defined
nonresponse outcomes, and a later decision that can expose an information
mistake. The pending-commitment experiment motivates a sealed-choice slice:
public handles precede source-authorized disclosure, and opening packets carry
their claimed values while pending. Choose the exact admitted source program
before adding a general protocol/phase language; the independent one-slot
experiment is not such a program and does not discharge this gate.

Prove the release discipline from the reference strategy and generated protocol
application.
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

Keep the concrete reference policy and generated application transition
available for execution. Prove their connection to the independent source game, not merely
to a new hand-defined runtime-aware game. Any graph-level example that does not
satisfy core admission must be labeled as such and cannot discharge this gate.

Use a named service instance, with nonzero delivery delay and at least two
admissible inclusion orders. A zero-cost instance is acceptable if explicit.
Give source timeout resolution a real transition and a reference policy or
environment driver. The
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

1. The lifted reference strategy's requests and actions are executable and
   information-local; the strategy uses no hidden scheduler state. This is a
   proof obligation for the lift, not a claim that it is emitted client software.
2. Actual application execution and decoding agree with the source outcome
   interpretation on completed runs.
3. Extend the checked compiled-profile law under `serialService` only when a
   broader stated service supplies the required progress and resolution facts.
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
with full native-policy quantifiers for the property claimed. If exact law or
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
