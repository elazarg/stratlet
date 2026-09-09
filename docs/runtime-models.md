# Request windows, public scheduling, and pending messages

The [compilation design](compilation-design.md) requires native operational and
strategic semantics at each stage. This document records the existing models,
not a completed path to blockchain execution. The public-delivery expansion is specified in
[ledger-expansion-design.md](ledger-expansion-design.md), with implementation
gates in [ledger-expansion-plan.md](ledger-expansion-plan.md). These are plans;
they do not change the proved boundary below.
The [compiler boundary](compiler-boundary.md) keeps rich Kotlin lowering
separate from the minimal core and identifies the optional-disclosure encoding
as the first integration step, not an already proved frontend theorem.
The [quitting compilation contract](quitting-compilation-contract.md) specifies
how runtime failure accounting must preserve that existing source meaning.

## Mechanized composition

`Vegas/Scheduled/Request.lean` combines private request windows with the actual
compiled public serializer, for every finite-domain checked core program and
legal request interface.

`Machine.Program.serializedRequestInterface` automatically lifts an original
source request interface: player validators, timeout actions, and bounds use
the order-erased source information, while controllers may use the added log.

Within each round, every active player resolves a private, nonempty bounded
window. Accepted requests select source-menu actions; exhaustion selects the
source-designated timeout action. After all windows resolve, the serializer
applies the legal frontier in its chosen order and closes internal work. The
scheduler may use prior public game data and orders, but not the current private
attempts or their resolved values. Players retain their own complete request
histories and the serializer's public order observations.

The theorem quantifies over every behavioral public-data scheduler. Its policy
is compiled through the request interface using immediately accepted requests;
the scheduler cannot cause a timeout. Only original-player deviations are tested.
No scheduler utility assumption, scheduler equilibrium, or incentive condition
on the source's timeout actions is required.

The composition proves honest terminal-configuration laws, finite-mixture
backtranslation of unilateral deviations against unchanged opponents, and
preservation/reflection of player Nash and same-error approximate Nash. The
intermediate request certificate also preserves the complete serialized history,
including published orders. The final comparison with the atomic source erases
orders and compares terminal configurations, not complete atomic execution traces.

## Public scheduling of delivery and deadlines: unproved

The preceding model does **not** model a scheduler operating inside a request
window. In particular, it does not cover:

- observing pending public requests, malformed packets, or submission timing;
- postponing or censoring an otherwise valid request;
- deciding which requests are included before a deadline;
- revealing another player's request or acceptance while a choice remains open;
- transaction fees, deadline-dependent costs, or nontermination.

These are not extra restrictions to assume about every blockchain. They describe
the boundary of the mechanized target. Applying the theorem to a concrete
runtime requires proving that its admitted behaviors realize this boundary, or
proving a different theorem for the additional behaviors.

### Native pending-message experiment

`Interaction/MessagePool.lean` supplies an independent executable kernel with
sender-local message identifiers, a pending inventory, recipient-local
delivery, and a shared published ledger. Any observer may receive any pending
message. Inclusion selects a preexisting message and never invokes its sender.
The kernel proves that delivery to another observer leaves a local view
unchanged and that inclusion preserves previously received information.

`InteractionTests/Pending.lean` derives a bounded two-player game from those
same operations and checks both inclusion orders and the responder's exact
local-policy law. Its environment is a fixed delivery/order choice, not the
full adaptive scheduling model. The compiler slice below uses this same kernel.

The separate `IdealCommitments` service provides privately registered,
owner/slot-scoped write-once values. `InteractionTests/Commitment.lean` checks
that pre-opening wire states are independent of the registered bit, while
legal cleartext states are distinguishable. Continuations in this experiment
receive only the wire pool, not the ideal table. A sender-checking handler
rejects guessed openings submitted through the opponent's native capability.
Accepted claims match
the stored value, and both values have successful opening executions.

Opening messages carry their claimed values: their pending delivery already
distinguishes the values, before ledger inclusion. Thus the hiding statement
ends at disclosure, not at inclusion. These tests do not establish an opening
barrier, liveness, quitting correspondence, cryptographic security, or source
equilibrium preservation. They introduce no private-message assumption on the
pool; private registration is an explicit ideal-service assumption.

### Sealed-message compiler slice

`Vegas/Compile/SealedMessages.lean` compiles a certified event-graph fragment
to executable `Interaction.SealedProgram` rules. The fragment has a common
value type, unrestricted commitment guards with no reads, and reveals of
commitment-produced fields; samples are excluded. The emitted rules retain
the graph's owners, producer indices, and prerequisites. Eligibility is a
separate backend certificate and leaves core well-formedness unchanged.

The native runner admits private registration, arbitrary raw submission,
recipient-local delivery, replay of observed messages, and inclusion.
Cleartext, malformed, duplicate, and
premature opening messages remain possible; rejected messages remain in the
public ledger. The honest opening controller uses only public application
events and the owner's supplied value. It checks the graph-derived release
prerequisites before emitting the value-bearing opening packet.

`SealedFragment.step_refines` proves that each native action either leaves
the decoded graph configuration unchanged or executes an available primitive
graph event. `SealedFragment.run_refines` consequently decodes every finite
native run from the empty runtime state to a reachable graph prefix, without
a fairness or termination premise. The proof-side decoder reads the private
ideal table; runtime observations do not expose that decoder.

`WFProgram.sealed_run_source` in `Vegas/Compile/SealedSource.lean` composes
this result with the existing source compiler theorem. If the decoded graph
prefix is terminal, it reconstructs an actual written-order execution of the
original checked source with matching terminal bindings and payout evaluation.
This is end-to-end support-level correctness, not equality of policy-induced laws.

`VegasTests/PendingSource.lean` is an actual checked nullable-choice core
program compiled through that path. Its two independent commitments precede
two reveals, each depending on both commitments. `PendingExecution` exercises
local delivery before inclusion, both commitment orders, the opening
controller, and the difference between a stored source `none` and a missing
opening. Wire prefixes containing only compiled commitments are identical
across their registered values, while admitted cleartext traffic distinguishes
them. Arbitrary raw submissions can deliberately disclose values early; the
honest release discipline does not restrict those submissions.

`PendingOutcome` checks that every pair of nullable values, in either tested
commitment order, completes with the expected decoded graph bindings. It
obtains reachability from the generic native-run theorem, rather than treating
an arbitrary list of store writes as an execution. Its `honestRun_source`
theorem instantiates the end-to-end source correspondence for these transcripts,
including every terminal binding. The fixture specializes the
source compiler at Lean elaboration time and checks the resulting rule data
against that compiler; native evaluation tests exercise the executable runner.
This is a checked closed-program artifact, not an extracted standalone source
compiler.

The complete R2 gate remains open. The scoped bounded policy interface below
enforces the author/owner controls that the raw transition system leaves as
labels. Strategy compilation and unilateral deviation comparison for this
application, general asynchronous activation, timeout settlement, and
cryptographic realization remain separate obligations.
In particular, missing openings remain pending rather than becoming the
source value `none`. This slice adds no public-message equilibrium claim to
the manuscript's private-window/serialization theorem.

The application emits accepted commitment/opening events. The payout equality
above evaluates the compiled graph's readout on the decoded state; it does not
execute an asset transfer or a contract settlement routine.

### Bounded policy game

`Interaction/SealedPolicies.lean` interprets the application as a GameTheory
`GameForm` using the native `SealedProgram.step`. Player commands register
under the invoked player's identity, author arbitrary payloads under that
identity, replay an observed original envelope, or wait. Payloads may name
another owner's handle or contain malformed data; handler checks still apply.
The environment may deliver a pending message, include it, or wait. Inclusion
does not obtain a new action from the original sender.

An explicit finite list determines which principal or environment is invoked
next. The policies choose actions adaptively; this instance does not let them
choose the invocation order. A player receives its current view and the
pre-action views and commands from its own past invocations, including waits
and rejected actions. Remote invocations append nothing to its memory.
This is recall of polling observations, not event-by-event notification.
The analysis horizon produces a prefix, without announcing a terminal event
or settling a pending application.

The environment sees the entire wire pool: pending messages, ledger, every
inbox and sent history, sender serials, and application events. This is a
strong wire-observer instance, not a claim that all this data is common
knowledge or available to a realistic node. Neither player nor environment
policies receive the ideal commitment table, its verifier, or the proof-facing
native action trace. The environment is fixed as a policy in a player game;
its inclusion and delivery choices can depend on this wire view and its own
past invocations.

The following comparisons use this policy interface:

- `runPolicies_enableRebroadcast` and `policyGame_enableRebroadcast` preserve
  the complete execution law when the same no-rebroadcast policies are
  embedded into the replay-enabled instance, at the same environment policy
  and invocation schedule. Disabling replay removes only the explicit
  rebroadcast command, including self-rebroadcast. Fresh same-payload
  submissions and duplicate deliveries remain. No conclusion about arbitrary
  replay-enabled deviations or Nash preservation follows from this embedding.
- `runPolicies_hiding` compares two states with equal wire/application data,
  equal service occupancy, and equal service values outside a protected owner.
  No opening originally authored by that owner may be retained anywhere in
  the pool. Under the same adaptive policies and a fixed schedule that does
  not invoke that owner, the joint law of the wire view, other principals'
  polling memories, and environment memory is identical. The owner's private
  memory may differ and is excluded from the comparison. Opponents can register
  their own values, submit arbitrary guessed openings, and replay available
  messages. Sender/handle checks keep
  successful opening validation confined to sender-scoped service slots.
  The theorem covers both replay selections. It is exact hiding for the ideal
  service, not a cryptographic theorem or a post-disclosure guarantee.

`VegasTests/PendingPolicies.lean` instantiates this comparison with the actual
checked nullable-choice program and every pair of its nullable values. Its
game starts empty: the owner's first two scoped policy invocations register
the chosen value and submit the handle, retaining the private command history.
The subsequent fixed schedule invokes other players and the environment.
Only the protected owner's setup policy changes between the compared games;
all opponent and environment policies remain fixed.
The cleartext control uses the same policy interface: a fixed responder reads
the delivered value and copies it into its own outgoing message, before
inclusion. Thus the control distinguishes values even though the application
rejects cleartext. The compiled setup submits an opaque handle instead.

`WFProgram.sealed_policy_source` in `Vegas/Game/SealedMessages.lean` proves
source-support correctness for every outcome of the native policy game from
the empty state. Its terminal conclusion preserves all source bindings and
payout evaluation. This does not construct a source deviation or equate
source/runtime policy laws. The hiding comparison does not discharge the
compiler's general release-controller, quitting, or settlement obligations.
There are no resource or timing observations of internal verification here;
adding them needs a new information-flow argument.

### The opening controller and its release boundary

`Interaction/SealedController.lean` supplies the local commit/open controller:
register the chosen value, submit its opaque handle, then poll the public-view
opening controller. `openingHandle?` determines readiness from the emitted
rules and public application events, without consulting the chosen value or
the private service. A ready controller submits the existing opening request;
otherwise it waits. It may submit repeatedly before acceptance. Completion of
the reveal node disables further submissions by this controller.

`SealedFragment.openingCommand_prerequisites` in
`Vegas/Game/SealedRelease.lean` proves the compiler boundary for every supported
graph: a generated opening command implies completion of all that reveal
node's graph prerequisites. These are the graph's actual edges, not a second
handwritten release condition. In the nullable-choice fixture, both commitments
must be complete before the owner can submit its opening.

The observation comparison is made before the value-bearing packet enters the
pool. `Interaction/SealedPolicyTrace.lean` records the initial and every
post-invocation snapshot using the same `invoke` function as the native game.
`tracePolicies_last` proves that its final-state law equals `runPolicies`.
`PolicyTrace.firstRelease` selects the first release-enabled snapshot, or the
last snapshot if readiness never occurs. This is a readout of the full trace:
execution and sampling continue after the selected snapshot, and no policy
observes the readout or a stopping signal. The comparison is unconditional,
including traces where release never occurs. Readiness need not be monotone;
after a reveal completes it becomes false again, without changing the first
release snapshot.

`tracePolicies_hiding_beforeRelease` in `Interaction/SealedRelease.lean`
proves equality of the selected wire/nonowner-memory observation laws when the
protected controller waits before the public release condition. The protected
owner may be invoked throughout the schedule. The opening controller
discharges this waiting condition. Opponents and the wire-observing environment
remain arbitrary adaptive policies, fixed between the two executions.

`VegasTests/PendingRelease.lean` starts the actual compiled example empty and
includes both initial owner invocations. The rest of the fixed schedule can
invoke that owner as well as its opponent and environment. Its
`controllerTraceLaw_hiding` compares every pair of nullable values under both
rebroadcast selections. `controllerTraceLaw_cut_reachable` obtains the selected
snapshot from a genuine native invocation prefix and the existing checked
source-support theorem. `PendingReleaseExamples` exercises owner polls before
readiness, immediate opening afterward, delivery before inclusion, and the
return to non-readiness after reveal completion. Full observations disclose the
chosen value; first-release observations remain equal.

`Interaction/SealedPersistence.lean` separately proves that every occupied
ideal-service slot retains its value under any further raw action list and
that application events are append-only. These safety properties do not imply
that an opening is eventually submitted or accepted.

This closes the controller's pre-release information-flow comparison for the
stated instance. It does not compare post-release source/runtime strategies,
identify missing openings with source quitting, or guarantee settlement. The
invocation order is still fixed; fees, verification side channels, accepted
commitments without registered values, and cryptographic realization are
separate model/proof obligations. No public-message Nash-preservation claim is
added to the manuscript.

### Locked choices and selective disclosure

`Interaction/SealedBinding.lean` ties every accepted commitment to its rule's
canonical owner/node slot and every accepted opening to its reveal rule's
source slot. The invariant holds from empty across arbitrary native actions,
including malformed traffic, re-registration, and replay. Acceptance therefore
certifies an occupied slot in this ideal service. This relies on the current
acceptance check; it is not a claim about arbitrary cryptographic commitments
that may have no successful opening.

`Interaction/SealedPolicyBinding.lean` transports that invariant to supported
policy executions and their release snapshots. A value present at the selected
snapshot persists to the final snapshot of the same complete trace.

`VegasTests/PendingChoiceLock.lean` extracts the opponent's value at release for
the actual checked nullable-choice program. The extraction is analysis data,
not an extra input to any policy. `choiceLaw_independent` proves that its law is
independent of the honest owner's value against unchanged arbitrary adaptive
opponent/environment policies and any fixed finite continuation schedule.
`mixed_choiceLaw_product` gives the corresponding product law for a randomized
honest input. The law includes runs where release is never reached: outer
`none` denotes that case, whereas `some none` denotes the source decline value
at a reached release. `choiceAtRelease_none_iff` proves this distinction on
supported traces; no successful-execution conditioning is used.

`choiceAtRelease_source_field` identifies each extracted value with the actual
compiled source field in a reachable decoded configuration.
`choiceAtRelease_persists` fixes it through the entire remaining execution, and
`opened_eq_choiceAtRelease` proves that any accepted later opening discloses
exactly that value. These results prevent value selection after the honest
opening. They do not force the opponent to publish its fixed value.

`VegasTests/PendingWithholding.lean` exercises that remaining choice in the
native policy game. Player one commits to `some false` in both executions,
then opens only when player zero's delivered opening contains `some false`.
After observing `some true`, it withholds. Both commitments and player zero's
opening have been accepted; the pending branch retains player one's original
bound value rather than changing it to the source decline value.

`VegasTests/PendingWithholdingSource.lean` compares publication with the
independent written-order source game. `withholding_not_source_publication`
proves that no source behavioral profile has the same publication law as the
withholding run: every terminal source result has a final public binding, even
when that binding contains `none`. The canonical commit/open controller can
finish from the same reached prefix under the unchanged environment and
remaining invocation horizon. The obstruction is therefore not merely a
horizon that is too short to execute a submitted opening.

The impossibility concerns a publication-preserving terminal-law comparison
for this bounded runtime and source fixture. It does not refute every coarser
decoder or every equilibrium claim. A resolution transition and its service
requirements must implement the source's specified quitting consequences;
changing a missing opening to `none` in the decoder alone supplies neither
that operational mechanism nor its strategic correctness. The next positive
comparison must account for this post-disclosure decision explicitly.

### Timeout dependency gates and atomic inclusion

These components extend the runtime toolkit, not the proved endpoint of the
sealed-message compiler. `Interaction/DependencyGate.lean` stages action
completion and ordered dependency checks at a supplied clock reading. An
overdue missing dependency excludes its principal; failed checks or a rejected
body return no staged state. The compiled entry point must supply authenticated
actor/action labels and its dependency list.

`Interaction/DependencyGateLaws.lean` proves that resolving an overdue
dependency with a shared mutable activity timer can prevent a second missing
dependency of a distinct active owner from resolving in that same pass. With
immutable deadlines, checks succeed whenever each dependency is completed,
already discharged, or overdue. This does not guarantee admission, body
acceptance, or inclusion of the enclosing call.

`Interaction/TransactionalInclusion.lean` uses native pool inclusion followed
by an atomic handler. Rejection retains the initial application state but
keeps the included message in the ledger and preserves earlier deliveries.
`InteractionTests/TimeoutGate.lean` exercises these operations together,
including the shared-timer failure and immutable-deadline success.

The gate clock has abstract natural-number units. The Kotlin emitters use a
call-entry snapshot of their shared activity timer, matching the fixed-deadline
policy by inspection; re-reading the staged timer is the countermodel. No
generator or VM refinement theorem connects those emitters to this gate. Ethereum is its
grounding instance, not a dependency of these components. See the
[timeout compilation design](timeout-compilation.md) for the precise issue
and next integration obligations.

`Interaction/SealedTimeout.lean` supplies an integrated final-expiration
instance at a named opening checkpoint of the original sealed application.
It uses the same `validateMessage?` operation as untimed execution, a public
monotone clock, permissionless expiration requests, and atomic included-call
receipts. Expiration is enabled only after the immutable deadline and when
the original public opening-readiness test passes. A valid late opening may
still win until expiration is included. Expiration stops later protocol-event
acceptance while leaving committed values and earlier public events intact.
Further service registration and wire activity remain possible. Completion
resolves the named checkpoint, not the entire program.
This is a final-failure policy, not source settlement or the dependency gate's
continuing principal-exclusion policy.

Its native policy game uses a fixed finite polling list. Players control their
own registration, raw submission, replay and waits from local views and own
histories; the wire-observing environment adaptively advances the clock,
delivers and includes messages, or waits. Public views include receipts and
resolution status. The environment does not see the commitment table. Every
supported policy outcome is an actual native run, and existing bound values
remain unchanged under all those policies. No clock or service progress is
assumed, and a bounded unresolved run stays unresolved.

The compiled-prefix `PendingTimeout` tests exercise readiness, the strict
deadline, both race orders after opening delivery, receipt order, and
retention of the secret in the private service without a fabricated public
opening. `PendingTimeoutPolicies` proves exact completion/expiration laws for
the same players and polling schedule under opposite environment inclusion
orders, with the valid opening delivered in both executions.

`WFProgram.sealed_timeout_run_source` and `sealed_timeout_policy_source`
connect every finite raw run and every supported policy-game outcome to a
reachable compiled graph prefix. If that decoded prefix is terminal, they
reconstruct a written-order source execution, its terminal bindings, and its
payout evaluation. Expiration and rejected traffic stutter this prefix
projection while retaining their real observations in the native state.
These results do not supply source policies or equality of outcome laws.
`PendingTimeoutSource` exercises the terminal branch for every nullable input
pair and both commitment inclusion orders, including a clock advance past the
deadline before completing both openings. Its terminality proof checks the
whole decoded graph, independently of the monitored checkpoint's status.

`SealedTimeout.HidingRelated.run` proves raw pre-disclosure noninterference:
services may differ in the protected principal's occupied values, while
occupancy, traffic, events, clock, resolution, and receipts agree. Retained
traffic must contain no opening authored by that principal. Identical raw
traces with no further commands from it preserve the relation; other principals
may submit arbitrary payloads, and replay, delivery, inclusion, and clock
advances are unrestricted. Expiration and rejection receipts therefore do not
create a hidden-value channel under these premises. This reuses the common
validator equality and the payload-generic retained-message invariant, rather
than assuming failed calls are unobservable.
`PendingTimeoutHiding` supplies a compiled-prefix instance with distinct
protected bindings and equal recipient views through an actually included
expiration call; its public status and receipts are checked explicitly.

Full source-quitting correspondence, adaptive hiding under the new policy
interface, and general deviation adequacy remain open. The fixed schedule is
not a model of arbitrary asynchronous activation or player-owned builder
capabilities.

### Shared message applications and fixed chance kernels

`Interaction/MessageApplication.lean` supplies a receipt-bearing message runtime
parameterized by application state, payloads, principal-local commands,
environment commands, and player/environment projections. Native inclusion uses
`MessagePool.includeApplication`: acceptance installs the returned application
state, rejection retains its prior state, and both publish the existing message
and a receipt. A missing message produces neither publication nor receipt.
Previously delivered messages remain in recipient inboxes.

Private commands are scoped to the invoked principal. Environment commands
invoke an application-supplied `FinDist` kernel without modifying the pool or
inclusion receipts. This supports a fixed chance law whose invocation time is
environment-controlled. A concrete application must prevent early sampling and
rerolling, and must not expose a command that selects the chance outcome.
The fixed-kernel law does not remove selection effects from adaptive stopping
or a failure to trigger the draw. There is no automatic clock advance, timeout,
or progress guarantee.

`MessageApplicationPolicies` derives a game from this same transition law.
Policies see their explicit projections and own sampled command histories;
the environment additionally sees the complete pool. Public receipts are part
of both observation interfaces. A fixed finite invocation list remains an
analysis parameter, not an observed global counter. Policy randomization and
application chance are composed as separate kernels. Every supported policy
outcome follows a supported native execution of its recorded action trace;
application invariants therefore lift to arbitrary supported policy runs.

`Vegas/Compile/ApplicationImage.lean` instantiates this carrier for finite
collections of public-choice, binding, and conditional-publication instructions.
An ordinary public-choice instruction retains its generated endpoint,
dependency-local guard, and two output fields. Raw
messages carry an address and a dynamically packaged language value; unknown
addresses, incorrect types, and malformed payloads are rejected without
removing public traffic. Successful inclusion publishes the value at both
fields and completes the pair once. The native inclusion law also preserves
sent histories and recipient inboxes and records the ledger entry and receipt.
`Vegas/Compile/PublicChoiceImage.lean` generates these instructions from
certified source occurrences. `include_source_choice` connects that actual
inclusion to the adjacent source steps under public-validation eligibility,
matching stores, readiness, and lookup of the generated instruction.
`ApplicationImageRefinement` proves preservation of public-memory agreement
and represented graph reachability through that inclusion. Its relation permits
unopened values to be missing from public memory. `ApplicationImageController`
connects the source-kernel controller to the handler's canonical typed address
and proves that encoded packets are accepted exactly for legal source choices
at the stated matching, ready checkpoints. `ConditionalImageController` supplies
the corresponding typed transport and source-kernel law for conditional
publications, using the image's actual accepted-handle and completion maps.
`ApplicationImageReadout` loads the complete source choice footprint from
current public memory and the owner's first slot-scoped private registrations.
Resolved public fields take precedence: an attempted opening cannot replace a
publicly resolved decline. Missing private fields can be recovered only for an
accepted canonical owner/field handle. The source-view theorem uses native
refinement, typed field metadata, operational availability, and correspondence
between cached registrations and accepted snapshots. Source environments and
service snapshots occur only in its proof, not in the readout's inputs.

Snapshot correspondence is not implied by the public accepted handle. The
runtime permits acceptance of an unprepared handle followed by a registration;
that later value cannot open the frozen handle. Generated controller assembly
must establish registration before binding submission, rather than infer
snapshot correspondence from the subsequent history. Whole-image controller
dispatch, availability, and this ordering invariant remain separate obligations.
`ApplicationImageRegistration` proves that, from
the canonical empty-service initialization, every principal's earliest recorded
registration equals its current preparation-table entry. This holds for all
supported policy executions, including arbitrary re-registration and traffic.
It establishes history-to-preparation provenance, not history-to-frozen-snapshot
correspondence when acceptance preceded preparation.
The same module's post-binding continuation theorem starts with a cached value
and the native binding update that snapshots it. Every supported later policy
run preserves both the cache entry and the exact accepted snapshot, even with
arbitrary further registrations. Connecting that update to a successful
generated binding submission/inclusion remains part of controller assembly.
The public initializer filters out sealed initial fields and establishes the
representation relation. The mixed-type checked program in
`VegasTests/ApplicationImage.lean` exercises generated Boolean and optional
Boolean endpoints, a guard that reads a public input, exact successful storage
and receipts, rejected payloads, and replay through actual native execution.

`ConditionalImage` generates binding and conditional-publication metadata from
the same source occurrences and field allocation. The image's public projection
contains accepted handles and a monotone clock as well as store and completion
flags. Its private operational state contains the ideal preparation service and
acceptance-time snapshots. Binding admission neither tests nor reveals whether
a registered value exists; wrong-type and absent registrations can be accepted
as opaque handles. Subsequent registration cannot make a frozen unopenable
handle openable. An authenticated opening is checked against its snapshot and
the compiled source guard; other players cannot use it as a guessing oracle.
This is ideal commitment functionality, not a cryptographic realization.

`ConditionalOpeningValidation` proves source-guard equality when the only
nonpublic validation dependency is the exact typed source reference supplied
by the verified claim. Public data supplies the other dependencies. The source
environment is proof data only. Decline and included overdue expiry use the
certificate's source-legal declining value, including when the accepted handle
cannot open. Explicit environment clock advancement and actual expiry traffic
are modeled separately; no liveness or honest deadline protection follows from
the instruction semantics alone.

`ConditionalImageRefinement` connects the generated instruction to source
execution in both local directions. A legal source choice with its correct
frozen binding is accepted as the canonical typed packet. Conversely, every
successful inclusion at a represented checkpoint has the exact native storage,
receipt, ledger, and message-history effects and performs the source's adjacent
commit/reveal steps. The latter theorem requires only consistency of any
recoverable frozen value with the source binding; it also covers declines and
expiry when no value can be recovered. These are endpoint laws, not a premise
that an entire public-message execution already simulates its source.

`ApplicationPlan` generates an image by structural consumption of the existing
source and accounting tree, rather than a supplied list of selected occurrences.
Its certificates check backend eligibility: public guard dependencies for
ordinary choices, the exact permitted private dependency for conditional
openings, and an unrestricted original guard for opaque bindings. The last
condition is necessary for the current unvalidated binding instruction: a later
opening guard need not enforce the original binding's restrictions.

Chance instructions retain the exact graph distribution code and use public
typed reads. The environment can trigger a ready address but cannot supply a
sampled value. Successful invocation atomically completes the instruction;
another invocation cannot redraw. `ApplicationImage.sample_law_refines` proves
equality with the graph's local distribution and refinement of every supported
draw. This assumes ideal unbiased entropy. A concrete entropy mechanism and
whole-profile laws under adaptive invocation timing require separate proofs.

`ApplicationPlanCoverage` proves exact consecutive graph-node coverage and
unique dispatch addresses; emitted membership gives exact lookup.
`ApplicationPlanAllocation` proves canonical target fields, no duplicate field
allocation, and the shared source-field/commitment-slot convention. The checked
mixed-type and conditional examples use this structural generator and its
coverage/lookup theorems. `ApplicationPlanOrigin` recovers the source occurrence
and its eligibility certificates from arbitrary successful dispatch.
`ApplicationPlanRefinement` then proves that every supported finite native or
randomized policy run retains a reachable graph witness, matching public storage
and completion flags and relating accepted snapshots to their sealed source
fields. Its premises do not restrict messages to generated packets.

Unpaired literal reveals, initial default resolution, and autonomous
publicly forced execution have no derivation constructors yet. Initial sealed
inputs also require explicit provisioning; filtering them out of public memory
does not implement it. Complete initialization, assembled source-policy
correspondence, and unilateral deviation simulation remain to be integrated.
`ApplicationImageOutcome` decodes actual public terminal fields, rejecting
missing or ill-typed public data and ignoring sealed fields.
`ApplicationPlanOutcome` starts at the actual empty-pool initialization and
proves that every completed supported execution has the public outcome of a
written-order source execution. Completion is tested by a finite scan of native
flags. This is a whole-run support theorem, not a settlement guarantee or an
equality of profile laws.

`VegasTests/GeneratedDisclosure.lean` compiles the complete eight-event optional
disclosure source through this generator. A concrete message run prepares and
binds the secret, publishes the forced marker, invokes chance, declines
disclosure, and publishes a response. Its checked public law retains the exact
source coin distribution and reports all nodes finished on every supported
branch. Repeating the chance invocation leaves this law unchanged. A supported
completed run is then given an actual written-order source witness by the
general compiler theorem. This is a concrete completion example, not a
whole-program policy or service theorem.

`VegasTests/GeneratedPersistentDisclosureController.lean` installs the generated
second conditional controller with the full owner-local readout. At the concrete
opened and declined checkpoints it proves the exact first-submission law for
arbitrary randomized source kernels and histories with the stated cache contents.
It checks that first-site opening traffic cannot populate the second-site cache
and that an already recorded second choice is not sampled again. These are local
controller laws; they do not establish the whole-program policy-prefix invariant
or a service guarantee.

`BindingImageController` generates the original binding's two-phase policy
from its source decision occurrence and compiler-allocated field. It samples
the source kernel into local ideal-service registration, then submits the
canonical opaque handle. For arbitrary histories its supported commands are
wait, correctly typed local registration, or that handle submission. An
ill-typed first registration prevents resampling, and a recorded handle
submission prevents another submission. This does not impose a private
network channel: the public packet is a separate message-pool action.
`BindingImageExecution` proves `SourceDecisionSite.bindingPolicy_two_invocations_source_law`,
retaining the complete law of two consecutive ready owner invocations. Its
premises include an available source-matching readout and empty registration
and submission caches. The latter are distinct conditions for arbitrary
supplied histories.
`ApplicationImageBindingInclusion` connects an actual recorded environment
inclusion to the cached accepted snapshot and preserves that snapshot through
arbitrary subsequent policies.

`VegasTests/GeneratedBindingPolicy.lean` instantiates these results at the
first decision of the persistent-disclosure source. From empty initialization,
two generated owner invocations and a specified inclusion have the exact
arbitrary randomized source law of frozen snapshots. The environment's full
pool/application observation is independent of that draw both while the binding
packet is pending and after its inclusion.
The inclusion is prescribed, not derived from fairness. This prefix result
does not establish general controller dispatch, arbitrary-interleaving source
readout invariants, settlement, or whole-profile/deviation correspondence.

`ApplicationImageInvariants` proves that every accepted handle and its frozen
snapshot persist through arbitrary supported native and policy executions.
This includes absent and ill-typed snapshots and requires no well-formed-image
premise. It fixes acceptance-time verification data; source consistency of that
data is additionally established by the generated-plan refinement relation.

`VegasTests/ConditionalApplicationImage.lean` uses a checked three-node source
with an unrestricted initial binding and an accounted optional publication.
It exercises generated code through the shared native runner: successful
opening, unregistered and wrong-typed preparation, late registration, voluntary
decline, clock-enabled expiry, invalid openings, and replay. Its concrete runs
do not replace the still-required randomized and unilateral whole-run laws.

`ChoiceController` samples a choice at its first encoded private command or
public submission and retains the value in the principal's own chronological
command history. Subsequent invocations wait or retry that value according to
an explicit retry policy. `ChoiceControllerHistory` expresses the full
first-invocation law as the decision kernel followed by the native player step,
derives its exact cache law, and proves cache retention through arbitrary later
invocations. The sample is recorded independently of delivery or acceptance.
`ChoiceEncoding` requires roundtrip decoding and canonical accepted commands;
its private-command and submission lifts use the same controller and history
proofs. Endpoint tagging separately proves disjoint decoding and rejects
misaddressed messages before invoking the application handler.
The non-Vegas stochastic regression checks two pre-inclusion polls: both pending
requests and both history entries contain one shared draw, not two independent
samples. `InteractionTests/PrivateChoice.lean` instead registers one ideal
commitment, checks agreement of service lookup and the cached draw after a
second poll, and proves the public pending pool remains empty.

`Vegas/Compile/PublicChoiceController.lean` adapts source decision kernels to
this controller using the generated endpoint and the complete declared choice
readout. Disclosure's composite responder uses the adapter after publication;
its timeout branches remain part of that same policy. The native readout uses
only public application fields, and the first ready invocation records exactly
the source response law. Deterministic service guarantees instantiate pure
source kernels. These local sampling and memory laws supply neither a complete
randomized source-profile law nor deviation simulation for the public runtime.

`Vegas/Compile/ConditionalOpeningController.lean` supplies the corresponding
local source-kernel adapter for certified optional openings. Its canonical
encoding addresses the generated publication node, distinguishes voluntary
decline from permissionless expiration, and preserves the source value
equivalence. The checked first-emission and acceptance theorems require matching
source readouts and the accepted-binding, readiness, verification, and guard
premises. Disclosure's native owner composes this component with a
`SourceDecisionSite.controller` for private initial registration, an opaque
binding phase, and response expiration. Publication packets carry an arbitrary
endpoint tag; dispatch rejects wrong tags without hiding delivered traffic.
The opening readout uses the earliest slot-scoped private command for an
accepted commitment, or the accepted public default, together with the full
remaining declared read footprint. This includes the fixed private marker,
reconstructed from public marker completion. Pure initialized service proofs
carry that exact cache through binding and disclosure. `compiledPlayers` projects
the three strategic kernels from one written source profile; its pure benchmark has the independent
AST's exact outcome law. The phase assembly is specific to this checked program.
General application generation, randomized whole-profile laws, and public
deviation simulation remain open.

`SealedTimeout.messageApplication` instantiates this carrier with the timed
sealed handler. Its state and action translations have both roundtrips, its
player/environment views agree, and every finite native run has exactly the
mapped timed execution law. `WFProgram.sealed_timeout_message_policy_source`
uses that correspondence for arbitrary shared player/environment policies:
their outcomes decode to reachable graph prefixes, and terminal decoded
prefixes reconstruct written-source executions, bindings, and payout
evaluation. This remains a support theorem, not source-policy backtranslation
or an outcome-law comparison. The final-expiration policy is unchanged.

`InteractionTests/MessageApplication.lean` exercises a separate lottery
application with no Vegas imports. It checks acceptance, rejection, retained
delivery, missing-message stutters, principal-scoped private operations, a
fixed fair draw, and completion disabling further draws. Its policy-game
regression checks that deterministic controllers retain the application's
chance law. Hiding of its private prediction is a projection equality, not a
cryptographic-security theorem.
The untimed receipt-free sealed instance remains a distinct weaker model;
extra receipt observations are not silently erased from the shared game.

`VegasTests/DisclosureApplication` specializes the checked optional-disclosure
program to this same carrier, with no graph configuration in operational state.
The application includes binding, the forced marker, one-shot public chance,
conditional publication, and the responder's continuation. Its publication
window starts at the sampled signal's clock. Disclosure, decline, and included
expiration all reach the response phase and arm its own window. Initial
expiration is a permissionless call that installs an explicit public default
`false`. The public state distinguishes that disposition from an accepted
opaque commitment. Binding accepts the canonical opaque handle even
when it has no opening. Acceptance captures a private verifier; both service
tables are omitted from player and environment observations. Acceptance's
public result and the marker/chance/clock observation laws are independent of
the tables. A later opening checks the captured verifier, not mutable private
preparation.

The response entry point delegates to `Interaction.PublicChoice`, whose owner,
node identities, and dependency gate come from a `PublicChoiceSite` in the
actual source. Its validator evaluates retained guard code using only its
stored dependency footprint. The response's constant guard has no stored
dependencies. In general, public execution additionally requires that every
dependency is public and that the native public store contains its correct
value; guards over private data need a different validation mechanism.
`DisclosurePublicChoiceRefinement.respond_handle` gives the exact native
handler equation, including rejection. Its source-step and graph-refinement
theorems instantiate the generated validator's source agreement and paired
graph effect. They relate the local adjacent source choice/reveal to the native
update; they do not identify intermediate observations or whole execution laws.
Application assembly and controllers remain specialized to this instance.

`DisclosureApplicationInvariant.run_binding` preserves the accepted binding
and verifier under every supported finite native continuation.
`run_unopenable_publication` proves that any publication reached from an
accepted unopenable binding is decline, even after arbitrary late preparation
and raw traffic. It does not force that publication to occur.
`DisclosureMalformed.unopenable_run` checks the complete native execution from
empty: acceptance, public chance, late preparation, a delivered and rejected
opening, clock advance, an included permissionless expiration, and response.
Its law retains chance, public receipts, and the failed opening in the
responder's inbox. Rejection does not erase that message.

Response expiration is a separate permissionless entry point selecting the
existing source rejection action `false`. Its window starts at publication's
successful inclusion, not at initial binding or the public sample. Early
expiration and expiration after a completed response reject. Publication cannot
be repeated to restart the response window; accepted handlers preserve its
value and window origin after resolution. Advancing the clock alone resolves
neither decision. The deadline enables expiration: a normal response can still
win until an expiration call is included.
`DisclosureExpiration.response_expiration_run` proves the complete native law
when the owner discloses and later expires an absent responder; no responder
action occurs. `response_expiration_source` connects the expiration handler to
an actual written-order source execution for every public payout list and
every invariant state meeting its public readiness/deadline conditions.
These are handler and included-call execution results. The timeout-driving
controllers described below still need a settlement proof under their services.

`DisclosureInitialExpiration.initial_expiration_run` gives the complete native
law with no owner action: the responder submits the initial expiration,
expires disclosure after the source chance step, and responds. The result
retains the public-default disposition, the chance law, and inclusion receipts.
Its source theorem fixes the initial source value to `false` rather than
reconstructing an arbitrary witness. Initial expiration preserves private
preparation; later binding cannot replace the installed default, and an opening
claiming the other Boolean rejects even if that value was privately prepared.
Early initial expiration and expiration after an accepted binding also reject.
The initial deadline is measured from this instance's clock-zero initialization.
A late ordinary binding can win until the expiration is included.

The publication kernel takes an opening validator separately from the source
guard predicate. Opaque bindings use the captured ideal verifier; public
defaults compare the claimed value to the recorded public value. No private
commitment is created or modified to implement the default. All-policy native
source-support and the specified honest law include these new handlers, but
neither they nor the scripts supply a service or deviation-comparison theorem.

This ideal instance captures binding at inclusion. Private preparation while
the handle is still pending remains possible. A cryptographic realization must
account for creation-time binding and the relationship between its packets
and these handles; no such realization or strategy comparison is proved here.

`DisclosureApplicationInvariant` and `DisclosureApplicationSource` prove that
arbitrary supported player/environment policy executions from empty decode to
reachable graph prefixes with exactly the native completion flags. A completed
native outcome is equivalent to a terminal decoded prefix and reconstructs an
actual written-order source execution and the compiled evaluation of any public
payout list. A valid accepted binding decodes to its stored value. An unopenable
binding uses `false` as a source witness and can only disclose decline; this
proof-facing convention neither installs a runtime value nor settles pending
execution. `DisclosureReachability`
supplies actual protocol witnesses for every valid canonical phase.
These are support results, not a strategic backtranslation or settlement
guarantee for arbitrary policies.

`DisclosureApplicationExecution.honest_policy_data` proves the complete shared
policy-run law from empty for a fixed initial binding, any deterministic
binding-and-signal-dependent disclosure rule, and any deterministic public response rule.
The law retains the hidden binding in addition to the public signal, optional
publication, and response. `DisclosureSourcePolicies` independently constructs
the corresponding information-local AST policies.
`DisclosureApplicationLaw.honest_source_law` equates actual message-policy
execution with that written-order denotation for every public payoff list;
`compiled_source_law` makes the complete generated policy assembly explicit
for the checked program's pure profiles.
`honest_settles` proves settlement for every supported run of these controllers
under the specified inclusion script. The script triggers the actual chance
kernel; it does not supply the sampled signal.

The same pure controllers drive permissionless expiration: the responder
resolves initial silence and absent publication, while the owner resolves an
absent response. The owner evaluates continuation rules at the accepted public
default when present, rather than its unsubmitted private intention. Local
controller laws check those choices, release gating, and completed-response
inactivity; they do not guarantee that the corresponding calls occur in time.

`DisclosureService` supplies a bounded service instance over the same policy
runner. Each cycle has two player invocations per principal, two deliveries,
another two invocations per principal, eight inclusion opportunities, the
marker and chance triggers, and one clock increment. Thus players can react
to delivered packets before inclusion. The inclusion selector may inspect the
entire environment view and choose any existing pending identifier; FIFO is
one concrete instance. The generic arrival bound counts every player invocation,
including replay and malformed submissions. Every complete cycle, and every
finite sequence of cycles from empty, drains the pending pool for all player
policies. This is resource accounting under a fixed phase discipline, not
Ethereum service, application settlement, or source-choice preservation.
`DisclosureServiceClock` proves that the public clock advances exactly once
per complete cycle under these same policy quantifiers.

`Interaction/MessageApplicationProgress.lean` turns reserved inclusion capacity
into application progress when a concrete pending resolver has stable readiness,
resolves on selection, and establishes a persistent milestone. This is a theorem
about the shared policy runner, with local native-inclusion premises.
`DisclosureServiceResolution` and `DisclosureResponseResolution` prove those
premises for initial binding, ordinary response, and all three overdue expiration
calls. Competing messages may resolve the phase first, so these results guarantee
phase resolution rather than a particular chosen value. They begin with a ready
request already pending and do not themselves establish controller submission
deadlines or timeout-race exclusion. The initialized results below establish
these facts for unchanged deterministic controllers under the stated service.

`Interaction/MessageApplicationArrival.lean` proves that player preparation,
submission, replay, and recipient delivery retain pending envelopes during a
delivery-only environment phase. `MessageApplicationSubmission` relates an
exact submission in a principal's history to a ready pending authored envelope
or an established milestone. Its premises are local application-kernel
preservation, request acceptance, and emission readiness on invariant states;
the history theorem itself assumes neither fairness nor invocation opportunity.

`DisclosureInitialService.responder_initial_by_cycle` connects these results
to the actual controller and service game from initialization. For every owner
policy, every admitted adaptive inclusion selector, and every cycle count at
least `window + 2`, the unchanged responder guarantees an accepted initial
binding, a completed marker, and a sampled public signal. An earlier submitted
initial expiration is accounted for by the history theorem; otherwise the
controller submits during the cycle. The service tail invokes the actual
chance kernel, without selecting its sampled value. This is an initial-phase
progress theorem. It does not identify the selected binding with an unchanged
owner's source choice.

`DisclosureServiceSettlement.responder_settles_by_cycle` proves complete
initialized settlement against every owner policy with the responder unchanged:
every supported execution after at least `2 * window + 4` complete cycles has
a native outcome. The proof uses the exact controller history, an immutable
signal time origin, publication resolution by `2 * window + 3`, and one response
cycle. It holds even for a zero window. This is a one-sided termination theorem,
not preservation of the responder's chosen value: its proof permits a competing
expiration to resolve a phase first.

`DisclosureOwnerSettlement.owner_settles_by_cycle` supplies the other side:
for a positive window, the unchanged owner guarantees an outcome by
`window + 3` cycles against every responder policy and admitted selector.
`owner_choices_preserved` also identifies the owner's actual selected secret
and opening or decline after every cycle count at least two. The first cycle
freezes the registered secret; the second includes the selected publication
before expiration is eligible. Both stages start from initialization. Full
pool provenance excludes stale conflicting owner-authored publication packets,
including packets retained for later replay. This does not restrict the
responder's raw messages or the selector's payload inspection.

`MessageApplicationPolicyInvariant` supplies policy-sensitive execution
invariant lifting, including native state and command histories. Its retained
message predicate is preserved through submission, delivery, inclusion, and
replay. The disclosure proofs instantiate it before and after the public signal;
they do not replace the runtime with a second evaluator.

`DisclosureResponderSettlement.responder_choice_preserved` proves the other
choice guarantee: for a positive window, any resolved response at a complete
service-cycle boundary equals the unchanged responder's selected function of
the actual signal and publication. `responder_settles_to_choice` guarantees
that exact reply by `2 * window + 4` cycles. Both begin at initialization,
permit arbitrary opposing policies and admitted adaptive inclusion selectors,
and retain full-pool provenance through replay. When publication first occurs
during inclusion, no responder response packet is present and the response
deadline is newly armed. The next cycle supplies a timely response opportunity;
after resolution, its value is immutable.

These theorems meet the disclosure operational integration gate for its
deterministic source controllers. The next task is generation of public
applications and controllers from checked programs, using disclosure as a
regression instance. Randomized outcome-law and strategic deviation comparison
remain obligations of that compilation edge.

`Interaction/MessageApplicationPolicyHistory.lean` supplies the reusable
history fact: if a principal's policy satisfies a law of its observed view and
chosen command, every entry recorded in its local history satisfies that law.
The responder instantiation identifies publication-expiration requests and
responses at the views where they were selected. Together with the submission
bridge, this accounts for one-shot flags without assuming requests remain
pending or that they have already succeeded.

`DisclosureServiceReaction` checks that a delivered cleartext packet can induce
value-dependent outgoing traffic while the ledger is still empty. The opaque
packet control checks this particular receiver, not arbitrary-receiver hiding.

This honest-law instance prescribes the invocation and inclusion sequence. It
is not an admission theorem for a class of delayed-delivery services, does not
cover arbitrary source randomization, and does not compare runtime deviations.
The remaining integration requires a general source-generated application,
timely opportunity and settlement under the service discipline, and complete
randomized source-policy and deviation laws. Queue clearance alone does not
establish those properties.

### Source-certified conditional publication

`Interaction.ConditionalPublication` classifies opening, owner decline, and
permissionless expiration messages. Its application-supplied metadata names
the accepted original handle, completion prerequisites, and deadline. A valid
opening must pass both ideal commitment verification and the application's
`canOpen` predicate. Cleartext and malformed messages remain possible traffic
but do not resolve the site. Expiration is strict and must actually be included;
the clock reading alone executes nothing.

`CommitmentAccounting.OpeningSite` locates a conditional-publication certificate
inside an actual source accounting derivation. It converts to a
`ConditionalPublicationSite`, whose `PublicChoiceSite` supplies the generated
choice/reveal nodes and exact rows. The conditional certificate identifies the
original typed source field. Later copies of a retained binding can supply
this certificate independently of the original accounting discharge. Backend
handle allocation is explicit:
an initial sealed field need not have a producer node, and a graph field id is
not automatically a commitment slot.

`ConditionalResolution` proves the local comparison in both directions.
Every accepted result is decline or the original bound value and performs the
existing legal source commit/reveal steps, assuming the represented binding and
opening-validator soundness. Conversely, every legal source value has an
accepted canonical owner request at a ready site, assuming validator
completeness. Both validator obligations concern the stored bound value;
commitment verification handles false claims about that value. The accounting
certificate alone does not imply that opening is always legal. In particular,
the persistent-quitting guard can allow only decline.

The `runtime_resolution_reachable` theorem in `ConditionalExecution` combines
the emitted metadata, runtime validation, source/store agreement, and actual
primitive graph kernels. An accepted result justifies the decoded effect of
executing the adjacent choice and reveal, preserving graph reachability.
An enclosing handler must actually apply that effect. The readiness test
includes prerequisites of both nodes, excluding only the internal
choice-to-reveal edge.
`DisclosurePublicationOrder` proves that the concrete optional-disclosure
site needs no additional waiting once its choice is ready, and that its
responder cannot execute before publication.

`DisclosurePublication` instantiates the metadata with the checked source's
accounting site. Its transactional handler is related both to actual source
`SmallStep.Star` steps and to the generic graph-reachability theorem. Concrete
submit/deliver/include executions check opening, decline, and expiration.
These fixtures start at a represented disclosure checkpoint; they do not yet
generate or prove the entire public interaction establishing that checkpoint.

These are local compiler and execution results, not whole-interaction
deviation adequacy. The service binding, represented source checkpoint, and
validator correspondence must be maintained by the enclosing application.
The classifier does not implement initial nonparticipation, all later forced
steps, or settlement. Atomic execution also removes the intermediate graph
observation point; the two primitive-step laws do not identify the histories.
Inclusion retains public traffic and recipient inboxes. If an opening was
delivered before expiration, the recipient retains its value even when the
application later records decline.

### Replay and application identity

`MessagePool.replay` copies an envelope available in the broadcaster's sent
history, inbox, or public ledger. It preserves the original message id, author,
and payload, without using the hidden pending pool to decide whether replay is
possible. `MessagePool.replay_view_determined` proves that the response and the
broadcaster's resulting observation depend only on that broadcaster's view.
The native action carries the broadcaster separately from the envelope author;
principal-scoped policies must preserve that distinction.

Duplicate envelopes can coexist in pending and be included repeatedly. There
is no transaction-nonce admission rule in this carrier. The application checks
its completed-node state on each inclusion; `SealedProgram.run_eventNodes_nodup`
preserves node uniqueness over every finite native action list, giving
at-most-once application execution from the empty state.
The source-support theorem covers replay actions as well. This is an
application-level replay result, not a claim about valid Ethereum transaction
histories. Concrete nonce validation, signatures, and their observations belong
to subsequent refinement obligations.

`VegasTests/PendingReplay.lean` exercises the compiled program. A recipient
rebroadcasts another player's envelope, two included copies execute only one
commitment, and replay after completion extends the public ledger without
changing the decoded source outcome. It also checks a distinct case: an
opening rejected for missing prerequisites can be replayed successfully after
those prerequisites complete, without another submission by its author.
Completed-node idempotence therefore does not make all replay actions inert or
unobservable. Fees and resource contention are not modeled here.

This is a single-application-instance model. Cross-instance replay requires an
explicit instance identity, a multi-instance execution model, and an isolation
proof. A cryptographic realization must bind the modeled identity and action
context to the authenticated encoding; no cross-instance guarantee follows
from the present owner/node handles.

### Required model and proof obligations

1. Define pending requests, inclusion steps, clocks, deadline processing, and
   the observable events available to every player and the delivery scheduler.
   Permit the scheduler to observe all data declared public by this model.
2. Specify which inclusion/progress guarantees the runtime actually provides.
   If censorship or indefinite delay is admitted, retain it in execution and
   define its source counterpart and utilities; do not remove it by treating
   the scheduler as rational.
3. Connect source-designated quitting to the actual timeout transition. Source
   quitting already accounts for a player's decision not to participate.
   Censoring a player's valid submission is a different causal event: representing
   its outcome as quitting does not prove honest-play or deviation preservation.
4. Prove honest outcome laws and opponent-preserving deviation backtranslation
   for the original players, uniformly over admitted delivery schedulers. The
   scheduler is environment behavior, not an additional equilibrium obligation.
5. If the claimed preservation property cannot hold under those behaviors,
   state and prove the obstruction for that precise model. No general
   delivery/deadline impossibility theorem is supplied by the current composition.

Kotlin nonresponse-handler elaboration, generated EVM-handler simulation, and
cryptographic realization are also separate proof boundaries. Neither private
window compilation nor the public serializer establishes them.

## Failure observations: checked one-shot comparisons

`Vegas/Runtime/FailureObservation.lean` and
`VegasTests/FailureObservation.lean` compare finite strategic kernels, not
transaction executions. They establish bounded representation comparisons
without changing the public-delivery boundary above.

- `response_law_iff_factor`: for fixed observation maps and response policies,
  equality of the joint raw-value/response law for every submitter distribution
  is equivalent to equality of the response distributions at each raw value.
  This tests a proposed policy translation; it does not assume all target
  policies ignore extra observations.
- `adequacy`: if a raw-value decoder has a section and the responder fixes its
  action without observing the raw value, the one-shot raw game is
  deviation-adequate for the decoded game. Both players may use arbitrary
  finite-support randomized strategies. The submitter is backtranslated by
  pushing its entire raw law through the decoder, independently of the
  opponent. Utilities may be any function of decoded value and response.
  The existing adequacy theorem consequently preserves and reflects Nash at
  compiled profiles. The construction is generic in raw/value/action types,
  imports no Vegas syntax, and allows submissions outside the compiler image.
- `early_compiled_not_nash`: exposing the quit/continue bit before the response
  changes a fair Nash profile into a non-equilibrium, although the complete
  terminal law agrees for every compiled profile. A responder's payoff rises
  from one half to one by copying the visible bit. Payoffs depend only on the
  resolved bit and response, not on order. This refutes the specified
  observation-erasing implementation, not every possible compiler or game.
- `no_delayed_response_mixture`: even a profile-local finite mixture of delayed
  responder replacements cannot reproduce that deviation against the unchanged
  fair submitter.

The positive example decodes six abstract failure labels to `none` and valid
Boolean values to `some`. Those labels do not implement timeouts, validation,
or cryptographic failure; their shared settlement is a parameter of this toy
game. The theorem justifies their collapse only behind the specified response
barrier, with no later decisions, fees, raw-dependent utilities, or environment
ports. There is no proof here that a public ledger enforces that barrier or
that arbitrary failure traffic has those semantics. The negative example
compares early with delayed visibility of a quit/continue bit; it does not
model selective opening of an earlier commitment.

The optional-disclosure encoding below supplies a concrete graph-information
and strategy correspondence without weakening `RevealComplete`. It does not
realize these raw failure labels cryptographically. A public runtime must
still derive the relevant response barrier from execution rather than its
strategy type.

## Profile-local preservation with an early signal

`Vegas/Runtime/ConstantSignal.lean` gives a second positive route that does not
require a response barrier. A submitter samples a value, a target responder
observes a function of that value, and the compiled responder ignores that
extra observation. Fix a source profile for which the observed function is
constant on the submitter's support. The hidden value itself may vary.

- `deviation_law` backtranslates every unilateral target replacement with the
  same complete outcome law. A deviating responder sees a constant signal
  because the submitter is unchanged. A deviating submitter may change the
  signal, but faces the unchanged, signal-independent compiled responder.
- `approximate_nash_iff` preserves and reflects same-error approximate Nash
  at these profiles; `nash_iff` gives the exact special case. This is a
  profile-local result, not an unrestricted adequacy certificate over every
  source profile. Off-support behavior of the deviating responder is arbitrary.
- `deviation_bound_iff` transports bounds on every terminal observable under
  unilateral deviations, including harm to another player. This needs neither
  source equilibrium nor an optimality assumption about the attacker.
- `no_quit_of_completion_better` shows that, in the Boolean quit/continue
  instance, a strict expected preference for completion against the designated
  responder excludes quit from the support of a source Nash profile.
  `nash_preserved_of_dominated_quit` derives preservation for every source Nash
  profile when completion strictly beats quit against every response action.
  That dominance assumption is sufficient, not necessary.

`VegasTests/ConstantSignal.lean` checks a profile with both hidden Boolean
values in support, a deviation that changes the quit signal, and a concrete
strict-penalty equilibrium. The earlier fair quit/continue counterexample has
a varying signal and is explicitly checked not to meet the new premise.

The dominance corollary concerns exact source Nash. An approximate equilibrium
may still put positive probability on a strictly dominated action; the
same-error theorem therefore still requires its constant-signal hypothesis.
There is no automatic extension to rare failures or arbitrary public metadata.

Both players here have one strategic stage, and the target's compiled responder
ignores the extra signal even off path. An implementation with further
decisions, alternate responses to malformed traffic, or scheduler-controlled
failure must justify a new comparison. Source dominance alone is not a proof
of that implementation property. None of these results identifies a secret
opening protocol with an optional source value.

For a future model where exact deviation laws fail, an upper bound on the
deviator's payoff by a source deviation may suffice for Nash preservation.
That weaker requirement would not by itself transport bounds on harm to other
players. The constant-signal result does transport them because it proves the
stronger, complete unilateral outcome-law equality.

## Optional-disclosure core probe

`VegasTests/OptionalDisclosure.lean` uses only existing constructors and option
expressions. An original hidden Boolean is followed by a forced marker, a
public coin, a fresh optional opening, disclosure of that copy, and a responder
choice. The original binding itself has no reveal node. The source guard
permits exactly `none` or `some` of the binding; it is an ideal private guard,
not a public cryptographic validator.

Checked evidence:

- Scope/freshness and guard legality produce a well-formed, live machine graph
  through `ToEventGraph.compile_guardLive` and `Machine.ofCompiled`.
- The graph dependencies place the signal after the binding, the optional
  choice after the signal, and the reply after its disclosure.
- Any legal optional opening and arbitrary Boolean reply have a written-order
  source execution. A signal-dependent rule can quit after one signal and
  open after the other; the opening need not be fixed at the initial binding.
- Changing the bound value in an accepted opening is rejected by the guard.
- Quitting and completion have distinct source payouts, and the reply can
  affect completion's payoff; the terminal projection does not merge them.
- The responder's source-visible environment is determined exactly by the
  public signal and optional opening, apart from the fixed marker. At `none`,
  changing the original Boolean leaves this environment unchanged.
- Neither the public graph observation nor any responder decision footprint
  directly exposes the original sealed field, at any graph configuration.
- The term's original binding is not literally revealed on every branch. Its
  checked version instead supplies a `CommitmentAccounting` certificate for
  the conditional-publication site. This accounts for the sealed resource; it
  does not prove confidentiality, erasure, persistent quitting, or realization.

`OptionalDisclosure.not_reveal_complete` records the narrower fact that the
program is not universally literal-reveal complete. Its checked accounting plan
admits the conditional publication without weakening that fact.
`VegasTests/DisclosureTrace.lean` additionally identifies
the unique ready node, internal/strategic phases, active player, and terminal
phase along its eight-node configuration spine. These facts do not classify
all reachable histories or establish a policy correspondence.

The policy-level encoding evidence is organized as follows:

- `DisclosureBinding` and `DisclosureCheckpoint` prove the exact law from
  initialization to the informed disclosure decision for every behavioral
  profile. They retain the store and full owner information, eliminate the
  forced marker choice, and identify that information with the binding and
  public signal.
- `DisclosureOpening` proves that the graph's ideal guard permits exactly
  `none` or the bound value, and executes the optional-copy choice and reveal.
  It does not implement cryptographic validation of a private guard.
- `DisclosureInformation` identifies the responder's complete information at
  every actual history ending at the reply checkpoint: exactly the public
  signal and optional opening. Its remembered decision record is empty by
  `EventGraph.own_eq_nil_of_no_completed_choice`. The legal reply menu is
  equivalent to `Bool`, with neither extra nor missing actions.
- `DisclosureResponse` and `DisclosureLaw.terminal_law` compose the entire
  execution. For every behavioral graph profile, the terminal-configuration law
  equals the extracted finite process: binding, public chance, informed opening,
  and informed reply. Extraction consults only the corresponding player's
  information-local policy at each decision.

- `DisclosureSites` and `DisclosurePolicy` prove realizability and legal lifting
  at every finite decision site, including off-path sites. Extraction after
  lifting is the identity on each player's complete finite strategy.
- `DisclosureCorrespondence.all_profile_law` identifies every behavioral
  graph profile's decoded terminal law with an explicitly specified finite
  disclosure game. The playerwise maps commute with unilateral replacement;
  lifting after extraction preserves outcomes, not irrelevant off-site policy
  code.
- `DisclosurePayoff` proves expected-utility agreement using the actual
  compiled evaluator for every terminal public payoff list. Nash is preserved
  and reflected under extraction, for all graph behavioral profiles.

The source semantic object here is the hand-specified `finiteForm`, not the
Kotlin evaluator. The encoding's initial menu is `Bool`, not the Kotlin
frontend's additional initial quitting choice; it is not a full frontend-game
equivalence.

`SealedOffer`, `SealedOfferEquilibrium`, and `SealedOfferRuntime` instantiate
this correspondence with prices and public buyer values in `{1, 2}`. They
prove a source equilibrium with expected utilities `(1, 1/2)`, an expected
seller-revenue bound of one against the designated buyer even under joint
binding/informed-quitting deviations, and the buyer's nonnegative expected
utility against every seller policy. The equilibrium and buyer guarantee
reach the actual private-request/public-serialization target. Runtime seller
strategies range over all independent finite mixtures of request controllers,
with private retry memory and public order observations. The scheduler is any
admitted public-data behavioral policy, not a delivery/censorship controller.

`BoundedGame.requestAdequacy` supplies the runtime step from finite menus and perfect
recall without a `WFProgram` premise. The checked-core wrapper uses that same
construction. The example's disclosure timeout is the existing quit action;
initial and reply timeouts select existing actions, not new quit settlements.
Its source utility expressions do not establish escrow funding, external-asset
delivery, or ledger conservation. The example remains an ideal finite game,
not a cryptographic or public-chain implementation.

The view equality is not a claim that an observed quit carries no information:
a player's decision to quit can depend on the secret. It states equality of
views for fixed public data, not statistical independence under every policy.
The graph field-secrecy result likewise does not hide a value deliberately
disclosed through the optional public copy.

The Kotlin probe is `src/test/resources/optional-disclosure.vg`, checked by
`OptionalDisclosureTest.kt` in `../vegas`. It typechecks the real frontend
syntax and enumerates the disclosure checkpoints after the two valid bindings
and two public signals. Each offers exactly the bound opening and quitting;
the owner sees the signal and binding, the responder sees the binding as
opaque, and completed quitting becomes public without replacing that earlier
opaque history by plaintext. This is executable Kotlin evidence, not Lean
verification of the evaluator.

Test-report coverage is a separate obligation. On the inspected Windows/JDK 25
setup, a clean Kotlin Maven run succeeds with 48 reported tests but reports
zero tests for 26 existing suites. The two new top-level disclosure tests are
reported explicitly. A successful process exit is not evidence that every
nested test in the broader Kotlin corpus executed; audit leaf discovery before
using that run as comprehensive frontend validation.

These are parallel probes, not equivalent full programs: Kotlin also admits
initial and responder quitting and uses its own branch-dependent settlements.
The Lean marker and optional-copy events are accounted for by the full-policy
comparison above. The additional Kotlin decisions, handler settlements, and
persistent abandonment are not. There is no frontend-lowering or public-delivery
theorem for this encoding. The manuscript distinguishes its finite semantic
instance from the executable frontend fixture.

## Persistent quitting and publicly determined choices

`VegasTests/PersistentDisclosure.lean` adds a second optional disclosure of the
same binding after an actual opponent response. Its guard admits only `none`
when the first public disposition is `none`; otherwise it admits `none` or the
original bound value. Both guards are legal in every declared environment.
The compiled dependencies require the first disposition and opponent response
before the second decision. The original sealed field has no public alias;
this does not hide a value already disclosed by a successful optional copy.

`Vegas/Core/ForcedChoice.lean` defines `PublicForcedChoice` for a typed source
guard. It contains public enable/value expressions and an all-environment
proof that, when enabled, the public value is the unique legal action. Its law
theorem collapses every randomized source choice at that site to that value.
Its continuation theorem uses `denoteSource` itself and leaves continuation
policies unchanged; it introduces no independent evaluator or game.

`VegasTests/PersistentDisclosureSource.lean` instantiates this certificate for
the second guard, using only the first public disposition. For every complete
source behavioral profile, its suffix after refusal has exactly the pure
terminal-environment law obtained by committing and revealing `none`.
`source_refusal_persists` proves that all supported whole-source executions
retain the refusal at the second checkpoint. These are source-law statements,
not just evaluations of a few selected policies.

`ToEventGraph.runBehavioral_backtranslate_source` packages the general
source/graph correspondence as an all-native-profile decoded-law theorem.
The graph program requires scope, freshness, and guard legality; this theorem
does not require or establish `WFProgram` admission. The probe instantiates
it in `graph_refusal_persists`: every supported terminal native run, under any
behavioral graph profile, has the same persistent-refusal property after source
decoding. It uses the existing compiler and native runner.

`PersistentDisclosurePolicy` checks the compiled graph's menu at the matching
eight-event configuration. For every actual graph history ending there, the
information-model choice is a singleton and every behavioral policy has the
same pure law at that site. The statement takes such a history as a premise;
it does not yet construct a graph history from the source-law witness.

The guard removes choice but leaves the administrative source events present.
There is no proof here that the public-message runtime can execute them without
the owner, or that their traffic can be erased from observations. The program
still fails literal `RevealComplete`; its accounting plan certifies the
conditional publication at the source boundary, not its runtime realization.
