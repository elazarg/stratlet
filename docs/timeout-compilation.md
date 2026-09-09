# Timeout resolution as a compilation mechanism

Timeout resolution belongs to the runtime implementation of a program's
specified nonresponse consequences. A deadline makes a resolution action
eligible; executing that action must implement those consequences. Passage of
time alone does not execute a program.

This document fixes the component boundaries and the next compiler obligations.
The checked scope includes a dependency gate, atomic message inclusion, and
a timed final-disclosure instance of the native sealed application. It is not
a source-to-timed-runtime strategic compiler theorem. Ethereum grounds the
design through the adjacent Kotlin compiler's generated contracts. Other
runtimes can supply the same components where their semantics fit.

## Operational components

| Component | Meaning and present scope |
| --- | --- |
| Clock | A reading supplied by the enclosing runtime. The gate uses natural-number units; it neither advances time nor publishes ticks. |
| Deadline policy | A predicate deciding whether a missing obligation is overdue. The two implemented instances use a mutable activity origin or immutable deadlines. |
| Dependency gate | Ordered checks stage completion and principal-exclusion effects. Exclusion discharges every dependency of that principal, not just the overdue obligation. |
| Application transaction | A handler returns an accepted next state or rejection. Rejection retains the initial application state. |
| Message inclusion | Publish a preexisting pending message and then run the application transaction. Rejection does not remove that publication or earlier observations. |
| Resolution behavior | The program-specific continuation, entitlement, or settlement effected by a successful resolution. No general compiler correspondence for it is established here. |

These are small functions and parameters, not a universal runtime configuration
language. Atomic application execution is a particular supported boundary;
a non-atomic runtime needs a different execution model and comparison. Clock
units, clock visibility, permitted advances, and inclusion guarantees belong
to the enclosing runtime, not to the gate's arithmetic.

`Interaction/DependencyGate.lean` stores completed action identities,
excluded principals, and the last activity reading. A call checks actor
eligibility and action freshness, stages action completion, checks its ordered
dependencies, and evaluates a body-acceptance predicate. Success records the
current activity reading. Failure returns no staged state to commit.

The compiled entry point must supply the authenticated actor, recorded action
identity, and dependency list. These are fixed entry-point metadata, not
caller-chosen labels. The raw gate API does not enforce this restriction or
authenticate its arguments. Actor and action owner are
separate because registration can execute under one role while completing an
action for another. An instance must establish their actual relationship.
The body predicate captures rejection after staged checks; it does not model
other application writes, reentrancy, transfers, or resource exhaustion.

`Interaction/TransactionalInclusion.lean` supplies the separate atomic
boundary over `MessagePool.includePending`. A handler returns `some next` or
`none`; the result records acceptance, rejection, or a missing message id.
An included rejected message remains on the public ledger. Sent histories and
recipient inboxes are unchanged by inclusion, so previously delivered content
remains available. This component does not yet specify a policy observation
interface for receipts, fees, account nonces, or finality.

## Concrete grounding: the call-entry activity snapshot

The adjacent compiler's
[Solidity emitter](https://github.com/elazarg/vegas/blob/47734f73e3ad22a550bec299b0bfce1c95105316/src/main/kotlin/vegas/backend/evm/Solidity.kt)
and
[Vyper emitter](https://github.com/elazarg/vegas/blob/47734f73e3ad22a550bec299b0bfce1c95105316/src/main/kotlin/vegas/backend/evm/Vyper.kt)
use a shared `lastTs` and a timeout window. The concrete clock is
`block.timestamp`, not block height. A missing dependency is overdue when
`origin + TIMEOUT < block.timestamp`, where `origin` is one snapshot of
`lastTs` taken before the call's dependency checks. Each overdue check marks
the dependency owner as bailed and resets `lastTs` immediately, but every
check in that call uses the same snapshot. Each successful action also resets
`lastTs`. These writes remain visible to the action body. Per-action
timestamps are recorded but do not determine expiry.

Dependency checks precede the game-action body. In Solidity they follow the
authorization and action-completion modifier preludes. Failure reverts staged
application-state writes as well as the body's writes. See the
[modifier semantics](https://docs.solidity.org/en/latest/contracts.html#function-modifiers)
and [state-reverting exceptions](https://docs.soliditylang.org/en/latest/control-structures.html#error-handling-assert-require-revert-and-exceptions).
Such a revert does not erase the included transaction. Fees and other
transaction-level effects need their own model; [EIP-140](https://eips.ethereum.org/EIPS/eip-140)
does not make rejected execution free.

There is also a staging difference between emitters. The Solidity `action`
modifier marks the current action completed before dependency checks; the
Vyper emitter marks it after the body. The gate's `call` follows the Solidity
order. Both use a call-entry snapshot for expiry while retaining activity
writes during dependency checks. Equating their
complete gate behavior would additionally require that the current action
is absent from its dependencies and that the body does not observe or exploit
the staging difference. No such emitter-equivalence theorem is supplied.

The [deployed Solidity regression](https://github.com/elazarg/vegas/blob/47734f73e3ad22a550bec299b0bfce1c95105316/src/test/kotlin/vegas/eth/tests/EthDependencySnapshotTest.kt)
checks that one overdue call persists both missing owners' exclusions, action
completion, and its activity timestamp. A call exactly at the deadline
rejects and retains neither staged completion nor exclusion. Vyper has
generated-code/golden coverage, not a deployment test. These tests are
implementation evidence, not a checked compiler-to-VM simulation.

## Re-reading a mutable activity origin

`slidingExpiry` instead reads the updated activity origin on every dependency
check. This policy has a within-call interference problem. Suppose a call
checks two missing dependencies of distinct, initially active owners:

1. If the shared deadline has not passed, the first check rejects.
2. If it has passed, the first check stages exclusion and sets `lastTs` to
   the current reading.
3. The second check now compares the current reading with itself plus the
   timeout window, so it cannot expire the second owner. It rejects.
4. The application transaction discards the first exclusion as well.

Waiting longer cannot make this same batch succeed from unchanged state.
Other calls may change that state; this is not a theorem that every such
contract is permanently stuck. Successful unrelated actions can also extend
the shared deadline, a distinct policy choice exercised by the tests.

`Interaction/DependencyGateLaws.lean` proves this obstruction for the abstract
gate. It distinguishes re-reading staged state from the emitters' call-entry
snapshot. The abstraction uses unbounded naturals and omits address checks,
other contract storage, finite-word overflow, gas, and external execution.
Connecting a generated handler to the gate remains a separate refinement
obligation.

## Immutable deadlines

`fixedExpiry` reads an immutable deadline for each dependency. A constant
deadline represents the call-entry snapshot used by the emitters. This
relationship is by inspection; there is no checked emitter correspondence.
An independently fixed deadline for each obligation is a separate policy.

The gate laws prove that checking succeeds when each dependency is already
completed, belongs to an initially excluded principal, or has passed its
immutable deadline. This is a check-level progress result, conditional on
that readiness premise. The enclosing call can still fail its admission or
body checks. It also still needs someone to submit it and a runtime that
includes it.

When every initially missing requested dependency is overdue, the exact result
also retains the completed set, excludes precisely the initial exclusions
plus the owners of those missing dependencies, and records the current clock
reading if any such dependency exists (otherwise retaining the initial reading).

Snapshotting the shared origin removes within-call timer interference;
it does not establish per-obligation deadlines or prevent other successful
calls from postponing resolution. A per-obligation deadline map supports the
latter policy. Both retain the gate's principal-wide exclusion rule. Changing
that rule is a separate operational choice with different strategic effects.

`InteractionTests/TimeoutGate.lean` checks the strict deadline boundary,
shared-timer failure, immutable-deadline success, body rejection, activity
reset, and principal-wide exclusion. Its actual submit/deliver/include
executions distinguish rolled-back application state from retained public
messages and recipient observations. These are runtime-component tests, not
compiled source fixtures or a source-equilibrium result.

## Connecting resolution to source meaning

### The integrated final-expiration instance

`Interaction/SealedTimeout.lean` attaches one named opening checkpoint and an
immutable absolute deadline to an existing `SealedProgram`. Ordinary traffic
uses `SealedProgram.validateMessage?`, the same pool-independent validator
used by the untimed application. All messages, including failed expiration
and opening calls, pass through atomic pool inclusion and produce public
success/rejection receipts. The caller cannot choose the checkpoint metadata.
Expiration is permissionless but must pass the checkpoint's original public
opening-readiness checks and the strict deadline test.

The chosen policy accepts a late valid opening until expiration has actually
been included. Expiration first stops subsequent protocol-event acceptance;
opening first disables expiration while allowing the program to continue.
Expiration preserves the service table and original public events. Further
network activity and registration of new service bindings remain possible;
occupied bindings remain unchanged. This policy
does not synthesize an opened value, pay a refund, discharge other graph
dependencies, or implement role-specific abandonment while other players
continue. Those are application/compiler responsibilities, not consequences
of the word timeout. This instance is a final-failure policy, distinct from
the adjacent emitter's principal-exclusion dependency gate.

The environment advances an explicitly public monotone natural-number clock.
Neither advancement nor exhausting a finite analysis horizon resolves the
checkpoint. The native policy game in `Interaction/SealedTimeoutPolicies.lean`
allows local-history-dependent register, submit, replay, and wait choices;
the environment adaptively advances the clock, delivers, includes, or waits.
It sees wire state and public application data, but not the hidden commitment
table. Polling uses a fixed finite invocation list and does not imply timely
inclusion. The policy-law module proves every supported result has its actual
native execution witness and preserves already occupied service bindings.

`VegasTests/PendingTimeout.lean` instantiates this extension with the program
emitted from `PendingSource`. Its race executions start with actual native
registration, commitment submission, and inclusion. They compare opening and
expiration orders after delivery, retaining the earlier inbox content even
when the opening is rejected. This connects the runtime experiment to the
actual compiled prefix; it does not identify expiration with that source's
terminal nullable value.

`WFProgram.sealed_timeout_run_source` proves that every finite raw timed run
decodes to a reachable compiled graph prefix. `sealed_timeout_policy_source`
lifts this result to every supported outcome of the native policy game.
When the decoded graph prefix is terminal, both reconstruct a written-order
source execution with matching terminal bindings and payout evaluation.
The decoder omits traffic, receipts, clock, and resolution: these are
support-level execution theorems, not observation or strategy equivalences.
Expiration may leave an incomplete graph prefix. A completed disclosure
checkpoint likewise need not complete the rest of the program.
`VegasTests/PendingTimeoutSource.lean` instantiates terminal reconstruction for
all nullable input pairs and both commitment inclusion orders after a real
clock advance past the deadline. With no expiration included, both openings
remain valid and the complete decoded graph reaches its source outcome.

`VegasTests/PendingTimeoutPolicies.lean` holds the players and invocation
schedule fixed while two environment policies choose opposite inclusion
orders. Both deliver the valid opening; their exact resolution laws are
respectively completion and expiration. This demonstrates an inclusion-order
effect even when the owner has submitted its bound value.

`Interaction/SealedTimeoutHiding.lean` relates paired raw executions whose
service contents differ only in a protected principal's occupied values. It
preserves equality of the declared views, including clock, resolution, and
success/rejection receipts, before that principal sends an opening. The
retained carrier must already exclude its opening messages and the common
trace must contain no further commands from that principal. This is a raw
noninterference theorem; lifting it to adaptive policy laws and proving an
emitted controller's disclosure discipline are additional obligations.

### Source correspondence still required

The current minimal source makes `reveal` publish the already sealed value.
A nullable choice of `none` is chosen at its source decision; it does not
authorize replacing a previously chosen `some value` after withholding a
later opening. The source and its well-formedness discipline remain unchanged.

The adjacent backend implements absence through completion flags and
principal exclusion. Bailing an owner neither fills the missing field nor
marks that field completed. Relating this to source nonresponse handlers
requires the handler elaboration and downstream field accesses to respect
the intended optionality. The gate alone has no field-value or payoff semantics.

The existing selective-publication witness also retains its force: a deadline
can settle withheld disclosure, but does not make an informed decision after
seeing an opponent's opening identical to an earlier nullable choice. A
source/backend pair needs either an actual corresponding source decision or
a proved weaker comparison, for example an incentive condition bounding
informed quitting. Hiding and binding do not supply that comparison by
themselves. See [runtime models](runtime-models.md) and the
[quitting compilation contract](quitting-compilation-contract.md).

## Next integration gate

### Initial defaults and privately prepared commitments

Private commitment preparation, public submission, and ledger acceptance are
separate operations. An owner can prepare a value and withhold its submission.
A source-designated initial default therefore cannot be implemented by
overwriting that private commitment, treating it as submitted, or making a
private preparation step publish an application decision.

The disclosure application records the accepted source binding as either an
owner-submitted opaque commitment or an explicit public default. An included
permissionless initial expiration chooses the latter without modifying private
storage or forging an owner-authored message. Subsequent validation uses the
accepted alternative, not an unsubmitted commitment the owner prepared earlier.
The generic publication kernel takes its opening validator independently of
the source guard: verification of a captured commitment and comparison with a
public default are separate implementations of that interface.

The initial deadline is the configured window from clock-zero initialization.
Early calls and calls after a binding is accepted reject; a late ordinary
binding may win until expiration is included. The source default is `false`,
the existing initial action used by the finite sealed-offer interface. It is
not a new initial quit branch or the richer frontend's persistent abandonment.
The checked full native execution contains no owner action: the responder's
calls expire initial selection, expire disclosure after source chance, and
respond. Its source execution uses that exact initial default. Separate checks
retain private preparation and reject attempts to bind or disclose a different
prepared value after the default. The pure owner controller reconstructs its
continuation choice from the accepted disposition rather than its unsubmitted
private intention; a local recovery theorem checks that behavior even with an
empty local history. The responder controller submits initial expiration when
its public deadline is overdue. Whole-execution opportunity and settlement
proofs remain open; the specified honest inclusion script does not take the
default branch.

The response default has an actual permissionless entry point. Successful
publication arms a response window, and an included overdue call selects the
source's rejection action `false`. A repeated publication cannot reset that
window; early calls and calls after response completion reject. Clock advance
does not execute the call. The native owner-disclosure/response-expiration
execution has the expected chance law and public receipts without any responder
action, and the handler has a written-source support theorem for arbitrary
public payouts. The pure owner controller submits response expiration after
observing its deadline, but settlement under deviations remains unproved.
Deadlines enable the fallback; a normal response may win until expiration is included.

There is a separate commitment-validity boundary. The disclosure application
accepts an opaque handle without testing whether it has an opening, and
captures an immutable private verifier at inclusion. Acceptance and subsequent
marker/chance readiness reveal no validity result. Later preparation cannot
repair an accepted unopenable binding: every native continuation that resolves
its publication selects decline. The checked hostile execution delivers and
rejects a late opening before an included expiration continues to the responder;
the failed message and its rejection receipt remain observable.

The snapshot point is inclusion, not creation of a cryptographic packet. This
ideal instance still permits preparation while a handle is pending. Its
realization must relate that freedom, actual packet binding, and native
observations; immutable accepted state alone does not prove the relation.
An unopenable snapshot's source-support witness is `false`, with decline at
publication. It is a legal source reconstruction, not an operational initial
default, a settlement guarantee, or a strategic backtranslation.

Public fallback and failure calls add observations. Their source-value
legality does not prove strategic preservation, but their visibility alone
does not refute unilateral Nash preservation either. Compiled opponents may
ignore auxiliary traffic, and a deviator may already know its own fallback.
The comparison must establish the actual observation and deviation law. A
claim of impossibility needs a witness for that claim and policy class.

### Whole-program comparison

The conditional-publication component supplies a local source-resolution
bridge without adopting the final-expiration instance's global stop policy.
`ConditionalOpeningSite` derives the paired choice/reveal metadata from a
source accounting certificate. `ConditionalResolution` proves accepted
results perform legal source steps and every legal source choice has a
canonical accepted request, under the appropriate soundness/completeness
directions of the application validator. `ConditionalExecution` proves the
accepted effect follows the two actual compiled graph kernels. The compiler
must also maintain source/store and original-handle correspondence.

This component distinguishes commitment verification from program legality.
An opening can verify correctly but be forbidden by a continuation guard after
earlier quitting. The application supplies that check; source well-formedness
does not force all bound openings to remain legal. Publication also retains
previously delivered payloads, including an opening overtaken by expiration.
These facts do not yet supply a whole-program timeout implementation or a
strategic comparison.

The shared `DisclosureApplication` instance includes binding, forced marker,
public chance, publication, and the responder's continuation. Decline and
included expiration resolve publication without terminating that continuation.
Its publication deadline is armed by the public sample. Arbitrary supported
policy runs have checked source-prefix support; specified pure controllers and
an inclusion script have the actual AST's complete outcome law from empty.
Every nontrivial source decision in this finite instance has an explicit
nonresponse handler. The forced marker and chance are environment-triggered
fixed application work. Pure timeout-driving controllers and an instantiated
slotted inclusion service are available. Players can react to pending delivery,
and reserved capacity drains the queue even under arbitrary player policies.
The service clock advances once per complete cycle. Stable pending resolvers
also have application-progress proofs for initial binding, ordinary response,
and all three expiration calls. These phase results start with an already
pending, ready request. The remaining proof must establish timely controller
submission, unchanged source choices, and settlement under unilateral deviations.
The instance does not yet provide the whole-program timeout contract below.

#### Service settlement proof targets

For the slotted service, number cycles from one. From clock-zero initialization,
`DisclosureServiceClock.service_schedule_clock` gives clock `c` after `c`
complete cycles, independently of player policies and admitted inclusion choices.
The service capacity theorem gives an empty queue at each cycle boundary.
The following are mathematical proof targets, not exported Lean settlement
results. For a window `w >= 1`, the proposed complete-cycle bounds are:

| Policies | Settlement bound |
| --- | --- |
| Both compiled pure controllers | 3 |
| Arbitrary owner, unchanged responder | `2*w + 4` |
| Unchanged owner, arbitrary responder | `w + 3` |

The one-cycle lag between observing resolution and acting explains the window
condition. With `w = 0`, an expiration can be eligible in the same inclusion
phase as an unchanged player's first normal publication or response. Ordering
expiration first can select the default. This race needs a checked negative
control, and the positive proof must exclude it without restricting the
deviator's raw commands.

`Interaction/MessageApplicationProgress.lean` proves the inclusion-phase
invariant: the concrete resolver envelope remains pending, or its application
milestone already holds. Its local premises require milestone persistence,
readiness preserved up to resolution, and resolution when that envelope is
selected. Sufficient reserved inclusion capacity then implies the milestone,
including for randomized selectors that inspect payloads. The result uses the
existing native policy runner and permits arbitrary competing pending messages.
It does not permit new arrivals during the reserved inclusion phase.

`DisclosureServiceResolution` and `DisclosureResponseResolution` discharge
those local premises for canonical initial binding, ordinary response, and
overdue initial, publication, and response expiration. These application
instances start from a pending request with the required phase invariant and
deadline. A competing call may establish the milestone first; the conclusion
therefore asserts resolution, not preservation of the request's chosen value.
Ledger membership alone would not suffice: it neither implies acceptance nor
distinguishes earlier publication from a pending replay. Controller history
must still connect a one-shot submission flag to a pending-or-resolved state.
Timely submission and exact unchanged-player choices remain obligations before
deriving the bounds or strategic laws.

#### Deviation-law proof targets

The intended comparison fixes the adaptive inclusion selector, assumes the
slotted service and `w >= 1`, and uses a sufficiently long schedule (the proposed
uniform bound is `2*w + 4` cycles). Neither an arbitrary environment nor the
inclusion predicate alone supplies the required opportunity guarantees.
The first source endpoint may use pure compiled policies with behavioral source
replacements, but draft-level coverage requires randomized source profiles too.

After settlement and exact unchanged-player choices, reconstruct laws rather
than choosing an independent source witness for each supported outcome:

- For an owner replacement, factor the decoded law into an initial binding
  distribution, independent source chance, an opening kernel conditional on
  binding and signal, and the unchanged source response kernel. Legal openings
  are decline or the retained binding. Unopenable accepted commitments use the
  existing decoder's `false` witness and permit only decline.
- For a responder replacement, retain the unchanged owner's initial and
  disclosure laws and reconstruct a response kernel depending on signal and
  actual publication. With a randomized honest binding, this requires proving
  conditional independence from that binding given those public inputs; a
  fixed-secret example cannot establish that information-flow property.

Finite-law disintegration can construct these kernels once their factorization
properties are proved. Zero-mass observations need legal fallback policies.
The candidate translation is profile-local and environment-dependent, not a
uniform translator for all opponent profiles. Runtime traffic and receipts
remain observations of the actual policies but are not equated with source
terminal environments. Randomized controllers must retain their own sampled
initial choice and sample each later source decision once; extra polling must
not create resampling opportunities for compiled play. These obligations are
not discharged by the scripted honest law or by source-support correspondence.

1. Relate the emitted resolution entry point and call-entry deadline policy
   to the gate and complete handler semantics. Treat source handler
   elaboration as an explicit compiler obligation.
2. Integrate conditional publication into the chosen source's complete public
   application and controller, including its actual continuation and
   observations. Do not reinterpret the final-expiration instance's global
   failure as that continuation. Preserve the original bound value and both
   calls' observable success or rejection throughout.
3. Prove that a supported source program's resolution executes its prescribed
   continuation or settlement while retaining bound values and observations.
   Eligibility for this backend is distinct from source well-formedness.
4. Establish the relevant strategic comparison against the same opponent
   and environment policies. State service assumptions under deviations,
   distinguish voluntary withholding from censorship, and retain unresolved
   outcomes when progress is not guaranteed.

The next gate is met by an actual compiler instance and a checked comparison
or precise obstruction in that integrated game, not by these component laws
alone. Later clock, cryptographic, transaction, and VM realizations refine
this path under named assumptions. Runtime-general interfaces remain outside
Vegas lowering and outside the Ethereum-specific implementation.
