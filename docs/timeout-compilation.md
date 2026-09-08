# Timeout resolution as a compilation mechanism

Timeout resolution belongs to the runtime implementation of a program's
specified nonresponse consequences. A deadline makes a resolution action
eligible; executing that action must implement those consequences. Passage of
time alone does not execute a program.

This document fixes the component boundaries and the next compiler obligations.
The checked scope is a dependency gate and atomic message inclusion, not a
timed implementation of the sealed-message compiler. Ethereum grounds the
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

## Concrete grounding: the shared activity timer

The adjacent compiler's
[Solidity emitter](https://github.com/elazarg/vegas/blob/aabcf72946aa7b88ac1703a95491ae2d2fe94cc4/src/main/kotlin/vegas/backend/evm/Solidity.kt#L77)
and
[Vyper emitter](https://github.com/elazarg/vegas/blob/aabcf72946aa7b88ac1703a95491ae2d2fe94cc4/src/main/kotlin/vegas/backend/evm/Vyper.kt#L111)
use a shared `lastTs` and a timeout window. The concrete clock is
`block.timestamp`, not block height. A missing dependency is overdue when
`lastTs + TIMEOUT < block.timestamp`. Its check marks the dependency owner
as bailed and resets `lastTs` immediately. Each successful action also resets
`lastTs`. Per-action timestamps are recorded but do not determine expiry.

Dependency checks precede the action body. Solidity evaluates the listed
modifiers in order; failure reverts their application-state writes as well
as the body's writes. See the
[modifier semantics](https://docs.solidity.org/en/latest/contracts.html#function-modifiers)
and [state-reverting exceptions](https://docs.soliditylang.org/en/latest/control-structures.html#error-handling-assert-require-revert-and-exceptions).
Such a revert does not erase the included transaction. Fees and other
transaction-level effects need their own model; [EIP-140](https://eips.ethereum.org/EIPS/eip-140)
does not make rejected execution free.

There is also a staging difference between emitters. The Solidity `action`
modifier marks the current action completed before dependency checks; the
Vyper emitter marks it after the body. The gate's `call` follows the Solidity
order. Both use the same timer-resetting dependency checks. Equating their
complete gate behavior would additionally require that the current action
is absent from its dependencies and that the body does not observe or exploit
the staging difference. No such emitter-equivalence theorem is supplied.

This algorithm has a within-call interference problem. Suppose a call checks
two missing dependencies of distinct, initially active owners:

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

`Interaction/DependencyGateLaws.lean` proves the shared-timer obstruction
for the abstract gate. The correspondence to the emitted modifier sequence
is a source-code inspection, not a checked emitter or Solidity refinement
theorem. The abstraction uses unbounded naturals and omits address checks,
other contract storage, finite-word overflow, gas, and external execution.
The adjacent emitter is not changed by these proofs.

## Immutable deadlines

`fixedExpiry` reads an immutable deadline for each dependency. A constant
deadline can instead represent one snapshot of the activity origin at call
entry. Neither choice is implemented by the inspected emitter.

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

1. Specify the emitted resolution entry point and deadline policy. Resolve
   the shared-timer defect before relying on its multi-dependency progress.
   Treat source handler elaboration as an explicit compiler obligation.
2. Integrate resolution with the same public-message application and native
   policy runner used by compiled commitment/opening traffic. Supply an
   explicit clock input, its observations, caller authorization, and the
   order of opening and resolution calls. Neither a testing horizon nor a
   clock advance substitutes for inclusion of a resolution action.
   First exercise the opening/resolution race: opening first prevents timeout
   resolution; resolution first prevents a later opening, according to the
   chosen entry-point policy. Keep a distinct nonresponse-resolution event,
   the original bound value, and both calls' observable success or rejection.
   Proving this operational rule does not yet identify its result with source
   quitting.
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
