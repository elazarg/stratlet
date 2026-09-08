# A road ahead

This is a non-binding working roadmap. It records a plausible route to a
realistic blockchain target and design questions to resolve along that route.
It is neither an implementation specification nor a claim that the proposed
theorems are true. Revise it in place as examples, proofs, and counterexamples
change our understanding; do not maintain it as a change log.

[Compilation design](compilation-design.md) states the architectural
commitments, [the implementation plan](ledger-expansion-plan.md) gives the
working gates, and [runtime models](runtime-models.md) records checked scope.
This document explores the choices within those boundaries. A proposal here
does not override a source semantics, an existing theorem, or an ownership
boundary.

## 1. Destination and shape

The objective is an executable game language whose properties can be analyzed
at its source and at each actual compiled representation, with proved
comparisons between them. A plausible artifact path is:

```text
checked minimal core
  -> event graph and compiled player controllers
  -> public-message application using abstract services
  -> transaction-facing contract and client controllers
  -> deployed EVM bytecode and client controllers
  -> the same artifact inside a named Ethereum ledger/network model
```

Every stage has native execution, control, observations, and outcomes. Its game
interpretation uses that execution rather than a separately maintained runner.
FOSG and other game formats remain optional analysis exports. The client stays
part of the compiled implementation: private values, opening witnesses, local
memory, and submission decisions cannot migrate into public contract storage.

Cryptographic proofs may realize selected ideal services under named
assumptions, relating their behavior rather than merely substituting an
implementation. They do not form a separate strategic tower. The eventual
target is a pinned protocol version and an explicit adversary, environment,
observation, and utility scope, not a
moving claim about "current Ethereum". Model correctness, realization under
security assumptions, and verification of deployed client binaries are
distinct deliverables.

There are two dimensions of development:

- **Representation depth:** replace a handler, wire format, service, or VM
  implementation with a more concrete one.
- **Modeled complications:** add a behavior, observation, resource effect, or
  environmental capability at an appropriate representation.

The first naturally gives compiler/refinement edges. The second should support
families of models, including dependency-closed subsets of complications where
their semantics permit it. We should not force either dimension into one fixed
list of levels or one universal model type.

A valid model configuration is distinct from eligibility of a particular
program, backend, and claimed property at that target. Removing a capability
used by the compiler can make that program unsupported, even when the smaller
runtime is well-defined.
Dependency closure concerns model construction; it does not promise a compiler
or the same preservation theorem for every program/configuration pair.

## 2. Model families and feature dependencies

### Different kinds of choices

Several useful simplifications are different mathematical operations:

| Choice | Example | What needs specifying |
| --- | --- | --- |
| Restrict a behavior | No explicit rebroadcast by an observer | Exactly which controllers/actions are restricted, and what execution remains |
| Select a service instance | Final append-only ledger; delayed local block views | Its executable behavior, observations, and service laws |
| Add an effect | Resource metering and charges | Changes to state, feasibility, observations, and outcomes |
| Refine a representation | Opaque authorization to signed wire encoding | Encoding, validation, failure behavior, and a simulation |
| Choose an analysis | Utility ignores fees | The readout/preferences; operational fee effects are still present |
| Restrict an environment | A delivery or inclusion bound | Which policies satisfy it, under which deviations and resource assumptions |

These choices should be available independently when meaningful, but they
should not all become Boolean switches. A zero-fee service, an unmetered VM,
and a utility that ignores fees describe different models or analyses.
Service hypotheses have their own order through the environment policies they
admit. Strengthening a delivery assumption is not the same operation as adding
an action, and the feature dependency order should not conflate them.

### Downward-closed selections

For a family of extensions, write `g <= f` when modeling `f` requires the
structure supplied by `g`. A selection `F` is admissible only if it contains
every prerequisite of each selected extension:

```text
f in F and g <= f  implies  g in F
```

This is a dependency condition, not a theorem that stronger models preserve
weaker models' properties. Example dependencies to exercise, not a frozen
feature catalog:

| Extension | Necessary structure |
| --- | --- |
| Identity-preserving envelope replay | A replayable envelope identity and broadcaster-local observation |
| Timeout resolution | A clock predicate, resolver actions, and application resolution behavior |
| Gas-dependent charging | Resource accounting, balances, and a charging rule |
| Cross-instance interference | Multiple addressed instances and a shared interaction context |
| Chain reorganization | Tentative branch state, rollback, and retained observation history |

The dependencies must not assume the desired defenses. Cross-instance replay,
for example, must be modelable without correct domain separation, so that the
need for domain separation can be demonstrated. Timed resolution does not
require a timely-inclusion guarantee merely to have a semantics.

Dependency closure may not be sufficient. Some service selections conflict,
and some compositions need additional compatibility conditions. An irrevocable
append-only ledger and reversible tentative execution should not coexist under
contradictory promises. They can instead be related through an explicit
finality interface. The useful family may be a partial order of compatible
instances and proved comparisons, rather than a complete lattice of flags.

For an advertised dependency-closed family, every compatible downward-closed
subselection should construct an actual model, with its stated relation to
the larger instance. Unsupported combinations should fail at configuration
construction, rather than acquire contradictory assumptions inside a theorem.
We need not advertise all possible selections before those constructions exist.

No universal `Runtime FeatureSet` record is proposed yet. Establish the
dependencies on concrete implementations before choosing a shared encoding.

### Disabling a feature has an exact meaning

**Replay.** Disabling the explicit replay action can leave fresh submissions of
the same payload by that same actor, repeated delivery, and other principals'
replay abilities.
Call this instance "no observer rebroadcast" if that is all it excludes. An
at-most-once transport service is a different instance with explicit admission
or deduplication behavior. Specify its identity scope: envelope, application
action, account nonce, or instance/domain/action. Application at-most-once
execution is a property to prove, not an action restriction.

**Quitting.** Three choices must remain distinct: analyzing non-quitting
policies, studying an ideal mandatory-participation model, and
proving that quitting is unprofitable under the actual game's preferences.
Restricting a strategy class proves a result for that restricted game, not an
unqualified Nash result for the full game. Ignoring quitting cannot delete
runtime silence while retaining claims about a runtime that permits it. The
selected source game's meaning and prescribed quitting consequences remain
unchanged; a runtime failure is identified with those consequences only by a
proved comparison. These restricted instances are useful results in their own right.

**Observations.** An analyst may study a game with a coarser observation
interface. That does not make a concrete player's richer observations disappear.
Using the result for the richer runtime needs a comparison or an incentive
condition. The same applies to erasing replay receipts or failed-call traffic.

**Costs.** Ignoring costs in utility does not eliminate their effects on
transaction validity, inclusion, or other players' behavior. An execution
abstraction that drops resource accounting needs its own justification.

### What can transfer between selections

Each extension should identify an embedding, projection, simulation relation,
or other appropriate comparison to its simpler instance. Merely observing that
one constructor set contains another is insufficient.

For example, restricting unilateral deviations preserves an equilibrium at a
fixed retained profile when its execution, utilities, and remaining deviation
payoffs are unchanged. The reverse direction needs bounds on the additional
deviations. Adding observations, fees, or an adaptive environment can also
change the execution of existing policies, so even this simple restriction
argument needs its premises checked.

Results should name their model instance or range over a family under explicit
hypotheses. If all required comparisons are parametric, one proof can cover
many downward-closed selections. Otherwise a result may hold only at selected
instances. Negative results also need an embedding argument before propagating
to other selections: an added mechanism can remove the original attack.

The aim is reusable proofs, not independent proofs of every combination and
not an automatic claim of monotonic strategic preservation.

## 3. Different implementation mechanisms for different details

Use the smallest mechanism that exposes the relevant operational behavior:

- **Ordinary parameters** for value types, identity types, resource
  bounds, and policies whose variation leaves the transition structure intact.
  A codec can be such a parameter behind explicit laws and fixed failure
  semantics; changing its decoding failures or collisions may instead require
  a representation comparison.
- **Small service interfaces with concrete instances** for commitments,
  authentication, clock access, and finality. Keep implementation data separate
  from proofs of particular service laws; an interface named "secure" is not
  evidence that a realization exists.
- **Action families or capability-indexed commands** when an extension adds
  choices or changes who controls them. Interpret them through the same native
  operations. A capability restriction must not require a hidden proof that an
  adversary's submitted payload will pass application validation.
- **State/effect combinators** where operations can genuinely be decorated,
  such as recording resource use. If a budget can halt execution, this is more
  than passive logging and must expose its interaction with the application.
- **Separate representations and lowering passes** for transaction envelopes,
  storage layouts, calldata, bytecode, and tentative chain execution.

A small action language may become useful once several real clients need
extensible event syntax. There is no reason yet to introduce a general-purpose
effect DSL, reproduce the rich Vegas frontend, or encode all future details in
one inductive type. Equally, a large dependent configuration record that
threads every possible flag through every theorem would be premature.

Operational orthogonality is a result, not a naming convention. Two extensions
need compatible state ownership, controls, observations, stopping behavior,
and service requirements. Their order may matter: metering before deduplication
can charge differently from metering afterward. Timeout resolution and opening
inclusion can race even if they are implemented in different modules.

For genuinely independent extensions, prove a commuting execution comparison
and the needed strategy/observation correspondence between composition orders.
For interacting extensions, choose and document an order or synchronization
interface. A parameterized public partial order of events may suffice; there
need not be one universal commutativity theorem.

The bounded policy game has two instances of the same native application,
with and without the explicit rebroadcast command, sharing the evaluator.
Its subtype of allowed commands suffices for their exact-law embedding;
no feature framework is needed for that comparison. Follow with an interaction
involving replay and application rejection/receipts. Let those proofs decide
whether further action indexing or a small service wrapper is the better API.

## 4. The public-message stage

The existing sealed-message fragment connects checked core programs through
their actual event graphs to a native message runner. Its support theorem and
concrete replay tests are a starting point, not a public-message strategic
preservation theorem. The full checked scope belongs in the runtime inventory.

The bounded instance supplies polling-local player policies and explicit
environment policies under a fixed invocation list. It proves ideal hiding
for a continuation that does not invoke the protected owner, and retains a
cleartext negative control. The next compiler comparison must connect emitted
controllers across their release boundary over that same runner. Preserve
authoring, withholding, malformed traffic, and replay. Distinguish the author
of an envelope from its broadcaster. A player's additional builder or network
capabilities must belong to that player's deviation scope, not be concealed
inside a fixed external environment.

An initial target is adaptive hiding up to the compiled release boundary:
changing an honest sealed value does not change the relevant opponent views
under the same admitted opponent and environment policies. Policies may react
to actual observed traffic; fixing a policy does not fix its realized event
sequence. Retain a cleartext negative control in the same model.

Silent events must not append artificial public ticks merely because an
information adapter uses global execution histories. Separate retained local
knowledge from application state and, eventually, from tentative chain state.
If the generic game library cannot represent the needed interface faithfully,
report the missing abstraction and develop it upstream rather than changing
the runtime to fit it.

### Opaque commitments and unsuccessful openings

Keep commitment and witness types abstract. A candidate interface includes
honest private creation and public verification of an opening:

```text
Commitment
OpeningWitness
verify : Commitment -> Value -> OpeningWitness -> Bool
```

This sketch is not a required Lean signature. Public admission, correctness,
binding, hiding, and failure behavior need separate specifications. Opaque
types alone do not establish secrecy against arbitrary mathematical policies.

The current ideal service records a value before commitment acceptance, and
the graph decoder obtains that value from its private table. A more permissive
service should admit appropriate opaque tokens without demanding that the
submitter already supply a source-value witness to the application. Some
tokens may never open successfully. An adversary's lack of a known witness is
also distinct from the mathematical nonexistence of an opening.

A service advertised as binding cannot merely accept an empty owner/slot
entry and allow it to be filled later: that would permit choosing the value
after observing other players. Its creation/opening timing and non-retroactive
binding need to be specified and justified. An intentionally insecure
late-binding instance is useful as a negative control; it must not discharge
a theorem's binding premise.

Such a service may require a relational or partial source correspondence that
retains unresolved commitments instead of immediately decoding a source value.
Deferring interpretation does not itself prove a legal source strategy exists.
If informed withholding creates a choice absent from the source, prove an
applicable weaker result or reject that source/backend/property combination.
Do not silently revise the source semantics or add a proof-of-knowledge
requirement to rescue the old theorem.

## 5. Transaction-facing contracts, settlement, and resources

Before instruction lowering, make the actual contract transition explicit:
instance identity, application action identity, commitment/opening requests,
public validation, success/rejection results, and persistent state. Add escrow
and settlement where the stated result needs them. A recorded entitlement to
withdraw is not automatically an executed transfer or an equivalent utility.

The transaction carrying a request has separate identity, signer, nonce,
destination, value, and resource budget. Ethereum checks the account nonce and
increments it before executing the message call; reverting that call does not
restore the transaction nonce. See the
[execution specification's transaction processing](https://github.com/ethereum/execution-specs/blob/master/src/ethereum/forks/cancun/fork.py)
and [message-call rollback](https://github.com/ethereum/execution-specs/blob/master/src/ethereum/forks/cancun/vm/interpreter.py).
These links identify a named fork for the example, not the future integration
target or a dependency already checked in Lean.

Thus replay of an unchanged Ethereum transaction and resubmission of an
application authorization in a fresh transaction are different operations.
Our replay example becomes a concrete execution only under the backend's
actual calling/authorization rules. A plausible initial backend authorizes
commitments by owner and allows anyone to submit a valid opening once known.
Owner-only calls are another legitimate choice with different capabilities.
Specify that choice above the cryptographic encoding boundary.

Timed resolution requires a clock predicate and an invocation. Identify the
resolver, its funding, and the ordering of late openings and resolution calls.
Prove that settlement implements the source's quitting consequences. Do not
manufacture automatic execution from the passage of time, or equate censorship
with voluntary quitting solely because one execution has the same payout.

A timely-inclusion assumption needs resource and interference preconditions
that remain true under the admitted deviations. Unbounded adversarial traffic
cannot silently consume another principal's promised service capacity.

Resource effects belong in native results. Rejection can preserve application
state while consuming gas; `REVERT` does not make execution free.
[EIP-140](https://eips.ethereum.org/EIPS/eip-140) specifies rollback and its gas
behavior. State-stuttering proofs therefore remain useful without erasing
costs, receipts, or their effects on later choices.

## 6. Bytecode and a realistic execution context

At the EVM edge, opaque application data receives concrete encodings. Prove
decoding, validation, storage layout, linking, deployment, and handler execution
against arbitrary admitted transaction inputs, not just generated calls.
Successful execution with sufficient gas and failures with insufficient gas
are different cases of the same runtime, not different convenient runners.

The extant EVM backend provides local components but its whole-runtime
refinement remains open and concerns a classical backend. It is not already a
lowering of this public sealed-message application. Reuse those components
only through a proved connection to the actual emitted handler.

Prefer a pinned, independently exercised EVM semantics to indefinitely
expanding a private gas-free subset. [EVMYulLean](https://github.com/NethermindEth/EVMYulLean)
is a candidate with an EVM model and conformance infrastructure; supported
forks and suitability require an audit. Conformance testing is evidence, not
a proof of equivalence to Ethereum. Generated code can stay small while the
target semantics handles arbitrary calldata and the admitted surrounding code.

External calls and reentrancy need explicit context boundaries. They may be
excluded from the first generated application, but actual transfers or calls
must not be proved using a model that suppresses their possible callbacks and
failures. Restrictions concern the artifact or a named context class, not a
claim that the full EVM lacks those behaviors.

The same artifact then runs inside transaction admission, blocks, network
delivery, tentative local views, and finality. There is no requirement that all
of these details be introduced in one step. Fork choice and finality have
their own operational structure; see the
[Ethereum fork-choice specification](https://github.com/ethereum/consensus-specs/blob/master/specs/phase0/fork-choice.md).

An important test before claiming reorganization support is an opening
observed in a block that later leaves the canonical chain. Application state
may roll back; recipient
knowledge persists. Finalized storage alone is therefore not an adequate
strategic observation projection. A plausible compiled discipline waits for
the relevant commitments to finalize before releasing openings, with explicit
deadline margins and security assumptions. Its adequacy still needs proof.

No opcode-correctness theorem establishes inclusion or finality. Under
indefinite censorship, prefix and safety results remain meaningful while
unconditional settlement generally fails. Stronger results need named service
assumptions or quantitative failure bounds.

## 7. Cryptography and the final strategic statement

Cryptographic realization fixes encodings, randomness, hashes, signatures, and
domain separation. It must cover malicious commitments/openings and replay,
not only honest encoding correctness. Hiding and binding alone do not supply
every extraction or simulation property a backtranslation might require.

Exact ideal hiding may become computational security with a security parameter
and an explicit adversary/test class. Computational indistinguishability is
not total variation or equality against unrestricted strategies. A bounded
experiment does not justify imposing a global finite horizon on an operating
chain. Infinite execution, settlement tails, and utility integrability need
their own semantics when a result requires them.

For compatible utilities, a plausible composition target is:

```text
target equilibrium error <= source equilibrium error
                          + honest-comparison error
                          + deviation-comparison error
```

The errors must be proved for the same admissible environment policy under
compiled play and deviations. They may include computational, service, and
utility discrepancies; do not condition away unfavorable failures. Full
outcome comparisons can transport bounds on harm to other players, whereas a
bound only on the deviator's utility does not automatically do so. Reflection,
coalitions, correlated recommendations, and sequential concepts each need the
corresponding comparison, not just an equilibrium-preservation label.

Some model selections may support exact laws; others only approximate or
profile-specific conclusions; others may admit a counterexample. This is a
useful result of the model family, not a reason to remove the troublesome
behavior from the richer instance.

## 8. Ownership and experiments that should guide the design

GameTheory owns generic policies, deviations, probability, comparisons,
composition, and utility transport. Runtime libraries own executable messages,
effects, and service models. Ledger/EVM libraries own transactions, VM and
chain semantics. Vegas owns the emitted artifacts and their correspondence
with the unchanged minimal source. The rich frontend remains independently
owned. Missing generic interfaces should be reported and developed upstream,
not copied into a Vegas-specific abstraction.

Before widening the supported source fragment substantially, exercise:

1. A small family with two optional behaviors, such as observer replay and
   explicit quitting/resolution: construct all four compatible selections with
   their prerequisites, reject an incomplete prerequisite selection, and keep
   unrelated metering, reorganization, and concrete-crypto imports absent.
   Model construction, compiler eligibility, and theorem availability should
   be separately testable.
2. The same compiled application with and without observer rebroadcast; prove
   the precise restriction relation and retain raw invalid submissions. These
   instances should not import unrelated fee, reorganization, or EVM models.
3. Adaptive observation-local hiding and a cleartext counterexample in the
   same native policy interface, without exposing a hidden global tick.
4. An accepted opaque commitment with no successful opening; distinguish this
   from source quitting and rule out choosing its value retroactively.
5. A published premature opening, replayed through the backend's real
   authorization/transaction rules; distinguish unchanged-transaction replay
   from a fresh transaction carrying the same application request.
6. A completed application action whose replay has no application effect but
   has a receipt/resource effect; check which comparisons survive composition.
7. A timed resolution/opening race and, separately, an observed opening on an
   orphaned branch. Neither state rollback nor timeout may erase knowledge.

These experiments can change the order of implementation. Extract a parameter,
combinator, or action abstraction when its independent instances and proof
obligations are understood. Keep the route to a realistic target visible
without making every nearer model pay for all of its details.
