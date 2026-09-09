# Compilation through operational games

## Purpose and status

This document specifies the compilation architecture and proof boundaries.
It is a design contract, not a claim that all its targets or proofs exist.
[The implementation plan](ledger-expansion-plan.md) gives acceptance gates;
[the current runtime inventory](runtime-models.md) records checked results.
The non-binding [road ahead](a-road-ahead.md) explores representation lowering
and composable, dependency-closed families of runtime complications.

The objective is to answer strategic questions about the operational models
in which compiled programs execute. Each target has native execution, control,
and observation semantics. Its strategies and game interpretation use those
semantics. A strategic theorem about another, idealized execution model applies
only after a proved connection to the actual target.

Ethereum is the grounding target, not the definition of a runtime. The
architecture must support an eventual connection to a complete Ethereum model
and to other runtimes without importing Ethereum or Vegas into their
foundations. Describe each concept at the least specific level supported by
its semantics and actual uses: clocks and atomic application updates can be
runtime-general; EVM opcodes and Ethereum transaction admission cannot.
Introduce a shared interface when a proof or concrete instance needs it,
not a speculative framework for every possible target.
Whether a particular runtime preserves a particular source property remains
a theorem or an impossibility question, not an architectural assumption.

## 1. Native representations and their game interpretations

```text
Core program -> graph protocol -> public-message runtime -> ledger/VM instance
     |                |                   |                        |
 source game       graph game         runtime game             concrete game
```

The vertical arrows are interpretations of the representation above them, not
another implementation pipeline. Every horizontal edge relates the executions
and, for each advertised strategic property, the corresponding games.

Vegas is itself a game-description format. FOSG, EFG, and other known formats
are analysis exports from stages that support them. No export is a mandatory
semantic owner or compiler IR. Format-specific assumptions and preservation
results belong to that export edge.

There is one authoritative execution semantics per representation. A game
adapter reuses it; it does not independently implement a more convenient
runner. Distinct source and target representations may have different native
runners, and their correspondence is proved. An executable interpreter and a
mathematical denotation may coexist with an explicit correctness theorem.

Use GameTheory's existing separation:

- `GameSignature` and `GameForm`: strategies, outcomes, and induced play laws;
- `ExecutionProtocol`: controlled transitions when this interface fits;
- `InformationModel`: local information and policies for those transitions;
- preferences, utilities, and `DeviationScheme`: analysis of those game forms.

A native language may interpret directly into `GameForm`; it need not first
be encoded as an execution protocol. An operational runtime may expose an
adapter to `ExecutionProtocol`, but that adapter must preserve the native
events, activation, and observations. Do not change the modeled system merely
to satisfy a library interface. GameTheory's D7/D8 design favors explicit
preservation levels and small, exercised transformations, not a universal
semantic record or speculative certificate hierarchy.

A direct game-form interpretation has the same locality obligation: strategy
arguments contain exactly the principal's available information, not global
execution state. Bypassing `InformationModel` cannot bypass this requirement.

## 2. Data associated with a compilation stage

The following are responsibilities, not mandatory fields of one large record.
Keep executable code, proof data, and analysis parameters separable.

| Responsibility | Required meaning |
| --- | --- |
| Artifact | Native source, graph, protocol configuration, contract, or bytecode; retains code needed by subsequent lowering. |
| Execution | Initial states, raw actions, transition results, histories, and stopping or continuation behavior. |
| Control | Principals and the capabilities each controls; unresolved environmental choices are explicit ports. |
| Information | Initial knowledge and event observations at each recipient, including retained local memory. |
| Outcomes | Native histories and the readouts relevant to a claim; payouts and asset effects are distinguished. |
| Analysis | Preferences, valuations, private-type/prior parameters when needed, deviation classes, and queries. |
| Requirements | Explicit runtime assumptions and compiler eligibility conditions, each with its proof obligation. |

A program denotes a game form before an analyst chooses utilities. A runtime
with open environment ports denotes a family of game forms after those ports
are supplied with admissible policies. Environment coordinates may be present
in the execution without being players whose equilibrium is tested.

For the first runtime, assign every capability to a principal, then partition
principals into game players and external environment principals. The full
informed execution has all those principals as coordinates. Fix local policies
`eta` for the external coordinates; a player profile fills the remaining
coordinates. The induced player-only `GameForm` runs that assembled profile
through the same evaluator. It introduces neither an environment utility nor
a second transition law. If a player owns a builder capability, that capability
belongs to its player coordinate, not to the fixed external profile.

Non-executable analysis expressions and proof obligations may accompany an
artifact. The compiler transports their interpretation, not just their text.
They do not grant the executable program additional knowledge or eliminate
adversarial behavior. The theorem states which queries and assumptions were
transported and which remain obligations. A symbolic condition is not evidence
that the runtime satisfies it.

No mandatory finite-state, finite-horizon, perfect-recall, or real-utility
field belongs in the general stage interface. Introduce each capability where
its theorem or executable algorithm needs it. The `Vegas.BoundedGame` wrapper
is a bounded analysis convenience, not the foundational type for all targets.

## 3. Proof obligations on a compiler edge

For artifacts `s` and `t = compile(s)`, distinguish four obligations. They
refer to the same artifacts, execution models, and observation definitions.

### Execution and representation

Relate initial states, transitions, outcomes, and relevant traces. A target
event may implement one source event, several events, or an administrative
stutter. Intermediate representations need explicit state or trace relations;
a total terminal decoder is not always the right operational interface.

A stuttering state projection says nothing by itself about an event's
information effect, cost, or effect on progress. Failed calls and empty blocks
must not be erased from player information merely because application state
does not change. Reordering, rollback, and batching need their own laws.

### Information and strategies

Compile policies using only information available to the executing principal.
The compiled policy is not allowed to inspect the environment's strategy or
another player's private policy. It must work in all environments covered by
the theorem.

Target deviations range over the capabilities of the target model, including
raw invalid inputs and observation-dependent behavior. Backtranslation is a
mathematical witness, not a restriction on the adversary's runtime code. Its
source policies must be information-local. A proof reconstructing private
memory from source information must justify that reconstruction for the full
target observation history.

State the strength actually proved:

| Evidence | Consequences requiring further stated hypotheses |
| --- | --- |
| Compiled-profile outcome laws | Correctness of compiled play; no general equilibrium conclusion. |
| Uniform unilateral outcome simulation | Unilateral bounds and Nash transport with compatible preferences; stronger recommendation results where proved. |
| Profile-local finite-mixture deviation laws | Expected-utility Nash/approximate Nash and linear observable bounds; not automatically arbitrary-preference or CE transport. |
| Recommendation-local deviation correspondence | CE-related transport for the specified recommendation semantics. |
| Continuation/information correspondence | Input to sequential solution-concept proofs, not a consequence of terminal-law equality alone. |
| Honest-context or coalition correspondence | Protection against the specified joint deviations; not inherited from unilateral results. |

Preservation and reflection are separate directions. Reflection at compiled
profiles is not a characterization of all target equilibria. Exact, approximate,
and computational comparisons are distinct claims.

### Preferences and queries

Retain the native outcome before choosing a coarser readout. Prefer exact
outcome-law statements when feasible, then derive results for the relevant
tests or preferences. A utility of decoded source outcomes is one instance;
gas, latency, information release, and capital exposure can require additional
target-trace utility. Prove the associated incentive condition or error bound.

Payout syntax can supply a default valuation. It does not fix all preferences
or establish that ledger transfers actually occur. Private valuations and
priors are analysis parameters unless the source explicitly makes them
executable data. Merely recording them in an artifact gives no runtime access.

### Assumptions and environment control

Write the environmental quantifiers before proving the edge. For example, an
exact uniform source/target comparison may require a causal environment map
`E` such that, for every admitted target environment `eta`,

```text
decode_* playTarget(eta, compileProfile sigma)
  = playSource(E eta, sigma)
```

The same `eta` and `E eta` must be used when comparing a profile with its
unilateral deviations. They are policies and may react differently to changed
messages; fixing them does not fix their realized event sequence. An abstract
environment must not be chosen afresh to repair each profile or deviation law.
The selected correspondence states any allowed dependence of a backtranslation
on the environment, profile, or horizon.
Every alternative in a deviation mixture also uses that same source
environment. Mixing over alternative source environments would be a different
comparison and cannot silently enter a composition proof.

If the source has no environment port, removing target environment influence
is itself part of the theorem. Censorship cannot be reclassified as voluntary
source quitting just because the final payout agrees on one execution.

Lower-stage guarantees must imply the assumptions needed by the upper stage,
for all deviations in scope. A timely-inclusion guarantee for uncongested
honest traffic is not sufficient for a theorem admitting hostile congestion.
Assume-guarantee contracts must identify who provides the guarantee, its
preconditions, and why those preconditions persist under the claimed behaviors.

Capabilities are assigned to principals. If a game player also controls a
builder, oracle, or network role, its allowed deviation must include those
capabilities or explicitly state the disjoint-control restriction. Fixing a
separate environment coordinate must not conceal an adversary-owned capability.

## 4. Composition and insertion of intermediate stages

Stages are named native representations, not numeric levels in a closed sum.
A compiler pass imports its source and target carriers; a target carrier does
not import its compiler. Proof modules depend on the pass and the mathematical
interfaces they use. General game analysis depends on neither endpoint syntax.

An edge exports its concrete translation and the preservation facts needed by
its consumers. Different passes need not share one monolithic certificate.
Composition requires agreement on:

- the actual intermediate artifact and game interpretation;
- policy and principal maps, including which capabilities may deviate;
- outcome/trace relations and preference interpretations;
- environment correspondence and discharge of service requirements;
- observation and strategy scope, horizons or progress conditions;
- the comparison notion and, when quantitative, its error budget.

The composition must recover the named strength, not just the same endpoint
types. In particular, a profile-local mixture edge cannot discharge a later
uniform, recommendation-local, continuation, or coalition obligation.

Exact uniform simulations can compose by composing maps and laws. A
profile-local mixture does not become uniform through composition. Trace
relations may compose relationally rather than through total decoders.
Approximate comparisons need their own composition theorem; computational
indistinguishability must not be treated as statistical equality.

To replace `A -> C` with `A -> B -> C`:

1. Define `B` with its own execution and information semantics.
2. Implement the two passes and prove their endpoint-specific obligations.
3. Establish that their composition realizes the intended final artifact, or
   prove correspondence to the chosen new final artifact if code changes.
4. Rebuild the required `A -> C` result by composition, with explicit changes
   to hypotheses, deviation scope, or error. Reprove any property not supplied
   by the new edges; do not inherit it by a common result name.
5. Update all consumers and audits. Keep no obsolete wrappers or aliases.

A layer introducing genuinely new information may invalidate an upper-level
property. Extensibility means this can be expressed and analyzed locally, not
that every inserted layer is automatically strategy-preserving.

## 5. The first public-message target

Start with raw messages, recipient-local delivered views, a pending inventory,
and a published ledger. Submission creates a message; delivery exposes an
existing message to an observer; inclusion selects an existing pending message
as the next public ledger entry. Inclusion is the scheduler's action and does
not consult the sender again. The first kernel uses a shared published ledger;
delayed receipt of ledger entries is a separate observation refinement.

The first security experiment must distinguish legal cleartext transmission
from compiled commitment traffic. Prove what an observer can learn from
pending messages before a relevant decision, and what opening permits later.
An ideal commitment service must be explicit; it is not an implementation of
cryptography. Application validation, quitting resolution, service guarantees,
clocks, fees, and consensus belong in separate layers when their proofs need
them, not mandatory fields of this kernel.
The [ledger design](ledger-expansion-design.md) details the event and service
contracts; its richer ledger features need not all be implemented at once.

The mathematical state may track all messages and delivery events. No policy
receives that whole state unless its modeled capability permits it. Publicly
transmitted data is neither private-by-default nor instantaneous common
knowledge. Local observations identify what each recipient has received and
what the recipient can infer about dissemination.

Silent delivery events must not generate a global observable tick through the
information adapter. An empty signal appended to every local history can leak
event counts. Native controller decisions and inclusion of pre-existing
messages are different events. The latter needs no hidden sender-activation
change. If a later model genuinely hides controller consultation, evaluate
the information-interface requirements at that layer; do not invent shared
notifications to satisfy a library adapter.

Use the commonly observed signal channel only for actual shared observations;
recipient-local delivery belongs to per-recipient signals. Signal definitions
must factor through explicit recipient projections, with noninterference
proofs, even if the underlying library callback can access the full event.
Submission acknowledgments, remote delivery, block receipt, and finality
notifications are separate observations. A clock field in global state is not
automatically information available to a player.

Raw submission must not require an omniscient proof that a hidden guard holds.
Validation, conflicts, rejection, retries, and receipts are transitions. A
message delivered to a recipient remains known after contract rollback unless
the observation model has a justified forgetting mechanism.

Source reconstruction at the public commitment layer is proof-facing. A relation
between native application state and graph configurations may supply a hidden
source-value witness, including for an accepted permanently unopenable binding.
Runtime handlers operate on their actual stored resources and public metadata;
the reconstruction witness is neither stored as an executable graph value nor
consulted by readiness, validation, or guard code. An earlier graph interpreter
can own its graph configuration directly because it executes typed source
choices. The later opaque-message layer needs a simulation relation instead.
Generalization to later uses of an unopened value requires implementable
validation, an explicit stronger service, or a source-eligibility proof that
the relevant continuations are independent of the reconstruction witness.

For bounded experiments, resource bounds and observation horizons are explicit
parameters. `Pending` remains a native result at a prefix cutoff; it is not
silently decoded into a source quit or assigned zero utility. Proving a law
conditional on successful settlement does not prove the unconditional law.
Bounded event count alone does not give a finite strategy space or a finite
counterfactual information cover. Prove any additional message-alphabet,
resource, or finite-site conditions used by a strategy-conversion theorem.
Invisible events still consume event fuel even when they reveal nothing.
Terminal-law claims therefore need a settlement bound uniform over admitted
profiles, deviations, and service policies, with the required bound on such
stutters, or a justified different stopping rule. Otherwise state only the
prefix/pending result.

The first positive compiler theorem may use ideal authentication or commitment
services, but each service exposes its public traffic, capabilities, failure
behavior, and security assumptions. Ideal value hiding does not imply hiding
submission existence, timing, malformed traffic, or selective opening. Do not
give an ideal commitment an undeclared atomic-delivery or forced-reveal power.

### Disclosure integration exit gate

The optional-disclosure instance is the operational integration test for this
edge. Its example-specific work has a finite acceptance gate:

1. From initialization, either unchanged player guarantees completion against
   arbitrary behavior by the other player under explicit service assumptions.
   Already-pending requests and application resolution are conclusions, not
   global liveness premises.
2. The same service and deadline conditions preserve each unchanged player's
   source choices; expiration cannot preempt its intended action.
3. Request-history accounting, delivery/inclusion progress, and invariant
   lifting use the shared runtime. The instance discharges application-specific
   obligations without maintaining a second evaluator.

This operational integration gate is checked for the disclosure instance's
deterministic source controllers under the slotted service and a positive
timeout window. From initialization, either unchanged controller guarantees
completion against an arbitrary opposing policy; the owner's binding and
publication and the responder's selected reply are preserved. These are
support-level guarantees, not randomized outcome-law or deviation adequacy.
The checked terms and their explicit service bounds are documented in
[timeout-compilation.md](timeout-compilation.md).

After this gate, the next implementation task is generation of the public
application and controllers from checked source programs. Disclosure becomes
a regression instance of that compiler. Randomized outcome-law and unilateral
deviation adequacy remain required, and should be developed at the reusable
compilation boundary rather than as prerequisites for further bespoke variants
of the example. Additional disclosure variants, optimized bounds, and richer
cryptographic mechanisms are outside this gate unless they expose an obligation
needed by that compiler edge. An abstraction failure redirects work to the
edge itself; it is not a reason to expand the fixture indefinitely.

The ordinary adjacent choice/reveal component uses `PublicChoiceSite`, built
on `SourceDecisionSite`, to derive node identities, ownership, readiness, and
guard code from the source occurrence. `EventGuard.validate` reads only the
stored dependencies of that guard; the candidate action is supplied directly.
Public execution requires public dependencies and a native store readout that
agrees on them. A guard depending on a sealed value requires a separate
validation mechanism or falls outside this component's supported fragment.
Neither source well-formedness nor adjacency establishes public validation.

Disclosure's native response handler invokes this generated endpoint and
validator. `DisclosurePublicChoiceRefinement` checks the exact handler equation,
the local source commit/reveal steps, and equality between the generated graph
macro and the decoded native update. These are local compiler-component
theorems, not whole-program randomized or strategic correspondence. Endpoint
and validator evaluation is executable on supplied metadata and stores; the
current metadata construction uses the noncomputable compiler elaboration.

The next generation step is the companion observation-local controller from
the source decision kernel, sampling once and retaining the selected request
across polling. Then assemble these components into whole public applications.

For an immediately public choice, the existing policy carrier can retain the
draw in its own chronological command history: sample at the first submission,
then recover the earliest submission for this site. A site-tagged codec must
distinguish it from other endpoints. The generic history/cache combinator
belongs in `Interaction`, with abstract payload and value types; Vegas supplies
the source kernel and certified observation readout. That readout may use both
current local observations and remembered own commands, and must reconstruct
the full source decision view, not merely the guard's validation dependencies.
Source environments and graph configurations remain proof-facing.

The controller acceptance gate is an exact first-emission law and preservation
of its selected value through every supported later invocation. Retry cadence
is explicit: retries are real public traffic, not erased stuttering. Start with
the current one-submission behavior and prove its law before adding a retrying
instance. Completion still requires the separate service/deadline theorem.

Conditional openings already have generated metadata in
`ConditionalOpeningSite.runtimeSite`; consume it rather than introduce another
site table. These local generation steps do not themselves establish strategic
equivalence between atomic publication and intermediate graph observations.

## 6. Ownership and dependencies

These are logical owners. Create physical library targets only as their first
clients justify them, with enforced import boundaries rather than empty trees.

| Owner | Belongs here | Does not belong here |
| --- | --- | --- |
| GameTheory mathematics | Probability laws, measures/couplings, expectation and error bounds. | Compiler- or ledger-specific copies of probability facts. |
| GameTheory game/protocol theory | Game forms, local policies, deviations, generic outcome/backtranslation laws and composition, preference and equilibrium transport. | Vegas syntax, mempools, EVM opcodes, Ethereum service assumptions. |
| Runtime-general models | Executable interaction machinery, local message delivery, service interfaces, event/trace refinements; game adapters for these concrete models. | Vegas guards/payoffs or a second definition of game-theoretic concepts. |
| Ledger models | Inclusion, blocks/receipts, clocks/finality interfaces, balances and transaction effects where modeled. | Vegas phases, a particular source quitting policy, or EVM-specific encoding. |
| EVM/Ethereum models | VM execution/ABI/gas where appropriate; Ethereum transaction, network and consensus realization in their own modules. | Vegas source syntax or general backtranslation theory. |
| Vegas | Minimal source, graph IR, compiler passes, source/target eligibility proofs, application-specific instantiations. | Another rich frontend or another generic game/ledger semantics. |
| Vegas backend integration | Lowering Vegas artifacts to selected runtime/VM representations and proving those compiler edges. | Ownership of the independent EVM or Ethereum semantics. |

Backtranslation as a general relation between game forms belongs in GameTheory;
reconstructing a Vegas source decision from graph fields belongs in Vegas.
Replaying a generic protocol controller's local memory is a candidate
GameTheory protocol result; interpreting public network delivery belongs to
the runtime model. A theorem's actual parameters and dependencies decide its
owner, not whether its name contains `runtime`, `compiler`, or `strategy`.

In particular, review the generic contents of `Vegas/Runtime/OutcomeSimulation.lean`,
`Vegas/Runtime/OutcomeSimulationComposition.lean`, and the adjacent deviation,
trace-utility, and correlated-transport modules for upstream ownership. Reuse
existing GameTheory APIs first. Its current concrete transformation API is not
a commitment to add every Vegas certificate unchanged. Follow its architecture
review process; move an accepted abstraction and its tests once, then update
consumers and the dependency pin. No parallel stable definitions or compatibility
facades. Do not commit a GameTheory-specific temporary issue into this repository.

The minimum upstream candidate is a same-player, noninvertible comparison of
game forms: playerwise strategy compilation and deviation backtranslation,
an outcome decoder, and honest and unilateral-deviation law equations against
unchanged opponents. A considered-deviation predicate is explicit when the
target strategy class is restricted. Composition requires proving that
right-edge backtranslated deviations lie in the left edge's considered class.
Utilities and solution concepts are derived consumers, not fields of the
outcome-law relation. Existing source/native, request, and strategy-conversion
clients motivate this extraction; a general hierarchy of compiler passes does
not. GameTheory's existing game forms, profiles, deviations, and Kuhn results
remain the canonical APIs. This candidate has not yet been moved upstream.

Game-free runtime modules may use GameTheory's probability-only root.
Their strategic adapters import GameTheory's protocol/core layers. Model
definitions do not import their Vegas compiler instantiations. General EVM and
ledger semantics must build with no Vegas imports. A directly written non-Vegas
protocol must exercise the reusable runtime and its strategic interpretation.

## 7. Route to a complete Ethereum instance

Keep contract application semantics, interaction services, ledger execution,
and VM/consensus realization independently parameterized, with explicit
composition. This supports further layers for byte encoding, cryptography,
dissemination, finality, resource accounting, or external contract interaction.
It does not prescribe one fixed order for all implementations.

A future complete model must prove the target interface and observation/control
correspondence, not merely supply similarly named state fields. Account for
the external transaction context admitted by the claim; a closed-contract
theorem does not automatically cover arbitrary surrounding contracts or roles.

The first finite-law implementation supplies prefix and bounded-settlement
results. Infinite execution, unbounded support, and computational security need
their appropriate semantics and comparison theorems. GameTheory has finite-law
and measure-theoretic infrastructure, not an already established complete
Ethereum game model. Do not require a universal probability abstraction now or
encode nontermination as source termination to reuse a bounded theorem.

For a positive source theorem, prove the concrete service/information premises
or state them explicitly. For a failure, exhibit the exact operational behavior
and the property it prevents. Keep source well-formedness distinct from runtime
eligibility: reject an unsupported compilation or weaken the advertised result
explicitly rather than silently extending the source game.

## 8. Engineering acceptance criteria

- Every claimed strategic endpoint is induced by the named operational model.
- Every new runtime layer is tested for unintended observations and omitted
  capabilities, as well as for successful execution.
- Adding a layer changes only its adjacent passes and consumers of facts those
  passes no longer provide; no global enumeration of levels is required.
- Source-outcome bounds and other selected queries can be interpreted at each
  stage with checked maps; assumptions and errors remain explicit.
- No generic theory depends on Vegas, and no generic interaction model depends
  on EVM/Ethereum. A real second client exercises the reusable boundary.
- All maintained modules remain reachable from build roots; architectural
  direction and cycle checks, warning-free builds, and axiom audits stay active.
- Paper claims name the actual endpoints and hypotheses. Planned layers do not
  count as a proved route to deployed execution.
