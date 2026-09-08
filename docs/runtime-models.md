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
full adaptive scheduling model. The kernel is not yet a target of a proved
Vegas compilation edge.

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
- The term fails `RevealComplete`. No existing `WFProgram` requirement is
  removed, and this term is not covered merely by applying a theorem quantified
  over `WFProgram`.

`OptionalDisclosure.not_checked` verifies that no `WFProgram` has this exact
graph-program input. `VegasTests/DisclosureTrace.lean` additionally identifies
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
