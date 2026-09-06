# Request windows and public scheduling

The proposed public-delivery expansion is specified in
[ledger-expansion-design.md](ledger-expansion-design.md), with implementation
gates in [ledger-expansion-plan.md](ledger-expansion-plan.md). These are plans;
they do not change the proved boundary below.
The [compiler boundary](compiler-boundary.md) keeps rich Kotlin lowering
separate from the minimal core and identifies the optional-disclosure encoding
as the first integration step, not an already proved frontend theorem.

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
transaction executions. They establish a bounded part of B0a in the expansion
plan without changing the public-delivery boundary above.

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

The next integration obligation is a concrete optional-disclosure core
encoding and its actual observation/strategy correspondence, including an
audit of `RevealComplete`. The later runtime obligation is to derive the
relevant response barrier from execution rather than its strategy type.

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
