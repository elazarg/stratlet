# Request windows and public scheduling

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
