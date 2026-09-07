/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Protocol.Execution
import GameTheory.Protocol.Information

/-!
# Adversarially scheduled protocols

A protocol in which players submit actions to a shared state machine and a
*scheduler* decides the order those submissions are applied in.  A blockchain is
one instance — the sequencer orders a block's transactions — but nothing here is
blockchain-specific: the underlying state machine is a parameter, so this covers
asynchronous public protocols generally.

The module depends only on `GameTheory`, so it can be lifted into that library
once the interface has been exercised by a real client.

## The scheduler is a protocol coordinate, not a game player

A scheduler passed as a parameter sits in the protocol's *type*, so two
schedulers give two protocols, their histories and information states live in
different families, and comparison requires transports.  The named
`Participant.scheduler` coordinate instead puts every accepted schedule inside
one execution protocol and lets operational theorems quantify over all of them.

`Participant` is therefore a submission-indexing type.  It does **not** assert
that every coordinate belongs to the population whose Nash equilibrium is under
analysis.  `Vegas.Scheduled.Strategic` fixes an arbitrary, possibly adversarial
scheduler strategy and quantifies equilibrium deviations only over
`Participant.player i`.  Scheduler preferences are neither inferred nor
preserved.

## The one design decision that matters

`State` records the realized order in a `log`.  On a public runtime the order in
which transactions landed *is* observable, so a model that quotients it away
understates what a strategy may condition on, and any preservation theorem
proved against such a model describes a system nobody runs.

`step_ne_of_order_ne` is what carrying it costs and buys: **confluence of
effects is not invisibility of order.**  Even where every pair of submissions
commutes, so the underlying state law is schedule-invariant, two schedules still
produce distinguishable protocol states.

## Deviation classes, not two games

`GameTheory` makes policy locality structural: a policy is a function of an
information state, so a policy reading something absent from that state cannot
be written.  The honest and robust readings are therefore two classes of policy
inside the one faithful game — `OrderOblivious` and everything — which is the
shape `DeviationAdequacyOn` consumes.  `blindSignals` is the documented
idealization that erases the order from participants' information while keeping
the same scheduled transition, and
`blind_infoOf_eq_forgetOrders` measures exactly what it drops.

## Two disciplines, and when each is needed

An order-aware deviation can be answered in two ways, because equilibrium asks
of an available deviation only that it not improve on the equilibrium payoff.
Make it unavailable, or let it be available and show it gains nothing.

`EnforcesOrder` takes the first route: the runtime accepts one order per view,
so the scheduler has nothing to choose and `step_eq_of_enforcesOrder` makes the
coordinate operationally inert.  It costs the round's parallelism, and an
enforced order means a stalled participant blocks the protocol.

`EffectsCommute` takes the second: every accepted order has the same effect, so
`step_base_eq_of_effectsCommute` makes the scheduler irrelevant to the
underlying state while leaving it its choice.  This is the cheaper answer and
the common case, and `counterSystem` shows it is not degenerate — the state
genuinely moves, and commutation is a fact about addition.

The two are ordered, not alternative: `effectsCommute_of_enforcesOrder`.  But
they leave different things observable, and the gap is the point.  Enforcement
determines the *log*, so nothing separates two schedules.  Commutation
determines only the *base* state; the log still differs, so a payoff reading the
log still sees a difference.  Payoff-irrelevance is commutation *plus* a
schedule-blind game — a condition on the game, not on the runtime.

Neither is a default, and the choice is not this module's to make.  `schedules`
is a field, so an artifact is permissive or enforcing by construction and both
properties appear only as hypotheses.  A developer wanting no order-sensitive
guarantee keeps the parallelism; one who wants it pays for exactly it.  The
obligation is to find, per property, the weakest discipline that supports it.

`raceSystem` marks where the permissive tier ends: doubling and adding do not
commute, so `EffectsCommute` fails and a preservation claim there has to buy
enforcement.  Two pending operations whose order changes the result is the shape
a public runtime actually has, which is why enforcement stays available rather
than being argued away.

## Menus are observation-local, not public

A participant menu that is only a function of one public `View` is adequate for
a runtime whose entire state is public, but it cannot express Vegas.

The obstruction is concrete.  A player's legal frontier action is determined by
`EventGraph.observe`, which includes the values sealed *to that player*
(`FrontierAction.available_iff_of_observe_eq`); `publicObserve` sees only fields
with no owner.  So no function of the public view decides what a Vegas player
may submit, and the public-menu obligation is not merely unproved for compiled
programs — it is false for them.  A model with that obligation could describe
only the fragment of the language with nothing sealed, which is the fragment
the language exists to avoid.

Hence `Obs` and `obs`: menus are local to a participant's *own* observation,
which is what `GameTheory`'s `PrivateSignal` channel was always for. `View`
remains the genuinely public player signal. The separate `SchedulerView`
contains exactly what may influence ordering. The compiled instance supplies
the full public graph observation: a scheduler may react to data everyone can
already see, but not to sealed values or same-round submissions.

## Vocabulary: absence, declining, and the scheduler

Three different notions must remain distinct.

*The scheduler* is `Participant.scheduler`, the participant that orders the
round.

*Declining* is `declineValue`, the null **value** a player submits to a nullable
commitment — so a decline is `some (declineValue b)`, a submission like any
other.  `Expr.nullableCommitGuard` accepts it unconditionally
(`evalExpr_nullableCommitGuard_declineValue`), the continuation is typed at
`option b` and must handle it, and the program may charge for it on the spot.
`AllowsDeclining` is its protocol-layer image.

*Absence* is `IsLegalJoint`'s `none`: no submission at all.  It is legal only
for an inactive participant, so the model forbids what no public runtime can
(`LegalOption.exists_eq_some_of_active`).  `AllowsSilence` names that gap, and
`silence_inert` is what makes it a gap rather than a decline — the silent
player's action moves nothing, so the player-controlled phase cannot distinguish
it from one never asked.  Independent automatic settlement may still run.

The two that survive are ordered, not alternative:
`AllowsSilence.toAllowsDeclining` says silence is a decline that is also
invisible, while `race_allowsDeclining` with `race_no_silence` shows the
converse fails.  The gap between them is the room a protocol has to charge for
declining, and it is why a deposit is slashable against a decline directly but
against silence only through a timeout.

## What is observable, and what is assumed

Two different things are visible on a public runtime, and only one is modelled
here.  They are different epistemic objects, not different resolutions.

*Settled order.*  Once a round has been applied, the order it was applied in is
on the chain.  Everyone reads it, everyone reads that everyone reads it, and so
on: it is **common knowledge**, which is what a public signal means in this
vocabulary.  `log` records it and `revealingSignals` publishes it.

*In-flight submissions.*  Before a round is applied, pending submissions may be
visible to some observers.  This is **not** common knowledge.  A player seeing a
pending submission does not know who else saw it, nor that others know they saw
it.  Publishing it as a public signal would be *wrong* rather than coarse.

*Ordering power is not information power.*  The scheduler modelled here picks an
order over a joint submission it cannot see.  That is already enough to matter —
`raceSystem` has two accepted orders reaching different totals — but it is
strictly weaker than choosing one's own action in response to someone else's.
The disciplines above constrain ordering power only.  Keeping the two apart is
what makes the assumption below legible: it is the one that excludes information
power, and it is assumed rather than established.

**This module assumes no participant observes a submission before it is
applied** — the scheduler included, which is conservative for the players and
restrictive for the adversary.  Front-running is outside the model.  Relaxing
the assumption is not a matter of publishing more signals: it needs an
information structure able to express mutual-but-not-common knowledge, which
`InfoSignals` does not directly provide.  It is stated because a reader taking
`revealingSignals` for "everything a chain reveals" would credit the model with
more faithfulness than it has.
-/

noncomputable section

namespace Vegas

open GameTheory.Protocol
open GameTheory.Math.Probability

universe u

variable {ι : Type u}

/-- Who submits in a round: the players, and the scheduler.

Deliberately an inductive rather than `Option ι`.  Three different things around
this model want to be called `none` — a participant who submitted nothing, the
null *value* a player submits to decline, and the scheduler — and conflating the
first two has caused real errors.  Naming the scheduler removes one of the three
outright, and makes the other two visibly different at every use site: a player
declining is `some (declineValue ..)`, a player submitting nothing is `none`. -/
inductive Participant (ι : Type u) where
  /-- The participant that orders the round. -/
  | scheduler
  /-- A submitting player. -/
  | player (i : ι)

deriving instance DecidableEq for Participant
deriving instance Fintype for Participant

/-- A state machine whose round is resolved by applying each submitted action in
turn.  Ordering is a real degree of freedom exactly when `applyOne` calls fail
to commute. -/
structure ScheduledSystem (ι : Type u) where
  /-- The underlying state, before any scheduling record is attached. -/
  Base : Type u
  /-- Each player's action carrier. -/
  Action : ι → Type u
  /-- The initial underlying state. -/
  init : Base
  /-- Who must submit. -/
  active : Base → ι → Prop
  /-- What an active player may submit. -/
  available : (state : Base) → (i : ι) → Set (Action i)
  /-- Where execution stops. -/
  terminal : Base → Prop
  /-- Apply one player's submission. -/
  applyOne : (state : Base) → (i : ι) → Action i → FinDist Base
  /-- Finish automatic work enabled by the ordered submissions.

  `applyOne` models the participant-controlled part of a round.  A compiled
  event graph may then have samples or reveals to execute before the next
  strategic frontier.  Keeping that closure explicit prevents an all-inactive
  state from satisfying `progress` by stuttering forever.  Systems with no
  automatic work use `FinDist.pure`. -/
  settle : Base → FinDist Base
  /-- What everyone publicly sees of the underlying state. -/
  View : Type u
  /-- The public view of a state. -/
  view : Base → View
  /-- Exactly the state summary on which scheduling choices may depend.

  This is separate from `View` because the two interfaces have different
  consumers.  It does not require the scheduler to be blind to public game
  data: a compiled Vegas scheduler receives the complete public observation. -/
  SchedulerView : Type u
  /-- The scheduler-visible summary of a state. -/
  schedulerView : Base → SchedulerView
  /-- What player `i` privately observes of the underlying state.

  Separate from `View` because a language with sealed commitments needs it.  A
  Vegas player's legal frontier is determined by its *own* observation, which
  includes values sealed to it, and no public view determines that menu.  A
  model whose menus were functions of a public view could not express such a
  program at all. -/
  Obs : ι → Type u
  /-- Player `i`'s private observation of a state. -/
  obs : Base → (i : ι) → Obs i
  /-- The options visible to a player at its own observation. -/
  menuAt : (i : ι) → Obs i → Set (Option (Action i))
  /-- Legality is observation-determined: what a player sees fixes what it may
  do.  Weaker than public determination, and what a sealed-commitment language
  actually satisfies.

  Split into the two cases rather than stated with a `match`, so the interface
  carries no matcher for a client's unifier to get stuck on. -/
  menuAt_some : ∀ (state : Base) (i : ι) (action : Action i),
    some action ∈ menuAt i (obs state i) ↔
      (active state i ∧ action ∈ available state i)
  /-- Abstaining is visibly allowed exactly when the player is not active. -/
  menuAt_none : ∀ (state : Base) (i : ι),
    (none : Option (Action i)) ∈ menuAt i (obs state i) ↔ ¬ active state i
  /-- Which orders the runtime will accept at a view.

  A permissive runtime accepts every order and leaves the scheduler a real
  choice.  An order-enforcing one accepts exactly one, and then the scheduler
  has no choice to make — see `EnforcesOrder`.  Indexed by the view rather than
  the state, because what the runtime accepts must be publicly determined for
  the scheduler's menu to be information-local. -/
  schedules : SchedulerView → Set (List ι)
  /-- Some order is always acceptable, so a round can always be resolved. -/
  schedules_nonempty : ∀ v, (schedules v).Nonempty
  /-- Every non-terminal state admits a legal joint submission. -/
  progress : ∀ state, ¬ terminal state →
    ∃ joint, IsLegalJoint (active state) (available state) joint

namespace ScheduledSystem

variable (sys : ScheduledSystem.{u} ι)

/-- The order a round's submissions were applied in. -/
abbrev Order (_sys : ScheduledSystem.{u} ι) : Type u := List ι

/-- What each participant may submit: an order for the scheduler, an action for
a player. -/
abbrev Submission (sys : ScheduledSystem.{u} ι) : Participant ι → Type u
  | .scheduler => sys.Order
  | .player i => sys.Action i

/-- A protocol state: the underlying state together with the public record of
the orders actually realized, most recent first. -/
structure State (sys : ScheduledSystem.{u} ι) where
  /-- The underlying state machine's state. -/
  base : sys.Base
  /-- Realized orders, most recent first.  Publicly observable. -/
  log : List sys.Order

/-- Apply the submitted actions along a given order, skipping players who did
not submit. -/
noncomputable def applyOrder (sys : ScheduledSystem.{u} ι)
    (joint : ∀ a, Option (sys.Submission a)) :
    sys.Order → sys.Base → FinDist sys.Base
  | [], state => FinDist.pure state
  | i :: rest, state =>
      match joint (.player i) with
      | none => applyOrder sys joint rest state
      | some action =>
          (sys.applyOne state i action).bind (applyOrder sys joint rest)

/-- Resolve a round completely: apply the submitted player actions in the
scheduler's order, then perform the system's automatic closure. -/
noncomputable def resolveOrder (sys : ScheduledSystem.{u} ι)
    (joint : ∀ a, Option (sys.Submission a))
    (order : sys.Order) (state : sys.Base) : FinDist sys.Base :=
  (sys.applyOrder joint order state).bind sys.settle

/-- The order a joint submission schedules. -/
def scheduledOrder (joint : ∀ a, Option (sys.Submission a)) : sys.Order :=
  (joint .scheduler).getD []

/-- Who is active: every player the state says must submit, and the scheduler,
always — a round is always ordered by someone. -/
def participantActive (state : sys.State) : Participant ι → Prop
  | .scheduler => True
  | .player i => sys.active state.base i

/-- What each participant may submit at a state. -/
def participantAvailable (state : sys.State) : (a : Participant ι) → Set (sys.Submission a)
  | .scheduler => sys.schedules (sys.schedulerView state.base)
  | .player i => sys.available state.base i

/-- What each participant observes: the explicitly delimited scheduler view for
the scheduler, and the player's own observation for a player. -/
abbrev ParticipantObs (sys : ScheduledSystem.{u} ι) : Participant ι → Type u
  | .scheduler => sys.SchedulerView
  | .player i => sys.Obs i

/-- Each participant's observation of a protocol state. -/
def participantObs (state : sys.State) : (a : Participant ι) → sys.ParticipantObs a
  | .scheduler => sys.schedulerView state.base
  | .player i => sys.obs state.base i

/-- The scheduler has no state information unavailable to an original player.

This is an epistemic, not probabilistic, condition.  The projection may expose
the complete public game state, and the scheduler may choose an arbitrary
state-dependent or randomized policy from it.  The condition says only that
every original player can recover the scheduler's pre-round view from that
player's own pre-round observation. -/
def SchedulerHasNoExtraInformation : Prop :=
  ∃ project : (i : ι) → sys.Obs i → sys.SchedulerView,
    ∀ state i, project i (sys.obs state i) = sys.schedulerView state

/-- The menu each participant sees at its own observation.  The scheduler must
order the round, so abstaining is not on its menu. -/
def participantMenuAt : (a : Participant ι) → sys.ParticipantObs a →
    Set (Option (sys.Submission a))
  | .scheduler, v => {choice | ∃ order ∈ sys.schedules v, choice = some order}
  | .player i, o => sys.menuAt i o

/-- Extend a players-only joint submission with an order for the scheduler.
A named definition rather than an inline match, so it reduces on `.player i`. -/
def withSchedule (order : sys.Order) (joint : ∀ i, Option (sys.Action i)) :
    ∀ a : Participant ι, Option (sys.Submission a)
  | .scheduler => some order
  | .player i => joint i

/-- The execution protocol.  There is exactly one: the scheduler is a coordinate
of the joint action, not a parameter of the protocol. -/
@[reducible] noncomputable def toExecutionProtocol : ExecutionProtocol (Participant ι) where
  State := sys.State
  Action := sys.Submission
  init := { base := sys.init, log := [] }
  active := sys.participantActive
  available := sys.participantAvailable
  terminal state := sys.terminal state.base
  step state legal :=
    (sys.resolveOrder legal.1 (sys.scheduledOrder legal.1) state.base).map
      fun next =>
        { base := next, log := sys.scheduledOrder legal.1 :: state.log }
  progress state hterminal := by
    obtain ⟨joint, hjoint⟩ := sys.progress state.base hterminal
    obtain ⟨order, horder⟩ :=
      sys.schedules_nonempty (sys.schedulerView state.base)
    refine ⟨sys.withSchedule order joint, ?_⟩
    intro a
    cases a with
    | scheduler => exact ⟨trivial, horder⟩
    | player i =>
        -- Case on the submission so both matchers reduce: the two sides are
        -- defeq but their matcher instances are generated at different types.
        have h := hjoint i
        simp only [withSchedule, participantActive, participantAvailable]
        cases hj : joint i with
        | none => rw [hj] at h; exact h
        | some action => rw [hj] at h; exact h

@[simp] theorem toExecutionProtocol_terminal (state : sys.State) :
    sys.toExecutionProtocol.terminal state = sys.terminal state.base := rfl

/-- Every successor of a step records exactly the order that was scheduled. -/
theorem log_of_mem_support_step
    {state : sys.State}
    {legal : { joint // sys.toExecutionProtocol.Legal state joint }}
    {next : sys.State}
    (hnext : next ∈ (sys.toExecutionProtocol.step state legal).support) :
    next.log = sys.scheduledOrder legal.1 :: state.log := by
  simp only [toExecutionProtocol, FinDist.support_map] at hnext
  obtain ⟨_base, _hbase, hnext⟩ := hnext
  rw [← hnext]

/-- Any invariant established by the settlement phase holds after every
realized protocol round. -/
theorem base_property_of_mem_support_step
    (property : sys.Base → Prop)
    (hsettle : ∀ state {next}, next ∈ (sys.settle state).support → property next)
    {state : sys.State}
    {legal : { joint // sys.toExecutionProtocol.Legal state joint }}
    {next : sys.State}
    (hnext : next ∈ (sys.toExecutionProtocol.step state legal).support) :
    property next.base := by
  simp only [toExecutionProtocol, FinDist.support_map, Set.mem_image] at hnext
  rcases hnext with ⟨nextBase, hresolved, rfl⟩
  unfold resolveOrder at hresolved
  rw [FinDist.support_bind] at hresolved
  simp only [Set.mem_iUnion] at hresolved
  rcases hresolved with ⟨postOrder, _hpostOrder, hsettled⟩
  exact hsettle postOrder hsettled

/-- **Confluence of effects is not invisibility of order.**

Two joint submissions that schedule different orders induce different successor
laws — whatever the state machine does, and in particular even when the two
orders have identical effects.

A schedule-invariance result about the underlying machine constrains what the
machine computes; it says nothing about what a participant observes.  Only a
statement about the protocol state does. -/
theorem step_ne_of_order_ne
    {state : sys.State}
    {left right : { joint // sys.toExecutionProtocol.Legal state joint }}
    (horder : sys.scheduledOrder left.1 ≠ sys.scheduledOrder right.1) :
    sys.toExecutionProtocol.step state left ≠
      sys.toExecutionProtocol.step state right := by
  intro heq
  obtain ⟨next, hnext⟩ := (sys.toExecutionProtocol.step state left).support_nonempty
  have hleft : next.log = sys.scheduledOrder left.1 :: state.log :=
    sys.log_of_mem_support_step hnext
  have hnextRight : next ∈ (sys.toExecutionProtocol.step state right).support := by
    rw [← heq]; exact hnext
  have hright : next.log = sys.scheduledOrder right.1 :: state.log :=
    sys.log_of_mem_support_step hnextRight
  exact horder (List.cons.inj (hleft.symm.trans hright)).1

/-! ## Enforcing the schedule

An order-aware player deviation must be included in a robust equilibrium
claim.  The elementary fixed-signal case is harmless: fix the adversarial
signal and back-translate the contingent player policy at that signal, as
`Participant.PlayerDeviationAdequacyOn` requires. Random independent signals
are handled by `Participant.RandomIndependentSignal.isPlayerNash_iff`.
A scheduler reacting to public history requires an additional causal
back-translation: fixing its randomness does not fix its realized orders.

Enforcement serves a stronger operational purpose. A runtime accepting exactly
one order at each view removes ordering choice and makes the entire successor
law equal, including the public log. This is useful when a developer wants
trace equality, or when commutation of underlying effects cannot be proved; it
is not required merely to ignore the scheduler's incentives.

Enforcement is a dial, not a default.  `schedules` is a field of the system, so
a compiled artifact is permissive or enforcing by construction, and
`EnforcesOrder` appears only as a *hypothesis* on the results that need it.  A
developer who wants no order-sensitive guarantee pays nothing: the permissive
runtime keeps its parallelism, and the theorems below simply do not apply to it.
A developer who does want one pays for exactly that.  The obligation on this
development is therefore to identify, for each property worth preserving, the
weakest discipline that supports it — not to enforce everywhere.

The price is real and is not modelled here: serializing a round costs
throughput, and enforcing an order means a stalled participant blocks the
protocol, which is why an enforcing runtime needs timeouts.

`EnforcesOrder` does not make the protocol schedule-free.  Timing remains
public — block height, elapsed time, who was slow — and that is a separate
signal this development does not model at all.  Enforcement removes *order* as a
channel, not every channel. -/

/-- The runtime accepts at most one order at each view, so the scheduler has no
choice to make. -/
def EnforcesOrder (sys : ScheduledSystem.{u} ι) : Prop :=
  ∀ v : sys.SchedulerView, (sys.schedules v).Subsingleton

/-- Applying a round reads the joint submission only through the players'
components, never the scheduler's. -/
theorem applyOrder_congr {left right : ∀ a, Option (sys.Submission a)}
    (hplayers : ∀ i, left (.player i) = right (.player i)) :
    ∀ (order : sys.Order) (state : sys.Base),
      sys.applyOrder left order state = sys.applyOrder right order state
  | [], _ => rfl
  | i :: rest, state => by
      simp only [applyOrder, hplayers i]
      cases hr : right (.player i) with
      | none =>
          simp only
          exact applyOrder_congr hplayers rest state
      | some action =>
          simp only
          exact congrArg _ (funext fun next => applyOrder_congr hplayers rest next)

/-- Resolving a round also ignores the scheduler coordinate once the player
submissions and order are fixed. -/
theorem resolveOrder_congr {left right : ∀ a, Option (sys.Submission a)}
    (hplayers : ∀ i, left (.player i) = right (.player i))
    (order : sys.Order) (state : sys.Base) :
    sys.resolveOrder left order state = sys.resolveOrder right order state := by
  unfold resolveOrder
  rw [sys.applyOrder_congr hplayers]

/-- Under an enforcing runtime every legal joint at a state schedules the same
order: the scheduler's component is determined. -/
theorem scheduledOrder_eq_of_enforcesOrder (henforce : sys.EnforcesOrder)
    {state : sys.State}
    (left right : { joint // sys.toExecutionProtocol.Legal state joint }) :
    sys.scheduledOrder left.1 = sys.scheduledOrder right.1 := by
  have hleft := left.2.2 .scheduler
  have hright := right.2.2 .scheduler
  unfold scheduledOrder
  cases hl : left.1 .scheduler with
  | none => rw [hl] at hleft; exact absurd trivial hleft
  | some orderLeft =>
      cases hr : right.1 .scheduler with
      | none => rw [hr] at hright; exact absurd trivial hright
      | some orderRight =>
          rw [hl] at hleft
          rw [hr] at hright
          simp only [Option.getD_some]
          exact henforce (sys.schedulerView state.base) hleft.2 hright.2

/-- **An enforcing runtime makes the scheduler operationally inert.**

Two legal joints agreeing on every player's submission induce the same successor
law, whatever the scheduler submitted.  Thus the scheduling coordinate cannot
influence the outcome at all.  This is an operational statement; it makes no
claim about a scheduler's preferences, which are outside player-equilibrium
preservation.

This is what restricting to order-oblivious play could not deliver.  That
restriction constrains behaviour and equilibrium quantifies over availability;
this removes the availability. -/
theorem step_eq_of_enforcesOrder (henforce : sys.EnforcesOrder)
    {state : sys.State}
    {left right : { joint // sys.toExecutionProtocol.Legal state joint }}
    (hplayers : ∀ i, left.1 (.player i) = right.1 (.player i)) :
    sys.toExecutionProtocol.step state left =
      sys.toExecutionProtocol.step state right := by
  have horder := sys.scheduledOrder_eq_of_enforcesOrder henforce left right
  simp only [toExecutionProtocol, horder]
  rw [sys.resolveOrder_congr hplayers]

/-! ## Visible order with no state effect

Enforcement is the strongest operational instrument, but it is not always
needed. The cheaper common case leaves every accepted order available and proves
that the choice cannot move anything a player's payoff can see. Player policies
may still condition on the public order — `coinOrderAware` is one — and robust
strategic analysis must quantify over them. `IndependentSignal.isPlayerNash_iff`
proves the base case of one extra public signal. A compiled scheduler may also
condition on the public state that players already observe; it still cannot
inspect sealed state or the current simultaneous submissions.

`EnforcesOrder` removes the scheduler's choice; `EffectsCommute` leaves the
choice and removes its consequences.  They differ in what stays observable, and
the difference is not cosmetic.  Enforcement determines the *log*, so no
observation whatsoever separates two schedules.  Commutation determines only the
*base* state: the log still differs, so a payoff that reads the log still sees a
difference.  Payoff-irrelevance is commutation *plus* a utility blind to the
schedule, and that second half is a condition on the game, not on the runtime.

Neither discipline handles a scheduler that reacts to what it is ordering.  Both
quantify over a fixed joint submission, which is exactly the model's claim that
the scheduler commits to an order without seeing the round's submissions.  A
runtime where the order may depend on the submissions is a different system, and
front-running is what that difference is called. -/

/-- Every order the runtime accepts has the same effect on the underlying state
for every legal player submission.

Strictly weaker than `EnforcesOrder`, which collapses the accepted orders to one:
here the scheduler still chooses, its choice still enters the log, and the choice
is still observable.  What it cannot do is move the underlying state. -/
def EffectsCommute (sys : ScheduledSystem.{u} ι) : Prop :=
  ∀ (joint : ∀ a, Option (sys.Submission a)) (state : sys.Base),
    IsLegalJoint (sys.active state) (sys.available state)
        (fun i => joint (.player i)) →
      ∀ {left right : sys.Order},
        left ∈ sys.schedules (sys.schedulerView state) →
          right ∈ sys.schedules (sys.schedulerView state) →
            sys.resolveOrder joint left state = sys.resolveOrder joint right state

/-- Forgetting the log of a round's successor leaves exactly the fully resolved
effect of the scheduled order, including automatic settlement. -/
theorem step_map_base {state : sys.State}
    (joint : { joint // sys.toExecutionProtocol.Legal state joint }) :
    (sys.toExecutionProtocol.step state joint).map State.base =
      sys.resolveOrder joint.1 (sys.scheduledOrder joint.1) state.base := by
  simp only [toExecutionProtocol, FinDist.map_comp, Function.comp_def]
  exact FinDist.map_id _

/-- A legal joint's scheduled order is one the runtime accepts. -/
theorem scheduledOrder_mem_schedules {state : sys.State}
    (joint : { joint // sys.toExecutionProtocol.Legal state joint }) :
    sys.scheduledOrder joint.1 ∈
      sys.schedules (sys.schedulerView state.base) := by
  have hlegal := joint.2.2 .scheduler
  unfold scheduledOrder
  cases hjoint : joint.1 .scheduler with
  | none => rw [hjoint] at hlegal; exact absurd trivial hlegal
  | some order => rw [hjoint] at hlegal; exact hlegal.2

/-- **Commuting effects make the scheduler irrelevant to the underlying state.**

Two legal joint submissions agreeing on every player's submission reach the same
law over underlying states, whatever the scheduler submitted.  The scheduler
keeps its choice and that choice stays visible in the log; what it has lost is
any influence on the state.

This is the permissive runtime's counterpart to `step_eq_of_enforcesOrder`, and
it is what lets such a runtime keep its parallelism and still support a
preservation claim.  Real-player deviations may read the order signal.  Such a
contingent deviation must be back-translated to an ordinary source deviation;
`Participant.PlayerDeviationAdequacyOn` states that obligation.  The generic
signal theorems prove averaging over independent signals. Applying that
argument to an executing public-history scheduler also requires a source
strategy construction for each fixed scheduler random seed. Enforcement buys
strictly more — equality of the whole successor law, log included — at the cost
of serializing the round. -/
theorem step_base_eq_of_effectsCommute (hcommute : sys.EffectsCommute)
    {state : sys.State}
    {left right : { joint // sys.toExecutionProtocol.Legal state joint }}
    (hplayers : ∀ i, left.1 (.player i) = right.1 (.player i)) :
    (sys.toExecutionProtocol.step state left).map State.base =
      (sys.toExecutionProtocol.step state right).map State.base := by
  rw [sys.step_map_base left, sys.step_map_base right]
  rw [sys.resolveOrder_congr hplayers]
  have hlegal : IsLegalJoint (sys.active state.base) (sys.available state.base)
      (fun i => right.1 (.player i)) := by
    intro i
    have h := right.2.2 (.player i)
    simp only [participantActive, participantAvailable] at h
    cases hjoint : right.1 (.player i) with
    | none => rw [hjoint] at h; simpa only [hjoint] using h
    | some action => rw [hjoint] at h; simpa only [hjoint] using h
  exact hcommute right.1 state.base hlegal
    (sys.scheduledOrder_mem_schedules left) (sys.scheduledOrder_mem_schedules right)

/-- Enforcement implies commutation: with one acceptable order there is nothing
for two orders to disagree about.  So the results below `EffectsCommute` are
available to an enforcing runtime too, and the two disciplines are ordered
rather than alternative. -/
theorem effectsCommute_of_enforcesOrder (henforce : sys.EnforcesOrder) :
    sys.EffectsCommute := by
  intro joint state _hlegal left right hleft hright
  rw [henforce (sys.schedulerView state) hleft hright]

/-! ## Two information models over one protocol -/

/-- The order-revealing observation history visible at one decision point. -/
abbrev RevealingSnapshot (sys : ScheduledSystem.{u} ι)
    (a : Participant ι) : Type u :=
  sys.ParticipantObs a × List (sys.Order × sys.ParticipantObs a)

/-- What an order-revealing participant knows.

`current` and `past` expose the runtime observations. `own` also records the
complete information snapshot at every earlier decision by this participant,
together with the submitted action. The latter is not extra runtime data: it
is the participant's own memory, and retaining it makes perfect recall true
rather than merely asserted. -/
structure RevealingInfo (sys : ScheduledSystem.{u} ι)
    (a : Participant ι) where
  current : sys.ParticipantObs a
  past : List (sys.Order × sys.ParticipantObs a)
  own : List (sys.RevealingSnapshot a × sys.Submission a)

/-- The order-blind observation history visible at one decision point. -/
abbrev BlindSnapshot (sys : ScheduledSystem.{u} ι)
    (a : Participant ι) : Type u :=
  sys.ParticipantObs a × List (sys.ParticipantObs a)

/-- What an order-blind participant knows. It retains its own decisions while
discarding the schedule from every remembered observation. -/
structure BlindInfo (sys : ScheduledSystem.{u} ι)
    (a : Participant ι) where
  current : sys.ParticipantObs a
  past : List (sys.ParticipantObs a)
  own : List (sys.BlindSnapshot a × sys.Submission a)

/-- Discard the schedule from an order-revealing information state, including
from the snapshots at which the participant previously acted. -/
def forgetOrders {a : Participant ι}
    (info : sys.RevealingInfo a) : sys.BlindInfo a where
  current := info.current
  past := info.past.map Prod.snd
  own := info.own.map fun remembered =>
    ((remembered.1.1, remembered.1.2.map Prod.snd), remembered.2)

/-- Extend order-revealing information by one realized transition. -/
def RevealingInfo.push {a : Participant ι}
    (prior : sys.RevealingInfo a) (choice : Option (sys.Submission a))
    (current : sys.ParticipantObs a) (order : sys.Order) :
    sys.RevealingInfo a where
  current := current
  past := (order, prior.current) :: prior.past
  own := match choice with
    | none => prior.own
    | some action => ((prior.current, prior.past), action) :: prior.own

/-- Reconstruct the scheduler's perfect-recall own-play record from its public
order/view history.  The scheduler acts in every nonterminal round, so its
earlier information snapshots and choices contain no data beyond this list. -/
def schedulerOwnOfPast (sys : ScheduledSystem.{u} ι) :
    List (sys.Order × sys.SchedulerView) →
      List (sys.RevealingSnapshot (.scheduler : Participant ι) × sys.Order)
  | [] => []
  | (order, view) :: past =>
      ((view, past), order) :: schedulerOwnOfPast sys past

/-- Reconstruct the scheduler's complete revealing information from one
player's information, given a projection from that player's observation to the
scheduler view.  The player's private component and own actions are discarded;
the shared public order history determines the scheduler's own-play memory. -/
def schedulerInfoFromPlayer {i : ι}
    (project : sys.Obs i → sys.SchedulerView)
    (info : sys.RevealingInfo (.player i)) :
    sys.RevealingInfo (.scheduler : Participant ι) := by
  let past := info.past.map fun entry => (entry.1, project entry.2)
  exact
    { current := project info.current
      past := past
      own := schedulerOwnOfPast sys past }

@[simp] theorem schedulerInfoFromPlayer_push {i : ι}
    (project : sys.Obs i → sys.SchedulerView)
    (prior : sys.RevealingInfo (.player i))
    (choice : Option (sys.Action i)) (current : sys.Obs i)
    (order : sys.Order) :
    sys.schedulerInfoFromPlayer project
        (RevealingInfo.push sys prior choice current order) =
      RevealingInfo.push sys (sys.schedulerInfoFromPlayer project prior)
        (some order) (project current) order := by
  cases prior
  cases choice <;>
    simp [schedulerInfoFromPlayer, RevealingInfo.push, schedulerOwnOfPast]

/-- Extend order-blind information by one realized transition. -/
def BlindInfo.push {a : Participant ι}
    (prior : sys.BlindInfo a) (choice : Option (sys.Submission a))
    (current : sys.ParticipantObs a) : sys.BlindInfo a where
  current := current
  past := prior.current :: prior.past
  own := match choice with
    | none => prior.own
    | some action => ((prior.current, prior.past), action) :: prior.own

@[simp] theorem forgetOrders_push {a : Participant ι}
    (prior : sys.RevealingInfo a) (choice : Option (sys.Submission a))
    (current : sys.ParticipantObs a) (order : sys.Order) :
    sys.forgetOrders (RevealingInfo.push sys prior choice current order) =
      BlindInfo.push sys (sys.forgetOrders prior) choice current := by
  cases prior
  cases choice <;> rfl

/-- Signals that publish the realized order alongside the public view: the
faithful model of a public runtime. -/
@[reducible] def revealingSignals : InfoSignals sys.toExecutionProtocol where
  PublicSignal := sys.View × sys.Order
  PrivateSignal a := sys.ParticipantObs a
  initialPublic := (sys.view sys.init, [])
  initialPrivate a := sys.participantObs sys.toExecutionProtocol.init a
  publicSignal event := (sys.view event.target.base, event.target.log.headD [])
  privateSignal a event := sys.participantObs event.target a
  InfoState a := sys.RevealingInfo a
  initInfo _ observation _ :=
    { current := observation, past := [], own := [] }
  pushInfo _ info choice observation pub :=
    RevealingInfo.push sys info choice observation pub.2

/-- Signals that publish only the public view: the idealization in which a round
resolves atomically.  A perfectly good information model — just not one of a
public chain. -/
@[reducible] def blindSignals : InfoSignals sys.toExecutionProtocol where
  PublicSignal := sys.View
  PrivateSignal a := sys.ParticipantObs a
  initialPublic := sys.view sys.init
  initialPrivate a := sys.participantObs sys.toExecutionProtocol.init a
  publicSignal event := sys.view event.target.base
  privateSignal a event := sys.participantObs event.target a
  InfoState a := sys.BlindInfo a
  initInfo _ observation _ :=
    { current := observation, past := [], own := [] }
  pushInfo _ info choice observation _ :=
    BlindInfo.push sys info choice observation

/-- **Blindness is exactly discarding the schedule.**

After every history the order-blind information state is the order-forgetting
projection of the order-revealing one.  The two models are related by a
forgetful map and differ in nothing else. -/
theorem blind_infoOf_eq_forgetOrders (a : Participant ι)
    {state : sys.toExecutionProtocol.State}
    (trace : ExecutionProtocol.Trace sys.toExecutionProtocol state) :
    sys.blindSignals.infoOf a trace =
      sys.forgetOrders (sys.revealingSignals.infoOf a trace) := by
  induction trace with
  | start => rfl
  | extend prior joint isLegal realized ih =>
      -- rewrite with `ih` before unfolding the signal records: unfolding first
      -- replaces the head symbol `ih` matches on.
      rw [InfoSignals.infoOf_extend, InfoSignals.infoOf_extend, ih]
      exact (sys.forgetOrders_push _ _ _ _).symm

/-- The observation a participant holds is its observation of the state the
history reached.  This is what makes the menu information-local. -/
theorem revealing_infoOf_current (a : Participant ι)
    {state : sys.toExecutionProtocol.State}
    (trace : ExecutionProtocol.Trace sys.toExecutionProtocol state) :
    (sys.revealingSignals.infoOf a trace).current =
      sys.participantObs state a := by
  induction trace with
  | start => rfl
  | extend prior joint isLegal realized _ih => rfl

/-- **A player can reconstruct the scheduler's complete information history.**

If the scheduler's current view is a projection of player `i`'s observation,
then after every protocol trace its entire perfect-recall information state is
a function of `i`'s information state.  This includes every prior scheduler
choice: realized orders are public and the scheduler is active in every round.

Thus a scheduler satisfying `SchedulerHasNoExtraInformation` has no private
fact or private memory that it can leak to a player through its next order. -/
theorem revealing_schedulerInfo_eq_fromPlayer {i : ι}
    (project : sys.Obs i → sys.SchedulerView)
    (hproject : ∀ state, project (sys.obs state i) = sys.schedulerView state)
    {state : sys.toExecutionProtocol.State}
    (trace : ExecutionProtocol.Trace sys.toExecutionProtocol state) :
    sys.schedulerInfoFromPlayer project
        (sys.revealingSignals.infoOf (.player i) trace) =
      sys.revealingSignals.infoOf (.scheduler : Participant ι) trace := by
  induction trace with
  | start =>
      simp only [InfoSignals.infoOf_start]
      unfold schedulerInfoFromPlayer
      simp only [participantObs, List.map_nil,
        schedulerOwnOfPast]
      rw [hproject]
  | @extend source target prior joint isLegal realized ih =>
      rw [InfoSignals.infoOf_extend, InfoSignals.infoOf_extend,
        sys.schedulerInfoFromPlayer_push, ih]
      change RevealingInfo.push sys
          (sys.revealingSignals.infoOf (.scheduler : Participant ι) prior)
          (some (target.log.headD [])) (project (sys.obs target.base i))
          (target.log.headD []) =
        RevealingInfo.push sys
          (sys.revealingSignals.infoOf (.scheduler : Participant ι) prior)
          (joint (.scheduler : Participant ι))
          (sys.schedulerView target.base) (target.log.headD [])
      have hlog : target.log = sys.scheduledOrder joint :: source.log :=
        sys.log_of_mem_support_step realized
      have horder : target.log.headD [] = sys.scheduledOrder joint := by
        rw [hlog]
        rfl
      have hscheduler := isLegal.2 (.scheduler : Participant ι)
      cases hchoice : joint (.scheduler : Participant ι) with
      | none =>
          rw [hchoice] at hscheduler
          exact False.elim (hscheduler trivial)
      | some order =>
          have hschedule : sys.scheduledOrder joint = order := by
            simp [ScheduledSystem.scheduledOrder, hchoice]
          rw [horder, hschedule, hproject]

/-- The same, order-blind. -/
theorem blind_infoOf_current (a : Participant ι)
    {state : sys.toExecutionProtocol.State}
    (trace : ExecutionProtocol.Trace sys.toExecutionProtocol state) :
    (sys.blindSignals.infoOf a trace).current =
      sys.participantObs state a := by
  induction trace with
  | start => rfl
  | extend prior joint isLegal realized _ih => rfl

namespace RevealingInfo

/-- Reconstruct GameTheory's canonical own-play record from the compact
decision memory carried by a revealing information state. -/
def recalledOwnPlayFrom (sys : ScheduledSystem.{u} ι) (a : Participant ι) :
    List (sys.RevealingSnapshot a × sys.Submission a) →
      List (sys.RevealingInfo a × sys.Submission a)
  | [] => []
  | (snapshot, action) :: prior =>
      ({ current := snapshot.1, past := snapshot.2, own := prior }, action) ::
        recalledOwnPlayFrom sys a prior

def recalledOwnPlay {a : Participant ι} (info : sys.RevealingInfo a) :
    List (sys.RevealingInfo a × sys.Submission a) :=
  recalledOwnPlayFrom sys a info.own

@[simp] theorem recalledOwnPlay_push_none {a : Participant ι}
    (prior : sys.RevealingInfo a) (current : sys.ParticipantObs a)
    (order : sys.Order) :
    recalledOwnPlay sys
        (RevealingInfo.push sys prior none current order) =
      recalledOwnPlay sys prior :=
  rfl

@[simp] theorem recalledOwnPlay_push_some {a : Participant ι}
    (prior : sys.RevealingInfo a) (action : sys.Submission a)
    (current : sys.ParticipantObs a) (order : sys.Order) :
    recalledOwnPlay sys
        (RevealingInfo.push sys prior (some action) current order) =
      (prior, action) :: recalledOwnPlay sys prior := by
  cases prior
  rfl

end RevealingInfo

/-- The order-revealing signals remember exactly the information state and
action at every earlier decision by the participant. -/
theorem revealing_ownPlay_eq_recalled (a : Participant ι)
    {state : sys.toExecutionProtocol.State}
    (trace : ExecutionProtocol.Trace sys.toExecutionProtocol state) :
    sys.revealingSignals.ownPlay a trace =
      RevealingInfo.recalledOwnPlay sys
        (sys.revealingSignals.infoOf a trace) := by
  induction trace with
  | start => rfl
  | @extend source target prior joint isLegal realized ih =>
      rw [InfoSignals.ownPlay_extend, InfoSignals.infoOf_extend]
      cases hchoice : joint a with
      | none =>
          rw [ih]
          exact
            (RevealingInfo.recalledOwnPlay_push_none sys
              (sys.revealingSignals.infoOf a prior)
              (sys.participantObs target a)
              (sys.view target.base, target.log.headD []).2).symm
      | some action =>
          rw [ih]
          exact
            (RevealingInfo.recalledOwnPlay_push_some sys
              (sys.revealingSignals.infoOf a prior) action
              (sys.participantObs target a)
              (sys.view target.base, target.log.headD []).2).symm

/-- The faithful scheduled information model has perfect recall. Revealing a
schedule does not replace the participant's memory of its own earlier
decisions. -/
theorem revealingSignals_perfectRecall :
    sys.revealingSignals.PerfectRecall := by
  intro a first second traceFirst traceSecond hinfo
  rw [sys.revealing_ownPlay_eq_recalled a traceFirst,
    sys.revealing_ownPlay_eq_recalled a traceSecond, hinfo]

private theorem participantMenuAt_adequate (state : sys.State) (a : Participant ι)
    (choice : Option (sys.Submission a)) :
    choice ∈ sys.participantMenuAt a (sys.participantObs state a) ↔
      LegalOption sys.toExecutionProtocol state a choice := by
  cases a with
  | scheduler =>
      cases choice with
      | none =>
          constructor
          · rintro ⟨order, _, hcontra⟩; exact absurd hcontra.symm (Option.some_ne_none order)
          · intro hlegal; exact absurd trivial hlegal
      | some order =>
          constructor
          · rintro ⟨other, hother, hchoice⟩
            have hsame : order = other := Option.some.inj hchoice
            subst hsame
            exact ⟨trivial, hother⟩
          · rintro ⟨_, hmem⟩; exact ⟨order, hmem, rfl⟩
  | player i =>
      cases choice with
      | none => exact sys.menuAt_none state.base i
      | some action => exact sys.menuAt_some state.base i action

/-- The order-revealing information model: the faithful one. -/
@[reducible] def revealingInformation : InformationModel sys.toExecutionProtocol where
  toInfoSignals := sys.revealingSignals
  menu a info := sys.participantMenuAt a info.current
  menu_adequate := by
    intro a state trace choice
    rw [sys.revealing_infoOf_current a trace]
    exact sys.participantMenuAt_adequate state a choice

/-- The faithful scheduled information model remembers every participant's own
earlier decisions. -/
theorem revealingInformation_perfectRecall :
    sys.revealingInformation.PerfectRecall :=
  sys.revealingSignals_perfectRecall

/-- The order-blind information model: the idealization.  Same menus — the
schedule never changes what is legal, only what is known. -/
@[reducible] def blindInformation : InformationModel sys.toExecutionProtocol where
  toInfoSignals := sys.blindSignals
  menu a info := sys.participantMenuAt a info.current
  menu_adequate := by
    intro a state trace choice
    rw [sys.blind_infoOf_current a trace]
    exact sys.participantMenuAt_adequate state a choice

/-! ## Order-oblivious deviations

The honest and robust readings are two classes of policy inside the one faithful
game.  A policy is *order-oblivious* when the schedule cannot change what it
does; that restricts what a participant reads, never what it can express. -/

/-- A policy is order-oblivious when it acts the same at any two information
states differing only in schedule.

Phrased on the action rather than the menu-certified choice, whose type depends
on the information state; the action's does not. -/
def OrderOblivious {a : Participant ι}
    (policy : sys.revealingInformation.Policy a) : Prop :=
  ∀ left right : sys.RevealingInfo a,
    sys.forgetOrders left = sys.forgetOrders right →
      (policy left).1 = (policy right).1

/-- Read an order-blind policy as an order-revealing one by discarding the
schedule first.

This typechecks without transport because `forgetOrders` preserves the current
observation and both menus are `participantMenuAt` of it, so the two `Choice`
types are definitionally equal. -/
def liftPolicy {a : Participant ι} (policy : sys.blindInformation.Policy a) :
    sys.revealingInformation.Policy a :=
  fun info => policy (sys.forgetOrders info)

/-- Everything an order-blind participant could have played is order-oblivious,
so the honest class is not an artificial restriction: it contains the image of
every schedule-free policy. -/
theorem liftPolicy_orderOblivious {a : Participant ι}
    (policy : sys.blindInformation.Policy a) :
    sys.OrderOblivious (sys.liftPolicy policy) := by
  intro left right hforget
  change (policy (sys.forgetOrders left)).1 = (policy (sys.forgetOrders right)).1
  rw [hforget]

/-! ## Silence, and how it differs from declining

Vegas already has a way to decline, and it is not this one.  A surface `yield`
lowers to a *nullable* sealed commitment; `Expr.nullableCommitGuard` accepts
`declineValue` unconditionally (`evalExpr_nullableCommitGuard_declineValue`),
and
`nullableCommitGuard_satisfiable` turns that into liveness — whatever the
environment, `declineValue` is an accepted submission.  The continuation is typed at
`option b` and eliminates it with `isNone`/`getD`, so a program *must* say what
happens when a player declines, and may charge for it on the spot.  Declining is
therefore a source strategy needing no back-translation, and the plain `commit`
form — payload restricted by `CommitPayloadTy`, hence non-nullable — is the
deliberate opposite: the form that obliges a player to act.

What that leaves uncovered is a player who sends nothing at all.  The two are
easy to conflate because both are called `none`, and they are not the same
`none`.  Submitting the null *value* is `some (declineValue b)`: a real submission,
legal, and exactly the source-level decline — `AllowsDeclining` at this layer.
`IsLegalJoint`'s `none` is the absence of any submission, which it permits only
to an inactive participant and which no public runtime can actually prevent.

The distinction decides where a penalty can come from.  A null submission is a
transaction — the program sees it, continues, and can slash a deposit
immediately.  Silence is not: `silence_inert` leaves the player-controlled phase
where it was.  The system's automatic `settle` phase may still run, but it cannot
attribute a submitted action to the silent player.  A protocol wanting to charge
that player must measure elapsed time or another external signal.  That is what
a timeout is for.

`AllowsSilence` names the residual gap and nothing more.  It does not show that
silence fails to pay — a statement about payoffs, a layer up. The general
commitment/action bridge is the compiler-derived `Machine.Program.serializedSystem`;
what is not established here is the stronger nullable-fragment theorem that
every compiled source `yield` furnishes an `AllowsDeclining` witness. -/

/-- A runtime in which every player always has an accepted submission.

The protocol-layer image of a nullable commitment: `declineValue` is accepted by
`Expr.nullableCommitGuard` whatever the environment, so a compiled `yield`
affords exactly this.  Note what it does *not* say — nothing about the effect.
A decline is a submission the program sees, so it may move the state and may be
charged for.  That is the whole difference from `AllowsSilence`. -/
structure AllowsDeclining (sys : ScheduledSystem.{u} ι) where
  /-- The declining submission. -/
  decline : (i : ι) → sys.Action i
  /-- It is always accepted, so no program condition can make declining
  illegal. -/
  decline_available : ∀ (state : sys.Base) (i : ι),
    decline i ∈ sys.available state i

/-- A runtime affording a participant to send nothing, modelled as an inert
action rather than as `IsLegalJoint`'s `none`.

Carried separately rather than as a field, because a system either affords it or
does not — `race_no_silence` shows the difference is real. -/
structure AllowsSilence (sys : ScheduledSystem.{u} ι) where
  /-- Sending nothing, as an action. -/
  silence : (i : ι) → sys.Action i
  /-- A runtime cannot prevent it. -/
  silence_available : ∀ (state : sys.Base) (i : ι), silence i ∈ sys.available state i
  /-- It moves nothing, so no penalty for it can be imposed by the silent
  participant's own submission.  Contrast a null submission, which is a
  transaction the program sees and can charge for. -/
  silence_inert : ∀ (state : sys.Base) (i : ι),
    sys.applyOne state i (silence i) = FinDist.pure state

/-- **Silence is a decline that also happens to be invisible.**

One direction only.  Every silent runtime affords declining, by forgetting that
the submission was inert; the converse fails, and `race_allowsDeclining` with
`race_no_silence` is the witness.  The gap between them is exactly the room a
protocol has to charge for declining. -/
def AllowsSilence.toAllowsDeclining {sys : ScheduledSystem.{u} ι}
    (hsilent : sys.AllowsSilence) : sys.AllowsDeclining where
  decline := hsilent.silence
  decline_available := hsilent.silence_available

/-- Everyone silent, with the scheduler proposing `order`. -/
def AllowsSilence.allSilent {sys : ScheduledSystem.{u} ι} (hsilent : sys.AllowsSilence)
    (order : sys.Order) : (a : Participant ι) → Option (sys.Submission a)
  | .scheduler => some order
  | .player i => some (hsilent.silence i)

/-- **The all-silent player phase is well defined and schedule-independent.**

When every player is silent, applying the player actions leaves the state where
it was in every order.  A following automatic `settle` phase is intentionally
outside this lemma and may move the system independently of those submissions.
No `EffectsCommute` hypothesis is needed: inert player actions commute with
everything. -/
theorem AllowsSilence.applyOrder_silent {sys : ScheduledSystem.{u} ι}
    (hsilent : sys.AllowsSilence) :
    ∀ (order proposed : sys.Order) (state : sys.Base),
      sys.applyOrder (hsilent.allSilent proposed) order state = FinDist.pure state
  | [], _, _ => rfl
  | i :: rest, proposed, state => by
      simp only [applyOrder, AllowsSilence.allSilent, hsilent.silence_inert,
        FinDist.pure_bind]
      exact hsilent.applyOrder_silent rest proposed state

end ScheduledSystem

/-! ## Witnesses

Both facts below would be worthless if their hypotheses could not be met, so
they are met in the most extreme case available: a system whose actions are the
*identity*, so every pair of submissions commutes and the underlying state law
is literally constant.  Schedules remain distinguishable, and an order-aware
policy remains expressible.  Nothing weaker than recording the order could see
either, which is the argument for recording it. -/

/-- Two players, a binary submission each, and a state nothing changes.
Maximally confluent: every action is the identity. -/
def coinSystem : ScheduledSystem.{0} (Fin 2) where
  Base := Unit
  Action _ := Bool
  init := ()
  active _ _ := True
  available _ _ := Set.univ
  terminal _ := False
  applyOne state _ _ := FinDist.pure state
  settle state := FinDist.pure state
  View := Unit
  view _ := ()
  SchedulerView := Unit
  schedulerView _ := ()
  Obs _ := Unit
  obs _ _ := ()
  menuAt _ _ := {some true, some false}
  menuAt_some _ _ action := by cases action <;> simp
  menuAt_none _ _ := by simp
  schedules _ := Set.univ
  schedules_nonempty _ := ⟨[], Set.mem_univ _⟩
  progress _ _ := ⟨fun _ => some true, fun _ => ⟨trivial, Set.mem_univ _⟩⟩

/-- A round in which both players submit and the scheduler picks `order`. -/
def coinRound (order : coinSystem.Order) (state : coinSystem.State) :
    { joint // coinSystem.toExecutionProtocol.Legal state joint } :=
  ⟨fun a =>
      match a with
      | .scheduler => some order
      | .player _ => some true,
    not_false, by
      intro a
      cases a with
      | scheduler => exact ⟨trivial, Set.mem_univ _⟩
      | player i => exact ⟨trivial, Set.mem_univ _⟩⟩

@[simp] theorem coinRound_scheduledOrder (order : coinSystem.Order)
    (state : coinSystem.State) :
    coinSystem.scheduledOrder (coinRound order state).1 = order := rfl

/-- **The separation is realized.**  Two schedules over a system in which every
action is the identity — so the underlying state law is the same constant either
way — nevertheless induce different successor laws, because the realized order
is part of what a participant observes. -/
theorem coin_step_ne (state : coinSystem.State) :
    coinSystem.toExecutionProtocol.step state (coinRound [0, 1] state) ≠
      coinSystem.toExecutionProtocol.step state (coinRound [1, 0] state) := by
  refine coinSystem.step_ne_of_order_ne ?_
  simp only [coinRound_scheduledOrder]
  intro horder
  exact absurd (List.cons.inj horder).1 (by decide)

@[simp] theorem coin_menu (i : Fin 2)
    (info : coinSystem.revealingInformation.InfoState (.player i)) :
    coinSystem.revealingInformation.menu (.player i) info =
      {some true, some false} := rfl

/-- A history in which player `0` was ordered first. -/
def coinFirstZero (i : Fin 2) : coinSystem.RevealingInfo (.player i) :=
  { current := (), past := [([0, 1], ())], own := [] }

/-- The same history except that player `1` was ordered first.  The two agree on
every observation and differ only in schedule. -/
def coinFirstOne (i : Fin 2) : coinSystem.RevealingInfo (.player i) :=
  { current := (), past := [([1, 0], ())], own := [] }

theorem coinFirst_forgetOrders_eq (i : Fin 2) :
    coinSystem.forgetOrders (coinFirstZero i) =
      coinSystem.forgetOrders (coinFirstOne i) := rfl

/-- An order-aware policy: submit `true` exactly when player `0` was ordered
first.  Nothing about the state differs between those histories. -/
def coinOrderAware (i : Fin 2) :
    coinSystem.revealingInformation.Policy (.player i) :=
  fun info =>
    if (info.past.headD ([], ())).1 = [0, 1] then
      ⟨some true, Set.mem_insert _ _⟩
    else
      ⟨some false, Set.mem_insert_of_mem _ rfl⟩

/-- **The order-oblivious class is proper.**

`coinOrderAware` acts differently at two histories that agree on every
observation and differ only in how a round was ordered, so it is not
order-oblivious —
and by `liftPolicy_orderOblivious` no schedule-free policy induces it.

This is not a counterexample to player-equilibrium preservation: distinct
policies can have the same payoff. Independent-signal Nash preservation is
proved in `Participant.RandomIndependentSignal.isPlayerNash_iff`; applying it
to an executing scheduler requires a separate source-policy construction.
This example only proves that a single order-oblivious policy cannot
reproduce both action branches. -/
theorem coinOrderAware_not_orderOblivious (i : Fin 2) :
    ¬ coinSystem.OrderOblivious (coinOrderAware i) := by
  intro hoblivious
  have hcongr := hoblivious (coinFirstZero i) (coinFirstOne i)
    (coinFirst_forgetOrders_eq i)
  simp only [coinFirstZero, Fin.isValue, coinOrderAware,
    List.headD_eq_head?_getD, List.head?_cons, Option.getD_some, ↓reduceIte,
    coinFirstOne, List.cons.injEq, one_ne_zero, zero_ne_one, and_true,
    and_self] at hcongr
  exact Bool.noConfusion (Option.some.inj hcongr)

/-! ## A runtime that is permissive and still safe

`coinSystem` shows the separation exists but is a weak witness for commutation:
every action is the identity, so of course order does not matter.  The system
below is the honest case.  Two players each add to a running total, the runtime
accepts either order, and the total genuinely changes — yet addition commutes,
so the reachable state does not depend on who went first.

This is the configuration the permissive tier is for.  Order-aware deviations
exist and are expressible; the scheduler really does choose; and none of it can
move the total.  `counter_step_ne` and `counter_step_base_eq` are the two halves
of the point, and they are deliberately stated about the very same pair of
rounds: the successor laws differ, because the log records the order, while the
laws over *totals* coincide.  A payoff reading the total is untouched; a payoff
reading the log is not.  That is why payoff-irrelevance needs the game to be
schedule-blind and cannot be read off the runtime alone. -/

/-- Two players who each add a number to a running total, with the runtime free
to order them either way.  Reducible so that `Base`, `View` and `Action` line up
with `Nat` at instance transparency, which numerals need. -/
@[reducible] def counterSystem : ScheduledSystem.{0} (Fin 2) where
  Base := Nat
  Action _ := Nat
  init := 0
  active _ _ := True
  available _ _ := Set.univ
  terminal _ := False
  applyOne state _ amount := FinDist.pure (state + amount)
  settle state := FinDist.pure state
  View := Nat
  view state := state
  SchedulerView := Unit
  schedulerView _ := ()
  Obs _ := Nat
  obs state _ := state
  menuAt _ _ := {choice | choice ≠ none}
  menuAt_some _ _ action := by
    constructor
    · intro _; exact ⟨trivial, Set.mem_univ _⟩
    · intro _; exact Option.some_ne_none action
  menuAt_none _ _ := by
    constructor
    · intro hmem; exact absurd rfl hmem
    · intro hcontra; exact absurd trivial hcontra
  schedules _ := {[0, 1], [1, 0]}
  schedules_nonempty _ := ⟨[0, 1], Set.mem_insert _ _⟩
  progress _ _ := ⟨fun _ => some 0, fun _ => ⟨trivial, Set.mem_univ _⟩⟩

/-- **The permissive runtime is genuinely permissive.**  Both orders are
accepted, so the scheduler has a real choice to make and `EnforcesOrder` fails.
Every result below therefore holds without enforcement. -/
theorem counter_not_enforcesOrder : ¬ counterSystem.EnforcesOrder := by
  intro henforce
  have hcontra := henforce () (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)
  exact absurd (List.cons.inj hcontra).1 (by decide)

/-- Resolving a round one player at a time, with the effect on the total made
explicit.  Stated separately because `applyOne` returning a point mass is what
collapses the bind. -/
private theorem counter_applyOrder_cons (joint) (i : Fin 2) (rest total) :
    counterSystem.applyOrder joint (i :: rest) total =
      match joint (.player i) with
      | none => counterSystem.applyOrder joint rest total
      | some amount => counterSystem.applyOrder joint rest (total + amount) := by
  cases hjoint : joint (.player i) with
  | none => simp only [ScheduledSystem.applyOrder, hjoint]
  | some amount =>
      simp only [ScheduledSystem.applyOrder, hjoint]
      exact FinDist.pure_bind _ _

/-- **And it is nevertheless safe.**  Addition commutes, so both accepted orders
carry a state to the same law even though each player's action moves it. -/
theorem counter_effectsCommute : counterSystem.EffectsCommute := by
  intro joint state _hlegal left right hleft hright
  simp only [ScheduledSystem.resolveOrder, counterSystem,
    FinDist.bind_pure]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hleft hright
  rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl <;>
    simp only [counter_applyOrder_cons] <;>
    cases joint (.player 0) <;> cases joint (.player 1) <;>
    simp only [ScheduledSystem.applyOrder] <;>
    first
      | rfl
      | exact congrArg FinDist.pure (by omega)

/-- A round in which both players add `1` and the scheduler picks `order`. -/
def counterRound (state : counterSystem.State) (order : counterSystem.Order)
    (horder : order ∈
      counterSystem.schedules (counterSystem.schedulerView state.base)) :
    { joint // counterSystem.toExecutionProtocol.Legal state joint } :=
  ⟨fun a =>
      match a with
      | .scheduler => some order
      | .player _ => some 1,
    not_false, by
      intro a
      cases a with
      | scheduler => exact ⟨trivial, horder⟩
      | player i => exact ⟨trivial, Set.mem_univ _⟩⟩

@[simp] theorem counterRound_scheduledOrder (state order horder) :
    counterSystem.scheduledOrder (counterRound state order horder).1 = order := rfl

/-- The first-player-first round at `state`. -/
def counterZeroFirst (state : counterSystem.State) :
    { joint // counterSystem.toExecutionProtocol.Legal state joint } :=
  counterRound state [0, 1] (Set.mem_insert _ _)

/-- The same round, ordered the other way. -/
def counterOneFirst (state : counterSystem.State) :
    { joint // counterSystem.toExecutionProtocol.Legal state joint } :=
  counterRound state [1, 0] (Set.mem_insert_of_mem _ rfl)

/-- **The schedule remains observable.**  The two accepted orders induce
different successor laws, because the realized order is recorded. -/
theorem counter_step_ne (state : counterSystem.State) :
    counterSystem.toExecutionProtocol.step state (counterZeroFirst state) ≠
      counterSystem.toExecutionProtocol.step state (counterOneFirst state) := by
  refine counterSystem.step_ne_of_order_ne ?_
  simp only [counterZeroFirst, counterOneFirst, counterRound_scheduledOrder]
  intro horder
  exact absurd (List.cons.inj horder).1 (by decide)

/-- **And is nevertheless payoff-inert for a schedule-blind game.**  The very
same two rounds carry the running total to the same law.  A utility reading the
total cannot separate them; only one reading the log can. -/
theorem counter_step_base_eq (state : counterSystem.State) :
    (counterSystem.toExecutionProtocol.step state
        (counterZeroFirst state)).map ScheduledSystem.State.base =
      (counterSystem.toExecutionProtocol.step state
        (counterOneFirst state)).map ScheduledSystem.State.base :=
  counterSystem.step_base_eq_of_effectsCommute counter_effectsCommute fun _ => rfl

/-- **Silence is available here.**  Adding zero is permitted and moves nothing,
so a player can vanish from a round undetectably. -/
def counter_allowsSilence : counterSystem.AllowsSilence where
  silence _ := 0
  silence_available _ _ := Set.mem_univ _
  silence_inert state _ := congrArg FinDist.pure (Nat.add_zero state)

/-! ## Where the permissive tier runs out

`EffectsCommute` would be worthless as a hypothesis if it held of every system,
so here is one it fails for.  Two players act on a total, one doubling it and one
adding to it.  Doubling and adding do not commute, the two accepted orders reach
different totals, and no amount of care about what the *game* reads can repair
that — the disagreement is in the runtime.

This is the smallest form of the problem a public runtime actually has: two
pending operations whose order changes the result.  A system in this shape is
where `EnforcesOrder` has to be paid for, and it is the reason enforcement stays
available rather than being argued away. -/

private theorem finDist_pure_ne {α : Type} {a b : α} (hne : a ≠ b) :
    FinDist.pure a ≠ FinDist.pure b := by
  intro heq
  have hprob : (FinDist.pure a).prob a = (FinDist.pure b).prob a := by rw [heq]
  rw [FinDist.prob_pure_self, FinDist.prob_pure_of_ne hne] at hprob
  exact absurd hprob one_ne_zero

/-- Two players acting on a total: player `0` doubles it, player `1` adds one. -/
@[reducible] def raceSystem : ScheduledSystem.{0} (Fin 2) where
  Base := Nat
  Action _ := Unit
  init := 1
  active _ _ := True
  available _ _ := Set.univ
  terminal _ := False
  applyOne state i _ := FinDist.pure (if i = 0 then state * 2 else state + 1)
  settle state := FinDist.pure state
  View := Nat
  view state := state
  SchedulerView := Unit
  schedulerView _ := ()
  Obs _ := Nat
  obs state _ := state
  menuAt _ _ := {choice | choice ≠ none}
  menuAt_some _ _ action := by
    constructor
    · intro _; exact ⟨trivial, Set.mem_univ _⟩
    · intro _; exact Option.some_ne_none action
  menuAt_none _ _ := by
    constructor
    · intro hmem; exact absurd rfl hmem
    · intro hcontra; exact absurd trivial hcontra
  schedules _ := {[0, 1], [1, 0]}
  schedules_nonempty _ := ⟨[0, 1], Set.mem_insert _ _⟩
  progress _ _ := ⟨fun _ => some (), fun _ => ⟨trivial, Set.mem_univ _⟩⟩

/-- Both players act, and the scheduler proposes `order`. -/
private def raceJoint (order : raceSystem.Order) :
    (a : Participant (Fin 2)) → Option (raceSystem.Submission a)
  | .scheduler => some order
  | .player _ => some ()

/-- **`EffectsCommute` is a real restriction.**  Doubling then adding reaches
`11` from `5`; adding then doubling reaches `12`.  So the permissive tier does
not cover every runtime, and for a system in this shape a preservation claim
needs `EnforcesOrder` rather than an argument that order does not matter. -/
theorem race_not_effectsCommute : ¬ raceSystem.EffectsCommute := by
  intro hcommute
  have hcontra := hcommute (raceJoint [0, 1]) 5
    (by
      intro i
      simp only [raceJoint]
      exact ⟨trivial, Set.mem_univ _⟩)
    (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)
  have hleft : raceSystem.applyOrder (raceJoint [0, 1]) [0, 1] 5 = FinDist.pure 11 := by
    simp only [ScheduledSystem.applyOrder, raceJoint, FinDist.pure_bind]
    norm_num
  have hright : raceSystem.applyOrder (raceJoint [0, 1]) [1, 0] 5 = FinDist.pure 12 := by
    simp only [ScheduledSystem.applyOrder, raceJoint, FinDist.pure_bind]
    norm_num
  simp only [ScheduledSystem.resolveOrder, raceSystem,
    FinDist.bind_pure] at hcontra
  rw [hleft, hright] at hcontra
  exact absurd hcontra (finDist_pure_ne (by decide))

/-- **Declining is available even here.**  Every action is accepted, so a player
can always submit something — and in `raceSystem` that submission necessarily
moves the total, which is the point. -/
def race_allowsDeclining : raceSystem.AllowsDeclining where
  decline _ := ()
  decline_available _ _ := Set.mem_univ _

/-- **And silence is a real restriction too.**  Every `raceSystem` action moves
the total, so none is inert and no player can vanish without trace.  A system can
fail to afford silence, which is why `AllowsSilence` is a hypothesis rather than
a field of `ScheduledSystem`. -/
theorem race_no_silence : IsEmpty raceSystem.AllowsSilence := by
  constructor
  intro hsilent
  have hinert := hsilent.silence_inert 1 0
  rw [show raceSystem.applyOne 1 0 (hsilent.silence 0) = FinDist.pure 2 from rfl] at hinert
  exact absurd hinert (finDist_pure_ne (by decide))

end Vegas
