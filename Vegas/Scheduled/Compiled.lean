/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Confluence
import Vegas.EventGraph.Protocol
import Vegas.Scheduled.Basic
import Vegas.Scheduled.Order

/-!
# The serialized counterfactual for a compiled program

`Vegas.Scheduled.Basic` reasons about scheduling over an abstract system, while
`EventGraph.toExecutionProtocol` compiles a program to a protocol that resolves a
whole frontier atomically.  This module derives serialized counterfactuals from
the same compiled graph so the two semantics can be compared without treating
them as unrelated models.

## What is built here, and what it is not

This is **not** the compiled protocol.  That one applies a frontier packet as a
single joint action, with no scheduler coordinate at all
(`toExecutionProtocol_step_eq_pure_applyFrontier`), so no strategy in it can
condition on an order.

What is built here is the *counterfactual*: the same graph, run by a runtime
that applies one player's submission at a time in an order it chooses and
publishes.  It is the implementation a compiler would produce if it serialized
the frontier instead of exposing it whole. Having both as instances of one
interface is what lets the comparison be stated rather than described.

## Why menus need the private channel

A player's legal frontier action is fixed by its *own* observation
(`FrontierAction.available_iff_of_observe_eq`), which includes values sealed to
it; `publicObserve` sees only unowned fields.  So `Obs` here is the pair of the
public observation and the player's own — the public part carries activity,
which depends on global readiness, and the private part carries availability.
This is exactly the requirement that made `ScheduledSystem` grow `Obs` in the
first place.

## Proved boundary

The permissive serializer admits exactly the orders of the active players, its
automatic phase reaches a stable checkpoint within `G.nodeCount` internal
steps, and `serializedSystem_effectsCommute` proves that every accepted order
has the same settled graph effect.  Order is still public in the protocol log.

The scheduler may condition on the complete public graph observation and its
own earlier public orders.  It sees neither sealed values nor the players'
simultaneous submissions in the round it is ordering.  Every accepted order
nevertheless implements exactly the same atomic graph successor, so this
public-state dependence does not weaken the operational theorem.

The fixed serializer uses the executable policy in `Vegas.Scheduled.Order`:
compute activity from the public observation and sort active players by a
backend-supplied `LinearOrder`.  It selects one order and makes the scheduler
coordinate operationally inert.  The generic signal theorems in
`Vegas.Scheduled.Strategic` separately prove Nash preservation under an
independent public signal. They do not yet back-translate arbitrary
history-aware deviations in this serializer into source behavioral policies.
-/

noncomputable section

namespace Vegas

open GameTheory.Protocol
open GameTheory.Math.Probability
open EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

namespace EventGraph


/-- Apply exactly the writes selected by one frontier action.  The reachability
check only totalizes the function on malformed calls; legal serialized rounds
prove that every checked target is reachable. -/
noncomputable def applySerializedAction {G : Graph Player L}
    (state : ReachableConfig G) {who : Player}
    (action : FrontierAction G who) : ReachableConfig G := by
  let target := state.1.completeNodes (actionWrites action)
  if hreachable : Reachable G target then
    exact ⟨target, hreachable⟩
  else
    exact state

omit [Fintype Player] in
theorem applySerializedAction_eq_of_reachable
    {G : Graph Player L} (state : ReachableConfig G) {who : Player}
    (action : FrontierAction G who)
    (hreachable : Reachable G
      (state.1.completeNodes (actionWrites action))) :
    applySerializedAction state action =
      ⟨state.1.completeNodes (actionWrites action), hreachable⟩ := by
  apply Subtype.ext
  simp [applySerializedAction, hreachable]

/-- Deterministic serialized execution before automatic settlement. -/
noncomputable def applySerializedOrder {G : Graph Player L}
    (joint : ∀ who, Option (FrontierAction G who)) :
    List Player → ReachableConfig G → ReachableConfig G
  | [], state => state
  | who :: rest, state =>
      match joint who with
      | none => applySerializedOrder joint rest state
      | some action =>
          applySerializedOrder joint rest
            (applySerializedAction state action)

/-- Being obliged to move, in the compiled protocol's sense. -/
def ActiveAt (G : Graph Player L) (cfg : Config G) (who : Player) : Prop :=
  ¬ Terminal G cfg ∧ readyInternalNodes G cfg = ∅ ∧ who ∈ activePlayers G cfg

/-- Activity is public.  It depends only on the completed-node downset: node
ownership and prerequisites are graph data, not sealed values. -/
theorem activeAt_iff_of_done_eq {G : Graph Player L} {left right : Config G}
    {who : Player}
    (hdone : left.done = right.done) :
    ActiveAt G left who ↔ ActiveAt G right who := by
  have hterminal : Terminal G left ↔ Terminal G right := by
    unfold Terminal
    rw [hdone]
  have hinternal : readyInternalNodes G left = readyInternalNodes G right := by
    classical
    apply Finset.ext
    intro node
    simp only [readyInternalNodes, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨row, hrow, hkind, hnode⟩
      exact ⟨row, hrow, hkind, by simpa [Ready, hdone] using hnode⟩
    · rintro ⟨row, hrow, hkind, hnode⟩
      exact ⟨row, hrow, hkind, by simpa [Ready, hdone] using hnode⟩
  have hready : ∀ actor,
      readyCommitNodes G left actor = readyCommitNodes G right actor := by
    intro actor
    apply Finset.ext
    intro node
    simp only [readyCommitNodes, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨row, guard, hrow, hsem, hnode⟩
      exact ⟨row, guard, hrow, hsem, by simpa [Ready, hdone] using hnode⟩
    · rintro ⟨row, guard, hrow, hsem, hnode⟩
      exact ⟨row, guard, hrow, hsem, by simpa [Ready, hdone] using hnode⟩
  have hactive : activePlayers G left = activePlayers G right := by
    classical
    unfold activePlayers
    ext actor
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hready actor]
  unfold ActiveAt
  rw [hinternal, hactive]
  exact and_congr_left' (not_congr hterminal)

/-- Equal public observations in particular have equal completed-node sets, so
they induce the same activity. -/
theorem activeAt_iff_of_public_eq {G : Graph Player L} {left right : Config G}
    {who : Player}
    (hpublic : publicObserve G left = publicObserve G right) :
    ActiveAt G left who ↔ ActiveAt G right who := by
  apply activeAt_iff_of_done_eq
  exact congrArg PublicObservation.done hpublic

/-- The same fact when both public and private observations are available. -/
theorem activeAt_iff_of_obs_eq {G : Graph Player L} {left right : Config G}
    {who : Player}
    (hpublic : publicObserve G left = publicObserve G right)
    (_hown : observe G left who = observe G right who) :
    ActiveAt G left who ↔ ActiveAt G right who :=
  activeAt_iff_of_public_eq hpublic

/-- Players active at a public view.  The existential makes this total on
unrealizable observations; public determinacy makes it exact on every view
actually produced by a configuration. -/
def ActiveAtView (G : Graph Player L) (seen : PublicObservation G)
    (who : Player) : Prop :=
  ∃ cfg : Config G, publicObserve G cfg = seen ∧ ActiveAt G cfg who

theorem activeAtView_iff {G : Graph Player L} (state : Config G) (who : Player) :
    ActiveAtView G (publicObserve G state) who ↔ ActiveAt G state who := by
  constructor
  · rintro ⟨witness, hpublic, hactive⟩
    exact (activeAt_iff_of_public_eq hpublic).mp hactive
  · intro hactive
    exact ⟨state, rfl, hactive⟩

/-- What a participant's own view permits it to submit. -/
def MenuAllows (G : Graph Player L) (cfg : Config G) (who : Player) :
    Option (FrontierAction G who) → Prop
  | none => ¬ ActiveAt G cfg who
  | some action => ActiveAt G cfg who ∧ FrontierAction.Available G cfg who action

/-- **What a player may submit is fixed by what it sees.**

Activity comes from the public part, availability from the player's own.  This
is the obligation `ScheduledSystem` imposes, and it is satisfiable here only
because the observation is the pair: no function of the public view alone
decides a Vegas player's menu. -/
theorem menuAllows_iff_of_obs_eq {G : Graph Player L} (hwf : G.WF)
    {left right : Config G} {who : Player}
    (hpublic : publicObserve G left = publicObserve G right)
    (hown : observe G left who = observe G right who)
    (choice : Option (FrontierAction G who)) :
    MenuAllows G left who choice ↔ MenuAllows G right who choice := by
  cases choice with
  | none => exact not_congr (activeAt_iff_of_obs_eq hpublic hown)
  | some action =>
      exact and_congr (activeAt_iff_of_obs_eq hpublic hown)
        (FrontierAction.available_iff_of_observe_eq hwf hown)

/-! ## Automatic closure

A serialized player frontier is not a complete graph round.  It can enable
samples and reveals, and those internal events must run before the next player
frontier is offered.  The generic scheduled model exposes this phase as
`ScheduledSystem.settle`; the compiled instance discharges it by repeatedly
using the event graph's own internal-step law.
-/

/-- Execute the same ready internal event selected by the canonical graph
protocol. -/
noncomputable def stepReadyInternal {G : Graph Player L} (hwf : G.WF)
    (state : ReachableConfig G)
    (hinternal : (readyInternalNodes G state.1).Nonempty) :
    FinDist (ReachableConfig G) := by
  let node := Classical.choose hinternal
  have hready : ReadyInternalNode G state.1 node :=
    (Finset.mem_filter.mp (Classical.choose_spec hinternal)).2
  have havailable : InternalAvailable G state.1 { node := node } :=
    InternalAvailable.of_readyInternalNode hwf
      (reachable_storeCoherent hwf state.2) hready
  exact stepAvailable G state
    (.internal { node := node } (Classical.choice havailable))

/-- The serializer's automatic one-node transition is exactly the canonical
source protocol's transition whenever internal work is ready. Player actions
and their strategies are not consulted in either expression. -/
theorem toExecutionProtocol_step_eq_stepReadyInternal
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (state : ReachableConfig G)
    (legal : { joint : ∀ who, Option (FrontierAction G who) //
      (toExecutionProtocol G hwf hguards).Legal state joint })
    (hinternal : (readyInternalNodes G state.1).Nonempty) :
    (toExecutionProtocol G hwf hguards).step state legal =
      stepReadyInternal hwf state hinternal := by
  unfold stepReadyInternal
  change (if _hinternal :
      (readyInternalNodes G state.1).Nonempty then _ else _) = _
  exact dif_pos hinternal

omit [Fintype Player] in
/-- Every successor of a selected internal event strictly advances the graph
downset. -/
theorem stepReadyInternal_done_ssubset {G : Graph Player L} (hwf : G.WF)
    (state : ReachableConfig G)
    (hinternal : (readyInternalNodes G state.1).Nonempty)
    {next : ReachableConfig G}
    (hnext : next ∈ (stepReadyInternal hwf state hinternal).support) :
    state.1.done ⊂ next.1.done := by
  unfold stepReadyInternal at hnext
  exact done_ssubset_of_stepAvailable_support G state _ hnext

/-- Run at most `fuel` ready internal nodes.  Each recursive call consumes one
unit of fuel and one graph node, so `G.nodeCount` suffices to reach the next
strategic checkpoint. -/
noncomputable def settleInternal {G : Graph Player L} (hwf : G.WF) :
    Nat → ReachableConfig G → FinDist (ReachableConfig G)
  | 0, state => FinDist.pure state
  | fuel + 1, state =>
      if hinternal : (readyInternalNodes G state.1).Nonempty then
        (stepReadyInternal hwf state hinternal).bind
          (settleInternal hwf fuel)
      else
        FinDist.pure state

/-- The canonical source command at an internal-only state. A ready internal
node witnesses nontermination, while every player is inactive because the
protocol does not offer a strategic frontier until internal work is exhausted. -/
noncomputable def sourceInternalCommand {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    (state : ReachableConfig G)
    (hinternal : (readyInternalNodes G state.1).Nonempty) :
    { joint : ∀ who, Option (FrontierAction G who) //
      (toExecutionProtocol G hwf hguards).Legal state joint } := by
  let source := toExecutionProtocol G hwf hguards
  have hterminal : ¬ Terminal G state.1 := by
    intro hterminal
    obtain ⟨node, hnode⟩ := hinternal
    have hready : ReadyInternalNode G state.1 node :=
      (Finset.mem_filter.mp hnode).2
    rcases hready with ⟨_row, _hrow, _hkind, hready⟩
    exact hready.1 (hterminal node)
  have hinactive : ∀ who, ¬ source.active state who := by
    intro who hactive
    exact (Finset.not_nonempty_iff_eq_empty.mpr hactive.2.1) hinternal
  exact ⟨source.noop, source.noop_isLegal hterminal hinactive⟩

omit [Fintype Player] in
@[simp] theorem settleInternal_zero {G : Graph Player L} (hwf : G.WF)
    (state : ReachableConfig G) :
    settleInternal hwf 0 state = FinDist.pure state := rfl

omit [Fintype Player] in
theorem settleInternal_of_no_internal {G : Graph Player L} (hwf : G.WF)
    (fuel : Nat) (state : ReachableConfig G)
    (hempty : readyInternalNodes G state.1 = ∅) :
    settleInternal hwf fuel state = FinDist.pure state := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [settleInternal]
      rw [dif_neg (Finset.not_nonempty_iff_eq_empty.mpr hempty)]

omit [Fintype Player] in
theorem settleInternal_succ_of_internal {G : Graph Player L} (hwf : G.WF)
    (fuel : Nat) (state : ReachableConfig G)
    (hinternal : (readyInternalNodes G state.1).Nonempty) :
    settleInternal hwf (fuel + 1) state =
      (stepReadyInternal hwf state hinternal).bind
        (settleInternal hwf fuel) := by
  simp only [settleInternal]
  rw [dif_pos hinternal]

/-- Every recursive settlement step is literally a legal source-protocol
transition followed by the remaining closure. Thus settlement compresses
ordinary source steps without changing sample laws or reveal effects. -/
theorem settleInternal_succ_eq_source_step
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    (fuel : Nat) (state : ReachableConfig G)
    (hinternal : (readyInternalNodes G state.1).Nonempty) :
    settleInternal hwf (fuel + 1) state =
      ((toExecutionProtocol G hwf hguards).step state
          (sourceInternalCommand hwf hguards state hinternal)).bind
        (settleInternal hwf fuel) := by
  rw [settleInternal_succ_of_internal hwf fuel state hinternal,
    toExecutionProtocol_step_eq_stepReadyInternal
      G hwf hguards state _ hinternal]

omit [Fintype Player] in
/-- If the fuel covers every graph node not already completed, every supported
settlement result is a strategic checkpoint: no internal event remains ready. -/
theorem settleInternal_support_no_internal_of_card_add
    {G : Graph Player L} (hwf : G.WF)
    (fuel : Nat) (state : ReachableConfig G) {next : ReachableConfig G}
    (hcapacity : G.nodeCount ≤ state.1.done.card + fuel)
    (hnext : next ∈ (settleInternal hwf fuel state).support) :
    readyInternalNodes G next.1 = ∅ := by
  induction fuel generalizing state next with
  | zero =>
      rw [settleInternal_zero, FinDist.mem_support_pure] at hnext
      subst next
      have hcard_le : state.1.done.card ≤ G.nodeCount := by
        have hsubset : state.1.done ⊆
            (Finset.univ : Finset (Fin G.nodeCount)) := by
          intro node _hnode
          exact Finset.mem_univ node
        simpa using Finset.card_le_card hsubset
      have hcard : state.1.done.card = G.nodeCount := by omega
      have hdone : state.1.done = Finset.univ :=
        Finset.eq_univ_of_card state.1.done (by
          simpa only [Fintype.card_fin] using hcard)
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro node hnode
      have hreadyInternal := (Finset.mem_filter.mp hnode).2
      rcases hreadyInternal with ⟨_row, _hrow, _hkind, hready⟩
      exact hready.1 (by rw [hdone]; exact Finset.mem_univ node)
  | succ fuel ih =>
      by_cases hinternal : (readyInternalNodes G state.1).Nonempty
      · rw [settleInternal_succ_of_internal hwf fuel state hinternal,
          FinDist.support_bind] at hnext
        simp only [Set.mem_iUnion] at hnext
        rcases hnext with ⟨middle, hmiddle, hrest⟩
        have hgrow := stepReadyInternal_done_ssubset
          hwf state hinternal hmiddle
        have hcard_grow := Finset.card_lt_card hgrow
        exact ih middle (by omega) hrest
      · have hempty : readyInternalNodes G state.1 = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hinternal
        rw [settleInternal_of_no_internal hwf (fuel + 1) state hempty,
          FinDist.mem_support_pure] at hnext
        simpa [hnext] using hempty

omit [Fintype Player] in
/-- `nodeCount` fuel always suffices for the automatic closure. -/
theorem settleInternal_nodeCount_support_no_internal
    {G : Graph Player L} (hwf : G.WF)
    (state : ReachableConfig G) {next : ReachableConfig G}
    (hnext : next ∈ (settleInternal hwf G.nodeCount state).support) :
    readyInternalNodes G next.1 = ∅ := by
  exact settleInternal_support_no_internal_of_card_add
    hwf G.nodeCount state (by omega) hnext

omit [Fintype Player] in
/-- Automatic settlement never forgets a completed graph node. -/
theorem settleInternal_done_subset
    {G : Graph Player L} (hwf : G.WF) (fuel : Nat)
    (state : ReachableConfig G) {next : ReachableConfig G}
    (hnext : next ∈ (settleInternal hwf fuel state).support) :
    state.1.done ⊆ next.1.done := by
  induction fuel generalizing state next with
  | zero =>
      rw [settleInternal_zero, FinDist.mem_support_pure] at hnext
      subst next
      exact Finset.Subset.rfl
  | succ fuel ih =>
      by_cases hinternal : (readyInternalNodes G state.1).Nonempty
      · rw [settleInternal_succ_of_internal hwf fuel state hinternal,
          FinDist.support_bind] at hnext
        simp only [Set.mem_iUnion] at hnext
        rcases hnext with ⟨middle, hmiddle, hrest⟩
        exact Finset.Subset.trans
          (stepReadyInternal_done_ssubset hwf state hinternal hmiddle).1
          (ih middle hrest)
      · have hempty : readyInternalNodes G state.1 = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hinternal
        rw [settleInternal_of_no_internal hwf (fuel + 1) state hempty,
          FinDist.mem_support_pure] at hnext
        subst next
        exact Finset.Subset.rfl

omit [Fintype Player] in
/-- If settlement starts with ready automatic work, every result after
`nodeCount` fuel has completed at least one fresh node. -/
theorem settleInternal_nodeCount_done_ssubset_of_internal
    {G : Graph Player L} (hwf : G.WF) (state : ReachableConfig G)
    (hinternal : (readyInternalNodes G state.1).Nonempty)
    {next : ReachableConfig G}
    (hnext : next ∈ (settleInternal hwf G.nodeCount state).support) :
    state.1.done ⊂ next.1.done := by
  rcases hinternal with ⟨node, hnode⟩
  have hnodeLt : node.val < G.nodeCount := node.isLt
  have hpositive : 0 < G.nodeCount := by omega
  obtain ⟨fuel, hcount⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hpositive)
  rw [hcount, settleInternal_succ_of_internal hwf fuel state
    ⟨node, hnode⟩, FinDist.support_bind] at hnext
  simp only [Set.mem_iUnion] at hnext
  rcases hnext with ⟨middle, hmiddle, hrest⟩
  exact Finset.ssubset_of_ssubset_of_subset
    (stepReadyInternal_done_ssubset hwf state ⟨node, hnode⟩ hmiddle)
    (settleInternal_done_subset hwf fuel middle hrest)

/-- **The serialized runtime for a compiled program.**

The same graph as `EventGraph.toExecutionProtocol`, run one submission at a time
in an order the scheduler picks and the state records.  This is the
counterfactual the negative scheduling results are about; the compiled protocol
is the atomic one and has no scheduler coordinate at all.

The accepted orders are precisely the duplicate-free enumerations of the
players active at the public view.  Thus an inactive or terminal checkpoint has
only the empty order, while a concurrent strategic frontier exposes exactly its
genuine serialization choices. -/
def serializedSystem (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G) :
    ScheduledSystem Player where
  Base := ReachableConfig G
  Action who := FrontierAction G who
  init := ⟨Config.initial G, Reachable.initial⟩
  active state who := ActiveAt G state.1 who
  available state who := { action | FrontierAction.Available G state.1 who action }
  terminal state := Terminal G state.1
  applyOne state who action :=
    FinDist.pure (applySerializedAction state action)
  settle state := settleInternal hwf G.nodeCount state
  View := PublicObservation G
  view state := publicObserve G state.1
  SchedulerView := PublicObservation G
  schedulerView state := publicObserve G state.1
  Obs who := PublicObservation G × Observation G who
  obs state who := (publicObserve G state.1, observe G state.1 who)
  menuAt who seen := by
    classical
    if _hrealizable : ∃ state : ReachableConfig G,
        publicObserve G state.1 = seen.1 ∧
          observe G state.1 who = seen.2 then
      exact
        { choice | ∃ state : ReachableConfig G,
            publicObserve G state.1 = seen.1 ∧
              observe G state.1 who = seen.2 ∧
              MenuAllows G state.1 who choice }
    else
      exact {none}
  menuAt_some state who action := by
    rw [dif_pos ⟨state, rfl, rfl⟩]
    constructor
    · rintro ⟨witness, hpublic, hown, hallows⟩
      exact
        (menuAllows_iff_of_obs_eq hwf hpublic hown (some action)).mp
          hallows
    · rintro ⟨hactive, havailable⟩
      exact ⟨state, rfl, rfl, hactive, havailable⟩
  menuAt_none state who := by
    rw [dif_pos ⟨state, rfl, rfl⟩]
    constructor
    · rintro ⟨witness, hpublic, hown, hallows⟩
      exact
        (menuAllows_iff_of_obs_eq hwf hpublic hown none).mp hallows
    · intro hinactive
      exact ⟨state, rfl, rfl, hinactive⟩
  schedules seen :=
    { order | order.Nodup ∧
        ∀ who : Player, who ∈ order ↔ ActiveAtView G seen who }
  schedules_nonempty seen := by
    classical
    let active := (Finset.univ : Finset Player).filter
      (ActiveAtView G seen)
    exact ⟨active.toList, active.nodup_toList, fun who => by
      simp [active]⟩
  progress state hterminal := (toExecutionProtocol G hwf hguards).progress state hterminal

/-- The serializer gives its scheduler exactly the current public graph
observation.  In particular, scheduling may depend on every publicly visible
value; it is not restricted to the active-player set. -/
@[simp] theorem serializedSystem_schedulerView
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (state : ReachableConfig G) :
    (serializedSystem G hwf hguards).schedulerView state =
      publicObserve G state.1 :=
  rfl

/-- Every original player can recover the scheduler's complete pre-round view
from its own observation.  Thus the scheduler has no private state signal to
leak through its order, although its policy may use all public graph data. -/
theorem serializedSystem_schedulerHasNoExtraInformation
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G) :
    (serializedSystem G hwf hguards).SchedulerHasNoExtraInformation := by
  refine ⟨fun _who seen => seen.1, ?_⟩
  intro state who
  rfl

/-- The no-extra-information result holds for complete perfect-recall
histories, not merely for the current state.  From any original player's
revealing information one recovers the scheduler's current public view, its
prior public views and orders, and its remembered scheduling choices. -/
theorem serializedSystem_schedulerInfo_eq_fromPlayer
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (who : Player)
    {state : (serializedSystem G hwf hguards).toExecutionProtocol.State}
    (trace : ExecutionProtocol.Trace
      (serializedSystem G hwf hguards).toExecutionProtocol state) :
    (serializedSystem G hwf hguards).schedulerInfoFromPlayer
        (fun seen : PublicObservation G × Observation G who => seen.1)
        ((serializedSystem G hwf hguards).revealingSignals.infoOf
          (.player who) trace) =
      (serializedSystem G hwf hguards).revealingSignals.infoOf
        (.scheduler : Participant Player) trace :=
  (serializedSystem G hwf hguards).revealing_schedulerInfo_eq_fromPlayer
    (fun seen : PublicObservation G × Observation G who => seen.1)
    (fun _state => rfl) trace

/-- The serialized and canonical protocols expose exactly the same menu at an
original player's current graph observation. Runtime order history may enrich
information, but it neither creates nor removes an action. -/
theorem serializedSystem_playerMenu_eq_localMenu
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (who : Player) (seen : LocalSnapshot G who)
    (own : List (LocalSnapshot G who × FrontierAction G who)) :
    (serializedSystem G hwf hguards).menuAt who seen =
      localMenu G hwf hguards who { current := seen, own := own } := by
  classical
  change
    (if _hrealizable : ∃ state : ReachableConfig G,
        publicObserve G state.1 = seen.1 ∧ observe G state.1 who = seen.2 then
      { choice | ∃ state : ReachableConfig G,
          publicObserve G state.1 = seen.1 ∧
            observe G state.1 who = seen.2 ∧
            MenuAllows G state.1 who choice }
    else {none}) =
    localMenu G hwf hguards who { current := seen, own := own }
  ext choice
  unfold localMenu
  by_cases hrealizable : ∃ state : ReachableConfig G,
      publicObserve G state.1 = seen.1 ∧
        observe G state.1 who = seen.2
  · rw [dif_pos hrealizable, dif_pos hrealizable]
    constructor
    · rintro ⟨state, hpublic, hprivate, hlegal⟩
      refine ⟨state, hpublic, hprivate, ?_⟩
      cases choice <;> exact hlegal
    · rintro ⟨state, hpublic, hprivate, hlegal⟩
      refine ⟨state, hpublic, hprivate, ?_⟩
      cases choice <;> exact hlegal
  · rw [dif_neg hrealizable, dif_neg hrealizable]

omit [Fintype Player] in
/-- The deterministic serialized fold executes exactly the concatenated player
writes.  The `processed` prefix records the intermediate-state invariant. -/
theorem applySerializedOrder_val_aux
    {G : Graph Player L} (hwf : G.WF)
    (joint : ∀ who, Option (FrontierAction G who))
    {origin : Config G} (horigin : Reachable G origin)
    (havailable : ∀ who action, joint who = some action →
      FrontierAction.Available G origin who action)
    {processed order : List Player}
    (horder : (processed ++ order).Nodup)
    (current : ReachableConfig G)
    (hcurrent : current.1 =
      origin.completeNodes (roundWrites joint processed)) :
    (applySerializedOrder joint order current).1 =
      origin.completeNodes (roundWrites joint (processed ++ order)) := by
  induction order generalizing processed current with
  | nil => simpa [applySerializedOrder] using hcurrent
  | cons who rest ih =>
      have hsplit : ((processed ++ [who]) ++ rest).Nodup := by
        simpa [List.append_assoc] using horder
      have hprefix : (processed ++ [who]).Nodup :=
        List.Nodup.of_append_left hsplit
      cases haction : joint who with
      | none =>
          have hcurrent' : current.1 =
              origin.completeNodes
                (roundWrites joint (processed ++ [who])) := by
            rw [roundWrites_append]
            have hempty : roundWrites joint [who] = [] := by
              simp [EventGraph.roundWrites, EventGraph.playerWrites, haction]
            rw [hempty]
            simpa using hcurrent
          simpa [applySerializedOrder, haction, List.append_assoc] using
            ih hsplit current hcurrent'
      | some action =>
          have hnextReach : Reachable G
              (origin.completeNodes
                (roundWrites joint (processed ++ [who]))) := by
            apply reachable_completeNodes_of_commitAvailable hwf horigin
            · exact roundWrites_nodes_nodup havailable hprefix
            · intro step hstep
              exact commitAvailable_of_mem_roundWrites havailable hstep
          let next : ReachableConfig G :=
            ⟨origin.completeNodes
              (roundWrites joint (processed ++ [who])), hnextReach⟩
          have hraw : current.1.completeNodes (actionWrites action) =
              next.1 := by
            dsimp [next]
            rw [hcurrent, ← Config.completeNodes_append]
            congr 1
            simp [EventGraph.roundWrites, EventGraph.playerWrites, haction]
          have htargetReach : Reachable G
              (current.1.completeNodes (actionWrites action)) := by
            rw [hraw]
            exact next.2
          have happly : applySerializedAction current action = next := by
            rw [applySerializedAction_eq_of_reachable
              current action htargetReach]
            exact Subtype.ext hraw
          simp only [applySerializedOrder, haction]
          rw [happly]
          simpa [List.append_assoc] using ih hsplit next rfl

omit [Fintype Player] in
/-- A legal duplicate-free order reaches exactly its explicit write list. -/
theorem applySerializedOrder_val
    {G : Graph Player L} (hwf : G.WF)
    (joint : ∀ who, Option (FrontierAction G who))
    (state : ReachableConfig G)
    (havailable : ∀ who action, joint who = some action →
      FrontierAction.Available G state.1 who action)
    {order : List Player} (horder : order.Nodup) :
    (applySerializedOrder joint order state).1 =
      state.1.completeNodes (roundWrites joint order) := by
  simpa using applySerializedOrder_val_aux hwf joint state.2 havailable
    (processed := []) horder state rfl

/-- `ScheduledSystem.applyOrder` is the distributional wrapper around the
deterministic serialized fold. -/
theorem serializedSystem_applyOrder_eq_pure
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (joint : ∀ who, Option (FrontierAction G who))
    (order : List Player) (state : ReachableConfig G) :
    (serializedSystem G hwf hguards).applyOrder
        ((serializedSystem G hwf hguards).withSchedule [] joint)
        order state =
      FinDist.pure (applySerializedOrder joint order state) := by
  induction order generalizing state with
  | nil => rfl
  | cons who rest ih =>
      simp only [ScheduledSystem.applyOrder, ScheduledSystem.withSchedule]
      cases haction : joint who with
      | none => simpa [haction, applySerializedOrder] using ih state
      | some action =>
          change
            (FinDist.pure (applySerializedAction state action)).bind
                ((serializedSystem G hwf hguards).applyOrder
                  ((serializedSystem G hwf hguards).withSchedule [] joint)
                  rest) = _
          have htail := ih (applySerializedAction state action)
          have hreduce :
              applySerializedOrder joint (who :: rest) state =
                applySerializedOrder joint rest
                  (applySerializedAction state action) := by
            simp [applySerializedOrder, haction]
          exact
            (FinDist.pure_bind (applySerializedAction state action)
              ((serializedSystem G hwf hguards).applyOrder
                ((serializedSystem G hwf hguards).withSchedule [] joint)
                rest)).trans
              (htail.trans (congrArg FinDist.pure hreduce.symm))

/-- Starting from a round checkpoint, a legal duplicate-free player order
produces exactly its explicit write list. -/
theorem serializedSystem_applyOrder_map_val
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (joint : ∀ who, Option (FrontierAction G who))
    (state : ReachableConfig G)
    (havailable : ∀ who action, joint who = some action →
      FrontierAction.Available G state.1 who action)
    {order : List Player} (horder : order.Nodup) :
    ((serializedSystem G hwf hguards).applyOrder
        ((serializedSystem G hwf hguards).withSchedule [] joint)
        order state).map Subtype.val =
      FinDist.pure
        (state.1.completeNodes (roundWrites joint order)) := by
  rw [serializedSystem_applyOrder_eq_pure, FinDist.map_pure]
  exact congrArg FinDist.pure
    (applySerializedOrder_val hwf joint state havailable horder)

/-- The compiled scheduled system's automatic phase always lands at a
strategic checkpoint (or a terminal state). -/
theorem serializedSystem_settle_support_no_internal
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (state : ReachableConfig G) {next : ReachableConfig G}
    (hnext : next ∈
      ((serializedSystem G hwf hguards).settle state).support) :
    readyInternalNodes G next.1 = ∅ := by
  exact settleInternal_nodeCount_support_no_internal hwf state hnext

/-- Every realized round of the serialized runtime finishes its automatic
closure.  In particular, internal-only states cannot generate an infinite log
of all-abstain rounds. -/
theorem serializedSystem_step_support_no_internal
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (state : (serializedSystem G hwf hguards).State)
    (legal : { joint //
      (serializedSystem G hwf hguards).toExecutionProtocol.Legal state joint })
    {next : (serializedSystem G hwf hguards).State}
    (hnext : next ∈
      ((serializedSystem G hwf hguards).toExecutionProtocol.step
        state legal).support) :
    readyInternalNodes G next.base.1 = ∅ := by
  exact (serializedSystem G hwf hguards).base_property_of_mem_support_step
    (fun next => readyInternalNodes G next.1 = ∅)
    (fun postOrder _next hsettled =>
      serializedSystem_settle_support_no_internal
        G hwf hguards postOrder hsettled)
    hnext

/-- Every realized serialized round completes at least one fresh graph node.
This includes an initial internal-only round as well as ordinary strategic
frontiers. -/
theorem serializedSystem_step_done_ssubset
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (state : (serializedSystem G hwf hguards).State)
    (legal : { joint //
      (serializedSystem G hwf hguards).toExecutionProtocol.Legal state joint })
    {next : (serializedSystem G hwf hguards).State}
    (hnext : next ∈
      ((serializedSystem G hwf hguards).toExecutionProtocol.step
        state legal).support) :
    state.base.1.done ⊂ next.base.1.done := by
  classical
  let sys := serializedSystem G hwf hguards
  let players : ∀ who, Option (FrontierAction G who) :=
    fun who => legal.1 (.player who)
  let order : List Player := sys.scheduledOrder legal.1
  have hplayersLegal : IsLegalJoint
      (fun who => ActiveAt G state.base.1 who)
      (fun who =>
        { action | FrontierAction.Available G state.base.1 who action })
      players := by
    intro who
    have hlocal := legal.2.2 (.player who)
    cases hchoice : legal.1 (.player who) with
    | none =>
        rw [hchoice] at hlocal
        have hplayerChoice : players who = none := hchoice
        rw [hplayerChoice]
        exact hlocal
    | some action =>
        rw [hchoice] at hlocal
        have hplayerChoice : players who = some action := hchoice
        rw [hplayerChoice]
        exact ⟨hlocal.1, hlocal.2⟩
  have horderMem : order ∈ sys.schedules (sys.schedulerView state.base) :=
    sys.scheduledOrder_mem_schedules legal
  have horderSpec : order.Nodup ∧
      ∀ who : Player, who ∈ order ↔ ActiveAt G state.base.1 who := by
    change order.Nodup ∧ ∀ who : Player,
      who ∈ order ↔
        ActiveAtView G (publicObserve G state.base.1) who at horderMem
    exact ⟨horderMem.1, fun who =>
      (horderMem.2 who).trans (activeAtView_iff state.base.1 who)⟩
  have havailable : ∀ who action, players who = some action →
      FrontierAction.Available G state.base.1 who action := by
    intro who action haction
    have hlocal := hplayersLegal who
    rw [haction] at hlocal
    exact hlocal.2
  have happly :
      (serializedSystem G hwf hguards).applyOrder legal.1 order state.base =
        FinDist.pure (applySerializedOrder players order state.base) := by
    have hleft :=
      (serializedSystem G hwf hguards).applyOrder_congr
        (left := legal.1)
        (right := (serializedSystem G hwf hguards).withSchedule [] players)
        (fun who => rfl) order state.base
    have hright := serializedSystem_applyOrder_eq_pure
      G hwf hguards players order state.base
    exact hleft.trans hright
  simp only [ScheduledSystem.toExecutionProtocol, FinDist.support_map,
    Set.mem_image] at hnext
  rcases hnext with ⟨nextBase, hresolved, rfl⟩
  unfold ScheduledSystem.resolveOrder at hresolved
  rw [FinDist.support_bind] at hresolved
  simp only [Set.mem_iUnion] at hresolved
  rcases hresolved with ⟨postOrder, hpostOrder, hsettled⟩
  rw [happly] at hpostOrder
  have hpostEq : postOrder =
      applySerializedOrder players order state.base :=
    FinDist.mem_support_pure.mp hpostOrder
  subst postOrder
  by_cases hinternal :
      (readyInternalNodes G state.base.1).Nonempty
  · have horderEmpty : order = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro who hwho
      have hactive : ActiveAt G state.base.1 who :=
        (horderSpec.2 who).mp hwho
      exact hinternal.ne_empty hactive.2.1
    rw [horderEmpty] at hsettled
    exact settleInternal_nodeCount_done_ssubset_of_internal
      hwf state.base hinternal hsettled
  · have hnoInternal : readyInternalNodes G state.base.1 = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hinternal
    have hactivePlayers : (activePlayers G state.base.1).Nonempty := by
      by_contra hnone
      have hempty : activePlayers G state.base.1 = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnone
      rcases exists_internal_available_of_no_active
          hwf hguards legal.2.1 hempty with ⟨event, havailableInternal⟩
      have hready := havailableInternal.readyInternalNode
      have hmem : event.node ∈ readyInternalNodes G state.base.1 := by
        unfold readyInternalNodes
        simp [hready]
      rw [hnoInternal] at hmem
      exact (Finset.notMem_empty event.node) hmem
    rcases hactivePlayers with ⟨who, hwhoActive⟩
    have hactive : ActiveAt G state.base.1 who :=
      ⟨legal.2.1, hnoInternal, hwhoActive⟩
    have hwhoOrder : who ∈ order := (horderSpec.2 who).mpr hactive
    have hlocal := hplayersLegal who
    cases haction : players who with
    | none =>
        rw [haction] at hlocal
        exact False.elim (hlocal hactive)
    | some action =>
        rw [haction] at hlocal
        rcases (Finset.mem_filter.mp hwhoActive).2 with ⟨node, hnodeMem⟩
        have hready : ReadyCommitNode G state.base.1 who node :=
          (Finset.mem_filter.mp hnodeMem).2
        rcases
            (hlocal.2.value?_isSome_iff_readyCommitNode.mpr hready) with
          ⟨value, hvalue⟩
        let written := (node, G.nodeTypedValue node value)
        have hactionWrite : written ∈ actionWrites action :=
          (mem_actionWrites_iff action written).mpr ⟨value, hvalue, rfl⟩
        have hroundWrite : written ∈ roundWrites players order :=
          (mem_roundWrites_iff players order written).mpr
            ⟨who, hwhoOrder,
              (mem_playerWrites_iff players who written).mpr
                ⟨action, haction, hactionWrite⟩⟩
        have hpostGrow : state.base.1.done ⊂
            (applySerializedOrder players order state.base).1.done := by
          rw [applySerializedOrder_val hwf players state.base havailable
            horderSpec.1, Config.completeNodes_done]
          refine Finset.ssubset_iff_subset_ne.mpr
            ⟨Finset.subset_union_left, ?_⟩
          intro heq
          have hnodeWritten : node ∈
              ((roundWrites players order).map Prod.fst).toFinset := by
            rw [List.mem_toFinset]
            exact List.mem_map_of_mem (f := Prod.fst) hroundWrite
          have hnodeDone : node ∈ state.base.1.done := by
            rw [heq]
            exact Finset.mem_union_right _ hnodeWritten
          exact hready.ready.1 hnodeDone
        exact Finset.ssubset_of_ssubset_of_subset hpostGrow
          (settleInternal_done_subset hwf G.nodeCount
            (applySerializedOrder players order state.base) hsettled)

/-- A serialized trace cannot be longer than the number of graph nodes
completed at its endpoint. -/
theorem serializedSystem_trace_length_le_done_card
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G) :
    ∀ (state : (serializedSystem G hwf hguards).toExecutionProtocol.State)
      (trace : (serializedSystem G hwf hguards).toExecutionProtocol.Trace state),
      trace.length ≤ state.base.1.done.card := by
  intro state trace
  induction trace with
  | start => rfl
  | @extend source target prior joint isLegal realized ih =>
      have hgrow := serializedSystem_step_done_ssubset
        G hwf hguards source ⟨joint, isLegal⟩ realized
      have hcard := Finset.card_lt_card hgrow
      simp only [ExecutionProtocol.Trace.length]
      omega

/-- `nodeCount` is a uniform horizon for the actual serialized execution
protocol, independently of every scheduler choice. -/
theorem serializedSystem_boundedHorizon
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G) :
    (serializedSystem G hwf hguards).toExecutionProtocol.BoundedHorizon
      G.nodeCount := by
  intro state trace hlength
  have hdoneCard : G.nodeCount ≤ state.base.1.done.card :=
    le_trans hlength
      (serializedSystem_trace_length_le_done_card
        G hwf hguards state trace)
  change Terminal G state.base.1
  intro node
  by_contra hnotDone
  have hstrict : state.base.1.done ⊂ insert node state.base.1.done :=
    Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_insert node state.base.1.done, by
        intro heq
        exact hnotDone (by rw [heq]; exact Finset.mem_insert_self node _)⟩
  have hstrictUniv : state.base.1.done ⊂
      (Finset.univ : Finset (Fin G.nodeCount)) :=
    Finset.ssubset_of_ssubset_of_subset hstrict (Finset.subset_univ _)
  have hcardLt := Finset.card_lt_card hstrictUniv
  simp only [Finset.card_univ, Fintype.card_fin] at hcardLt
  omega

omit [Fintype Player] in
theorem readyAtView_iff {G : Graph Player L} (state : Config G)
    (node : Fin G.nodeCount) :
    ReadyAtView G (publicObserve G state) node ↔ Ready G state node := by
  rfl

omit [Fintype Player] in
theorem readyCommitAtView_iff {G : Graph Player L} (state : Config G)
    (who : Player) (node : Fin G.nodeCount) :
    ReadyCommitAtView G (publicObserve G state) who node ↔
      ReadyCommitNode G state who node := by
  rw [ReadyCommitAtView, readyAtView_iff]
  cases hsem : (G.nodeRow node).sem with
  | sample dist => simp [ReadyCommitNode, hsem]
  | reveal source => simp [ReadyCommitNode, hsem]
  | commit owner guard =>
      by_cases howner : owner = who
      · subst owner
        simp [ReadyCommitNode, hsem]
      · simp [ReadyCommitNode, hsem, howner]

omit [Fintype Player] in
theorem readyInternalAtView_iff {G : Graph Player L} (state : Config G)
    (node : Fin G.nodeCount) :
    ReadyInternalAtView G (publicObserve G state) node ↔
      ReadyInternalNode G state node := by
  rw [ReadyInternalAtView, readyAtView_iff]
  cases hsem : (G.nodeRow node).sem with
  | sample dist => simp [ReadyInternalNode, hsem]
  | reveal source => simp [ReadyInternalNode, hsem]
  | commit owner guard => simp [ReadyInternalNode, hsem]

/-- The executable public test agrees with semantic activity at every realized
view. -/
theorem activeAtPublicView_iff {G : Graph Player L} (state : Config G)
    (who : Player) :
    ActiveAtPublicView G (publicObserve G state) who ↔
      ActiveAt G state who := by
  unfold ActiveAtPublicView ActiveAt
  constructor
  · rintro ⟨hnonterminal, hnoInternal, node, hcommit⟩
    refine ⟨?_, ?_, ?_⟩
    · intro hterminal
      obtain ⟨unfinished, hunfinished⟩ := hnonterminal
      exact hunfinished (hterminal unfinished)
    · apply Finset.eq_empty_iff_forall_notMem.mpr
      intro query hquery
      have hinternal : ReadyInternalNode G state query :=
        (Finset.mem_filter.mp hquery).2
      exact hnoInternal query
        ((readyInternalAtView_iff state query).mpr hinternal)
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ who, ?_⟩
      refine ⟨node, Finset.mem_filter.mpr ⟨Finset.mem_univ node, ?_⟩⟩
      exact (readyCommitAtView_iff state who node).mp hcommit
  · rintro ⟨hnonterminal, hnoInternal, hactive⟩
    refine ⟨?_, ?_, ?_⟩
    · by_contra hall
      apply hnonterminal
      intro node
      by_contra hdone
      exact hall ⟨node, hdone⟩
    · intro node hinternal
      have hmem : node ∈ readyInternalNodes G state := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ node,
          (readyInternalAtView_iff state node).mp hinternal⟩
      rw [hnoInternal] at hmem
      exact (Finset.notMem_empty node) hmem
    · have hnonempty : (readyCommitNodes G state who).Nonempty :=
        (Finset.mem_filter.mp hactive).2
      obtain ⟨node, hnode⟩ := hnonempty
      exact ⟨node, (readyCommitAtView_iff state who node).mpr
        (Finset.mem_filter.mp hnode).2⟩

theorem mem_fixedOrder_iff [LinearOrder Player]
    (G : Graph Player L) (state : Config G)
    (who : Player) :
    who ∈ fixedOrder G (publicObserve G state) ↔ ActiveAt G state who := by
  simp only [fixedOrder, Finset.mem_sort, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact activeAtPublicView_iff state who

theorem fixedOrder_nodup [LinearOrder Player] (G : Graph Player L)
    (seen : PublicObservation G) : (fixedOrder G seen).Nodup := by
  unfold fixedOrder
  exact Finset.sort_nodup _ _

/-- The selected fixed order is one of the permissive serializer's valid
enumerations. -/
theorem fixedOrder_mem_serializedSystem_schedules
    [LinearOrder Player]
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (state : Config G) :
    fixedOrder G (publicObserve G state) ∈
      (serializedSystem G hwf hguards).schedules (publicObserve G state) := by
  exact ⟨fixedOrder_nodup G _, fun who =>
    (mem_fixedOrder_iff G state who).trans
      (activeAtView_iff state who).symm⟩

/-- A serialized implementation with a fixed public ordering policy. It has
the same action and settlement semantics as `serializedSystem`, but its
scheduling coordinate carries no operational choice. -/
noncomputable def fixedSerializedSystem [LinearOrder Player]
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G) :
    ScheduledSystem Player :=
  { serializedSystem G hwf hguards with
    schedules := fun seen => {fixedOrder G seen}
    schedules_nonempty := fun seen =>
      ⟨fixedOrder G seen, Set.mem_singleton _⟩ }

/-- The fixed serializer accepts exactly one order at each public view. -/
theorem fixedSerializedSystem_enforcesOrder
    [LinearOrder Player]
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G) :
    (fixedSerializedSystem G hwf hguards).EnforcesOrder := by
  intro seen left hleft right hright
  exact (Set.mem_singleton_iff.mp hleft).trans
    (Set.mem_singleton_iff.mp hright).symm

/-- Fixed scheduling changes the scheduler menu, not automatic execution:
its realized rounds reach the same kind of stable checkpoint. -/
theorem fixedSerializedSystem_step_support_no_internal
    [LinearOrder Player]
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (state : (fixedSerializedSystem G hwf hguards).State)
    (legal : { joint //
      (fixedSerializedSystem G hwf hguards).toExecutionProtocol.Legal
        state joint })
    {next : (fixedSerializedSystem G hwf hguards).State}
    (hnext : next ∈
      ((fixedSerializedSystem G hwf hguards).toExecutionProtocol.step
        state legal).support) :
    readyInternalNodes G next.base.1 = ∅ := by
  exact (fixedSerializedSystem G hwf hguards).base_property_of_mem_support_step
    (fun next => readyInternalNodes G next.1 = ∅)
    (fun postOrder _next hsettled =>
      settleInternal_nodeCount_support_no_internal hwf postOrder hsettled)
    hnext

/-- Changing only the scheduler coordinate cannot change a fixed-order
serialization step. -/
theorem fixedSerializedSystem_step_determined_by_players
    [LinearOrder Player]
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    {state : (fixedSerializedSystem G hwf hguards).State}
    {left right : { joint //
      (fixedSerializedSystem G hwf hguards).toExecutionProtocol.Legal
        state joint }}
    (hplayers : ∀ who,
      left.1 (.player who) = right.1 (.player who)) :
    (fixedSerializedSystem G hwf hguards).toExecutionProtocol.step
        state left =
      (fixedSerializedSystem G hwf hguards).toExecutionProtocol.step
        state right := by
  exact (fixedSerializedSystem G hwf hguards).step_eq_of_enforcesOrder
    (fixedSerializedSystem_enforcesOrder G hwf hguards) hplayers

/-- At a realized public view, accepted schedules are exactly the duplicate-free
enumerations of the players who must submit there. -/
theorem mem_serializedSystem_schedules_iff
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (state : Config G) (order : List Player) :
    order ∈
        (serializedSystem G hwf hguards).schedules (publicObserve G state) ↔
      order.Nodup ∧ ∀ who : Player, who ∈ order ↔ ActiveAt G state who := by
  change order.Nodup ∧
      (∀ who : Player, who ∈ order ↔
        ActiveAtView G (publicObserve G state) who) ↔ _
  constructor
  · rintro ⟨hnodup, hmembers⟩
    exact ⟨hnodup, fun who =>
      (hmembers who).trans (activeAtView_iff state who)⟩
  · rintro ⟨hnodup, hmembers⟩
    exact ⟨hnodup, fun who =>
      (hmembers who).trans (activeAtView_iff state who).symm⟩

/-- **A legal serialized player order implements the atomic frontier exactly.**

The atomic protocol and the serializer use the same explicit node/value writes.
The former chooses a canonical enumeration of all players (inactive coordinates
contribute no writes); an accepted runtime order enumerates exactly the active
players. Legality makes those write lists permutations, and graph confluence
makes their resulting reachable configurations equal. -/
theorem applySerializedOrder_eq_applyFrontier
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (state : ReachableConfig G)
    (joint : ∀ who, Option (FrontierAction G who))
    (hlegal : (toExecutionProtocol G hwf hguards).Legal state joint)
    {order : List Player}
    (horder : order ∈
      (serializedSystem G hwf hguards).schedules
        (publicObserve G state.1)) :
    applySerializedOrder joint order state =
      EventGraph.applyFrontier G hwf state joint := by
  classical
  have havailable : ∀ who action, joint who = some action →
      FrontierAction.Available G state.1 who action := by
    intro who action haction
    have hlocal := hlegal.2 who
    rw [haction] at hlocal
    exact hlocal.2
  have horder' := (mem_serializedSystem_schedules_iff
    G hwf hguards state.1 order).mp horder
  have horderedNodes :
      ((roundWrites joint order).map Prod.fst).Nodup :=
    roundWrites_nodes_nodup havailable horder'.1
  have hcanonicalNodes :
      ((roundWrites joint
        (Finset.univ.toList : List Player)).map Prod.fst).Nodup :=
    roundWrites_nodes_nodup havailable Finset.univ.nodup_toList
  have hwrites : (roundWrites joint order).Perm
      (roundWrites joint (Finset.univ.toList : List Player)) := by
    apply (List.perm_ext_iff_of_nodup
      (horderedNodes.of_map Prod.fst)
      (hcanonicalNodes.of_map Prod.fst)).mpr
    intro written
    constructor
    · intro hwritten
      obtain ⟨who, _hwho, hplayer⟩ :=
        (mem_roundWrites_iff joint order written).mp hwritten
      exact (mem_roundWrites_iff joint _ written).mpr
        ⟨who, by simp, hplayer⟩
    · intro hwritten
      obtain ⟨who, _hwho, hplayer⟩ :=
        (mem_roundWrites_iff joint _ written).mp hwritten
      obtain ⟨action, haction, _hactionWrite⟩ :=
        (mem_playerWrites_iff joint who written).mp hplayer
      have hlocal := hlegal.2 who
      rw [haction] at hlocal
      exact (mem_roundWrites_iff joint order written).mpr
        ⟨who, (horder'.2 who).mpr hlocal.1, hplayer⟩
  apply Subtype.ext
  calc
    (applySerializedOrder joint order state).1 =
        state.1.completeNodes (roundWrites joint order) :=
      applySerializedOrder_val hwf joint state havailable horder'.1
    _ = state.1.completeNodes
        (roundWrites joint (Finset.univ.toList : List Player)) :=
      Config.completeNodes_perm state.1 hwrites horderedNodes
    _ = (EventGraph.applyFrontier G hwf state joint).1 :=
      (EventGraph.applyFrontier_val_of_available
        G hwf state joint havailable).symm

/-- Before automatic closure, applying an accepted scheduler order has exactly
the atomic source-round successor law. -/
theorem serializedSystem_applyOrder_eq_atomicFrontier
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (state : ReachableConfig G)
    (joint : ∀ who, Option (FrontierAction G who))
    (hlegal : (toExecutionProtocol G hwf hguards).Legal state joint)
    {order : List Player}
    (horder : order ∈
      (serializedSystem G hwf hguards).schedules
        (publicObserve G state.1)) :
    (serializedSystem G hwf hguards).applyOrder
        ((serializedSystem G hwf hguards).withSchedule [] joint)
        order state =
      FinDist.pure (EventGraph.applyFrontier G hwf state joint) := by
  rw [serializedSystem_applyOrder_eq_pure]
  exact congrArg FinDist.pure
    (applySerializedOrder_eq_applyFrontier
      G hwf hguards state joint hlegal horder)

/-- A complete serialized strategic round is the atomic source successor
followed by precisely the serializer's automatic internal closure. Thus the
only remaining temporal difference is the deliberate batching of forced
internal events between player checkpoints. -/
theorem serializedSystem_resolveOrder_eq_settle_atomicFrontier
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (state : ReachableConfig G)
    (joint : ∀ who, Option (FrontierAction G who))
    (hlegal : (toExecutionProtocol G hwf hguards).Legal state joint)
    {order : List Player}
    (horder : order ∈
      (serializedSystem G hwf hguards).schedules
        (publicObserve G state.1)) :
    (serializedSystem G hwf hguards).resolveOrder
        ((serializedSystem G hwf hguards).withSchedule order joint)
        order state =
      (serializedSystem G hwf hguards).settle
        (EventGraph.applyFrontier G hwf state joint) := by
  let sys := serializedSystem G hwf hguards
  have hschedulerIrrelevant :
      sys.resolveOrder (sys.withSchedule order joint) order state =
        sys.resolveOrder (sys.withSchedule [] joint) order state :=
    sys.resolveOrder_congr
      (left := sys.withSchedule order joint)
      (right := sys.withSchedule [] joint)
      (fun _who => rfl) order state
  rw [hschedulerIrrelevant]
  unfold ScheduledSystem.resolveOrder
  rw [serializedSystem_applyOrder_eq_atomicFrontier
    G hwf hguards state joint hlegal horder]
  exact FinDist.pure_bind _ _

/-- **The serialized runtime is genuinely permissive.**

Two distinct enumerations of the players are both accepted, so its scheduler has
a real choice to make -- which is the whole difference from the compiled
protocol, where there is no scheduler coordinate to choose with.

Stated from a supplied pair rather than derived from `1 < card Player`, so a
caller exhibits the two orders its own program actually admits. -/
theorem serializedSystem_not_enforcesOrder
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    {seen : PublicObservation G} {left right : List Player}
    (hleft : left ∈ (serializedSystem G hwf hguards).schedules seen)
    (hright : right ∈ (serializedSystem G hwf hguards).schedules seen)
    (hne : left ≠ right) :
    ¬ (serializedSystem G hwf hguards).EnforcesOrder := by
  intro henforce
  exact hne (henforce seen hleft hright)

/-- **The permissive compiled serializer has order-independent effects.**

Every accepted order is a duplicate-free enumeration of the same active
players.  A legal joint submission therefore contributes the same
duplicate-free node/value writes in every accepted order; the event-graph
diamond law makes the completed configuration identical, and the common
automatic settlement phase preserves equality of the resulting laws.

The public schedule log is intentionally outside this statement: different
orders remain observable even though their underlying graph effects commute. -/
theorem serializedSystem_effectsCommute
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G) :
    (serializedSystem G hwf hguards).EffectsCommute := by
  intro joint state hlegal left right hleft hright
  let players : ∀ who, Option (FrontierAction G who) :=
    fun who => joint (.player who)
  have havailable : ∀ who action, players who = some action →
      FrontierAction.Available G state.1 who action := by
    intro who action haction
    have hlocal := hlegal who
    change joint (.player who) = some action at haction
    dsimp only at hlocal
    rw [haction] at hlocal
    exact hlocal.2
  have hleft' := (mem_serializedSystem_schedules_iff
    G hwf hguards state.1 left).mp hleft
  have hright' := (mem_serializedSystem_schedules_iff
    G hwf hguards state.1 right).mp hright
  have horderPerm : left.Perm right :=
    (List.perm_ext_iff_of_nodup hleft'.1 hright'.1).mpr
      (fun who => (hleft'.2 who).trans (hright'.2 who).symm)
  have hwritesNodup : ((roundWrites players left).map Prod.fst).Nodup :=
    roundWrites_nodes_nodup havailable hleft'.1
  have hconfig :
      state.1.completeNodes (roundWrites players left) =
        state.1.completeNodes (roundWrites players right) :=
    Config.completeNodes_perm state.1
      (roundWrites_perm players horderPerm) hwritesNodup
  let sys := serializedSystem G hwf hguards
  have htoPlayers (order : List Player) :
      sys.applyOrder joint order state =
        sys.applyOrder (sys.withSchedule [] players) order state := by
    apply sys.applyOrder_congr
    intro who
    rfl
  have hbase :
      (sys.applyOrder joint left state).map Subtype.val =
        (sys.applyOrder joint right state).map Subtype.val := by
    calc
      _ = (sys.applyOrder (sys.withSchedule [] players) left state).map
            Subtype.val := congrArg (FinDist.map Subtype.val) (htoPlayers left)
      _ = FinDist.pure
            (state.1.completeNodes (roundWrites players left)) :=
          serializedSystem_applyOrder_map_val
            G hwf hguards players state havailable hleft'.1
      _ = FinDist.pure
            (state.1.completeNodes (roundWrites players right)) :=
          congrArg FinDist.pure hconfig
      _ = (sys.applyOrder (sys.withSchedule [] players) right state).map
            Subtype.val :=
          (serializedSystem_applyOrder_map_val
            G hwf hguards players state havailable hright'.1).symm
      _ = (sys.applyOrder joint right state).map Subtype.val :=
          congrArg (FinDist.map Subtype.val) (htoPlayers right).symm
  have happly : sys.applyOrder joint left state =
      sys.applyOrder joint right state := by
    apply FinDist.map_injective (f := Subtype.val) Subtype.val_injective
    exact hbase
  unfold ScheduledSystem.resolveOrder
  rw [happly]

end EventGraph

end Vegas
