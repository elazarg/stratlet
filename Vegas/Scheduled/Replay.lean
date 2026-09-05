/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Scheduled.Basic

/-!
# Replaying a public-information scheduler without observing orders

Fix an arbitrary deterministic scheduler policy. A player whose observations
determine the scheduler's observations can reconstruct the published orders
from its order-free observation history by executing that policy locally.
The scheduler may react to public data and all its previous choices.

This reconstructs the full runtime information, including memory at earlier
decisions, and back-translates every deterministic order-aware player policy
to an order-blind policy. The order-blind model here retains every observation.
`Vegas.Scheduled.Information` proves that the compiled graph's compact source
information suffices to recover it on legal runtime histories.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Vegas.ScheduledSystem

open GameTheory.Protocol GameTheory.Math.Probability

variable {ι : Type} (sys : ScheduledSystem ι)

/-- The scheduler follows this policy at every prefix; original-player
submissions are unrestricted except for the trace's legality. -/
def SchedulerFollows (policy : sys.revealingInformation.Policy .scheduler) :
    {state : sys.toExecutionProtocol.State} → sys.toExecutionProtocol.Trace state → Prop
  | _, .start => True
  | _, .extend prior joint _ _ =>
      SchedulerFollows policy prior ∧
        joint .scheduler = (policy (sys.revealingSignals.infoOf .scheduler prior)).1

/-- Recover the orders preceding the current checkpoint from past player
observations alone. The input list is newest first, as in `BlindInfo.past`.
Recursion first reconstructs the older prefix, then runs the scheduler on
exactly the information it had at the next decision. -/
def replayOrderPast {i : ι}
    (policy : sys.revealingInformation.Policy .scheduler)
    (project : sys.Obs i → sys.SchedulerView) :
    List (sys.Obs i) → List (sys.Order × sys.Obs i)
  | [] => []
  | previous :: rest =>
      let past := replayOrderPast policy project rest
      let schedulerInfo := sys.schedulerInfoFromPlayer project
        { current := previous, past := past, own := [] }
      ((policy schedulerInfo).1.getD [], previous) :: past

/-- Reconstruct the player's full order-revealing information, including the
information remembered at its own earlier decisions, without taking any
realized order as input. -/
def replayPlayerInfo {i : ι}
    (policy : sys.revealingInformation.Policy .scheduler)
    (project : sys.Obs i → sys.SchedulerView)
    (info : sys.BlindInfo (.player i)) : sys.RevealingInfo (.player i) where
  current := info.current
  past := sys.replayOrderPast policy project info.past
  own := info.own.map fun remembered =>
    ((remembered.1.1, sys.replayOrderPast policy project remembered.1.2), remembered.2)

@[simp] theorem replayOrderPast_map_snd {i : ι}
    (policy : sys.revealingInformation.Policy .scheduler)
    (project : sys.Obs i → sys.SchedulerView) (past : List (sys.Obs i)) :
    (sys.replayOrderPast policy project past).map Prod.snd = past := by
  induction past with
  | nil => rfl
  | cons previous rest ih => simp only [replayOrderPast, List.map_cons, ih]

/-- Replay fills in only ordering data. It leaves all order-free information
unchanged, even at counterfactual information states. -/
@[simp] theorem forgetOrders_replayPlayerInfo {i : ι}
    (policy : sys.revealingInformation.Policy .scheduler)
    (project : sys.Obs i → sys.SchedulerView) (info : sys.BlindInfo (.player i)) :
    sys.forgetOrders (sys.replayPlayerInfo policy project info) = info := by
  cases info
  simp [forgetOrders, replayPlayerInfo, List.map_map, Function.comp_def]

theorem replayPlayerInfo_push {i : ι}
    (policy : sys.revealingInformation.Policy .scheduler)
    (project : sys.Obs i → sys.SchedulerView)
    (prior : sys.BlindInfo (.player i))
    (choice : Option (sys.Submission (.player i))) (current : sys.Obs i) :
    sys.replayPlayerInfo policy project (BlindInfo.push sys prior choice current) =
      RevealingInfo.push sys (sys.replayPlayerInfo policy project prior) choice current
        ((policy (sys.schedulerInfoFromPlayer project
          (sys.replayPlayerInfo policy project prior))).1.getD []) := by
  cases prior
  cases choice <;> rfl

/-- **A fixed public-information scheduler gives no information beyond the
order-free observation history.** This theorem executes the policy along the
history; it does not treat a policy function as an unexecuted public signal.
The statement covers every legal player deviation and every realized chance
outcome compatible with the fixed scheduler. -/
theorem revealing_info_eq_replayPlayerInfo {i : ι}
    (policy : sys.revealingInformation.Policy .scheduler)
    (project : sys.Obs i → sys.SchedulerView)
    (hproject : ∀ state, project (sys.obs state i) = sys.schedulerView state)
    {state : sys.toExecutionProtocol.State} (trace : sys.toExecutionProtocol.Trace state)
    (hfollows : sys.SchedulerFollows policy trace) :
    sys.revealingSignals.infoOf (.player i) trace =
      sys.replayPlayerInfo policy project (sys.blindSignals.infoOf (.player i) trace) := by
  induction trace with
  | start => rfl
  | @extend source target prior joint legal realized ih =>
      obtain ⟨hprior, hchoice⟩ := hfollows
      have hinfo := ih hprior
      have hscheduler := sys.revealing_schedulerInfo_eq_fromPlayer project hproject prior
      have hlog := sys.log_of_mem_support_step realized
      have horder : target.log.headD [] =
          (policy (sys.schedulerInfoFromPlayer project
            (sys.replayPlayerInfo policy project
              (sys.blindSignals.infoOf (.player i) prior)))).1.getD [] := by
        rw [hlog]
        change (joint .scheduler).getD [] = _
        rw [hchoice, ← hscheduler, hinfo]
      rw [InfoSignals.infoOf_extend, InfoSignals.infoOf_extend]
      change RevealingInfo.push sys _ (joint (.player i)) _ (target.log.headD []) =
        sys.replayPlayerInfo policy project (BlindInfo.push sys _ (joint (.player i)) _)
      rw [sys.replayPlayerInfo_push, hinfo, horder]

/-- Under the same fixed scheduler, retaining orders does not separate any
two histories that the order-blind player cannot distinguish. -/
theorem revealing_info_eq_iff_blind_info_eq {i : ι}
    (scheduler : sys.revealingInformation.Policy .scheduler)
    (project : sys.Obs i → sys.SchedulerView)
    (hproject : ∀ state, project (sys.obs state i) = sys.schedulerView state)
    {first second : sys.toExecutionProtocol.State}
    (left : sys.toExecutionProtocol.Trace first)
    (right : sys.toExecutionProtocol.Trace second)
    (hleft : sys.SchedulerFollows scheduler left)
    (hright : sys.SchedulerFollows scheduler right) :
    sys.revealingSignals.infoOf (.player i) left =
        sys.revealingSignals.infoOf (.player i) right ↔
      sys.blindSignals.infoOf (.player i) left =
        sys.blindSignals.infoOf (.player i) right := by
  constructor
  · intro heq
    rw [sys.blind_infoOf_eq_forgetOrders, sys.blind_infoOf_eq_forgetOrders, heq]
  · intro heq
    rw [sys.revealing_info_eq_replayPlayerInfo scheduler project hproject left hleft,
      sys.revealing_info_eq_replayPlayerInfo scheduler project hproject right hright, heq]

/-- Back-translate an arbitrary order-aware player policy by locally replaying
the fixed scheduler. Menus depend only on the current observation, which the
reconstruction preserves definitionally. -/
def backtranslatePlayerPolicy {i : ι}
    (scheduler : sys.revealingInformation.Policy .scheduler)
    (project : sys.Obs i → sys.SchedulerView)
    (policy : sys.revealingInformation.Policy (.player i)) :
    sys.blindInformation.Policy (.player i) :=
  fun info => policy (sys.replayPlayerInfo scheduler project info)

/-- The translated policy takes exactly the runtime policy's action on every
trace following the fixed scheduler, uniformly over other players' policies. -/
theorem backtranslatePlayerPolicy_act_eq {i : ι}
    (scheduler : sys.revealingInformation.Policy .scheduler)
    (project : sys.Obs i → sys.SchedulerView)
    (hproject : ∀ state, project (sys.obs state i) = sys.schedulerView state)
    (policy : sys.revealingInformation.Policy (.player i))
    {state : sys.toExecutionProtocol.State} (trace : sys.toExecutionProtocol.Trace state)
    (hfollows : sys.SchedulerFollows scheduler trace) :
    (sys.backtranslatePlayerPolicy scheduler project policy
      (sys.blindSignals.infoOf (.player i) trace)).1 =
        (policy (sys.revealingSignals.infoOf (.player i) trace)).1 := by
  rw [sys.revealing_info_eq_replayPlayerInfo scheduler project hproject trace hfollows]
  rfl

/-- The same local replay back-translates arbitrary behavioral player
policies. Only the scheduler is fixed and deterministic; the player may
randomize independently at every information state. -/
def backtranslatePlayerBehavioralPolicy {i : ι}
    (scheduler : sys.revealingInformation.Policy .scheduler)
    (project : sys.Obs i → sys.SchedulerView)
    (policy : sys.revealingInformation.BehavioralPolicy (.player i)) :
    sys.blindInformation.BehavioralPolicy (.player i) :=
  fun info => policy (sys.replayPlayerInfo scheduler project info)

/-- Exact local action laws for every behavioral deviation. The translation
depends on the scheduler and the deviator's policy, not on opponents' policies
or the realized hidden state. -/
theorem backtranslatePlayerBehavioralPolicy_law_eq {i : ι}
    (scheduler : sys.revealingInformation.Policy .scheduler)
    (project : sys.Obs i → sys.SchedulerView)
    (hproject : ∀ state, project (sys.obs state i) = sys.schedulerView state)
    (policy : sys.revealingInformation.BehavioralPolicy (.player i))
    {state : sys.toExecutionProtocol.State} (trace : sys.toExecutionProtocol.Trace state)
    (hfollows : sys.SchedulerFollows scheduler trace) :
    (sys.backtranslatePlayerBehavioralPolicy scheduler project policy
      (sys.blindSignals.infoOf (.player i) trace)).map Subtype.val =
        (policy (sys.revealingSignals.infoOf (.player i) trace)).map Subtype.val := by
  rw [sys.revealing_info_eq_replayPlayerInfo scheduler project hproject trace hfollows]
  rfl

/-- Lift a behavioral order-blind policy by forgetting the observed orders. -/
def liftBehavioralPolicy {who : Participant ι}
    (policy : sys.blindInformation.BehavioralPolicy who) :
    sys.revealingInformation.BehavioralPolicy who :=
  fun info => policy (sys.forgetOrders info)

/-- Already order-blind policies are unchanged by back-translation. In
particular, back-translating a deviator does not change compiled honest
opponents into scheduler-dependent policies. -/
theorem backtranslatePlayerBehavioralPolicy_lift {i : ι}
    (scheduler : sys.revealingInformation.Policy .scheduler)
    (project : sys.Obs i → sys.SchedulerView)
    (policy : sys.blindInformation.BehavioralPolicy (.player i)) :
    sys.backtranslatePlayerBehavioralPolicy scheduler project
      (sys.liftBehavioralPolicy policy) = policy := by
  funext info
  apply FinDist.map_injective Subtype.val_injective
  change (policy (sys.forgetOrders (sys.replayPlayerInfo scheduler project info))).map
      Subtype.val = (policy info).map Subtype.val
  rw [sys.forgetOrders_replayPlayerInfo]

/-- Keep the fixed scheduler and replace each original player's behavioral
policy independently by its order-blind replay. The replacement ignores all
observed orders, even at counterfactual information states. -/
def replayBehavioralProfile
    (scheduler : sys.revealingInformation.Policy .scheduler)
    (project : (i : ι) → sys.Obs i → sys.SchedulerView)
    (profile : (who : Participant ι) → sys.revealingInformation.BehavioralPolicy who) :
    (who : Participant ι) → sys.revealingInformation.BehavioralPolicy who
  | .scheduler => scheduler.toBehavioral
  | .player i => fun info =>
      sys.backtranslatePlayerBehavioralPolicy scheduler (project i)
        (profile (.player i)) (sys.forgetOrders info)

variable [Fintype ι]

theorem behavioralJoint_scheduler_eq
    (scheduler : sys.revealingInformation.Policy .scheduler)
    (profile : (who : Participant ι) → sys.revealingInformation.BehavioralPolicy who)
    (hscheduler : profile .scheduler = scheduler.toBehavioral)
    {state : sys.toExecutionProtocol.State} (trace : sys.toExecutionProtocol.Trace state)
    (hterm : ¬ sys.toExecutionProtocol.terminal state)
    {command : {joint // sys.toExecutionProtocol.Legal state joint}}
    (hcommand : command ∈ (sys.revealingInformation.behavioralJoint profile trace hterm).support) :
    command.1 .scheduler = (scheduler (sys.revealingSignals.infoOf .scheduler trace)).1 := by
  rw [InformationModel.behavioralJoint, FinDist.support_map] at hcommand
  obtain ⟨draws, hdraws, rfl⟩ := hcommand
  have hdraw := FinDist.mem_support_pi.mp hdraws Participant.scheduler
  rw [hscheduler] at hdraw
  have heq : draws .scheduler = scheduler (sys.revealingSignals.infoOf .scheduler trace) :=
    FinDist.mem_support_pure.mp hdraw
  exact congrArg Subtype.val heq

/-- **Removing order dependence preserves the complete behavioral history
law under a fixed public-information scheduler.** This holds for every
behavioral player profile, not only equilibrium or honest play. The replay of
each player uses only that player's order-blind history and the scheduler
policy, never opponents' policies or hidden state.

The scheduler is an environment parameter. The comparison uses the same
serialized execution protocol and an order-blind player information
projection. Identification with the canonical compiled source game's compact
information is supplied separately by `Vegas.Scheduled.Information`. -/
theorem runBehavioralFrom_replay
    (scheduler : sys.revealingInformation.Policy .scheduler)
    (project : (i : ι) → sys.Obs i → sys.SchedulerView)
    (hproject : ∀ state i, project i (sys.obs state i) = sys.schedulerView state)
    (profile : (who : Participant ι) → sys.revealingInformation.BehavioralPolicy who)
    (hscheduler : profile .scheduler = scheduler.toBehavioral)
    (fuel : Nat) (start : sys.toExecutionProtocol.History)
    (hfollows : sys.SchedulerFollows scheduler start.trace) :
    sys.revealingInformation.runBehavioralFrom profile fuel start =
      sys.revealingInformation.runBehavioralFrom
        (sys.replayBehavioralProfile scheduler project profile) fuel start := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      by_cases hterm : sys.toExecutionProtocol.terminal start.state
      · rw [InformationModel.runBehavioralFrom_of_terminal _ _ _ hterm,
          InformationModel.runBehavioralFrom_of_terminal _ _ _ hterm]
      · have hhere : sys.revealingInformation.behavioralJoint profile start.trace hterm =
            sys.revealingInformation.behavioralJoint
              (sys.replayBehavioralProfile scheduler project profile) start.trace hterm := by
          apply InformationModel.behavioralJoint_congr
          intro who
          cases who with
          | scheduler => rw [hscheduler]; rfl
          | player i =>
              apply FinDist.map_injective Subtype.val_injective
              change (profile (.player i)
                  (sys.revealingSignals.infoOf (.player i) start.trace)).map Subtype.val =
                (sys.backtranslatePlayerBehavioralPolicy scheduler (project i)
                  (profile (.player i))
                  (sys.forgetOrders (sys.revealingSignals.infoOf (.player i) start.trace))).map
                    Subtype.val
              rw [← sys.blind_infoOf_eq_forgetOrders]
              exact (sys.backtranslatePlayerBehavioralPolicy_law_eq scheduler (project i)
                (fun state => hproject state i) (profile (.player i)) start.trace hfollows).symm
        rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ hterm,
          InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ hterm, ← hhere]
        apply FinDist.bind_congr
        intro command hcommand
        apply FinDist.bindOnSupport_congr
        intro next realized
        apply ih
        exact ⟨hfollows, sys.behavioralJoint_scheduler_eq scheduler profile hscheduler
          start.trace hterm hcommand⟩

/-- Complete behavioral play from the initial history has the same law after
replacing every player independently by its order-blind replay. -/
theorem runBehavioral_replay
    (scheduler : sys.revealingInformation.Policy .scheduler)
    (project : (i : ι) → sys.Obs i → sys.SchedulerView)
    (hproject : ∀ state i, project i (sys.obs state i) = sys.schedulerView state)
    (profile : (who : Participant ι) → sys.revealingInformation.BehavioralPolicy who)
    (hscheduler : profile .scheduler = scheduler.toBehavioral)
    (fuel : Nat) :
    sys.revealingInformation.runBehavioral profile fuel =
      sys.revealingInformation.runBehavioral
        (sys.replayBehavioralProfile scheduler project profile) fuel :=
  sys.runBehavioralFrom_replay scheduler project hproject profile hscheduler fuel
    sys.toExecutionProtocol.initHistory trivial

/-- Install a fixed scheduler without changing any original player's policy. -/
def fixScheduler
    (scheduler : sys.revealingInformation.Policy .scheduler)
    (profile : (who : Participant ι) → sys.revealingInformation.BehavioralPolicy who) :
    (who : Participant ι) → sys.revealingInformation.BehavioralPolicy who
  | .scheduler => scheduler.toBehavioral
  | .player i => profile (.player i)

/-- **Replay also preserves the law for a randomly selected scheduler
policy.** Each sampled policy is actually executed along the public history;
its realized orders need not be data-independent. Randomness selecting the
policy is independent of the subsequent player/chance draws. The translated
players are allowed to know the selected policy and simulate it locally.

This is equality of executed-history laws, not merely an independent-signal
game instantiated with a function type. It still compares the order-revealing
and full order-blind runtime information models, not the compact source game. -/
theorem runMixedScheduler_replay
    (schedulers : FinDist (sys.revealingInformation.Policy .scheduler))
    (project : (i : ι) → sys.Obs i → sys.SchedulerView)
    (hproject : ∀ state i, project i (sys.obs state i) = sys.schedulerView state)
    (profile : (who : Participant ι) → sys.revealingInformation.BehavioralPolicy who)
    (fuel : Nat) :
    (schedulers.bind fun scheduler => sys.revealingInformation.runBehavioral
      (sys.fixScheduler scheduler profile) fuel) =
        schedulers.bind fun scheduler => sys.revealingInformation.runBehavioral
          (sys.replayBehavioralProfile scheduler project profile) fuel := by
  apply FinDist.bind_congr
  intro scheduler _
  exact sys.runBehavioral_replay scheduler project hproject
    (sys.fixScheduler scheduler profile) rfl fuel

end Vegas.ScheduledSystem
