/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Scheduled.Equilibrium
import Vegas.Compile.Request
import Vegas.Runtime.FiniteRequest
import Mathlib.Data.Fintype.List

/-! # Private request windows followed by public serialization

Each round resolves private request windows into a legal joint submission and
then executes the compiled serializer. Players retain both their private request
histories and the serializer's public order observations. The scheduler is an
arbitrary public-data behavioral policy, compiled through the request interface;
its request is accepted immediately. No scheduler optimality is required.

This is NOT a delivery scheduler: attempts, rejections, and silence are not
published, and the scheduler cannot postpone, censor, or expire a request. A
public delivery/deadline model needs separate operational and strategic proofs.
-/

noncomputable section

namespace Vegas.Machine.Program

open GameTheory GameTheory.Protocol Vegas.Runtime

variable {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}

/-- Players keep their source request representation. The scheduler supplies
an order through a canonical menu validator, without a delivery decision. -/
def SerializedRequest (Request : Player → Type) : Participant Player → Type
  | .scheduler => Option (List Player)
  | .player who => Request who

def serializedTimeoutPolicy (program : Program Player L)
    {Request : Player → Type} (interface : RequestCompiler.Interface program.information Request) :
    (who : Participant Player) → program.serializedArena.information.Policy who
  | .scheduler, info =>
      ⟨some (Classical.choose (program.serializedSystem.schedules_nonempty info.current)),
        ⟨_, Classical.choose_spec (program.serializedSystem.schedules_nonempty info.current), rfl⟩⟩
  | .player who, info => program.serializedPlayerChoiceEquiv who info
      ((interface.gate who).timeoutAction (program.eraseSerializedPlayerInformation who info))

/-- Lift the original source request interface automatically. Player timeout
actions, validation, encoding, and window bounds ignore the added order log;
deviating controllers may nevertheless observe and use that log. -/
def serializedRequestInterface (program : Program Player L)
    {Request : Player → Type} (interface : RequestCompiler.Interface program.information Request) :
    RequestCompiler.Interface program.serializedArena.information (SerializedRequest Request) where
  gate
    | .scheduler =>
        (RequestCompiler.menuInterface program.serializedArena.information
          (program.serializedTimeoutPolicy interface) (fun _ _ => 0)).gate .scheduler
    | .player who => {
        timeoutAction := program.serializedTimeoutPolicy interface (.player who)
        decode := fun info request =>
          ((interface.gate who).decode
            (program.eraseSerializedPlayerInformation who info) request).map
              (program.serializedPlayerChoiceEquiv who info)
        encode := fun info choice =>
          (interface.gate who).encode (program.eraseSerializedPlayerInformation who info)
            ((program.serializedPlayerChoiceEquiv who info).symm choice)
        decode_encode := by
          intro info choice
          rw [(interface.gate who).decode_encode, Option.map_some, Equiv.apply_symm_apply] }
  slots
    | .scheduler => fun _ => 0
    | .player who => fun info =>
        interface.slots who (program.eraseSerializedPlayerInformation who info)

/-- Finite original-player action packets give finite serialized menus.
The scheduler's legal orders are duplicate-free lists, not arbitrary lists. -/
@[reducible] def serializedChoiceFintype (program : Program Player L)
    (actions : ∀ who, Fintype (program.execution.Action who))
    (who : Participant Player) (info : program.serializedArena.information.InfoState who) :
    Fintype (program.serializedArena.information.Choice who info) := by
  classical
  cases who with
  | player who =>
      letI : Fintype (EventGraph.FrontierAction program.graph who) := actions who
      letI : Fintype (program.information.Choice who
          (program.eraseSerializedPlayerInformation who info)) :=
        Fintype.ofInjective (β := Option (EventGraph.FrontierAction program.graph who))
          (fun choice => (choice.1 : Option (EventGraph.FrontierAction program.graph who)))
          (fun _ _ heq => Subtype.ext heq)
      exact Fintype.ofEquiv _ (program.serializedPlayerChoiceEquiv who info)
  | scheduler =>
      let extract : program.serializedArena.information.Choice .scheduler info →
          {order : List Player // order.Nodup} := fun choice =>
        ⟨Classical.choose choice.2, (Classical.choose_spec choice.2).1.1⟩
      apply Fintype.ofInjective extract
      intro left right heq
      apply Subtype.ext
      exact (Classical.choose_spec left.2).2.trans
        ((congrArg (fun order : {order : List Player // order.Nodup} => some order.1) heq).trans
          (Classical.choose_spec right.2).2.symm)

end Vegas.Machine.Program

namespace Vegas.WFProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Vegas.Runtime

variable {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
variable (source : WFProgram Player L) [FiniteDomains source]

/-- Scheduler actions are lists, but every legal order is duplicate-free.
Thus the choice menus are finite without assuming that all order lists are. -/
@[reducible] def serializedChoiceFintype (who : Participant Player)
    (info : (Machine.compile source).serializedArena.information.InfoState who) :
    Fintype ((Machine.compile source).serializedArena.information.Choice who info) :=
  (Machine.compile source).serializedChoiceFintype source.actionFintype who info

variable {Request : Participant Player → Type}
variable (interface : RequestCompiler.Interface
  (Machine.compile source).serializedArena.information Request)

variable (schedulerUtility : (Machine.compile source).serializedArena.History → ℝ)

def serializedRequestGame : UtilityGame (Participant Player) :=
  (RequestCompiler.targetGame (Machine.compile source).serializedArena.information interface
    (Machine.compile source).graph.nodeCount
    ((Machine.compile source).serializedUtility schedulerUtility)).mixed

/-- The middle boundary is the actual serialized behavioral game. This
certificate preserves its full history law, including all published orders. -/
def serializedRequestAdequacy :
    DeviationAdequacy ((Machine.compile source).serializedGame schedulerUtility).behavioral
      (source.serializedRequestGame interface schedulerUtility) :=
  ((Machine.compile source).serializedGame schedulerUtility).requestAdequacy
    source.serializedChoiceFintype (Machine.compile source).serializedPerfectRecall interface

def compileSerializedRequestProfile
    (scheduler : (Machine.compile source).serializedArena.information.BehavioralPolicy .scheduler)
    (profile : Profile source.game.behavioral.form.sig) :
    Profile (source.serializedRequestGame interface schedulerUtility).form.sig :=
  (source.serializedRequestAdequacy interface schedulerUtility).compileProfile
    ((Machine.compile source).compileSerializedBehavioralProfile scheduler profile)

/-- Exact original-player Nash equivalence. The scheduler is fixed but
arbitrary, may use public game data, and need not optimize any utility. -/
theorem serialized_request_nash_iff
    (scheduler : (Machine.compile source).serializedArena.information.BehavioralPolicy .scheduler)
    (profile : Profile source.game.behavioral.form.sig) :
    Scheduled.IsPlayerNash (source.serializedRequestGame interface schedulerUtility)
      (source.compileSerializedRequestProfile interface schedulerUtility scheduler profile) ↔
    IsNash source.game.behavioral.form (euPreference source.game.behavioral.utility) profile := by
  let certificate := source.serializedRequestAdequacy interface schedulerUtility
  refine Iff.trans ?_
    ((Machine.compile source).isPlayerNash_compileSerialized_iff schedulerUtility scheduler profile)
  change Scheduled.IsPlayerNash _ (certificate.compileProfile _) ↔ _
  constructor
  · intro hnash who replacement _
    have h := hnash who (certificate.compileStrategy (.player who) replacement) trivial
    change expectedUtility _ _ ((source.serializedRequestGame interface schedulerUtility).form.play
      (Profile.update (certificate.compileProfile _) _ _)) ≤ _ at h
    rw [certificate.compileProfile_update, certificate.expectedUtility_compileProfile,
      certificate.expectedUtility_compileProfile] at h
    exact h
  · intro hnash who replacement _
    rw [certificate.expectedUtility_deviation _ _ _ trivial,
      certificate.expectedUtility_compileProfile]
    exact hnash who (certificate.backtranslateStrategy (.player who) replacement) trivial

/-- Honest compiled play has exactly the original terminal configuration law. -/
theorem serialized_request_honest_law
    (scheduler : (Machine.compile source).serializedArena.information.BehavioralPolicy .scheduler)
    (profile : Profile source.game.behavioral.form.sig) :
    ((source.serializedRequestGame interface schedulerUtility).form.play
      (source.compileSerializedRequestProfile interface schedulerUtility scheduler profile)).map
        (fun state => state.1.state.base) =
    ((Machine.compile source).information.runBehavioral profile
      (Machine.compile source).graph.nodeCount).map ExecutionProtocol.History.state := by
  have h := (source.serializedRequestAdequacy interface schedulerUtility).honest_law
    ((Machine.compile source).compileSerializedBehavioralProfile scheduler profile)
  have hmap := congrArg (fun law => law.map (fun history => history.state.base)) h
  rw [FinDist.map_comp] at hmap
  exact hmap.trans ((Machine.compile source).runBehavioral_compileSerialized scheduler profile)

/-- Every combined request/order-aware deviation is a finite mixture of source
deviations against the same honest opponents. No equilibrium premise is used. -/
theorem serialized_request_deviation_law
    (scheduler : (Machine.compile source).serializedArena.information.BehavioralPolicy .scheduler)
    (profile : Profile source.game.behavioral.form.sig) (who : Player)
    (replacement : (source.serializedRequestGame interface schedulerUtility).form.sig.Strategy
      (.player who)) :
    ∃ alternatives : FinDist ((Machine.compile source).information.BehavioralPolicy who),
      ((source.serializedRequestGame interface schedulerUtility).form.play
        (Profile.update
          (source.compileSerializedRequestProfile interface schedulerUtility scheduler profile)
          (.player who) replacement)).map (fun state => state.1.state.base) =
      alternatives.bind fun alternative =>
        ((Machine.compile source).information.runBehavioral
          (Function.update profile who alternative)
          (Machine.compile source).graph.nodeCount).map ExecutionProtocol.History.state := by
  let certificate := source.serializedRequestAdequacy interface schedulerUtility
  obtain ⟨alternatives, hlaw⟩ := (Machine.compile source).serializedDeviation_eq_sourceMixture
    scheduler profile who (certificate.backtranslateStrategy (.player who) replacement)
  refine ⟨alternatives, ?_⟩
  have h := certificate.deviation_law
    ((Machine.compile source).compileSerializedBehavioralProfile scheduler profile)
    (.player who) replacement trivial
  have hmap := congrArg (fun law => law.map (fun history => history.state.base)) h
  rw [FinDist.map_comp] at hmap
  exact hmap.trans hlaw

/-- The composition preserves the same approximation budget, rather than
merely preserving exact equilibria. Scheduler deviations are not tested. -/
theorem serialized_request_approximate_nash_iff
    (scheduler : (Machine.compile source).serializedArena.information.BehavioralPolicy .scheduler)
    (profile : Profile source.game.behavioral.form.sig) (ε : ℝ) :
    (∀ who replacement,
      expectedUtility (source.serializedRequestGame interface schedulerUtility).utility
        (.player who)
        ((source.serializedRequestGame interface schedulerUtility).form.play
          (Profile.update
            (source.compileSerializedRequestProfile interface schedulerUtility scheduler profile)
            (.player who) replacement)) ≤
      expectedUtility (source.serializedRequestGame interface schedulerUtility).utility
        (.player who)
        ((source.serializedRequestGame interface schedulerUtility).form.play
          (source.compileSerializedRequestProfile
            interface schedulerUtility scheduler profile)) + ε) ↔
    IsεNash source.game.behavioral.form source.game.behavioral.utility ε profile := by
  let certificate := source.serializedRequestAdequacy interface schedulerUtility
  refine Iff.trans ?_
    ((Machine.compile source).serialized_approximate_nash_iff schedulerUtility scheduler profile ε)
  unfold compileSerializedRequestProfile
  constructor
  · intro hbound who replacement
    have h := hbound who (certificate.compileStrategy (.player who) replacement)
    rw [certificate.compileProfile_update, certificate.expectedUtility_compileProfile,
      certificate.expectedUtility_compileProfile] at h
    exact h
  · intro hbound who replacement
    rw [certificate.expectedUtility_deviation _ _ _ trivial,
      certificate.expectedUtility_compileProfile]
    exact hbound who (certificate.backtranslateStrategy (.player who) replacement)

end Vegas.WFProgram
