/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.ChoiceController

/-! # Sample-once choice-controller regressions

This non-Vegas fixture invokes one stochastic controller twice before any
message is included.  The second invocation retries the value recorded by the
first submission rather than sampling the choice kernel again.
-/

namespace InteractionTests.ChoiceController

open Interaction GameTheory.Math.Probability

noncomputable section

abbrev Principal := Fin 1

inductive Payload where
  | choice (value : Bool)
  | other (value : Bool)
  deriving DecidableEq

abbrev Application := Bool
abbrev PrivateCommand := Unit
abbrev EnvironmentCommand := Unit
abbrev View := Bool

def application : MessageApplication Principal where
  Application := Application
  Payload := Payload
  PrivateCommand := PrivateCommand
  EnvironmentCommand := EnvironmentCommand
  PlayerView := View
  EnvironmentView := Unit
  privateStep := fun state _ _ => state
  environmentStep := fun state _ => FinDist.pure state
  handle := fun _ _ => none
  observePlayer := fun state _ => state
  observeEnvironment := fun _ => ()

def codec : MessageApplication.SubmissionCodec Bool Payload where
  encode := .choice
  decode
    | .choice value => some value
    | .other _ => none
  decode_encode := by intro value; rfl

def fair : FinDist Bool := FinDist.uniformOfFintype

def controller : application.ChoiceController Bool Unit where
  codec := codec
  ready := fun _ => true
  resolved := fun view => view.application
  readout? := fun _ _ => some ()
  kernel := fun _ => fair
  retry := fun _ _ => true

def players : Principal → application.PlayerPolicy :=
  fun _ => controller.policy application

def environment : application.EnvironmentPolicy :=
  fun _ _ => FinDist.pure .wait

def initial : application.State :=
  MessageApplication.State.initial application false

def law : FinDist application.PolicyExecution :=
  application.runPolicies players environment [.player 0, .player 0]
    (MessageApplication.PolicyExecution.initial application initial)

def e0 : application.PolicyExecution :=
  MessageApplication.PolicyExecution.initial application initial

def e1 (value : Bool) : application.PolicyExecution :=
  { native := { initial with pool := (initial.pool.submit 0 (.choice value)).2 }
    principalHistory := fun _ =>
      [⟨MessageApplication.State.observe application initial 0,
        .submit (.choice value)⟩]
    environmentHistory := []
    nativeTrace := [.submit 0 (.choice value)] }

def e2 (value : Bool) : application.PolicyExecution :=
  { native := { (e1 value).native with
      pool := ((e1 value).native.pool.submit 0 (.choice value)).2 }
    principalHistory := fun _ =>
      (e1 value).principalHistory 0 ++
        [⟨MessageApplication.State.observe application (e1 value).native 0,
          .submit (.choice value)⟩]
    environmentHistory := []
    nativeTrace := (e1 value).nativeTrace ++ [.submit 0 (.choice value)] }

private theorem first_policy :
    players 0 (e0.principalHistory 0)
        (MessageApplication.State.observe application e0.native 0) =
      fair.map fun value => .submit (.choice value) := by
  rfl

private theorem first_step (value : Bool) :
    application.playerStep 0 e0 (.submit (.choice value)) = FinDist.pure (e1 value) := by
  simp only [MessageApplication.playerStep, MessageApplication.advance, e0, e1, application,
    initial, MessageApplication.State.initial, MessageApplication.PolicyExecution.initial,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind]
  congr
  funext who
  fin_cases who
  rfl

private theorem retry_policy (value : Bool) :
    players 0 ((e1 value).principalHistory 0)
        (MessageApplication.State.observe application (e1 value).native 0) =
      FinDist.pure (.submit (.choice value)) := by
  rfl

private theorem retry_step (value : Bool) :
    application.playerStep 0 (e1 value) (.submit (.choice value)) =
      FinDist.pure (e2 value) := by
  simp only [MessageApplication.playerStep, MessageApplication.advance, e1, e2, application,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind]
  congr
  funext who
  fin_cases who
  rfl

private theorem first_invoke :
    application.invoke players environment e0 (.player 0) = fair.map e1 := by
  simp only [MessageApplication.invoke]
  rw [first_policy, FinDist.bind_map]
  apply congrArg (FinDist.bind fair)
  funext value
  rw [first_step]

private theorem retry_invoke (value : Bool) :
    application.invoke players environment (e1 value) (.player 0) =
      FinDist.pure (e2 value) := by
  simp only [MessageApplication.invoke]
  rw [retry_policy, FinDist.pure_bind, retry_step]

def decodePayload : Payload → Option Bool
  | .choice value => some value
  | .other _ => none

def pendingValues (execution : application.PolicyExecution) : List (Option Bool) :=
  execution.native.pool.pending.map fun message => decodePayload message.payload

def historyValues (execution : application.PolicyExecution) : List (Option Bool) :=
  (execution.principalHistory 0).map fun entry =>
    match entry.command with
    | .submit payload => decodePayload payload
    | _ => none

def recordedValues (execution : application.PolicyExecution) :
    List (Option Bool) × List (Option Bool) :=
  (pendingValues execution, historyValues execution)

/-- Two polls retain one sample in both the wire pool and own command history.
The law is diagonal, rather than the product of two fresh fair samples. -/
theorem two_polls_sample_once :
    law.map recordedValues =
      fair.map (fun value => ([some value, some value], [some value, some value])) := by
  rw [show law = application.runPolicies players environment [.player 0, .player 0] e0
    from rfl]
  simp only [MessageApplication.runPolicies, first_invoke, FinDist.bind_map,
    retry_invoke, FinDist.bind_pure, FinDist.map_bind, FinDist.map_pure]
  rw [FinDist.map_eq_bind]
  apply congrArg (FinDist.bind fair)
  funext value
  rfl

theorem codec_rejects_other_endpoint (value : Bool) :
    codec.decode (.other value) = none := rfl

theorem resolved_controller_waits (history : List application.PlayerEntry)
    (view : application.View) (hresolved : view.application = true) :
    controller.policy application history view = FinDist.pure .wait := by
  exact controller.policy_of_resolved application history view hresolved

end

end InteractionTests.ChoiceController
