/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.ChoiceControllerHistory
import Interaction.IdealCommitments

/-! # Private sample-once controller regression

The sampled command registers an ideal commitment through the authenticated
private-command capability. Nothing is submitted to the public message pool.
-/

namespace InteractionTests.PrivateChoice

open Interaction GameTheory.Math.Probability

noncomputable section

abbrev Principal := Fin 1

structure PrivateCommand where
  value : Bool
  deriving DecidableEq

def application : MessageApplication Principal where
  Application := IdealCommitments Principal Nat Bool
  Payload := Unit
  PrivateCommand := PrivateCommand
  EnvironmentCommand := Unit
  PlayerView := Unit
  EnvironmentView := Unit
  privateStep := fun service who command =>
    (service.sealValue who 0 command.value).state
  environmentStep := fun service _ => FinDist.pure service
  handle := fun _ _ => none
  observePlayer := fun _ _ => ()
  observeEnvironment := fun _ => ()

def privateEncoding : MessageApplication.ChoiceEncoding Bool PrivateCommand where
  encode value := ⟨value⟩
  decode command := some command.value
  decode_encode := by intro value; rfl
  decode_sound := by
    intro command value hdecode
    cases command with
    | mk actual =>
        simp only [Option.some.injEq] at hdecode
        subst actual
        rfl

def fair : FinDist Bool := FinDist.uniformOfFintype

def controller : application.ChoiceController Bool Unit where
  codec := privateEncoding.privateCommand application
  ready := fun _ => true
  resolved := fun _ => false
  readout? := fun _ _ => some ()
  kernel := fun _ => fair
  retry := fun _ _ => false

def players : Principal → application.PlayerPolicy :=
  fun _ => controller.policy application

def environment : application.EnvironmentPolicy :=
  fun _ _ => FinDist.pure .wait

def initial : application.State :=
  MessageApplication.State.initial application IdealCommitments.empty

def law : FinDist application.PolicyExecution :=
  application.runPolicies players environment [.player 0, .player 0]
    (MessageApplication.PolicyExecution.initial application initial)

def observed (execution : application.PolicyExecution) :
    Option Bool × Option Bool × List (Message Principal Unit) :=
  (execution.native.application.lookup (0, 0),
    controller.codec.cachedValue application (execution.principalHistory 0),
    execution.native.pool.pending)

/-- Registration and the controller cache retain the same single fair draw;
the second poll waits, and private registration creates no public message. -/
theorem two_polls_private_sample_once :
    law.map observed = fair.map fun value => (some value, some value, []) := by
  simp only [law, MessageApplication.runPolicies, MessageApplication.invoke, players,
    controller, MessageApplication.ChoiceController.policy, privateEncoding,
    MessageApplication.ChoiceEncoding.privateCommand,
    MessageApplication.ChoiceEncoding.cachedValue, initial,
    MessageApplication.PolicyExecution.initial, application, MessageApplication.State.initial,
    FinDist.bind_map, FinDist.map_bind, FinDist.bind_pure,
    Bool.false_eq_true, if_false, if_true]
  rw [FinDist.bind_bind]
  simp only [FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro value _
  simp [MessageApplication.playerStep, MessageApplication.advance,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step,
    MessageApplication.ChoiceEncoding.privateCommand, privateEncoding,
    controller, observed, application, MessagePool.empty,
    IdealCommitments.sealValue, IdealCommitments.lookup, IdealCommitments.empty]

end

end InteractionTests.PrivateChoice
