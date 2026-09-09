/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies

/-! # A guarded message-application lottery

This fixture tests the generic application runtime directly. A designated
player privately records a prediction, publishes a lock request, and then the
environment may trigger one fixed fair draw. It is an application regression,
not a strategic or liveness theorem.
-/

namespace InteractionTests.MessageApplication

open Interaction GameTheory.Math.Probability

noncomputable section

abbrev Principal := Fin 2

inductive Payload where
  | lock
  | malformed
  deriving DecidableEq

inductive PrivateCommand where
  | predict (value : Bool)

inductive EnvironmentCommand where
  | draw

structure Application where
  prediction : Option Bool
  locked : Bool
  outcome : Option Bool
  deriving DecidableEq

structure PublicState where
  locked : Bool
  outcome : Option Bool
  deriving DecidableEq

def fair : FinDist Bool := FinDist.uniformOfFintype

def privateStep (state : Application) (who : Principal) :
    PrivateCommand → Application
  | .predict value =>
      if who = 0 ∧ state.prediction.isNone ∧ !state.locked then
        { state with prediction := some value }
      else state

def environmentStep (state : Application) :
    EnvironmentCommand → FinDist Application
  | .draw =>
      if state.locked ∧ state.outcome.isNone then
        fair.map fun value => { state with outcome := some value }
      else FinDist.pure state

def handle (state : Application) (message : Message Principal Payload) :
    Option Application :=
  match message.payload with
  | .lock =>
      if message.sender = 0 ∧ state.prediction.isSome ∧ !state.locked then
        some { state with locked := true }
      else none
  | .malformed => none

def observe (state : Application) (_ : Principal) : PublicState :=
  ⟨state.locked, state.outcome⟩

def lottery : MessageApplication Principal where
  Application := Application
  Payload := Payload
  PrivateCommand := PrivateCommand
  EnvironmentCommand := EnvironmentCommand
  PlayerView := PublicState
  EnvironmentView := PublicState
  privateStep := privateStep
  environmentStep := environmentStep
  handle := handle
  observePlayer := observe
  observeEnvironment := fun state => ⟨state.locked, state.outcome⟩

def initialApplication : Application := ⟨none, false, none⟩
def initial := MessageApplication.State.initial lottery initialApplication

def acceptedActions : List lottery.Action :=
  [.privateCommand 0 (.predict true), .submit 0 .lock, .deliver 1 (0, 0),
    .include (0, 0)]

def s1 := { initial with application := privateStep initial.application 0 (.predict true) }
def s2 := { s1 with pool := (s1.pool.submit 0 .lock).2 }
def s3 := { s2 with pool := (s2.pool.deliver 1 (0, 0)).state }
def s4 := lottery.includePending s3 (0, 0)

private theorem step1 : lottery.step initial (.privateCommand 0 (.predict true)) =
    FinDist.pure s1 := rfl
private theorem step2 : lottery.step s1 (.submit 0 .lock) = FinDist.pure s2 := rfl
private theorem step3 : lottery.step s2 (.deliver 1 (0, 0)) = FinDist.pure s3 := rfl
private theorem step4 : lottery.step s3 (.include (0, 0)) = FinDist.pure s4 := rfl

theorem accepted_run : lottery.run acceptedActions initial = FinDist.pure s4 := by
  rw [show acceptedActions = [.privateCommand 0 (.predict true), .submit 0 .lock,
    .deliver 1 (0, 0), .include (0, 0)] from rfl]
  rw [MessageApplication.run_cons, step1, FinDist.pure_bind]
  rw [MessageApplication.run_cons, step2, FinDist.pure_bind]
  rw [MessageApplication.run_cons, step3, FinDist.pure_bind]
  rw [MessageApplication.run_cons, step4, FinDist.pure_bind]
  rfl

theorem accepted_receipt_and_publication :
    s4.pool.ledger = [⟨(0, 0), .lock⟩] ∧ s4.pool.inbox 1 = [⟨(0, 0), .lock⟩] ∧
      s4.receipts = [((0, 0), true)] := by
  constructor
  · rfl
  · constructor <;> rfl

def rejectedActions : List lottery.Action :=
  [.submit 0 .lock, .deliver 1 (0, 0), .include (0, 0)]

def r1 := { initial with pool := (initial.pool.submit 0 .lock).2 }
def r2 := { r1 with pool := (r1.pool.deliver 1 (0, 0)).state }
def r3 := lottery.includePending r2 (0, 0)

private theorem rejectedStep1 : lottery.step initial (.submit 0 .lock) =
    FinDist.pure r1 := rfl
private theorem rejectedStep2 : lottery.step r1 (.deliver 1 (0, 0)) =
    FinDist.pure r2 := rfl
private theorem rejectedStep3 : lottery.step r2 (.include (0, 0)) =
    FinDist.pure r3 := rfl

theorem rejected_run : lottery.run rejectedActions initial = FinDist.pure r3 := by
  rw [show rejectedActions = [.submit 0 .lock, .deliver 1 (0, 0),
    .include (0, 0)] from rfl]
  rw [MessageApplication.run_cons, rejectedStep1, FinDist.pure_bind]
  rw [MessageApplication.run_cons, rejectedStep2, FinDist.pure_bind]
  rw [MessageApplication.run_cons, rejectedStep3, FinDist.pure_bind]
  rfl

theorem rejected_receipt_and_publication :
    r3.pool.ledger = [⟨(0, 0), .lock⟩] ∧ r3.pool.inbox 1 = [⟨(0, 0), .lock⟩] ∧
      r3.receipts = [((0, 0), false)] := by
  constructor
  · rfl
  · constructor <;> rfl

theorem unknown_include_stutters :
    lottery.step initial (.include (0, 7)) = FinDist.pure initial := by
  rfl

theorem private_command_is_scoped :
    lottery.step initial (.privateCommand 1 (.predict true)) = FinDist.pure initial := by
  rfl

theorem early_draw_stutters :
    lottery.step initial (.environment .draw) = FinDist.pure initial := by
  simp [MessageApplication.step, lottery, environmentStep, initial,
    initialApplication, MessageApplication.State.initial]

theorem accepted_draw_law :
    lottery.step s4 (.environment .draw) =
      fair.map (fun value =>
        { s4 with application.outcome := some value }) := by
  change (fair.map (fun value =>
      { s4.application with outcome := some value })).map
        (fun application => { s4 with application }) = _
  rw [FinDist.map_comp]
  rfl

theorem accepted_draw_is_fair (value : Bool) :
    ((lottery.step s4 (.environment .draw)).map
        (fun state => state.application.outcome)).prob (some value) = 1 / 2 := by
  have hlaw :
      (lottery.step s4 (.environment .draw)).map
          (fun state => state.application.outcome) =
        fair.map some := by
    rw [accepted_draw_law, FinDist.map_comp]
    apply congrArg (FinDist.map · fair)
    funext sampled
    rfl
  rw [hlaw, FinDist.prob_map_of_injective]
  · simp [fair]
  · intro left right heq
    exact Option.some.inj heq

def completed (value : Bool) : MessageApplication.State lottery :=
  { s4 with application.outcome := some value }

theorem completion_disables_reroll (value : Bool) :
    lottery.step (completed value) (.environment .draw) =
      FinDist.pure (completed value) := by
  simp [MessageApplication.step, lottery, environmentStep, completed]

theorem observations_hide_prediction :
    MessageApplication.State.observe lottery
        { s4 with application.prediction := some false } 1 =
      MessageApplication.State.observe lottery s4 1 := by
  rfl

/-- The policy game retains application randomness even when every controller
is deterministic. This test starts at the lock established by `accepted_run`. -/
theorem policy_draw_law (players : Principal → lottery.PlayerPolicy) :
    (((lottery.policyGame
      (fun _ _ => FinDist.pure (.application .draw)) [.environment] s4).play players).map
        (fun execution => execution.native.application.outcome)) = fair.map some := by
  simp only [MessageApplication.policyGame, MessageApplication.runPolicies,
    MessageApplication.invoke, FinDist.pure_bind, FinDist.bind_pure]
  change (lottery.environmentPolicyStep
    (MessageApplication.PolicyExecution.initial lottery s4) (.application .draw)).map
      ((fun state : lottery.State => state.application.outcome) ∘
        MessageApplication.PolicyExecution.native) = fair.map some
  rw [← FinDist.map_comp, MessageApplication.environmentStep_native]
  change (lottery.step s4 (.environment .draw)).map
    (fun state : lottery.State => state.application.outcome) = fair.map some
  rw [accepted_draw_law]
  rw [FinDist.map_comp]
  rfl

end

end InteractionTests.MessageApplication
