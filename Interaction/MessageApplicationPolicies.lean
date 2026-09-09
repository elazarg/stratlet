/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplication
import GameTheory.Core.Form

/-! # Observation-local policies for message applications

The policy game follows a fixed finite invocation list. Each principal sees
the current principal projection and only its own sampled command history.
The environment sees the complete message pool and the application's explicit
environment projection. Native application randomness remains a `FinDist`
transition and is not collapsed into policy randomization.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} (app : MessageApplication Principal)

inductive PlayerCommand where
  | privateCommand (command : app.PrivateCommand)
  | submit (payload : app.Payload)
  | replay (id : MessageId Principal)
  | wait

structure PlayerEntry where
  beforeView : app.View
  command : app.PlayerCommand

abbrev PlayerPolicy :=
  List app.PlayerEntry → app.View → FinDist app.PlayerCommand

/-- Environment-controlled wire and application triggers. The application
command selects a fixed kernel, not one of its stochastic outcomes. -/
inductive EnvironmentPolicyCommand where
  | deliver (observer : Principal) (id : MessageId Principal)
  | include (id : MessageId Principal)
  | application (command : app.EnvironmentCommand)
  | wait

structure EnvironmentEntry where
  beforeView : app.EnvironmentObservation
  command : app.EnvironmentPolicyCommand

abbrev EnvironmentPolicy :=
  List app.EnvironmentEntry → app.EnvironmentObservation →
    FinDist app.EnvironmentPolicyCommand

inductive Invocation where
  | player (who : Principal)
  | environment

/-- Policy-facing bounded execution. The native action trace is proof-facing
and is not included in either observation projection. -/
structure PolicyExecution where
  native : app.State
  principalHistory : Principal → List app.PlayerEntry
  environmentHistory : List app.EnvironmentEntry
  nativeTrace : List app.Action

def PolicyExecution.initial (state : app.State) : app.PolicyExecution :=
  ⟨state, fun _ => [], [], []⟩

def PlayerCommand.toAction (who : Principal) : app.PlayerCommand → Option app.Action
  | .privateCommand command => some (.privateCommand who command)
  | .submit payload => some (.submit who payload)
  | .replay id => some (.replay who id)
  | .wait => none

def EnvironmentPolicyCommand.toAction :
    app.EnvironmentPolicyCommand → Option app.Action
  | .deliver observer id => some (.deliver observer id)
  | .include id => some (.include id)
  | .application command => some (.environment command)
  | .wait => none

/-- Execute an optional native action, retaining the full stochastic kernel. -/
def advance [DecidableEq Principal] (execution : app.PolicyExecution) :
    Option app.Action → FinDist (app.State × List app.Action)
  | none => FinDist.pure (execution.native, execution.nativeTrace)
  | some action =>
      (app.step execution.native action).bind fun next =>
        FinDist.pure (next, execution.nativeTrace ++ [action])

def playerStep [DecidableEq Principal] (who : Principal)
    (execution : app.PolicyExecution) (command : app.PlayerCommand) :
    FinDist app.PolicyExecution :=
  let view := State.observe app execution.native who
  (app.advance execution (PlayerCommand.toAction app who command)).bind fun advanced =>
    FinDist.pure
      { execution with
        native := advanced.1
        principalHistory := fun other =>
          if other = who then execution.principalHistory who ++ [⟨view, command⟩]
          else execution.principalHistory other
        nativeTrace := advanced.2 }

def environmentPolicyStep [DecidableEq Principal]
    (execution : app.PolicyExecution) (command : app.EnvironmentPolicyCommand) :
    FinDist app.PolicyExecution :=
  let view := State.environmentView app execution.native
  (app.advance execution (EnvironmentPolicyCommand.toAction app command)).bind fun advanced =>
    FinDist.pure
      { execution with
        native := advanced.1
        environmentHistory := execution.environmentHistory ++ [⟨view, command⟩]
        nativeTrace := advanced.2 }

def invoke [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (execution : app.PolicyExecution) : @Invocation Principal → FinDist app.PolicyExecution
  | .player who =>
      (players who (execution.principalHistory who) (State.observe app execution.native who)).bind
        (app.playerStep who execution)
  | .environment =>
      (environment execution.environmentHistory (State.environmentView app execution.native)).bind
        (app.environmentPolicyStep execution)

def runPolicies [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy) :
    List (@Invocation Principal) → app.PolicyExecution → FinDist app.PolicyExecution
  | [], execution => FinDist.pure execution
  | invocation :: rest, execution =>
      (invoke app players environment execution invocation).bind
        (runPolicies players environment rest)

def policySignature (Principal : Type uPrincipal)
    (app : MessageApplication Principal) : GameSignature Principal where
  Strategy := fun _ => app.PlayerPolicy
  Outcome := app.PolicyExecution

def policyGame [DecidableEq Principal]
    (environment : app.EnvironmentPolicy) (schedule : List (@Invocation Principal))
    (initial : app.State) : GameForm Principal where
  sig := policySignature Principal app
  play players := runPolicies app players environment schedule
    (PolicyExecution.initial app initial)

/-! ## Local-history laws -/

/-- Recording a player command preserves the native transition law. -/
theorem playerStep_native [DecidableEq Principal] (who : Principal)
    (execution : app.PolicyExecution) (command : app.PlayerCommand) :
    (app.playerStep who execution command).map PolicyExecution.native =
      match command.toAction app who with
      | none => FinDist.pure execution.native
      | some action => app.step execution.native action := by
  cases hcommand : command.toAction app who <;>
    simp [playerStep, advance, hcommand, FinDist.map_bind]

/-- Recording an environment command preserves the native transition law. -/
theorem environmentStep_native [DecidableEq Principal]
    (execution : app.PolicyExecution) (command : app.EnvironmentPolicyCommand) :
    (app.environmentPolicyStep execution command).map PolicyExecution.native =
      match command.toAction with
      | none => FinDist.pure execution.native
      | some action => app.step execution.native action := by
  cases hcommand : command.toAction <;>
    simp [environmentPolicyStep, advance, hcommand, FinDist.map_bind]

theorem playerStep_other_history [DecidableEq Principal]
    (who other : Principal) (hne : other ≠ who)
    (execution : app.PolicyExecution) (command : app.PlayerCommand)
    (next : app.PolicyExecution)
    (hnext : next ∈ (app.playerStep who execution command).support) :
    next.principalHistory other = execution.principalHistory other := by
  simp only [playerStep, FinDist.support_bind, Set.mem_iUnion] at hnext
  rcases hnext with ⟨advanced, _, hnext⟩
  simp only [FinDist.mem_support_pure] at hnext
  subst next
  simp [hne]

theorem environmentStep_principalHistory [DecidableEq Principal]
    (execution : app.PolicyExecution) (command : app.EnvironmentPolicyCommand)
    (next : app.PolicyExecution)
    (hnext : next ∈ (app.environmentPolicyStep execution command).support) :
    next.principalHistory = execution.principalHistory := by
  simp only [environmentPolicyStep, FinDist.support_bind, Set.mem_iUnion] at hnext
  rcases hnext with ⟨advanced, _, hnext⟩
  simp only [FinDist.mem_support_pure] at hnext
  subst next
  rfl

/-- Waiting records the invocation and sampled view but performs no native
action and leaves the proof-facing action trace unchanged. -/
theorem playerStep_wait [DecidableEq Principal] (who : Principal)
    (execution : app.PolicyExecution) :
    app.playerStep who execution .wait = FinDist.pure
      { execution with
        principalHistory := fun other =>
          if other = who then execution.principalHistory who ++
            [⟨State.observe app execution.native who, .wait⟩]
          else execution.principalHistory other } := by
  simp [playerStep, advance, PlayerCommand.toAction]

theorem environmentStep_wait [DecidableEq Principal]
    (execution : app.PolicyExecution) :
    app.environmentPolicyStep execution .wait = FinDist.pure
      { execution with
        environmentHistory := execution.environmentHistory ++
          [⟨State.environmentView app execution.native, .wait⟩] } := by
  simp [environmentPolicyStep, advance, EnvironmentPolicyCommand.toAction]

end Interaction.MessageApplication
