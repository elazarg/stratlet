/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedTimeout
import GameTheory.Core.Form

/-! # Observation-local policies for the timed sealed application

The bounded game uses the actual timed runner. Player policies retain their
own polling views and commands, including failed calls and waits. The
environment sees wire traffic, receipts, the public clock and resolution, but
not the ideal commitment table. It controls clock advances, delivery and
inclusion. A fixed finite polling schedule is an analysis parameter, not a
settlement guarantee or an observed global counter. No policy is supplied with
the testing horizon or another principal's private invocation memory.
-/

noncomputable section

namespace Interaction.SealedTimeout

open GameTheory GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

inductive PlayerCommand (Principal : Type uPrincipal) (Value : Type uValue) where
  | register (slot : Nat) (value : Value)
  | submit (payload : Payload Principal Value)
  | replay (id : MessageId Principal)
  | wait

structure PlayerEntry (Principal : Type uPrincipal) (Value : Type uValue) where
  beforeView : View Principal Value
  command : PlayerCommand Principal Value

abbrev PlayerPolicy (Principal : Type uPrincipal) (Value : Type uValue) :=
  List (PlayerEntry Principal Value) → View Principal Value →
    FinDist (PlayerCommand Principal Value)

inductive EnvironmentCommand (Principal : Type uPrincipal) where
  | deliver (observer : Principal) (id : MessageId Principal)
  | include (id : MessageId Principal)
  | advance (clock : Nat)
  | wait

structure EnvironmentEntry (Principal : Type uPrincipal) (Value : Type uValue) where
  beforeView : EnvironmentView Principal Value
  command : EnvironmentCommand Principal

abbrev EnvironmentPolicy (Principal : Type uPrincipal) (Value : Type uValue) :=
  List (EnvironmentEntry Principal Value) → EnvironmentView Principal Value →
    FinDist (EnvironmentCommand Principal)

inductive Invocation (Principal : Type uPrincipal) where
  | player (who : Principal)
  | environment

structure PolicyExecution (Principal : Type uPrincipal) (Value : Type uValue) where
  native : State Principal Value
  principalHistory : Principal → List (PlayerEntry Principal Value)
  environmentHistory : List (EnvironmentEntry Principal Value)
  nativeTrace : List (Action Principal Value)

def PolicyExecution.initial (state : State Principal Value) : PolicyExecution Principal Value :=
  ⟨state, fun _ => [], [], []⟩

def PlayerCommand.toAction (who : Principal) :
    PlayerCommand Principal Value → Option (Action Principal Value)
  | .register slot value => some (.register who slot value)
  | .submit payload => some (.submit who payload)
  | .replay id => some (.replay who id)
  | .wait => none

def EnvironmentCommand.toAction : EnvironmentCommand Principal → Option (Action Principal Value)
  | .deliver observer id => some (.deliver observer id)
  | .include id => some (.include id)
  | .advance clock => some (.advance clock)
  | .wait => none

def applyNative [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (execution : PolicyExecution Principal Value)
    (action : Option (Action Principal Value)) :
    State Principal Value × List (Action Principal Value) :=
  match action with
  | none => (execution.native, execution.nativeTrace)
  | some action => (timed.step execution.native action, execution.nativeTrace ++ [action])

def playerStep [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (who : Principal)
    (execution : PolicyExecution Principal Value) (command : PlayerCommand Principal Value) :
    PolicyExecution Principal Value :=
  let view := execution.native.observe who
  let advanced := applyNative timed execution (command.toAction who)
  { execution with
    native := advanced.1
    principalHistory := fun other =>
      if other = who then execution.principalHistory who ++ [⟨view, command⟩]
      else execution.principalHistory other
    nativeTrace := advanced.2 }

def environmentStep [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal)
    (execution : PolicyExecution Principal Value) (command : EnvironmentCommand Principal) :
    PolicyExecution Principal Value :=
  let view := execution.native.environmentView
  let advanced := applyNative timed execution command.toAction
  { execution with
    native := advanced.1
    environmentHistory := execution.environmentHistory ++ [⟨view, command⟩]
    nativeTrace := advanced.2 }

def invoke [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal)
    (players : Principal → PlayerPolicy Principal Value)
    (environment : EnvironmentPolicy Principal Value)
    (execution : PolicyExecution Principal Value) :
    Invocation Principal → FinDist (PolicyExecution Principal Value)
  | .player who =>
      (players who (execution.principalHistory who) (execution.native.observe who)).map
        fun command => playerStep timed who execution command
  | .environment =>
      (environment execution.environmentHistory execution.native.environmentView).map
        fun command => environmentStep timed execution command

def runPolicies [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal)
    (players : Principal → PlayerPolicy Principal Value)
    (environment : EnvironmentPolicy Principal Value) :
    List (Invocation Principal) → PolicyExecution Principal Value →
      FinDist (PolicyExecution Principal Value)
  | [], execution => FinDist.pure execution
  | invocation :: rest, execution =>
      (invoke timed players environment execution invocation).bind
        (runPolicies timed players environment rest)

def policySignature (Principal : Type uPrincipal) (Value : Type uValue) :
    GameSignature Principal where
  Strategy := fun _ => PlayerPolicy Principal Value
  Outcome := PolicyExecution Principal Value

def policyGame [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (environment : EnvironmentPolicy Principal Value)
    (schedule : List (Invocation Principal)) (initial : State Principal Value) :
    GameForm Principal where
  sig := policySignature Principal Value
  play players := runPolicies timed players environment schedule (PolicyExecution.initial initial)

end Interaction.SealedTimeout
