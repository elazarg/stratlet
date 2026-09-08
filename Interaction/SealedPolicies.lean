/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedExecution
import GameTheory.Core.Form

/-!
# Observation-local policies for the native sealed-message runtime

Execution follows a fixed finite invocation list. A principal policy sees its
current native view and only its own sampled pre-action views and raw commands;
that memory records waits and rejected operations as well as state-changing
commands. The environment sees the complete message pool (including every
inbox, sent list, and next serial) and public application events, but not the
ideal commitment service. `nativeTrace` records actual non-wait native actions
for proofs and is not supplied to either policy.
-/

noncomputable section

namespace Interaction.SealedProgram

open GameTheory GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

inductive PlayerCommand (Principal : Type uPrincipal) (Value : Type uValue) where
  | register (slot : Nat) (value : Value)
  | submit (payload : Payload Principal Value)
  | replay (id : MessageId Principal)
  | wait

def PlayerCommand.allowed {Principal : Type uPrincipal} {Value : Type uValue}
    (rebroadcast : Bool) : PlayerCommand Principal Value → Prop
  | .replay _ => rebroadcast = true
  | _ => True

structure PlayerEntry (Principal : Type uPrincipal) (Value : Type uValue) where
  beforeView : View Principal Value
  command : PlayerCommand Principal Value

abbrev PlayerPolicy (Principal : Type uPrincipal) (Value : Type uValue)
    (rebroadcast : Bool) :=
  List (PlayerEntry Principal Value) → View Principal Value →
    FinDist { command : PlayerCommand Principal Value // command.allowed rebroadcast }

inductive EnvironmentCommand (Principal : Type uPrincipal) where
  | deliver (observer : Principal) (id : MessageId Principal)
  | include (id : MessageId Principal)
  | wait

structure EnvironmentView (Principal : Type uPrincipal) (Value : Type uValue) where
  pool : MessagePool Principal (Payload Principal Value)
  events : List (Event Principal Value)

def State.environmentView (state : State Principal Value) :
    EnvironmentView Principal Value :=
  ⟨state.pool, state.events⟩

structure EnvironmentEntry (Principal : Type uPrincipal) (Value : Type uValue) where
  beforeView : EnvironmentView Principal Value
  command : EnvironmentCommand Principal

abbrev EnvironmentPolicy (Principal : Type uPrincipal) (Value : Type uValue) :=
  List (EnvironmentEntry Principal Value) → EnvironmentView Principal Value →
    FinDist (EnvironmentCommand Principal)

inductive Invocation (Principal : Type uPrincipal) where
  | player (who : Principal)
  | environment

/-- A bounded execution prefix. `nativeTrace` is proof-facing bookkeeping and is
not included in either policy's view. -/
structure PolicyExecution (Principal : Type uPrincipal) (Value : Type uValue) where
  native : State Principal Value
  principalHistory : Principal → List (PlayerEntry Principal Value)
  environmentHistory : List (EnvironmentEntry Principal Value)
  nativeTrace : List (Action Principal Value)

def PolicyExecution.initial (state : State Principal Value) :
    PolicyExecution Principal Value where
  native := state
  principalHistory := fun _ => []
  environmentHistory := []
  nativeTrace := []

def PlayerCommand.toAction (who : Principal) :
    PlayerCommand Principal Value → Option (Action Principal Value)
  | .register slot value => some (.register who slot value)
  | .submit payload => some (.submit who payload)
  | .replay id => some (.replay who id)
  | .wait => none

def EnvironmentCommand.toAction :
    EnvironmentCommand Principal → Option (Action Principal Value)
  | .deliver observer id => some (.deliver observer id)
  | .include id => some (.include id)
  | .wait => none

def applyNative [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (execution : PolicyExecution Principal Value)
    (action : Option (Action Principal Value)) :
    State Principal Value × List (Action Principal Value) :=
  match action with
  | none => (execution.native, execution.nativeTrace)
  | some action => (step program execution.native action, execution.nativeTrace ++ [action])

def playerStep [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (who : Principal)
    (execution : PolicyExecution Principal Value) (command : PlayerCommand Principal Value) :
    PolicyExecution Principal Value :=
  let view := execution.native.observe who
  let advanced := applyNative program execution (command.toAction who)
  { execution with
    native := advanced.1
    principalHistory := fun other =>
      if other = who then execution.principalHistory who ++ [⟨view, command⟩]
      else execution.principalHistory other
    nativeTrace := advanced.2 }

def environmentStep [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (execution : PolicyExecution Principal Value)
    (command : EnvironmentCommand Principal) : PolicyExecution Principal Value :=
  let view := execution.native.environmentView
  let advanced := applyNative program execution command.toAction
  { execution with
    native := advanced.1
    environmentHistory := execution.environmentHistory ++ [⟨view, command⟩]
    nativeTrace := advanced.2 }

def invoke [DecidableEq Principal] [DecidableEq Value] (rebroadcast : Bool)
    (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value)
    (execution : PolicyExecution Principal Value) :
    Invocation Principal → FinDist (PolicyExecution Principal Value)
  | .player who =>
      (players who (execution.principalHistory who) (execution.native.observe who)).map
        fun command => playerStep program who execution command.1
  | .environment =>
      (environment execution.environmentHistory execution.native.environmentView).map
        fun command => environmentStep program execution command

def runPolicies [DecidableEq Principal] [DecidableEq Value] (rebroadcast : Bool)
    (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value) :
    List (Invocation Principal) → PolicyExecution Principal Value →
      FinDist (PolicyExecution Principal Value)
  | [], execution => FinDist.pure execution
  | invocation :: rest, execution =>
      (invoke rebroadcast program players environment execution invocation).bind
        (runPolicies rebroadcast program players environment rest)

/-- Policy and prefix-outcome carriers, independent of application and
environment choices. This signature owns canonical profile operations. -/
def policySignature (Principal : Type uPrincipal) (Value : Type uValue)
    (rebroadcast : Bool) : GameSignature Principal where
  Strategy := fun _ => PlayerPolicy Principal Value rebroadcast
  Outcome := PolicyExecution Principal Value

def policyGame [DecidableEq Principal] [DecidableEq Value] (rebroadcast : Bool)
    (program : SealedProgram Principal) (environment : EnvironmentPolicy Principal Value)
    (schedule : List (Invocation Principal)) (initial : State Principal Value) :
    GameForm Principal where
  sig := policySignature Principal Value rebroadcast
  play players := runPolicies rebroadcast program players environment schedule
    (PolicyExecution.initial initial)

end Interaction.SealedProgram
