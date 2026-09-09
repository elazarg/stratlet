/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.TransactionalInclusion
import GameTheory.Math.Probability.FinDist

/-! # Applications over public message interaction

The application supplies its own state, raw payloads, principal-local commands,
environment commands, and observation projections. Inclusion is atomic and
records public acceptance/rejection receipts. Private commands and environment
commands cannot modify the message pool or its receipts.

An environment command invokes a fixed application kernel: it can trigger a
chance transition without selecting its sampled value. The application must
enforce readiness and prevent rerolling where required. This interface supplies
neither that invariant nor a service guarantee. It adds no clock or automatic
timeout; those belong to the selected application/environment instance.
-/

namespace Interaction

open GameTheory.Math.Probability

universe uPrincipal u

/-- Application code and the projections exposed by its message runtime.
The private transition's principal is supplied by the runtime capability, not
by the private command. Raw actions alone are not authenticated policies. -/
structure MessageApplication (Principal : Type uPrincipal) where
  Application : Type u
  Payload : Type u
  PrivateCommand : Type u
  EnvironmentCommand : Type u
  PlayerView : Type u
  EnvironmentView : Type u
  privateStep : Application → Principal → PrivateCommand → Application
  environmentStep : Application → EnvironmentCommand → FinDist Application
  handle : Application → Message Principal Payload → Option Application
  observePlayer : Application → Principal → PlayerView
  observeEnvironment : Application → EnvironmentView

namespace MessageApplication

variable {Principal : Type uPrincipal} (app : MessageApplication Principal)

structure State where
  application : app.Application
  pool : MessagePool Principal app.Payload
  receipts : List (MessageId Principal × Bool)

def State.initial (application : app.Application) : app.State :=
  ⟨application, MessagePool.empty Principal app.Payload, []⟩

structure View where
  messages : MessagePool.View Principal app.Payload
  application : app.PlayerView
  receipts : List (MessageId Principal × Bool)

def State.observe (state : app.State) (who : Principal) : app.View :=
  ⟨state.pool.observe who, app.observePlayer state.application who, state.receipts⟩

structure EnvironmentObservation where
  pool : MessagePool Principal app.Payload
  application : app.EnvironmentView
  receipts : List (MessageId Principal × Bool)

def State.environmentView (state : app.State) : app.EnvironmentObservation :=
  ⟨state.pool, app.observeEnvironment state.application, state.receipts⟩

/-- Native actions. The policy interface determines which principal controls
each action; inclusion never invokes the message author's controller. -/
inductive Action where
  | privateCommand (who : Principal) (command : app.PrivateCommand)
  | submit (who : Principal) (payload : app.Payload)
  | replay (who : Principal) (id : MessageId Principal)
  | deliver (who : Principal) (id : MessageId Principal)
  | include (id : MessageId Principal)
  | environment (command : app.EnvironmentCommand)

/-- Publish an existing message and apply the application's transaction. A
missing message produces neither a ledger entry nor an inclusion receipt. -/
def includePending [DecidableEq Principal] (state : app.State)
    (id : MessageId Principal) : app.State :=
  let result := state.pool.includeApplication state.application id app.handle
  ⟨result.application, result.pool,
    match result.receipt with
    | none => state.receipts
    | some accepted => state.receipts ++ [(id, accepted)]⟩

noncomputable section

/-- The native transition law. Application chance and policy randomization
are distinct kernels; both are retained by the policy interpretation. -/
def step [DecidableEq Principal] (state : app.State) : app.Action → FinDist app.State
  | .privateCommand who command =>
      FinDist.pure { state with application := app.privateStep state.application who command }
  | .submit who payload =>
      FinDist.pure { state with pool := (state.pool.submit who payload).2 }
  | .replay who id =>
      FinDist.pure { state with pool := (state.pool.replay who id).state }
  | .deliver who id =>
      FinDist.pure { state with pool := (state.pool.deliver who id).state }
  | .include id => FinDist.pure (app.includePending state id)
  | .environment command =>
      (app.environmentStep state.application command).map
        fun application => { state with application }

/-- The law of a supplied finite native action sequence, without a policy or
an assumed settlement event at the end of the sequence. -/
def run [DecidableEq Principal] : List app.Action → app.State → FinDist app.State
  | [], state => FinDist.pure state
  | action :: rest, state => (app.step state action).bind (run rest)

@[simp] theorem run_nil [DecidableEq Principal] (state : app.State) :
    app.run [] state = FinDist.pure state := rfl

@[simp] theorem run_cons [DecidableEq Principal] (state : app.State)
    (action : app.Action) (rest : List app.Action) :
    app.run (action :: rest) state = (app.step state action).bind (app.run rest) := rfl

theorem run_append [DecidableEq Principal] (state : app.State)
    (first second : List app.Action) :
    app.run (first ++ second) state = (app.run first state).bind (app.run second) := by
  induction first generalizing state with
  | nil => simp
  | cons action rest ih =>
      simp only [List.cons_append, run_cons, FinDist.bind_bind]
      congr 1
      funext next
      exact ih next

end

end MessageApplication
end Interaction
