/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.Deadline
import Interaction.SealedProgram
import Interaction.TransactionalInclusion

/-! # A timed disclosure checkpoint in the native sealed application

This instance adds one immutable deadline and a permissionless expiration call
to an existing sealed program. Expiration is enabled only when that program's
public opening-readiness check passes. A successful expiration disables later
protocol-event acceptance, retaining existing commitments and public events.
It does not freeze the ideal service: new registrations remain possible, as do
wire publication, replay, delivery, inclusion attempts, and clock advancement.
This is an explicit final-failure disposition, not a source value, a refund,
or persistent role-specific abandonment with continuing application actions.

Opening remains possible after the deadline until expiration is included.
Both calls use the same message pool; ordinary traffic uses the untimed
application's actual validator. A public monotone clock is supplied by the
environment. Its advancement neither expires an obligation nor includes a call.
Completion resolves the monitored opening checkpoint; it does not terminate
the whole sealed program or prevent later protocol events.
No progress, fees, concrete authentication, or cryptographic realization is
assumed. Principal-scoped policies supply the raw author labels.
-/

namespace Interaction

universe uPrincipal uValue

structure SealedTimeout (Principal : Type uPrincipal) where
  program : SealedProgram Principal
  openingNode : Nat
  deadline : Nat

namespace SealedTimeout

variable {Principal : Type uPrincipal} {Value : Type uValue}

inductive Payload (Principal : Type uPrincipal) (Value : Type uValue) where
  | protocol (payload : SealedProgram.Payload Principal Value)
  | expire

structure Application (Principal : Type uPrincipal) (Value : Type uValue) where
  service : IdealCommitments Principal Nat Value
  events : List (SealedProgram.Event Principal Value)
  resolution : DeadlineResolution

structure State (Principal : Type uPrincipal) (Value : Type uValue) where
  application : Application Principal Value
  pool : MessagePool Principal (Payload Principal Value)
  clock : Nat
  receipts : List (MessageId Principal × Bool)

def State.empty (Principal : Type uPrincipal) (Value : Type uValue) :
    State Principal Value :=
  ⟨⟨IdealCommitments.empty, [], .pending⟩,
    MessagePool.empty Principal (Payload Principal Value), 0, []⟩

structure View (Principal : Type uPrincipal) (Value : Type uValue) where
  messages : MessagePool.View Principal (Payload Principal Value)
  events : List (SealedProgram.Event Principal Value)
  resolution : DeadlineResolution
  clock : Nat
  receipts : List (MessageId Principal × Bool)

def State.observe (state : State Principal Value) (who : Principal) : View Principal Value :=
  ⟨state.pool.observe who, state.application.events, state.application.resolution,
    state.clock, state.receipts⟩

/-- The checkpoint is ready according to the original program's public rule
and accepted commitment, without inspecting the service's hidden value. -/
def ready [DecidableEq Principal] (timed : SealedTimeout Principal)
    (events : List (SealedProgram.Event Principal Value)) : Bool :=
  match timed.program.rules[timed.openingNode]? with
  | some ⟨.reveal owner _, _⟩ =>
      timed.program.openingReady events owner timed.openingNode
  | _ => false

/-- The handler stages only application effects. Publication and receipt
recording are supplied by the enclosing atomic inclusion operation. -/
def handle [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (now : Nat)
    (application : Application Principal Value)
    (message : Message Principal (Payload Principal Value)) :
    Option (Application Principal Value) :=
  match message.payload with
  | .protocol payload =>
      if application.resolution = .expired then none else do
        let event ← SealedProgram.validateMessage? timed.program application.service
          application.events ⟨message.id, payload⟩
        let resolution := match event with
          | .opened node _ =>
              if node = timed.openingNode then .completed else application.resolution
          | _ => application.resolution
        some { application with events := application.events ++ [event], resolution }
  | .expire =>
      if timed.ready application.events then
        match Deadline.expire now ⟨timed.deadline, application.resolution⟩ with
        | some result => some { application with resolution := result.resolution }
        | none => none
      else none

def includePending [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (state : State Principal Value)
    (id : MessageId Principal) : State Principal Value :=
  let included := state.pool.includeApplication state.application id (timed.handle state.clock)
  { application := included.application
    pool := included.pool
    clock := state.clock
    receipts := match included.receipt with
      | none => state.receipts
      | some accepted => state.receipts ++ [(id, accepted)] }

inductive Action (Principal : Type uPrincipal) (Value : Type uValue) where
  | register (owner : Principal) (slot : Nat) (value : Value)
  | submit (author : Principal) (payload : Payload Principal Value)
  | replay (broadcaster : Principal) (id : MessageId Principal)
  | deliver (observer : Principal) (id : MessageId Principal)
  | include (id : MessageId Principal)
  | advance (clock : Nat)

/-- Native execution; raw action labels are not authenticated capabilities. -/
def step [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (state : State Principal Value) :
    Action Principal Value → State Principal Value
  | .register owner slot value =>
      { state with application.service :=
          (state.application.service.sealValue owner slot value).state }
  | .submit author payload => { state with pool := (state.pool.submit author payload).2 }
  | .replay broadcaster id => { state with pool := (state.pool.replay broadcaster id).state }
  | .deliver observer id => { state with pool := (state.pool.deliver observer id).state }
  | .include id => timed.includePending state id
  | .advance clock => if state.clock ≤ clock then { state with clock } else state

def run [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (state : State Principal Value)
    (actions : List (Action Principal Value)) : State Principal Value :=
  actions.foldl timed.step state

@[simp] theorem run_nil [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (state : State Principal Value) :
    timed.run state [] = state := rfl

@[simp] theorem run_cons [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (state : State Principal Value)
    (action : Action Principal Value) (rest : List (Action Principal Value)) :
    timed.run state (action :: rest) = timed.run (timed.step state action) rest := rfl

theorem run_append [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (state : State Principal Value)
    (first second : List (Action Principal Value)) :
    timed.run state (first ++ second) = timed.run (timed.run state first) second :=
  List.foldl_append

end SealedTimeout

end Interaction
