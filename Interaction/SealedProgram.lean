/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.IdealCommitments
import Interaction.MessagePool

/-! # Finite sealed-message programs

This module is a small runtime-general application kernel for finite programs
whose nodes accept commitments, public openings, or neither. Private sealing
and opening checks use a privileged ideal service; its table and verifier are
specification operations, not public runtime queries. Raw owner and sender
arguments are control labels, so authentication requires a separate
principal-scoped policy interface. The public view
contains the message-pool view and accepted application events, but never the
service table or unopened values.

Inclusion has no liveness, timeout, or forced-opening guarantee. Cleartext and
malformed messages may enter the public ledger, but the application rejects
them.
-/

namespace Interaction

universe uPrincipal uValue

inductive SealedRuleKind (Principal : Type uPrincipal) where
  | commit (owner : Principal)
  | reveal (owner : Principal) (sourceCommitNode : Nat)
  | disabled

structure SealedRule (Principal : Type uPrincipal) where
  kind : SealedRuleKind Principal
  requires : List Nat

structure SealedProgram (Principal : Type uPrincipal) where
  rules : List (SealedRule Principal)

namespace SealedProgram

variable {Principal : Type uPrincipal} {Value : Type uValue}

inductive Payload (Principal : Type uPrincipal) (Value : Type uValue) where
  | commitment (node : Nat) (handle : CommitmentHandle Principal Nat)
  | opening (node : Nat) (handle : CommitmentHandle Principal Nat) (claimed : Value)
  | cleartext (node : Nat) (value : Value)
  | malformed

inductive Event (Principal : Type uPrincipal) (Value : Type uValue) where
  | accepted (node : Nat) (handle : CommitmentHandle Principal Nat)
  | opened (node : Nat) (value : Value)

namespace Event

def node : Event Principal Value → Nat
  | .accepted node _ => node
  | .opened node _ => node

end Event

structure State (Principal : Type uPrincipal) (Value : Type uValue) where
  service : IdealCommitments Principal Nat Value
  pool : MessagePool Principal (Payload Principal Value)
  events : List (Event Principal Value)

structure View (Principal : Type uPrincipal) (Value : Type uValue) where
  messages : MessagePool.View Principal (Payload Principal Value)
  events : List (Event Principal Value)

def State.empty (Principal : Type uPrincipal) (Value : Type uValue) :
    State Principal Value where
  service := IdealCommitments.empty
  pool := MessagePool.empty Principal (Payload Principal Value)
  events := []

def done (events : List (Event Principal Value)) (node : Nat) : Bool :=
  events.any fun event => event.node == node

def accepted? (events : List (Event Principal Value)) (node : Nat) :
    Option (CommitmentHandle Principal Nat) :=
  events.findSome? fun event =>
    match event with
    | .accepted eventNode handle => if eventNode = node then some handle else none
    | .opened _ _ => none

def State.observe (state : State Principal Value) (who : Principal) :
    View Principal Value :=
  ⟨state.pool.observe who, state.events⟩

def prerequisitesDone (events : List (Event Principal Value))
    (rule : SealedRule Principal) : Bool :=
  rule.requires.all (done events)

/-- Seal privately, then submit only the owner-scoped opaque handle. A repeat
submission is still admitted to the message pool; the ideal table retains the
first registered value. -/
def submitCommit [DecidableEq Principal] (state : State Principal Value)
    (owner : Principal) (node : Nat) (value : Value) :
    MessageId Principal × State Principal Value :=
  let sealed := state.service.sealValue owner node value
  let submitted := state.pool.submit owner (.commitment node (owner, node))
  (submitted.1, { state with service := sealed.state, pool := submitted.2 })

/-- Return the accepted handle when the public event log says an owner's reveal
node is ready. This query is independent of the claimed value and does not
inspect the ideal service table. -/
def openingHandle? [DecidableEq Principal] (program : SealedProgram Principal)
    (events : List (Event Principal Value)) (owner : Principal) (revealNode : Nat) :
    Option (CommitmentHandle Principal Nat) :=
  match program.rules[revealNode]? with
  | some rule =>
      match rule.kind with
      | .reveal expectedOwner source =>
          if owner = expectedOwner ∧ done events revealNode = false ∧
              prerequisitesDone events rule = true ∧
              accepted? events source = some (owner, source) then
            some (owner, source)
          else none
      | _ => none
  | none => none

/-- Whether the public event log makes an owner's reveal node ready. -/
def openingReady [DecidableEq Principal] (program : SealedProgram Principal)
    (events : List (Event Principal Value)) (owner : Principal) (revealNode : Nat) : Bool :=
  (openingHandle? program events owner revealNode).isSome

/-- Construct an owner's public opening payload from value-independent public
readiness. -/
def openingRequest? [DecidableEq Principal] (program : SealedProgram Principal)
    (events : List (Event Principal Value)) (owner : Principal) (revealNode : Nat)
    (claimed : Value) : Option (Payload Principal Value) :=
  (openingHandle? program events owner revealNode).map fun handle =>
    .opening revealNode handle claimed

def submitOpening? [DecidableEq Principal] (program : SealedProgram Principal)
    (state : State Principal Value) (owner : Principal) (revealNode : Nat)
    (claimed : Value) : Option (MessageId Principal × State Principal Value) :=
  (openingRequest? program state.events owner revealNode claimed).map fun payload =>
    let submitted := state.pool.submit owner payload
    (submitted.1, { state with pool := submitted.2 })

/-- Validate one application message using only the ideal service and public
application events. Message-pool ownership and inclusion are deliberately
outside this kernel. -/
def validateMessage? [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (service : IdealCommitments Principal Nat Value)
    (events : List (Event Principal Value))
    (message : Message Principal (Payload Principal Value)) : Option (Event Principal Value) :=
  match message.payload with
  | .commitment node handle =>
      match program.rules[node]? with
      | some rule =>
          match rule.kind with
          | .commit owner =>
              if message.sender = owner ∧ handle = (owner, node) ∧
                  done events node = false ∧ prerequisitesDone events rule = true ∧
                  (service.lookup handle).isSome = true then
                some (.accepted node handle)
              else none
          | _ => none
      | none => none
  | .opening node handle claimed =>
      match program.rules[node]? with
      | some rule =>
          match rule.kind with
          | .reveal owner source =>
              if message.sender = owner ∧ handle = (owner, source) ∧
                  done events node = false ∧ prerequisitesDone events rule = true ∧
                  accepted? events source = some handle ∧
                  service.verify ⟨handle, claimed⟩ = true then
                some (.opened node claimed)
              else none
          | _ => none
      | none => none
  | .cleartext _ _ => none
  | .malformed => none

def handle [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (state : State Principal Value)
    (message : Message Principal (Payload Principal Value)) : State Principal Value :=
  match validateMessage? program state.service state.events message with
  | some event => { state with events := state.events ++ [event] }
  | none => state

theorem handle_eq_of_validateMessage?_eq_some [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (state : State Principal Value)
    (message : Message Principal (Payload Principal Value)) (event : Event Principal Value)
    (hvalid : validateMessage? program state.service state.events message = some event) :
    handle program state message = { state with events := state.events ++ [event] } := by
  simp [handle, hvalid]

/-- Include a pending message in the public ledger, then apply the pure
application handler to the included preexisting message. Rejected application
messages remain visible in the ledger. -/
def includePending [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (state : State Principal Value)
    (id : MessageId Principal) : State Principal Value :=
  let included := state.pool.includePending id
  let includedState := { state with pool := included.state }
  match included.message with
  | some message => handle program includedState message
  | none => includedState

@[simp] theorem done_nil (node : Nat) :
    done ([] : List (Event Principal Value)) node = false := rfl

@[simp] theorem accepted?_nil (node : Nat) :
    accepted? ([] : List (Event Principal Value)) node = none := rfl

@[simp] theorem State.observe_events (state : State Principal Value) (who : Principal) :
    (state.observe who).events = state.events := rfl

@[simp] theorem handle_cleartext [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (state : State Principal Value)
    (message : Message Principal (Payload Principal Value)) (node : Nat) (value : Value)
    (hpayload : message.payload = .cleartext node value) :
    handle program state message = state := by
  simp [handle, validateMessage?, hpayload]

@[simp] theorem handle_malformed [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (state : State Principal Value)
    (message : Message Principal (Payload Principal Value))
    (hpayload : message.payload = .malformed) :
    handle program state message = state := by
  simp [handle, validateMessage?, hpayload]

end SealedProgram

end Interaction
