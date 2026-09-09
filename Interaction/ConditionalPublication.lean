/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.IdealCommitments
import Interaction.MessagePool

/-! # Conditional publication kernel

This module classifies one source-authorized publication decision.  It is an
injectable application handler, not a runner, game, commitment implementation,
or strategic correspondence theorem.  Callers establish that the accepted
handle came from the preceding native commitment.  The application supplies
`canOpen` from its current state; the compiler edge must relate that predicate
to the source guard.  Ideal verification alone does not enforce program guards.
-/

namespace Interaction

universe uPrincipal uValue

structure ConditionalPublication (Principal : Type uPrincipal) where
  owner : Principal
  sourceSlot : Nat
  choiceNode : Nat
  publicationNode : Nat
  requires : List Nat
  deadline : Nat

namespace ConditionalPublication

variable {Principal : Type uPrincipal} {Value : Type uValue}

inductive Payload (Principal : Type uPrincipal) (Value : Type uValue) where
  | opening (handle : CommitmentHandle Principal Nat) (claimed : Value)
  | decline
  | expire
  | cleartext (value : Value)
  | malformed

/-- Canonical owner request for one application-level resolution result. -/
def requestPayload (site : ConditionalPublication Principal) :
    Option Value → Payload Principal Value
  | none => .decline
  | some value => .opening (site.owner, site.sourceSlot) value

def ready [DecidableEq Principal] (site : ConditionalPublication Principal)
    (accepted : Option (CommitmentHandle Principal Nat))
    (done : Nat → Bool) : Bool :=
  accepted == some (site.owner, site.sourceSlot) &&
    !done site.choiceNode && !done site.publicationNode &&
    site.requires.all done

def resolve? [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat)
    (service : IdealCommitments Principal Nat Value)
    (accepted : Option (CommitmentHandle Principal Nat))
    (done : Nat → Bool)
    (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value)) : Option (Option Value) :=
  if !site.ready accepted done then none else
  match message.payload with
  | .opening handle claimed =>
      if message.sender = site.owner ∧ handle = (site.owner, site.sourceSlot) ∧
          service.verify ⟨handle, claimed⟩ ∧ canOpen claimed then
        some (some claimed)
      else none
  | .decline => if message.sender = site.owner then some none else none
  | .expire => if site.deadline < now then some none else none
  | .cleartext _ | .malformed => none

theorem resolve_opening [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat)
    (service : IdealCommitments Principal Nat Value)
    (accepted : Option (CommitmentHandle Principal Nat)) (done : Nat → Bool)
    (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value))
    (handle : CommitmentHandle Principal Nat) (claimed : Value)
    (hpayload : message.payload = .opening handle claimed) :
    site.resolve? now service accepted done canOpen message = some (some claimed) ↔
      site.ready accepted done = true ∧ message.sender = site.owner ∧
      handle = (site.owner, site.sourceSlot) ∧ service.verify ⟨handle, claimed⟩ = true ∧
      canOpen claimed = true := by
  simp [resolve?, hpayload]

theorem resolve_decline [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat)
    (service : IdealCommitments Principal Nat Value)
    (accepted : Option (CommitmentHandle Principal Nat)) (done : Nat → Bool)
    (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value))
    (hpayload : message.payload = .decline) :
    site.resolve? now service accepted done canOpen message = some none ↔
      site.ready accepted done = true ∧ message.sender = site.owner := by
  simp [resolve?, hpayload]

/-- At a ready site, the canonical owner-authored request always accepts a
decline; an opening accepts exactly when the stored-value and application-guard
checks both succeed. -/
theorem resolve_requestPayload [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat)
    (service : IdealCommitments Principal Nat Value)
    (accepted : Option (CommitmentHandle Principal Nat)) (done : Nat → Bool)
    (canOpen : Value → Bool)
    (hready : site.ready accepted done = true) (serial : Nat) (result : Option Value) :
    site.resolve? now service accepted done canOpen
        ⟨(site.owner, serial), site.requestPayload result⟩ = some result ↔
      match result with
      | none => True
      | some value =>
          service.verify ⟨(site.owner, site.sourceSlot), value⟩ = true ∧
            canOpen value = true := by
  cases result <;> simp [resolve?, requestPayload, hready, Message.sender]

theorem resolve_expire [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat)
    (service : IdealCommitments Principal Nat Value)
    (accepted : Option (CommitmentHandle Principal Nat)) (done : Nat → Bool)
    (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value))
    (hpayload : message.payload = .expire) :
    site.resolve? now service accepted done canOpen message = some none ↔
      site.ready accepted done = true ∧ site.deadline < now := by
  simp [resolve?, hpayload]

theorem resolve_opening_wrong_handle [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat)
    (service : IdealCommitments Principal Nat Value)
    (accepted : Option (CommitmentHandle Principal Nat)) (done : Nat → Bool)
    (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value))
    (handle : CommitmentHandle Principal Nat) (claimed : Value)
    (hpayload : message.payload = .opening handle claimed)
    (hwrong : handle ≠ (site.owner, site.sourceSlot)) :
    site.resolve? now service accepted done canOpen message = none := by
  simp [resolve?, hpayload, hwrong]

theorem resolve_opening_when_closed [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat)
    (service : IdealCommitments Principal Nat Value)
    (accepted : Option (CommitmentHandle Principal Nat)) (done : Nat → Bool)
    (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value))
    (handle : CommitmentHandle Principal Nat) (claimed : Value)
    (hpayload : message.payload = .opening handle claimed)
    (hclosed : canOpen claimed = false) :
    site.resolve? now service accepted done canOpen message = none := by
  simp [resolve?, hpayload, hclosed]

theorem resolve_success_inversion [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat)
    (service : IdealCommitments Principal Nat Value)
    (accepted : Option (CommitmentHandle Principal Nat)) (done : Nat → Bool)
    (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value)) (result : Option Value)
    (hresolve : site.resolve? now service accepted done canOpen message = some result) :
    site.ready accepted done = true := by
  cases hready : site.ready accepted done <;>
    simp [resolve?, hready] at hresolve ⊢

/-- Publishing a value witnesses the application-supplied opening predicate.
This fact is deliberately separate from commitment verification: callers must
relate `canOpen` to the source program's guard. -/
theorem resolve_some_canOpen [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat)
    (service : IdealCommitments Principal Nat Value)
    (accepted : Option (CommitmentHandle Principal Nat)) (done : Nat → Bool)
    (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value)) (value : Value)
    (hresolve : site.resolve? now service accepted done canOpen message = some (some value)) :
    canOpen value = true := by
  cases hpayload : message.payload with
  | opening handle claimed =>
      simp only [resolve?, hpayload] at hresolve
      split at hresolve <;> try contradiction
      split at hresolve <;> try contradiction
      rename_i hopen
      cases hresolve
      exact hopen.2.2.2
  | decline => simp [resolve?, hpayload] at hresolve
  | expire => simp [resolve?, hpayload] at hresolve
  | cleartext clear => simp [resolve?, hpayload] at hresolve
  | malformed => simp [resolve?, hpayload] at hresolve

/-- A published value has an opening in the supplied ideal verifier. This
does not assume that a valid opening existed when the handle was accepted. -/
theorem resolve_some_lookup [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat)
    (service : IdealCommitments Principal Nat Value)
    (accepted : Option (CommitmentHandle Principal Nat)) (done : Nat → Bool)
    (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value)) (value : Value)
    (hresolve : site.resolve? now service accepted done canOpen message = some (some value)) :
    service.lookup (site.owner, site.sourceSlot) = some value := by
  cases hpayload : message.payload with
  | opening handle claimed =>
      simp only [resolve?, hpayload] at hresolve
      split at hresolve <;> try contradiction
      split at hresolve <;> try contradiction
      rename_i hopen
      cases hresolve
      exact hopen.2.1 ▸ (IdealCommitments.verify_eq_true_iff service ⟨handle, value⟩).mp
        hopen.2.2.1
  | decline => simp [resolve?, hpayload] at hresolve
  | expire => simp [resolve?, hpayload] at hresolve
  | cleartext clear => simp [resolve?, hpayload] at hresolve
  | malformed => simp [resolve?, hpayload] at hresolve

/-- A successful resolution either publishes the explicit decline code or the
value already stored at the site's canonical owner-scoped handle. -/
theorem resolve_value [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat)
    (service : IdealCommitments Principal Nat Value)
    (accepted : Option (CommitmentHandle Principal Nat)) (done : Nat → Bool)
    (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value))
    (stored : Value)
    (hstored : service.lookup (site.owner, site.sourceSlot) = some stored)
    (result : Option Value)
    (hresolve : site.resolve? now service accepted done canOpen message = some result) :
    result = none ∨ result = some stored := by
  cases result with
  | none => exact Or.inl rfl
  | some resultValue =>
    right
    cases hpayload : message.payload with
    | opening handle claimed =>
        simp only [resolve?, hpayload] at hresolve
        split at hresolve <;> try contradiction
        split at hresolve <;> try contradiction
        rename_i hopen
        cases hresolve
        rcases hopen with ⟨_, hhandle, hverify⟩
        subst handle
        symm
        simpa [IdealCommitments.verify, hstored] using hverify.1
    | decline => simp [resolve?, hpayload] at hresolve
    | expire => simp [resolve?, hpayload] at hresolve
    | cleartext value => simp [resolve?, hpayload] at hresolve
    | malformed => simp [resolve?, hpayload] at hresolve

end ConditionalPublication

end Interaction
