/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.ChoiceEncodingRouting
import Interaction.ConditionalPublication

/-! # Addressed conditional-publication requests

The binding handle identifies the sealed resource; the publication-node tag
identifies this use of that resource. Voluntary choices and permissionless
expiration have distinct encodings, even when both resolve to decline.
-/

namespace Interaction.ConditionalPublication

open MessageApplication

universe uPrincipal uValue

variable {Principal : Type uPrincipal} [DecidableEq Principal] {Value : Type uValue}

/-- Encode only voluntary owner choices. Expiration and malformed traffic are
not records of a sampled source choice. -/
def choiceEncoding (site : ConditionalPublication Principal) :
    ChoiceEncoding (Option Value) (Payload Principal Value) where
  encode := site.requestPayload
  decode
    | .opening handle value => if handle = (site.owner, site.sourceSlot) then some (some value)
        else none
    | .decline => some none
    | .expire | .cleartext _ | .malformed => none
  decode_encode value := by cases value <;> simp [requestPayload]
  decode_sound payload value hdecode := by
    cases payload with
    | opening handle claimed =>
        change (if handle = (site.owner, site.sourceSlot) then some (some claimed)
          else none) = some value at hdecode
        by_cases hhandle : handle = (site.owner, site.sourceSlot)
        · rw [if_pos hhandle] at hdecode
          have hvalue := Option.some.inj hdecode
          subst value
          simp [requestPayload, hhandle]
        · simp [hhandle] at hdecode
    | decline =>
        change some none = some value at hdecode
        have hvalue := Option.some.inj hdecode
        subst value
        rfl
    | expire | cleartext _ | malformed =>
        change none = some value at hdecode
        cases hdecode

@[simp]
theorem choiceEncoding_decode_expire (site : ConditionalPublication Principal) :
    (site.choiceEncoding (Value := Value)).decode .expire = none := rfl

/-- The generated publication identity scopes both routing and cached choice
recognition; it is independent of the source binding slot. -/
def addressedChoiceEncoding (site : ConditionalPublication Principal) :
    ChoiceEncoding (Option Value) (Nat × Payload Principal Value) :=
  site.choiceEncoding.atEndpoint site.publicationNode

/-- The same conditional-publication handler, with explicit endpoint routing.
Different tags reject before examining readiness, verification, or guards. -/
def resolveAddressed? (site : ConditionalPublication Principal) (now : Nat)
    (verify : IdealCommitments.Opening
      (Principal := Principal) (Slot := Nat) (Value := Value) → Bool)
    (accepted : Option (CommitmentHandle Principal Nat)) (done : Nat → Bool)
    (canOpen : Value → Bool) (message : Message Principal (Nat × Payload Principal Value)) :
    Option (Option Value) :=
  Message.dispatchEndpoint? site.publicationNode
    (site.resolve? now verify accepted done canOpen) message

@[simp]
theorem resolveAddressed?_addressed (site : ConditionalPublication Principal) (now : Nat)
    (verify : IdealCommitments.Opening
      (Principal := Principal) (Slot := Nat) (Value := Value) → Bool)
    (accepted : Option (CommitmentHandle Principal Nat)) (done : Nat → Bool)
    (canOpen : Value → Bool) (id : MessageId Principal) (payload : Payload Principal Value) :
    site.resolveAddressed? now verify accepted done canOpen
        ⟨id, (site.publicationNode, payload)⟩ =
      site.resolve? now verify accepted done canOpen ⟨id, payload⟩ := by
  simp [resolveAddressed?]

@[simp]
theorem resolveAddressed?_other (site : ConditionalPublication Principal) (now : Nat)
    (verify : IdealCommitments.Opening
      (Principal := Principal) (Slot := Nat) (Value := Value) → Bool)
    (accepted : Option (CommitmentHandle Principal Nat)) (done : Nat → Bool)
    (canOpen : Value → Bool) (id : MessageId Principal) (payload : Payload Principal Value)
    (other : Nat) (hne : other ≠ site.publicationNode) :
    site.resolveAddressed? now verify accepted done canOpen ⟨id, (other, payload)⟩ = none := by
  simp [resolveAddressed?, hne]

end Interaction.ConditionalPublication
