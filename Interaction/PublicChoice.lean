/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessagePool

/-! # Authenticated public choice endpoint

This runtime-general component validates one owner-authored public choice once
its dependency nodes are complete.  It is an injectable handler only: it has no
state, runner, scheduler, commitment mechanism, or timeout behavior.
-/

namespace Interaction

universe uPrincipal uValue uState

structure PublicChoice (Principal : Type uPrincipal) where
  owner : Principal
  choiceNode : Nat
  publicationNode : Nat
  requires : List Nat

namespace PublicChoice

variable {Principal : Type uPrincipal} {Value : Type uValue}

def ready (site : PublicChoice Principal) (done : Nat → Bool) : Bool :=
  !done site.choiceNode && !done site.publicationNode && site.requires.all done

def resolve? [DecidableEq Principal] (site : PublicChoice Principal)
    (done : Nat → Bool) (valid : Value → Bool)
    (message : Message Principal Value) : Option Value :=
  if message.sender = site.owner ∧ site.ready done ∧ valid message.payload then
    some message.payload
  else none

/-- Direct normalization to the endpoint's authentication, readiness, and
validation conditional. -/
theorem resolve?_eq [DecidableEq Principal] (site : PublicChoice Principal)
    (done : Nat → Bool) (valid : Value → Bool) (message : Message Principal Value) :
    site.resolve? done valid message =
      if message.sender = site.owner ∧ site.ready done ∧ valid message.payload then
        some message.payload
      else none := rfl

/-- Application effects can be attached to the accepted value without adding
another acceptance test. -/
theorem resolve?_map [DecidableEq Principal] {State : Type uState}
    (site : PublicChoice Principal) (done : Nat → Bool) (valid : Value → Bool)
    (message : Message Principal Value) (record : Value → State) :
    (site.resolve? done valid message).map record =
      if message.sender = site.owner ∧ site.ready done ∧ valid message.payload then
        some (record message.payload) else none := by
  unfold resolve?
  split <;> rfl

/-- Exact inversion and introduction rule for an accepted public value. -/
theorem resolve_iff [DecidableEq Principal] (site : PublicChoice Principal)
    (done : Nat → Bool) (valid : Value → Bool) (message : Message Principal Value)
    (value : Value) :
    site.resolve? done valid message = some value ↔
      site.ready done = true ∧ message.sender = site.owner ∧
        valid value = true ∧ message.payload = value := by
  simp only [resolve?]
  split
  · rename_i haccepted
    simp only [Option.some.injEq]
    constructor
    · intro hpayload
      exact ⟨haccepted.2.1, haccepted.1, hpayload ▸ haccepted.2.2, hpayload⟩
    · intro hconditions
      exact hconditions.2.2.2
  · rename_i hrejected
    constructor
    · intro hresolve
      cases hresolve
    · intro hconditions
      exact (hrejected ⟨hconditions.2.1, hconditions.1,
        by rw [hconditions.2.2.2]; exact hconditions.2.2.1⟩).elim

/-- A canonical owner-authored request accepts exactly when the endpoint is
ready and its payload passes the supplied validator. -/
theorem resolve_request [DecidableEq Principal] (site : PublicChoice Principal)
    (done : Nat → Bool) (valid : Value → Bool) (serial : Nat) (value : Value) :
    site.resolve? done valid ⟨(site.owner, serial), value⟩ = some value ↔
      site.ready done = true ∧ valid value = true := by
  simp [resolve?, Message.sender]

theorem resolve_wrong_owner [DecidableEq Principal] (site : PublicChoice Principal)
    (done : Nat → Bool) (valid : Value → Bool) (message : Message Principal Value)
    (howner : message.sender ≠ site.owner) :
    site.resolve? done valid message = none := by
  simp [resolve?, howner]

theorem resolve_when_not_ready [DecidableEq Principal] (site : PublicChoice Principal)
    (done : Nat → Bool) (valid : Value → Bool) (message : Message Principal Value)
    (hready : site.ready done = false) :
    site.resolve? done valid message = none := by
  simp [resolve?, hready]

theorem resolve_invalid [DecidableEq Principal] (site : PublicChoice Principal)
    (done : Nat → Bool) (valid : Value → Bool) (message : Message Principal Value)
    (hinvalid : valid message.payload = false) :
    site.resolve? done valid message = none := by
  simp [resolve?, hinvalid]

/-- Resolution depends only on the explicitly supplied public completion map,
validator, and message. -/
theorem resolve?_congr [DecidableEq Principal] (site : PublicChoice Principal)
    (leftDone rightDone : Nat → Bool) (leftValid rightValid : Value → Bool)
    (message : Message Principal Value)
    (hdone : ∀ node, leftDone node = rightDone node)
    (hvalid : ∀ value, leftValid value = rightValid value) :
    site.resolve? leftDone leftValid message = site.resolve? rightDone rightValid message := by
  rw [funext hdone, funext hvalid]

end PublicChoice

end Interaction
