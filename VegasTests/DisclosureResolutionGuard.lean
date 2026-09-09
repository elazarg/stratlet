/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ConditionalResolution
import VegasTests.PersistentDisclosure

/-! # Persistent refusal at the conditional-publication boundary

After the first disclosure is publicly declined, the second source guard has
no legal opening value.  The application predicate therefore rejects a valid
commitment opening while retaining the authenticated decline transition.
-/

noncomputable section

namespace VegasTests.DisclosureResolutionGuard

open Interaction Vegas
open VegasTests.PersistentDisclosure

abbrev RuntimePayload :=
  Interaction.ConditionalPublication.Payload
    VegasTests.PersistentDisclosure.Player Bool

def site : Interaction.ConditionalPublication
    VegasTests.PersistentDisclosure.Player where
  owner := 0
  sourceSlot := 0
  choiceNode := 8
  publicationNode := 9
  requires := []
  deadline := 10

def service (secret : Bool) : IdealCommitments
    VegasTests.PersistentDisclosure.Player Nat Bool where
  table owner slot := if owner = 0 ∧ slot = 0 then some secret else none

def done (_ : Nat) : Bool := false
def canOpen (_ : Bool) : Bool := false

theorem canOpen_matches_second_guard_after_refusal
    (secret signal response value : Bool) :
    canOpen value = true ↔
      evalGuard (Player := VegasTests.PersistentDisclosure.Player)
        (L := simpleExpr) secondGuard (some value)
        (((secondEnv secret signal none response).toView 0).eraseEnv) = true := by
  simp only [canOpen, Bool.false_eq_true, false_iff]
  intro hlegal
  have := refusal_forces_later_refusal secret signal response (some value) hlegal
  simp at this

theorem opening_rejected_after_refusal (secret : Bool) :
    site.resolve? 5 (service secret).verify (some (0, 0)) done canOpen
      ⟨(0, 0), .opening (0, 0) secret⟩ = (none : Option (Option Bool)) := by
  exact site.resolve_opening_when_closed 5 (service secret).verify (some (0, 0))
    done canOpen ⟨(0, 0), .opening (0, 0) secret⟩ (0, 0) secret rfl rfl

theorem decline_accepted_after_refusal (secret : Bool) :
    site.resolve? 5 (service secret).verify (some (0, 0)) done canOpen
      ⟨(0, 0), .decline⟩ = some (none : Option Bool) := by
  rfl

end VegasTests.DisclosureResolutionGuard
