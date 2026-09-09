/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.ConditionalPublication
import Interaction.TransactionalInclusion

/-! # Conditional-publication application regressions

These examples exercise the pure classifier through actual message submission,
recipient-local delivery, and transactional inclusion. They do not add a
runner or claim that messages retained in an inbox become secret again.
-/

namespace InteractionTests.ConditionalPublication

open Interaction

abbrev Principal := Fin 2
abbrev Value := Bool
abbrev Payload := Interaction.ConditionalPublication.Payload Principal Value
abbrev Pool := MessagePool Principal Payload
abbrev Service := IdealCommitments Principal Nat Value

def site : Interaction.ConditionalPublication Principal where
  owner := 0
  sourceSlot := 0
  choiceNode := 3
  publicationNode := 4
  requires := [2]
  deadline := 10

def service : Service :=
  ((IdealCommitments.empty : Service).sealValue 0 0 true).state

structure Application where
  service : Service
  accepted : Option (CommitmentHandle Principal Nat)
  completed : List Nat
  result : Option (Option Value)
  openingAllowed : Bool

def Application.done (state : Application) (node : Nat) : Bool :=
  decide (node ∈ state.completed)

def initial : Application := ⟨service, some (0, 0), [2], none, true⟩
def missingPrerequisite : Application := ⟨service, some (0, 0), [], none, true⟩
def declineOnly : Application := { initial with openingAllowed := false }

def handler (now : Nat) (state : Application)
    (message : Message Principal Payload) : Option Application :=
  match site.resolve? now state.service state.accepted state.done
      (fun _ => state.openingAllowed) message with
  | none => none
  | some choice => some {
      state with
      completed := site.publicationNode :: site.choiceNode :: state.completed
      result := some choice }

def submitDeliverInclude (now : Nat) (state : Application) (sender recipient : Principal)
    (payload : Payload) :=
  let submitted := (MessagePool.empty Principal Payload).submit sender payload
  let delivered := (submitted.2.deliver recipient submitted.1).state
  delivered.includeApplication state submitted.1 (handler now)

def isOpeningTrue : Payload → Bool
  | .opening (owner, slot) value => owner == 0 && slot == 0 && value
  | _ => false

def isExpiry : Payload → Bool
  | .expire => true
  | _ => false

def opened := submitDeliverInclude 5 initial 0 1 (.opening (0, 0) true)

#guard opened.receipt = some true
#guard opened.application.result = some (some true)
#guard 3 ∈ opened.application.completed
#guard 4 ∈ opened.application.completed
#guard (opened.pool.inbox 1).head?.any (fun message => isOpeningTrue message.payload)
#guard opened.pool.ledger.head?.any (fun message => isOpeningTrue message.payload)

def declined := submitDeliverInclude 5 initial 0 1 .decline

#guard declined.receipt = some true
#guard declined.application.result = some none

/- Expiry is permissionless and strict: equality is rejected, while the first
instant after the deadline succeeds without another owner's registration. -/
def expiryAtBoundary := submitDeliverInclude 10 initial 1 0 .expire
def expired := submitDeliverInclude 11 initial 1 0 .expire

#guard expiryAtBoundary.receipt = some false
#guard expiryAtBoundary.application.result = none
#guard expiryAtBoundary.application.completed = [2]
#guard expired.receipt = some true
#guard expired.application.result = some none
#guard service.lookup (1, 0) = none

def wrongOwner := submitDeliverInclude 5 initial 1 0 (.opening (0, 0) true)
def wrongHandle := submitDeliverInclude 5 initial 0 1 (.opening (0, 1) true)
def wrongValue := submitDeliverInclude 5 initial 0 1 (.opening (0, 0) false)

#guard wrongOwner.receipt = some false
#guard wrongHandle.receipt = some false
#guard wrongValue.receipt = some false

/- Binding correctness is independent of the application guard: a verified
opening can be forbidden while decline and expiration remain available. -/
def forbiddenOpening := submitDeliverInclude 5 declineOnly 0 1 (.opening (0, 0) true)
def forcedDecline := submitDeliverInclude 5 declineOnly 0 1 .decline
def forcedExpiry := submitDeliverInclude 11 declineOnly 1 0 .expire

#guard forbiddenOpening.receipt = some false
#guard forbiddenOpening.application.result = none
#guard (forbiddenOpening.pool.inbox 1).head?.any
  (fun message => isOpeningTrue message.payload)
#guard forcedDecline.receipt = some true
#guard forcedDecline.application.result = some none
#guard forcedExpiry.receipt = some true
#guard forcedExpiry.application.result = some none

def duplicatePool := ((MessagePool.empty Principal Payload).submit 0 .decline).2
def duplicate := duplicatePool.includeApplication opened.application (0, 0) (handler 5)

#guard duplicate.receipt = some false
#guard duplicate.application.result = some (some true)
#guard duplicate.application.completed = opened.application.completed

def prerequisiteMissing := submitDeliverInclude 11 missingPrerequisite 1 0 .expire

#guard prerequisiteMissing.receipt = some false
#guard prerequisiteMissing.application.result = none
#guard prerequisiteMissing.application.completed = []

/- A rejected included message remains public, and delivery performed before
the rejected application call remains in the recipient's inbox. -/
#guard wrongValue.pool.ledger.length = 1
#guard (wrongValue.pool.inbox 1).length = 1
#guard wrongValue.application.result = none
#guard wrongValue.application.completed = [2]

def openingThenExpiry :=
  let opening := (MessagePool.empty Principal Payload).submit 0 (.opening (0, 0) true)
  let delivered := (opening.2.deliver 1 opening.1).state
  let expiry := delivered.submit 1 .expire
  expiry.2.includeApplication initial expiry.1 (handler 11)

/- Expiration records public nonpublication, but the previously delivered
opening payload remains recipient-local knowledge. -/
#guard openingThenExpiry.receipt = some true
#guard openingThenExpiry.application.result = some none
#guard (openingThenExpiry.pool.inbox 1).head?.any
  (fun message => isOpeningTrue message.payload)
#guard openingThenExpiry.pool.ledger.head?.any (fun message => isExpiry message.payload)

end InteractionTests.ConditionalPublication
