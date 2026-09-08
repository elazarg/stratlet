/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.DependencyGateLaws
import Interaction.TransactionalInclusion

/-! # Executable regressions for staged timeout dependency gates -/

namespace InteractionTests.TimeoutGate

open Interaction Interaction.DependencyGate

abbrev Principal := Fin 3
abbrev Index := Nat
abbrev Gate := DependencyGate Principal Index

def initial : Gate := ⟨∅, ∅, 0⟩

/- Expiry is strict: equality with the deadline is not overdue. -/
#guard slidingExpiry (Principal := Principal) (Index := Index) 10 10 initial (0, 0) = false
#guard slidingExpiry (Principal := Principal) (Index := Index) 11 10 initial (0, 0) = true

def dependencies : List (Principal × Index) := [(0, 0), (1, 0)]

/- The first overdue owner resets the shared activity origin, so the second
distinct overdue owner is no longer expired and the staged call fails. -/
#guard call 10 (slidingExpiry 10 5) 2 (2, 9) dependencies (fun _ => true) initial = none

/- Stable per-obligation deadlines expire both missing dependencies in the
same call and commit both exclusions. -/
def fixedSuccess : Option Gate :=
  call 10 (fixedExpiry 10 (fun _ => 5)) 2 (2, 9) dependencies (fun _ => true) initial

#guard fixedSuccess.isSome
#guard fixedSuccess.any fun gate => 0 ∈ gate.excluded && 1 ∈ gate.excluded
#guard fixedSuccess.any fun gate => (2, 9) ∈ gate.completed

/- Body rejection discards the otherwise successful staged completion and
exclusions. -/
#guard (call 10 (fixedExpiry 10 (fun _ => 5)) 2 (2, 9) dependencies
  (fun _ => false) initial).isNone

/- An unrelated successful call resets the shared activity origin and can
prevent a later missing dependency from expiring. -/
def afterUnrelated : Gate :=
  (call 8 (slidingExpiry 8 5) 2 (2, 7) [] (fun _ => true) initial).getD initial

#guard afterUnrelated.lastActivity = 8
#guard (call 10 (slidingExpiry 10 5) 2 (2, 8) [(0, 0)] (fun _ => true)
  afterUnrelated).isNone
#guard (call 10 (slidingExpiry 10 5) 2 (2, 8) [(0, 0)] (fun _ => true)
  initial).isSome

/- Excluding one overdue obligation excludes its principal, thereby
discharging another nonexpired obligation of that same principal. -/
def firstOnlyExpiry : Gate → Principal × Index → Bool :=
  fun _ dependency => decide (dependency = (0, 0))

def principalWide : Option Gate :=
  call 10 firstOnlyExpiry 2 (2, 6) [(0, 0), (0, 1)] (fun _ => true) initial

#guard principalWide.isSome
#guard principalWide.any fun gate => 0 ∈ gate.excluded

/-! ## Transactional publication boundary -/

abbrev Pool := MessagePool Principal Unit

def submitted : Pool := ((MessagePool.empty Principal Unit).submit 2 ()).2
def delivered : Pool := (submitted.deliver 1 (2, 0)).state

def slidingHandler (gate : Gate) (message : Message Principal Unit) : Option Gate :=
  if message.sender = 2 then
    call 10 (slidingExpiry 10 5) 2 (2, 9) dependencies (fun _ => true) gate
  else none

def rejected := delivered.includeApplication initial (2, 0) slidingHandler

/- Failed staged gate effects roll back, while inclusion publication and the
recipient's earlier delivery remain recorded. -/
#guard rejected.receipt = some false
#guard rejected.application = initial
#guard rejected.pool.ledger.length = 1
#guard (rejected.pool.ledger.head?.map Message.sender) = some 2
#guard (rejected.pool.inbox 1).length = 1

def fixedHandler (gate : Gate) (message : Message Principal Unit) : Option Gate :=
  if message.sender = 2 then
    call 10 (fixedExpiry 10 (fun _ => 5)) 2 (2, 9) dependencies (fun _ => true) gate
  else none

def accepted := delivered.includeApplication initial (2, 0) fixedHandler

#guard accepted.receipt = some true
#guard accepted.pool.ledger.length = 1
#guard (accepted.pool.inbox 1).length = 1
#guard 0 ∈ accepted.application.excluded
#guard 1 ∈ accepted.application.excluded

/- Entry-point metadata belongs to the handler. A different sender does not
acquire the fixed action's authority just by submitting the same payload. -/
def unauthorizedPool : Pool := ((MessagePool.empty Principal Unit).submit 0 ()).2
def unauthorized := unauthorizedPool.includeApplication initial (0, 0) fixedHandler

#guard unauthorized.receipt = some false
#guard unauthorized.application = initial
#guard unauthorized.pool.ledger.length = 1

end InteractionTests.TimeoutGate

/-- info: 'Interaction.DependencyGate.checkAll_slidingExpiry_two_active_missing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.DependencyGate.checkAll_slidingExpiry_two_active_missing

/-- info: 'Interaction.DependencyGate.checkAll_fixedExpiry_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.DependencyGate.checkAll_fixedExpiry_exact

/-- info: 'Interaction.DependencyGate.checkAll_fixedExpiry_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.DependencyGate.checkAll_fixedExpiry_exists

/-- info: 'Interaction.MessagePool.includeApplication_reject_ledger' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessagePool.includeApplication_reject_ledger

/-- info: 'Interaction.MessagePool.includeApplication_preserves_inbox' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessagePool.includeApplication_preserves_inbox
