/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedExecution
import Interaction.SealedProgramLaws
import VegasTests.PendingSource

/-! # Native execution of the compiled nullable source

These are finite operational transcripts through the generic sealed-message
runner. They make no strategic, liveness, or cryptographic claim.
-/

namespace VegasTests.PendingExecution

open Interaction Interaction.SealedProgram
open VegasTests.PendingSource

abbrev Value := Option Bool
abbrev Program := SealedProgram Player
abbrev RuntimeState := SealedProgram.State Player Value

/-- Executable static specialization of the four rules emitted by the
certified source compiler. Elaboration reduces the exact compiler term; this
does not assert general executable extraction from arbitrary source syntax. -/
def program : Program := by
  run_tac do
    let expected ← Lean.Elab.Tactic.getMainTarget
    let emitted ← Lean.Elab.Term.elabTerm
      (← `(VegasTests.PendingSource.sealedFragment.compile)) (some expected)
    let normalized ← Lean.Meta.reduce emitted
    Lean.Elab.Tactic.closeMainGoal `sealedEmission normalized

theorem program_eq_compile : program = sealedFragment.compile := rfl

#guard program.rules.length == 4

def initial : RuntimeState := SealedProgram.State.empty Player Value

def commitActions (left right : Value) (reverse : Bool) : List (Action Player Value) :=
  [.register 0 0 left,
   .submit 0 (.commitment 0 (0, 0)),
   .register 1 1 right,
   .submit 1 (.commitment 1 (1, 1)),
   .deliver 1 (0, 0),
   .deliver 0 (1, 0)] ++
  if reverse then [.include (1, 0), .include (0, 0)]
  else [.include (0, 0), .include (1, 0)]

def afterCommits (left right : Value) (reverse : Bool) : RuntimeState :=
  program.run initial (commitActions left right reverse)

/-- Delivered handles are opaque: before inclusion, the entire public pool is
independent of both privately registered bits. -/
theorem commit_delivery_pool_eq (left right otherLeft otherRight : Value) :
    (program.run initial ((commitActions left right false).take 6)).pool =
      (program.run initial ((commitActions otherLeft otherRight false).take 6)).pool := by
  rfl

theorem forward_commit_events (left right : Value) :
    (afterCommits left right false).events =
      [.accepted 0 (0, 0), .accepted 1 (1, 1)] := by
  rfl

theorem reverse_commit_events (left right : Value) :
    (afterCommits left right true).events =
      [.accepted 1 (1, 1), .accepted 0 (0, 0)] := by
  rfl

theorem opening0_enabled (left right : Value) (reverse : Bool) :
    program.openingRequest? (afterCommits left right reverse).events 0 2 left =
      some (.opening 2 (0, 0) left) := by
  cases reverse <;> rfl

theorem opening1_enabled (left right : Value) (reverse : Bool) :
    program.openingRequest? (afterCommits left right reverse).events 1 3 right =
      some (.opening 3 (1, 1) right) := by
  cases reverse <;> rfl

theorem opening0_submission_is_native_step (left right : Value) (reverse : Bool) :
    (program.submitOpening? (afterCommits left right reverse) 0 2 left).map Prod.snd =
      some (program.step (afterCommits left right reverse)
        (.submit 0 (.opening 2 (0, 0) left))) :=
  submitOpening?_eq_step program (afterCommits left right reverse) 0 2 left _
    (opening0_enabled left right reverse)

theorem opening1_submission_is_native_step (left right : Value) (reverse : Bool) :
    (program.submitOpening? (afterCommits left right reverse) 1 3 right).map Prod.snd =
      some (program.step (afterCommits left right reverse)
        (.submit 1 (.opening 3 (1, 1) right))) :=
  submitOpening?_eq_step program (afterCommits left right reverse) 1 3 right _
    (opening1_enabled left right reverse)

theorem opening0_requires_both {events : List (Event Player Value)} {claimed : Value}
    (hrequest : program.openingRequest? events 0 2 claimed =
      some (.opening 2 (0, 0) claimed)) :
    done events 0 = true ∧ done events 1 = true := by
  obtain ⟨requires, hrule, _, hrequires, _⟩ :=
    openingRequest?_sound program events 0 2 0 claimed hrequest
  have hshape : requires = [0, 1] := by
    have heq := congrArg SealedRule.requires (Option.some.inj hrule)
    change graph.messagePrerequisites (node 2) = requires at heq
    exact heq.symm.trans node2_messagePrerequisites
  subst requires
  simpa using hrequires

theorem opening1_requires_both {events : List (Event Player Value)} {claimed : Value}
    (hrequest : program.openingRequest? events 1 3 claimed =
      some (.opening 3 (1, 1) claimed)) :
    done events 0 = true ∧ done events 1 = true := by
  obtain ⟨requires, hrule, _, hrequires, _⟩ :=
    openingRequest?_sound program events 1 3 1 claimed hrequest
  have hshape : requires = [0, 1] := by
    have heq := congrArg SealedRule.requires (Option.some.inj hrule)
    change graph.messagePrerequisites (node 3) = requires at heq
    exact heq.symm.trans node3_messagePrerequisites
  subst requires
  simpa using hrequires

def openingActions (left right : Value) : List (Action Player Value) :=
  [.submit 0 (.opening 2 (0, 0) left),
   .deliver 1 (0, 1),
   .submit 1 (.opening 3 (1, 1) right),
   .deliver 0 (1, 1),
   .include (0, 1),
   .include (1, 1)]

def honestRun (left right : Value) (reverse : Bool) : RuntimeState :=
  program.run (afterCommits left right reverse) (openingActions left right)

theorem honest_none_events :
    (honestRun none none false).events =
      [.accepted 0 (0, 0), .accepted 1 (1, 1),
       .opened 2 none, .opened 3 none] := by
  rfl

theorem honest_some_events :
    (honestRun (some false) (some true) true).events =
      [.accepted 1 (1, 1), .accepted 0 (0, 0),
       .opened 2 (some false), .opened 3 (some true)] := by
  rfl

theorem honest_forward_events (left right : Value) :
    (honestRun left right false).events =
      [.accepted 0 (0, 0), .accepted 1 (1, 1), .opened 2 left, .opened 3 right] := by
  fin_cases left <;> fin_cases right <;> rfl

theorem honest_reverse_events (left right : Value) :
    (honestRun left right true).events =
      [.accepted 1 (1, 1), .accepted 0 (0, 0), .opened 2 left, .opened 3 right] := by
  fin_cases left <;> fin_cases right <;> rfl

theorem honest_service_left (left right : Value) (reverse : Bool) :
    (honestRun left right reverse).service.lookup (0, 0) = some left := by
  fin_cases left <;> fin_cases right <;> cases reverse <;> rfl

theorem honest_service_right (left right : Value) (reverse : Bool) :
    (honestRun left right reverse).service.lookup (1, 1) = some right := by
  fin_cases left <;> fin_cases right <;> cases reverse <;> rfl

def pendingNoneOpening : RuntimeState :=
  program.step (afterCommits none none false)
    (.submit 0 (.opening 2 (0, 0) none))

/-- A generated `none` opening that has only been submitted remains pending;
the source decline is already an accepted commitment, but reveal node 2 is not
done until that preexisting opening is included. -/
theorem none_opening_pending :
    pendingNoneOpening.pool.pending =
      [⟨(0, 1), .opening 2 (0, 0) none⟩] ∧
    pendingNoneOpening.events =
      [.accepted 0 (0, 0), .accepted 1 (1, 1)] ∧
    done pendingNoneOpening.events 2 = false := by
  exact ⟨rfl, rfl, rfl⟩

def declined : RuntimeState :=
  program.run initial
    [.register 0 0 none, .submit 0 (.commitment 0 (0, 0)), .include (0, 0)]

/-- A submitted source `none` is an accepted commitment. It is not the absence
of a pending message or action. -/
theorem decline_is_not_missing :
    declined.events = [.accepted 0 (0, 0)] ∧ initial.events = [] := by
  exact ⟨rfl, rfl⟩

def cleartextAttempt (value : Value) : RuntimeState :=
  program.run initial [.submit 0 (.cleartext 0 value), .include (0, 0)]

/-- Raw cleartext is publicly included but rejected by the application. -/
theorem cleartext_public_but_rejected (value : Value) :
    (cleartextAttempt value).pool.ledger = [⟨(0, 0), .cleartext 0 value⟩] ∧
      (cleartextAttempt value).events = [] := by
  exact ⟨rfl, rfl⟩

theorem cleartext_leaks (left right : Value) (hne : left ≠ right) :
    (cleartextAttempt left).pool.ledger ≠ (cleartextAttempt right).pool.ledger := by
  intro heq
  have hpayload := congrArg (fun messages => messages.map Message.payload) heq
  change [Payload.cleartext 0 left] = [Payload.cleartext 0 right] at hpayload
  have := (List.cons.inj hpayload).1
  cases this
  exact hne rfl

#guard (honestRun none none false).events.length == 4

/-- info: 4 -/
#guard_msgs in
#eval (honestRun none none false).events.length

end VegasTests.PendingExecution
