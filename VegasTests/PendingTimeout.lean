/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedTimeout
import VegasTests.PendingExecution

/-! # Timeout races over the compiled pending-choice application

This fixture extends a genuine compiled source prefix with a timed resolution
state. Expiration is a distinct runtime disposition: it neither fabricates a
source value nor establishes source-terminal or quitting correspondence.
-/

namespace VegasTests.PendingTimeout

open Interaction Interaction.SealedProgram
open VegasTests.PendingSource VegasTests.PendingExecution


abbrev TimedState := Interaction.SealedTimeout.State Player Value

def timed : SealedTimeout Player := ⟨program, 3, 10⟩
def empty : TimedState := Interaction.SealedTimeout.State.empty Player Value

def commitPrefix (left right : Value) : TimedState :=
  timed.run empty
    [.register 0 0 left,
     .submit 0 (.protocol (.commitment 0 (0, 0))), .include (0, 0),
     .register 1 1 right,
     .submit 1 (.protocol (.commitment 1 (1, 1))), .include (1, 0)]

theorem commitPrefix_events (left right : Value) :
    (commitPrefix left right).application.events =
      [.accepted 0 (0, 0), .accepted 1 (1, 1)] := by
  fin_cases left <;> fin_cases right <;> rfl

theorem commitPrefix_bound (left right : Value) :
    (commitPrefix left right).application.service.lookup (1, 1) = some right := by
  fin_cases left <;> fin_cases right <;> rfl

def tooEarly : TimedState :=
  timed.run empty
    [.submit 0 .expire, .include (0, 0)]

theorem expire_before_ready_rejected :
    tooEarly.application.resolution = .pending ∧
      tooEarly.receipts = [((0, 0), false)] := ⟨rfl, rfl⟩

def advanced (left right : Value) : TimedState :=
  timed.step (commitPrefix left right) (.advance 11)

theorem advance_does_not_expire (left right : Value) :
    (advanced left right).clock = 11 ∧
      (advanced left right).application.resolution = .pending := by
  fin_cases left <;> fin_cases right <;> exact ⟨rfl, rfl⟩

def atBoundary (left right : Value) : TimedState :=
  timed.run (commitPrefix left right)
    [.advance 10, .submit 0 .expire, .include (0, 1)]

theorem expire_at_boundary_rejected (left right : Value) :
    (atBoundary left right).application.resolution = .pending ∧
      (atBoundary left right).receipts =
        [((0, 0), true), ((1, 0), true), ((0, 1), false)] := by
  fin_cases left <;> fin_cases right <;> decide

/-- Both competing calls are pending and the opening has already been
delivered before either inclusion order is chosen. -/
def raceReady (left right : Value) : TimedState :=
  timed.run (commitPrefix left right)
    [.advance 11,
     .submit 1 (.protocol (.opening 3 (1, 1) right)),
     .deliver 0 (1, 1),
     .submit 0 .expire]

def openingWins (left right : Value) : TimedState :=
  timed.run (raceReady left right) [.include (1, 1), .include (0, 1)]

def expiryWins (left right : Value) : TimedState :=
  timed.run (raceReady left right) [.include (0, 1), .include (1, 1)]

theorem race_same_pending_and_delivery (left right : Value) :
    (raceReady left right).pool.pending.length = 2 ∧
      ((raceReady left right).pool.inbox 0).getLast?.map Message.id = some (1, 1) := by
  fin_cases left <;> fin_cases right <;> exact ⟨rfl, rfl⟩

theorem opening_wins (left right : Value) :
    (openingWins left right).application.resolution = .completed ∧
      (openingWins left right).receipts =
        [((0, 0), true), ((1, 0), true), ((1, 1), true), ((0, 1), false)] := by
  fin_cases left <;> fin_cases right <;> decide

theorem expiry_wins (left right : Value) :
    (expiryWins left right).application.resolution = .expired ∧
      (expiryWins left right).receipts =
        [((0, 0), true), ((1, 0), true), ((0, 1), true), ((1, 1), false)] := by
  fin_cases left <;> fin_cases right <;> decide

theorem both_calls_published_and_pending_empty (left right : Value) :
    (openingWins left right).pool.pending = [] ∧
      (expiryWins left right).pool.pending = [] ∧
      (openingWins left right).pool.ledger.length =
        (expiryWins left right).pool.ledger.length := by
  fin_cases left <;> fin_cases right <;> decide

theorem delivered_opening_survives_both_orders (left right : Value) :
    (openingWins left right).pool.inbox 0 = (raceReady left right).pool.inbox 0 ∧
      (expiryWins left right).pool.inbox 0 = (raceReady left right).pool.inbox 0 := by
  fin_cases left <;> fin_cases right <;> exact ⟨rfl, rfl⟩

theorem bound_value_survives_both_orders (left right : Value) :
    (openingWins left right).application.service.lookup (1, 1) = some right ∧
      (expiryWins left right).application.service.lookup (1, 1) = some right := by
  fin_cases left <;> fin_cases right <;> exact ⟨rfl, rfl⟩

/-- Once expiration wins, the ordinary opening is published but rejected and
does not mutate the protocol-event log. -/
theorem expired_rejects_protocol_event (left right : Value) :
    (expiryWins left right).application.events =
      (raceReady left right).application.events := by
  fin_cases left <;> fin_cases right <;> rfl

theorem raceReady_events (left right : Value) :
    (raceReady left right).application.events =
      [.accepted 0 (0, 0), .accepted 1 (1, 1)] := by
  fin_cases left <;> fin_cases right <;> rfl

theorem expiry_does_not_fabricate_decline (left right : Value) :
    .opened 3 none ∉ (expiryWins left right).application.events := by
  rw [expired_rejects_protocol_event, raceReady_events]
  simp

/-- Expiration closes protocol-event acceptance, not the ideal service or wire
runtime. A fresh registration succeeds while the earlier binding is retained. -/
def registeredAfterExpiry (left right : Value) : TimedState :=
  timed.step (expiryWins left right) (.register 0 7 left)

theorem expiration_allows_fresh_registration (left right : Value) :
    (registeredAfterExpiry left right).application.service.lookup (0, 7) = some left ∧
      (registeredAfterExpiry left right).application.service.lookup (1, 1) = some right ∧
      (registeredAfterExpiry left right).application.events =
        (expiryWins left right).application.events := by
  fin_cases left <;> fin_cases right <;> exact ⟨rfl, rfl, rfl⟩

end VegasTests.PendingTimeout
