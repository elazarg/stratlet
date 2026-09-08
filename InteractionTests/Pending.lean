/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Core.Form
import Interaction.MessagePool

/-! # A bounded pending-message interaction

This is a regression example, not a general asynchronous-game semantics. The
game form below calls the same native message-pool operations as the direct
execution examples.
-/

noncomputable section

namespace InteractionTests.Pending

open GameTheory GameTheory.Math.Probability
open Interaction Interaction.MessagePool

abbrev Pool := MessagePool Bool Bool
abbrev LocalView := View Bool Bool

structure Outcome where
  pool : Pool
  first : Bool
  response : Bool

def Strategy : Bool → Type
  | false => Bool
  | true => LocalView → FinDist Bool

def afterFirstSubmission (first : Bool) : MessageId Bool × Pool :=
  submit (empty Bool Bool) false first

def beforeResponse (first deliverFirst : Bool) : MessageId Bool × Pool :=
  let submitted := afterFirstSubmission first
  if deliverFirst then
    (submitted.1, (deliver submitted.2 true submitted.1).state)
  else submitted

/-- A fixed finite environment decides whether the first wire message is
delivered and in which order the two pending messages enter the public ledger. -/
def nativeRun (deliverFirst reverseInclusion first : Bool)
    (respond : LocalView → FinDist Bool) : FinDist Outcome :=
  let ready := beforeResponse first deliverFirst
  (respond (observe ready.2 true)).bind fun response =>
    let replied := submit ready.2 true response
    let included :=
      if reverseInclusion then
        includePending (includePending replied.2 replied.1).state ready.1
      else
        includePending (includePending replied.2 ready.1).state replied.1
    FinDist.pure ⟨included.state, first, response⟩

def form (deliverFirst reverseInclusion : Bool) : GameForm Bool where
  sig := { Strategy := Strategy, Outcome := Outcome }
  play profile := nativeRun deliverFirst reverseInclusion (profile false) (profile true)

theorem form_play (deliverFirst reverseInclusion : Bool) (profile : Profile (form
    deliverFirst reverseInclusion).sig) :
    (form deliverFirst reverseInclusion).play profile =
      nativeRun deliverFirst reverseInclusion (profile false) (profile true) :=
  rfl

theorem undelivered_invisible (first : Bool) :
    observe (beforeResponse first false).2 true = observe (empty Bool Bool) true := by
  rfl

theorem delivered_cleartext (first : Bool) :
    (observe (beforeResponse first true).2 true).inbox =
      [⟨(false, 0), first⟩] := by
  simp [beforeResponse, afterFirstSubmission, submit, empty, deliver, lookup, observe]

theorem response_marginal (deliverFirst reverseInclusion first : Bool)
    (respond : LocalView → FinDist Bool) :
    (nativeRun deliverFirst reverseInclusion first respond).map Outcome.response =
      respond (observe (beforeResponse first deliverFirst).2 true) := by
  simp [nativeRun]

def constantResponse (value : Bool) : LocalView → FinDist Bool :=
  fun _ => FinDist.pure value

theorem forward_ledger (first response : Bool) :
    (nativeRun true false first (constantResponse response)).map
        (fun outcome => outcome.pool.ledger) =
      FinDist.pure [⟨(false, 0), first⟩, ⟨(true, 0), response⟩] := by
  simp [nativeRun, constantResponse, beforeResponse, afterFirstSubmission, submit,
    empty, deliver, lookup, includePending, removeFirst]

theorem reverse_ledger (first response : Bool) :
    (nativeRun true true first (constantResponse response)).map
        (fun outcome => outcome.pool.ledger) =
      FinDist.pure [⟨(true, 0), response⟩, ⟨(false, 0), first⟩] := by
  simp [nativeRun, constantResponse, beforeResponse, afterFirstSubmission, submit,
    empty, deliver, lookup, includePending, removeFirst]

end InteractionTests.Pending
