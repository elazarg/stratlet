/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedExecution
import Interaction.SealedProgramLaws

/-! # Persistence laws for native sealed execution

Occupied ideal-service slots are write-once across every raw native action.
Application events are likewise append-only. These are operational safety
facts; they make no scheduling, authentication, or disclosure assumption.
-/

namespace Interaction.SealedProgram

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- One arbitrary native action cannot change an occupied ideal-service slot. -/
theorem step_lookup_of_eq_some (program : SealedProgram Principal)
    (state : State Principal Value) (action : Action Principal Value)
    (handle : CommitmentHandle Principal Nat) (value : Value)
    (hlookup : state.service.lookup handle = some value) :
    (step program state action).service.lookup handle = some value := by
  cases action with
  | register owner slot replacement =>
      exact IdealCommitments.lookup_sealValue_of_eq_some
        state.service owner slot replacement handle value hlookup
  | submit sender payload => exact hlookup
  | replay broadcaster id => exact hlookup
  | deliver observer id => exact hlookup
  | «include» id =>
      simp only [step]
      unfold includePending
      generalize hinc : state.pool.includePending id = included
      cases hm : included.message with
      | none => simp [hm, hlookup]
      | some message =>
          simp only [hm]
          rw [handle_preserves_service]
          exact hlookup

/-- An occupied ideal-service slot retains its value throughout every finite
raw native execution. -/
theorem run_lookup_of_eq_some (program : SealedProgram Principal)
    (state : State Principal Value) (actions : List (Action Principal Value))
    (handle : CommitmentHandle Principal Nat) (value : Value)
    (hlookup : state.service.lookup handle = some value) :
    (run program state actions).service.lookup handle = some value := by
  induction actions generalizing state with
  | nil => exact hlookup
  | cons action rest ih =>
      exact ih (step program state action)
        (step_lookup_of_eq_some program state action handle value hlookup)

private theorem handle_events_prefix (program : SealedProgram Principal)
    (state : State Principal Value)
    (message : Message Principal (Payload Principal Value)) :
    state.events.IsPrefix (handle program state message).events := by
  cases hvalid : validateMessage? program state.service state.events message with
  | some event =>
      rw [handle_eq_of_validateMessage?_eq_some program state message event hvalid]
      exact ⟨[event], rfl⟩
  | none => exact ⟨[], by simp [handle, hvalid]⟩

/-- Native execution only appends application events. -/
theorem step_events_prefix (program : SealedProgram Principal)
    (state : State Principal Value) (action : Action Principal Value) :
    state.events.IsPrefix (step program state action).events := by
  cases action with
  | register owner slot value => exact ⟨[], by simp [step]⟩
  | submit sender payload => exact ⟨[], by simp [step]⟩
  | replay broadcaster id => exact ⟨[], by simp [step]⟩
  | deliver observer id => exact ⟨[], by simp [step]⟩
  | «include» id =>
      simp only [step]
      unfold includePending
      generalize hinc : state.pool.includePending id = included
      cases hm : included.message with
      | none => exact ⟨[], by simp [hm]⟩
      | some message =>
          simp only [hm]
          exact handle_events_prefix program
            { state with pool := included.state } message

/-- A finite native run retains the starting event list as a prefix. -/
theorem run_events_prefix (program : SealedProgram Principal)
    (state : State Principal Value) (actions : List (Action Principal Value)) :
    state.events.IsPrefix (run program state actions).events := by
  induction actions generalizing state with
  | nil => exact ⟨[], by simp⟩
  | cons action rest ih =>
      exact (step_events_prefix program state action).trans
        (ih (step program state action))

end Interaction.SealedProgram
