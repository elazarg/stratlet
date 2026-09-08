/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedExecution
import Interaction.SealedProgramLaws

/-! # Application invariants over native action sequences

The runner admits repeated deliveries, submissions and replays. The application
handler, rather than a uniqueness condition on traffic, prevents a completed
node from executing twice.
-/

namespace Interaction.SealedProgram

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- Every native action preserves at-most-once application execution. -/
theorem step_eventNodes_nodup (program : SealedProgram Principal)
    (state : State Principal Value) (action : Action Principal Value)
    (hnodup : (state.events.map Event.node).Nodup) :
    ((step program state action).events.map Event.node).Nodup := by
  cases action with
  | register owner slot value => exact hnodup
  | submit sender payload => exact hnodup
  | replay broadcaster id => exact hnodup
  | deliver observer id => exact hnodup
  | «include» id => exact includePending_eventNodes_nodup program state id hnodup

/-- An arbitrary finite native run retains unique completed node ids, even
when the input contains copies of messages authored by another principal. -/
theorem run_eventNodes_nodup (program : SealedProgram Principal)
    (state : State Principal Value) (actions : List (Action Principal Value))
    (hnodup : (state.events.map Event.node).Nodup) :
    ((run program state actions).events.map Event.node).Nodup := by
  induction actions generalizing state with
  | nil => exact hnodup
  | cons action rest ih =>
      exact ih (step program state action) (step_eventNodes_nodup program state action hnodup)

end Interaction.SealedProgram
