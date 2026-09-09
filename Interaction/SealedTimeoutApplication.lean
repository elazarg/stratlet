/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplication
import Interaction.SealedTimeout

/-! # The timed sealed protocol as a shared message application

This adapter identifies the existing timed sealed runtime with the generic
message-application runtime. The clock is public application state, private
commands register ideal-service values, and environment commands advance the
clock monotonically. The correspondence is exact, including rejected and
missing-message inclusion behavior.
-/

namespace Interaction

open GameTheory.Math.Probability

universe uPrincipal uValue

namespace SealedTimeout

variable {Principal : Type uPrincipal} {Value : Type uValue}

structure SharedApplicationState (Principal : Type uPrincipal) (Value : Type uValue) where
  application : Application Principal Value
  clock : Nat

structure SharedApplicationView (Principal : Type uPrincipal) (Value : Type uValue) where
  events : List (SealedProgram.Event Principal Value)
  resolution : DeadlineResolution
  clock : Nat

noncomputable def messageApplication [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) : MessageApplication Principal where
  Application := SharedApplicationState Principal Value
  Payload := Payload Principal Value
  PrivateCommand := ULift.{uPrincipal} (Nat × Value)
  EnvironmentCommand := ULift.{max uPrincipal uValue} Nat
  PlayerView := SharedApplicationView Principal Value
  EnvironmentView := SharedApplicationView Principal Value
  privateStep state owner command :=
    { state with application.service :=
        (state.application.service.sealValue owner command.down.1 command.down.2).state }
  environmentStep state command :=
    FinDist.pure
      (if state.clock ≤ command.down then { state with clock := command.down } else state)
  handle state message := do
    let application ← timed.handle state.clock state.application message
    some { state with application }
  observePlayer state _ := ⟨state.application.events, state.application.resolution, state.clock⟩
  observeEnvironment state := ⟨state.application.events, state.application.resolution, state.clock⟩

def toSharedState [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (state : State Principal Value) :
    (messageApplication (Value := Value) timed).State :=
  ⟨⟨state.application, state.clock⟩, state.pool, state.receipts⟩

def fromSharedState [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal)
    (state : (messageApplication (Value := Value) timed).State) : State Principal Value :=
  ⟨state.application.application, state.pool, state.application.clock, state.receipts⟩

@[simp] theorem fromSharedState_toSharedState [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (state : State Principal Value) :
    fromSharedState timed (toSharedState timed state) = state := rfl

@[simp] theorem toSharedState_fromSharedState [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal)
    (state : (messageApplication (Value := Value) timed).State) :
    toSharedState timed (fromSharedState timed state) = state := by
  cases state
  rfl

def toSharedAction [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) : Action Principal Value →
      (messageApplication (Value := Value) timed).Action
  | .register owner slot value => .privateCommand owner (ULift.up (slot, value))
  | .submit author payload => .submit author payload
  | .replay broadcaster id => .replay broadcaster id
  | .deliver observer id => .deliver observer id
  | .include id => .include id
  | .advance clock => .environment (ULift.up clock)

def fromSharedAction [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) :
      (messageApplication (Value := Value) timed).Action → Action Principal Value
  | .privateCommand owner command => .register owner command.down.1 command.down.2
  | .submit author payload => .submit author payload
  | .replay broadcaster id => .replay broadcaster id
  | .deliver observer id => .deliver observer id
  | .include id => .include id
  | .environment command => .advance command.down

@[simp] theorem fromSharedAction_toSharedAction [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (action : Action Principal Value) :
    fromSharedAction timed (toSharedAction timed action) = action := by
  cases action <;> rfl

@[simp] theorem toSharedAction_fromSharedAction [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal)
    (action : (messageApplication (Value := Value) timed).Action) :
    toSharedAction timed (fromSharedAction timed action) = action := by
  cases action <;> rfl

def timedPlayerView [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal)
    (view : (messageApplication (Value := Value) timed).View) : View Principal Value :=
  ⟨view.messages, view.application.events, view.application.resolution,
    view.application.clock, view.receipts⟩

theorem timedPlayerView_observe [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (state : State Principal Value) (who : Principal) :
    timedPlayerView timed
      (MessageApplication.State.observe (app := messageApplication (Value := Value) timed)
        (toSharedState timed state) who) = state.observe who := rfl

def timedEnvironmentView [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal)
    (view : (messageApplication (Value := Value) timed).EnvironmentObservation) :
    EnvironmentView Principal Value :=
  ⟨view.pool, view.application.events, view.application.resolution,
    view.application.clock, view.receipts⟩

theorem timedEnvironmentView_observe [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (state : State Principal Value) :
    timedEnvironmentView timed
      (MessageApplication.State.environmentView
        (app := messageApplication (Value := Value) timed) (toSharedState timed state)) =
      state.environmentView := rfl

theorem step_shared [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (state : State Principal Value)
    (action : Action Principal Value) :
    (messageApplication (Value := Value) timed).step (toSharedState timed state)
        (toSharedAction timed action) =
      FinDist.pure (toSharedState timed (timed.step state action)) := by
  cases action with
  | register => rfl
  | submit => rfl
  | replay => rfl
  | deliver => rfl
  | «include» id =>
      simp only [MessageApplication.step, toSharedAction, toSharedState,
        messageApplication, SealedTimeout.step, SealedTimeout.includePending,
        MessageApplication.includePending]
      unfold MessagePool.includeApplication
      generalize state.pool.includePending id = included
      cases included with
      | mk message pool =>
          cases message with
          | none => rfl
          | some message =>
              cases hhandle : timed.handle state.clock state.application message <;>
                simp [hhandle]
  | advance clock =>
      simp only [MessageApplication.step, toSharedAction, toSharedState,
        messageApplication, SealedTimeout.step, FinDist.map_pure]
      split <;> rfl

theorem run_shared [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (state : State Principal Value)
    (actions : List (Action Principal Value)) :
    (messageApplication (Value := Value) timed).run
        (actions.map (toSharedAction timed)) (toSharedState timed state) =
      FinDist.pure (toSharedState timed (timed.run state actions)) := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      simp only [List.map_cons, MessageApplication.run_cons, SealedTimeout.run_cons,
        step_shared, FinDist.pure_bind]
      exact ih (timed.step state action)

theorem run_shared_actions [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (state : State Principal Value)
    (actions : List (messageApplication (Value := Value) timed).Action) :
    (messageApplication (Value := Value) timed).run actions (toSharedState timed state) =
      FinDist.pure (toSharedState timed
        (timed.run state (actions.map (fromSharedAction timed)))) := by
  have hactions : actions =
      (actions.map (fromSharedAction timed)).map (toSharedAction timed) := by
    induction actions with
    | nil => rfl
    | cons action rest ih =>
        change action :: rest =
          toSharedAction timed (fromSharedAction timed action) ::
            (rest.map (fromSharedAction timed)).map (toSharedAction timed)
        rw [toSharedAction_fromSharedAction]
        exact congrArg (List.cons action) ih
  conv_lhs => rw [hactions]
  exact run_shared timed state (actions.map (fromSharedAction timed))

end SealedTimeout
end Interaction
