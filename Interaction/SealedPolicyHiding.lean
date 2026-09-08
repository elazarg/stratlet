/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedHiding
import Interaction.SealedPolicies

/-! # Adaptive pre-disclosure hiding in the bounded policy game

The same policies may adapt to their respective views and invocation histories.
The finite invocation schedule is fixed and does not invoke the protected owner.
The observation law, including the environment's complete wire-pool view, is
independent of the protected registered values. The ideal service table is
excluded from every policy input and from the compared observation record.

This is a polling model: each principal remembers its own invocations, views,
and commands, not a globally numbered execution history. The analyst-level
joint observation record compares the environment and every potential attacker
but excludes the protected owner's private invocation history.
-/

noncomputable section

namespace Interaction.SealedProgram

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable {hiddenOwner : Principal}

/-- A joint record for comparing laws, not an additional policy observation. -/
def PolicyExecution.observations (hiddenOwner : Principal)
    (execution : PolicyExecution Principal Value) :
    EnvironmentView Principal Value ×
      ({ who : Principal // who ≠ hiddenOwner } → List (PlayerEntry Principal Value)) ×
        List (EnvironmentEntry Principal Value) :=
  (execution.native.environmentView,
    fun who => execution.principalHistory who, execution.environmentHistory)

structure PolicyExecution.HidingRelated (hiddenOwner : Principal)
    (left right : PolicyExecution Principal Value) : Prop where
  native : SealedProgram.HidingRelated hiddenOwner left.native right.native
  principalHistory : ∀ who, who ≠ hiddenOwner →
    left.principalHistory who = right.principalHistory who
  environmentHistory : left.environmentHistory = right.environmentHistory

theorem HidingRelated.environmentView_eq {left right : State Principal Value}
    (related : HidingRelated hiddenOwner left right) :
    left.environmentView = right.environmentView := by
  simp only [State.environmentView, related.pool, related.events]

theorem PolicyExecution.HidingRelated.observations_eq
    {left right : PolicyExecution Principal Value}
    (related : PolicyExecution.HidingRelated hiddenOwner left right) :
    left.observations hiddenOwner = right.observations hiddenOwner := by
  apply Prod.ext
  · exact related.native.environmentView_eq
  · apply Prod.ext
    · funext who
      exact related.principalHistory who who.property
    · exact related.environmentHistory

theorem PolicyExecution.HidingRelated.initial {left right : State Principal Value}
    (related : SealedProgram.HidingRelated hiddenOwner left right) :
    PolicyExecution.HidingRelated hiddenOwner (.initial left) (.initial right) :=
  ⟨related, fun _ _ => rfl, rfl⟩

theorem PolicyExecution.HidingRelated.playerStep
    [DecidableEq Principal] [DecidableEq Value]
    {left right : PolicyExecution Principal Value}
    (related : PolicyExecution.HidingRelated hiddenOwner left right)
    (program : SealedProgram Principal) (who : Principal) (hne : who ≠ hiddenOwner)
    (command : PlayerCommand Principal Value) :
    PolicyExecution.HidingRelated hiddenOwner
      (playerStep program who left command) (playerStep program who right command) := by
  refine ⟨?_, ?_, related.environmentHistory⟩
  · cases command with
    | register slot value => exact related.native.register who slot value hne
    | submit payload => exact related.native.submit who payload hne
    | replay id => exact related.native.replay who id
    | wait => exact related.native
  · intro other hother
    by_cases heq : other = who
    · subst other
      simp only [SealedProgram.playerStep, if_pos, related.principalHistory who hne,
        related.native.observe_eq who]
    · simp only [SealedProgram.playerStep, if_neg heq]
      exact related.principalHistory other hother

theorem PolicyExecution.HidingRelated.environmentStep
    [DecidableEq Principal] [DecidableEq Value]
    {left right : PolicyExecution Principal Value}
    (related : PolicyExecution.HidingRelated hiddenOwner left right)
    (program : SealedProgram Principal) (command : EnvironmentCommand Principal) :
    PolicyExecution.HidingRelated hiddenOwner
      (environmentStep program left command) (environmentStep program right command) := by
  refine ⟨?_, related.principalHistory, ?_⟩
  · cases command with
    | deliver observer id => exact related.native.deliver observer id
    | «include» id => exact related.native.includePending program id
    | wait => exact related.native
  · change left.environmentHistory ++ [⟨left.native.environmentView, command⟩] = _
    simp only [SealedProgram.environmentStep, related.environmentHistory,
      related.native.environmentView_eq]

/-- Adaptive policy behavior has the same joint observation law throughout
any fixed finite schedule that leaves the protected owner uninvoked. Both
explicit-rebroadcast capability selections are covered. -/
theorem runPolicies_hiding [DecidableEq Principal] [DecidableEq Value]
    (rebroadcast : Bool) (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value)
    (schedule : List (Invocation Principal))
    {left right : PolicyExecution Principal Value}
    (related : PolicyExecution.HidingRelated hiddenOwner left right)
    (hschedule : ∀ who, Invocation.player who ∈ schedule → who ≠ hiddenOwner) :
    (runPolicies rebroadcast program players environment schedule left).map
        (PolicyExecution.observations hiddenOwner) =
      (runPolicies rebroadcast program players environment schedule right).map
        (PolicyExecution.observations hiddenOwner) := by
  induction schedule generalizing left right with
  | nil => simp only [runPolicies, FinDist.map_pure, related.observations_eq]
  | cons invocation rest ih =>
      have hrest : ∀ who, Invocation.player who ∈ rest → who ≠ hiddenOwner :=
        fun who hmem => hschedule who (List.mem_cons_of_mem invocation hmem)
      cases invocation with
      | player who =>
          have hwho := hschedule who (List.mem_cons_self ..)
          simp only [runPolicies, invoke, FinDist.bind_map, FinDist.map_bind,
            related.principalHistory who hwho, related.native.observe_eq who]
          exact FinDist.bind_congr fun command _ =>
            ih (related.playerStep program who hwho command.1) hrest
      | environment =>
          simp only [runPolicies, invoke, FinDist.bind_map, FinDist.map_bind,
            related.environmentHistory, related.native.environmentView_eq]
          exact FinDist.bind_congr fun command _ =>
            ih (related.environmentStep program command) hrest

end Interaction.SealedProgram
