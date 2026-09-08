/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedPolicies

/-! # Laws for observation-local sealed-message policies -/

noncomputable section

namespace Interaction.SealedProgram

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

def enableRebroadcastCommand :
    { command : PlayerCommand Principal Value // command.allowed false } →
      { command : PlayerCommand Principal Value // command.allowed true }
  | ⟨command, allowed⟩ => ⟨command, by
      cases command with
      | replay id => simp [PlayerCommand.allowed] at allowed
      | register | submit | wait => trivial⟩

def enableRebroadcastPolicy (policy : PlayerPolicy Principal Value false) :
    PlayerPolicy Principal Value true :=
  fun history view => (policy history view).map enableRebroadcastCommand

@[simp] theorem enableRebroadcastCommand_value
    (command : { command : PlayerCommand Principal Value // command.allowed false }) :
    (enableRebroadcastCommand command).1 = command.1 := by
  cases command
  rfl

theorem invoke_enableRebroadcast [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value false)
    (environment : EnvironmentPolicy Principal Value)
    (execution : PolicyExecution Principal Value) (invocation : Invocation Principal) :
    invoke true program (fun who => enableRebroadcastPolicy (players who)) environment
        execution invocation =
      invoke false program players environment execution invocation := by
  cases invocation with
  | environment => rfl
  | player who =>
      rw [invoke, enableRebroadcastPolicy, FinDist.map_comp]
      congr 1

theorem runPolicies_enableRebroadcast [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value false)
    (environment : EnvironmentPolicy Principal Value)
    (schedule : List (Invocation Principal)) (execution : PolicyExecution Principal Value) :
    runPolicies true program (fun who => enableRebroadcastPolicy (players who)) environment
        schedule execution =
      runPolicies false program players environment schedule execution := by
  induction schedule generalizing execution with
  | nil => rfl
  | cons invocation rest ih =>
      simp only [runPolicies]
      rw [invoke_enableRebroadcast]
      exact FinDist.bind_congr fun next _ => ih next

theorem policyGame_enableRebroadcast [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value false)
    (environment : EnvironmentPolicy Principal Value)
    (schedule : List (Invocation Principal)) (initial : State Principal Value) :
    (policyGame true program environment schedule initial).play
        (fun who => enableRebroadcastPolicy (players who)) =
      (policyGame false program environment schedule initial).play players :=
  runPolicies_enableRebroadcast program players environment schedule _

/-- Only policies actually invoked by the fixed schedule affect execution. -/
theorem runPolicies_congr_on_schedule [DecidableEq Principal] [DecidableEq Value]
    (rebroadcast : Bool) (program : SealedProgram Principal)
    (first second : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value)
    (schedule : List (Invocation Principal)) (execution : PolicyExecution Principal Value)
    (hplayers : ∀ who, Invocation.player who ∈ schedule → first who = second who) :
    runPolicies rebroadcast program first environment schedule execution =
      runPolicies rebroadcast program second environment schedule execution := by
  induction schedule generalizing execution with
  | nil => rfl
  | cons invocation rest ih =>
      have hrest : ∀ who, Invocation.player who ∈ rest → first who = second who :=
        fun who hmem => hplayers who (List.mem_cons_of_mem invocation hmem)
      have hinvoke : invoke rebroadcast program first environment execution invocation =
          invoke rebroadcast program second environment execution invocation := by
        cases invocation with
        | environment => rfl
        | player who => simp only [invoke, hplayers who (List.mem_cons_self ..)]
      simp only [runPolicies, hinvoke]
      exact FinDist.bind_congr fun next _ => ih next hrest

theorem playerStep_other_history [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (who other : Principal)
    (execution : PolicyExecution Principal Value) (command : PlayerCommand Principal Value)
    (hne : other ≠ who) :
    (playerStep program who execution command).principalHistory other =
      execution.principalHistory other := by
  simp [playerStep, hne]

@[simp] theorem playerStep_self_history [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (who : Principal)
    (execution : PolicyExecution Principal Value) (command : PlayerCommand Principal Value) :
    (playerStep program who execution command).principalHistory who =
      execution.principalHistory who ++ [⟨execution.native.observe who, command⟩] := by
  simp [playerStep]

@[simp] theorem environmentStep_principalHistory [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (execution : PolicyExecution Principal Value)
    (command : EnvironmentCommand Principal) (who : Principal) :
    (environmentStep program execution command).principalHistory who =
      execution.principalHistory who := rfl

@[simp] theorem playerStep_native_eq_run_trace [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (initial : State Principal Value)
    (who : Principal) (execution : PolicyExecution Principal Value)
    (command : PlayerCommand Principal Value)
    (hinvariant : execution.native = run program initial execution.nativeTrace) :
    (playerStep program who execution command).native =
      run program initial (playerStep program who execution command).nativeTrace := by
  cases command <;> simp [playerStep, applyNative, PlayerCommand.toAction,
    hinvariant, run_append]

@[simp] theorem environmentStep_native_eq_run_trace
    [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (initial : State Principal Value)
    (execution : PolicyExecution Principal Value) (command : EnvironmentCommand Principal)
    (hinvariant : execution.native = run program initial execution.nativeTrace) :
    (environmentStep program execution command).native =
      run program initial (environmentStep program execution command).nativeTrace := by
  cases command <;> simp [environmentStep, applyNative, EnvironmentCommand.toAction,
    hinvariant, run_append]

private theorem invoke_native_eq_run_trace [DecidableEq Principal] [DecidableEq Value]
    (rebroadcast : Bool) (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value)
    (initial : State Principal Value) (execution next : PolicyExecution Principal Value)
    (invocation : Invocation Principal)
    (hinvariant : execution.native = run program initial execution.nativeTrace)
    (hnext : next ∈ (invoke rebroadcast program players environment execution invocation).support) :
    next.native = run program initial next.nativeTrace := by
  cases invocation with
  | player who =>
      simp only [invoke, FinDist.support_map, Set.mem_image] at hnext
      obtain ⟨command, _, rfl⟩ := hnext
      exact playerStep_native_eq_run_trace program initial who execution command.1 hinvariant
  | environment =>
      simp only [invoke, FinDist.support_map, Set.mem_image] at hnext
      obtain ⟨command, _, rfl⟩ := hnext
      exact environmentStep_native_eq_run_trace program initial execution command hinvariant

theorem runPolicies_native_eq_run_trace [DecidableEq Principal] [DecidableEq Value]
    (rebroadcast : Bool) (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value)
    (schedule : List (Invocation Principal)) (initial : State Principal Value)
    (execution : PolicyExecution Principal Value)
    (hmem : execution ∈ (runPolicies rebroadcast program players environment schedule
      (PolicyExecution.initial initial)).support) :
    execution.native = run program initial execution.nativeTrace := by
  have general : ∀ (rest : List (Invocation Principal))
      (start result : PolicyExecution Principal Value),
      start.native = run program initial start.nativeTrace →
      result ∈ (runPolicies rebroadcast program players environment rest start).support →
      result.native = run program initial result.nativeTrace := by
    intro rest
    induction rest with
    | nil =>
        intro start result hinvariant hresult
        have heq : result = start := by simpa [runPolicies] using hresult
        simpa [heq] using hinvariant
    | cons invocation rest ih =>
        intro start result hinvariant hresult
        simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at hresult
        obtain ⟨next, hnext, hresult⟩ := hresult
        exact ih next result
          (invoke_native_eq_run_trace rebroadcast program players environment initial
            start next invocation hinvariant hnext)
          hresult
  exact general schedule (PolicyExecution.initial initial) execution rfl hmem

end Interaction.SealedProgram
