/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedTimeoutPolicies
import Interaction.SealedTimeoutLaws

/-! # Native execution witnesses for timed policies -/

namespace Interaction.SealedTimeout

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

private theorem applyNative_eq_run_trace
    (timed : SealedTimeout Principal) (initial : State Principal Value)
    (execution : PolicyExecution Principal Value) (action : Option (Action Principal Value))
    (hinvariant : execution.native = timed.run initial execution.nativeTrace) :
    (applyNative timed execution action).1 =
      timed.run initial (applyNative timed execution action).2 := by
  cases action <;> simp [applyNative, hinvariant, run_append]

private theorem invoke_eq_run_trace
    (timed : SealedTimeout Principal) (players : Principal → PlayerPolicy Principal Value)
    (environment : EnvironmentPolicy Principal Value)
    (initial : State Principal Value) (execution next : PolicyExecution Principal Value)
    (invocation : Invocation Principal)
    (hinvariant : execution.native = timed.run initial execution.nativeTrace)
    (hnext : next ∈ (invoke timed players environment execution invocation).support) :
    next.native = timed.run initial next.nativeTrace := by
  cases invocation with
  | player who =>
      simp only [invoke, FinDist.support_map, Set.mem_image] at hnext
      obtain ⟨command, _, rfl⟩ := hnext
      exact applyNative_eq_run_trace timed initial execution (command.toAction who) hinvariant
  | environment =>
      simp only [invoke, FinDist.support_map, Set.mem_image] at hnext
      obtain ⟨command, _, rfl⟩ := hnext
      exact applyNative_eq_run_trace timed initial execution command.toAction hinvariant

/-- Every supported policy-game outcome is the result of its recorded actual
native actions. The trace is proof-facing and is not an extra policy input. -/
theorem runPolicies_native_eq_run_trace
    (timed : SealedTimeout Principal) (players : Principal → PlayerPolicy Principal Value)
    (environment : EnvironmentPolicy Principal Value)
    (schedule : List (Invocation Principal)) (initial : State Principal Value)
    (execution : PolicyExecution Principal Value)
    (hmem : execution ∈ (runPolicies timed players environment schedule
      (PolicyExecution.initial initial)).support) :
    execution.native = timed.run initial execution.nativeTrace := by
  have invariant : ∀ (rest : List (Invocation Principal))
      (start result : PolicyExecution Principal Value),
      start.native = timed.run initial start.nativeTrace →
      result ∈ (runPolicies timed players environment rest start).support →
      result.native = timed.run initial result.nativeTrace := by
    intro rest
    induction rest with
    | nil =>
        intro start result hstart hresult
        have heq : result = start := by simpa [runPolicies] using hresult
        simpa [heq] using hstart
    | cons invocation rest ih =>
        intro start result hstart hresult
        simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at hresult
        obtain ⟨next, hnext, hresult⟩ := hresult
        exact ih next result
          (invoke_eq_run_trace timed players environment initial start next invocation hstart hnext)
          hresult
  exact invariant schedule (PolicyExecution.initial initial) execution rfl hmem

/-- An occupied ideal binding remains unchanged under every supported timed
policy execution, including expiration, malformed traffic, and replay. -/
theorem runPolicies_lookup_of_eq_some
    (timed : SealedTimeout Principal) (players : Principal → PlayerPolicy Principal Value)
    (environment : EnvironmentPolicy Principal Value)
    (schedule : List (Invocation Principal)) (initial : State Principal Value)
    (execution : PolicyExecution Principal Value)
    (handle : CommitmentHandle Principal Nat) (value : Value)
    (hlookup : initial.application.service.lookup handle = some value)
    (hmem : execution ∈ (runPolicies timed players environment schedule
      (PolicyExecution.initial initial)).support) :
    execution.native.application.service.lookup handle = some value := by
  rw [runPolicies_native_eq_run_trace timed players environment schedule initial execution hmem]
  exact run_lookup_of_eq_some timed initial execution.nativeTrace handle value hlookup

end Interaction.SealedTimeout
