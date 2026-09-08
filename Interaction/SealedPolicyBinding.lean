/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedBinding
import Interaction.SealedPolicyLaws
import Interaction.SealedPolicyTrace

/-! # Commitment persistence in complete policy traces

An occupied ideal-service slot at any selected release snapshot retains the
same value at the end of that very execution trace.  The release predicate is
arbitrary; no monotonicity or progress property is required.
-/

noncomputable section

namespace Interaction.SealedProgram

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- The native binding invariant lifts through every supported bounded policy
execution from an invariant initial state. -/
theorem runPolicies_bindingInvariant (rebroadcast : Bool)
    (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value)
    (schedule : List (Invocation Principal)) (state : State Principal Value)
    (execution : PolicyExecution Principal Value)
    (invariant : BindingInvariant program state)
    (hmem : execution ∈
      (runPolicies rebroadcast program players environment schedule
        (PolicyExecution.initial state)).support) :
    BindingInvariant program execution.native := by
  have hrun := runPolicies_native_eq_run_trace rebroadcast program players environment
    schedule state execution hmem
  rw [hrun]
  exact invariant.run execution.nativeTrace

/-- Every first-release snapshot selected from an actual complete policy trace
satisfies the binding invariant when the initial native state does. -/
theorem tracePolicies_firstRelease_bindingInvariant (rebroadcast : Bool)
    (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value)
    (release : List (Event Principal Value) → Bool)
    (schedule : List (Invocation Principal)) (state : State Principal Value)
    (trace : PolicyTrace Principal Value)
    (invariant : BindingInvariant program state)
    (htrace : trace ∈
      (tracePolicies rebroadcast program players environment schedule
        (PolicyExecution.initial state)).support) :
    BindingInvariant program (trace.firstRelease release).native := by
  obtain ⟨front, suffix, _, hprefix⟩ :=
    tracePolicies_firstRelease_prefix rebroadcast program players environment release
      schedule (PolicyExecution.initial state) trace htrace
  exact runPolicies_bindingInvariant rebroadcast program players environment front state
    (trace.firstRelease release) invariant hprefix

omit [DecidableEq Principal] [DecidableEq Value] in
private theorem PolicyTrace.firstRelease_false_eq_last
    (trace : PolicyTrace Principal Value) :
    trace.firstRelease (fun _ => false) = trace.last := by
  induction trace with
  | finish execution => rfl
  | step execution tail ih => simpa [PolicyTrace.firstRelease, PolicyTrace.last] using ih

/-- The last snapshot of every supported complete policy trace also satisfies
the initial state's binding invariant. -/
theorem tracePolicies_last_bindingInvariant (rebroadcast : Bool)
    (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value)
    (schedule : List (Invocation Principal)) (state : State Principal Value)
    (trace : PolicyTrace Principal Value)
    (invariant : BindingInvariant program state)
    (htrace : trace ∈
      (tracePolicies rebroadcast program players environment schedule
        (PolicyExecution.initial state)).support) :
    BindingInvariant program trace.last.native := by
  rw [← trace.firstRelease_false_eq_last]
  exact tracePolicies_firstRelease_bindingInvariant rebroadcast program players environment
    (fun _ => false) schedule state trace invariant htrace

/-- Every supported policy invocation preserves an already occupied slot. -/
theorem invoke_lookup_of_eq_some (rebroadcast : Bool)
    (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value)
    (execution next : PolicyExecution Principal Value)
    (invocation : Invocation Principal)
    (handle : CommitmentHandle Principal Nat) (value : Value)
    (hlookup : execution.native.service.lookup handle = some value)
    (hnext : next ∈
      (invoke rebroadcast program players environment execution invocation).support) :
    next.native.service.lookup handle = some value := by
  cases invocation with
  | player who =>
      simp only [invoke, FinDist.support_map, Set.mem_image] at hnext
      obtain ⟨command, _, rfl⟩ := hnext
      cases command with
      | mk command allowed =>
        cases command with
        | wait => exact hlookup
        | register slot replacement =>
            exact step_lookup_of_eq_some program execution.native
              (.register who slot replacement) handle value hlookup
        | submit payload =>
            exact step_lookup_of_eq_some program execution.native
              (.submit who payload) handle value hlookup
        | replay id =>
            exact step_lookup_of_eq_some program execution.native
              (.replay who id) handle value hlookup
  | environment =>
      simp only [invoke, FinDist.support_map, Set.mem_image] at hnext
      obtain ⟨command, _, rfl⟩ := hnext
      cases command with
      | wait => exact hlookup
      | deliver observer id =>
          exact step_lookup_of_eq_some program execution.native
            (.deliver observer id) handle value hlookup
      | «include» id =>
          exact step_lookup_of_eq_some program execution.native
            (.include id) handle value hlookup

/-- An occupied slot at the start of a supported complete trace has the same
value in its last snapshot. -/
theorem tracePolicies_last_lookup_of_eq_some (rebroadcast : Bool)
    (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value)
    (schedule : List (Invocation Principal))
    (initial : PolicyExecution Principal Value) (trace : PolicyTrace Principal Value)
    (handle : CommitmentHandle Principal Nat) (value : Value)
    (htrace : trace ∈
      (tracePolicies rebroadcast program players environment schedule initial).support)
    (hlookup : initial.native.service.lookup handle = some value) :
    trace.last.native.service.lookup handle = some value := by
  induction schedule generalizing initial trace with
  | nil =>
      have htrace' : trace = .finish initial := by simpa [tracePolicies] using htrace
      subst trace
      exact hlookup
  | cons invocation rest ih =>
      simp only [tracePolicies, FinDist.support_bind, Set.mem_iUnion,
        FinDist.support_map, Set.mem_image] at htrace
      obtain ⟨next, hnext, tail, htail, rfl⟩ := htrace
      exact ih next tail htail
        (invoke_lookup_of_eq_some rebroadcast program players environment initial next
          invocation handle value hlookup hnext)

/-- A value present at the first release-selected snapshot persists to the
last snapshot of the same supported complete policy trace. -/
theorem tracePolicies_firstRelease_lookup_persists (rebroadcast : Bool)
    (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value)
    (release : List (Event Principal Value) → Bool)
    (schedule : List (Invocation Principal))
    (initial : PolicyExecution Principal Value) (trace : PolicyTrace Principal Value)
    (handle : CommitmentHandle Principal Nat) (value : Value)
    (htrace : trace ∈
      (tracePolicies rebroadcast program players environment schedule initial).support)
    (hlookup : (trace.firstRelease release).native.service.lookup handle = some value) :
    trace.last.native.service.lookup handle = some value := by
  induction schedule generalizing initial trace with
  | nil =>
      have htrace' : trace = .finish initial := by simpa [tracePolicies] using htrace
      subst trace
      exact hlookup
  | cons invocation rest ih =>
      simp only [tracePolicies, FinDist.support_bind, Set.mem_iUnion,
        FinDist.support_map, Set.mem_image] at htrace
      obtain ⟨next, hnext, tail, htail, rfl⟩ := htrace
      cases hrelease : release initial.native.events with
      | false =>
          exact ih next tail htail (by
            simpa [PolicyTrace.firstRelease, hrelease] using hlookup)
      | true =>
          have hinitial : initial.native.service.lookup handle = some value := by
            simpa [PolicyTrace.firstRelease, hrelease] using hlookup
          have hnextLookup := invoke_lookup_of_eq_some rebroadcast program players environment
            initial next invocation handle value hinitial hnext
          exact tracePolicies_last_lookup_of_eq_some rebroadcast program players environment
            rest next tail handle value htail hnextLookup

end Interaction.SealedProgram
