/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedController
import Interaction.SealedPolicyTrace

/-! # Trace law after the commit controller reaches its opening phase -/

noncomputable section

namespace Interaction.SealedProgram

open GameTheory GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

private theorem invoke_owner_history_length [DecidableEq Principal] [DecidableEq Value]
    (rebroadcast : Bool) (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value) (owner : Principal)
    (execution next : PolicyExecution Principal Value) (invocation : Invocation Principal)
    (hlength : 2 ≤ (execution.principalHistory owner).length)
    (hnext : next ∈
      (invoke rebroadcast program players environment execution invocation).support) :
    2 ≤ (next.principalHistory owner).length := by
  cases invocation with
  | environment =>
      simp only [invoke, FinDist.support_map, Set.mem_image] at hnext
      obtain ⟨command, _, rfl⟩ := hnext
      simpa using hlength
  | player who =>
      simp only [invoke, FinDist.support_map, Set.mem_image] at hnext
      obtain ⟨command, _, rfl⟩ := hnext
      by_cases hwho : owner = who
      · subst who
        simp only [playerStep_self_history, List.length_append, List.length_singleton]
        omega
      · rw [playerStep_other_history program who owner execution command.1 hwho]
        exact hlength

/-- Once the owner's first two invocations are recorded, its complete
commit/open policy and its opening-only policy induce exactly the same complete
trace law on every remaining fixed schedule. -/
theorem tracePolicies_commitOpen_eq_opening_of_two_le
    [DecidableEq Principal] [DecidableEq Value]
    (rebroadcast : Bool) (program : SealedProgram Principal)
    (environment : EnvironmentPolicy Principal Value)
    (schedule : List (Invocation Principal)) (execution : PolicyExecution Principal Value)
    (players : Profile (policySignature Principal Value rebroadcast))
    (owner : Principal) (commitNode revealNode : Nat) (value : Value)
    (hlength : 2 ≤ (execution.principalHistory owner).length) :
    tracePolicies rebroadcast program
        (Profile.update (sig := policySignature Principal Value rebroadcast) players owner
          (commitOpenPolicy rebroadcast program owner commitNode revealNode value))
        environment schedule execution =
      tracePolicies rebroadcast program
        (Profile.update (sig := policySignature Principal Value rebroadcast) players owner
          (openingPolicy rebroadcast program owner revealNode value))
        environment schedule execution := by
  induction schedule generalizing execution with
  | nil => rfl
  | cons invocation rest ih =>
      simp only [tracePolicies]
      have hinvoke :
          invoke rebroadcast program
              (Profile.update (sig := policySignature Principal Value rebroadcast) players owner
                (commitOpenPolicy rebroadcast program owner commitNode revealNode value))
              environment execution invocation =
            invoke rebroadcast program
              (Profile.update (sig := policySignature Principal Value rebroadcast) players owner
                (openingPolicy rebroadcast program owner revealNode value))
              environment execution invocation := by
        cases invocation with
        | environment => rfl
        | player who =>
            by_cases hwho : who = owner
            · subst who
              simp only [invoke, Profile.update_same]
              unfold commitOpenPolicy
              split <;> try omega
              rfl
            · simp [invoke, Profile.update_of_ne _ _ hwho]
      rw [hinvoke]
      exact FinDist.bind_congr fun next hnext => by
        rw [ih next (invoke_owner_history_length rebroadcast program _ environment owner
          execution next invocation hlength hnext)]

end Interaction.SealedProgram
