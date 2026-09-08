/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedPolicies

/-! # Complete native policy traces and public release readouts

The trace recorder calls the same native policy invocation function as the
bounded game, retaining the initial and every post-invocation snapshot. Its
last-snapshot law is exactly the game's execution law.

The first-release readout selects a snapshot from a completed trace. It does
not stop execution, change any policy input, or condition on release occurring.
When the public predicate never holds, the readout selects the last snapshot.
-/

noncomputable section

namespace Interaction.SealedProgram

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

inductive PolicyTrace (Principal : Type uPrincipal) (Value : Type uValue) where
  | finish (execution : PolicyExecution Principal Value)
  | step (execution : PolicyExecution Principal Value) (tail : PolicyTrace Principal Value)

def PolicyTrace.last : PolicyTrace Principal Value → PolicyExecution Principal Value
  | .finish execution => execution
  | .step _ tail => tail.last

/-- The earliest release-enabled snapshot, or the last snapshot if the
predicate never holds. No later snapshot influences a selected prefix. -/
def PolicyTrace.firstRelease (release : List (Event Principal Value) → Bool) :
    PolicyTrace Principal Value → PolicyExecution Principal Value
  | .finish execution => execution
  | .step execution tail =>
      if release execution.native.events then execution else tail.firstRelease release

def tracePolicies [DecidableEq Principal] [DecidableEq Value] (rebroadcast : Bool)
    (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value) :
    List (Invocation Principal) → PolicyExecution Principal Value →
      FinDist (PolicyTrace Principal Value)
  | [], execution => FinDist.pure (.finish execution)
  | invocation :: rest, execution =>
      (invoke rebroadcast program players environment execution invocation).bind fun next =>
        (tracePolicies rebroadcast program players environment rest next).map (.step execution)

/-- Recording snapshots preserves the actual native game law exactly. -/
theorem tracePolicies_last [DecidableEq Principal] [DecidableEq Value]
    (rebroadcast : Bool) (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value)
    (schedule : List (Invocation Principal)) (execution : PolicyExecution Principal Value) :
    (tracePolicies rebroadcast program players environment schedule execution).map
        PolicyTrace.last =
      runPolicies rebroadcast program players environment schedule execution := by
  induction schedule generalizing execution with
  | nil => simp [tracePolicies, runPolicies, PolicyTrace.last]
  | cons invocation rest ih =>
      simp only [tracePolicies, FinDist.map_bind, FinDist.map_comp, Function.comp_def,
        PolicyTrace.last, ih, runPolicies]

theorem tracePolicies_firstRelease_cons [DecidableEq Principal] [DecidableEq Value]
    (rebroadcast : Bool) (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value)
    (release : List (Event Principal Value) → Bool)
    (invocation : Invocation Principal) (rest : List (Invocation Principal))
    (execution : PolicyExecution Principal Value) :
    (tracePolicies rebroadcast program players environment (invocation :: rest) execution).map
        (PolicyTrace.firstRelease release) =
      if release execution.native.events then FinDist.pure execution else
        (invoke rebroadcast program players environment execution invocation).bind fun next =>
          (tracePolicies rebroadcast program players environment rest next).map
            (PolicyTrace.firstRelease release) := by
  cases hrelease : release execution.native.events <;>
    simp [tracePolicies, PolicyTrace.firstRelease, hrelease, Function.comp_def]

/-- Every selected snapshot occurs in the support of execution of an actual
invocation prefix, using unchanged player/environment policies. -/
theorem tracePolicies_firstRelease_prefix [DecidableEq Principal] [DecidableEq Value]
    (rebroadcast : Bool) (program : SealedProgram Principal)
    (players : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value)
    (release : List (Event Principal Value) → Bool)
    (schedule : List (Invocation Principal)) (execution : PolicyExecution Principal Value)
    (trace : PolicyTrace Principal Value)
    (htrace : trace ∈
      (tracePolicies rebroadcast program players environment schedule execution).support) :
    ∃ front suffix, schedule = front ++ suffix ∧
      trace.firstRelease release ∈
        (runPolicies rebroadcast program players environment front execution).support := by
  induction schedule generalizing execution trace with
  | nil =>
      have heq : trace = .finish execution := by simpa [tracePolicies] using htrace
      subst trace
      exact ⟨[], [], rfl, FinDist.mem_support_pure.mpr rfl⟩
  | cons invocation rest ih =>
      simp only [tracePolicies, FinDist.support_bind, Set.mem_iUnion,
        FinDist.support_map, Set.mem_image] at htrace
      obtain ⟨next, hnext, tail, htail, rfl⟩ := htrace
      cases hrelease : release execution.native.events with
      | true =>
          refine ⟨[], invocation :: rest, rfl, ?_⟩
          simp [runPolicies, PolicyTrace.firstRelease, hrelease]
      | false =>
          obtain ⟨front, suffix, hsplit, hprefix⟩ := ih next tail htail
          refine ⟨invocation :: front, suffix, by simp [hsplit], ?_⟩
          simp only [PolicyTrace.firstRelease, hrelease, Bool.false_eq_true, ↓reduceIte,
            runPolicies, FinDist.support_bind, Set.mem_iUnion]
          exact ⟨next, hnext, hprefix⟩

end Interaction.SealedProgram
