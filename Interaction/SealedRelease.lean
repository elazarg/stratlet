/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedController
import Interaction.SealedPolicyHiding
import Interaction.SealedPolicyTrace

/-! # Hiding through a public release boundary

Protected-owner invocations are permitted. Before release, the specified
controller waits; afterward, execution continues and may disclose the value.
The compared law reads the first release-enabled snapshot of each complete
native trace, or its final snapshot if release never becomes enabled.
-/

noncomputable section

namespace Interaction.SealedProgram

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

def PlayerPolicy.WaitsBefore {rebroadcast : Bool}
    (policy : PlayerPolicy Principal Value rebroadcast)
    (release : List (Event Principal Value) → Bool) : Prop :=
  ∀ history view, release view.events = false →
    policy history view = FinDist.pure ⟨.wait, trivial⟩

theorem openingPolicy_waitsBefore [DecidableEq Principal]
    (rebroadcast : Bool) (program : SealedProgram Principal)
    (owner : Principal) (node : Nat) (value : Value) :
    (openingPolicy rebroadcast program owner node value).WaitsBefore
      (fun events => (openingHandle? program events owner node).isSome) := by
  intro history view hrelease
  have hnone : openingHandle? program view.events owner node = none := by
    cases hhandle : openingHandle? program view.events owner node with
    | none => rfl
    | some handle => simp [hhandle] at hrelease
  simp [openingPolicy, openingCommand, openingRequest?, hnone]

theorem PolicyExecution.HidingRelated.owner_wait
    [DecidableEq Principal] [DecidableEq Value]
    {hiddenOwner : Principal} {left right : PolicyExecution Principal Value}
    (related : PolicyExecution.HidingRelated hiddenOwner left right)
    (program : SealedProgram Principal) :
    PolicyExecution.HidingRelated hiddenOwner
      (SealedProgram.playerStep program hiddenOwner left .wait)
      (SealedProgram.playerStep program hiddenOwner right .wait) := by
  refine ⟨related.native, ?_, related.environmentHistory⟩
  intro who hne
  simp only [SealedProgram.playerStep, if_neg hne]
  exact related.principalHistory who hne

/-- Any readout invariant under the native hiding relation has the same law
at the first public release boundary. The readout is analysis data, not an
additional observation supplied to policies. Both full traces execute. -/
theorem tracePolicies_release_readout_congr
    [DecidableEq Principal] [DecidableEq Value]
    (rebroadcast : Bool) (program : SealedProgram Principal) (hiddenOwner : Principal)
    (first second : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value)
    (release : List (Event Principal Value) → Bool)
    (hplayers : ∀ who, who ≠ hiddenOwner → first who = second who)
    (hfirst : (first hiddenOwner).WaitsBefore release)
    (hsecond : (second hiddenOwner).WaitsBefore release)
    (schedule : List (Invocation Principal))
    {Result : Type*} (readout : PolicyExecution Principal Value → Result)
    (hreadout : ∀ {left right}, PolicyExecution.HidingRelated hiddenOwner left right →
      readout left = readout right)
    {left right : PolicyExecution Principal Value}
    (related : PolicyExecution.HidingRelated hiddenOwner left right) :
    ((tracePolicies rebroadcast program first environment schedule left).map
        (PolicyTrace.firstRelease release)).map readout =
      ((tracePolicies rebroadcast program second environment schedule right).map
        (PolicyTrace.firstRelease release)).map readout := by
  induction schedule generalizing left right with
  | nil =>
      simp only [tracePolicies, FinDist.map_pure, PolicyTrace.firstRelease, hreadout related]
  | cons invocation rest ih =>
      rw [tracePolicies_firstRelease_cons, tracePolicies_firstRelease_cons]
      have hpublic : release left.native.events = release right.native.events :=
        congrArg release related.native.events
      cases hrelease : release left.native.events with
      | true =>
          have hright : release right.native.events = true := hpublic.symm.trans hrelease
          simp only [hright, ↓reduceIte, FinDist.map_pure, hreadout related]
      | false =>
          have hright : release right.native.events = false := hpublic.symm.trans hrelease
          simp only [hright, Bool.false_eq_true, ↓reduceIte, FinDist.map_bind]
          cases invocation with
          | player who =>
              by_cases hwho : who = hiddenOwner
              · subst who
                rw [invoke, invoke, hfirst _ _ hrelease, hsecond _ _ hright]
                simp only [FinDist.map_pure, FinDist.pure_bind]
                exact ih (related.owner_wait program)
              · simp only [invoke, FinDist.bind_map, hplayers who hwho,
                  related.principalHistory who hwho, related.native.observe_eq who]
                exact FinDist.bind_congr fun command _ =>
                  ih (related.playerStep program who hwho command.1)
          | environment =>
              simp only [invoke, FinDist.bind_map, related.environmentHistory,
                related.native.environmentView_eq]
              exact FinDist.bind_congr fun command _ => ih (related.environmentStep program command)

/-- Exact observation-law equality at the first public release boundary.
The protected policies may differ privately but must wait before release.
Other player policies and the environment policy are unchanged. -/
theorem tracePolicies_hiding_beforeRelease
    [DecidableEq Principal] [DecidableEq Value]
    (rebroadcast : Bool) (program : SealedProgram Principal) (hiddenOwner : Principal)
    (first second : Principal → PlayerPolicy Principal Value rebroadcast)
    (environment : EnvironmentPolicy Principal Value)
    (release : List (Event Principal Value) → Bool)
    (hplayers : ∀ who, who ≠ hiddenOwner → first who = second who)
    (hfirst : (first hiddenOwner).WaitsBefore release)
    (hsecond : (second hiddenOwner).WaitsBefore release)
    (schedule : List (Invocation Principal))
    {left right : PolicyExecution Principal Value}
    (related : PolicyExecution.HidingRelated hiddenOwner left right) :
    ((tracePolicies rebroadcast program first environment schedule left).map
        (PolicyTrace.firstRelease release)).map (PolicyExecution.observations hiddenOwner) =
      ((tracePolicies rebroadcast program second environment schedule right).map
        (PolicyTrace.firstRelease release)).map (PolicyExecution.observations hiddenOwner) :=
  tracePolicies_release_readout_congr rebroadcast program hiddenOwner first second environment
    release hplayers hfirst hsecond schedule (PolicyExecution.observations hiddenOwner)
    (fun related => related.observations_eq) related

end Interaction.SealedProgram
