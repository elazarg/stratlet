/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedRelease
import Interaction.SealedControllerTrace
import Vegas.Game.SealedRelease
import VegasTests.PendingPolicies

/-! # The compiled release controller in complete native policy executions

The protected owner registers and submits from the empty state, then polls
the existing public-view opening controller. Invocation schedules may continue
to invoke that owner. Hiding concerns the first release-enabled snapshot of a
complete trace, not the observations after an opening is submitted.
-/

namespace VegasTests.PendingRelease

open Interaction Interaction.SealedProgram GameTheory GameTheory.Math.Probability
open VegasTests.PendingSource VegasTests.PendingExecution VegasTests.PendingPolicies

def release (events : List (Event Player Value)) : Bool :=
  openingReady program events 0 2

theorem release_requires_both (events : List (Event Player Value))
    (hrelease : release events = true) :
    done events 0 = true ∧ done events 1 = true := by
  let view : View Player Value :=
    ⟨(MessagePool.empty Player (Payload Player Value)).observe 0, events⟩
  have hcommand := (openingCommand_ne_wait_iff_ready program 0 2 (none : Value) view).2
    hrelease
  have hprereqs := sealedFragment.openingCommand_prerequisites 0 (node 2) none view hcommand
  exact ⟨hprereqs (node 0) (by rw [node2_prereqs]; simp),
    hprereqs (node 1) (by rw [node2_prereqs]; simp)⟩

noncomputable section

def controllerProfile (rebroadcast : Bool) (value : Value)
    (players : Profile (policySignature Player Value rebroadcast)) :
    Profile (policySignature Player Value rebroadcast) :=
  Profile.update players 0 (commitOpenPolicy rebroadcast program 0 0 2 value)

def openingProfile (rebroadcast : Bool) (value : Value)
    (players : Profile (policySignature Player Value rebroadcast)) :
    Profile (policySignature Player Value rebroadcast) :=
  Profile.update players 0 (openingPolicy rebroadcast program 0 2 value)

def controllerTraceLaw (rebroadcast : Bool) (value : Value)
    (players : Profile (policySignature Player Value rebroadcast))
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player)) :
    FinDist (PolicyTrace Player Value) :=
  tracePolicies rebroadcast program (controllerProfile rebroadcast value players) environment
    (.player 0 :: .player 0 :: schedule) (PolicyExecution.initial initial)

/-- The trace law is a recording of the ordinary native game, including its
post-release suffix and any further owner invocations. -/
theorem controllerTraceLaw_last (rebroadcast : Bool) (value : Value)
    (players : Profile (policySignature Player Value rebroadcast))
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player)) :
    (controllerTraceLaw rebroadcast value players environment schedule).map PolicyTrace.last =
      (policyGame rebroadcast program environment (.player 0 :: .player 0 :: schedule) initial).play
        (controllerProfile rebroadcast value players) :=
  tracePolicies_last rebroadcast program _ environment _ _

theorem openingTraceLaw_hiding (rebroadcast : Bool) (left right : Value)
    (players : Profile (policySignature Player Value rebroadcast))
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player)) :
    ((tracePolicies rebroadcast program (openingProfile rebroadcast left players)
      environment schedule (prepared left)).map (PolicyTrace.firstRelease release)).map
        (PolicyExecution.observations 0) =
      ((tracePolicies rebroadcast program (openingProfile rebroadcast right players)
        environment schedule (prepared right)).map (PolicyTrace.firstRelease release)).map
          (PolicyExecution.observations 0) := by
  apply tracePolicies_hiding_beforeRelease
  · intro who hne
    simp only [openingProfile, Profile.update_of_ne _ _ hne]
  · simpa only [openingProfile, Profile.update_same, PlayerPolicy.WaitsBefore,
      release, openingReady] using
      openingPolicy_waitsBefore rebroadcast program 0 2 left
  · simpa only [openingProfile, Profile.update_same, PlayerPolicy.WaitsBefore,
      release, openingReady] using
      openingPolicy_waitsBefore rebroadcast program 0 2 right
  · exact prepared_related left right

theorem controllerTraceLaw_firstRelease (rebroadcast : Bool) (value : Value)
    (players : Profile (policySignature Player Value rebroadcast))
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player)) :
    (controllerTraceLaw rebroadcast value players environment schedule).map
        (PolicyTrace.firstRelease release) =
      (tracePolicies rebroadcast program (openingProfile rebroadcast value players)
        environment schedule (prepared value)).map (PolicyTrace.firstRelease release) := by
  simp only [controllerTraceLaw, controllerProfile, tracePolicies, invoke, Profile.update_same,
    commitOpenPolicy, PolicyExecution.initial, playerStep, List.length_nil, List.length_append,
    List.length_cons, ite_true, FinDist.map_pure, FinDist.pure_bind,
    FinDist.map_comp, Function.comp_def]
  change (tracePolicies rebroadcast program
    (Profile.update (sig := policySignature Player Value rebroadcast) players 0
      (commitOpenPolicy rebroadcast program 0 0 2 value)) environment schedule
        (prepared value)).map (PolicyTrace.firstRelease release) = _
  rw [tracePolicies_commitOpen_eq_opening_of_two_le rebroadcast program environment schedule
    (prepared value) players 0 0 2 value (by simp [prepared, playerStep, PolicyExecution.initial])]
  rfl

/-- Empty-state controller runs have the same observations at the first
compiled release boundary for every fixed schedule, including owner polls.
Both full executions continue after the compared snapshot. -/
theorem controllerTraceLaw_hiding (rebroadcast : Bool) (left right : Value)
    (players : Profile (policySignature Player Value rebroadcast))
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player)) :
    ((controllerTraceLaw rebroadcast left players environment schedule).map
      (PolicyTrace.firstRelease release)).map (PolicyExecution.observations 0) =
      ((controllerTraceLaw rebroadcast right players environment schedule).map
        (PolicyTrace.firstRelease release)).map (PolicyExecution.observations 0) := by
  rw [controllerTraceLaw_firstRelease, controllerTraceLaw_firstRelease]
  exact openingTraceLaw_hiding rebroadcast left right players environment schedule

/-- Every cutoff is a genuine policy execution prefix of the compiled checked
source, not a fabricated state in a stopped runtime. -/
theorem controllerTraceLaw_cut_reachable (rebroadcast : Bool) (value : Value)
    (players : Profile (policySignature Player Value rebroadcast))
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player))
    (trace : PolicyTrace Player Value)
    (htrace : trace ∈ (controllerTraceLaw rebroadcast value players environment schedule).support) :
    ∃ cfg : Vegas.EventGraph.Config graph,
      graph.decodeSealed (.option .bool) (trace.firstRelease release).native = some cfg ∧
        Vegas.EventGraph.Reachable graph cfg := by
  obtain ⟨front, _suffix, _hsplit, hcut⟩ := tracePolicies_firstRelease_prefix
    rebroadcast program (controllerProfile rebroadcast value players) environment release
      (.player 0 :: .player 0 :: schedule) (PolicyExecution.initial initial) trace htrace
  obtain ⟨cfg, hdecode, hreachable, _⟩ := source.sealed_policy_source
    (.option .bool) sealedFragment rebroadcast _ environment front (trace.firstRelease release) hcut
  exact ⟨cfg, hdecode, hreachable⟩

end

end VegasTests.PendingRelease

/-- info: 'Interaction.SealedProgram.tracePolicies_hiding_beforeRelease' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedProgram.tracePolicies_hiding_beforeRelease

/-- info: 'VegasTests.PendingRelease.controllerTraceLaw_hiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingRelease.controllerTraceLaw_hiding

/-- info: 'Vegas.EventGraph.SealedFragment.openingCommand_prerequisites' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.openingCommand_prerequisites
