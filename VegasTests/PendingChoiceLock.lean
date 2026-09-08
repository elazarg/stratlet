/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.PendingRelease
import Interaction.SealedPolicyBinding

/-! # The opponent's value at the compiled release boundary

The extracted value is analysis data, not an added runtime observation.
Its outer `none` records that release was not reached; `some none` records
the source's nullable decline value at a reached release boundary.
The complete native executions still include their post-release suffixes.
-/

noncomputable section

namespace VegasTests.PendingChoiceLock

open Interaction Interaction.SealedProgram GameTheory GameTheory.Math.Probability
open VegasTests.PendingSource VegasTests.PendingExecution VegasTests.PendingPolicies
open VegasTests.PendingRelease

def choiceAtRelease (execution : PolicyExecution Player Value) : Option Value :=
  if release execution.native.events then execution.native.service.lookup (1, 1) else none

private theorem choiceAtRelease_congr {left right : PolicyExecution Player Value}
    (related : PolicyExecution.HidingRelated (0 : Player) left right) :
    choiceAtRelease left = choiceAtRelease right := by
  simp only [choiceAtRelease, related.native.events,
    related.native.service.1 (1, 1) (by decide)]

theorem choiceAtRelease_lookup {execution : PolicyExecution Player Value} {chosen : Value}
    (hchoice : choiceAtRelease execution = some chosen) :
    execution.native.service.lookup (1, 1) = some chosen := by
  unfold choiceAtRelease at hchoice
  split at hchoice
  · exact hchoice
  · contradiction

theorem choiceAtRelease_ready {execution : PolicyExecution Player Value} {chosen : Value}
    (hchoice : choiceAtRelease execution = some chosen) :
    release execution.native.events = true := by
  unfold choiceAtRelease at hchoice
  split at hchoice
  · assumption
  · contradiction

def choiceLaw (rebroadcast : Bool) (value : Value)
    (players : Profile (policySignature Player Value rebroadcast))
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player)) :
    FinDist (Option Value) :=
  ((controllerTraceLaw rebroadcast value players environment schedule).map
    (PolicyTrace.firstRelease release)).map choiceAtRelease

/-- The opponent's extracted value (including the unreached-release marker)
has one law independent of the protected owner's chosen source value. All
opponent and environment policies are unchanged and may adapt to native views. -/
theorem choiceLaw_independent (rebroadcast : Bool) (left right : Value)
    (players : Profile (policySignature Player Value rebroadcast))
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player)) :
    choiceLaw rebroadcast left players environment schedule =
      choiceLaw rebroadcast right players environment schedule := by
  unfold choiceLaw
  rw [controllerTraceLaw_firstRelease, controllerTraceLaw_firstRelease]
  apply tracePolicies_release_readout_congr (hiddenOwner := 0)
  · intro who hne
    simp only [openingProfile, Profile.update_of_ne _ _ hne]
  · simpa only [openingProfile, Profile.update_same, PlayerPolicy.WaitsBefore,
      release, openingReady] using openingPolicy_waitsBefore rebroadcast program 0 2 left
  · simpa only [openingProfile, Profile.update_same, PlayerPolicy.WaitsBefore,
      release, openingReady] using openingPolicy_waitsBefore rebroadcast program 0 2 right
  · exact fun related => choiceAtRelease_congr related
  · exact prepared_related left right

/-- Randomizing the protected source input yields a product law with the
opponent's extracted choice. This includes failure to reach release and does
not condition on later completion. -/
theorem mixed_choiceLaw_product (rebroadcast : Bool) (input : FinDist Value)
    (players : Profile (policySignature Player Value rebroadcast))
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player)) :
    (input.bind fun value =>
      (controllerTraceLaw rebroadcast value players environment schedule).map
        (fun trace => (value, choiceAtRelease (trace.firstRelease release)))) =
      input.product (choiceLaw rebroadcast none players environment schedule) := by
  change _ = input.bind (fun value =>
    (choiceLaw rebroadcast none players environment schedule).map (Prod.mk value))
  apply FinDist.bind_congr
  intro value _
  rw [← choiceLaw_independent rebroadcast value none players environment schedule]
  simp only [choiceLaw, FinDist.map_comp, Function.comp_def]

/-- Once extracted at release, the opponent's value is fixed through the
post-release suffix of this same complete trace, including arbitrary retries,
malformed messages, registrations, and withheld openings. -/
theorem choiceAtRelease_persists (rebroadcast : Bool) (value : Value)
    (players : Profile (policySignature Player Value rebroadcast))
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player))
    (trace : PolicyTrace Player Value)
    (htrace : trace ∈ (controllerTraceLaw rebroadcast value players environment schedule).support)
    (chosen : Value) (hchoice : choiceAtRelease (trace.firstRelease release) = some chosen) :
    trace.last.native.service.lookup (1, 1) = some chosen :=
  tracePolicies_firstRelease_lookup_persists rebroadcast program
    (controllerProfile rebroadcast value players) environment release
    (.player 0 :: .player 0 :: schedule) (PolicyExecution.initial initial) trace (1, 1) chosen
    htrace (choiceAtRelease_lookup hchoice)

/-- Reaching this compiled release barrier guarantees an actual occupied
opponent slot. Only an unreached release can produce the outer `none`. -/
theorem choiceAtRelease_some (rebroadcast : Bool) (value : Value)
    (players : Profile (policySignature Player Value rebroadcast))
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player))
    (trace : PolicyTrace Player Value)
    (htrace : trace ∈ (controllerTraceLaw rebroadcast value players environment schedule).support)
    (hrelease : release (trace.firstRelease release).native.events = true) :
    ∃ chosen, choiceAtRelease (trace.firstRelease release) = some chosen := by
  have invariant := tracePolicies_firstRelease_bindingInvariant rebroadcast program
    (controllerProfile rebroadcast value players) environment release
    (.player 0 :: .player 0 :: schedule) initial trace (BindingInvariant.empty program) htrace
  obtain ⟨chosen, hlookup⟩ := invariant.done_commit_lookup 1 1 [] rfl
    (release_requires_both _ hrelease).2
  exact ⟨chosen, by simp only [choiceAtRelease, hrelease, ↓reduceIte, hlookup]⟩

/-- On supported traces, outer absence records precisely an unreached release;
it never conflates that case with the legal nullable source value. -/
theorem choiceAtRelease_none_iff (rebroadcast : Bool) (value : Value)
    (players : Profile (policySignature Player Value rebroadcast))
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player))
    (trace : PolicyTrace Player Value)
    (htrace : trace ∈ (controllerTraceLaw rebroadcast value players environment schedule).support) :
    choiceAtRelease (trace.firstRelease release) = none ↔
      release (trace.firstRelease release).native.events = false := by
  constructor
  · intro hnone
    cases hrelease : release (trace.firstRelease release).native.events with
    | false => rfl
    | true =>
        obtain ⟨chosen, hchoice⟩ := choiceAtRelease_some rebroadcast value players environment
          schedule trace htrace hrelease
        rw [hnone] at hchoice
        contradiction
  · intro hrelease
    simp [choiceAtRelease, hrelease]

/-- The extracted value is the actual compiled source binding, not merely a
value stored in an unrelated private runtime slot. -/
theorem choiceAtRelease_source_field (rebroadcast : Bool) (value : Value)
    (players : Profile (policySignature Player Value rebroadcast))
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player))
    (trace : PolicyTrace Player Value)
    (htrace : trace ∈ (controllerTraceLaw rebroadcast value players environment schedule).support)
    (chosen : Value) (hchoice : choiceAtRelease (trace.firstRelease release) = some chosen) :
    ∃ cfg : Vegas.EventGraph.Config graph,
      graph.decodeSealed (.option .bool) (trace.firstRelease release).native = some cfg ∧
      Vegas.EventGraph.Reachable graph cfg ∧
      Vegas.EventGraph.Store.getAs cfg.store (graph.nodeTarget (node 1)) (.option .bool) =
        some chosen := by
  have invariant := tracePolicies_firstRelease_bindingInvariant rebroadcast program
    (controllerProfile rebroadcast value players) environment release
    (.player 0 :: .player 0 :: schedule) initial trace (BindingInvariant.empty program) htrace
  have haccepted := invariant.accepted_mem_of_done_commit 1 1 [] rfl
    (release_requires_both _ (choiceAtRelease_ready hchoice)).2
  obtain ⟨front, _, _, hcut⟩ := tracePolicies_firstRelease_prefix rebroadcast program
    (controllerProfile rebroadcast value players) environment release
    (.player 0 :: .player 0 :: schedule) (PolicyExecution.initial initial) trace htrace
  have hnative := runPolicies_native_eq_run_trace rebroadcast program
    (controllerProfile rebroadcast value players) environment front initial _ hcut
  have hnodup := run_eventNodes_nodup program initial
    (trace.firstRelease release).nativeTrace (by simp [initial, State.empty])
  rw [← hnative] at hnodup
  obtain ⟨cfg, hdecode, hreachable⟩ :=
    controllerTraceLaw_cut_reachable rebroadcast value players environment schedule trace htrace
  have hfield := Vegas.EventGraph.Graph.decodeSealed_accepted_getAs (G := graph) (.option .bool)
    (trace.firstRelease release).native cfg (node 1) (1, 1) hnodup haccepted hdecode
  exact ⟨cfg, hdecode, hreachable, hfield.2.trans (choiceAtRelease_lookup hchoice)⟩

/-- Any accepted later opening of the opponent's node discloses exactly the
value extracted before the honest owner's release. This does not force an
opening to occur. -/
theorem opened_eq_choiceAtRelease (rebroadcast : Bool) (value : Value)
    (players : Profile (policySignature Player Value rebroadcast))
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player))
    (trace : PolicyTrace Player Value)
    (htrace : trace ∈ (controllerTraceLaw rebroadcast value players environment schedule).support)
    (chosen disclosed : Value)
    (hchoice : choiceAtRelease (trace.firstRelease release) = some chosen)
    (hopened : Event.opened 3 disclosed ∈ trace.last.native.events) :
    disclosed = chosen := by
  have invariant := tracePolicies_last_bindingInvariant rebroadcast program
    (controllerProfile rebroadcast value players) environment
    (.player 0 :: .player 0 :: schedule) initial trace (BindingInvariant.empty program) htrace
  obtain ⟨owner, sourceNode, requires, hrule, hlookup⟩ := invariant.opened 3 disclosed hopened
  have hkind := congrArg SealedRule.kind (Option.some.inj hrule)
  change SealedRuleKind.reveal (1 : Player) 1 = .reveal owner sourceNode at hkind
  obtain ⟨rfl, rfl⟩ := SealedRuleKind.reveal.inj hkind
  exact Option.some.inj (hlookup.symm.trans
    (choiceAtRelease_persists rebroadcast value players environment schedule trace htrace
      chosen hchoice))

end VegasTests.PendingChoiceLock

/-- info: 'VegasTests.PendingChoiceLock.mixed_choiceLaw_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingChoiceLock.mixed_choiceLaw_product

/-- info: 'VegasTests.PendingChoiceLock.choiceAtRelease_source_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingChoiceLock.choiceAtRelease_source_field

/-- info: 'VegasTests.PendingChoiceLock.opened_eq_choiceAtRelease' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingChoiceLock.opened_eq_choiceAtRelease
