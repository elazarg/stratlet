/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureApplicationPolicies

/-! # Honest execution of the disclosure application -/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Vegas EventGraph Interaction GameTheory GameTheory.Math.Probability

variable {window : Nat}

private theorem responseGraphPrerequisites_eq :
    graph.publicationPrerequisites (node 6) (node 7) = [2, 3, 5, 0, 1, 4] := by
  simpa only [responsePrerequisites, responseEndpoint_requires] using
    responsePrerequisites_eq

private theorem openingEncoding_private (command : Nat × Bool) :
    (openingCommandEncoding (window := window)).decode
      ((.privateCommand command) : (application window).PlayerCommand) = none := rfl

private theorem openingEncoding_bind (handle : CommitmentHandle TestPlayer Nat) :
    (openingCommandEncoding (window := window)).decode
      ((.submit (.bind handle)) : (application window).PlayerCommand) = none := rfl

private theorem application_privateStep_eq :
    (application window).privateStep = privateStep := rfl

private theorem application_environmentStep_eq :
    (application window).environmentStep = environmentStep := rfl

private theorem application_handle_eq :
    (application window).handle = handle window := rfl

private theorem application_observePlayer_eq :
    (application window).observePlayer = fun state _ => state.observe := rfl

private theorem application_observeEnvironment_eq :
    (application window).observeEnvironment = observe := rfl

def policyData? (execution : (application window).PolicyExecution) : Option RunData :=
  if execution.native.application.outcome?.isSome then
    some execution.native.application.data
  else none

/-- The native checkpoint after registration, binding, marker, and public chance.
Histories are the observations and commands recorded by those actual steps. -/
private def afterSignal (window : Nat) (secret signal : Bool) :
    (application window).PolicyExecution :=
  let initialState := initial window
  let prepared := { initialState with application := privateStep empty 0 (0, secret) }
  let submitted := { prepared with pool := (prepared.pool.submit 0 (.bind (0, 0))).2 }
  let bound := (application window).includePending submitted (0, 0)
  let marked := { bound with application := { bound.application with markerDone := true } }
  { native := { marked with application :=
      { marked.application with signal := some signal, signalAt := marked.application.clock } }
    principalHistory := fun who => if who = 0 then
      [⟨MessageApplication.State.observe (application window) initialState 0,
          .privateCommand (0, secret)⟩,
        ⟨MessageApplication.State.observe (application window) prepared 0,
          .submit (.bind (0, 0))⟩] else []
    environmentHistory :=
      [⟨MessageApplication.State.environmentView (application window) submitted, .include (0, 0)⟩,
        ⟨MessageApplication.State.environmentView (application window) bound, .application .marker⟩,
        ⟨MessageApplication.State.environmentView (application window) marked,
          .application .sample⟩]
    nativeTrace :=
      [.privateCommand 0 (0, secret), .submit 0 (.bind (0, 0)), .include (0, 0),
        .environment .marker, .environment .sample] }

private theorem prefix_law (window : Nat) (secret : Bool)
    (complete : Bool → Bool → Bool) (response : Bool → Option Bool → Bool) :
    (application window).runPolicies (honestPlayers secret complete response) honestEnvironment
      [.player 0, .player 0, .environment, .environment, .environment]
      (MessageApplication.PolicyExecution.initial (application window) (initial window)) =
        fairCoin.denote.map (afterSignal window secret) := by
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, honestPlayers,
    MessageApplication.PolicyExecution.initial, initial, MessageApplication.State.initial, empty,
    IdealCommitments.empty, MessagePool.empty, Fin.isValue, MessageApplication.State.observe,
    application_observePlayer_eq, observe, ownerPolicy_pure_eq, Option.isSome_none,
    Bool.false_eq_true, ↓reduceIte, initialCachedValue,
    MessageApplication.ChoiceEncoding.cachedValue, FinDist.pure_bind,
    MessageApplication.playerStep, MessageApplication.advance,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step,
    application_privateStep_eq, privateStep, IdealCommitments.sealValue, List.nil_append,
    initialCommandEncoding, initialChoiceEncoding, bindingSubmitted, List.any_eq_true,
    Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, MessagePool.submit, MessageApplication.includePending,
    MessagePool.includeApplication, MessagePool.includePending, MessagePool.lookup,
    application_handle_eq, handle, Message.sender, Publication.publicationSite_eq,
    Option.bind_eq_bind, response_resolve_map, application_environmentStep_eq, environmentStep,
    FinDist.map_eq_bind, honestEnvironment, MessageApplication.environmentPolicyStep,
    MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.State.environmentView, application_observeEnvironment_eq,
    FinDist.bind_pure, FinDist.bind_bind, List.length_append, List.length_cons, List.length_nil,
    zero_add, Prod.mk.eta, List.append_assoc, List.cons_append,
    MessageApplication.ChoiceEncoding.cachedValue_cons,
    MessageApplication.ChoiceEncoding.privateCommand_decode_private, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_left, Nat.reduceAdd, decide_true,
    List.find?_cons_of_pos, MessagePool.removeFirst, and_self, Option.isSome_some, afterSignal,
    Option.isNone_none]
  congr 1
  funext signal
  congr 2
  funext who
  by_cases hwho : who = 0 <;> simp [hwho]

private theorem suffix_law (window : Nat) (secret signal : Bool)
    (complete : Bool → Bool → Bool) (response : Bool → Option Bool → Bool) :
    ((application window).runPolicies (honestPlayers secret complete response) honestEnvironment
      [.player 0, .environment, .player 1, .environment]
      (afterSignal window secret signal)).map policyData? =
        FinDist.pure (some ⟨secret, signal,
          if complete secret signal then some secret else none,
          response signal (if complete secret signal then some secret else none)⟩) := by
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, honestPlayers,
    ownerPolicy_pure_eq, responderPolicy_pure_eq]
  cases hchoice : complete secret signal <;>
    simp [honestEnvironment, initialCachedValue, initialCommandEncoding,
      initialChoiceEncoding, MessageApplication.ChoiceEncoding.cachedValue,
      openingEncoding_private, openingEncoding_bind, openingController_ready,
      pureOpeningCommand, openingBound?,
      afterSignal, initial, MessageApplication.State.initial,
      MessageApplication.State.observe, MessageApplication.State.environmentView,
      application_observePlayer_eq, application_observeEnvironment_eq, observe, empty,
      MessageApplication.playerStep, MessageApplication.environmentPolicyStep,
      MessageApplication.advance, MessageApplication.PlayerCommand.toAction,
      MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
      application_privateStep_eq, privateStep, application_handle_eq, handle,
      MessageApplication.includePending, MessagePool.includeApplication,
      MessagePool.includePending, MessagePool.lookup, MessagePool.submit, MessagePool.empty,
      MessagePool.removeFirst, Message.sender, IdealCommitments.sealValue,
      IdealCommitments.empty, IdealCommitments.lookup, IdealCommitments.freezeAt,
      IdealCommitments.verify, DisclosureBinding.reference,
      ConditionalPublication.resolveAddressed?, Message.dispatchEndpoint?, Message.routeEndpoint?,
      ConditionalPublication.resolve?, ConditionalPublication.ready,
      ConditionalPublication.requestPayload, Publication.publicationSite_eq,
      acceptedReference, verifyOpening, DisclosureBinding.verify, done, PublicState.done,
      responseEndpoint_requires, responseGraphPrerequisites_eq, PublicChoice.ready,
      responseReady, PublicChoice.resolve?_map, policyData?, outcome?, data, boundValue?,
      DisclosureBinding.value?, hchoice]

/-- The observation-local controllers execute the complete disclosure protocol
from the empty message state. The only stochastic transition is the fixed fair
source signal; neither the environment policy nor either player selects it. -/
theorem honest_policy_data (window : Nat) (secret : Bool)
    (complete : Bool → Bool → Bool) (response : Bool → Option Bool → Bool) :
    (((application window).policyGame honestEnvironment honestSchedule
      (initial window)).play (honestPlayers secret complete response)).map policyData? =
      fairCoin.denote.map (fun signal =>
        let opening := if complete secret signal then some secret else none
        some ⟨secret, signal, opening, response signal opening⟩) := by
  change ((application window).runPolicies _ _
    ([.player 0, .player 0, .environment, .environment, .environment] ++
      [.player 0, .environment, .player 1, .environment]) _).map policyData? = _
  rw [MessageApplication.runPolicies_append, prefix_law, FinDist.bind_map, FinDist.map_bind]
  simp only [suffix_law]
  rw [FinDist.map_eq_bind]


/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.honest_policy_data' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.honest_policy_data

end VegasTests.OptionalDisclosure.DisclosureState
