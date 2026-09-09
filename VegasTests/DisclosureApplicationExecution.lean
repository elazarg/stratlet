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

def policyData? (execution : (application window).PolicyExecution) : Option RunData :=
  if execution.native.application.outcome?.isSome then
    some execution.native.application.data
  else none

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
  cases hfalse : complete secret false <;>
    cases htrue : complete secret true <;>
    simp only [MessageApplication.policyGame]
  all_goals
    rw [show honestSchedule = .player 0 :: .player 0 :: .environment ::
      .environment :: .environment :: .player 0 :: .environment ::
      .player 1 :: .environment :: [] by rfl]
  all_goals try rw [MessageApplication.runPolicies]
  all_goals simp only [application, observe, MessageApplication.invoke, honestPlayers,
    ownerPolicy, registered, MessageApplication.PolicyExecution.initial, initial,
    MessageApplication.State.initial, empty, Fin.isValue, List.any_nil, Bool.not_false, ↓reduceIte,
    Option.isSome_none, Bool.false_eq_true,
    FinDist.pure_bind, MessageApplication.playerStep, MessageApplication.advance,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step, privateStep,
    List.nil_append, MessageApplication.State.observe]
  all_goals try rw [MessageApplication.runPolicies]
  all_goals simp only [MessageApplication.invoke, honestPlayers, ownerPolicy, registered,
    Fin.isValue, ↓reduceIte, List.any_cons, List.any_nil, Bool.or_false, Bool.not_true,
    Bool.false_eq_true, MessageApplication.State.observe, bindingSubmitted,
    Option.isSome_none,
    Bool.or_self, FinDist.pure_bind, MessageApplication.playerStep, MessageApplication.advance,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step, List.cons_append,
    List.nil_append]
  all_goals try rw [MessageApplication.runPolicies]
  all_goals simp only [MessageApplication.invoke, honestEnvironment, List.length_nil, Fin.isValue,
    FinDist.pure_bind, MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    MessageApplication.includePending, MessagePool.includeApplication, handle, Option.isNone_none,
    zero_add, Publication.publicationSite_eq, Option.bind_eq_bind, List.nil_append,
    List.cons_append, MessageApplication.State.environmentView, observe]
  all_goals simp only [Fin.isValue, MessagePool.includePending, MessagePool.lookup,
    MessagePool.submit, MessagePool.empty, List.nil_append, zero_add, decide_true,
    List.find?_cons_of_pos, Message.sender, IdealCommitments.sealValue,
    IdealCommitments.empty, and_self, ↓reduceIte]
  all_goals simp only [Fin.isValue, MessagePool.removeFirst, ↓reduceIte]
  all_goals try rw [MessageApplication.runPolicies]
  all_goals simp only [MessageApplication.invoke, honestEnvironment, Fin.isValue,
    List.length_cons, List.length_nil, zero_add, FinDist.pure_bind,
    MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step, environmentStep,
    Option.isSome_some, Bool.not_false, Bool.and_self, ↓reduceIte, FinDist.map_pure,
    List.cons_append, List.nil_append, MessageApplication.State.environmentView, observe]
  all_goals try rw [MessageApplication.runPolicies]
  all_goals simp only [MessageApplication.invoke, honestEnvironment, Fin.isValue,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, FinDist.pure_bind,
    MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step, environmentStep,
    Option.isNone_none, Bool.and_self, ↓reduceIte, FinDist.map_comp, List.cons_append,
    List.nil_append, FinDist.bind_map, Function.comp_apply,
    MessageApplication.State.environmentView, observe, FinDist.bind_bind, FinDist.map_bind]
  all_goals rw [FinDist.map_eq_bind]
  all_goals apply congrArg fairCoin.denote.bind
  all_goals funext signal
  all_goals cases signal <;> simp only [hfalse, htrue]
  all_goals try rw [MessageApplication.runPolicies]
  all_goals simp only [MessageApplication.invoke, honestPlayers, ownerPolicy,
    Fin.isValue, ↓reduceIte, List.any_cons, List.any_nil, Bool.or_self,
    Option.isSome_none,
    Bool.false_eq_true, MessageApplication.State.observe,
    publicationSubmitted, hfalse, FinDist.pure_bind, MessageApplication.playerStep,
    MessageApplication.advance, MessageApplication.PlayerCommand.toAction, MessageApplication.step,
    List.cons_append, List.nil_append, htrue]
  all_goals try rw [MessageApplication.runPolicies]
  all_goals simp only [MessageApplication.invoke, honestEnvironment, Fin.isValue,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, MessagePool.submit, ↓reduceIte,
    List.nil_append, List.cons_append, FinDist.pure_bind, MessageApplication.environmentPolicyStep,
    MessageApplication.advance, MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step, MessageApplication.includePending, MessagePool.includeApplication,
    MessagePool.includePending, MessagePool.lookup, decide_true, List.find?_cons_of_pos,
    MessagePool.removeFirst, handle, ConditionalPublication.resolve?, ConditionalPublication.ready,
    acceptedReference, DisclosureBinding.reference, Option.map_some,
    verifyOpening, DisclosureBinding.verify, IdealCommitments.verify,
    IdealCommitments.freezeAt, IdealCommitments.lookup, and_self,
    Publication.publicationSite_eq, BEq.rfl, done, Option.isSome_none, Bool.not_false,
    Bool.and_self, List.all_cons, Option.isSome_some, List.all_nil, Bool.not_true,
    Bool.false_eq_true, Message.sender, Option.bind_eq_bind, Option.bind_some,
    MessageApplication.State.environmentView, observe]
  all_goals try rw [MessageApplication.runPolicies]
  all_goals simp only [MessageApplication.invoke, honestPlayers, responderPolicy,
    MessageApplication.State.observe, Fin.isValue, one_ne_zero,
    ↓reduceIte, Option.isSome_none, Bool.false_eq_true]
  all_goals rw [responseController_pure_eq]
  all_goals simp only [application, observe, PublicChoice.ready, responseEndpoint_choiceNode,
    responseEndpoint_publicationNode, responseEndpoint_requires,
    responseGraphPrerequisites_eq, PublicState.done,
    MessageApplication.SubmissionCodec.cachedValue_nil, Option.isSome_some, Option.isSome_none,
    Option.isNone_none, Bool.not_false, Bool.and_self, ↓reduceIte,
    List.all_cons, List.all_nil, Option.getD_some,
    FinDist.pure_bind, MessageApplication.playerStep,
    MessageApplication.advance, MessageApplication.PlayerCommand.toAction, MessageApplication.step,
    List.cons_append, List.nil_append]
  all_goals try rw [MessageApplication.runPolicies]
  all_goals simp only [MessageApplication.invoke, honestEnvironment, Fin.isValue,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, MessagePool.submit, one_ne_zero,
    ↓reduceIte, List.nil_append, FinDist.pure_bind, MessageApplication.environmentPolicyStep,
    MessageApplication.advance, MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step, MessageApplication.includePending, MessagePool.includeApplication,
    MessagePool.includePending, MessagePool.lookup, decide_true, List.find?_cons_of_pos,
    MessagePool.removeFirst, List.cons_append, handle, PublicChoice.resolve?_map, Message.sender,
    responseValidator_true, responseEndpoint_owner, PublicChoice.ready,
    responseEndpoint_choiceNode,
    responseEndpoint_publicationNode, responseEndpoint_requires, responseGraphPrerequisites_eq,
    done, Option.isSome_none,
    Bool.not_false, Bool.and_self, List.all_cons, Option.isSome_some, List.all_nil, and_self,
    MessageApplication.State.environmentView, observe]
  all_goals unfold policyData?
  all_goals try simp only [MessageApplication.runPolicies, Fin.isValue, FinDist.map_pure,
    outcome?, Option.bind_eq_bind, Option.bind_some, Option.isSome_some, ↓reduceIte, data,
    boundValue?, DisclosureBinding.value?,
    Option.getD_some]
  all_goals simp only [IdealCommitments.lookup, Fin.isValue, ↓reduceIte,
    Option.getD_some]

/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.honest_policy_data' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.honest_policy_data

end VegasTests.OptionalDisclosure.DisclosureState
