/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureApplicationPolicies

/-! # Honest execution of the disclosure application -/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory GameTheory.Math.Probability

variable {window : Nat}

def policyData? (execution : (application window).PolicyExecution) : Option RunData :=
  if execution.native.application.outcome?.isSome then
    some execution.native.application.data
  else none

/-- The observation-local controllers execute the complete disclosure protocol
from the empty message state. The only stochastic transition is the fixed fair
source signal; neither the environment policy nor either player selects it. -/
theorem honest_policy_data (window : Nat) (secret : Bool)
    (opening : Bool → Option Bool) (response : Bool → Option Bool → Bool)
    (hvalid : OpeningValid secret opening) :
    (((application window).policyGame honestEnvironment honestSchedule
      (initial window)).play (honestPlayers secret opening response)).map policyData? =
      fairCoin.denote.map (fun signal =>
        some ⟨secret, signal, opening signal, response signal (opening signal)⟩) := by
  rcases hvalid false with hfalse | hfalse <;>
    rcases hvalid true with htrue | htrue <;>
    simp only [MessageApplication.policyGame]
  all_goals
    rw [show honestSchedule = .player 0 :: .player 0 :: .environment ::
      .environment :: .environment :: .player 0 :: .environment ::
      .player 1 :: .environment :: [] by rfl]
  all_goals try rw [MessageApplication.runPolicies]
  all_goals simp only [application, observe, MessageApplication.invoke, honestPlayers,
    ownerPolicy, registered, MessageApplication.PolicyExecution.initial, initial,
    MessageApplication.State.initial, empty, Fin.isValue, List.any_nil, Bool.not_false, ↓reduceIte,
    FinDist.pure_bind, MessageApplication.playerStep, MessageApplication.advance,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step, privateStep,
    List.nil_append, MessageApplication.State.observe]
  all_goals try rw [MessageApplication.runPolicies]
  all_goals simp only [MessageApplication.invoke, honestPlayers, ownerPolicy, registered,
    Fin.isValue, ↓reduceIte, List.any_cons, List.any_nil, Bool.or_false, Bool.not_true,
    Bool.false_eq_true, MessageApplication.State.observe, Option.isNone_none, bindingSubmitted,
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
  all_goals simp only [MessageApplication.invoke, honestPlayers, ownerPolicy, registered,
    Fin.isValue, ↓reduceIte, List.any_cons, List.any_nil, Bool.or_self, Bool.or_false,
    Bool.not_true, Bool.false_eq_true, MessageApplication.State.observe, Option.isNone_some,
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
    Publication.publicationSite_eq, BEq.rfl, done, Option.isSome_none, Bool.not_false,
    Bool.and_self, List.all_cons, Option.isSome_some, List.all_nil, Bool.not_true,
    Bool.false_eq_true, Message.sender, Option.bind_eq_bind, Option.bind_some,
    MessageApplication.State.environmentView, observe, and_true, true_and]
  all_goals try rw [MessageApplication.runPolicies]
  all_goals simp only [MessageApplication.invoke, honestPlayers, responderPolicy,
    MessageApplication.State.observe, Fin.isValue, responseSubmitted, one_ne_zero, ↓reduceIte,
    List.any_nil, Bool.false_eq_true, FinDist.pure_bind, MessageApplication.playerStep,
    MessageApplication.advance, MessageApplication.PlayerCommand.toAction, MessageApplication.step,
    List.cons_append, List.nil_append, FinDist.bind_bind, FinDist.map_bind]
  all_goals try rw [MessageApplication.runPolicies]
  all_goals simp only [MessageApplication.invoke, honestEnvironment, Fin.isValue,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, MessagePool.submit, one_ne_zero,
    ↓reduceIte, List.nil_append, FinDist.pure_bind, MessageApplication.environmentPolicyStep,
    MessageApplication.advance, MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step, MessageApplication.includePending, MessagePool.includeApplication,
    MessagePool.includePending, MessagePool.lookup, decide_true, List.find?_cons_of_pos,
    MessagePool.removeFirst, List.cons_append, handle, Message.sender, responseReady, done,
    Option.isSome_none, Bool.not_false, Bool.and_self, responsePrerequisites_eq, List.all_cons,
    Option.isSome_some, List.all_nil, and_self, MessageApplication.State.environmentView, observe,
    IdealCommitments.verify, IdealCommitments.freezeAt, IdealCommitments.lookup,
    BEq.rfl, Option.bind_some]
  all_goals try simp only [MessageApplication.runPolicies, Fin.isValue, FinDist.map_pure,
    policyData?,
    outcome?, Option.bind_eq_bind, Option.bind_some, Option.isSome_some, ↓reduceIte, data,
    Option.getD_some, FinDist.bind_pure]
  all_goals simp only [IdealCommitments.lookup, Fin.isValue, and_self, ↓reduceIte,
    Option.getD_some, MessageApplication.invoke, honestEnvironment, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, FinDist.pure_bind,
    MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    MessageApplication.includePending, MessagePool.includeApplication, MessagePool.includePending,
    MessagePool.lookup, decide_true, List.find?_cons_of_pos, MessagePool.removeFirst,
    List.cons_append, List.nil_append, handle, Message.sender, responseReady, done,
    Option.isSome_none, Bool.not_false, Bool.and_self, responsePrerequisites_eq, List.all_cons,
    Option.isSome_some, List.all_nil, MessageApplication.State.environmentView, observe,
    FinDist.map_pure, policyData?, outcome?, Option.bind_eq_bind, Option.bind_some, data]

/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.honest_policy_data' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.honest_policy_data

end VegasTests.OptionalDisclosure.DisclosureState
