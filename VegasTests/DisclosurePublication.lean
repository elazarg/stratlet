/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.TransactionalInclusion
import Vegas.Compile.ConditionalExecution
import Vegas.Compile.ConditionalOpeningController
import VegasTests.DisclosureAccounting
import VegasTests.DisclosureOpening

/-! # Transactional publication of the checked optional-disclosure source

The application below uses the compiled graph's actual choice and publication
nodes at the source checkpoint. The fixture's exact guard characterization is
what justifies accepting the classifier's opening or decline. This is not a
generic conditional-opening compiler, runner, or strategy correspondence.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.Publication

open Vegas EventGraph Interaction

abbrev Payload := ConditionalPublication.Payload TestPlayer Bool
abbrev Pool := MessagePool TestPlayer Payload
abbrev Service := IdealCommitments TestPlayer Nat Bool

def accountingSite : CommitmentAccounting.OpeningSite DisclosureAccounting.optionalPlan := by
  unfold DisclosureAccounting.optionalPlan DisclosureAccounting.optionalPlanWithPayoffs
  apply CommitmentAccounting.OpeningSite.commit
  apply CommitmentAccounting.OpeningSite.commit
  apply CommitmentAccounting.OpeningSite.reveal
  apply CommitmentAccounting.OpeningSite.sample
  apply CommitmentAccounting.OpeningSite.here

/-- The accounting witness supplies the ordinary adjacent choice occurrence
and its conditional-opening certificate to the backend. -/
def publicationCertificate : ConditionalPublicationSite source.prog :=
  accountingSite.conditionalPublicationSite

private def compilerInitial : ToEventGraph.BuildState TestPlayer simpleExpr source.Γ :=
  ToEventGraph.BuildState.fromInitial
    (ToEventGraph.initialState source.Γ source.env source.wctx)

private def identityTransport :
    MessageApplication.ChoiceEncoding (Nat × Payload) (Nat × Payload) where
  encode := id
  decode := some
  decode_encode := by intro value; rfl
  decode_sound := by
    intro wire value hdecode
    exact Option.some.inj hdecode

private def openingChoiceEncoding :=
  publicationCertificate.choiceEncoding source.fresh compilerInitial 0 10 identityTransport

theorem opening_choice_encodes_decline :
    openingChoiceEncoding.encode none = (5, .decline) := rfl

theorem opening_choice_encodes_bound_value (secret : Bool) :
    openingChoiceEncoding.encode (some secret) = (5, .opening (0, 0) secret) := rfl

theorem opening_choice_rejects_wrong_endpoint :
    openingChoiceEncoding.decode (6, .decline) = none := rfl

theorem opening_choice_does_not_cache_expiry :
    openingChoiceEncoding.decode (5, .expire) = none := rfl

def publicationSite (deadline : Nat) : ConditionalPublication TestPlayer :=
  graph.conditionalPublication 0 0 (node 4) (node 5) deadline

@[simp] theorem publicationSite_eq (deadline : Nat) :
    publicationSite deadline = ⟨0, 0, 4, 5, [0, 1, 2, 3, 0, 1], deadline⟩ := rfl

theorem publicationSite_from_accounting (deadline : Nat) :
    publicationSite deadline = publicationCertificate.runtimeSite OptionalDisclosure.source.fresh
      compilerInitial 0 deadline := by
  rfl

def registeredService (secret : Bool) : Service :=
  ((IdealCommitments.empty : Service).sealValue 0 0 secret).state

structure Application where
  config : Config graph
  service : Service
  accepted : Option (CommitmentHandle TestPlayer Nat)
  completed : List Nat
  result : Option (Option Bool)

def Application.done (state : Application) (index : Nat) : Bool :=
  decide (index ∈ state.completed)

def initial (data : RunData) : Application :=
  ⟨cfg data 4, registeredService data.secret, some (0, 0), [0, 1, 2, 3], none⟩

def handler (deadline now : Nat) (state : Application)
    (message : Message TestPlayer Payload) : Option Application :=
  match (publicationSite deadline).resolve? now state.service.verify state.accepted state.done
      (fun _ => true) message with
  | none => none
  | some choice => some {
      state with
      config := (state.config.completeNode (node 4) ⟨.option .bool, choice⟩).completeNode
        (node 5) ⟨.option .bool, choice⟩
      completed := 5 :: 4 :: state.completed
      result := some choice }

def submitDeliverInclude (deadline now : Nat) (state : Application)
    (sender recipient : TestPlayer) (payload : Payload) :=
  let submitted := (MessagePool.empty TestPlayer Payload).submit sender payload
  let delivered := (submitted.2.deliver recipient submitted.1).state
  delivered.includeApplication state submitted.1 (handler deadline now)

theorem complete_publication (data : RunData) (choice : Option Bool) :
    ((cfg data 4).completeNode (node 4) ⟨.option .bool, choice⟩).completeNode
        (node 5) ⟨.option .bool, choice⟩ =
      cfg { data with opening := choice } 6 := by
  have hprefix : cfg data 4 = cfg { data with opening := choice } 4 := by rfl
  rw [hprefix]
  calc
    _ = (cfg { data with opening := choice } 5).completeNode
        (node 5) ⟨.option .bool, choice⟩ := by
      exact congrArg
        (fun state => state.completeNode (node 5) ⟨.option .bool, choice⟩)
        (cfg_succ { data with opening := choice } 4).symm
    _ = cfg { data with opening := choice } 6 :=
      (cfg_succ { data with opening := choice } 5).symm

theorem handler_success (data : RunData) (deadline now : Nat)
    (message : Message TestPlayer Payload) (next : Application)
    (hhandler : handler deadline now (initial data) message = some next) :
    ∃ choice, (choice = none ∨ choice = some data.secret) ∧
      next.config = cfg { data with opening := choice } 6 ∧
      evalGuard openingGuard choice
        ((openingEnv data.secret data.signal).toView 0).eraseEnv = true := by
  unfold handler initial at hhandler
  split at hhandler
  next => contradiction
  next choice hresolve =>
    have hlookup : (registeredService data.secret).lookup (0, 0) = some data.secret := by
      exact (IdealCommitments.seal_first
        (IdealCommitments.empty : Service) 0 0 data.secret rfl).2
    have hvalue := (publicationSite deadline).resolve_value now
      (registeredService data.secret) (some (0, 0)) (initial data).done
      (fun _ => true) message data.secret hlookup choice hresolve
    have hvalid : choice = none ∨ choice = some data.secret := hvalue
    cases hhandler
    refine ⟨choice, hvalid, rfl, ?_⟩
    exact (opening_guard_iff data.secret data.signal choice).mpr hvalid

/-- Every accepted handler result performs the actual source AST's adjacent
commit/reveal steps, with the continuation selected by its accounting site. -/
theorem handler_source_steps (data : RunData) (deadline now : Nat)
    (message : Message TestPlayer Payload) (next : Application)
    (hhandler : handler deadline now (initial data) message = some next) :
    let found := publicationCertificate.choice
    let env := openingEnv data.secret data.signal
    ∃ choice, next.config = cfg { data with opening := choice } 6 ∧
      SmallStep.Star
        ⟨found.context, env, .commit found.choiceName found.owner found.guard
          (.reveal found.publicName found.owner found.choiceName .here found.tail)⟩
        ⟨(found.publicName, .pub found.ty) ::
            (found.choiceName, .sealed found.owner found.ty) :: found.context,
          (env.cons choice).cons choice, found.tail⟩ := by
  obtain ⟨choice, _, hnext, hlegal⟩ := handler_success data deadline now message next hhandler
  exact ⟨choice, hnext, DisclosureAccounting.optionalSpec.commit_reveal_steps
    5 publicationCertificate.choice.tail (openingEnv data.secret data.signal) choice hlegal⟩

private theorem checkpoint_agrees (data : RunData) :
    (ToEventGraph.decisionSiteState publicationCertificate.choice.decision source.fresh
      compilerInitial).Agrees (cfg data 4).store (openingEnv data.secret data.signal) := by
  intro name ty binding
  cases binding with
  | here => rfl
  | there binding =>
    cases binding with
    | here => rfl
    | there binding =>
      cases binding with
      | here => rfl
      | there binding =>
        cases binding with
        | here => rfl
        | there binding => cases binding

/-- The concrete transactional handler instantiates the generic generated-site
execution theorem at its represented source checkpoint. -/
theorem handler_graph_reachable (data : RunData) (deadline now : Nat)
    (message : Message TestPlayer Payload) (next : Application)
    (hhandler : handler deadline now (initial data) message = some next)
    (hreachable : Reachable graph (cfg data 4)) : Reachable graph next.config := by
  obtain ⟨choice, _, hnext, hlegal⟩ := handler_success data deadline now message next hhandler
  have hcompleted : ∀ index : Fin graph.nodeCount,
      (initial data).done index.val = true ↔ index ∈ (cfg data 4).done := by
    intro index
    change decide (index.val ∈ [0, 1, 2, 3]) = true ↔
      index ∈ ({node 3, node 2, node 1, node 0} : Finset (Fin graph.nodeCount))
    fin_cases index <;> decide
  have hready : (publicationCertificate.runtimeSite source.fresh compilerInitial 0 deadline).ready
      (some (0, 0)) (initial data).done = true := by
    rw [← publicationSite_from_accounting]
    rfl
  have hresult := publicationCertificate.completePublication_reachable source.fresh compilerInitial
    (cfg data 4) (openingEnv data.secret data.signal) (checkpoint_agrees data)
    0 deadline (some (0, 0)) (initial data).done hcompleted hready choice hlegal hreachable
  rw [hnext]
  change Reachable graph
    (((cfg data 4).completeNode (node 4) ⟨.option .bool, choice⟩).completeNode
      (node 5) ⟨.option .bool, choice⟩) at hresult
  rw [complete_publication] at hresult
  exact hresult

def opened (secret signal response : Bool) :=
  let data : RunData := ⟨secret, signal, none, response⟩
  submitDeliverInclude 10 5 (initial data) 0 1 (.opening (0, 0) secret)

def declined (secret signal response : Bool) :=
  let data : RunData := ⟨secret, signal, none, response⟩
  submitDeliverInclude 10 5 (initial data) 0 1 .decline

def expired (secret signal response : Bool) :=
  let data : RunData := ⟨secret, signal, none, response⟩
  submitDeliverInclude 10 11 (initial data) 1 0 .expire

theorem opened_result (secret signal response : Bool) :
    (opened secret signal response).receipt = some true ∧
      (opened secret signal response).application.config =
        cfg ⟨secret, signal, some secret, response⟩ 6 := by
  cases secret <;> cases signal <;> cases response <;>
    simp [opened, submitDeliverInclude, handler, publicationSite_eq,
      ConditionalPublication.resolve?, ConditionalPublication.ready, Application.done,
      Message.sender, IdealCommitments.empty, IdealCommitments.sealValue,
      IdealCommitments.verify, IdealCommitments.lookup,
      initial, registeredService, MessagePool.empty, MessagePool.submit,
      MessagePool.deliver, MessagePool.lookup, MessagePool.includeApplication,
      MessagePool.includePending, MessagePool.removeFirst, complete_publication]

theorem declined_result (secret signal response : Bool) :
    (declined secret signal response).receipt = some true ∧
      (declined secret signal response).application.config =
        cfg ⟨secret, signal, none, response⟩ 6 := by
  cases secret <;> cases signal <;> cases response <;>
    simp [declined, submitDeliverInclude, handler, publicationSite_eq,
      ConditionalPublication.resolve?, ConditionalPublication.ready, Application.done,
      Message.sender, IdealCommitments.empty, IdealCommitments.sealValue,
      initial, registeredService, MessagePool.empty, MessagePool.submit,
      MessagePool.deliver, MessagePool.lookup, MessagePool.includeApplication,
      MessagePool.includePending, MessagePool.removeFirst, complete_publication]

theorem expired_result (secret signal response : Bool) :
    (expired secret signal response).receipt = some true ∧
      (expired secret signal response).application.config =
        cfg ⟨secret, signal, none, response⟩ 6 := by
  cases secret <;> cases signal <;> cases response <;>
    simp [expired, submitDeliverInclude, handler, publicationSite_eq,
      ConditionalPublication.resolve?, ConditionalPublication.ready, Application.done,
      IdealCommitments.empty, IdealCommitments.sealValue,
      initial, registeredService, MessagePool.empty, MessagePool.submit,
      MessagePool.deliver, MessagePool.lookup, MessagePool.includeApplication,
      MessagePool.includePending, MessagePool.removeFirst, complete_publication]

def deliveredOpeningThenExpiry (secret signal response : Bool) :=
  let data : RunData := ⟨secret, signal, none, response⟩
  let opening := (MessagePool.empty TestPlayer Payload).submit 0 (.opening (0, 0) secret)
  let delivered := (opening.2.deliver 1 opening.1).state
  let expiry := delivered.submit 1 .expire
  expiry.2.includeApplication (initial data) expiry.1 (handler 10 11)

theorem delivered_opening_survives_expiry (secret signal response : Bool) :
    (deliveredOpeningThenExpiry secret signal response).receipt = some true ∧
      ((deliveredOpeningThenExpiry secret signal response).pool.inbox 1).length = 1 ∧
      (deliveredOpeningThenExpiry secret signal response).application.result = some none := by
  cases secret <;> cases signal <;> cases response <;> decide

end VegasTests.OptionalDisclosure.Publication

/--
info: 'VegasTests.OptionalDisclosure.Publication.handler_graph_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VegasTests.OptionalDisclosure.Publication.handler_graph_reachable

/--
info: 'VegasTests.OptionalDisclosure.Publication.handler_source_steps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VegasTests.OptionalDisclosure.Publication.handler_source_steps
