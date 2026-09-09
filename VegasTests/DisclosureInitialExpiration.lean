/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureApplicationSource

/-! # Initial expiration without an owner commitment

An initial expiration installs a public source default. Private preparation
remains intact and does not determine that default. The full native execution
below contains no owner action: the responder submits both expiration calls
and then responds to the resolved decline. Service guarantees and strategic
comparison remain separate obligations.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Vegas EventGraph Interaction GameTheory.Math.Probability

private theorem initialExpiryResponseGraphPrerequisites_eq :
    graph.publicationPrerequisites (node 6) (node 7) = [2, 3, 5, 0, 1, 4] := by
  simpa only [responsePrerequisites, responseEndpoint_requires] using
    responsePrerequisites_eq

def initialExpiryActions (window : Nat) (response : Bool) :
    List (application window).Action :=
  [.environment (.advance (window + 1)),
    .submit 1 .expireInitial, .include (1, 0),
    .environment .marker, .environment .sample,
    .environment (.advance (window + 1 + window + 1)),
    .submit 1 (.publish 5 .expire), .include (1, 1),
    .submit 1 (.respond response), .include (1, 2)]

/-- Both actual expiration calls are authored by the responder. The native
law retains source chance, the public-default tag, and all inclusion receipts. -/
theorem initial_expiration_run (window : Nat) (response : Bool) :
    (((application window).run (initialExpiryActions window response) (initial window)).map
      fun state => (state.application.outcome?, state.application.accepted, state.receipts)) =
      fairCoin.denote.map (fun signal =>
        (some (signal, none, response), some (DisclosureBinding.publicDefault false),
          [((1, 0), true), ((1, 1), true), ((1, 2), true)])) := by
  have hclock : window + 1 ≤ window + 1 + window + 1 := by omega
  simp [initialExpiryActions, MessageApplication.run, MessageApplication.step,
    application, initial, MessageApplication.State.initial, empty,
    MessageApplication.includePending, MessagePool.includeApplication,
    MessagePool.includePending, MessagePool.lookup, MessagePool.submit,
    MessagePool.empty, MessagePool.removeFirst, handle, PublicChoice.resolve?_map,
    environmentStep, Message.sender,
    ConditionalPublication.resolveAddressed?, Message.dispatchEndpoint?, Message.routeEndpoint?,
    ConditionalPublication.resolve?, ConditionalPublication.ready, acceptedReference,
    DisclosureBinding.reference, Publication.publicationSite_eq, done,
    responseReady, responseValidator_true, responseEndpoint_owner, PublicChoice.ready,
    responseEndpoint_choiceNode,
    responseEndpoint_publicationNode, initialExpiryResponseGraphPrerequisites_eq,
    outcome?, hclock, FinDist.map_eq_bind]

/-- Expiration preserves unsubmitted private preparation and records an
explicitly public default. It cannot be mistaken for a successful owner bind. -/
theorem initial_expiration_preserves_preparation (window : Nat) (prepared : Bool) :
    let before := { privateStep empty 0 (0, prepared) with clock := window + 1 }
    ∃ next,
      handle window before ⟨(1, 0), .expireInitial⟩ = some next ∧
      next.service.lookup (0, 0) = some prepared ∧
      next.acceptedService = before.acceptedService ∧
      next.observe.accepted = some (.publicDefault false) ∧
      next.boundValue? = some false := by
  dsimp only
  refine ⟨_, expireInitial_accepts window _ 1 0 rfl (by simp), ?_, rfl, rfl, ?_⟩
  · simp [privateStep, empty, IdealCommitments.sealValue,
      IdealCommitments.lookup, IdealCommitments.empty]
  · exact publicDefault_value _ false rfl

/-- Once the public default is installed, the different privately prepared
value cannot be published as its opening, at any clock or readiness state. -/
theorem initial_default_rejects_different_opening (window : Nat) (state : DisclosureState)
    (serial : Nat) (haccepted : state.accepted = some (.publicDefault false)) :
    handle window state ⟨(0, serial), .publish 5 (.opening (0, 0) true)⟩ = none := by
  simp [handle, ConditionalPublication.resolveAddressed?, Message.dispatchEndpoint?,
    Message.routeEndpoint?, ConditionalPublication.resolve?, verifyOpening, haccepted,
    DisclosureBinding.verify]

/-- An accepted public default supplies its opening value independently of
private registration. The canonical addressed request is accepted at the
actual ready application checkpoint. -/
theorem public_default_opening_accepts (window : Nat) (state : DisclosureState)
    (value signal : Bool) (serial : Nat)
    (haccepted : state.accepted = some (.publicDefault value))
    (hmarker : state.markerDone = true) (hsignal : state.signal = some signal)
    (hpublication : state.publication = none) :
    handle window state ⟨(0, serial), .publish 5 (.opening (0, 0) value)⟩ =
      some { state with publication := some (some value), responseAt := state.clock } := by
  simp [handle, ConditionalPublication.resolveAddressed?, Message.dispatchEndpoint?,
    Message.routeEndpoint?, ConditionalPublication.resolve?, ConditionalPublication.ready,
    Publication.publicationSite_eq, acceptedReference, DisclosureBinding.reference,
    verifyOpening, DisclosureBinding.verify, done, haccepted, hmarker, hsignal,
    hpublication, Message.sender]

/-- Every supported complete run of the initial-expiration script has a
written-source execution with the initial source value `false`. -/
theorem initial_expiration_source (payouts : Payouts) (window : Nat) (response : Bool)
    (next : (application window).State)
    (hnext : next ∈ ((application window).run (initialExpiryActions window response)
      (initial window)).support)
    (signal : Bool) (houtcome : next.application.outcome? = some (signal, none, response)) :
    Vegas.SmallStep.Star (Vegas.SourceConfig.initial (coreWithPayoffs payouts))
      ⟨TerminalContext, terminalEnv false signal none response, .ret payouts⟩ := by
  have hinvariant := (application window).run_application_invariant Invariant
    privateStep_invariant (handle_invariant window) environmentStep_invariant
    (initial window) next (initialExpiryActions window response) empty_invariant hnext
  have hmem : (next.application.outcome?, next.application.accepted, next.receipts) ∈
      (((application window).run (initialExpiryActions window response) (initial window)).map
        fun state =>
          (state.application.outcome?, state.application.accepted, state.receipts)).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [initial_expiration_run, FinDist.support_map] at hmem
  obtain ⟨drawn, _, hresult⟩ := hmem
  have haccepted : next.application.accepted = some (.publicDefault false) :=
    (congrArg (fun result => result.2.1) hresult).symm
  have hvalue := publicDefault_value next.application false haccepted
  obtain ⟨secret, hsecret, _, hsource, _⟩ :=
    outcome_source payouts next.application hinvariant signal none response houtcome
  simp only [hvalue, Option.getD_some] at hsecret
  exact hsecret ▸ hsource

/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.initial_expiration_run' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.initial_expiration_run

/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.initial_expiration_source' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.initial_expiration_source

end VegasTests.OptionalDisclosure.DisclosureState
