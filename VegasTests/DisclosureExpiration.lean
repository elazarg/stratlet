/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureApplicationSource

/-! # Response expiration in the native disclosure application

The owner prepares and discloses its binding, then submits an expiration call
after the response window. The absent responder performs no action. The shared
native runner settles with the existing source rejection value. This is an
included-call execution law, not a promise that a service will include it.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

def responseExpiryActions (window : Nat) (secret : Bool) :
    List (application window).Action :=
  [.privateCommand 0 (0, secret), .submit 0 (.bind (0, 0)), .include (0, 0),
    .environment .marker, .environment .sample,
    .submit 0 (.publish 5 (.opening (0, 0) secret)), .include (0, 1),
    .environment (.advance (window + 1)),
    .submit 0 .expireResponse, .include (0, 2)]

/-- A real owner-authored expiration call settles the missing response as
source rejection. Public chance and all three inclusion receipts are retained. -/
theorem response_expiration_run (window : Nat) (secret : Bool) :
    (((application window).run (responseExpiryActions window secret) (initial window)).map
      fun state => (state.application.outcome?, state.receipts)) =
      fairCoin.denote.map (fun signal =>
        (some (signal, some secret, false),
          [((0, 0), true), ((0, 1), true), ((0, 2), true)])) := by
  have hrequires : graph.publicationPrerequisites (node 6) (node 7) =
      [2, 3, 5, 0, 1, 4] := by
    simpa only [responsePrerequisites, responseEndpoint_requires] using responsePrerequisites_eq
  simp [responseExpiryActions, MessageApplication.run, MessageApplication.step,
    application, initial, MessageApplication.State.initial, empty,
    MessageApplication.includePending, MessagePool.includeApplication,
    MessagePool.includePending, MessagePool.lookup, MessagePool.submit,
    MessagePool.empty, MessagePool.removeFirst, privateStep, handle, environmentStep,
    Message.sender, IdealCommitments.freezeAt, IdealCommitments.lookup,
    IdealCommitments.empty, IdealCommitments.sealValue, IdealCommitments.verify,
    ConditionalPublication.resolveAddressed?, Message.dispatchEndpoint?, Message.routeEndpoint?,
    ConditionalPublication.resolve?, ConditionalPublication.ready,
    acceptedReference, DisclosureBinding.reference, verifyOpening, DisclosureBinding.verify,
    Publication.publicationSite_eq, done, responseReady, PublicChoice.ready, hrequires,
    outcome?, FinDist.map_eq_bind]

/-- The source outcome reconstructed after expiration uses the actual source
rejection action, for every accepted publication and every public payout list. -/
theorem response_expiration_source (payouts : Payouts) (window : Nat)
    (state : DisclosureState) (hinvariant : Invariant state)
    (signal : Bool) (publication : Option Bool)
    (hsignal : state.signal = some signal) (hpublication : state.publication = some publication)
    (caller : TestPlayer) (serial : Nat) (hready : state.responseReady = true)
    (hexpired : state.responseAt + window < state.clock) :
    ∃ next,
      handle window state ⟨(caller, serial), .expireResponse⟩ = some next ∧
      next.outcome? = some (signal, publication, false) ∧
      ∃ secret, Vegas.SmallStep.Star (Vegas.SourceConfig.initial (coreWithPayoffs payouts))
        ⟨TerminalContext, terminalEnv secret signal publication false, .ret payouts⟩ := by
  let next := { state with response := some false }
  have hhandle := expireResponse_accepts window state caller serial hready hexpired
  have hnext : Invariant next := handle_invariant window state _ next hinvariant hhandle
  have houtcome : next.outcome? = some (signal, publication, false) := by
    simp [next, outcome?, hsignal, hpublication]
  obtain ⟨secret, _, _, hsource, _⟩ :=
    outcome_source payouts next hnext signal publication false houtcome
  exact ⟨next, hhandle, houtcome, secret, hsource⟩

/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.response_expiration_run' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.response_expiration_run

/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.response_expiration_source' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.response_expiration_source

end VegasTests.OptionalDisclosure.DisclosureState
