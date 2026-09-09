/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureApplicationInvariant

/-! # Unopenable bindings in native public interaction

An owner submits an opaque handle without preparing an opening. The application
accepts it and executes public chance. Subsequent private preparation cannot
repair that accepted binding. A delivered opening attempt is rejected but stays
visible, and a later included expiration continues to the actual response.

These are execution and immutable-binding results, not a service guarantee or
a strategic equivalence. In particular, this ideal instance captures binding
at inclusion; it does not model a cryptographic packet's creation-time binding.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

/-- Wrong-endpoint traffic can be submitted, delivered, and included. Dispatch
rejects its application effect while retaining the delivered raw message and
the failed inclusion receipt, even at an otherwise ready application state. -/
theorem wrong_endpoint_run (window : Nat) (state : DisclosureState)
    (endpoint : Nat) (request : ConditionalPublication.Payload TestPlayer Bool)
    (hne : endpoint ≠ 5) :
    (((application window).run
      [.submit 0 (.publish endpoint request), .deliver 1 (0, 0), .include (0, 0)]
      (MessageApplication.State.initial (application window) state)).map fun final =>
        (final.application, final.receipts, final.pool.inbox 1)) =
      FinDist.pure (state, [((0, 0), false)],
        [⟨(0, 0), Payload.publish endpoint request⟩]) := by
  simp [MessageApplication.run, MessageApplication.step,
    MessageApplication.State.initial, MessageApplication.includePending,
    MessagePool.includeApplication, MessagePool.includePending, MessagePool.lookup,
    MessagePool.submit, MessagePool.empty, MessagePool.deliver, MessagePool.removeFirst,
    application, publish_wrong_endpoint window state (0, 0) endpoint request hne]

private def unopenablePrefix (window : Nat) : List (application window).Action :=
  [.submit 0 (.bind (0, 0)), .include (0, 0), .environment .marker, .environment .sample]

private def unopenableSuffix (window : Nat) (lateValue response : Bool) :
    List (application window).Action :=
  [.privateCommand 0 (0, lateValue),
    .submit 0 (.publish 5 (.opening (0, 0) lateValue)), .deliver 1 (0, 1), .include (0, 1),
    .environment (.advance (window + 1)),
    .submit 1 (.publish 5 .expire), .include (1, 0),
    .submit 1 (.respond response), .include (1, 1)]

private def unopenableAtSignal (window : Nat) (signal : Bool) : (application window).State :=
  { application := { empty with
      accepted := some (.commitment (0, 0)), markerDone := true, signal := some signal }
    pool := { MessagePool.empty TestPlayer Payload with
      ledger := [⟨(0, 0), .bind (0, 0)⟩]
      sent := fun who => if who = 0 then [⟨(0, 0), .bind (0, 0)⟩] else []
      nextSerial := fun who => if who = 0 then 1 else 0 }
    receipts := [((0, 0), true)] }

private theorem unopenable_prefix_law (window : Nat) :
    (application window).run (unopenablePrefix window) (initial window) =
      fairCoin.denote.map (unopenableAtSignal window) := by
  simp [unopenablePrefix, unopenableAtSignal, MessageApplication.run,
    MessageApplication.step, application, initial, MessageApplication.State.initial,
    empty, MessageApplication.includePending, MessagePool.includeApplication,
    MessagePool.includePending, MessagePool.lookup, MessagePool.submit, MessagePool.empty,
    MessagePool.removeFirst, handle, environmentStep, Message.sender,
    IdealCommitments.freezeAt, IdealCommitments.lookup, IdealCommitments.empty,
    FinDist.map_eq_bind]

private theorem unopenable_suffix_law (window : Nat) (signal lateValue response : Bool) :
    (((application window).run (unopenableSuffix window lateValue response)
      (unopenableAtSignal window signal)).map fun state =>
        (state.application.outcome?, state.receipts, state.pool.inbox 1)) =
      FinDist.pure (some (signal, none, response),
        [((0, 0), true), ((0, 1), false), ((1, 0), true), ((1, 1), true)],
        [⟨(0, 1), Payload.publish 5 (.opening (0, 0) lateValue)⟩]) := by
  have hrequires : graph.publicationPrerequisites (node 6) (node 7) =
      [2, 3, 5, 0, 1, 4] := by
    simpa only [responsePrerequisites, responseEndpoint_requires] using responsePrerequisites_eq
  simp [unopenableSuffix, unopenableAtSignal, MessageApplication.run, MessageApplication.step,
    application, empty, MessageApplication.includePending, MessagePool.includeApplication,
    MessagePool.includePending, MessagePool.lookup, MessagePool.submit, MessagePool.empty,
    MessagePool.removeFirst, MessagePool.deliver, privateStep, handle, environmentStep,
    Message.sender, IdealCommitments.lookup, IdealCommitments.empty, IdealCommitments.sealValue,
    IdealCommitments.verify, ConditionalPublication.resolveAddressed?, Message.dispatchEndpoint?,
    Message.routeEndpoint?, ConditionalPublication.resolve?, ConditionalPublication.ready,
    acceptedReference, DisclosureBinding.reference, verifyOpening, DisclosureBinding.verify,
    Publication.publicationSite_eq, done, responseReady, PublicChoice.resolve?_map,
    PublicChoice.ready, hrequires, outcome?]

/-- The owner attempts preparation only after the accepted binding and public
signal. Expiration is a real responder-authored message, not a clock effect. -/
def unopenableActions (window : Nat) (lateValue response : Bool) :
    List (application window).Action :=
  unopenablePrefix window ++ unopenableSuffix window lateValue response

/-- The complete native law retains the source chance, successful binding,
rejected opening receipt, delivered failed message, and source decline followed
by the response. There is no successful opening for either late Boolean. -/
theorem unopenable_run (window : Nat) (lateValue response : Bool) :
    (((application window).run (unopenableActions window lateValue response)
      (initial window)).map fun state =>
        (state.application.outcome?, state.receipts, state.pool.inbox 1)) =
      fairCoin.denote.map (fun signal =>
        (some (signal, none, response),
          [((0, 0), true), ((0, 1), false), ((1, 0), true), ((1, 1), true)],
          [⟨(0, 1), Payload.publish 5 (.opening (0, 0) lateValue)⟩])) := by
  rw [unopenableActions, MessageApplication.run_append, unopenable_prefix_law]
  rw [FinDist.bind_map, FinDist.map_bind]
  simp only [unopenable_suffix_law]
  rw [FinDist.map_eq_bind]

/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.unopenable_run' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.unopenable_run

end VegasTests.OptionalDisclosure.DisclosureState
