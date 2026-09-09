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

/-- The owner attempts preparation only after the accepted binding and public
signal. Expiration is a real responder-authored message, not a clock effect. -/
def unopenableActions (window : Nat) (lateValue response : Bool) :
    List (application window).Action :=
  [.submit 0 (.bind (0, 0)), .include (0, 0), .environment .marker,
    .environment .sample, .privateCommand 0 (0, lateValue),
    .submit 0 (.publish (.opening (0, 0) lateValue)), .deliver 1 (0, 1), .include (0, 1),
    .environment (.advance (window + 1)),
    .submit 1 (.publish .expire), .include (1, 0),
    .submit 1 (.respond response), .include (1, 1)]

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
          [⟨(0, 1), Payload.publish (.opening (0, 0) lateValue)⟩])) := by
  simp only [application, outcome?, Option.bind_eq_bind, Fin.isValue, unopenableActions,
    initial, MessageApplication.State.initial, empty, IdealCommitments.empty, MessagePool.empty,
    MessageApplication.run, MessageApplication.step, MessagePool.submit, List.nil_append, zero_add,
    MessageApplication.includePending, MessagePool.includeApplication, MessagePool.includePending,
    MessagePool.lookup, handle, Message.sender, IdealCommitments.freezeAt, IdealCommitments.lookup,
    ConditionalPublication.resolve?, ConditionalPublication.ready, Publication.publicationSite_eq,
    done, List.all_cons, List.all_nil, IdealCommitments.verify, and_true, responseReady,
    Bool.and_self, responsePrerequisites_eq, environmentStep, FinDist.map_eq_bind,
    FinDist.pure_bind, privateStep, IdealCommitments.sealValue, MessagePool.deliver,
    FinDist.bind_bind, decide_true, List.find?_cons_of_pos, MessagePool.removeFirst, ↓reduceIte,
    Option.isNone_none, and_self, Option.isSome_some, Bool.not_false, List.cons_append,
    Nat.reduceAdd, true_and, BEq.rfl, Option.isSome_none, Bool.not_true, Bool.false_eq_true,
    Option.none_beq_some, Option.bind_none, one_ne_zero, Nat.zero_le, Nat.lt_add_one,
    Option.bind_some]

/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.unopenable_run' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.unopenable_run

end VegasTests.OptionalDisclosure.DisclosureState
