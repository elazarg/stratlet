/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureServiceResolution
import VegasTests.DisclosureSites

/-! # A zero-window publication race under service

The selector below gives pending publication-expiration calls priority and
otherwise includes the first pending message.  It remains a genuine inclusion
service: payload inspection changes order, not whether a nonempty queue is
served.  The boundary is a native-reachable prelude followed by the cycle's
actual eight-slot inclusion phase; it is not a complete three-cycle compiled
controller law.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

def publicationExpirationId? : List (Message TestPlayer Payload) →
    Option (MessageId TestPlayer)
  | [] => none
  | message :: rest =>
      match message.payload with
      | .publish .expire => some message.id
      | _ => publicationExpirationId? rest

private theorem publicationExpirationId?_find
    (messages : List (Message TestPlayer Payload)) (id : MessageId TestPlayer)
    (hselected : publicationExpirationId? messages = some id) :
    ∃ message, messages.find? (fun candidate => candidate.id = id) = some message := by
  induction messages with
  | nil => simp [publicationExpirationId?] at hselected
  | cons first rest ih =>
      cases hpayload : first.payload <;>
        simp only [publicationExpirationId?, hpayload] at hselected
      case publish request =>
        cases request <;> simp only at hselected
        case expire =>
          cases hselected
          exact ⟨first, by simp⟩
        all_goals
          by_cases hid : first.id = id
          · exact ⟨first, by simp [hid]⟩
          · obtain ⟨message, hlookup⟩ := ih hselected
            exact ⟨message, by simpa [hid] using hlookup⟩
      all_goals
        by_cases hid : first.id = id
        · exact ⟨first, by simp [hid]⟩
        · obtain ⟨message, hlookup⟩ := ih hselected
          exact ⟨message, by simpa [hid] using hlookup⟩

private theorem publicationExpirationId?_lookup
    (pool : MessagePool TestPlayer Payload) (id : MessageId TestPlayer)
    (hselected : publicationExpirationId? pool.pending = some id) :
    ∃ message, pool.lookup id = some message := by
  simpa only [MessagePool.lookup] using
    publicationExpirationId?_find pool.pending id hselected

def expirationFirst : (application 0).EnvironmentPolicy := fun _ view =>
  FinDist.pure <| match publicationExpirationId? view.pool.pending with
    | some id => .include id
    | none => match view.pool.pending with
      | [] => .wait
      | message :: _ => .include message.id

theorem expirationFirst_service :
    (application 0).InclusionService (fun _ => True) expirationFirst := by
  intro history view command _ hcommand
  simp only [expirationFirst, FinDist.mem_support_pure] at hcommand
  cases hselected : publicationExpirationId? view.pool.pending with
  | some id =>
      simp only [hselected] at hcommand
      subst command
      obtain ⟨message, hlookup⟩ := publicationExpirationId?_lookup view.pool id hselected
      cases hpending : view.pool.pending with
      | nil => simp [publicationExpirationId?, hpending] at hselected
      | cons first rest => exact ⟨id, message, hlookup, rfl⟩
  | none =>
      simp only [hselected] at hcommand
      cases hpending : view.pool.pending with
      | nil =>
          simp only [hpending] at hcommand
          exact hcommand
      | cons first rest =>
          simp only [hpending] at hcommand
          subst command
          exact ⟨first.id, first, by simp [MessagePool.lookup, hpending], rfl⟩

def zeroWindowRacePrelude : List (application 0).Action :=
  [.privateCommand 0 (0, true), .submit 0 (.bind (0, 0)), .include (0, 0),
    .environment .marker, .environment .sample, .environment (.advance 1),
    .submit 0 (.publish (.opening (0, 0) true)),
    .submit 1 (.publish .expire)]

/-- The race state is genuinely native-reachable from the empty application:
the owner has a valid `true` binding and opening pending, while an overdue
publication-expiration call is pending behind it. -/
theorem zero_window_race_prelude_observation :
    (((application 0).run zeroWindowRacePrelude (initial 0)).map fun state =>
      (state.application.boundValue?, state.application.signal,
        state.application.signalAt, state.application.clock,
        state.application.publication, state.pool.pending)) =
      fairCoin.denote.map fun signal =>
        (some true, some signal, 0, 1, none,
          [⟨(0, 1), Payload.publish (.opening (0, 0) true)⟩,
            ⟨(1, 0), Payload.publish .expire⟩]) := by
  simp [zeroWindowRacePrelude, MessageApplication.run, MessageApplication.step,
    application, initial, MessageApplication.State.initial, empty,
    MessageApplication.includePending, MessagePool.includeApplication,
    MessagePool.includePending, MessagePool.lookup, MessagePool.submit,
    MessagePool.empty, MessagePool.removeFirst, privateStep, handle, environmentStep,
    Message.sender, IdealCommitments.freezeAt, IdealCommitments.lookup,
    IdealCommitments.empty, IdealCommitments.sealValue, boundValue?,
    DisclosureBinding.value?, FinDist.map_eq_bind]

theorem zero_window_race_prelude_reachable :
    ∃ state ∈ ((application 0).run zeroWindowRacePrelude (initial 0)).support,
      Invariant state.application ∧
      state.application.boundValue? = some true ∧
      state.application.signal.isSome = true ∧
      state.application.signalAt < state.application.clock ∧
      state.application.publication = none ∧
      state.pool.pending =
        [⟨(0, 1), Payload.publish (.opening (0, 0) true)⟩,
          ⟨(1, 0), Payload.publish .expire⟩] := by
  have hout : ((some true : Option Bool), (some true : Option Bool), (0 : Nat),
      (1 : Nat), (none : Option (Option Bool)),
      ([⟨(0, 1), Payload.publish (.opening (0, 0) true)⟩,
        ⟨(1, 0), Payload.publish .expire⟩] : List (Message TestPlayer Payload))) ∈
      (fairCoin.denote.map fun (signal : Bool) =>
        ((some true : Option Bool), some signal, (0 : Nat), (1 : Nat),
          (none : Option (Option Bool)),
          ([⟨(0, 1), Payload.publish (.opening (0, 0) true)⟩,
            ⟨(1, 0), Payload.publish .expire⟩] :
              List (Message TestPlayer Payload)))).support := by
    rw [FinDist.support_map]
    exact ⟨true, coin_supported true, rfl⟩
  have hout' : (some true, some true, 0, 1, none,
      [⟨(0, 1), Payload.publish (.opening (0, 0) true)⟩,
        ⟨(1, 0), Payload.publish .expire⟩]) ∈
      (((application 0).run zeroWindowRacePrelude (initial 0)).map fun state =>
        (state.application.boundValue?, state.application.signal,
          state.application.signalAt, state.application.clock,
          state.application.publication, state.pool.pending)).support := by
    rw [zero_window_race_prelude_observation]
    exact hout
  rw [FinDist.support_map] at hout'
  obtain ⟨state, hstate, heq⟩ := hout'
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hbound, hsignal, hsignalAt, hclock, hpublication, hpending⟩ := heq
  have hinvariant := (application 0).run_application_invariant Invariant
    privateStep_invariant (handle_invariant 0) environmentStep_invariant
    (initial 0) state zeroWindowRacePrelude empty_invariant hstate
  refine ⟨state, hstate, hinvariant, hbound, ?_, ?_, hpublication, hpending⟩
  · simp [hsignal]
  · omega

private theorem verifyOpening_true_of_invariant (state : DisclosureState)
    (hinvariant : Invariant state) (hbound : state.boundValue? = some true) :
    state.verifyOpening ⟨(0, 0), true⟩ = true := by
  rcases hinvariant.1 with hnone | hcommit | hdefault
  · simp [boundValue?, hnone] at hbound
  · have hstored : state.acceptedService.lookup (0, 0) = some true := by
      simpa [boundValue?, hcommit, DisclosureBinding.value?] using hbound
    simp [verifyOpening, hcommit, DisclosureBinding.verify,
      IdealCommitments.verify, hstored]
  · simp [boundValue?, hdefault, DisclosureBinding.value?] at hbound

/-- Positive control for the queued owner request: from the same ready state,
including the earlier opening first accepts it and publishes `true`. -/
theorem zero_window_queued_opening_valid (state : (application 0).State)
    (hinvariant : Invariant state.application)
    (hbound : state.application.boundValue? = some true)
    (hsignal : state.application.signal.isSome = true)
    (hpublication : state.application.publication = none)
    (hpending : state.pool.pending =
      [⟨(0, 1), Payload.publish (.opening (0, 0) true)⟩,
        ⟨(1, 0), Payload.publish .expire⟩]) :
    ((application 0).includePending state (0, 1)).application.publication =
      some (some true) := by
  have hlookup : state.pool.lookup (0, 1) =
      some ⟨(0, 1), Payload.publish (.opening (0, 0) true)⟩ := by
    simp [MessagePool.lookup, hpending]
  have hready := publication_ready_of_signal (window := 0)
    state.application hinvariant hsignal hpublication
  let before := state.application
  have hresolve : (Publication.publicationSite (before.signalAt + 0)).resolve?
      before.clock before.verifyOpening before.acceptedReference before.done (fun _ => true)
      ⟨(0, 1), .opening (0, 0) true⟩ = some (some true) := by
    apply (ConditionalPublication.resolve_opening _ _ _ _ _ _ _ (0, 0) true rfl).2
    exact ⟨by simpa [before] using hready, rfl, rfl,
      verifyOpening_true_of_invariant before (by simpa [before] using hinvariant)
        (by simpa [before] using hbound), rfl⟩
  have hhandle : handle 0 before
      ⟨(0, 1), Payload.publish (.opening (0, 0) true)⟩ =
      some { before with publication := some (some true), responseAt := before.clock } := by
    simp only [handle, hresolve, Option.bind_eq_bind, Option.bind_some]
  dsimp only [before] at hhandle
  rw [(application 0).includePending_accept state (0, 1) _ _ hlookup hhandle]

private theorem run_publication_fixed (state next : (application 0).State)
    (actions : List (application 0).Action) (result : Option Bool)
    (hpublication : state.application.publication = some result)
    (hnext : next ∈ ((application 0).run actions state).support) :
    next.application.publication = some result := by
  apply (application 0).run_application_invariant
    (fun current => current.publication = some result) ?_ ?_ ?_
    state next actions hpublication hnext
  · intro current who command hcurrent
    exact hcurrent
  · intro current message final hcurrent hhandle
    exact (handle_publication_fixed 0 current message final result hcurrent hhandle).1.trans
      hcurrent
  · intro current command final hcurrent hfinal
    exact (environmentStep_publication current final command hfinal).trans hcurrent

/-- At inclusion index two, the admitted payload-sensitive selector includes
the expiration before the earlier valid opening.  The remaining seven service
slots cannot change the resulting decline or the accepted `true` binding. -/
theorem zero_window_serviced_publication_race
    (players : TestPlayer → (application 0).PlayerPolicy)
    (execution next : (application 0).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 2)
    (hinvariant : Invariant execution.native.application)
    (hbound : execution.native.application.boundValue? = some true)
    (hsignal : execution.native.application.signal.isSome = true)
    (hexpired : execution.native.application.signalAt < execution.native.application.clock)
    (hpublication : execution.native.application.publication = none)
    (hpending : execution.native.pool.pending =
      [⟨(0, 1), Payload.publish (.opening (0, 0) true)⟩,
        ⟨(1, 0), Payload.publish .expire⟩])
    (hnext : next ∈ ((application 0).runPolicies players
      (serviceEnvironment expirationFirst) (List.replicate 8 .environment)
      execution).support) :
    next.native.application.boundValue? = some true ∧
      next.native.application.publication = some none := by
  rw [List.replicate_succ, MessageApplication.runPolicies.eq_def] at hnext
  simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
  obtain ⟨command, hcommand, hmiddle⟩ := hmiddle
  have hservicePolicy : serviceEnvironment expirationFirst execution.environmentHistory
      execution.native.environmentView = expirationFirst execution.environmentHistory
        execution.native.environmentView := by
    unfold serviceEnvironment
    rw [hphase]
    rfl
  rw [hservicePolicy] at hcommand
  simp only [expirationFirst, MessageApplication.State.environmentView, hpending,
    publicationExpirationId?, FinDist.mem_support_pure] at hcommand
  subst command
  have hnative : middle.native = (application 0).includePending execution.native (1, 0) := by
    simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
      MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
      FinDist.pure_bind, FinDist.mem_support_pure] at hmiddle
    exact congrArg MessageApplication.PolicyExecution.native hmiddle
  have hlookup : execution.native.pool.lookup (1, 0) =
      some ⟨(1, 0), Payload.publish .expire⟩ := by
    simp [MessagePool.lookup, hpending]
  have hready := publication_ready_of_signal (window := 0)
    execution.native.application hinvariant hsignal hpublication
  let before := execution.native.application
  have hhandle : handle 0 before ⟨(1, 0), Payload.publish .expire⟩ =
      some { before with publication := some none, responseAt := before.clock } := by
    dsimp only [before]
    simp only [handle, ConditionalPublication.resolve?]
    rw [hready]
    simp [Publication.publicationSite_eq, hexpired]
  have hmiddleApplication : middle.native.application =
      { before with publication := some none, responseAt := before.clock } := by
    rw [hnative, (application 0).includePending_accept execution.native (1, 0) _ _
      hlookup hhandle]
  have hnativeTail := (application 0).runPolicies_native_support players
    (serviceEnvironment expirationFirst) (List.replicate 7 .environment) middle next hnext
  obtain ⟨actions, _, hrun⟩ := hnativeTail
  have hacceptedSome : middle.native.application.accepted.isSome = true := by
    rw [hmiddleApplication]
    change before.accepted.isSome = true
    dsimp only [before]
    cases haccepted : execution.native.application.accepted with
    | none => simp [boundValue?, haccepted] at hbound
    | some binding => rfl
  have hbinding := run_binding 0 middle.native next.native actions hacceptedSome hrun
  have hpublicationTail := run_publication_fixed middle.native next.native actions none
    (by rw [hmiddleApplication]) hrun
  refine ⟨?_, hpublicationTail⟩
  change next.native.application.accepted.bind
    (DisclosureBinding.value? next.native.application.acceptedService) = some true
  rw [hbinding.1, hbinding.2, hmiddleApplication]
  simpa only [before, boundValue?] using hbound

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.expirationFirst_service'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.expirationFirst_service

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.zero_window_race_prelude_reachable'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.zero_window_race_prelude_reachable

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.zero_window_queued_opening_valid'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.zero_window_queued_opening_valid

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.zero_window_serviced_publication_race'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.zero_window_serviced_publication_race

end VegasTests.OptionalDisclosure.DisclosureState
