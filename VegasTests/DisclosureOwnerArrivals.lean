/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureServiceArrivals
import VegasTests.DisclosureOwnerBinding

/-! # The unchanged owner's first public request

The first two invocations start from the real empty policy execution. They
prepare the chosen secret and submit its opaque reference, without resolving
any public decision or emitting a publication. Subsequent service proofs use
these actual history and pending-envelope facts.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

/-- The unchanged owner's first two invocations prepare its private value and
submit the canonical opaque binding. No environment or opponent invocation is
hidden in this prefix. -/
theorem owner_initial_pair (secret : Bool) (complete : Bool → Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (howner : players 0 = ownerPolicy secret complete)
    (environment : (application window).EnvironmentPolicy)
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((application window).runPolicies players environment
      [.player 0, .player 0]
      (MessageApplication.PolicyExecution.initial (application window) (initial window))).support) :
    next.native.application.service.lookup (0, 0) = some secret ∧
      next.native.pool.pending = [⟨(0, 0), Payload.bind (0, 0)⟩] ∧
      next.native.application.observe = empty.observe ∧
      registered (next.principalHistory 0) = true ∧
      bindingSubmitted (next.principalHistory 0) = true ∧
      publicationSubmitted (next.principalHistory 0) = false := by
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, howner] at hnext
  simp [ownerPolicy, registered, bindingSubmitted, MessageApplication.PolicyExecution.initial,
    initial, MessageApplication.State.initial, empty, MessageApplication.State.observe,
    MessageApplication.playerStep, MessageApplication.advance,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step, application, observe,
    privateStep, FinDist.mem_support_pure] at hnext
  subst next
  simp [MessagePool.submit, MessagePool.empty, IdealCommitments.sealValue,
    IdealCommitments.lookup, IdealCommitments.empty, registered, bindingSubmitted,
    publicationSubmitted, observe, empty]

/-- The complete arrival phase retains the actual owner-authored binding and
its permanently registered secret, despite arbitrary responder commands and
packet delivery. No inclusion or deadline premise is used in this phase. -/
theorem owner_initial_arrival (secret : Bool) (complete : Bool → Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (howner : players 0 = ownerPolicy secret complete)
    (selector : (application window).EnvironmentPolicy)
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceArrivals
      (MessageApplication.PolicyExecution.initial (application window) (initial window))).support) :
    OwnerSecretStored secret next.native.application ∧
      ⟨(0, 0), Payload.bind (0, 0)⟩ ∈ next.native.pool.pending ∧
      next.native.application.observe = empty.observe := by
  let rest : List (@MessageApplication.Invocation TestPlayer) :=
    [.player 1, .player 1, .environment, .environment,
      .player 0, .player 0, .player 1, .player 1]
  have hsplit : serviceArrivals = [.player 0, .player 0] ++ rest := rfl
  rw [hsplit, MessageApplication.runPolicies_append] at hnext
  simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨prepared, hprepared, hnext⟩ := hnext
  have hpair := owner_initial_pair secret complete players howner
    (serviceEnvironment selector) prepared hprepared
  have hhistory := (application window).runPolicies_environmentHistory_length players
    (serviceEnvironment selector) [.player 0, .player 0]
    (MessageApplication.PolicyExecution.initial (application window) (initial window)) prepared
    hprepared
  have hhistory' : prepared.environmentHistory.length = 0 := by
    simpa [MessageApplication.PolicyExecution.initial,
      MessageApplication.Invocation.isEnvironment] using hhistory
  have hcount : rest.countP MessageApplication.Invocation.isEnvironment = 2 := by decide
  have hpublic := service_communication_phase players selector rest prepared next (by
    intro offset hoffset
    rw [hcount] at hoffset
    rw [hhistory']
    omega) hnext
  refine ⟨?_, ?_, hpublic.1.trans hpair.2.2.1⟩
  · apply (application window).runPolicies_application_invariant (OwnerSecretStored secret)
      (privateStep_ownerSecretStored secret)
      (fun state message final => handle_ownerSecretStored secret state final message)
      (fun state command final => environmentStep_ownerSecretStored secret state final command)
      players (serviceEnvironment selector) rest prepared next hpair.1 hnext
  · apply hpublic.2.subset
    simp [hpair.2.1]

/-- At a resolved binding and sampled signal, an unchanged owner submits the
source-selected publication at its first opportunity. Remaining player and
delivery invocations retain that exact authenticated request. -/
theorem owner_publication_arrival (secret signal : Bool) (complete : Bool → Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (howner : players 0 = ownerPolicy secret complete)
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (haccepted : execution.native.application.accepted = some (.commitment (0, 0)))
    (hsignal : execution.native.application.signal = some signal)
    (hpublication : execution.native.application.publication = none)
    (hresponse : execution.native.application.response = none)
    (hnotSubmitted : publicationSubmitted (execution.principalHistory 0) = false)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceArrivals execution).support) :
    ∃ serial, ⟨(0, serial), Payload.publish
      ((Publication.publicationSite (execution.native.application.signalAt + window)).requestPayload
        (if complete secret signal then some secret else none))⟩ ∈ next.native.pool.pending := by
  apply service_owner_arrival _ players selector execution next hphase ?_ hnext
  rw [howner]
  have hrequest := owner_publication_after_signal secret signal complete
    (execution.principalHistory 0)
    (MessageApplication.State.observe (application window) execution.native 0)
    haccepted hsignal hpublication hresponse hnotSubmitted
  cases hchoice : complete secret signal <;>
    simpa [ConditionalPublication.requestPayload, hchoice] using hrequest

end VegasTests.OptionalDisclosure.DisclosureState
