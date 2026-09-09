/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureService

/-! # Reactions to pending traffic in the disclosure service

The same service used for capacity proofs admits value-dependent player
reactions before inclusion. A deliberately cleartext sender lets the recipient
copy its value into a fresh pending message. For other packets the recipient
uses a constant guess. These are native policy-execution laws, not
deviation adequacy or a hiding theorem against arbitrary receivers.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

def probeValue : Payload → Bool
  | .cleartext value => value
  | _ => false

/-- Send one raw packet, then wait; copy a delivered cleartext packet when
acting as its recipient. Application rejection does not prevent the signal. -/
def wireProbePlayers (payload : Payload) : TestPlayer → (application window).PlayerPolicy
  | 0 => fun history _ => FinDist.pure <|
      if history.isEmpty then .submit payload else .wait
  | 1 => fun _ view => FinDist.pure <|
      match view.messages.inbox.head? with
      | some message => .submit (.respond (probeValue message.payload))
      | none => .wait

/-- The recipient's two reactions occur while the ledger is still empty.
The environment selector is arbitrary: its inclusion phase has not begun. -/
theorem wire_probe_reactions (payload : Payload)
    (selector : (application window).EnvironmentPolicy) :
    ((((application window).policyGame (serviceEnvironment selector) serviceArrivals
      (initial window)).play (wireProbePlayers payload)).map
        (fun execution => (execution.native.pool.sent 1, execution.native.pool.ledger))) =
      FinDist.pure
        ([⟨(1, 0), Payload.respond (probeValue payload)⟩,
          ⟨(1, 1), .respond (probeValue payload)⟩], []) := by
  simp [MessageApplication.policyGame, serviceArrivals, MessageApplication.runPolicies,
    MessageApplication.invoke, wireProbePlayers, MessageApplication.PolicyExecution.initial,
    initial, MessageApplication.State.initial, MessageApplication.playerStep,
    MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.PlayerCommand.toAction, MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step, MessageApplication.State.observe,
    MessageApplication.State.environmentView,
    serviceEnvironment, MessagePool.submit, MessagePool.empty, MessagePool.observe,
    MessagePool.deliver, MessagePool.lookup, application]

theorem cleartext_reactions_before_inclusion (value : Bool)
    (selector : (application window).EnvironmentPolicy) :
    ((((application window).policyGame (serviceEnvironment selector) serviceArrivals
      (initial window)).play (wireProbePlayers (.cleartext value))).map
        (fun execution => (execution.native.pool.sent 1, execution.native.pool.ledger))) =
      FinDist.pure
        ([⟨(1, 0), Payload.respond value⟩, ⟨(1, 1), .respond value⟩], []) :=
  wire_probe_reactions (.cleartext value) selector

theorem opaque_probe_constant_response (selector : (application window).EnvironmentPolicy) :
    ((((application window).policyGame (serviceEnvironment selector) serviceArrivals
      (initial window)).play (wireProbePlayers (.bind (0, 0)))).map
        (fun execution => (execution.native.pool.sent 1, execution.native.pool.ledger))) =
      FinDist.pure ([⟨(1, 0), Payload.respond false⟩, ⟨(1, 1), .respond false⟩], []) :=
  wire_probe_reactions (.bind (0, 0)) selector

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.wire_probe_reactions' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.wire_probe_reactions

end VegasTests.OptionalDisclosure.DisclosureState
