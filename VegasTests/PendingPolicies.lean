/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedPolicyHiding
import Vegas.Game.SealedMessages
import VegasTests.PendingExecution

/-! # Policies over the actual checked pending-message application

The positive experiment starts empty and registers and submits a nullable
value through the owner's scoped policy, retaining its private command history.
Opponent and environment policies remain arbitrary and adaptive within the
subsequent fixed invocation schedule. The negative control delivers cleartext
and has the same local responder copy the value into its own outgoing message.
Neither experiment asserts settlement or equilibrium preservation.
-/

namespace VegasTests.PendingPolicies

open Interaction Interaction.SealedProgram GameTheory.Math.Probability
open VegasTests.PendingSource VegasTests.PendingExecution

def prepared (value : Value) : PolicyExecution Player Value :=
  playerStep program 0
    (playerStep program 0 (PolicyExecution.initial initial) (.register 0 value))
    (.submit (.commitment 0 (0, 0)))

theorem prepared_native (value : Value) :
    (prepared value).native = (submitCommit initial 0 0 value).2 := rfl

noncomputable section

def sealPolicy (rebroadcast : Bool) (value : Value) : PlayerPolicy Player Value rebroadcast :=
  fun history _ => match history.length with
  | 0 => FinDist.pure ⟨.register 0 value, trivial⟩
  | 1 => FinDist.pure ⟨.submit (.commitment 0 (0, 0)), trivial⟩
  | _ => FinDist.pure ⟨.wait, trivial⟩

def sealedLaw (rebroadcast : Bool) (value : Value)
    (players : Player → PlayerPolicy Player Value rebroadcast)
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player)) :
    FinDist (PolicyExecution Player Value) :=
  (policyGame rebroadcast program environment (.player 0 :: .player 0 :: schedule) initial).play
    (GameTheory.Profile.update players 0 (sealPolicy rebroadcast value))

theorem sealedLaw_eq_continuation (rebroadcast : Bool) (value : Value)
    (players : Player → PlayerPolicy Player Value rebroadcast)
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player))
    (hschedule : ∀ who, Invocation.player who ∈ schedule → who ≠ (0 : Player)) :
    sealedLaw rebroadcast value players environment schedule =
      runPolicies rebroadcast program players environment schedule (prepared value) := by
  simp only [sealedLaw, policyGame, runPolicies, invoke, GameTheory.Profile.update_same,
    PolicyExecution.initial, playerStep, sealPolicy, List.length_nil, List.length_append,
    List.length_cons, ite_true, FinDist.map_pure, FinDist.pure_bind]
  change runPolicies rebroadcast program _ environment schedule (prepared value) = _
  apply runPolicies_congr_on_schedule
  intro who hmem
  exact GameTheory.Profile.update_of_ne
    (sig := (policyGame rebroadcast program environment
      (.player 0 :: .player 0 :: schedule) initial).sig)
    players _ (hschedule who hmem)

theorem prepared_related (left right : Value) :
    PolicyExecution.HidingRelated (0 : Player) (prepared left) (prepared right) := by
  refine ⟨submitCommit_empty_related 0 0 left right, ?_, rfl⟩
  intro who hne
  simp [prepared, playerStep, PolicyExecution.initial, hne]

/-- Every pair of nullable source values has the same pre-disclosure
observation law against the same adaptive policies in this bounded instance. -/
theorem sealedLaw_hiding (rebroadcast : Bool) (left right : Value)
    (players : Player → PlayerPolicy Player Value rebroadcast)
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player))
    (hschedule : ∀ who, Invocation.player who ∈ schedule → who ≠ (0 : Player)) :
    (sealedLaw rebroadcast left players environment schedule).map (PolicyExecution.observations 0) =
      (sealedLaw rebroadcast right players environment schedule).map
        (PolicyExecution.observations 0) := by
  rw [sealedLaw_eq_continuation rebroadcast left players environment schedule hschedule,
    sealedLaw_eq_continuation rebroadcast right players environment schedule hschedule]
  exact runPolicies_hiding rebroadcast program players environment schedule
    (prepared_related left right) hschedule

/-- The hidden setup and every policy-generated continuation use the actual
compiled graph runner, including arbitrary opponent payloads and inclusion. -/
theorem sealedLaw_reachable (rebroadcast : Bool) (value : Value)
    (players : Player → PlayerPolicy Player Value rebroadcast)
    (environment : EnvironmentPolicy Player Value) (schedule : List (Invocation Player))
    (execution : PolicyExecution Player Value)
    (hmem : execution ∈ (sealedLaw rebroadcast value players environment schedule).support) :
    ∃ cfg : Vegas.EventGraph.Config graph,
      graph.decodeSealed (.option .bool) execution.native = some cfg ∧
        Vegas.EventGraph.Reachable graph cfg := by
  obtain ⟨cfg, hdecode, hreachable, _⟩ := source.sealed_policy_source
    (.option .bool) sealedFragment rebroadcast _ environment
      (.player 0 :: .player 0 :: schedule) execution hmem
  exact ⟨cfg, hdecode, hreachable⟩

def copyCleartext : PlayerPolicy Player Value true := fun _ view =>
  match view.messages.inbox.head? with
  | some ⟨_, .cleartext _ value⟩ => FinDist.pure ⟨.submit (.cleartext 1 value), trivial⟩
  | _ => FinDist.pure ⟨.wait, trivial⟩

def deliverFirst : EnvironmentPolicy Player Value :=
  fun _ _ => FinDist.pure (.deliver 1 (0, 0))

def disclosePolicy (value : Value) : PlayerPolicy Player Value true :=
  fun _ _ => FinDist.pure ⟨.submit (.cleartext 0 value), trivial⟩

def cleartextResponseLaw (value : Value) : FinDist (PolicyExecution Player Value) :=
  (policyGame true program deliverFirst [.player 0, .environment, .player 1] initial).play
    (GameTheory.Profile.update (fun _ => copyCleartext) 0 (disclosePolicy value))

/-- The opponent's fixed local policy reads a delivered pending cleartext
message and publishes that value in its own response, before any inclusion. -/
theorem cleartextResponseLaw_sent (value : Value) :
    (cleartextResponseLaw value).map (fun execution => execution.native.pool.sent 1) =
      FinDist.pure [⟨(1, 0), Payload.cleartext 1 value⟩] := by
  simp [cleartextResponseLaw, policyGame, runPolicies, invoke, deliverFirst,
    copyCleartext, disclosePolicy, environmentStep, playerStep, PolicyExecution.initial,
    State.observe, MessagePool.observe, step, initial, State.empty,
    MessagePool.empty, MessagePool.submit, MessagePool.deliver,
    MessagePool.lookup, EnvironmentCommand.toAction, PlayerCommand.toAction, applyNative]

theorem cleartextResponseLaw_distinguishes (left right : Value) (hne : left ≠ right) :
    (cleartextResponseLaw left).map (fun execution => execution.native.pool.sent 1) ≠
      (cleartextResponseLaw right).map (fun execution => execution.native.pool.sent 1) := by
  rw [cleartextResponseLaw_sent, cleartextResponseLaw_sent]
  intro heq
  have hmem : [⟨(1, 0), Payload.cleartext 1 left⟩] ∈
      (FinDist.pure [⟨(1, 0), Payload.cleartext 1 right⟩] :
        FinDist (List (Message Player (Payload Player Value)))).support := by
    rw [← heq]
    exact FinDist.mem_support_pure.mpr rfl
  have hlist := FinDist.mem_support_pure.mp hmem
  have hpayload := congrArg Message.payload (List.cons.inj hlist).1
  cases hpayload
  exact hne rfl

end

end VegasTests.PendingPolicies

/-- info: 'Interaction.SealedProgram.runPolicies_hiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedProgram.runPolicies_hiding

/-- info: 'Interaction.SealedProgram.policyGame_enableRebroadcast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedProgram.policyGame_enableRebroadcast

/-- info: 'Vegas.WFProgram.sealed_policy_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.sealed_policy_source

/-- info: 'VegasTests.PendingPolicies.sealedLaw_hiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingPolicies.sealedLaw_hiding
