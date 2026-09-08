/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedTimeoutPolicies
import VegasTests.PendingTimeout

/-! # Policy-level timeout ordering regression

The players and invocation schedule are identical in both games.  Only the
wire-observing environment's order for two already-pending calls differs.  In
particular, player 1 submits a valid opening in both games; expiration is an
inclusion-order outcome, not an encoding of that player's decision to quit.
-/

namespace VegasTests.PendingTimeoutPolicies

open GameTheory GameTheory.Math.Probability
open Interaction Interaction.SealedProgram Interaction.SealedTimeout
open VegasTests.PendingSource

noncomputable section

private def players : Player → PlayerPolicy Player VegasTests.PendingExecution.Value
  | 0 => fun _ _ => FinDist.pure (.submit .expire)
  | 1 => fun _ _ => FinDist.pure (.submit (.protocol (.opening 3 (1, 1) (some true))))

private def openingFirst :
    EnvironmentPolicy Player VegasTests.PendingExecution.Value := fun history _ =>
  FinDist.pure <| match history.length with
    | 0 => .advance 11
    | 1 => .deliver 0 (1, 1)
    | 2 => .include (1, 1)
    | _ => .include (0, 1)

private def expiryFirst :
    EnvironmentPolicy Player VegasTests.PendingExecution.Value := fun history _ =>
  FinDist.pure <| match history.length with
    | 0 => .advance 11
    | 1 => .deliver 0 (1, 1)
    | 2 => .include (0, 1)
    | _ => .include (1, 1)

private def schedule : List (Invocation Player) :=
  [.environment, .player 1, .player 0, .environment, .environment, .environment]

private def initial :=
  VegasTests.PendingTimeout.commitPrefix (some false) (some true)

private def openingFirstResult :=
  VegasTests.PendingTimeout.timed.run initial
    [.advance 11, .submit 1 (.protocol (.opening 3 (1, 1) (some true))),
     .submit 0 .expire, .deliver 0 (1, 1), .include (1, 1), .include (0, 1)]

private def expiryFirstResult :=
  VegasTests.PendingTimeout.timed.run initial
    [.advance 11, .submit 1 (.protocol (.opening 3 (1, 1) (some true))),
     .submit 0 .expire, .deliver 0 (1, 1), .include (0, 1), .include (1, 1)]

def openingFirstLaw :=
  (policyGame VegasTests.PendingTimeout.timed openingFirst schedule initial).play players

def expiryFirstLaw :=
  (policyGame VegasTests.PendingTimeout.timed expiryFirst schedule initial).play players

private theorem openingFirst_native :
    openingFirstLaw.map (fun outcome => outcome.native) =
      FinDist.pure openingFirstResult := by
  simp only [openingFirstLaw, policyGame, policySignature, schedule, runPolicies, invoke, players,
    openingFirst, FinDist.map_pure, FinDist.pure_bind, PolicyExecution.initial,
    environmentStep, playerStep, applyNative, EnvironmentCommand.toAction,
    PlayerCommand.toAction, List.nil_append, List.length_cons, List.length_nil,
    List.length_append]
  rfl

private theorem expiryFirst_native :
    expiryFirstLaw.map (fun outcome => outcome.native) =
      FinDist.pure expiryFirstResult := by
  simp only [expiryFirstLaw, policyGame, policySignature, schedule, runPolicies, invoke, players,
    expiryFirst, FinDist.map_pure, FinDist.pure_bind, PolicyExecution.initial,
    environmentStep, playerStep, applyNative, EnvironmentCommand.toAction,
    PlayerCommand.toAction, List.nil_append, List.length_cons, List.length_nil,
    List.length_append]
  rfl

theorem openingFirst_resolution :
    openingFirstLaw.map (fun outcome => outcome.native.application.resolution) =
      FinDist.pure .completed := by
  have h := congrArg (FinDist.map fun state => state.application.resolution)
    openingFirst_native
  rw [FinDist.map_comp] at h
  have hr : openingFirstResult.application.resolution = .completed := rfl
  rw [FinDist.map_pure, hr] at h
  exact h

theorem expiryFirst_resolution :
    expiryFirstLaw.map (fun outcome => outcome.native.application.resolution) =
      FinDist.pure .expired := by
  have h := congrArg (FinDist.map fun state => state.application.resolution)
    expiryFirst_native
  rw [FinDist.map_comp] at h
  have hr : expiryFirstResult.application.resolution = .expired := rfl
  rw [FinDist.map_pure, hr] at h
  exact h

theorem same_players_deliver_opening :
    openingFirstLaw.map (fun outcome =>
      (outcome.native.pool.inbox 0).getLast?.map Message.id) =
        FinDist.pure (some (1, 1)) ∧
    expiryFirstLaw.map (fun outcome =>
      (outcome.native.pool.inbox 0).getLast?.map Message.id) =
        FinDist.pure (some (1, 1)) := by
  constructor
  · have h := congrArg (FinDist.map fun state =>
        (state.pool.inbox 0).getLast?.map Message.id) openingFirst_native
    rw [FinDist.map_comp, FinDist.map_pure] at h
    have hr : (openingFirstResult.pool.inbox 0).getLast?.map Message.id =
        some (1, 1) := rfl
    rw [hr] at h
    exact h
  · have h := congrArg (FinDist.map fun state =>
        (state.pool.inbox 0).getLast?.map Message.id) expiryFirst_native
    rw [FinDist.map_comp, FinDist.map_pure] at h
    have hr : (expiryFirstResult.pool.inbox 0).getLast?.map Message.id =
        some (1, 1) := rfl
    rw [hr] at h
    exact h

end

end VegasTests.PendingTimeoutPolicies

/-- info: 'VegasTests.PendingTimeoutPolicies.openingFirst_resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingTimeoutPolicies.openingFirst_resolution

/-- info: 'VegasTests.PendingTimeoutPolicies.expiryFirst_resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingTimeoutPolicies.expiryFirst_resolution

/-- info: 'VegasTests.PendingTimeoutPolicies.same_players_deliver_opening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingTimeoutPolicies.same_players_deliver_opening
