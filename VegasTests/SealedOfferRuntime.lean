/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.SealedOfferEquilibrium

/-! # Sealed offers through private requests and public serialization

The interface remains ideal and request attempts remain private. At disclosure,
timeout selects the existing quit action. Initial and reply timeouts select
existing game actions, not additional quitting settlements.
-/

noncomputable section

namespace VegasTests.SealedOffer

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability
open OptionalDisclosure

@[reducible] def nodeFintype : ∀ index : Fin 8,
    Fintype (simpleExpr.Val (graph.nodeRow (node index)).ty)
  | 0 => inferInstanceAs (Fintype Bool)
  | 1 => inferInstanceAs (Fintype Bool)
  | 2 => inferInstanceAs (Fintype Bool)
  | 3 => inferInstanceAs (Fintype Bool)
  | 4 => inferInstanceAs (Fintype (Option Bool))
  | 5 => inferInstanceAs (Fintype (Option Bool))
  | 6 => inferInstanceAs (Fintype Bool)
  | 7 => inferInstanceAs (Fintype Bool)

@[reducible] def actionFintype (who : TestPlayer) : Fintype (machine.execution.Action who) := by
  letI : ∀ index : Fin graph.nodeCount,
      Fintype (simpleExpr.Val (graph.nodeRow index).ty) := nodeFintype
  exact FrontierAction.instFintype graph who

def timeoutPolicy : ∀ who, machine.information.Policy who
  | 0, info => by
      classical
      let input := decodeOpeningInfo info
      exact if hinfo : openingInfo input.1 input.2 = info then
        hinfo ▸ openingChoiceAt input.1 input.2 false
      else Function.update (program.defaultPureProfile 0) bindingInfo (bindingChoice false) info
  | 1, info => by
      classical
      let input := decodeResponseInfo info
      exact if hinfo : responseInfo input.1 input.2 = info then
        hinfo ▸ responseChoiceAt input.1 input.2 false
      else program.defaultPureProfile 1 info

theorem timeout_disclosure (secret signal : Bool) :
    (timeoutPolicy 0 (openingInfo secret signal)).1 = some (openingAction none) := by
  unfold timeoutPolicy
  dsimp only
  rw [decode_openingInfo]
  simp
  rfl

def sourceInterface := Runtime.RequestCompiler.menuInterface machine.information
  timeoutPolicy (fun _ _ => 2)

def interface := machine.serializedRequestInterface sourceInterface

def runtimeGame (schedulerUtility : machine.serializedExecution.History → ℝ) :
    UtilityGame (Participant TestPlayer) :=
  (Runtime.RequestCompiler.targetGame machine.serializedInformation interface
    machine.graph.nodeCount (machine.serializedUtility schedulerUtility)).mixed

def certificate (schedulerUtility : machine.serializedExecution.History → ℝ) :
    Runtime.DeviationAdequacy (machine.serializedBoundedGame schedulerUtility).behavioral
      (runtimeGame schedulerUtility) :=
  (machine.serializedBoundedGame schedulerUtility).requestAdequacy
    (machine.serializedChoiceFintype actionFintype) machine.serializedPerfectRecall interface

def runtimeProfile (schedulerUtility : machine.serializedExecution.History → ℝ)
    (scheduler : machine.serializedInformation.BehavioralPolicy .scheduler) :
    Profile (runtimeGame schedulerUtility).form.sig :=
  (certificate schedulerUtility).compileProfile
    (machine.compileSerializedBehavioralProfile scheduler (compileProfile honestProfile))

/-- All original-player request-controller mixtures are tested, including
combined changes to game decisions, retry behavior, and use of public orders. -/
theorem runtime_honest_isPlayerNash
    (schedulerUtility : machine.serializedExecution.History → ℝ)
    (scheduler : machine.serializedInformation.BehavioralPolicy .scheduler) :
    Participant.IsPlayerNash (runtimeGame schedulerUtility)
      (runtimeProfile schedulerUtility scheduler) := by
  intro who replacement _
  change expectedUtility _ _ ((runtimeGame schedulerUtility).form.play
    (Profile.update ((certificate schedulerUtility).compileProfile _) _ _)) ≤ _
  rw [(certificate schedulerUtility).expectedUtility_deviation _ _ _ trivial]
  have hsource := serialized_honest_isPlayerNash schedulerUtility scheduler who
    ((certificate schedulerUtility).backtranslateStrategy (.player who) replacement) trivial
  exact hsource.trans_eq
      ((certificate schedulerUtility).expectedUtility_compileProfile _ (.player who)).symm

/-- The honest buyer's guarantee survives arbitrary seller controller mixtures
under every admitted public-data scheduler, with the same buyer and payoffs. -/
theorem runtime_buyer_nonnegative
    (schedulerUtility : machine.serializedExecution.History → ℝ)
    (scheduler : machine.serializedInformation.BehavioralPolicy .scheduler)
    (replacement : (runtimeGame schedulerUtility).form.sig.Strategy (.player 0)) :
    0 ≤ expectedUtility (runtimeGame schedulerUtility).utility (.player 1)
      ((runtimeGame schedulerUtility).form.play
        (Profile.update (runtimeProfile schedulerUtility scheduler) (.player 0) replacement)) := by
  have hlaw := (certificate schedulerUtility).deviation_law
    (machine.compileSerializedBehavioralProfile scheduler (compileProfile honestProfile))
    (.player 0) replacement trivial
  have hvalue := congrArg (fun law => expectedUtility
    (machine.serializedBoundedGame schedulerUtility).behavioral.utility (.player 1) law) hlaw
  rw [expectedUtility_map] at hvalue
  exact (serialized_buyer_nonnegative schedulerUtility scheduler
    ((certificate schedulerUtility).backtranslateStrategy (.player 0) replacement)).trans_eq
      hvalue.symm

end VegasTests.SealedOffer
