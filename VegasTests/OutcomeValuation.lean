/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.SealedOfferRuntime
import Vegas.Scheduled.Valuation

/-! # Allocation and transfer valuations on an unchanged compiled graph

This example reuses the sealed-offer execution, with allocation and monetary
transfer interpreted separately. Buyer value and seller cost are arbitrary
real analysis parameters. This is a family of utility games; private-type
information and physical asset delivery require separate models.
-/

noncomputable section

namespace VegasTests.OutcomeValuation

open Vegas GameTheory GameTheory.Math.Probability OptionalDisclosure

structure Settlement where
  allocated : Bool
  payment : ℝ
  quit : Bool

def settlement (data : RunData) : Settlement :=
  match data.opening with
  | none => ⟨false, 0, true⟩
  | some price => ⟨data.response, if data.response then SealedOffer.amount price else 0, false⟩

def valuation (buyerValue sellerCost : ℝ) (outcome : Settlement) (who : TestPlayer) : ℝ :=
  if who = 0 then
    outcome.payment - (if outcome.allocated then sellerCost else 0) -
      (if outcome.quit then 1 else 0)
  else (if outcome.allocated then buyerValue else 0) - outcome.payment

def observe (state : SealedOffer.machine.State) : Settlement :=
  settlement (decodeConfig state.1)

def graphGame (buyerValue sellerCost : ℝ) : Vegas.BoundedGame TestPlayer :=
  SealedOffer.machine.boundedOutcomeGame observe (valuation buyerValue sellerCost)

/-- Actual all-profile decoded-law correspondence supports independent real
valuations, beyond those expressible by the graph's integer payout list. -/
theorem expected_value (buyerValue sellerCost : ℝ)
    (profile : Profile (graphGame buyerValue sellerCost).behavioral.form.sig) (who : TestPlayer) :
    expectedUtility (graphGame buyerValue sellerCost).utility who
      ((graphGame buyerValue sellerCost).behavioral.form.play profile) =
      (finiteForm.play (extractProfile profile)).expect
        (fun data => valuation buyerValue sellerCost (settlement data) who) := by
  have hlaw := congrArg (fun law : FinDist RunData => law.expect
    (fun data => valuation buyerValue sellerCost (settlement data) who)) (all_profile_law profile)
  simp only [FinDist.expect_map] at hlaw
  exact hlaw

def serializedGame (buyerValue sellerCost : ℝ)
    (schedulerUtility : SealedOffer.machine.serializedExecution.History → ℝ) :=
  SealedOffer.machine.serializedBoundedOutcomeGame observe (valuation buyerValue sellerCost)
    schedulerUtility

def runtimeGame (buyerValue sellerCost : ℝ)
    (schedulerUtility : SealedOffer.machine.serializedExecution.History → ℝ) :=
  (Runtime.RequestCompiler.targetGame SealedOffer.machine.serializedInformation
    SealedOffer.interface SealedOffer.machine.graph.nodeCount
    (serializedGame buyerValue sellerCost schedulerUtility).utility).mixed

def certificate (buyerValue sellerCost : ℝ)
    (schedulerUtility : SealedOffer.machine.serializedExecution.History → ℝ) :
    Runtime.DeviationAdequacy (serializedGame buyerValue sellerCost schedulerUtility).behavioral
      (runtimeGame buyerValue sellerCost schedulerUtility) :=
  (serializedGame buyerValue sellerCost schedulerUtility).requestAdequacy
    (SealedOffer.machine.serializedChoiceFintype SealedOffer.actionFintype)
    SealedOffer.machine.serializedPerfectRecall SealedOffer.interface

/-- Every source Nash profile for this valuation survives the composed
serializer and request implementation. No private-value auction theorem is
assumed or claimed: the source equilibrium remains an explicit premise. -/
theorem runtime_nash (buyerValue sellerCost : ℝ)
    (schedulerUtility : SealedOffer.machine.serializedExecution.History → ℝ)
    (scheduler : SealedOffer.machine.serializedInformation.BehavioralPolicy .scheduler)
    (profile : Profile (graphGame buyerValue sellerCost).behavioral.form.sig)
    (hnash : IsNash (graphGame buyerValue sellerCost).behavioral.form
      (euPreference (graphGame buyerValue sellerCost).utility) profile) :
    Participant.IsPlayerNash (runtimeGame buyerValue sellerCost schedulerUtility)
      ((certificate buyerValue sellerCost schedulerUtility).compileProfile
        (SealedOffer.machine.compileSerializedBehavioralProfile scheduler profile)) := by
  have hs := (SealedOffer.machine.serializedBoundedOutcomeGame_nash_iff observe
    (valuation buyerValue sellerCost) schedulerUtility scheduler profile).mpr hnash
  intro who replacement _
  rw [(certificate buyerValue sellerCost schedulerUtility).expectedUtility_deviation
    _ _ _ trivial]
  exact (hs who
    ((certificate buyerValue sellerCost schedulerUtility).backtranslateStrategy
      (.player who) replacement) trivial).trans_eq
        ((certificate buyerValue sellerCost schedulerUtility).expectedUtility_compileProfile
          _ (.player who)).symm

end VegasTests.OutcomeValuation
