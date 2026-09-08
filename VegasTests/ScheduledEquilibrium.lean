/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.Game
import VegasTests.ScheduledReplay

/-! # End-to-end serializer regressions -/

noncomputable section

namespace VegasTests.ScheduledEquilibrium

open Vegas GameTheory GameTheory.Protocol GameTheory.Math.Probability

/-- A genuinely concurrent compiled game, with arbitrary order-aware
behavioral deviations and an arbitrary public-data behavioral scheduler. -/
example
    (schedulerUtility : matchingPenniesMachine.serializedExecution.History → ℝ)
    (scheduler : matchingPenniesMachine.serializedInformation.BehavioralPolicy .scheduler)
    (profile : (who : TestPlayer) → matchingPenniesMachine.information.BehavioralPolicy who) :
    Participant.IsPlayerNash
      (matchingPenniesMachine.serializedBoundedGame schedulerUtility).behavioral
      (matchingPenniesMachine.compileSerializedBehavioralProfile scheduler profile) ↔
    IsNash matchingPenniesGame.behavioral.form
      (euPreference matchingPenniesGame.behavioral.utility) profile :=
  matchingPenniesMachine.isPlayerNash_compileSerialized_iff schedulerUtility scheduler profile

/-- Automatic chance settlement at the initial history is included in the
complete-law comparison, not assumed away as an already stable initial state. -/
example (scheduler : coinMachine.serializedInformation.BehavioralPolicy .scheduler)
    (profile : (who : TestPlayer) → coinMachine.information.BehavioralPolicy who) :
    (coinMachine.serializedInformation.runBehavioral
      (coinMachine.compileSerializedBehavioralProfile scheduler profile)
      coinMachine.graph.nodeCount).map (fun history => history.state.base) =
    (coinMachine.information.runBehavioral profile coinMachine.graph.nodeCount).map
      ExecutionProtocol.History.state :=
  coinMachine.runBehavioral_compileSerialized scheduler profile

/-- The zero-node terminal game requires no scheduler move or positivity assumption. -/
example (scheduler : emptyMachine.serializedInformation.BehavioralPolicy .scheduler)
    (profile : (who : TestPlayer) → emptyMachine.information.BehavioralPolicy who) :
    (emptyMachine.serializedInformation.runBehavioral
      (emptyMachine.compileSerializedBehavioralProfile scheduler profile)
      emptyMachine.graph.nodeCount).map (fun history => history.state.base) =
    (emptyMachine.information.runBehavioral profile emptyMachine.graph.nodeCount).map
      ExecutionProtocol.History.state :=
  emptyMachine.runBehavioral_compileSerialized scheduler profile

/-- Honest opponents are unchanged even at counterfactual information values. -/
example
    (scheduler : matchingPenniesMachine.serializedSystem.revealingInformation.Policy .scheduler)
    (who : TestPlayer) (policy : matchingPenniesMachine.information.BehavioralPolicy who) :
    matchingPenniesMachine.backtranslateSerializedBehavioralPolicy scheduler who
      (matchingPenniesMachine.compileSerializedBehavioralPolicy who policy) = policy :=
  matchingPenniesMachine.backtranslateSerializedBehavioralPolicy_compile scheduler who policy

/-- Predrawing is valid for the public-data counter example as well as compiled
graphs. The player policies on both sides are literally the same arguments. -/
example
    (profile : (who : Participant (Fin 2)) →
      ScheduledReplay.publicCounter.revealingInformation.BehavioralPolicy who) (fuel : Nat) :
    ∃ schedulers : FinDist (ScheduledReplay.publicCounter.revealingInformation.Policy .scheduler),
      (schedulers.bind fun scheduler =>
        ScheduledReplay.publicCounter.revealingInformation.runBehavioral
          (ScheduledReplay.publicCounter.fixScheduler scheduler profile) fuel) =
      ScheduledReplay.publicCounter.revealingInformation.runBehavioral profile fuel :=
  ScheduledReplay.publicCounter.exists_predrawScheduler profile fuel
    ScheduledReplay.publicCounter.toExecutionProtocol.initHistory

/-- info: 'Vegas.ScheduledSystem.exists_predrawScheduler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ScheduledSystem.exists_predrawScheduler

/-- info: 'Vegas.Machine.Program.backtranslateSerializedBehavioralPolicy_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Machine.Program.backtranslateSerializedBehavioralPolicy_compile

end VegasTests.ScheduledEquilibrium
