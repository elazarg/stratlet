/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.MatchingPenniesEquilibrium
import Vegas.Scheduled.Request

/-! # The actual hidden-choice program with requests and public orders

This regression uses a designated default action, not an additional quitting
outcome. It checks the compiler composition independently of mechanism design.
-/

noncomputable section

namespace VegasTests.ScheduledRequest

open Vegas GameTheory MatchingPenniesEquilibrium

def sourceInterface := Runtime.RequestCompiler.menuInterface program.information
  program.defaultPureProfile (fun _ _ => 2)

def interface := program.serializedRequestInterface sourceInterface

example : interface.slots .scheduler = fun _ => 0 := rfl

example (who : TestPlayer) (info : program.serializedInformation.InfoState (.player who)) :
    interface.slots (.player who) info = 2 := rfl

example (who : TestPlayer) (info : program.serializedInformation.InfoState (.player who)) :
    ((interface.gate (.player who)).timeoutAction info).1 =
      (program.defaultPureProfile who
        (program.eraseSerializedPlayerInformation who info)).1 := rfl

/-- Every behavioral public-data scheduler is admitted, with arbitrary utility.
The equilibrium test includes every order-aware private request-controller mixture. -/
theorem fair_nash
    (schedulerUtility : program.serializedExecution.History → ℝ)
    (scheduler : program.serializedInformation.BehavioralPolicy .scheduler) :
    Participant.IsPlayerNash
      (matchingPenniesProgram.serializedRequestGame interface schedulerUtility)
      (matchingPenniesProgram.compileSerializedRequestProfile
        interface schedulerUtility scheduler fairPolicy) :=
  (matchingPenniesProgram.serialized_request_nash_iff
    interface schedulerUtility scheduler fairPolicy).mpr fair_isNash

/-- info: 'VegasTests.ScheduledRequest.fair_nash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ScheduledRequest.fair_nash

end VegasTests.ScheduledRequest
