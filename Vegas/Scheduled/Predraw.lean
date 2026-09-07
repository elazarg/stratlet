/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Protocol.Predraw
import Vegas.Scheduled.Replay

/-! # Predrawing one participant's randomness

Only the selected participant is predrawn. All other participants retain their
behavioral policies and private randomness throughout the comparison.
-/

noncomputable section

namespace Vegas.ScheduledSystem

open GameTheory.Protocol GameTheory.Math.Probability

variable {ι : Type} (sys : ScheduledSystem ι)

/-- Public order/view memory counts every executed round. -/
theorem revealingInfo_past_length (who : Participant ι)
    {state : sys.toExecutionProtocol.State} (trace : sys.toExecutionProtocol.Trace state) :
    (sys.revealingSignals.infoOf who trace).past.length = trace.length := by
  induction trace with
  | start => rfl
  | extend prior _ _ _ ih =>
      change (sys.revealingSignals.infoOf who prior).past.length + 1 = prior.length + 1
      rw [ih]

variable [Fintype ι]

/-- A behavioral scheduler is a mixture of actually executing deterministic
public-history schedulers, with every player's behavioral policy untouched.
The witness is local to the bounded run, which is sufficient for deviation
inequalities and does not assert a uniform finite table for all profiles. -/
theorem exists_predrawScheduler
    (profile : (who : Participant ι) → sys.revealingInformation.BehavioralPolicy who)
    (fuel : Nat) (start : sys.toExecutionProtocol.History) :
    ∃ schedulers : FinDist (sys.revealingInformation.Policy .scheduler),
      (schedulers.bind fun scheduler => sys.revealingInformation.runBehavioralFrom
        (sys.fixScheduler scheduler profile) fuel start) =
      sys.revealingInformation.runBehavioralFrom profile fuel start := by
  classical
  obtain ⟨schedulers, hlaw⟩ := sys.revealingInformation.exists_predrawOne .scheduler
    (fun first later hlength heq => by
      have heqlength := congrArg (fun info => info.past.length) heq
      rw [sys.revealingInfo_past_length, sys.revealingInfo_past_length] at heqlength
      omega) profile fuel start
  refine ⟨schedulers, ?_⟩
  have hupdate : ∀ scheduler : sys.revealingInformation.Policy .scheduler,
      GameTheory.Profile.update (sig := sys.revealingInformation.behavioralSignature)
        profile .scheduler scheduler.toBehavioral =
        sys.fixScheduler scheduler profile := by
    intro scheduler
    funext who
    cases who <;> simp [fixScheduler]
  simpa only [hupdate] using hlaw

end Vegas.ScheduledSystem
