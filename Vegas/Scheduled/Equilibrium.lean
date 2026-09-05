/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Scheduled.Law
import Vegas.Scheduled.Predraw
import Vegas.Scheduled.Strategic

/-! # Equilibrium preservation for the actual serialized game -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Vegas.Machine.Program

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

/-- Translate each runtime player separately; the scheduler is not a source player. -/
def backtranslateSerializedBehavioralProfile (program : Program Player L)
    (scheduler : program.serializedSystem.revealingInformation.Policy .scheduler)
    (profile : (who : Participant Player) →
      program.serializedArena.information.BehavioralPolicy who) :
    (who : Player) → program.information.BehavioralPolicy who :=
  fun who => program.backtranslateSerializedBehavioralPolicy scheduler who (profile (.player who))

/-- Canonical back-translation preserves complete runtime histories, not only
their payoffs, under a fixed executing public-data scheduler. -/
theorem runBehavioralFrom_backtranslateSerialized (program : Program Player L)
    (scheduler : program.serializedSystem.revealingInformation.Policy .scheduler)
    (profile : (who : Participant Player) →
      program.serializedArena.information.BehavioralPolicy who)
    (hscheduler : profile .scheduler = scheduler.toBehavioral)
    (fuel : Nat) (start : program.serializedArena.History)
    (hfollows : program.serializedSystem.SchedulerFollows scheduler start.trace) :
    program.serializedArena.information.runBehavioralFrom profile fuel start =
      program.serializedArena.information.runBehavioralFrom
        (program.compileSerializedBehavioralProfile scheduler.toBehavioral
          (program.backtranslateSerializedBehavioralProfile scheduler profile)) fuel start := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      by_cases hterm : program.serializedArena.execution.terminal start.state
      · rw [InformationModel.runBehavioralFrom_of_terminal _ _ _ hterm,
          InformationModel.runBehavioralFrom_of_terminal _ _ _ hterm]
      · have hhere : program.serializedArena.information.behavioralJoint profile start.trace hterm =
            program.serializedArena.information.behavioralJoint
              (program.compileSerializedBehavioralProfile scheduler.toBehavioral
                (program.backtranslateSerializedBehavioralProfile scheduler profile))
                start.trace hterm := by
          apply InformationModel.behavioralJoint_congr
          intro who
          cases who with
          | scheduler => rw [hscheduler]; rfl
          | player who =>
              apply FinDist.map_injective Subtype.val_injective
              exact (program.backtranslateSerializedBehavioralPolicy_law scheduler who
                (profile (.player who)) start.trace hfollows).symm
        rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ hterm,
          InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ hterm, ← hhere]
        apply FinDist.bind_congr
        intro command hcommand
        apply FinDist.bindOnSupport_congr
        intro next realized
        apply ih
        exact ⟨hfollows, program.serializedSystem.behavioralJoint_scheduler_eq scheduler
          profile hscheduler start.trace hterm hcommand⟩

/-- Arbitrary behavioral runtime players under a fixed scheduler have exactly
the terminal-state law of their canonical source back-translations. -/
theorem runBehavioral_backtranslateSerialized (program : Program Player L)
    (scheduler : program.serializedSystem.revealingInformation.Policy .scheduler)
    (profile : (who : Participant Player) →
      program.serializedArena.information.BehavioralPolicy who)
    (hscheduler : profile .scheduler = scheduler.toBehavioral) :
    (program.serializedArena.information.runBehavioral profile program.graph.nodeCount).map
      (fun history => history.state.base) =
    (program.information.runBehavioral
      (program.backtranslateSerializedBehavioralProfile scheduler profile)
      program.graph.nodeCount).map ExecutionProtocol.History.state := by
  change (program.serializedArena.information.runBehavioralFrom profile _ _).map _ = _
  rw [program.runBehavioralFrom_backtranslateSerialized scheduler profile hscheduler _
    program.serializedArena.execution.initHistory trivial]
  exact program.runBehavioral_compileSerialized scheduler.toBehavioral _

/-- Expected utility of every compiled original player is independent of the
behavioral scheduler, whose utility is deliberately unconstrained. -/
theorem expectedUtility_compileSerialized (program : Program Player L)
    (schedulerUtility : program.serializedArena.History → ℝ)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) (who : Player) :
    expectedUtility (program.serializedGame schedulerUtility).behavioral.utility (.player who)
      ((program.serializedGame schedulerUtility).behavioral.form.play
        (program.compileSerializedBehavioralProfile scheduler profile)) =
    expectedUtility program.game.behavioral.utility who
      (program.game.behavioral.form.play profile) := by
  have heq := congrArg
    (fun law => law.expect (fun state => program.settledPlayerUtility state who))
    (program.runBehavioral_compileSerialized scheduler profile)
  change (program.serializedArena.information.runBehavioral
    (program.compileSerializedBehavioralProfile scheduler profile) program.graph.nodeCount).expect
      (fun history => program.settledPlayerUtility history.state.base who) =
    (program.information.runBehavioral profile program.graph.nodeCount).expect
      (fun history => program.settledPlayerUtility history.state who)
  simpa only [FinDist.expect_map] using heq

/-- Unilateral target deviations translate to unilateral source deviations:
every honest opponent remains exactly its original behavioral source policy. -/
theorem backtranslateSerialized_update (program : Program Player L)
    (scheduler : program.serializedSystem.revealingInformation.Policy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) (who : Player)
    (replacement : program.serializedArena.information.BehavioralPolicy (.player who)) :
    program.backtranslateSerializedBehavioralProfile scheduler
      (Profile.update (sig := (program.serializedGame (fun _ => 0)).behavioral.form.sig)
        (program.compileSerializedBehavioralProfile scheduler.toBehavioral profile)
        (.player who) replacement) =
    Profile.update (sig := program.game.behavioral.form.sig) profile who
      (program.backtranslateSerializedBehavioralPolicy
      scheduler who replacement) := by
  funext other
  by_cases heq : other = who
  · subst other
    simp [backtranslateSerializedBehavioralProfile]
  · simp [backtranslateSerializedBehavioralProfile, Profile.update, heq,
      compileSerializedBehavioralProfile, program.backtranslateSerializedBehavioralPolicy_compile]

/-- Exact unilateral-deviation payoff equality for the actual serialized game. -/
theorem expectedUtility_backtranslateSerialized_update (program : Program Player L)
    (schedulerUtility : program.serializedArena.History → ℝ)
    (scheduler : program.serializedSystem.revealingInformation.Policy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) (who : Player)
    (replacement : program.serializedArena.information.BehavioralPolicy (.player who)) :
    expectedUtility (program.serializedGame schedulerUtility).behavioral.utility (.player who)
      ((program.serializedGame schedulerUtility).behavioral.form.play
        (Profile.update (program.compileSerializedBehavioralProfile scheduler.toBehavioral profile)
          (.player who) replacement)) =
    expectedUtility program.game.behavioral.utility who
      (program.game.behavioral.form.play (Profile.update profile who
        (program.backtranslateSerializedBehavioralPolicy scheduler who replacement))) := by
  have heq := program.runBehavioral_backtranslateSerialized scheduler
    (Profile.update (sig := (program.serializedGame schedulerUtility).behavioral.form.sig)
      (program.compileSerializedBehavioralProfile scheduler.toBehavioral profile)
      (.player who) replacement) (by simp [Profile.update, compileSerializedBehavioralProfile])
  rw [program.backtranslateSerialized_update] at heq
  have hpay := congrArg
    (fun law => law.expect (fun state => program.settledPlayerUtility state who))
    heq
  change (program.serializedArena.information.runBehavioral _ program.graph.nodeCount).expect
      (fun history => program.settledPlayerUtility history.state.base who) =
    (program.information.runBehavioral _ program.graph.nodeCount).expect
      (fun history => program.settledPlayerUtility history.state who)
  simpa only [FinDist.expect_map] using hpay

/-- A source behavioral Nash equilibrium remains Nash for the original
players against all behavioral runtime deviations. The fixed scheduler may
react arbitrarily to public data; it is not tested as an equilibrium player. -/
theorem isPlayerNash_compileSerialized_pureScheduler (program : Program Player L)
    (schedulerUtility : program.serializedArena.History → ℝ)
    (scheduler : program.serializedSystem.revealingInformation.Policy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (hnash : IsNash program.game.behavioral.form
      (euPreference program.game.behavioral.utility) profile) :
    Scheduled.IsPlayerNash (program.serializedGame schedulerUtility).behavioral
      (program.compileSerializedBehavioralProfile scheduler.toBehavioral profile) := by
  intro who replacement _
  rw [program.expectedUtility_backtranslateSerialized_update,
    program.expectedUtility_compileSerialized]
  exact (isNash_iff (F := program.game.behavioral.form) profile).mp hnash who
    (program.backtranslateSerializedBehavioralPolicy scheduler who replacement)

/-- Behavioral scheduler randomization cannot introduce a profitable player
deviation. Each predrawn scheduler actually reacts to the observed public
history. The averaging argument fixes no honest player's random choices. -/
theorem isPlayerNash_compileSerialized_of_isNash (program : Program Player L)
    (schedulerUtility : program.serializedArena.History → ℝ)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (hnash : IsNash program.game.behavioral.form
      (euPreference program.game.behavioral.utility) profile) :
    Scheduled.IsPlayerNash (program.serializedGame schedulerUtility).behavioral
      (program.compileSerializedBehavioralProfile scheduler profile) := by
  intro who replacement _
  let deviated := Profile.update
    (sig := (program.serializedGame schedulerUtility).behavioral.form.sig)
    (program.compileSerializedBehavioralProfile scheduler profile) (.player who) replacement
  obtain ⟨schedulers, hlaw⟩ := program.serializedSystem.exists_predrawScheduler
    deviated program.graph.nodeCount program.serializedArena.execution.initHistory
  have hfixed : ∀ pureScheduler,
      program.serializedSystem.fixScheduler pureScheduler deviated =
      Profile.update (sig := (program.serializedGame schedulerUtility).behavioral.form.sig)
        (program.compileSerializedBehavioralProfile pureScheduler.toBehavioral profile)
        (.player who) replacement := by
    intro pureScheduler
    funext participant
    cases participant with
    | scheduler => simp [ScheduledSystem.fixScheduler, Profile.update,
        compileSerializedBehavioralProfile]
    | player other =>
        by_cases heq : other = who
        · subst other
          simp [ScheduledSystem.fixScheduler, deviated]
        · simp [ScheduledSystem.fixScheduler, deviated, Profile.update, heq,
            compileSerializedBehavioralProfile]
  rw [program.expectedUtility_compileSerialized]
  change expectedUtility (program.serializedUtility schedulerUtility) (.player who)
    (program.serializedSystem.revealingInformation.runBehavioralFrom deviated
      program.graph.nodeCount program.serializedArena.execution.initHistory) ≤ _
  rw [← hlaw, expectedUtility_bind]
  calc
    _ ≤ schedulers.expect (fun _ => expectedUtility program.game.behavioral.utility who
        (program.game.behavioral.form.play profile)) := by
      apply FinDist.expect_mono
      intro pureScheduler _
      rw [hfixed]
      change expectedUtility (program.serializedGame schedulerUtility).behavioral.utility
        (.player who) ((program.serializedGame schedulerUtility).behavioral.form.play _) ≤ _
      rw [program.expectedUtility_backtranslateSerialized_update]
      exact (isNash_iff (F := program.game.behavioral.form) profile).mp hnash who _
    _ = _ := FinDist.expect_const _ _

/-- Compilation commutes with a unilateral source deviation. -/
theorem compileSerialized_update (program : Program Player L)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) (who : Player)
    (replacement : program.information.BehavioralPolicy who) :
    program.compileSerializedBehavioralProfile scheduler
      (Profile.update (sig := program.game.behavioral.form.sig) profile who replacement) =
    Profile.update (sig := (program.serializedGame (fun _ => 0)).behavioral.form.sig)
      (program.compileSerializedBehavioralProfile scheduler profile) (.player who)
      (program.compileSerializedBehavioralPolicy who replacement) := by
  funext participant
  cases participant with
  | scheduler => simp [compileSerializedBehavioralProfile, Profile.update]
  | player other =>
      by_cases heq : other = who
      · subst other; simp [compileSerializedBehavioralProfile]
      · simp [compileSerializedBehavioralProfile, Profile.update, heq]

/-- **End-to-end behavioral Nash equivalence for the actual serializer.**
For every public-data behavioral scheduler, compiled source profiles are Nash
for the original players exactly when they were Nash in the canonical atomic
source game. All behavioral player deviations are admitted. Scheduler utility
and scheduler optimality play no role. -/
theorem isPlayerNash_compileSerialized_iff (program : Program Player L)
    (schedulerUtility : program.serializedArena.History → ℝ)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) :
    Scheduled.IsPlayerNash (program.serializedGame schedulerUtility).behavioral
      (program.compileSerializedBehavioralProfile scheduler profile) ↔
    IsNash program.game.behavioral.form (euPreference program.game.behavioral.utility) profile := by
  constructor
  · intro hnash
    rw [isNash_iff]
    intro who replacement
    have htarget := hnash who (program.compileSerializedBehavioralPolicy who replacement) trivial
    rw [← program.compileSerialized_update, program.expectedUtility_compileSerialized,
      program.expectedUtility_compileSerialized] at htarget
    exact htarget
  · exact program.isPlayerNash_compileSerialized_of_isNash schedulerUtility scheduler profile

end Vegas.Machine.Program
