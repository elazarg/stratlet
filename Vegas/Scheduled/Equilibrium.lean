/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Scheduled.Law
import Vegas.Scheduled.Predraw
import Vegas.Scheduled.Strategic
import GameTheory.Core.Approximate

/-! # Equilibrium preservation for the actual serialized game -/

noncomputable section

namespace Vegas.Machine.Program

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

/-- Translate each runtime player separately; the scheduler is not a source player. -/
def backtranslateSerializedBehavioralProfile (program : Program Player L)
    (scheduler : program.serializedSystem.revealingInformation.Policy .scheduler)
    (profile : (who : Participant Player) →
      program.serializedInformation.BehavioralPolicy who) :
    (who : Player) → program.information.BehavioralPolicy who :=
  fun who => program.backtranslateSerializedBehavioralPolicy scheduler who (profile (.player who))

/-- Canonical back-translation preserves complete runtime histories, not only
their payoffs, under a fixed executing public-data scheduler. -/
theorem runBehavioralFrom_backtranslateSerialized (program : Program Player L)
    (scheduler : program.serializedSystem.revealingInformation.Policy .scheduler)
    (profile : (who : Participant Player) →
      program.serializedInformation.BehavioralPolicy who)
    (hscheduler : profile .scheduler = scheduler.toBehavioral)
    (fuel : Nat) (start : program.serializedExecution.History)
    (hfollows : program.serializedSystem.SchedulerFollows scheduler start.trace) :
    program.serializedInformation.runBehavioralFrom profile fuel start =
      program.serializedInformation.runBehavioralFrom
        (program.compileSerializedBehavioralProfile scheduler.toBehavioral
          (program.backtranslateSerializedBehavioralProfile scheduler profile)) fuel start := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      by_cases hterm : program.serializedExecution.terminal start.state
      · rw [InformationModel.runBehavioralFrom_of_terminal _ _ _ hterm,
          InformationModel.runBehavioralFrom_of_terminal _ _ _ hterm]
      · have hhere : program.serializedInformation.behavioralJoint profile start.trace hterm =
            program.serializedInformation.behavioralJoint
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
      program.serializedInformation.BehavioralPolicy who)
    (hscheduler : profile .scheduler = scheduler.toBehavioral) :
    (program.serializedInformation.runBehavioral profile program.graph.nodeCount).map
      (fun history => history.state.base) =
    (program.information.runBehavioral
      (program.backtranslateSerializedBehavioralProfile scheduler profile)
      program.graph.nodeCount).map ExecutionProtocol.History.state := by
  change (program.serializedInformation.runBehavioralFrom profile _ _).map _ = _
  rw [program.runBehavioralFrom_backtranslateSerialized scheduler profile hscheduler _
    program.serializedExecution.initHistory trivial]
  exact program.runBehavioral_compileSerialized scheduler.toBehavioral _

/-- Expected utility of every compiled original player is independent of the
behavioral scheduler, whose utility is deliberately unconstrained. -/
theorem expectedUtility_compileSerialized (program : Program Player L)
    (schedulerUtility : program.serializedExecution.History → ℝ)
    (scheduler : program.serializedInformation.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) (who : Player) :
    expectedUtility
      (program.serializedBoundedGame schedulerUtility).behavioral.utility (.player who)
      ((program.serializedBoundedGame schedulerUtility).behavioral.form.play
        (program.compileSerializedBehavioralProfile scheduler profile)) =
    expectedUtility program.boundedGame.behavioral.utility who
      (program.boundedGame.behavioral.form.play profile) := by
  have heq := congrArg
    (fun law => law.expect (fun state => program.payoutUtility state who))
    (program.runBehavioral_compileSerialized scheduler profile)
  change (program.serializedInformation.runBehavioral
    (program.compileSerializedBehavioralProfile scheduler profile) program.graph.nodeCount).expect
      (fun history => program.payoutUtility history.state.base who) =
    (program.information.runBehavioral profile program.graph.nodeCount).expect
      (fun history => program.payoutUtility history.state who)
  simpa only [FinDist.expect_map] using heq

/-- Unilateral target deviations translate to unilateral source deviations:
every honest opponent remains exactly its original behavioral source policy. -/
theorem backtranslateSerialized_update (program : Program Player L)
    (scheduler : program.serializedSystem.revealingInformation.Policy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) (who : Player)
    (replacement : program.serializedInformation.BehavioralPolicy (.player who)) :
    program.backtranslateSerializedBehavioralProfile scheduler
      (Profile.update (sig := (program.serializedBoundedGame (fun _ => 0)).behavioral.form.sig)
        (program.compileSerializedBehavioralProfile scheduler.toBehavioral profile)
        (.player who) replacement) =
    Profile.update (sig := program.boundedGame.behavioral.form.sig) profile who
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
    (schedulerUtility : program.serializedExecution.History → ℝ)
    (scheduler : program.serializedSystem.revealingInformation.Policy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) (who : Player)
    (replacement : program.serializedInformation.BehavioralPolicy (.player who)) :
    expectedUtility
      (program.serializedBoundedGame schedulerUtility).behavioral.utility (.player who)
      ((program.serializedBoundedGame schedulerUtility).behavioral.form.play
        (Profile.update (program.compileSerializedBehavioralProfile scheduler.toBehavioral profile)
          (.player who) replacement)) =
    expectedUtility program.boundedGame.behavioral.utility who
      (program.boundedGame.behavioral.form.play (Profile.update profile who
        (program.backtranslateSerializedBehavioralPolicy scheduler who replacement))) := by
  have heq := program.runBehavioral_backtranslateSerialized scheduler
    (Profile.update (sig := (program.serializedBoundedGame schedulerUtility).behavioral.form.sig)
      (program.compileSerializedBehavioralProfile scheduler.toBehavioral profile)
      (.player who) replacement) (by simp [Profile.update, compileSerializedBehavioralProfile])
  rw [program.backtranslateSerialized_update] at heq
  have hpay := congrArg
    (fun law => law.expect (fun state => program.payoutUtility state who))
    heq
  change (program.serializedInformation.runBehavioral _ program.graph.nodeCount).expect
      (fun history => program.payoutUtility history.state.base who) =
    (program.information.runBehavioral _ program.graph.nodeCount).expect
      (fun history => program.payoutUtility history.state who)
  simpa only [FinDist.expect_map] using hpay

/-- Every unilateral runtime deviation has a terminal-state law which is a
finite mixture of unilateral source-deviation laws against the *same* honest
opponents. The mixture may depend on the profile and horizon; it is not a
uniform translator for all counterfactual opponent profiles. No rationality or
equilibrium assumption is made about any participant. -/
theorem serializedDeviation_eq_sourceMixture (program : Program Player L)
    (scheduler : program.serializedInformation.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) (who : Player)
    (replacement : program.serializedInformation.BehavioralPolicy (.player who)) :
    ∃ replacements : FinDist (program.information.BehavioralPolicy who),
      (program.serializedInformation.runBehavioral
        (Function.update (program.compileSerializedBehavioralProfile scheduler profile)
          (.player who) replacement) program.graph.nodeCount).map
            (fun history => history.state.base) =
      replacements.bind fun alternative =>
        (program.information.runBehavioral (Function.update profile who alternative)
          program.graph.nodeCount).map ExecutionProtocol.History.state := by
  let deviated := Function.update
    (program.compileSerializedBehavioralProfile scheduler profile) (.player who) replacement
  obtain ⟨schedulers, hlaw⟩ := program.serializedSystem.exists_predrawScheduler
    deviated program.graph.nodeCount program.serializedExecution.initHistory
  refine ⟨schedulers.map (fun pureScheduler =>
    program.backtranslateSerializedBehavioralPolicy pureScheduler who replacement), ?_⟩
  have hfixed : ∀ pureScheduler,
      program.serializedSystem.fixScheduler pureScheduler deviated =
      Profile.update (sig := (program.serializedBoundedGame (fun _ => 0)).behavioral.form.sig)
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
          simp [ScheduledSystem.fixScheduler, deviated, Profile.update]
        · simp [ScheduledSystem.fixScheduler, deviated, Profile.update, heq,
            compileSerializedBehavioralProfile]
  change (program.serializedSystem.revealingInformation.runBehavioralFrom deviated
    program.graph.nodeCount program.serializedExecution.initHistory).map _ = _
  rw [← hlaw, FinDist.map_bind, FinDist.bind_map]
  apply FinDist.bind_congr
  intro pureScheduler _
  rw [hfixed]
  have htranslate := program.runBehavioral_backtranslateSerialized pureScheduler
    (Profile.update (sig := (program.serializedBoundedGame (fun _ => 0)).behavioral.form.sig)
      (program.compileSerializedBehavioralProfile pureScheduler.toBehavioral profile)
      (.player who) replacement) (by simp [Profile.update, compileSerializedBehavioralProfile])
  rw [program.backtranslateSerialized_update] at htranslate
  exact htranslate

/-- Exact source expectations also survive every unilateral runtime deviation.
The observable need not be a utility or belong to the deviating player. -/
theorem serializedDeviation_expect_eq (program : Program Player L)
    (scheduler : program.serializedInformation.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) (who : Player)
    (observable : program.State → ℝ) (value : ℝ)
    (hvalue : ∀ alternative : program.information.BehavioralPolicy who,
      (program.information.runBehavioral (Function.update profile who alternative)
        program.graph.nodeCount).expect (fun history => observable history.state) = value)
    (replacement : program.serializedInformation.BehavioralPolicy (.player who)) :
    (program.serializedInformation.runBehavioral
      (Function.update (program.compileSerializedBehavioralProfile scheduler profile)
        (.player who) replacement) program.graph.nodeCount).expect
          (fun history => observable history.state.base) = value := by
  obtain ⟨replacements, hlaw⟩ := program.serializedDeviation_eq_sourceMixture
    scheduler profile who replacement
  have hexpect := congrArg (fun law => law.expect observable) hlaw
  rw [FinDist.expect_map, FinDist.expect_bind] at hexpect
  rw [hexpect]
  calc
    _ = replacements.expect (fun _ => value) := by
      apply FinDist.expect_congr
      intro alternative _
      simpa only [FinDist.expect_map] using hvalue alternative
    _ = value := FinDist.expect_const _ _

/-- Any source bound on any terminal-state loss survives arbitrary unilateral
runtime deviations and arbitrary public-data behavioral scheduling. The loss
can measure harm to an honest player, not merely the deviator's own utility. -/
theorem serializedDeviation_expect_le (program : Program Player L)
    (scheduler : program.serializedInformation.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) (who : Player)
    (loss : program.State → ℝ) (bound : ℝ)
    (hbound : ∀ alternative : program.information.BehavioralPolicy who,
      (program.information.runBehavioral (Function.update profile who alternative)
        program.graph.nodeCount).expect (fun history => loss history.state) ≤ bound)
    (replacement : program.serializedInformation.BehavioralPolicy (.player who)) :
    (program.serializedInformation.runBehavioral
      (Function.update (program.compileSerializedBehavioralProfile scheduler profile)
        (.player who) replacement) program.graph.nodeCount).expect
          (fun history => loss history.state.base) ≤ bound := by
  obtain ⟨replacements, hlaw⟩ := program.serializedDeviation_eq_sourceMixture
    scheduler profile who replacement
  have hexpect := congrArg (fun law => law.expect loss) hlaw
  rw [FinDist.expect_map, FinDist.expect_bind] at hexpect
  rw [hexpect]
  calc
    _ ≤ replacements.expect (fun _ => bound) := by
      apply FinDist.expect_mono
      intro alternative _
      simpa only [FinDist.expect_map] using hbound alternative
    _ = bound := FinDist.expect_const _ _

/-- A source behavioral Nash equilibrium remains Nash for the original
players against all behavioral runtime deviations. The fixed scheduler may
react arbitrarily to public data; it is not tested as an equilibrium player. -/
theorem isPlayerNash_compileSerialized_pureScheduler (program : Program Player L)
    (schedulerUtility : program.serializedExecution.History → ℝ)
    (scheduler : program.serializedSystem.revealingInformation.Policy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (hnash : IsNash program.boundedGame.behavioral.form
      (euPreference program.boundedGame.behavioral.utility) profile) :
    Participant.IsPlayerNash (program.serializedBoundedGame schedulerUtility).behavioral
      (program.compileSerializedBehavioralProfile scheduler.toBehavioral profile) := by
  intro who replacement _
  rw [program.expectedUtility_backtranslateSerialized_update,
    program.expectedUtility_compileSerialized]
  exact (isNash_iff (F := program.boundedGame.behavioral.form) profile).mp hnash who
    (program.backtranslateSerializedBehavioralPolicy scheduler who replacement)

/-- Behavioral scheduler randomization cannot introduce a profitable player
deviation. Each predrawn scheduler actually reacts to the observed public
history. The averaging argument fixes no honest player's random choices. -/
theorem isPlayerNash_compileSerialized_of_isNash (program : Program Player L)
    (schedulerUtility : program.serializedExecution.History → ℝ)
    (scheduler : program.serializedInformation.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (hnash : IsNash program.boundedGame.behavioral.form
      (euPreference program.boundedGame.behavioral.utility) profile) :
    Participant.IsPlayerNash (program.serializedBoundedGame schedulerUtility).behavioral
      (program.compileSerializedBehavioralProfile scheduler profile) := by
  intro who replacement _
  rw [program.expectedUtility_compileSerialized]
  exact program.serializedDeviation_expect_le scheduler profile who
    (fun state => program.payoutUtility state who) _
    (fun alternative => (isNash_iff (F := program.boundedGame.behavioral.form) profile).mp
      hnash who alternative) replacement

/-- Compilation commutes with a unilateral source deviation. -/
theorem compileSerialized_update (program : Program Player L)
    (scheduler : program.serializedInformation.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) (who : Player)
    (replacement : program.information.BehavioralPolicy who) :
    program.compileSerializedBehavioralProfile scheduler
      (Profile.update (sig := program.boundedGame.behavioral.form.sig) profile who replacement) =
    Profile.update (sig := (program.serializedBoundedGame (fun _ => 0)).behavioral.form.sig)
      (program.compileSerializedBehavioralProfile scheduler profile) (.player who)
      (program.compileSerializedBehavioralPolicy who replacement) := by
  funext participant
  cases participant with
  | scheduler => simp [compileSerializedBehavioralProfile, Profile.update]
  | player other =>
      by_cases heq : other = who
      · subst other; simp [compileSerializedBehavioralProfile]
      · simp [compileSerializedBehavioralProfile, Profile.update, heq]

/-- Exact preservation and reflection of every unilateral terminal-loss bound.
This characterizes worst-case expected harm without assuming existence of a
best response, bounded utilities, equilibrium, or adversarial rationality. -/
theorem serializedDeviation_expect_bound_iff (program : Program Player L)
    (scheduler : program.serializedInformation.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) (who : Player)
    (loss : program.State → ℝ) (bound : ℝ) :
    (∀ replacement : program.serializedInformation.BehavioralPolicy (.player who),
      (program.serializedInformation.runBehavioral
        (Function.update (program.compileSerializedBehavioralProfile scheduler profile)
          (.player who) replacement) program.graph.nodeCount).expect
            (fun history => loss history.state.base) ≤ bound) ↔
    (∀ alternative : program.information.BehavioralPolicy who,
      (program.information.runBehavioral (Function.update profile who alternative)
        program.graph.nodeCount).expect (fun history => loss history.state) ≤ bound) := by
  constructor
  · intro hbound alternative
    have htarget := hbound (program.compileSerializedBehavioralPolicy who alternative)
    have hupdate := program.compileSerialized_update scheduler profile who alternative
    change program.compileSerializedBehavioralProfile scheduler
      (Function.update profile who alternative) = Function.update
        (program.compileSerializedBehavioralProfile scheduler profile) (.player who)
        (program.compileSerializedBehavioralPolicy who alternative) at hupdate
    rw [← hupdate] at htarget
    have hlaw := congrArg (fun law => law.expect loss)
      (program.runBehavioral_compileSerialized scheduler (Function.update profile who alternative))
    simp only [FinDist.expect_map] at hlaw
    exact hlaw ▸ htarget
  · exact fun hbound => program.serializedDeviation_expect_le
      scheduler profile who loss bound hbound

/-- Approximate equilibrium is preserved with exactly the same error budget.
Only original-player deviations are tested in the implementation. -/
theorem serialized_approximate_nash_iff (program : Program Player L)
    (schedulerUtility : program.serializedExecution.History → ℝ)
    (scheduler : program.serializedInformation.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) (ε : ℝ) :
    (∀ who replacement,
      expectedUtility
        (program.serializedBoundedGame schedulerUtility).behavioral.utility (.player who)
        ((program.serializedBoundedGame schedulerUtility).behavioral.form.play
          (Profile.update (program.compileSerializedBehavioralProfile scheduler profile)
            (.player who) replacement)) ≤
      expectedUtility
        (program.serializedBoundedGame schedulerUtility).behavioral.utility (.player who)
        ((program.serializedBoundedGame schedulerUtility).behavioral.form.play
          (program.compileSerializedBehavioralProfile scheduler profile)) + ε) ↔
    IsεNash program.boundedGame.behavioral.form
      program.boundedGame.behavioral.utility ε profile := by
  rw [isεNash_iff]
  simp only [program.expectedUtility_compileSerialized]
  apply forall_congr'
  intro who
  exact program.serializedDeviation_expect_bound_iff scheduler profile who
    (fun state => program.payoutUtility state who) _

/-- **End-to-end behavioral Nash equivalence for the actual serializer.**
For every public-data behavioral scheduler, compiled source profiles are Nash
for the original players exactly when they were Nash in the canonical atomic
source game. All behavioral player deviations are admitted. Scheduler utility
and scheduler optimality play no role. -/
theorem isPlayerNash_compileSerialized_iff (program : Program Player L)
    (schedulerUtility : program.serializedExecution.History → ℝ)
    (scheduler : program.serializedInformation.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) :
    Participant.IsPlayerNash (program.serializedBoundedGame schedulerUtility).behavioral
      (program.compileSerializedBehavioralProfile scheduler profile) ↔
    IsNash program.boundedGame.behavioral.form
      (euPreference program.boundedGame.behavioral.utility) profile := by
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
