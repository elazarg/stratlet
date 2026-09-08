/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Protocol.Strategic
import Vegas.Game.Basic
import Vegas.Runtime.DeviationAdequacy

/-!
# Kuhn correspondence for Vegas games

The GameTheory protocol layer proves unilateral, opponent-preserving Kuhn
laws directly on `InformationModel`.  This module packages those laws as exact
deviation-adequacy certificates between a Vegas game's behavioral form and the
mixed extension of its pure-policy form.

The generic certificates take perfect recall explicitly. The compiled
event-graph information model discharges it, and finite checked programs derive
a counterfactual finite-site cover for the unilateral certificates.
-/

noncomputable section

namespace Vegas.BoundedGame

open GameTheory
open GameTheory.Protocol

universe uPlayer uGame

variable {Player : Type uPlayer} [Fintype Player] [DecidableEq Player]
variable (G : BoundedGame.{uPlayer, uGame} Player)

/-- Compile behavioral policies to independently predrawn pure policies.
Under perfect recall, every unilateral mixed deviation is realized by its
behavioral reading while all opponents remain fixed. -/
def behavioralToMixedPureAdequacy
    [∀ who, Fintype (G.information.InfoState who)]
    [∀ who, DecidableEq (G.information.InfoState who)]
    (recall : G.information.PerfectRecall) :
    Runtime.DeviationAdequacy G.behavioral G.mixedPure where
  compileStrategy := fun _who strategy => strategy.toMixed
  backtranslateStrategy := fun _who strategy =>
    InformationModel.MixedPolicy.toBehavioral
      (M := G.information) strategy
  decodeOutcome := fun history : G.execution.History => history
  utility_eq := rfl
  honest_law := by
    intro profile
    change
      GameTheory.Math.Probability.FinDist.map
          (id : G.execution.History → G.execution.History)
          (G.information.runMixed
            (fun who => (profile who).toMixed) G.horizon) =
        G.information.runBehavioral profile G.horizon
    rw [GameTheory.Math.Probability.FinDist.map_id]
    exact
      G.information.runMixed_toMixed
        (G.information.actsOnceWhereItMatters_of_perfectRecall recall)
        profile G.horizon
  compiled_considered := fun _ _ => trivial
  deviation_law := by
    intro profile who replacement _
    change
      GameTheory.Math.Probability.FinDist.map
          (id : G.execution.History → G.execution.History)
          (G.information.runMixed
            (Profile.update (fun player => (profile player).toMixed)
              who replacement) G.horizon) =
        G.information.runBehavioral
          (Profile.update profile who
            (InformationModel.MixedPolicy.toBehavioral
              (M := G.information) replacement)) G.horizon
    rw [GameTheory.Math.Probability.FinDist.map_id]
    exact
      G.information.kuhn_behavioral_update_toMixed
        recall profile who replacement G.horizon

/-- Read a mixed pure-policy profile behaviorally. Under perfect recall, every
unilateral behavioral deviation is realized by predrawing that deviator's
local policy while all opponents remain fixed. -/
def mixedPureToBehavioralAdequacy
    [∀ who, Fintype (G.information.InfoState who)]
    [∀ who, DecidableEq (G.information.InfoState who)]
    (recall : G.information.PerfectRecall) :
    Runtime.DeviationAdequacy G.mixedPure G.behavioral where
  compileStrategy := fun _who strategy =>
    InformationModel.MixedPolicy.toBehavioral
      (M := G.information) strategy
  backtranslateStrategy := fun _who strategy => strategy.toMixed
  decodeOutcome := fun history : G.execution.History => history
  utility_eq := rfl
  honest_law := by
    intro profile
    change
      GameTheory.Math.Probability.FinDist.map
          (id : G.execution.History → G.execution.History)
          (G.information.runBehavioral
            (fun who => InformationModel.MixedPolicy.toBehavioral
              (M := G.information) (profile who)) G.horizon) =
        G.information.runMixed profile G.horizon
    rw [GameTheory.Math.Probability.FinDist.map_id]
    exact
      (G.information.runMixed_toBehavioral
        (InformationModel.constrainsAlike_of_perfectRecall recall)
        G.horizon profile).symm
  compiled_considered := fun _ _ => trivial
  deviation_law := by
    intro profile who replacement _
    change
      GameTheory.Math.Probability.FinDist.map
          (id : G.execution.History → G.execution.History)
          (G.information.runBehavioral
            (Profile.update
              (fun player => InformationModel.MixedPolicy.toBehavioral
                (M := G.information) (profile player))
              who replacement) G.horizon) =
        G.information.runMixed
          (Profile.update profile who replacement.toMixed) G.horizon
    rw [GameTheory.Math.Probability.FinDist.map_id]
    exact
      G.information.kuhn_mixed_update_toBehavioral
        recall profile who replacement G.horizon

/-- Finite counterfactual information-site coverage replaces ambient
information-state finiteness in behavioral-to-mixed deviation adequacy. -/
def behavioralToMixedPureWithinAdequacy
    (sites : (who : Player) →
      Finset (G.information.InfoState who))
    (fallback : Profile G.pure.form.sig)
    (cover : G.information.CoversInformationSites sites G.horizon)
    (recall : G.information.PerfectRecall) :
    Runtime.DeviationAdequacy G.behavioral G.mixedPure := by
  classical
  exact
    { compileStrategy := fun who strategy =>
        strategy.toMixedWithin (sites who) (fallback who)
      backtranslateStrategy := fun _who strategy =>
        InformationModel.MixedPolicy.toBehavioral
          (M := G.information) strategy
      decodeOutcome := fun history : G.execution.History => history
      utility_eq := rfl
      honest_law := by
        intro profile
        change
          GameTheory.Math.Probability.FinDist.map
              (id : G.execution.History → G.execution.History)
              (G.information.runMixed
                (fun who => (profile who).toMixedWithin
                  (sites who) (fallback who)) G.horizon) =
            G.information.runBehavioral profile G.horizon
        rw [GameTheory.Math.Probability.FinDist.map_id]
        exact
          G.information.runMixed_toMixedWithin
            (G.information.actsOnceWhereItMatters_of_perfectRecall recall)
            sites profile fallback G.horizon cover
      compiled_considered := fun _ _ => trivial
      deviation_law := by
        intro profile who replacement _
        change
          GameTheory.Math.Probability.FinDist.map
              (id : G.execution.History → G.execution.History)
              (G.information.runMixed
                (Profile.update
                  (fun player => (profile player).toMixedWithin
                    (sites player) (fallback player))
                  who replacement) G.horizon) =
            G.information.runBehavioral
              (Profile.update profile who
                (InformationModel.MixedPolicy.toBehavioral
                  (M := G.information) replacement)) G.horizon
        rw [GameTheory.Math.Probability.FinDist.map_id]
        exact
          G.information.kuhn_behavioral_update_toMixedWithin
            recall sites G.horizon cover profile fallback who replacement }

/-- Finite counterfactual site coverage also supplies the reverse
mixed-to-behavioral deviation certificate. -/
def mixedPureToBehavioralWithinAdequacy
    (sites : (who : Player) →
      Finset (G.information.InfoState who))
    (fallback : Profile G.pure.form.sig)
    (cover : G.information.CoversInformationSites sites G.horizon)
    (recall : G.information.PerfectRecall) :
    Runtime.DeviationAdequacy G.mixedPure G.behavioral := by
  classical
  exact
    { compileStrategy := fun _who strategy =>
        InformationModel.MixedPolicy.toBehavioral
          (M := G.information) strategy
      backtranslateStrategy := fun who strategy =>
        strategy.toMixedWithin (sites who) (fallback who)
      decodeOutcome := fun history : G.execution.History => history
      utility_eq := rfl
      honest_law := by
        intro profile
        change
          GameTheory.Math.Probability.FinDist.map
              (id : G.execution.History → G.execution.History)
              (G.information.runBehavioral
                (fun who => InformationModel.MixedPolicy.toBehavioral
                  (M := G.information) (profile who)) G.horizon) =
            G.information.runMixed profile G.horizon
        rw [GameTheory.Math.Probability.FinDist.map_id]
        exact
          (G.information.runMixed_toBehavioral
            (InformationModel.constrainsAlike_of_perfectRecall recall)
            G.horizon profile).symm
      compiled_considered := fun _ _ => trivial
      deviation_law := by
        intro profile who replacement _
        change
          GameTheory.Math.Probability.FinDist.map
              (id : G.execution.History → G.execution.History)
              (G.information.runBehavioral
                (Profile.update
                  (fun player => InformationModel.MixedPolicy.toBehavioral
                    (M := G.information) (profile player))
                  who replacement) G.horizon) =
            G.information.runMixed
              (Profile.update profile who
                (replacement.toMixedWithin
                  (sites who) (fallback who))) G.horizon
        rw [GameTheory.Math.Probability.FinDist.map_id]
        exact
          G.information.kuhn_mixed_update_toBehavioralWithin
            recall sites G.horizon cover profile who replacement
              (fallback who) }

end Vegas.BoundedGame

namespace Vegas.Machine.Program

open GameTheory
open GameTheory.Protocol

variable {Player : Type} [Fintype Player] [DecidableEq Player]
variable {L : IExpr}

/-- Every compiled behavioral profile has a mixed pure-policy realization with
the same complete history law. -/
theorem exists_mixedPure_play_eq_behavioral
    (program : Machine.Program Player L)
    (behavioral : Profile program.boundedGame.behavioral.form.sig) :
    ∃ mixed : Profile program.boundedGame.mixedPure.form.sig,
      program.boundedGame.mixedPure.form.play mixed =
        program.boundedGame.behavioral.form.play behavioral := by
  exact program.information.exists_mixed_runMixed_eq_runBehavioral
    (program.information.actsOnceWhereItMatters_of_perfectRecall program.perfectRecall)
    behavioral program.boundedGame.horizon

/-- Every compiled mixed pure-policy profile has a behavioral realization with
the same complete history law. -/
theorem exists_behavioral_play_eq_mixedPure
    (program : Machine.Program Player L)
    (mixed : Profile program.boundedGame.mixedPure.form.sig) :
    ∃ behavioral : Profile program.boundedGame.behavioral.form.sig,
      program.boundedGame.behavioral.form.play behavioral =
        program.boundedGame.mixedPure.form.play mixed := by
  let behavioral := fun who => InformationModel.MixedPolicy.toBehavioral
    (M := program.information) (mixed who)
  refine ⟨behavioral, ?_⟩
  change
    program.information.runBehavioral behavioral program.boundedGame.horizon =
      program.information.runMixed mixed program.boundedGame.horizon
  exact (program.information.runMixed_toBehavioral
    (InformationModel.constrainsAlike_of_perfectRecall program.perfectRecall)
    program.boundedGame.horizon mixed).symm

end Vegas.Machine.Program

namespace Vegas.WFProgram

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Protocol

variable {Player : Type} [Fintype Player] [DecidableEq Player]
variable {L : IExpr}

/-- Finite source domains make every local menu choice finite even though the
carrier of accumulated information histories is not globally finite. -/
@[reducible]
noncomputable def choiceFintype
    (program : WFProgram Player L) [FiniteDomains program]
    (who : Player) (info : program.boundedGame.information.InfoState who) :
    Fintype (program.boundedGame.information.Choice who info) := by
  classical
  letI : Fintype (program.boundedGame.execution.Action who) :=
    program.actionFintype who
  exact Fintype.ofFinite _

/-- Every compiled local menu is inhabited, including unreachable information
values that use the idle fallback. -/
theorem choice_nonempty
    (program : WFProgram Player L) (who : Player)
    (info : program.boundedGame.information.InfoState who) :
    Nonempty (program.boundedGame.information.Choice who info) := by
  exact EventGraph.choice_nonempty
    (Machine.compile program).graph
    (Machine.compile program).graphWF
    (Machine.compile program).guardLive who info

/-- A locally full-support behavioral profile used only to enumerate every
counterfactual information site through the compiled horizon. -/
noncomputable def fullSupportBehavioral
    (program : WFProgram Player L) [FiniteDomains program] :
    Profile program.boundedGame.behavioral.form.sig := by
  intro who info
  letI : Fintype (program.boundedGame.information.Choice who info) :=
    program.choiceFintype who info
  letI : Nonempty (program.boundedGame.information.Choice who info) :=
    program.choice_nonempty who info
  exact FinDist.uniformOfFintype

theorem mem_support_fullSupportBehavioral
    (program : WFProgram Player L) [FiniteDomains program]
    (who : Player) (info : program.boundedGame.information.InfoState who)
    (choice : program.boundedGame.information.Choice who info) :
    choice ∈ (program.fullSupportBehavioral who info).support := by
  let : Fintype (program.boundedGame.information.Choice who info) :=
    program.choiceFintype who info
  let : Nonempty (program.boundedGame.information.Choice who info) :=
    program.choice_nonempty who info
  exact FinDist.mem_support_uniformOfFintype choice

/-- The finite information sites reached by the locally full-support profile
through the semantic horizon. -/
noncomputable def kuhnSites
    (program : WFProgram Player L) [FiniteDomains program]
    (who : Player) : Finset (program.boundedGame.information.InfoState who) :=
  program.boundedGame.information.behavioralSupportSitesFrom
    program.fullSupportBehavioral program.boundedGame.horizon
    program.boundedGame.execution.initHistory who

/-- Full support makes the enumerated sites cover every legal counterfactual
history, not merely histories reached by one intended strategy. -/
theorem kuhnSites_cover
    (program : WFProgram Player L) [FiniteDomains program] :
    program.boundedGame.information.CoversInformationSites
      program.kuhnSites program.boundedGame.horizon := by
  exact
    program.boundedGame.information
      |>.behavioralSupportSitesFrom_covers_of_fullSupport
        program.fullSupportBehavioral program.boundedGame.horizon
        program.boundedGame.execution.initHistory
        (program.mem_support_fullSupportBehavioral)

/-- Finite checked programs have an exact behavioral-to-mixed deviation
certificate and therefore preserve and reflect Nash at the compiled profile. -/
noncomputable def behavioralToMixedPureAdequacy
    (program : WFProgram Player L) [FiniteDomains program] :
    Runtime.DeviationAdequacy program.boundedGame.behavioral
      program.boundedGame.mixedPure :=
  program.boundedGame.behavioralToMixedPureWithinAdequacy
    program.kuhnSites (Machine.compile program).defaultPureProfile
    program.kuhnSites_cover (Machine.compile program).perfectRecall

/-- The reverse mixed-to-behavioral deviation certificate for finite checked
programs. -/
noncomputable def mixedPureToBehavioralAdequacy
    (program : WFProgram Player L) [FiniteDomains program] :
    Runtime.DeviationAdequacy program.boundedGame.mixedPure
      program.boundedGame.behavioral :=
  program.boundedGame.mixedPureToBehavioralWithinAdequacy
    program.kuhnSites (Machine.compile program).defaultPureProfile
    program.kuhnSites_cover (Machine.compile program).perfectRecall

end Vegas.WFProgram
