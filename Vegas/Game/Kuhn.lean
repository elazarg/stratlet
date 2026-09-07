/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Languages.FOSG.Kuhn
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

namespace Vegas.Game

open GameTheory
open GameTheory.Protocol

universe uPlayer uGame

variable {Player : Type uPlayer} [Fintype Player] [DecidableEq Player]
variable (G : Game.{uPlayer, uGame} Player)

/-- Compile behavioral policies to independently predrawn pure policies.
Under perfect recall, every unilateral mixed deviation is realized by its
behavioral reading while all opponents remain fixed. -/
def behavioralToMixedPureAdequacy
    [∀ who, Fintype (G.arena.information.InfoState who)]
    [∀ who, DecidableEq (G.arena.information.InfoState who)]
    (recall : G.arena.information.PerfectRecall) :
    Runtime.DeviationAdequacy G.behavioral G.mixedPure where
  compileStrategy := fun _who strategy => strategy.toMixed
  backtranslateStrategy := fun _who strategy =>
    InformationModel.MixedPolicy.toBehavioral
      (M := G.arena.information) strategy
  decodeOutcome := fun history : G.arena.History => history
  utility_eq := rfl
  honest_law := by
    intro profile
    change
      GameTheory.Math.Probability.FinDist.map
          (id : G.arena.History → G.arena.History)
          (G.arena.information.runMixed
            (fun who => (profile who).toMixed) G.horizon) =
        G.arena.information.runBehavioral profile G.horizon
    rw [GameTheory.Math.Probability.FinDist.map_id]
    exact
      G.arena.information.runMixed_toMixed
        (G.arena.information.actsOnceWhereItMatters_of_perfectRecall recall)
        profile G.horizon
  compiled_considered := fun _ _ => trivial
  deviation_law := by
    intro profile who replacement _
    change
      GameTheory.Math.Probability.FinDist.map
          (id : G.arena.History → G.arena.History)
          (G.arena.information.runMixed
            (Profile.update (fun player => (profile player).toMixed)
              who replacement) G.horizon) =
        G.arena.information.runBehavioral
          (Profile.update profile who
            (InformationModel.MixedPolicy.toBehavioral
              (M := G.arena.information) replacement)) G.horizon
    rw [GameTheory.Math.Probability.FinDist.map_id]
    exact
      G.arena.information.kuhn_behavioral_update_toMixed
        recall profile who replacement G.horizon

/-- Read a mixed pure-policy profile behaviorally. Under perfect recall, every
unilateral behavioral deviation is realized by predrawing that deviator's
local policy while all opponents remain fixed. -/
def mixedPureToBehavioralAdequacy
    [∀ who, Fintype (G.arena.information.InfoState who)]
    [∀ who, DecidableEq (G.arena.information.InfoState who)]
    (recall : G.arena.information.PerfectRecall) :
    Runtime.DeviationAdequacy G.mixedPure G.behavioral where
  compileStrategy := fun _who strategy =>
    InformationModel.MixedPolicy.toBehavioral
      (M := G.arena.information) strategy
  backtranslateStrategy := fun _who strategy => strategy.toMixed
  decodeOutcome := fun history : G.arena.History => history
  utility_eq := rfl
  honest_law := by
    intro profile
    change
      GameTheory.Math.Probability.FinDist.map
          (id : G.arena.History → G.arena.History)
          (G.arena.information.runBehavioral
            (fun who => InformationModel.MixedPolicy.toBehavioral
              (M := G.arena.information) (profile who)) G.horizon) =
        G.arena.information.runMixed profile G.horizon
    rw [GameTheory.Math.Probability.FinDist.map_id]
    exact
      (G.arena.information.runMixed_toBehavioral
        (InformationModel.constrainsAlike_of_perfectRecall recall)
        G.horizon profile).symm
  compiled_considered := fun _ _ => trivial
  deviation_law := by
    intro profile who replacement _
    change
      GameTheory.Math.Probability.FinDist.map
          (id : G.arena.History → G.arena.History)
          (G.arena.information.runBehavioral
            (Profile.update
              (fun player => InformationModel.MixedPolicy.toBehavioral
                (M := G.arena.information) (profile player))
              who replacement) G.horizon) =
        G.arena.information.runMixed
          (Profile.update profile who replacement.toMixed) G.horizon
    rw [GameTheory.Math.Probability.FinDist.map_id]
    exact
      G.arena.information.kuhn_mixed_update_toBehavioral
        recall profile who replacement G.horizon

/-- Finite counterfactual information-site coverage replaces ambient
information-state finiteness in behavioral-to-mixed deviation adequacy. -/
def behavioralToMixedPureWithinAdequacy
    (sites : (who : Player) →
      Finset (G.arena.information.InfoState who))
    (fallback : Profile G.pure.form.sig)
    (cover : G.arena.information.CoversInformationSites sites G.horizon)
    (recall : G.arena.information.PerfectRecall) :
    Runtime.DeviationAdequacy G.behavioral G.mixedPure := by
  classical
  exact
    { compileStrategy := fun who strategy =>
        strategy.toMixedWithin (sites who) (fallback who)
      backtranslateStrategy := fun _who strategy =>
        InformationModel.MixedPolicy.toBehavioral
          (M := G.arena.information) strategy
      decodeOutcome := fun history : G.arena.History => history
      utility_eq := rfl
      honest_law := by
        intro profile
        change
          GameTheory.Math.Probability.FinDist.map
              (id : G.arena.History → G.arena.History)
              (G.arena.information.runMixed
                (fun who => (profile who).toMixedWithin
                  (sites who) (fallback who)) G.horizon) =
            G.arena.information.runBehavioral profile G.horizon
        rw [GameTheory.Math.Probability.FinDist.map_id]
        exact
          G.arena.information.runMixed_toMixedWithin
            (G.arena.information.actsOnceWhereItMatters_of_perfectRecall recall)
            sites profile fallback G.horizon cover
      compiled_considered := fun _ _ => trivial
      deviation_law := by
        intro profile who replacement _
        change
          GameTheory.Math.Probability.FinDist.map
              (id : G.arena.History → G.arena.History)
              (G.arena.information.runMixed
                (Profile.update
                  (fun player => (profile player).toMixedWithin
                    (sites player) (fallback player))
                  who replacement) G.horizon) =
            G.arena.information.runBehavioral
              (Profile.update profile who
                (InformationModel.MixedPolicy.toBehavioral
                  (M := G.arena.information) replacement)) G.horizon
        rw [GameTheory.Math.Probability.FinDist.map_id]
        exact
          G.arena.information.kuhn_behavioral_update_toMixedWithin
            recall sites G.horizon cover profile fallback who replacement }

/-- Finite counterfactual site coverage also supplies the reverse
mixed-to-behavioral deviation certificate. -/
def mixedPureToBehavioralWithinAdequacy
    (sites : (who : Player) →
      Finset (G.arena.information.InfoState who))
    (fallback : Profile G.pure.form.sig)
    (cover : G.arena.information.CoversInformationSites sites G.horizon)
    (recall : G.arena.information.PerfectRecall) :
    Runtime.DeviationAdequacy G.mixedPure G.behavioral := by
  classical
  exact
    { compileStrategy := fun _who strategy =>
        InformationModel.MixedPolicy.toBehavioral
          (M := G.arena.information) strategy
      backtranslateStrategy := fun who strategy =>
        strategy.toMixedWithin (sites who) (fallback who)
      decodeOutcome := fun history : G.arena.History => history
      utility_eq := rfl
      honest_law := by
        intro profile
        change
          GameTheory.Math.Probability.FinDist.map
              (id : G.arena.History → G.arena.History)
              (G.arena.information.runBehavioral
                (fun who => InformationModel.MixedPolicy.toBehavioral
                  (M := G.arena.information) (profile who)) G.horizon) =
            G.arena.information.runMixed profile G.horizon
        rw [GameTheory.Math.Probability.FinDist.map_id]
        exact
          (G.arena.information.runMixed_toBehavioral
            (InformationModel.constrainsAlike_of_perfectRecall recall)
            G.horizon profile).symm
      compiled_considered := fun _ _ => trivial
      deviation_law := by
        intro profile who replacement _
        change
          GameTheory.Math.Probability.FinDist.map
              (id : G.arena.History → G.arena.History)
              (G.arena.information.runBehavioral
                (Profile.update
                  (fun player => InformationModel.MixedPolicy.toBehavioral
                    (M := G.arena.information) (profile player))
                  who replacement) G.horizon) =
            G.arena.information.runMixed
              (Profile.update profile who
                (replacement.toMixedWithin
                  (sites who) (fallback who))) G.horizon
        rw [GameTheory.Math.Probability.FinDist.map_id]
        exact
          G.arena.information.kuhn_mixed_update_toBehavioralWithin
            recall sites G.horizon cover profile who replacement
              (fallback who) }

end Vegas.Game

namespace Vegas.Machine.Program

open GameTheory
open GameTheory.Protocol

variable {Player : Type} [Fintype Player] [DecidableEq Player]
variable {L : IExpr}

/-- Every compiled behavioral profile has a mixed pure-policy realization with
the same complete history law. -/
theorem exists_mixedPure_play_eq_behavioral
    (program : Machine.Program Player L)
    (behavioral : Profile program.game.behavioral.form.sig) :
    ∃ mixed : Profile program.game.mixedPure.form.sig,
      program.game.mixedPure.form.play mixed =
        program.game.behavioral.form.play behavioral := by
  rcases program.game.arena.kuhn_behavioral_to_mixed
      (program.perfectRecall.actsOnceAtEachInfoState
        |> program.information.actsOnceWhereItMatters_of_actsOnce)
      behavioral program.game.horizon with ⟨mixed, hmixed⟩
  refine ⟨mixed, ?_⟩
  change
    program.information.runMixed mixed program.game.horizon =
      program.information.runBehavioral behavioral program.game.horizon
  exact hmixed

/-- Every compiled mixed pure-policy profile has a behavioral realization with
the same complete history law. -/
theorem exists_behavioral_play_eq_mixedPure
    (program : Machine.Program Player L)
    (mixed : Profile program.game.mixedPure.form.sig) :
    ∃ behavioral : Profile program.game.behavioral.form.sig,
      program.game.behavioral.form.play behavioral =
        program.game.mixedPure.form.play mixed := by
  rcases program.game.arena.kuhn_mixed_to_behavioral
      program.perfectRecall mixed program.game.horizon with
    ⟨behavioral, hbehavioral⟩
  refine ⟨behavioral, ?_⟩
  change
    program.information.runBehavioral behavioral program.game.horizon =
      program.information.runMixed mixed program.game.horizon
  exact hbehavioral

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
    (who : Player) (info : program.game.arena.information.InfoState who) :
    Fintype (program.game.arena.information.Choice who info) := by
  classical
  letI : Fintype (program.game.arena.execution.Action who) :=
    program.actionFintype who
  exact Fintype.ofFinite _

/-- Every compiled local menu is inhabited, including unreachable information
values that use the idle fallback. -/
theorem choice_nonempty
    (program : WFProgram Player L) (who : Player)
    (info : program.game.arena.information.InfoState who) :
    Nonempty (program.game.arena.information.Choice who info) := by
  exact EventGraph.choice_nonempty
    (Machine.compile program).graph
    (Machine.compile program).graphWF
    (Machine.compile program).guardLive who info

/-- A locally full-support behavioral profile used only to enumerate every
counterfactual information site through the compiled horizon. -/
noncomputable def fullSupportBehavioral
    (program : WFProgram Player L) [FiniteDomains program] :
    Profile program.game.behavioral.form.sig := by
  intro who info
  letI : Fintype (program.game.arena.information.Choice who info) :=
    program.choiceFintype who info
  letI : Nonempty (program.game.arena.information.Choice who info) :=
    program.choice_nonempty who info
  exact FinDist.uniformOfFintype

theorem mem_support_fullSupportBehavioral
    (program : WFProgram Player L) [FiniteDomains program]
    (who : Player) (info : program.game.arena.information.InfoState who)
    (choice : program.game.arena.information.Choice who info) :
    choice ∈ (program.fullSupportBehavioral who info).support := by
  let : Fintype (program.game.arena.information.Choice who info) :=
    program.choiceFintype who info
  let : Nonempty (program.game.arena.information.Choice who info) :=
    program.choice_nonempty who info
  exact FinDist.mem_support_uniformOfFintype choice

/-- The finite information sites reached by the locally full-support profile
through the semantic horizon. -/
noncomputable def kuhnSites
    (program : WFProgram Player L) [FiniteDomains program]
    (who : Player) : Finset (program.game.arena.information.InfoState who) :=
  program.game.arena.information.behavioralSupportSitesFrom
    program.fullSupportBehavioral program.game.horizon
    program.game.arena.execution.initHistory who

/-- Full support makes the enumerated sites cover every legal counterfactual
history, not merely histories reached by one intended strategy. -/
theorem kuhnSites_cover
    (program : WFProgram Player L) [FiniteDomains program] :
    program.game.arena.information.CoversInformationSites
      program.kuhnSites program.game.horizon := by
  exact
    program.game.arena.information
      |>.behavioralSupportSitesFrom_covers_of_fullSupport
        program.fullSupportBehavioral program.game.horizon
        program.game.arena.execution.initHistory
        (program.mem_support_fullSupportBehavioral)

/-- Finite checked programs have an exact behavioral-to-mixed deviation
certificate and therefore preserve and reflect Nash at the compiled profile. -/
noncomputable def behavioralToMixedPureAdequacy
    (program : WFProgram Player L) [FiniteDomains program] :
    Runtime.DeviationAdequacy program.game.behavioral
      program.game.mixedPure :=
  program.game.behavioralToMixedPureWithinAdequacy
    program.kuhnSites (Machine.compile program).defaultPureProfile
    program.kuhnSites_cover (Machine.compile program).perfectRecall

/-- The reverse mixed-to-behavioral deviation certificate for finite checked
programs. -/
noncomputable def mixedPureToBehavioralAdequacy
    (program : WFProgram Player L) [FiniteDomains program] :
    Runtime.DeviationAdequacy program.game.mixedPure
      program.game.behavioral :=
  program.game.mixedPureToBehavioralWithinAdequacy
    program.kuhnSites (Machine.compile program).defaultPureProfile
    program.kuhnSites_cover (Machine.compile program).perfectRecall

end Vegas.WFProgram
