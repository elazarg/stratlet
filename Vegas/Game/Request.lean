/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Game.Kuhn
import Vegas.Runtime.RequestCompiler

/-! # Behavioral request compilation for finite-menu games

Finite menus and a bounded horizon suffice; neither a globally finite history
carrier nor a Vegas source-language admission certificate is needed.
-/

noncomputable section

namespace Vegas.BoundedGame

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Vegas.Runtime

variable {Player : Type} [Fintype Player] [DecidableEq Player]

/-- Behavioral-to-request deviation adequacy for any bounded perfect-recall
game with finite local menus. Full support enumerates every counterfactual
information site, including those reached only under deviations. -/
def requestAdequacy (game : BoundedGame Player)
    (choices : ∀ who info, Fintype (game.information.Choice who info))
    (recall : game.information.PerfectRecall)
    {Request : Player → Type}
    (interface : RequestCompiler.Interface game.information Request) :
    DeviationAdequacy game.behavioral
      (RequestCompiler.targetGame game.information interface
        game.horizon game.utility).mixed := by
  let full : ∀ who, game.information.BehavioralPolicy who := fun who info => by
    letI := choices who info
    letI : Nonempty (game.information.Choice who info) :=
      ⟨(interface.gate who).timeoutAction info⟩
    exact FinDist.uniformOfFintype
  have hfull : ∀ who info (choice : game.information.Choice who info),
      choice ∈ (full who info).support := by
    intro who info choice
    let := choices who info
    let : Nonempty (game.information.Choice who info) :=
      ⟨(interface.gate who).timeoutAction info⟩
    exact FinDist.mem_support_uniformOfFintype choice
  let sites := game.information.behavioralSupportSitesFrom full game.horizon
    game.execution.initHistory
  have cover : game.information.CoversInformationSites sites game.horizon :=
    game.information.behavioralSupportSitesFrom_covers_of_fullSupport
      full game.horizon game.execution.initHistory hfull
  exact (game.behavioralToMixedPureWithinAdequacy sites
    (fun who => (interface.gate who).timeoutAction) cover recall).trans
      (RequestCompiler.mixedAdequacy _ interface recall _ _)

end Vegas.BoundedGame
