/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Game.SourceCorrespondence
import Vegas.Game.SourceRequest
import Vegas.Runtime.OutcomeSimulationComposition

/-! # Independent source outcomes through the request compiler -/

noncomputable section

namespace Vegas.WFProgram

open GameTheory Vegas.Runtime

variable {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}

/-- Every request-controller mixture has a uniform source-policy translation;
the decoder retains exactly the independent source terminal environment. -/
def sourceRequestOutcomeSimulation (source : WFProgram Player L) [FiniteDomains source]
    {Request : Player → Type}
    (interface : RequestCompiler.Interface source.boundedGame.information Request) :
    OutcomeSimulationOn (sourceGameForm source.core.prog source.core.env)
      (source.requestGame interface).form (fun _ _ => True) :=
  source.sourceOutcomeSimulation.trans
    (source.behavioralRequestAdequacy interface).toOutcomeSimulationOn
    (fun _ _ _ => trivial)

end Vegas.WFProgram
