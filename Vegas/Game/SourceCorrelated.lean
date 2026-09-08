/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Game.SourceCorrespondence
import Vegas.Runtime.Correlated

/-! # Correlated recommendations for independent source policies -/

noncomputable section

namespace Vegas.WFProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

/-- Correlated source recommendations remain correlated equilibrium after
native compilation, against every response to the compiled own recommendation. -/
theorem source_native_correlatedEq_of (source : WFProgram Player L)
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (law : FinDist (SourceBehavioralProfile source.core.prog))
    (hsource : IsCorrelatedEq (sourceGameForm source.core.prog source.core.env)
      (euPreference valuation) law) :
    IsCorrelatedEq source.game.behavioralForm
      (euPreference fun history player => valuation
        (ToEventGraph.observeSourceOutcome source.core source.legal history.state) player)
      (source.sourceOutcomeSimulation.compileLaw law) :=
  source.sourceOutcomeSimulation.isCorrelatedEq_compileLaw_of valuation law hsource

/-- Coarse correlated equilibrium is preserved and reflected by native
compilation for every independent source recommendation law and valuation. -/
theorem source_native_coarseCorrelatedEq_iff (source : WFProgram Player L)
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (law : FinDist (SourceBehavioralProfile source.core.prog)) :
    IsCoarseCorrelatedEq source.game.behavioralForm
      (euPreference fun history player => valuation
        (ToEventGraph.observeSourceOutcome source.core source.legal history.state) player)
      (source.sourceOutcomeSimulation.compileLaw law) ↔
      IsCoarseCorrelatedEq (sourceGameForm source.core.prog source.core.env)
        (euPreference valuation) law :=
  source.sourceOutcomeSimulation.isCoarseCorrelatedEq_compileLaw_iff valuation law

end Vegas.WFProgram
