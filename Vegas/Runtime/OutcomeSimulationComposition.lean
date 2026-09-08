/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.OutcomeSimulation

/-! # Composition of utility-independent outcome simulations -/

noncomputable section

namespace Vegas.Runtime.OutcomeSimulationOn

open GameTheory
open GameTheory.Math.Probability

/-- Utility-independent outcome simulations compose when every target
deviation translated by the second pass is admitted by the first pass. -/
def trans {Player : Type*} [DecidableEq Player]
    {source middle target : GameForm Player}
    {MiddleConsidered : (who : Player) → middle.sig.Strategy who → Prop}
    {TargetConsidered : (who : Player) → target.sig.Strategy who → Prop}
    (left : OutcomeSimulationOn source middle MiddleConsidered)
    (right : OutcomeSimulationOn middle target TargetConsidered)
    (backtranslated_considered : ∀ who replacement,
      TargetConsidered who replacement →
        MiddleConsidered who (right.backtranslateStrategy who replacement)) :
    OutcomeSimulationOn source target TargetConsidered where
  compileStrategy who strategy :=
    right.compileStrategy who (left.compileStrategy who strategy)
  backtranslateStrategy who strategy :=
    left.backtranslateStrategy who (right.backtranslateStrategy who strategy)
  decodeOutcome := left.decodeOutcome ∘ right.decodeOutcome
  honest_law profile := by
    rw [← FinDist.map_comp, right.honest_law, left.honest_law]
  compiled_considered who strategy :=
    right.compiled_considered who (left.compileStrategy who strategy)
  deviation_law profile who replacement hconsidered := by
    rw [← FinDist.map_comp, right.deviation_law _ _ _ hconsidered,
      left.deviation_law _ _ _
        (backtranslated_considered who replacement hconsidered)]

end Vegas.Runtime.OutcomeSimulationOn
