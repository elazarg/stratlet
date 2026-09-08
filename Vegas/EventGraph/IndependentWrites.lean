/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Execution

/-! # Fixed-law independent graph writes -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Execute a requested node list using fixed, mutually independent typed-value
laws.  Unlike `policyNodeStep`, the laws do not inspect the evolving graph
configuration. -/
def runIndependentWrites {G : Graph Player L}
    (laws : Fin G.nodeCount → FinDist (TypedValue L)) :
    Config G → List (Fin G.nodeCount) → FinDist (Config G)
  | cfg, [] => FinDist.pure cfg
  | cfg, node :: rest =>
      (laws node).bind fun written =>
        runIndependentWrites laws (cfg.completeNode node written) rest

@[simp] theorem runIndependentWrites_nil {G : Graph Player L}
    (laws : Fin G.nodeCount → FinDist (TypedValue L)) (cfg : Config G) :
    runIndependentWrites laws cfg [] = FinDist.pure cfg := rfl

@[simp] theorem runIndependentWrites_cons {G : Graph Player L}
    (laws : Fin G.nodeCount → FinDist (TypedValue L)) (cfg : Config G)
    (node : Fin G.nodeCount) (rest : List (Fin G.nodeCount)) :
    runIndependentWrites laws cfg (node :: rest) =
      (laws node).bind fun written =>
        runIndependentWrites laws (cfg.completeNode node written) rest := rfl

end Vegas.EventGraph
