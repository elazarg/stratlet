/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImage
import Vegas.Compile.SealedMessages

/-! # Generated public-chance instructions

A chance instruction is a direct graph projection: it retains the node's
public output field, public dependency list, and exact compiled distribution.
It adds no entropy source or scheduling policy beyond the application kernel.
-/

namespace Vegas.EventGraph.Graph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Canonical application code for one graph sample node.  The caller's source
origin certificate separately establishes that the selected row has exactly
this sample semantics. -/
def sampleCode (G : Graph P L) (node : Fin G.nodeCount)
    (dist : EventDist L) : SampleCode L where
  node := node.val
  outputField := G.nodeTarget node
  requires := G.messagePrerequisites node
  dist := dist

@[simp] theorem sampleCode_node (G : Graph P L) (node : Fin G.nodeCount)
    (dist : EventDist L) :
    (G.sampleCode node dist).node = node.val := rfl

@[simp] theorem sampleCode_outputField (G : Graph P L) (node : Fin G.nodeCount)
    (dist : EventDist L) :
    (G.sampleCode node dist).outputField = G.nodeTarget node := rfl

@[simp] theorem sampleCode_requires (G : Graph P L) (node : Fin G.nodeCount)
    (dist : EventDist L) :
    (G.sampleCode node dist).requires = G.messagePrerequisites node := rfl

@[simp] theorem sampleCode_dist (G : Graph P L) (node : Fin G.nodeCount)
    (dist : EventDist L) :
    (G.sampleCode node dist).dist = dist := rfl

end Vegas.EventGraph.Graph
