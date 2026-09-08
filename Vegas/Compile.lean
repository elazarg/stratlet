/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Compiler
import Vegas.Compile.DecisionSite
import Vegas.Compile.FieldMap
import Vegas.Compile.SourceAdequacy
import Vegas.Compile.SourceOrder
import Vegas.Compile.SourceLaw
import Vegas.Compile.Machine

/-!
# Compilation: checked Vegas programs to event graphs

`Compiler` lowers a `GraphProgram` / `WFProgram` into a canonical
`EventGraph.Graph` with typed fields, causal dependencies, guarded commit
nodes, exact finite laws, and terminal payoff projections.
-/
