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
import Vegas.Compile.SourceInformation
import Vegas.Compile.PolicyInformation
import Vegas.Compile.SourceLaw
import Vegas.Compile.SourceExecution
import Vegas.Compile.SourceExecutionGraph
import Vegas.Compile.SourceExecutionLaw
import Vegas.Compile.SourceExecutionOutcome
import Vegas.Compile.SourceExecutionLaw
import Vegas.Compile.SourceOutcome
import Vegas.Compile.SourceObservation
import Vegas.Compile.SourcePolicy
import Vegas.Compile.SourceBacktranslation
import Vegas.Compile.SourceStrategy
import Vegas.Compile.Machine

/-!
# Compilation: checked Vegas programs to event graphs

`Compiler` lowers a `GraphProgram` / `WFProgram` into a canonical
`EventGraph.Graph` with typed fields, causal dependencies, guarded commit
nodes, exact finite laws, and terminal payoff projections.
-/
