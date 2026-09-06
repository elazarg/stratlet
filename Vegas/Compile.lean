/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Compiler
import Vegas.Compile.SourceAdequacy
import Vegas.Compile.Classical
import Vegas.Compile.ClassicalEVM
import Vegas.Compile.BooleanEVM
import Vegas.Compile.EVMRefinement
import Vegas.Compile.Request

/-!
# Compilation: checked Vegas programs to event graphs

`Compiler` lowers a `GraphProgram` / `WFProgram` into a canonical
`EventGraph.Graph` with typed fields, causal dependencies, guarded commit
nodes, exact finite laws, and terminal payoff projections.
-/
