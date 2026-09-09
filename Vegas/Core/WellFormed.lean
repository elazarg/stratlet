/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Accounting
import Vegas.Core.Scope

/-!
# Checked Vegas programs

This file separates the obligations needed for event-graph compilation from
the stronger obligations expected at the checked-game boundary.

`GraphProgram` is the direct graph-construction input: context uniqueness and
fresh bindings. Distribution expressions already denote normalized `FinDist`
laws. `WFProgram` adds commitment accounting and guard legality. Guard legality
is used by checked game construction to derive graph guard liveness and
checkpoint progress. Accounting requires each sealed binding to have either a
literal reveal or a certified conditional publication in the source program.
The latter publishes an explicit decline or the original value. This resource
discipline does not erase retained knowledge or enforce role-wide quitting;
those properties concern the source continuations. Accounting is not needed
for graph progress, which concerns execution of the graph nodes that exist.

Low-level continuation evaluators can operate on raw suffix programs, where
constructing fresh bundles for each recursive subprogram would be painful and
irrelevant.

**Strategy-level guard admissibility.** The program-level `Legal`
predicate promises that every commit site admits some guard-satisfying action
in the source-visible context. Compilation turns this into graph-level
`GuardLive`, which is the nondeadlock fact used by checkpoint models and later
strategic presentations.
-/

namespace Vegas

/-- A Vegas program paired with exactly the static obligations needed to
compile it into an event graph.

* `wctx`       — the initial context has distinct variable names.
* `fresh`      — syntactic binders are SSA-fresh.
The compiler does not require commitment accounting or guard legality. -/
structure GraphProgram (P : Type) [DecidableEq P] (L : IExpr) where
  Γ : VCtx P L
  prog : VegasCore P L Γ
  env : VEnv L Γ
  wctx : WFCtx Γ
  fresh : FreshBindings prog

/-- A checked Vegas program at the game boundary.

`core` is the graph-compilable program. `legal` feeds the graph guard-liveness
and progress theorem layer. `accounted` is an inspectable plan naming the
literal or conditional publication of every initial and newly committed sealed
binding. Its semantic codecs and guards do not themselves provide a concrete
runtime validator, timeout mechanism, or frontend lowering certificate. -/
structure WFProgram (P : Type) [DecidableEq P] (L : IExpr) where
  core : GraphProgram P L
  accounted : CommitmentAccounting (SealedVars core.Γ).toFinset core.prog
  legal : Legal core.prog

namespace WFProgram

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every newly committed binding has a literal reveal or an explicitly
certified conditional-publication site. -/
theorem committed_source_resolved (program : WFProgram P L) :
    ∀ x, x ∈ CommittedVars program.core.prog →
      x ∈ RevealedSources program.core.prog ∨ x ∈ program.accounted.dispositions :=
  program.accounted.committed_resolved

/-- Sealed inputs satisfy the same explicit accounting discipline as newly
committed bindings. -/
theorem initial_sealed_source_resolved (program : WFProgram P L) :
    ∀ x, x ∈ SealedVars program.core.Γ →
      x ∈ RevealedSources program.core.prog ∨ x ∈ program.accounted.dispositions :=
  fun x hx => program.accounted.pending_resolved x (List.mem_toFinset.mpr hx)

end WFProgram

/-- A checked program with finite initial state and finite operational domains.
This is proof/evidence, not a semantic parameter of the game. -/
class FiniteDomains {P : Type} [DecidableEq P] {L : IExpr}
    (g : WFProgram P L) where
  context : FiniteVCtx g.core.Γ
  program : FiniteProgram g.core.prog

instance finiteDomains_of {P : Type} [DecidableEq P] {L : IExpr}
    (g : WFProgram P L)
    [FiniteVCtx g.core.Γ] [FiniteProgram g.core.prog] :
    FiniteDomains g where
  context := inferInstance
  program := inferInstance

end Vegas
