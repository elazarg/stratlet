import Vegas.Scope

/-!
# Well-formed Vegas programs

This file defines `WFProgram`, the bundle that packages a Vegas program with
the three well-formedness obligations needed to produce a game-theoretic
object from it: `WF` (fresh bindings, reveal-completeness, view-scoping),
`NormalizedDists` (sample distributions sum to 1), and `Legal` (every commit
site has a feasible action). User-facing game APIs downstream — `toKernelGame`,
`Game`, `IsNash`, `IsPureNash`, `IsεNash`, and the equilibrium-family
predicates — consume `WFProgram` rather than a raw `VegasCore` plus separate
side conditions. This is the API boundary where raw, unchecked syntax becomes
a "real" game.

Internal semantic functions (`outcomeDistBehavioral`, `outcomeDistPure`,
`outcomeDistBehavioralPMF`, `outcomeDist`) and the MAID/TraceSemantics
metatheory continue to operate on raw programs — they recurse through
subprograms where constructing fresh bundles would be painful and
irrelevant.

**Strategy-level guard admissibility.** The program-level `Legal`
predicate only promises that every commit site *admits* some guard-
satisfying action; it does not rule out strategies that propose
guard-violating actions. To close that gap, `toKernelGame` and
`toStrategicKernelGame` refine their `Strategy` field to a subtype
carrying `ProgramBehavioralStrategy.IsLegal` / `ProgramPureStrategy.IsLegal`:
every commit site's kernel is required to satisfy the commit guard at
every reachable environment. The user-facing equilibrium predicates and
all downstream corollaries consume these *legal* subtypes, so a "Nash
equilibrium" the corollaries produce is automatically protocol-legal.
-/

namespace Vegas

/-- A Vegas program paired with its initial environment and the three
well-formedness obligations needed to interpret it as a game.

* `wf`         — the program is structurally well-formed: fresh bindings,
  reveal-completeness, and view-scoping (see `WF` in `Vegas.Scope`).
* `normalized` — every sample site's distribution sums to `1`.
* `legal`      — every commit site has at least one action satisfying its
  guard (the game never deadlocks).

`wf` already includes `RevealComplete []`, so the bundle does not carry a
separate `reveals` field. -/
structure WFProgram (P : Type) [DecidableEq P] (L : IExpr) where
  Γ : VCtx P L
  prog : VegasCore P L Γ
  env : VEnv L Γ
  wf : WF prog
  normalized : NormalizedDists prog
  legal : Legal prog

end Vegas
