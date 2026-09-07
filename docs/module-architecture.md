# Library and proof boundaries

The package has four build targets. `lake --wfail build` checks all four;
`lake --wfail build Vegas` checks the runtime-general library alone.

| Target | Contents | Local dependencies |
| --- | --- | --- |
| `Vegas` | Core and surface syntax, event graphs, machine semantics, games, abstract runtimes, public serialization | none |
| `VegasEVM` | Contract representations, deployment and instruction semantics, backend compilation, local code-generation proofs | `Vegas` |
| `VegasTests` | Concrete witnesses and regression tests | `Vegas`, `VegasEVM` |
| `Paper` | Axiom-pinned general claims and concrete paper witnesses | all three |

All targets also use the pinned external mathematical dependencies. The table
describes library dependencies, not additional logical axioms.

## Backend correctness

`VegasEVM/Compile/EVMRefinement.lean` defines `BooleanCompilationCorrect`, the
whole-backend instruction-level simulation obligation. It is not discharged.
The checked expression and handler lemmas in the backend do not imply that
obligation, nor do they establish strategic preservation on deployed bytecode.
Keeping the backend in the full default build checks its existing proofs while
allowing consumers of `Vegas` to avoid importing this development.

## Carrier definitions and compiler edges

`Vegas/Machine/Program.lean` defines the backend-neutral machine carrier and
its execution model. `Vegas/Compile/Machine.lean` constructs it from checked
source programs and proves source-support and terminal-payout adequacy.
The machine carrier does not import its compiler.

`Vegas/Game/Basic.lean` defines games and their graph-derived instances.
`Vegas/Game/Kuhn.lean` supplies strategy-representation certificates, and
`Vegas/Game/Request.lean` instantiates generic request compilation for games.
`Vegas/Game.lean` imports all three. The runtime interfaces do not import the
game-specific adapters.

`Vegas/Language/Basic.lean` owns surface syntax; `Vegas/Language/ToCore.lean`
owns its typed lowering. The lowering returns core syntax, not a `WFProgram`
certificate. The language regression tests check specific lowering equations
and nullable-guard behavior. General admission and semantic-preservation
theorems for that surface language remain separate obligations.

## Ownership and maintenance

Declarations extending graph execution live in `Vegas.EventGraph`, even when
their files are under `Vegas/Scheduled/`. Public modules group related results;
declaration namespaces identify the objects or constructions they concern.
The graph serialization implementation uses the existing graph write lemmas
directly instead of re-exporting copies under a compiler grouping namespace.
Player-only equilibrium notions and independent-signal constructions live
under `Vegas.Participant`; the public-submission counterexample has its own
`Vegas.PublicSubmission` namespace. Generic finite-law composition and product
projection belong to GameTheory's `FinDist` API; bounded execution and
one-participant predrawing belong to its protocol layer. The scheduled-runtime
proofs use those APIs and supply the scheduler-specific information and
profile facts.

Use `private` for helpers whose role is confined to a proof or implementation.
Usage counts alone are insufficient: typeclass instances, simplification
lemmas, theorem-statement dependencies, and intentional analysis APIs may have
no explicit callers outside their defining file.

`scripts/check-module-boundaries.py` checks local import resolution, default-root
coverage, complete game/runtime aggregators, and the dependency directions
above. It scans configured library trees, not temporary research checkouts.
The warning-free Lean build remains the check that imports and proofs elaborate.

The paper audit lives in `Paper/General.lean` and root `Paper.lean`; tests use
the owning mathematical theorems directly rather than importing audit wrappers.
The live manuscript is separately revision-pinned as described in `ARTIFACT.md`.
