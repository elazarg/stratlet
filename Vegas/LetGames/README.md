# Vegas/LetGames -- Game-Theoretic Layer on DagLet

This module adds game-theoretic structure on top of the `Dag` (DAG-style) calculus: utility functions on outcomes, expected utility computation, profile well-formedness predicates, unilateral deviations, and Nash equilibrium.

## Design Overview

`Game.lean` does not introduce a new calculus or evaluator. It defines the game-theoretic concepts (EU, Nash, WF profiles) that operate on the `Dag.DagProg` syntax and `Dag.evalD` semantics. The key idea is that a "game" is a `DagProg` (the rules/protocol) plus a `Utility` function (the payoffs), and game-theoretic reasoning happens externally via deviations and EU comparisons.

Note: The flagship `Proto.lean` calculus (in `LetProtocol/`) defines its own `Game`, `EU`, and `IsNash_WF` types directly. This `LetGames/Game.lean` provides an analogous structure for the `Dag` variant. The two are parallel but not unified; a future bridge could relate them.

## Key Types

**`EU_ofWDist d u who`** -- Expected utility: weighted sum of `u(outcome, player)` over the support of distribution `d`.

**`EU sigma p env u who`** -- Expected utility induced by evaluating `DagProg p` under profile `sigma` at environment `env`, with utility `u`, for player `who`.

**`SupportedOn v A envv d`** -- Legality predicate: every value in `d.weights` is a legal action in `A envv`.

**`WFProfileLocal sigma`** -- The profile's chosen distributions are supported on the offered action sets at every view-environment.

**`Profile.overrideAt sigma who choose'`** / **`Deviate`** -- Override a profile for a single player, leaving other players' strategies unchanged.

**`IsNash sigma p env u`** -- No player can improve their EU by a unilateral deviation over all possible replacement strategies.

**`IsNash_WF`** -- Nash equilibrium restricted to deviations that maintain `WFProfileLocal` (legality).

## What Is Not Modeled

- No mixed strategy Nash equilibrium existence (only the definition; no existence proofs).
- No subgame perfection or refinements.
- No connection to measure-theoretic EU; everything is discrete finite sums.
- No multi-game or repeated game structure.
- No mechanism design or auction-specific utilities.

## Design Decisions

- **Utility is external**: `L.Val tau -> Player -> Real` is a function provided alongside the program, not embedded in the syntax. This keeps the calculus generic.
- **Deviations are unrestricted by default**: `IsNash` quantifies over all replacement strategies. `IsNash_WF` adds legality as a side-condition.
- **Bridge to ProbLet**: The file re-exports `evalD_eq_evalP_toProb` as a convenience, so measure-theoretic reasoning can be done via the Prob layer.

## File Listing

| File | Description |
|------|-------------|
| `Game.lean` | `EU_ofWDist`, `EU`, `SupportedOn`, `WFProfileLocal/Global`, `Deviate`, `IsNash`, `IsNash_WF`, ProbLet bridge |
