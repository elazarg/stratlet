# VegasCore

A Lean 4 formalization providing formal semantics for the [VEGAS](https://github.com/elazarg/VEGAS) game specification language. VegasCore defines a layered calculus for strategic computation and compiles game specifications to [Multi-Agent Influence Diagrams (MAIDs)](https://github.com/elazarg/GameTheory), from which extensive-form games can be derived via the GameTheory library's MAID-to-EFG bridge.

The repository has one mainline implementation and one secondary exploration tree:

- `Vegas/` is the mainline language and backend stack.
- `Explorations/` preserves older design explorations, but is not the primary
  project surface.
- `GameTheory/` is the root-level submodule providing the broader game-theory
  library used by the MAID backend.

## Overview

Games are expressed as programs where:
- Players make **strategic choices** from available actions, restricted by **Views** (observable projections of the environment)
- Outcomes may be **probabilistic** (sampling from finite-support weighted distributions)
- **Strategy profiles** determine how players choose actions at each decision point

The mainline `Vegas/` tree is organized around:

1. **Core / ExprSimple / VegasSimple** -- the generic interface and current concrete instantiation
2. **BigStep / TraceSemantics / ActionGraph** -- the main semantic presentations and graph IR
3. **Strategic / MAID** -- the strategic semantics and the main backend stack
4. **GameTheory** -- the external submodule providing MAID and general game-theory infrastructure

## Project Structure

```text
Vegas/
  Core.lean
  ExprSimple.lean
  VegasSimple.lean
  WF.lean
  Examples.lean
  FDist.lean
  BigStep.lean
  TraceSemantics.lean
  ActionGraph.lean
  Strategic.lean
  MAID/
    Backend.lean
    Compile.lean
    Fold.lean
    Correctness.lean

Explorations/
  LetCore/
  LetProb/
  LetProtocol/
  LetGames/

GameTheory/
```

## Key Concepts

### Strategy Profiles
A `Profile` maps player decisions to probability distributions over actions. Each decision site has a `View` that restricts what the player can observe. Fixing a profile converts a strategic program into a pure probabilistic program.

### Views (Partial Information)
A `View Gamma` projects the full environment `Env Gamma` to a visible sub-environment `Env Delta`. Strategies at a commit site can only depend on the projected environment, enforcing information restrictions structurally.

### Weighted Distributions
`FDist alpha` is the main finitely-supported weighted distribution used in the
mainline semantics. It is implemented with `Finsupp` over `ℚ≥0`.

### Strategic Semantics
`Vegas/Strategic.lean` packages normalized Vegas programs as `KernelGame`s so
general game-theory results can be imported from `GameTheory`.

## Building

Requires Lean 4, Mathlib, and the checked-out `GameTheory` submodule.

```bash
git submodule update --init --recursive
lake build
```

## Status

This is research work exploring formal foundations for expressing games as
programs. The mainline repository is MAID-first: game specifications compile to
MAID representations, from which extensive-form games (EFG) can be derived via
the `GameTheory` library's MAID -> EFG bridge.
