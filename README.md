# StratLet

A Lean 4 formalization providing formal semantics for programs designed to express games. This project develops a layered calculus where games are represented as programs with probabilistic outcomes, player choices, and partial information.

## Overview

Games are expressed as programs where:
- Players make **strategic choices** from available actions
- Outcomes may be **probabilistic** (sampling from distributions)
- Players may have **partial information** about the game state (modeled via views)
- **Strategy profiles** determine how players choose actions

The semantics are defined in layers, each building on the previous:

1. **Deterministic computation** - Basic typed expressions and environments
2. **Probabilistic programs** - Sampling from distributions with conditioning
3. **Strategic programs** - Player-owned choices with strategy profiles
4. **Partial information** - Views, commitments, and reveals

## Project Structure

```
Vegas/
├── Env.lean          # Type-safe De Bruijn environments and values
├── Expr.lean         # Expression language (int, bool, basic ops)
├── ProgCore.lean     # Generic program calculus with pluggable effects
├── WDist.lean        # Finite-support weighted distributions
├── ProbLet.lean      # Probabilistic programs with sampling/conditioning
├── FullInfoLet.lean  # Strategic games with perfect information
└── PartialInfoLet.lean  # Games with hidden information via views
```

## Key Concepts

### Strategy Profiles
A `Profile` maps player choices to probability distributions over actions. Fixing a profile converts a strategic program into a pure probabilistic program.

### Behavioral Interpretation
Programs can be evaluated to a lazy `Beh` (behavior) tree that exposes decision points. This separates the program structure from strategy instantiation.

### Views (Partial Information)
A `View` projects the full environment to a subset visible to a player. This models information asymmetry - players choose based only on what they can see.

### Commit-Reveal
The partial information layer includes `commit` and `reveal` commands for modeling protocols where values are hidden and later disclosed.

## Building

Requires Lean 4 (v4.27.0) and Mathlib.

```bash
lake build
```

## Status

This is preliminary research work exploring formal foundations for expressing games as programs. The API and structure are subject to change.
