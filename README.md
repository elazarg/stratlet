# StratLet

A Lean 4 formalization providing formal semantics for games expressed as programs. This project develops a layered calculus where games are represented as typed programs with probabilistic outcomes, player-owned strategic choices, and partial information.

## Overview

Games are expressed as programs where:
- Players make **strategic choices** from available actions, restricted by **Views** (observable projections of the environment)
- Outcomes may be **probabilistic** (sampling from finite-support weighted distributions)
- **Strategy profiles** determine how players choose actions at each decision point
- **Conditioning** uses hard rejection (`observe`) on boolean predicates

The semantics are defined in layers, each building on the previous:

1. **LetCore** -- Typed environments (de Bruijn indices), abstract `Language` interface, generic `Prog` calculus parameterized by effect commands
2. **LetProb** -- Weighted distributions (`WDist`), sampling, conditioning, measure-theoretic bridge to Mathlib
3. **LetProtocol** -- Protocol-with-yields: `sample` (chance) and `choose` (decision) commands with Views, Profiles, Nash equilibrium
4. **LetGames** -- Game-theoretic layer: utility functions, expected utility, deviations, Nash equilibrium
5. **GameTheory** -- Classical game representations (EFG, MAID, NFG) as standalone types

## Project Structure

```
Vegas/
  Defs.lean              -- Cross-cutting definitions (Player = Nat)
  LetCore/               -- De Bruijn envs, Language interface, generic Prog
    Env.lean             -- Typed environments and de Bruijn indices
    Language.lean        -- Abstract Language interface and ExprLaws
    Prog.lean            -- Generic program calculus, evaluator, LangSem
    ProgLemmas.lean      -- Equational laws for the deterministic fragment
    Concrete.lean        -- BasicLang: concrete int/bool language
  LetProb/               -- Probabilistic layer
    WDist.lean           -- Weighted distributions, monad ops, toMeasure
    WDistLemmas.lean     -- Monad laws, mass properties, measure bridge
    Prob.lean            -- Probabilistic programs (PProg), evalP
    ProbLemmas.lean      -- Simp lemmas, observe laws, conservation, posterior
    EquivLaws.lean       -- Program equivalence (ProgEq), congruence, algebraic laws
    MeasureTransformer.lean  -- Alternative MT denotation, correctness
    ConditionalEU.lean   -- EV, EV_cond, EV_bind tower property
  LetProtocol/           -- Protocol / strategic calculi
    Proto.lean           -- Flagship: ProtoProg, View, Profile, Game, Nash
    ProtoLemmas.lean     -- Simp lemmas, profile irrelevance, bridge to Prob
    ProtoCondEU.lean     -- Conditional EU, IsNash_Cond
    ProtoGameLemmas.lean -- EU lemmas, deviator identity
    FullInfo.lean        -- Full-info variant with behavioral/operational semantics
    FullInfoLemmas.lean  -- Extensional properties for FullInfo
    PartialInfo.lean     -- Partial-info variant with commit/reveal (BasicLang)
    PartialInfoLemmas.lean -- Commit-reveal coherence, view properties
    Dag.lean             -- DAG-style variant with Views
    DagLemmas.lean       -- Profile independence, observe fusion for Dag
    ParentView.lean      -- MAID-compatible parent-set views
    ParentViewLemmas.lean -- Local info, compilation bridge, round-trip
    ParentViewExample.lean -- Sequential game example
    Step.lean            -- IO evaluator with callback handler
    Examples/            -- Worked examples (SequentialGame, HiddenDecision)
  LetGames/              -- Game-theoretic layer on Dag
    Game.lean            -- EU, WFProfile, Deviate, IsNash, IsNash_WF
  GameTheory/            -- Classical game representations
    EFG.lean             -- Extensive-form game trees, evaluators
    EFGExamples.lean     -- Sequential game tree example
    MAID.lean            -- Multi-agent influence diagrams
    NFG.lean             -- Normal-form games, Nash, dominance
    NFGExamples.lean     -- Prisoner's Dilemma, Matching Pennies
```

## Key Concepts

### Strategy Profiles
A `Profile` maps player decisions to probability distributions over actions. Each decision site has a `View` that restricts what the player can observe. Fixing a profile converts a strategic program into a pure probabilistic program.

### Views (Partial Information)
A `View Gamma` projects the full environment `Env Gamma` to a visible sub-environment `Env Delta`. Strategies at a yield site can only depend on the projected environment, enforcing information restrictions structurally.

### Weighted Distributions
`WDist alpha` is a finite-support weighted distribution: a list of `(value, NNReal)` pairs. It forms a monad (`pure`, `bind`, `zero`) and can be lifted to Mathlib's `Measure` type via `toMeasure`.

### Nash Equilibrium
`IsNash_WF` defines Nash equilibrium: no player can improve their expected utility by a unilateral deviation, restricted to well-formed (legal) deviations.

## Building

Requires Lean 4 and Mathlib.

```bash
lake build
```

## Status

This is research work exploring formal foundations for expressing games as programs. The core calculus and key theorems are proved; classical game representations (EFG, MAID, NFG) are defined; bridges between the protocol calculus and classical representations are planned.
