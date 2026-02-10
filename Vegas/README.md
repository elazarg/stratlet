# Vegas -- Formal Game Semantics in Lean 4

Vegas is a layered denotational semantics for games expressed as programs. Games are modeled as typed programs with probabilistic outcomes, player-owned strategic choices, and partial information (via environment projections). The semantics maps programs to weighted distributions (`WDist`) that can be lifted to Mathlib's `Measure` type, enabling both computational evaluation and measure-theoretic reasoning.

## Architecture

The layers build strictly upward, each importing only its predecessors:

```
                     GameTheory
                    (EFG, MAID, NFG)
                         |
                      LetGames
                     (Game, EU, Nash)
                         |
                     LetProtocol
              (Proto, FullInfo, PartialInfo,
               Dag, ParentView, Step)
                         |
                       LetProb
              (WDist, Prob, EquivLaws,
               MeasureTransformer, ConditionalEU)
                         |
                       LetCore
              (Env, Language, Prog, Concrete)
                         |
                        Defs
                      (Player)
```

**LetCore** defines the generic program calculus: de Bruijn-indexed environments, an abstract `Language` interface, and a `Prog` type parameterized by bind/stmt commands. The generic evaluator `evalProg_gen` dispatches to command handlers provided by a `LangSem`.

**LetProb** adds probabilistic computation: `WDist` (weighted finite-support distributions), sampling commands, hard conditioning (`observe`), and a suite of measure-theoretic bridge theorems connecting `WDist` to Mathlib's `Measure`.

**LetProtocol** adds strategic computation: yield sites where players make choices (restricted by Views to partial information), strategy profiles, strategy application (`applyProfile`), compilation to `Prob`, EU computation, and Nash equilibrium. Five variant calculi explore different information structures (full info, partial info, DAG-style, parent-set/MAID-compatible).

**LetGames** adds game-theoretic structure (utility functions, EU, deviations, Nash) on top of the Dag variant.

**GameTheory** defines classical game representations (extensive-form game trees, multi-agent influence diagrams, normal-form games) as standalone types, intended as denotation targets for the protocol calculus.

## Design Philosophy

**Correct by construction.** Programs are intrinsically well-typed via de Bruijn indices; there is no type-checking phase that could fail. Partial information is enforced by View projections at each yield site -- the profile/kernel can only observe `Env Delta`, not `Env Gamma`.

**Layered effect decomposition.** Each layer adds exactly one concern (probability, strategy, information restriction) by instantiating the generic `Prog` with new command families. The evaluator, environment machinery, and structural lemmas are shared.

**Computational and denotational.** `WDist` is a computable data structure (list of pairs); `toMeasure` lifts it to Mathlib's measure theory. Proofs connect the two, but computation does not require measure theory imports.

**Unnormalized semantics.** Conditioning is hard rejection (zeroing mass), not renormalization. This matches the measure transformer approach of Borgstrom et al. (2013) and avoids division-by-zero issues until the explicit normalization step.

## Key Type Flow

```
Language  -->  Prog CB CS Gamma tau  -->  WDist (L.Val tau)
               (generic program)          (weighted distribution)
                     |
               ProtoProg Gamma tau   -->  evalProto sigma p env : WDist
               (protocol program)         (under a fixed Profile sigma)
                     |
               Game Gamma            -->  EU G sigma env who : Real
               (program + utility)        (expected utility)
```

## What This Project IS

- A formal semantics for multi-player games with probabilistic outcomes and partial information, expressed as typed programs in Lean 4.
- A layered calculus where each concern (determinism, probability, strategy, information) is added incrementally.
- A framework for stating and proving properties like observe fusion, profile irrelevance, semantic preservation under compilation, and Nash equilibrium conditions.

## What This Project IS NOT

- Not a game solver or equilibrium finder. It defines what Nash equilibrium *means* formally, but does not compute equilibria.
- Not an AI/ML tool. There is no learning, no neural network integration, no reinforcement learning.
- Not a blockchain or smart contract framework. The commit/reveal in `PartialInfo` is a structural placeholder, not a cryptographic protocol.
- Not a general-purpose probabilistic programming language. The focus is on game semantics, not inference or model fitting.

## Directory Structure

| Directory | Description |
|-----------|-------------|
| `Defs.lean` | Cross-cutting definitions (`Player = Nat`) |
| `LetCore/` | De Bruijn environments, `Language` interface, generic `Prog` calculus |
| `LetProb/` | `WDist`, probabilistic programs, measure bridge, EV tower property |
| `LetProtocol/` | Protocol calculi with yields, Views, Profiles, Nash, five variants |
| `LetGames/` | Game-theoretic layer (EU, deviations, Nash) on Dag |
| `GameTheory/` | Classical game representations (EFG, MAID, NFG) |

## Re-export Modules

The files `LetCore.lean`, `LetProb.lean`, `LetProtocol.lean`, `LetGames.lean`, and `GameTheory.lean` at the top level of `Vegas/` are re-export modules that import all files in the corresponding subdirectory.
