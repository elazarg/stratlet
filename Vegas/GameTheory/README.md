# Vegas/GameTheory -- Classical Game Representations

This module defines classical game-theoretic representations -- extensive-form games (EFG), multi-agent influence diagrams (MAID), and normal-form games (NFG) -- as standalone data structures in Lean 4. These exist in parallel to the protocol calculus layer (`LetProtocol/`) and serve as targets for denotation (future WP2/WP3 bridges) and as independent formalizations of standard concepts.

## Design Overview

Each file defines a self-contained game representation with its own types, evaluation, and solution concepts. These are classical representations from the game theory literature, formalized with the standard definitions. They do not depend on the `Prog` calculus or the `Language` interface -- they are purely mathematical structures.

The intended relationship to the protocol layer is:
- **EFG**: A `ParentProtoProg` can be mapped to a `GameTree` by unfolding the protocol into a tree of terminal, chance, and decision nodes.
- **MAID**: A `ParentProtoProg` can be mapped to a `Diagram` by extracting the DAG structure of yield sites and their parent dependencies.
- **NFG**: A finite game with simultaneous moves can be represented directly.

These bridges are planned for WP2 (`Denotations.lean`) and WP3 (`EUBridge.lean`) but are not yet implemented.

## Extensive-Form Games (EFG.lean)

**`GameTree iota`** -- An inductive game tree parameterized by a player type `iota`:
- `terminal payoff` -- leaf node with a payoff function `iota -> Real`
- `chance branches` -- nature node with weighted branches `List (GameTree x NNReal)`
- `decision pid player actions` -- player decision node identified by a decision-point ID `pid`, the player `player`, and a list of subtrees (one per action)

**`PureStrategy`** -- Maps decision-point IDs to action indices (`Nat -> Nat`).

**`BehavioralStrategy`** -- Maps decision-point IDs to distributions over actions (`Nat -> List NNReal`).

**`WFTree`** -- Well-formedness predicate: chance nodes have nonempty branches with weights summing to 1; decision nodes have nonempty action lists; recursive.

**`GameTree.eval`** -- Pure strategy evaluator: traverses the tree, selecting actions deterministically.

**`GameTree.evalWDist`** -- Behavioral strategy evaluator: returns a `WDist` over payoff functions.

**`InformationSet`** -- Groups decision nodes where a player cannot distinguish between them (structural definition; not yet connected to evaluation).

## Multi-Agent Influence Diagrams (MAID.lean)

**`NodeKind`** -- `chance`, `decision agent`, or `utility agent`.

**`Node`** -- A node with `id : Nat`, `kind : NodeKind`, and `parents : List Nat`.

**`Diagram`** -- A MAID: a list of `Node`s with unique IDs, valid parent references, and an acyclicity property.

**`Policy`** -- Maps decision node IDs to distributions (`Nat -> List NNReal`).

Queries: `decisionNodes`, `utilityNodes`, `agents`, `findNode`.

## Normal-Form Games (NFG.lean)

**`NFGame iota A`** -- A finite normal-form game with player type `iota` and action types `A : iota -> Type` (all finite). The payoff function maps strategy profiles to player utilities.

**`StrategyProfile A`** -- A pure strategy profile: each player picks an action (`forall i, A i`).

**`deviate s i a`** -- Replace player `i`'s action in profile `s` with `a`.

**`IsNashPure G s`** -- Pure Nash equilibrium: no player can improve by unilateral deviation.

**`IsDominant G i a`** -- Action `a` is dominant for player `i`: best response against all opponent profiles.

**`dominant_is_nash`** -- If every player has a dominant action, the profile of dominant actions is Nash.

## Normal-Form Game Examples (NFGExamples.lean)

- **Prisoner's Dilemma**: (Defect, Defect) is proved to be a pure Nash equilibrium; (Cooperate, Cooperate) is proved not to be.
- **Matching Pennies**: No pure Nash equilibrium exists (proved by exhaustive case analysis).

## EFG Examples (EFGExamples.lean)

- **Sequential game tree**: P0 picks L/R, then P1 picks L/R. Payoffs verified under "always left" and "always right" pure strategies.

## What Is Not Modeled

- No mixed strategy Nash equilibrium for NFG (only pure).
- No evaluation or equilibrium computation for MAID (structural definition only).
- No information set-aware evaluation for EFG (information sets are defined but not connected to strategy restrictions).
- No bridges to the protocol calculus (planned for WP2/WP3).
- No Bayesian games or games with incomplete information.
- No mechanism design or auction theory.

## Design Decisions

- **Standalone definitions**: Each game representation is self-contained and does not depend on the protocol calculus. This allows independent development and testing.
- **`Nat`-indexed decision points in EFG**: Decision nodes carry a `pid : Nat` rather than being identified by tree position. This matches the MAID convention and simplifies strategy definitions.
- **Finite types for NFG**: The `Fintype` and `DecidableEq` requirements on player and action types ensure all quantifications are decidable, enabling computational proofs.

## Further Reading

- Koller, Milch. "Multi-Agent Influence Diagrams for Representing and Solving Games" (GEB 2003) -- MAIDs.
- Osborne, Rubinstein. "A Course in Game Theory" (MIT Press, 1994) -- extensive-form and normal-form games.
- Kuhn. "Extensive Games and the Problem of Information" (1953) -- information sets and behavioral strategies.
- Myerson. "Game Theory: Analysis of Conflict" (Harvard, 1991) -- comprehensive game theory reference.

## File Listing

| File | Description |
|------|-------------|
| `EFG.lean` | `GameTree`, `PureStrategy`, `BehavioralStrategy`, `WFTree`, `eval`, `evalWDist`, `InformationSet` |
| `EFGExamples.lean` | Sequential game tree example with payoff verification |
| `MAID.lean` | `NodeKind`, `Node`, `Diagram`, `Policy`, structural queries |
| `NFG.lean` | `NFGame`, `StrategyProfile`, `deviate`, `IsNashPure`, `IsDominant`, `dominant_is_nash` |
| `NFGExamples.lean` | Prisoner's Dilemma and Matching Pennies with Nash equilibrium proofs |
