# Vegas/LetProtocol/Examples -- Worked Protocol Examples

This directory contains small, self-contained examples that demonstrate how to encode games as `ProtoProg` programs using the protocol calculus.

## SequentialGame.lean -- Two-Player Coordination

A two-player sequential game using `BasicLang`:

1. **Player 0** chooses a boolean (yield ID 0, empty view -- sees nothing).
2. **Player 1** observes Player 0's choice (yield ID 1, full view projecting to the boolean context), then chooses a boolean.
3. The program returns Player 1's choice.

Utility is a coordination game: both players prefer matching choices (1 if match, 0 otherwise). The example demonstrates:
- Views with different visibility: empty view for P0 (no information), full view for P1 (observes P0's choice).
- Yield ID assignment and `NoDupYieldIds`.
- `Game` construction with `ProtoProg` + `Utility`.

Structural theorems verify that the protocol has exactly two yields `[0, 1]`, both are decision yields, and yield IDs are unique.

## HiddenDecision.lean -- Nature Samples, Player Guesses Blind

A single-player decision problem with hidden information using `BasicLang`:

1. **Nature** samples a boolean uniformly (yield ID 0, empty view, `WDist.uniform`).
2. **Player 0** guesses a boolean (yield ID 1, empty view -- cannot see nature's sample).
3. The program returns the guess.

This demonstrates:
- A `sample` yield (chance node) versus a `choose` yield (decision node).
- Information asymmetry: the player's view is empty despite the environment containing nature's sample.
- The expected utility under any strategy is 0.5 (player guesses randomly, matches half the time).
