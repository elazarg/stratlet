# Outcomes, payouts, and utilities

## Semantic boundary

The protocol determines legal actions, information, and an outcome law. An
analysis supplies an interpretation of those outcomes and a utility for each
player. The compiler does not enforce a player's preferences.

`Vegas.Payout` is the finite integer vector evaluated by source `ret` and
compiled payout expressions. It is neither the complete semantic outcome nor
an assertion about asset delivery. `Machine.Program.boundedOutcomeGame observe value`
attaches any interpretation of the settled machine state and any real utility
profile. `Machine.Program.boundedGame` is the explicit default convention that values
the integer payout itself. `payoutUtility` names that convention. No source
constructor or well-formedness condition is changed.

For an economic interpretation, use separate allocation, asset-transfer, and
quitting components. A utility function may use any of them. In particular,
asset transfers can conserve a pot while utilities need not sum to zero.
Interpreting a record as a delivery or ownership change does not establish
that a blockchain realizes it. The ledger adapter must discharge that claim.

`serializedBoundedOutcomeGame` uses the same interpretation on the settled base state.
`serializedBoundedOutcomeGame_nash_iff` preserves and reflects player Nash for every
such valuation and every admitted public-data scheduler. The request compiler
already accepts arbitrary source-history utility, and `BoundedGame.requestAdequacy`
therefore applies to these valued games when its finite-menu and recall
requirements hold. Neither result covers a utility that distinguishes runtime
details erased by its decoder merely because it is called a valuation.

## Preservation specifications

The generic modules import GameTheory, not the Vegas language or graph syntax.
They are reusable for other finite-outcome runtime models.

| Specification | Meaning and scope |
| --- | --- |
| `OutcomeSimulationOn` | Exact decoded honest and unilateral-deviation laws, with a uniform playerwise back-translation and an explicit deviation class. |
| `DeviationAdequacyOn` | Outcome simulation plus equality of target and decoded source utility. `withUtility` attaches any source valuation to one simulation. |
| `FactorsThrough` | A target valuation can be computed from the decoded source outcome alone. |
| `AgreeOnTests` | Two laws have the same expectations for a chosen class of observations or utility tests; this can be weaker than full trace-law equality. |
| `HonestContextSimulation` | Any target context fixing designated honest strategies decodes to a finite mixture of source contexts fixing the same strategies. This is a stronger obligation, not an instance inferred from unilateral adequacy. |

Outcomes can themselves be observable source traces. Choosing a coarser
economic readout deliberately forgets distinctions; choosing a finer trace
readout asks a stronger question. These choices must be stated in a theorem,
not inferred from a type being named `Outcome`.

`universal_expectation_iff` characterizes the exact boundary: equality of
decoded laws preserves a target valuation's expectation for every pair of
finite laws iff the valuation factors through the decoder. Equivalently it
must be constant on every decoder fibre (`factorsThrough_iff`). If two target
outcomes decode identically but have different values, their point laws refute
the universal property. This is an all-laws result. A concrete runtime may
only need a condition on reachable laws or attainable deviations.

## Opponents with additional trace preferences

There are three different questions.

1. **Is the honest player's policy still a best response at the compiled
   profile?** Its comparison depends only on its own utility and the fixed
   opponent strategies. Changing an opponent's utility without changing that
   opponent's policy does not change this comparison.
2. **Will an equilibrium opponent keep its compiled policy?** Not in general.
   For a target utility `sourceValue ∘ decode + bonus`,
   `combined_noGain_iff` proves that a replacement is unprofitable exactly when
   its expected bonus gain is at most its back-translated source-value loss.
   Nonpositive bonus gain suffices at a source best response; a positive gain
   smaller than a strict source loss also suffices. A uniform bonus-gain bound
   gives an approximate best-response bound (`combined_regret_bound`). These
   comparisons include the distribution of traces, not just terminal labels.
3. **What if the opponent changes strategy for any reason?**
   `OutcomeSimulationOn.guarantee` transports any expected lower bound proved
   against all source replacements of that opponent. It makes no reference to
   the opponent's utility or rationality. The observable can value an honest
   victim rather than the deviator. Other players remain fixed. For several
   arbitrary opponents, `HonestContextSimulation.guarantee` requires its
   stronger context-law hypothesis; no generic coalition instance is claimed.

The checked `VegasTests.TraceUtility` witness distinguishes (2) from (3).
Both players receive one at the safe source outcome and zero at the harmful
outcome. The opponent controls that choice. The target adds a controllable
bit and pays the opponent an extra two for a harmful outcome with that bit set.
Every compiled strategy sets the bit to false, so every compiled profile has
the original utility. Exact outcome simulation holds for every replacement.
The harmful profile is a target Nash equilibrium and the safe source Nash
profile fails to be target Nash. The honest player receives zero at the harmful
equilibrium. Its source equilibrium payoff of one was never a guarantee
against every source opponent.

"Consistent utility" must name a property. Equality after decoding, a
nonprofitable residual, and a residual bounded by the source loss have different
consequences. Preserving the order of deterministic outcomes alone is not
enough to preserve comparisons of lotteries under expected utility: a nonlinear
increasing transformation can change those comparisons.

## Relationship to secure compilation

The outcome decoder and adversarial back-translation use established
secure-compilation ideas. In [robust property preservation](https://arxiv.org/abs/1807.04603),
source properties quantified over all source contexts must survive all target
contexts. [Trace-relating secure compilation](https://doi.org/10.1145/3460860)
also accounts for different source and target observation spaces.

Here fixed honest policies play the role of the protected component and
opponent strategies play the role of adversarial contexts. An expected-value
bound is a quantitative property of an outcome distribution, so trace-set
inclusion alone does not suffice. Nash compares the law of a profile with the
law after a unilateral replacement, retaining the other participants' policies.
The distinction between a uniform context back-translation and a profile-local
mixture is material to these comparisons.

This is the research positioning, not a checked equivalence or embedding of
our certificates into those frameworks. The general robust-preservation idea,
outcome decoding, and elementary utility-factorization and bonus calculations
are supporting theory. The concrete Vegas information model, controller replay,
and scheduling constructions carry the compiler contribution.

## Remaining boundaries

- Private types belong to the information/preferences layer, not to mandatory
  source commitments. GameTheory represents Bayesian type-contingent plans,
  but a uniform type-local Vegas/runtime policy correspondence is not proved.
  A fixed valuation parameter is not a private-information model.
- The Kotlin frontend and solver exporters still use their monetary analysis
  convention. This Lean interface does not claim a new Kotlin valuation syntax
  or certified Kotlin-to-Lean translation.
- Runtime trace costs, transaction fees, external asset delivery, censorship,
  and deadline incentives require explicit outcome interpretations and utility
  relations. They are not accounted for by silently assigning zero value to
  erased details.
- The generic trace-bonus theorem uses a uniform outcome-simulation certificate.
  The public serializer's behavioral back-translation is instead a
  profile-local mixture. Its existing arbitrary-state-observable bound theorem
  establishes protection independently of adversarial preferences; it does not
  identify a uniform source back-translation for trace-sensitive equilibria.

The next bounded extension is a finite private-type policy adapter and one
valuation-sensitive mechanism with explicit source quitting. Dominant-strategy
truthfulness against arbitrary runtime opponents needs more than preservation
of Nash at compiled profiles. Realized multi-asset settlement needs a separate
ledger model even if its utilities have already been defined in Lean.
