## Bottom line

The strongest paper VegasCore is close to is not an end-to-end verified game-to-blockchain compiler paper.

It is a mechanized semantics paper along these lines:

> A well-formed finite VegasCore program compiles to a bounded imperfect-information game with perfect recall. Terminal
> graph executions reconstruct valid source executions with the same payoff, and behavioral and product-mixed-pure
> strategy presentations are mutually deviation adequate, so their outcome laws and Nash equilibria correspond.
> Public serialization preserves the complete terminal-state law of compiled behavioral play and preserves and reflects
> Nash equilibrium for the original players against every behavioral public-data scheduler and every behavioral player
> deviation. More generally, unilateral runtime-deviation terminal laws are finite mixtures of source-deviation laws
> against unchanged opponents. Every upper bound on expected terminal loss is preserved and reflected, without assuming
> adversarial rationality; approximate Nash equilibria retain exactly the same error budget.

The strongest new result around that core is a mechanized scheduling boundary. The actual graph-derived serializer gives
the scheduler the complete public graph observation, but no sealed value or same-round submission. Every accepted
serialization of a legal frontier reaches exactly the atomic graph successor, not merely an order-independent related
state, and automatic closure consists of ordinary source internal steps. The scheduler is an arbitrary environment
strategy rather than a member of the equilibrium population.

Every runtime player can reconstruct the scheduler's complete information from its own runtime information. The
scheduler may react to all public observations and previous orders. Every legal runtime history has an atomic source
history preserving the graph endpoint, erased player information, and player payoffs. Expanding one runtime round into
source steps preserves the exact joint probability law of state and every player's erased information, including for
arbitrary behavioral runtime policies.

Scheduler replay makes the information argument constructive. For every fixed deterministic public-information
scheduler, a player can reconstruct its full runtime information from its order-free observation history. Replacing
arbitrary behavioral players by these independent local replays preserves the entire execution law. A mixture over
actually executing scheduler policies has the same property; realized orders may depend on public game data.

The canonical source game's compact information determines the player's full order-free runtime information on all
legal traces. The proof uses the data-independent completed-node timeline and preservation of already written fields;
it does not make the scheduler's realized orders data-independent. Canonical source back-translation then reconstructs
every order-aware runtime deviation after fixing an executing scheduler policy, independently of opponents' policies.
Already compiled honest policies back-translate to exactly their original source policies, even off the realized path.

The complete atomic/serialized terminal-state laws agree for compiled source players under every behavioral scheduler.
For randomized deviations, only the scheduler's randomness is predrawn on finitely many support-reachable information
sites. Honest players remain behavioral and their random choices are not disclosed or fixed by the argument. Averaging
the resulting source-deviation inequalities establishes behavioral Nash equivalence for the actual serialized game.
The independent-signal games are auxiliary examples, not premises of this result.

The finite-mixture law is independent of the choice of terminal observable, so it supports honest-player loss bounds as
well as the deviator's incentive inequalities. For randomized schedulers the mixture is profile- and horizon-local;
opponent-independent back-translation is proved for fixed pure executing schedulers. These are unilateral results,
not coordinated-coalition security. They do not assert equality of the entire source and runtime equilibrium sets.

Most ingredients are already proved:

- Terminal source-payoff reconstruction: Vegas/Compile/SourceAdequacy.lean:441
- Bounded horizon and perfect recall: Vegas/EventGraph/Protocol.lean:381, Vegas/Machine/Program.lean:122
- A finite-domain game construction: Vegas/Game.lean:36
- Behavioral↔mixed-pure deviation-adequacy certificates: Vegas/Game/Kuhn.lean:360
- Nash preservation/reflection from deviation adequacy: Vegas/Runtime/DeviationAdequacy.lean:236
- Exact serialized-round implementation and the scheduler information boundary: Vegas/Scheduled/Compiled.lean
- Source-history expansion and exact one-round information laws: Vegas/Scheduled/History.lean
- Executed scheduler replay and exact full behavioral-history laws: Vegas/Scheduled/Replay.lean
- Compact information sufficiency on all legal runtime histories: Vegas/Scheduled/Information.lean
- Opponent-independent canonical policy back-translation: Vegas/Scheduled/Backtranslation.lean
- Complete atomic/serialized terminal-state laws: Vegas/Scheduled/Law.lean
- Scheduler-only finite-support predrawing: Vegas/Scheduled/Predraw.lean
- Actual serializer behavioral Nash preservation and reflection: Vegas/Scheduled/Equilibrium.lean
- Terminal-loss bound equivalence and exact-error approximate Nash: Vegas/Scheduled/Equilibrium.lean
- Concrete compiled fair equilibrium and unilateral-adversary payoff guarantee: VegasTests/MatchingPenniesEquilibrium.lean
- Player-only Nash preservation for independent signals: Vegas/Scheduled/Strategic.lean
- Exact FOSG→EFG behavioral-law and Nash results exist in the imported GameTheory library: GameTheory/GameTheory/
Languages/Bridges/FOSGToEFGStrategic.lean:240

The development uses a full Lean build, paper-facing axiom guards, and a documentation-reference checker. The Kotlin
compiler is a separate artifact; its test results do not validate the Lean strategic claims.

## What the existing result actually says

The project currently has five strong layers:

1. Source program → event graph

    Every terminal compiled execution reconstructs a possible written-order source execution with the same payoff. This
    is support-level, endpoint correctness. It is not equality of probabilistic laws or a strategy-preservation theorem.

2. Event graph → canonical game

    The graph induces a bounded FOSG with perfect recall. Player commitments at a strategic frontier are submitted
    jointly and serialized canonically. Internal nodes, however, are selected noncomputably with Classical.choose: Vegas/
    EventGraph/Protocol.lean:241.

3. Behavioral game ↔ product-mixed-pure game

    This is the strongest concrete deviation-adequacy instantiation. It is a substantial Vegas-specific application of
    the generic Kuhn machinery, and it really does support Nash equivalence.

4. Atomic graph execution ↔ serialized counterfactuals

    The same compiled graph now induces an atomic frontier protocol, a permissive serializer, and a fixed-order serializer.
    The permissive scheduler receives `publicObserve`, may condition on every public value, and accepts exactly the
    duplicate-free enumerations of the currently active players. An explicit write-list permutation proof shows that each
    accepted order reaches exactly `applyFrontier`; subsequent automatic settlement is a sequence of source internal
    transitions and reaches a stable checkpoint. Matching pennies exhibits two genuinely enabled orders and proves both
    implement the same atomic successor. The fixed serializer sorts public activity by a backend-supplied `LinearOrder`;
    its scheduling coordinate is operationally inert.

5. Player-only strategic scheduling adequacy

    `Scheduled.PlayerDeviationAdequacyOn` fixes an arbitrary scheduler strategy and quantifies over unilateral deviations
    only by the source game's players. The independent-signal constructions permit arbitrary scheduler utility and
    arbitrary signal-aware player deviations. Their expected payoff averages ordinary source-deviation payoffs, proving
    Nash preservation and reflection at lifted source profiles. Matching pennies instantiates these auxiliary games.
    The actual serialized game has a separate, unconditional behavioral Nash equivalence theorem. Compact information
    sufficiency connects full order-blind runtime recall to the canonical source game. Replay removes order dependence
    from arbitrary behavioral deviations against each fixed scheduler. Complete terminal laws and scheduler-only
    predrawing extend the result to every behavioral scheduler without changing honest opponents.

There is no strategic-preservation theorem from either game to a generated contract game, and no separate strategic
semantics for the pre-compilation raw program. The canonical atomic-to-serialized Nash theorem is direct: it compares
terminal-state laws and player payoffs, not a deterministic decoding of complete target histories into complete atomic
histories. No such decoder is needed for utilities that depend only on the settled state. Behavioral scheduler policies
use independent local draws; the theorem does not include an external seed correlated with hidden game data.

## The paper I would aim for

The best near-term paper would be something like:

“Mechanized Strategic Semantics for Compiling Partial-Information Games”

The contribution should be presented as:

- a proof-carrying typed core;
- compilation into a canonical concurrent event structure;
- operational source-payoff soundness;
- extraction of a bounded perfect-recall stochastic game;
- exact equivalence of standard strategic presentations;
- behavioral Nash equivalence through a public-data adversarial serialization environment;
- deviation adequacy as the interface required for later runtime passes.

The concrete case study in VegasTests/MatchingPenniesEquilibrium.lean establishes that the initial compiled menus are
exactly Boolean choices, proves the execution's payoff table through automatic reveals, constructs the fair behavioral
equilibrium, and transports it to the actual serializer for every behavioral scheduler. Off-path policies and arbitrary
legal behavioral deviations are included. One fair player guarantees both expected payoffs are exactly zero against an
arbitrary unilateral runtime adversary, irrespective of its objective.

VegasTests/ScheduledEquilibrium.lean also instantiates the equivalence for arbitrary profiles. Initial chance settlement
and the zero-node game instantiate the complete-law theorem. A multistage equilibrium example with public chance between
strategic frontiers remains missing: the general theorem covers it, but the concrete fair-coin example has only one
strategic frontier and therefore does not exercise adaptive scheduling between player decisions.

## The strongest enhanced version

The scheduling theorem supports the following concrete claim:

> Publicly serializing a legal atomic frontier preserves every original player's expected utility and Nash equilibrium,
> uniformly over schedulers that may react to all prior public observations but not to sealed values or current-round
> submissions.

The matching-pennies example combines:

- the existing proof that both runtime orders are accepted and have the same settled graph effect;
- a target utility that factors through the settled source outcome and ignores the order log;
- erasure of every schedule-conditioned target-player policy to an atomic-game policy, after fixing the adversarial
  public-history scheduler;
- the direct player-Nash equivalence theorem, instantiated at the proved equilibrium.

The graph-derived scheduling model establishes these properties generically. Matching pennies has a real concurrent
frontier, permissive serialization exposes both orders, both implement the atomic successor, and automatic nodes settle
via source steps. The information-sufficiency proof and complete law theorem discharge the source/runtime bridge.
Scheduler-only predrawing and source-deviation payoff equalities give Nash equivalence without treating the scheduler
as a Nash player or restricting it to data-independent orders.

## Proved runtime obstructions

The positive serializer theorem is paired with two explicit negative boundaries:

1. Public sequential submission. In Vegas/Scheduled/PublicSubmission.lean, a scheduler chooses the first of two public,
   irreversible Boolean writes; the second player observes the first value. Matching-pennies utility depends only on
   the final bits. The second player can force +1 against any first-player policy. Every target profile preserving its
   source payoff zero therefore fails player Nash; approximate equilibrium slack plus payoff error must be at least 1.
   The resulting impossibility quantifies over all strategy compilers and outcome decoders into this runtime, not merely
   the constant-policy embedding. VegasTests/RuntimeBoundaries.lean instantiates it with the compiled source game.

2. Informed final refusal. Vegas/Runtime/SelectiveAbort.lean adds a designated player's final completion/abort decision,
   observing only its prospective utility. Honest completion preserves the tagged source outcome law. The exact optimal
   refusal value is the expectation of the source payoff clipped from below at the abort payoff. With source choices
   fixed, refusal is unprofitable iff every supported prospective payoff is at least the abort payoff. The full Nash iff
   additionally quantifies over simultaneous replacement of the player's source strategy and randomized refusal rule.
   For compiled matching pennies, a refund payoff of zero makes a deviation worth +1/2. The fair honest-completion lift
   is Nash exactly when the designated player's net abort payoff is at most −1.

The first result changes same-frontier information, so it is not a counterexample to the positive serializer theorem.
The second is an exact characterization for one explicit final-veto pass, not a general completeness theorem for
distributed implementations. It neither provides cryptographic commitments nor implements, funds, or enforces a deposit.
The next bridge is from actual request, disclosure, inclusion, and timeout rules to these modeled capabilities.

## Claims that are currently unsupported or overstated

Several draft claims should be removed or narrowed immediately.

- The abstract says schedule signals can sustain correlated equilibria and that advance and incremental disclosure are
incomparable: overleaf/main.tex:38. I found no corresponding VegasCore theorem; “incremental” does not occur in the
formalization, and correlated equilibrium appears only in comments or proposed work.

- “Source-payoff adequacy” is one-way terminal reconstruction. The prose calling part of that a “support-level converse”
is confusing: overleaf/sections/03-language-graph.tex:126. There is no source/target law equality here.

- The “native frontier game to FOSG” translation is not a separate proved translation: the Vegas arena is directly
defined as a FOSG in Vegas/Game.lean:86. The EFG result is substantial, but imported from GameTheory and should be
attributed as such.

- The paper-facing `schedule_confluence` theorem remains algebraic permutation invariance for a fixed assignment. The new
`compiled_permissive_effects_commute` theorem is the operational serializer result; prose should cite the latter for
runtime order-independence and should still say that the public schedule log differs.

- “Checked program” currently means a manually constructed proof-carrying WFProgram: Vegas/Core/WellFormed.lean:56. The
core compiler is noncomputable, and there is no raw Vegas syntax→WFProgram proof-producing checker. Calling the Lean
side an “executable graph compiler” is therefore misleading.

- The language descriptions disagree in small but semantically meaningful ways. For example, Lean payoffs may omit a
player or contain duplicate entries, which are summed: Vegas/Foundation/Payoff.lean:20. The Kotlin IR instead claims
one payoff expression per strategic role.

- Lean’s Legal obligation quantifies over every visible environment, not just reachable ones: Vegas/Core/
Obligations.lean:281. This is a stronger and potentially more restrictive language boundary than the paper currently
suggests.

## Why the blockchain paper is not close yet

The runtime tower is impressively developed, but it currently establishes adjacent representation and code-generation
facts—not strategic preservation to a public blockchain.

The decisive gaps are:

- BooleanCompilationCorrect is stated but unproved: Vegas/Compile/EVMRefinement.lean:192.
- The EVM semantics is gas-free, partial, and explicitly not validated against Ethereum’s conformance suite: Vegas/
Machine/Contract/EVMExecution.lean:11.

- IdealVisibility explicitly models hiding that public EVM storage does not provide: Vegas/Machine/Contract/
IdealVisibility.lean:12.

- The Lean EVM path does not cryptographically realize sealed commitments; the supported handlers store typed action
values.

- There is no target game including public traces, transaction ordering, inclusion, nonresponse, deadlines, fees, gas,
oracle deviations, or external utility.

- Settlement is currently an outcome readout, not verified movement of assets.
- Kotlin and Lean implement related architectures independently. There is no checked interchange format or translation
validator.

- The Kotlin repository’s README currently claims faithful preservation of strategic properties and on-chain realization
of commit–reveal. Those claims are materially stronger than either artifact establishes.

The long draft’s status ledger is unusually accurate about these gaps: overleaf/Long/sections/a-status-ledger.tex:27. I
would treat it as the authoritative engineering plan and rewrite the short draft to agree with it.

## Artifact and positioning problems

The paper is not currently reproducibly tied to the reviewed code:

- It pins VegasCore commit cb814f3 rather than the reviewed repository revision.
- The draft reports 39 examples and 494 tests: overleaf/sections/07-artifacts.tex:28. The pinned Kotlin repository
currently contains 42 .vg files and emits 499 testcase records.

- overleaf/ is gitignored, so the reviewed paper is not versioned with the theorem surface.

The related-work section also misses the nearest conceptual predecessors. Halpern and Pass already relate mediator
implementation, deviating machines, distribution preservation, and equilibrium preservation in a cryptographic/game-
theoretic framework: Game Theory with Costly Computation. BitML is closer than the current paragraph suggests because it
has a computational-soundness story for compilation to Bitcoin, followed by an Agda verified-compilation development:
BitML, verified BitML compilation. The recent Pseudo-Equilibria paper directly addresses transferring equilibria from
ideal cryptography to real protocols.

Deviation adequacy can still be a good contribution, but its novelty should be claimed as an exact, finite, machine-
checked compiler interface—not as the first connection between deviation simulation and equilibrium preservation.

## Recommended order of work

1. Freeze and name one finite supported fragment.
2. Add a multistage case study with public chance between strategic frontiers and a proved equilibrium or loss guarantee.
3. Relate actual request, disclosure, inclusion, and timeout rules to the modeled public-write or final-veto capabilities;
   the small-model impossibilities and exact refusal criterion do not establish that refinement.
4. Correct the abstract, theorem descriptions, attribution, README claims, and artifact counts once the result is fixed.
5. Either build the Kotlin→Lean translation validator or present the artifacts unequivocally as independent.
6. Keep public-chain strategic adequacy and whole-handler EVM verification separate from the proved serializer result.

The scheduling results include exact atomic implementation, compact-information sufficiency, canonical local policy
back-translation, complete terminal laws, and behavioral Nash equivalence under arbitrary public-data behavioral
schedulers. The blockchain paper still requires a different scale of additional work.
