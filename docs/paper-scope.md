# Paper scope and completion gate

## Subject

Checked strategic compilation of finite imperfect-information event-graph games,
including explicit source disclosure choices, through private bounded request
windows and public serialization. The contribution is the concrete construction
and its mechanization, not the general principle that simulation of deviations
transfers Nash equilibrium.

The runtime construction is the central theorem. A finite optional-disclosure
case study connects an independently specified game and its full policy space
to that construction. The sealed-offer instance binds an offer before public
market information; the owner later opens or quits, and the recipient responds
after disclosure. The checked equilibrium and recipient guarantee account for
arbitrary initial-offer and informed-quitting deviations. This is not a novel
auction mechanism or a scalability experiment.

The source semantic object is `OptionalDisclosure.finiteForm`. Its connection
to the eight-node graph, arbitrary public payoff lists, and concrete request/
serializer instance is checked in `DisclosureCorrespondence`, `DisclosurePayoff`,
and `SealedOfferRuntime`. The case does not claim equivalence with the richer
Kotlin fixture: initial and buyer quitting, its different settlements, and
persistent abandonment remain outside this finite source game.

## Completion criteria

1. Keep the source language and its well-formedness discipline unchanged.
   Follow the [quitting compilation contract](quitting-compilation-contract.md):
   a lower-level optional-copy graph needs a strategic implementation proof,
   not admission as a source `WFProgram` by removing reveal-completeness.
2. Prove the optional-disclosure pattern's full graph-information and policy-law
   correspondence, including administrative marker choices, hidden bindings,
   chance, later source quitting, response, and off-path legal policies.
   Written-order support and selected-view equalities alone do not pass.
   Identify the source semantic object explicitly; a hand-written finite game
   is not automatically the meaning of the corresponding Kotlin program.
3. Instantiate the pattern as the sealed-offer escrow, prove its source
   incentives and adversarial guarantee, and apply the generic runtime theorem.
   The same source program, payoff projection, and unchanged opponents must
   occur throughout the chain.
4. Maintain a focused manuscript: derived information, the two concrete runtime
   constructions, the composed theorem, the application, and precise limits.
   Keep every claimed theorem in the Lean paper audit. Supporting elementary
   obstructions explain premises; they are not independent novelty headlines.
5. Verify warning-free Lean builds and claim/option/axiom audits; reproduce from
   a fresh checkout; record what is and is not executed by supporting Kotlin
   tests. Commit and push the source and separate paper repositories.

Completion means these artifacts and proofs exist, not that they are planned
or the abstract can be phrased conditionally. Stop extending this paper once
these gates pass. Submission formatting and expert evaluation remain author
decisions; likely top-tier acceptance and novelty priority cannot be certified
by the artifact.

## Deliberate exclusions

No public pending-request delivery, censorship-tolerant deadline theorem,
computational commitment realization, transaction fees, consensus/finality,
whole EVM-handler simulation, or general Kotlin-to-Lean correctness claim.
No rich frontend syntax is added to the minimal core. The Kotlin fixture is
supporting implementation evidence unless a checked correspondence is supplied.

The [ledger expansion plan](ledger-expansion-plan.md) remains the later path
to public-interaction compilation and a realistic blockchain realization.
Its larger two-client, quantitative, public-delivery milestone is a separate
research target, not the stopping condition for this manuscript. The reusable
runtime interfaces stay decoupled from source syntax; package extraction follows
an actual second client rather than speculative abstractions.

The [submission assessment](submission-assessment.md) and
[pinned comparisons](research-comparisons.md) constrain positioning. Established
computational game representation and BitML already address strategic
implementation. A reviewer may judge the exact, idealized Vegas construction
insufficiently novel; another elementary quit calculation would not answer that
objection. The paper must make the actual construction and restrictions easy to
inspect.
