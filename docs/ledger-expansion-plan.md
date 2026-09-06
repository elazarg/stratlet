# Ledger expansion: implementation and research gates

Status: planned, not implemented. This is the execution plan for
[ledger-expansion-design.md](ledger-expansion-design.md). Existing proof status
is recorded separately in [runtime-models.md](runtime-models.md).

## Scope of the next paper-sized result

Aim for a checked public-delivery compiler for a conservative finite phase
fragment, with explicit source quitting, environment capabilities, and
information barriers; quantify outcome/incentive errors where execution can
fail; demonstrate reuse outside Vegas and one substantive Vegas application.

Do not make the next result contingent on formalizing all Ethereum consensus,
all EVM instructions, computational cryptography, infinite executions, and
the Kotlin parser. Those are distinct later proof obligations, but the new
interfaces must leave room for them. Equally, do not label the next model a
complete blockchain or the resulting paper an end-to-end deployment theorem.

There is no sound calendar estimate before the first semantic tests. Proceed
by the bounded gates below. At each gate, record the exact statements, admitted
behavior, dependencies, evidence, failed conjectures, and next decision. A
failed conjecture is useful evidence; a placeholder proof is not completion.

## P0. Falsify the candidate discipline before building a framework

**Deliverables:** small executable finite instances, checked distinguishing
laws/counterexamples, and a decision about the first positive source fragment.
Use the current canonical execution/information machinery for the experiments;
do not introduce a universal ledger/game hierarchy first.

Test these event sequences with explicit local observations:

| Test | Required question |
| --- | --- |
| Timely valid request censored until expiry | Does an environment-controlled outcome have a source-controlled counterpart? |
| Last-slot submission | Can acceptance depend on an adversarial order after the deviator learns something source-invisible? |
| Public malformed traffic | Can an arbitrary payload, length, or retry pattern influence the scheduler and another player's outcome? |
| Early and late commitments with hidden values | Is the visible footprint simulable from the source information, even if values are hidden? |
| One reveal observed before another opening decision | Does the full source include the actual informed quitting decision? |
| Hidden invalid commitment | Where is the guard checked, and which source branch accounts for failure? |
| Timeout enabled with no resolution caller | Does the contract actually settle, or merely permit someone to settle it? |
| Zero-payout deviation saving fees | Is a source indifference turned into a profitable target deviation? |
| Reverted or orphaned reveal | Does the observer retain information after state rollback? |
| Distinct recipient mempools | Was global common knowledge inadvertently substituted for local delivery? |

The reorg test can be a small standalone model; it is not a claim that the
initial final-ledger compiler already handles forks. Likewise, a finite stalled
prefix is not a proof of infinite nontermination.

**Positive baseline:** manually specify a source phase game and public-delivery
instance with one hidden selection phase and an explicit disclosure/quit
phase. Use a nonzero delay bound, at least two inclusion orders, a malformed
request, and a genuinely later informed decision. Trace examples alone are
insufficient: prove an all-policy or unilateral-law statement for this slice.

**Gate:** choose one of three outcomes, supported by the tests:

- The simpler source abstraction survives; proceed to its general compiler.
- It survives only with extra source-visible control/information; specify that
  source construct and revise the target theorem before proceeding.
- The proposed discipline offers no meaningful abstraction over direct ledger
  play; stop and reassess the contribution. Do not hide the failed premise in
  an interface or continue adding infrastructure to defend it.

The preferred hypothesis is fixed epochs plus barriers and bounded service.
It is not assumed true until this gate passes.

## P1. Establish reusable ownership with two actual clients

**Depends on:** a passing P0 slice.

Introduce only the runtime targets required by that slice, following the import
graph in the design. Extract the exercised generic operational and request
proofs from Vegas, updating all consumers and audits without compatibility
wrappers. Reuse GameTheory probability and protocol machinery. Leave graph
compilation and source syntax in Vegas.

The second client is a directly defined, non-Vegas timed escrow/release
protocol with two parties, explicit nonresponse settlement, and competing
requests. It imports the generic runtime/ledger/game adapters but no `Vegas`
module. At least one operational invariant and one strategic comparison must
be proved through the same modules used by Vegas. A second namespace that
imports the Vegas compiler does not count as a second client.

Add automated import checks for:

- no `Vegas` imports in generic packages;
- no game/utility/solution-concept imports in operational ledger targets;
- no chain-specific imports in generic strategic translation;
- no reverse imports into GameTheory from its consumers;
- no placeholders/custom axioms in the claimed proof dependency closure.

Use separate Lake targets in this repository first. A standalone package/repo
release follows only after the API works for both clients. Do not create new
remote repositories or revise GameTheory's architectural decisions implicitly.

**Gate:** both clients build independently, existing paper claims still compile,
and the generic API does not mention event-graph fields or Vegas handlers.

## P2. Public ledger semantics and capability laws

**Depends on:** P0 and the minimal ownership split from P1.

Implement raw submissions, recipient-local delivery, ordered inclusion,
execution receipts, clocks, and explicit timeout-driving transactions. Fix
whether endpoint equality includes costs, pending state, or finalized state
for each theorem. Define ideal commitment/authentication services by actual
transition and observation rules, not by exposing a plaintext value to every
runtime policy and asking them to ignore it.

Prove:

1. local observations come from the canonical event history;
2. validation/replay/nonce rules preserve the ledger/application invariant;
3. balance/escrow accounting for success, rejection, and resolution;
4. finite-prefix execution and explicit unsettled states;
5. precise service lemmas for admitted, persistently valid, timely requests;
6. which deadline margins imply inclusion/resolution, with units and boundary
   convention (strictly before versus at the cutoff) stated explicitly.

Implement an unrestricted instance and a named bounded-service instance over
the same operational semantics. The latter must admit multiple delivery delays
and inclusion orders. Avoid a proof that reduces every scheduler to the one
honest schedule.

**Gate:** all P0 bad behaviors are either admitted and have the expected effect,
or excluded by a visible capability with an independent rationale. In
particular, no implicit keeper, hidden mempool, free execution, or forced
participation can appear in the target theorem.

## P3. General strategic comparison for the concrete phase construction

**Depends on:** P2 and the phase source selected at P0.

Construct information-local source replacements for arbitrary runtime
controllers, not just the compiler image. Prove T1 from the design, first for
deterministic policies and then for the chosen finite randomization class.
If a behavioral result uses finite-site coverage, derive coverage over every
admitted counterfactual, not just the honest execution tree.

Required intermediate lemmas:

- phase projection and receipt/settlement correspondence;
- irrevocability before the next information exposure;
- reconstruction of controller memory and public transcript effects;
- scheduler replay that respects its full admitted information;
- unchanged opponents and a common causal source environment;
- honest and unilateral-law statements using the same outcome decoder;
- source replacements remain implementable for equilibrium reflection.

The source-environment policy must not be picked afresh to explain each
deviation. Check the quantifier order in the actual theorem. If the simulator
can only match a source game with a different environmental response, report
that different theorem and its consequences; do not claim the intended Nash
result from it.

Derive the source-player Nash consequence and an adversarial expected-loss
corollary for a designated honest player. The latter requires no equilibrium
or rationality premise for the attacker. Coalition results are separate.

**Gate:** a concrete constructor discharges T1 for a nontrivial family of phase
protocols. A record whose input fields are the two desired laws does not pass.

## P4. Checked Vegas fragment and an application

**Depends on:** P3. The source syntax/interface work can begin after P0 settles
the semantics, but the application theorem depends on the general comparison.

Add explicit source constructs for the phase behavior actually needed: binding,
disclosure, quitting, validation failure, and environmental failure when it
cannot be abstracted away. Specify what later actions remain possible after
each nonresponse branch. Keep these semantics independent of whether the
programmer's incentives favor completion.

Implement a conservative executable checker producing a phase protocol and
the compiler-specific structural proofs. List ledger capabilities separately
as application obligations. Prove the relation from source choices and full
information to the constructed protocol. Do not substitute terminal support
reconstruction for a quantitative/strategic frontend theorem.

The preferred flagship application is a finite sealed-bid second-price auction
with at least three bidders, a specified tie rule, private finite valuations,
explicit reveal/nonresponse/invalid-bid settlements, and declared costs.
Start by checking whether the intended bidding profile is actually an
equilibrium of the **full** source game; do not assume the textbook auction
claim survives the added branches. If truthful completion is false, retain the
counterexample and analyze the correct incentives. A finite escrow is the
fallback only if the auction requires unrelated economic machinery.

Required evidence:

- source theorem about an actual complete strategy profile or a quantified
  honest-player loss bound;
- application of the general public-delivery compiler theorem;
- a changed runtime assumption or source handler that demonstrably changes
  the result;
- at least one analysis conclusion that is not merely the old fair-bit
  equilibrium transported through another wrapper.

**Gate:** the compiler is generic over the checked fragment and the application
uses it. A manually inserted application-only checkpoint is not the general
source elaboration theorem.

## P5. Failure probabilities and cost error

**Depends on:** P3; generic probability lemmas can be developed once their
concrete consumers are known. This is the bridge to realistic, non-perfect
service rather than a claim that real cryptography has finite total variation.

Prove unconditional finite-law coupling/error composition, then the precise
expected-utility and approximate-Nash budget in T2. Instantiate at least one
nonzero service-failure or cost-error bound in the ledger client. Include a
test where failure depends on a player's information to reject conditioning
away the bad runs. Include a test showing why a failure bound proved only
against honest play cannot justify a deviation theorem.

An unbounded cost/utility model is not covered by a bounded-error corollary.
Where an exact cost-aware theorem is tractable, prefer it; otherwise expose
the bound and its resource assumptions. Show how the errors of successive
interfaces add, without an unjustified independence assumption.

**Gate:** the bound reaches the application theorem, not just a standalone
total-variation lemma. Exact `delta = 0` specializes to the earlier comparison.

## P6. Research and release decision

**Depends on:** P1--P5 for the intended expanded result.

Compare the actual delivered theorem and construction with BitML,
computational game representation, timeability, concurrent refinement, and
composable ledger functionalities. Determine whether the new theorem handles
public interaction in a substantively different way or is only a formalized
instance of an existing construction. Update the research assessment honestly.

The paper should tell one story: source control and information, the public
implementation discipline, the concrete proof, and its boundary. Supporting
obstructions explain hypotheses rather than accumulate into a catalogue of
"impossibility" headlines. Explain GameTheory as a dependency, and document
the independently reusable runtime artifact without turning the paper into its
full API manual.

Before release, run warning-free full builds, all import/claim/axiom checks,
fresh-checkout reproduction, and measured application/build experiments if
reporting measurements. Keep the manuscript and `Paper.lean` audit synchronized.
Research plans are not entered into the claim registry as completed theorems.

**Stop/submit criterion:** a nontrivial generic public-interaction compiler,
two genuine clients, one substantive strategic application, an instantiated
quantitative boundary, and a defensible literature comparison. If only the
elementary negative results survive, say that the expansion did not establish
the intended stronger contribution. Do not turn that outcome into an assertion
that the paper is ready.

## Later tracks toward a closed blockchain proof

These tracks have distinct owners and may proceed independently once the
ledger interfaces stabilize. They are not hidden prerequisites for P0.

| Track | First bounded deliverable | Required to call the eventual path closed |
| --- | --- | --- |
| Frontend validation | checker for a finite Kotlin-emitted object including handlers | evidence that the actual source artifact denotes the checked game, with parser/trusted emitter assumptions stated |
| EVM lowering | whole four-handler Boolean simulation at a pinned execution revision | linked handlers and surrounding transaction semantics, including fees/failure/external effects admitted by the fragment |
| Ledger service realization | map one published composable ledger functionality to our capabilities | proved correspondence for observations and admissible adversaries, not similar names for liveness |
| Distributed Ethereum model | pinned fork, block validity, local tentative/final views and a retained-observation reorg test | network, fork choice, finality and inclusion realization under named stake/connectivity assumptions |
| Crypto realization | one named commitment and authentication interface with malicious-input semantics | computational reduction, security parameters, utility/controller restrictions, all admitted public leakage |
| Long-lived execution | compatible finite-prefix laws and one proved termination-tail bound | path laws and justified terminal/discounted utilities without truncation masquerading as termination |
| Multi-role principals | a player that also controls an inclusion authority in a finite test | combined capabilities and corruption/resource budgets respected by the game deviation theorem |

An external paper's theorem may support a conditional realization argument,
but is not a checked Lean theorem until its relevant definitions, assumptions,
and proof or a verified adapter are present. The final artifact should enumerate
each remaining assumption by owner, scope, and theorem consumer.

## Maintenance discipline

- Change source and documentation together; never suppress warnings locally.
- Do not refactor all of GameTheory or EVM code to prepare speculative reuse.
- Keep generic module extraction, new semantics, and substantive proofs in
  reviewable commits. Push both repositories when each is changed.
- Keep the maintained paper in a final-reading style. Until the expansion's
  theorems exist, its roadmap belongs in these design documents, not as an
  expanded abstract or an aspirational theorem in the paper.
