# Public delivery, deadlines, and strategic compilation

Status: public-delivery model design under the
[compilation architecture](compilation-design.md). No proposed theorem here
is a claim about the existing implementation. The proved boundary remains
[runtime-models.md](runtime-models.md). The execution plan and acceptance gates
are in [ledger-expansion-plan.md](ledger-expansion-plan.md).

The language/compiler boundary is fixed in
[compiler-boundary.md](compiler-boundary.md): Kotlin owns the rich frontend,
VegasCore remains a minimal semantic target. The strategic relation between
explicit quitting and failed submissions/openings must be proved before
certifying their abstraction by an optional value. Runtime expansion does not
authorize surface-language growth in the core.

## 1. Research objective

Extend strategic compilation from resolved private windows to protocols whose
requests, delivery, and deadlines are observable runtime events. Establish a
useful positive compiler theorem, identify its necessary implementation
conditions, and make the remaining route to an actual blockchain explicit.

The intended contribution is a concrete, mechanized implementation discipline
and compiler, not another definition implying Nash preservation. Neither a
new ledger record nor an elementary censorship counterexample is sufficient.
The work must explain which source control and information a realistic runtime
can preserve, and exercise that explanation on a substantive application.

Three different claims must remain separate:

1. **Representation correctness:** a runtime implements a specified,
   runtime-aware protocol, including its exposure, failure, and cost events.
2. **Strategic abstraction:** a checked subclass of those protocols implements
   a simpler source game without introducing profitable deviations or changing
   the outcomes of compiled play.
3. **Blockchain realization:** an actual network/consensus/execution system
   realizes the runtime interface under explicit resource and trust assumptions.

The expansion targets the first two. Its interfaces must make the third a
well-posed composition task, not an assertion that a ledger is trustworthy.

## 2. Semantic commitments

### Preserve control, not just outcomes

Voluntary quitting, delivery failure, invalid-input rejection, execution
reversion, and unresolved execution are distinct causal events. A public
settlement may not reveal which caused nonresponse, but the semantic model
must retain who controlled it. Never give the contract a fictional ability to
distinguish withholding from censorship.

A source action to quit does not authorize the scheduler to replace a player's
valid submission by that action. A theorem can justify erasing the distinction
only when the claimed laws and incentives really are preserved. Otherwise the
environmental influence must remain in the source semantics, or the simpler
compilation must be rejected.

### All available observations, at their actual recipients

Requests carry sender, phase, nonce/identifier, payload or commitment handle,
size, and relevant fee/timing metadata. Logs and receipts are observations.
The scheduler may inspect everything exposed to it, including pending public
requests. Private routes, if modeled, must be explicit channels.

A public mempool is not automatically one globally shared instantaneous view.
Keep recipient-indexed delivered views and local receipt histories. A globally
visible buffer may be a named first instance, not a silently faithful model of
gossip. Increasing one agent's information or declaring common knowledge is
not assumed to preserve equilibria monotonically. Ordinary local signal
histories can express selective delivery; no new epistemic logic is required
merely to represent agents receiving different messages.

### Scheduler behavior is not an equilibrium requirement

Network relays, block builders, clock progression, oracle services, and other
environment roles have explicit policy ports. Their policies can be adversarial
within the chosen model. Nash and loss bounds concern the actual game players.

Initially, game players and environment authorities are disjoint. This is an
explicit scope restriction. Eventually a principal may control both a game role
and a validator/builder role; then a unilateral deviation must include both
capabilities. Do not exclude such deviations by assigning their second role to
a fixed environment coordinate. Resource/trust bounds must hold for the combined
adversary, not separately for two supposedly independent roles.

### Bounded inclusion is a capability, not consensus folklore

Separate dissemination, transaction inclusion, confirmation, and finality.
State bounds with units and preconditions: connectivity, sufficient fee/funding,
admission, persistent validity, capacity, and competing traffic. Inclusion of an
invalidated nonce conflict is not guaranteed. Fairness without a quantitative
bound does not imply inclusion before a finite deadline.

The unrestricted ledger may censor, stall, or revert. A bounded-service instance
restricts those behaviors openly. A positive theorem for that instance is
conditional until a blockchain adapter proves the service assumptions.
Under partial synchrony, a fixed inclusion deadline cannot be justified before
the relevant stabilization/connectivity assumptions hold. State whether a bound
is conditional on that regime or includes its failure probability. Also prove
that the service class remains feasible under the unilateral deviations being
quantified over: an assumption about unopposed honest traffic cannot be reused
under adversarial congestion without a resource or capacity argument.

## 3. Ownership and reuse

The [compilation design](compilation-design.md#6-ownership-and-dependencies)
owns the dependency boundaries. This document specifies the concrete
public-delivery model and its proof obligations, not another compiler
architecture or a list of packages to create in advance.

Generic game-form backtranslation, deviation comparisons, preference
transport, and composition belong in GameTheory, subject to its existing
architecture and APIs. Concrete message-pool, ledger, and service semantics
belong in reusable runtime libraries. Their game adapters reuse the same
execution laws. Vegas owns its native core/graph semantics, compiler passes,
and their instantiations; the rich Kotlin frontend remains separate.

Application state is a parameter of the ledger. Auction phases, escrow rules,
and timeout settlement belong to an application protocol, not the generic
ledger transition. The ledger supplies calls, clocks, receipts, and a driver
interface; application code decides what a resolution call means. Ideal
commitment/authentication state is a composed service, not a universal ledger
field. The state inventory below describes that composed instance.

Extract the exercised dependency slice rather than copying definitions or
moving the entire EVM backend at once. Establish independent reuse with a
non-Vegas client. Game-free model modules may use the probability-only
GameTheory root; strategic adapters use its game/protocol interfaces.
Physical library targets follow working clients and enforce these import
boundaries. Creating separate remote repositories is a release decision,
not a prerequisite for model design.

## 4. Small executable ledger model

The first instance is a finite-horizon, bounded-resource ledger with final
append-only blocks, ideal authentication, and explicitly ideal commitments.
It models public interaction, not computational cryptography or consensus.

State contains:

- contract/application state and escrow balances;
- protocol phase and its opening, submission-cutoff, and resolution times;
- submitted requests, recipient-local delivered views, and inclusion status;
- accepted transactions and ordered receipts, including failures;
- commitment handles and access-controlled ideal functionality state;
- environment time and block time as distinct fields when they differ;
- remaining explicitly modeled resources and an unresolved/settled status.

Use one event transition relation/kernel with separate local observations.
Expose these event kinds without inventing a second evaluator:

| Event | Controller and effect |
| --- | --- |
| Submit / wait | player controller; records a raw attempt or deliberately does nothing |
| Deliver / withhold delivery | network environment; updates specified recipients' views |
| Propose / include | ledger environment; selects an ordered admissible transaction batch |
| Execute | deterministic contract transition, or explicitly parameterized service law; emits success/revert receipt |
| Advance time | clock/service process; not a player's request-slot counter |
| Resolve timeout | an authorized transaction or explicitly modeled driver, enabled by the contract's clock predicate |
| Settle | executes the source-specified outcome and records actual transfers |

Raw invalid inputs remain legal actions of adversarial controllers; validation
is execution, not deletion from their strategy space. Duplicate, replayed,
conflicting, late, and malformed requests have defined behavior. A transaction
that reverts may still consume fees and produce a receipt. A timeout is not
autonomous EVM execution: permissionless resolution still needs someone to
submit it and the chain to include it. Keeper availability and funding are
separate from the game players' rationality.

State-indexed well-formed commands may select these raw events, but must not
encode successful delivery or source-valid payloads as prerequisites for a
player to act. Waiting is an available action, not an absent mandatory move.

Finite alphabets, message-length/resource bounds, and a finite event horizon
are explicit parameters of the first model. Block capacity alone does not bound
all off-chain submissions. Prove any finite-site strategy coverage used for
behavioral/mixed conversion; do not inherit it from bounded protocol depth
with an unbounded request alphabet.

At the horizon, retain `Pending` with its state and accumulated costs rather
than converting it into a source abort. Prefix safety and settlement probability
can be stated without a terminal utility for pending runs. Expected terminal
utility requires a termination theorem, or an explicit source-agreed utility
for unresolved runs. Eventual infinite execution needs a later path-law layer.

## 5. Source discipline and the first compiler

Use a **phase protocol** above the ledger only as needed by a concrete compiler
output: finite menus, declared observations, nonparticipation outcomes, and
resolution checkpoints. It is not a new rich source language. Kotlin lowers
its existing language to the minimal core; core-to-protocol compilation must
justify the target structure and its strategic relation to that core game.
A protocol's game interpretation belongs to its runtime adapter and derives
existing GameTheory game forms from the native execution, not another
evaluator. Freeze its representation only after the concrete compiler slice
in the implementation plan exercises it.

The semantic comparison must distinguish, without necessarily adding syntax:

1. selecting and binding a value;
2. disclosing an already bound value, including the source-defined option not
   to disclose and its consequences;
3. environmental delivery failure, if this influence cannot be abstracted away;
4. validation failure and its specified settlement;
5. public chance, available only at the source-prescribed checkpoint.

An ordinary optional choice is a candidate abstraction of disclosure-or-quitting:
`some v` must match the earlier binding; `none` denotes quit consequences.
Public quitting, opaque malformed commitments, and cryptographic/application
opening failures are not identified until a strategic comparison justifies
their different observation times, signaling opportunities, and retry rights.
General handlers remain frontend constructs. Checked-source admission requires
an inspectable `CommitmentAccounting` plan: each sealed name has a literal
reveal or a certified conditional-publication site. Weaker graph construction
alone is not source acceptance.
The [quitting compilation contract](quitting-compilation-contract.md) separates
source obligations from representation and runtime proof obligations.
Binding, information, and quit persistence are proof obligations of the
encoding, not consequences of using an option type. The detailed representation comparison
is in [compiler-boundary.md](compiler-boundary.md).

Environmental failure need not be added to the minimal core. If it cannot be
abstracted away for that core game, reject the target/fragment combination or
state a different conditional/approximate result. A generic runtime-aware game
can describe the failure for analysis without becoming a new VegasCore syntax
or being passed off as preservation of the original source.

The first positive candidate uses fixed public epochs and information barriers:

- honest compiled submissions use a fixed, source-information-compatible
  schedule and encoding shape;
- all simultaneous selections become irrevocable, or resolve to the specified
  nonparticipation branch, before outcome-relevant openings become observable;
- reveal-time quitting is analyzed using the complete actual observation, not
  merely the signal convenient for a payoff calculation;
- resolution has enough dissemination, inclusion, and finality margin for
  timely, persistently valid compiled requests;
- admitted ordering effects on the abstract transition are proved to commute
  or are serialized by a checked source-preserving discipline;
- malformed requests and public metadata cannot alter other players' compiled
  behavior or service guarantees in unmodeled ways;
- utilities include modeled costs, or the theorem is explicitly a zero-cost
  instance or carries a quantitative cost error.

These are proof obligations to discharge for a concrete compiler, not fields
named `preservesNash` in a supposed executable type checker. Start with a
conservative syntactic/checkable fragment. A checker may report a failed
condition or a residual external obligation. It must not add penalties,
zero-knowledge proofs, privacy, or fairness silently to make a program pass.

### Hidden guards are a separate implementation issue

The current source may filter a sealed choice using information unavailable to
an on-chain validator. An ordinary commitment does not prove that its hidden
payload satisfies that guard. Choose and expose one of:

- a first fragment whose commitment admission is structural and whose relevant
  validation is public at the declared stage;
- deferred validation with source-specified invalid-opening outcomes;
- a named proof-of-validity functionality, later requiring cryptographic
  realization and witness availability.

The first compiler should use the first two, not acquire a general ZK assumption
by accident. Some current `WFProgram`s will therefore not qualify. Well-formed
source menus alone are not a proof of public implementability.

### Last-moment submissions are a decisive test

Bounded inclusion guarantees timely honest submissions, but does not remove
an adversary's ability to submit near a cutoff. Inclusion then may depend on
the scheduler. Nor does a commitment hide its existence, sender, timing,
length, or arbitrary extra traffic from a deviating player.

Do not assert that fixed epochs solve these issues. The candidate proof must
show that each late/metadata-aware deviation induces only a source-admissible
mixture using the same information. If not, narrow the accepted core fragment
or state the different runtime-aware game theorem without claiming it preserves
the original core game.
Never discard the deviation or assume the scheduler ignores its signal.

## 6. Target theorem statements and quantifiers

Use `K_S(e, sigma)` and `K_T(eta, rho)` for play laws with source and target
environment policies. `C` compiles player strategies and `d` decodes the
outcome relevant to the claim. Notation below specifies targets, not proved
Lean declarations.

### T1. Environment-respecting strategic implementation

The preferred strong shape is:

```text
for every admissible target environment eta,
  there is an admissible source environment e, fixed independently of sigma,
  such that for every source profile sigma:
    d_* K_T(eta, C sigma) = K_S(e, sigma),
    and for every player i and target replacement tau_i,
      there is a finite law nu over source replacements satisfying
        d_* K_T(eta, (C sigma)[i := tau_i])
          = bind nu (s_i => K_S(e, sigma[i := s_i])).
```

All source opponents and the selected source environment remain unchanged in
the second equation. The mixture may be profile-local; a uniform translator
is a stronger result only if constructed. For a source without environmental
influence, `e` must be proved inert, not chosen to repair the equation.

First prove T1 for the concrete phase/ledger construction, with one checked
core consumer already identified. Then prove its connection to the simpler
graph game for the compatible core fragment. The intermediate protocol must
not become a substitute rich language that leaves that connection optional.
The environmental correspondence must come from causal local semantics; a
post hoc simulator that sees future randomness or the opponents' private
policies is not an admissible implementation.

A general UC-style simulator can have different quantifiers and interfaces.
Its existence does not automatically supply this same-environment,
opponent-preserving statement. If the strong shape fails, record the exact
weaker property and which Nash/loss statement it actually supports. Do not
silently replace fixed-environment Nash by a worst-case-over-environments
solution concept. The initial goal remains ordinary player Nash for each
admissible environment, with no environment optimality requirement.

### T2. Quantitative implementation

Bound errors on the unconditional law of compiled play and of every admitted
unilateral deviation. If utility has oscillation at most `R_i`, terminal-law
total variation at most `delta`, and expected utility-translation error at
most `kappa_i`, target the per-comparison bound
`eta_i = R_i * delta + kappa_i`. With honest error `eta_h` and deviating error
`eta_d`, source epsilon-Nash should transfer with budget
`epsilon + eta_h + eta_d` (in particular `epsilon + 2 * eta_i` for a common
bound). Reflection at compiled profiles also needs the compiled-source
deviation direction. Prove the constants, do not advertise them from this plan.

Compose per-layer errors with a coupling/hybrid argument. A union bound does
not require independent failure events, but each failure guarantee must apply
uniformly to the adaptive behaviors allowed at that layer. Do not condition on
successful delivery/finality and call the resulting law the original game.
For example, an adversary may make failure depend on a privately known loss.

Computational indistinguishability is not total variation. The later crypto
bridge must use efficiently representable bounded utilities, efficient player
controllers, an explicit security parameter, and the appropriate computational
comparison, or change the claimed solution concept explicitly. Exact finite
equilibrium against unbounded strategies is not a real-cryptography theorem.

### T3. Core eligibility and concrete instantiation

An executable checker consumes only the supported core representation, not
Kotlin handler syntax. Core acceptance establishes well-formedness; a separate
runtime eligibility check constructs the protocol, action/observation maps,
barrier and validation evidence, and residual ledger requirements. Its
soundness theorem supplies the compiler's structural premises. A ledger
realization supplies environmental assumptions. Neither check proves Kotlin
lowering correct. Runtime controllers remain larger than compiled policies.

A language-independent protocol client and a compiled Vegas application must
use the same T1/T2 proof modules. Without both, extraction has not demonstrated
reuse and the theorem may only be a disguised Vegas-specific interface.

### Negative results: necessary conditions, not claimed completeness

- **Control obstruction:** if an admitted environment can force a distinct
  timeout settlement despite the compiled authorized submission, and the
  source assigns that choice exclusively to the player, the required honest
  law fails. State the target settlement/authorization premises so this really
  rules out the intended implementation class, not arbitrary decoders.
- **Information obstruction:** if another player's choice remains free after
  a payoff-relevant hidden value becomes visible, exhibit the failure of the
  claimed all-game preservation. Reuse existing witnesses where possible;
  their elementary mathematics is not the expansion's novelty.
- **Progress obstruction:** if an environment may stall forever, unconditional
  preservation of a terminating source cannot follow. A finite-horizon test
  proves unresolved prefixes, not an infinite nontermination theorem.
- **Cost obstruction:** if a deviation changes fees or capital exposure absent
  from source utility, exact transfer needs cancellation or a new source cost
  semantics. Fixed honest gas charges alone do not justify cancellation.

Each negative result should correspond to a positive construction hypothesis
and a compiler diagnostic. This yields a useful boundary map. A necessary and
sufficient classification for all games or blockchains is not promised.

## 7. Route to a realistic complete blockchain model

The long-term concrete target is an EVM chain with Ethereum proof-of-stake
network/consensus semantics. Pin an explicitly named fork and specification
revisions at the integration gate; do not prove against a moving label such as
"current Ethereum". Earlier models remain reusable for other chains.

```text
written Vegas source (rich frontend owns its semantics and lowering)
  -> checked minimal core artifact -> canonical strategic game
  -> compiler-produced protocol with justified information/control correspondence
  -> public transaction protocol + ideal commitment/authentication services
  -> executable contract calls with costs, failures, and settlement
  -> linked bytecode in a named EVM transaction semantics
  -> blocks, network delivery, local chain views, fork choice, finality
  -> concrete cryptographic and consensus realization assumptions
```

These arrows are a dependency diagram, not one homogeneous simulation. Some
are operational refinements, some strategic back-translations, some statistical
couplings, and some computational realization reductions. Each needs an
explicit adapter before they can be composed.

| Boundary | Required work and evidence |
| --- | --- |
| Written source to minimal core | Lower existing constructs, including optional disclosure and handler consequences, into core values/control; retain explicit trust in Kotlin until source-to-core strategic correspondence is proved or validated |
| Core import and frontend validation | Check emitted core without handler syntax; reduce frontend trust pass by pass in separate integration tooling, not a rich-language extension of VegasCore |
| Core to runtime protocol | Prove the concrete encoding and target eligibility conditions preserve the original core game's control and information; do not substitute a richer game silently |
| Protocol to contract | Concrete admission, nonce replay protection, authentication, escrow, settlement, and keeper-triggered resolution; correct behavior for hostile inputs |
| Contract to EVM | Close whole generated-handler and linking simulation; gas, exceptional halts, revert effects, balances, logs, external calls/reentrancy where allowed; existing Boolean component lemmas are inputs, not the finished proof |
| VM to ledger | Transaction preconditions, fee/nonce accounting, block validity, ordering and timestamp constraints, receipts, persistent validity under interference |
| Ledger to distributed chain | Recipient-local tentative/final views, gossip/partitions, forks, reorgs, proposer/builder power, actual inclusion/finality guarantees and their failure bounds |
| Ideal commitments to cryptography | Hiding, binding, domain/session separation, malicious commitments/openings, validity proofs if used, computational strategy bounds; evaluate signatures and entropy/oracle assumptions separately |
| Costs to game utilities | Actual transfers, gas, slashing, opportunity/capital costs when relevant; private valuations and external utility remain explicit application inputs |
| Infinite service lifetime | Finite-prefix consistency, path measures/termination tails, stopping and utility integrability; no global bounded-horizon axiom for an operating chain |
| Principals and corruption | Combined game/network/validator control, static versus adaptive corruption, honest-resource/connectivity assumptions valid under the admitted deviations |

Reorgs undo state, not knowledge. Observers remember a revealed secret even if
the transaction disappears from the canonical chain. A chain adapter must
relate retained local observation histories as well as finalized ledger states.
This is a mandatory adversarial test for any finality abstraction.

No semantics can capture every economically relevant external fact by default.
"Complete" means a closed composition for a named protocol version, environment,
adversary/resource class, observation surface, and utility model, with every
remaining assumption listed. A model-complete proof, a protocol-realization
proof under cryptographic assumptions, and verification of actual client
binaries are distinct deliverables. Unproved external theorems may be cited as
conditional assumptions, never described as checked Lean dependencies.

## 8. Prior work informing the design

- [Bitcoin as a Transaction Ledger: A Composable Treatment](https://crypto.ethz.ch/publications/BMTZ17.html)
  is a direct reference for making ledger capabilities realizable rather than
  postulating an overly strong service. Its author page explicitly distinguishes
  its weaker realizable functionality from a stronger proposal.
- [Ouroboros Genesis](https://crypto.ethz.ch/publications/files/BGKRZ18.pdf),
  Section 2.2, separates transaction validation, adversarial extension policy,
  clock behavior, local ledger views, and conditional liveness. These boundaries
  motivate our capability split; no formal equivalence with that functionality
  is claimed.
- [Ethereum execution specifications](https://github.com/ethereum/execution-specs)
  and [consensus specifications](https://github.com/ethereum/consensus-specs)
  are distinct integration references. Executable specifications and test
  vectors are not themselves refinement proofs for this artifact.
- [Computational extensive-form games](https://arxiv.org/abs/1506.03030),
  [timeability](https://arxiv.org/abs/1502.03430), and
  [BitML](https://eprint.iacr.org/2018/122) remain the principal strategic,
  information, and contract-compilation comparisons. The expansion must be
  evaluated against them at theorem level, not just advertise another runtime.

The contribution hypothesis is a checked compiler discipline connecting
source information/control to public delivery and deadline semantics, with
reusable operational theory and quantified implementation error. Its novelty
is a research question to test at the gates below, not established by this design.
