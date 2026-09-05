# VegasCore

VegasCore is a Lean 4 foundation for executable games with partial
information. A checked source program has one semantic compilation, with two
consumers: GameTheory analysis and gradual lowering toward concrete runtimes.

## Architecture

```text
                              ┌─→ ExecutionProtocol + InformationModel
VegasCore source              │        └─→ FOSG / strategic forms / analysis
      │                       │
      └─→ Machine.Program ────┤
          typed EventGraph    │
          + reified node code └─→ System₀ → System₁ → … → backend artifact
                                      small certified lowering passes
```

`Machine.Program` is the first backend-neutral machine IR. It contains:

- typed initial and event storage fields;
- dependency-derived sample, guarded commit, and reveal nodes;
- reified typed expression/distribution code with every variable mapped to a
  graph field;
- normalized rational probability tables retained for runtime lowering, with
  exact `FinDist` denotations for execution and analysis;
- terminal payoff code;
- graph well-formedness and guard-liveness proofs.

The event-graph compilation result also retains its terminal source context,
proof-indexed source-to-field map, and original source payoff expressions.
`Machine.compile_sourcePayoffOfTerminal` proves that every terminal reachable
machine store reconstructs a typed source environment in which source and
machine payoff evaluation agree exactly, including sealed source bindings.
`Machine.compile_sourceStar` strengthens this at support level: the
reconstructed draws, commitments, and reveals form an actual written-order
`SmallStep.Star` from the program's initial source environment to that terminal
environment.

Retaining code is essential. Evaluator closures alone can define semantics but
cannot be traversed by a Solidity, EVM, native, SMT, or circuit backend.

The GameTheory view is derived from this machine program. It is not the final
runtime model, and concrete implementation details are not added to the game in
one jump.

## Gradual lowering

`Machine.System` represents one operational stage. Its commands are indexed by
the state from which they are valid. `Machine.Refinement abstract concrete`
projects concrete states and decodes each concrete command as either:

- one abstract command with exactly the projected stochastic transition; or
- an administrative command whose projection stutters.

Refinements compose. This supports small passes such as adding bookkeeping,
choosing an order, introducing an encoding, or splitting one logical operation
across transactions.

`Machine.AdministrativeLayer` is the first such pass. It attaches arbitrary
machine metadata and permits exact stochastic metadata-only commands. Its
generated refinement proves that semantic steps retain their abstract law,
administrative steps stutter after projection, and terminality is unchanged.
It can also lift an abstract observation by hiding the metadata; using that
lift is a modeling choice, not a proof that a real runtime keeps it secret.

`Machine.Instrumentation` is the adjacent non-stuttering pass: metadata is
updated atomically with every realized semantic successor. It covers target-
neutral completion counters, receipts, and explicit execution-order records.
The supplied `executionLog` is a proof-facing reference instance; a contract
backend can lower its records to stable action ids and completion storage one
representation decision at a time.

`Machine.Contract.Manifest` is the first emitter-facing inventory. It finitely
enumerates typed value slots, per-action completion slots, stable logical
actions, direct dependencies, logical authority, player input types, and the
original reified node code. It is lossless and adds no behavior. Physical
storage, ABI triggering of internal actions, role addresses, entropy,
commitment cryptography, timeouts, settlement, and target arithmetic are later
passes with separate obligations.

`Machine.Contract.Layout` makes the next decision independently: it maps the
logical slots to bounded natural-number keys and requires injectivity. The
canonical layout is proved collision-free and dense, with value slots followed
by completion slots. It does not yet encode a typed language value into a
target storage word.

`Machine.Contract.Request` is the logical ABI envelope: stable node id,
logical authority, and optional typed payload. `Request.accepts` executably
checks bounds, authority/payload shape, readiness, typed reads, and commit
guards, and is proved to accept exactly envelopes represented by currently
valid proof-carrying machine commands. The classical reference decoder has the
same acceptance boundary. Concrete address authentication, calldata/storage
decoding, revert behavior, gas, transaction ordering, and permission to
trigger internal actions remain explicit backend obligations.

`Machine.Contract.StorageCodec` is the target-word boundary. Combined with a
certified layout, it gives typed sparse-storage reads and writes with proved
round trips, distinct-slot noninterference, and separation between graph
values and completion bits. The included reference codec is semantic and
lossless, not a finite serialization. Codecs are indexed by the compiled
program and need only support the types that its fields and nodes actually use;
an unused unbounded type in the source language no longer blocks a finite
target codec. A program that does use the current `simpleExpr` integer type
still contains unbounded Lean `Int`, so exact EVM-word lowering needs a bounded
source integer type, a proved range invariant, or chosen modular/checked-
overflow semantics. GameTheory does not decide that compiler policy.

`Machine.Contract.EVM.boolStorageCodec` is a deliberately narrow first finite
refinement: for a compiled `simpleExpr` program whose graph fields and nodes
are all Boolean, it uses canonical zero/one values in `BitVec 256` words. The
matching-pennies example is configured with this codec even though
`simpleExpr` itself also contains unbounded integers. This is only a storage-
word representation, not an EVM instruction or transaction semantics.

`Machine.Contract.RawStore.encodeSnapshot` bridges finite semantic graph state
to canonical contract storage: optional typed field words followed by explicit
completion bits. Its executable decoder is a proved left inverse, and the
resulting raw-store encoding is injective on reachable machine states. An
arbitrary decoded snapshot is not automatically reachable; preserving that
invariant is an obligation of each lowered runtime transition.

`Machine.Contract.Request.acceptsStore` connects those boundaries: it decodes
canonical raw storage and runs the executable logical request checks over the
resulting snapshot. On storage encoded from a reachable machine state, its
answer is proved identical to semantic command availability. This is still a
logical ABI over typed payloads; concrete calldata decoding and caller
authentication remain later passes.

`Machine.Contract.Request.executeConfig?` is the adjacent logical executor. It
rejects exactly the requests rejected by `acceptsConfig`; on an encoded valid
command, its next-configuration law is exactly `Machine.step` with reachability
proofs erased. `IExpr.evalLaw` and `EventDist.evalLaw` retain an exact
normalized `RationalLaw` table through compilation; the compiler proves table
equality before deriving semantic law equality. `FinDist` remains the
noncomputable PMF-based analysis object. A backend must still realize the
retained rational table using an oracle, VRF, rejection sampler, or other
entropy mechanism and prove that its actual distribution matches the table.
GameTheory supplies the semantic probability object, not that physical
realization policy.

`Machine.Contract.Request.executeStore?` carries the same reference law across
canonical storage: decode the snapshot, execute, and re-encode every successor.
For an encoded reachable state and valid command envelope, the resulting raw-
store law is proved exactly equal to `Machine.step` mapped through
`RawStore.encodeState`. Conversely, every request accepted against such a
store is proved to represent some valid semantic command with that same exact
law, so hostile accepted requests preserve the encoded-reachability invariant.

`Machine.Contract.PlayerRegistry` and `PlayerCall` add caller authentication
as a separate deterministic gate. Registry addresses are injective, and a
stored player call is accepted exactly when its caller owns the claimed player
role and its logical commit request is semantically valid. Internal sample and
reveal triggering is intentionally not assigned to arbitrary callers here;
that requires an explicit oracle/keeper/protocol policy.

`Machine.Contract.PlayerCalldata` is the word-level player ABI: caller,
claimed player, node id, and one target word. Decoding requires the node to be
a commit owned by that player and decodes the word at the guard's language
type. Every valid semantic commit round-trips to the same logical request and
is accepted against its encoded state. Its executor then composes decoding,
caller authentication, stored validation, and stored execution; for every
valid semantic commit, the resulting raw-store law is exactly `Machine.step`
mapped through the canonical state encoding. The law remains semantic and
PMF-based, but the player-commit transition itself is deterministic and needs
no entropy realization. Byte serialization, selectors, and gas remain
target-specific.

`Machine.Contract.InternalCalldata` is the separate internal-action entry
point. A call carries only caller and node, decoding excludes player rows, and
an explicit `TriggerPolicy` controls authorization per caller and node. This
permits, for example, oracle-only sample nodes and permissionless reveal
nodes. Authorized valid triggers have the same exact raw-store step law. This
introduces no automatic scheduler or entropy implementation: a concrete caller
can choose among concurrently enabled nodes, and exposing or controlling that
ordering requires its own information/strategy preservation result.

`Machine.Contract.initialStore` and `terminalOutcome?` close the state-only
contract lifecycle. Deployment is exactly the canonical raw encoding of
`Machine.init`, with every action incomplete. Terminal readout rejects
malformed or unfinished storage; on encoded reachable storage it evaluates
exactly the retained machine payoff, and for compiled source it equals the
payoff of an actual source terminal environment. This yields settlement data,
not asset custody, transfers, or withdrawal semantics.

`Machine.Contract.ConfiguredContract` is the first whole-contract target. It
packages the manifest, canonical layout, word codec, player registry, internal
trigger policy, constructor storage, terminal readout, and a typed sum of both
transaction entry points. Dispatch preserves the exact one-step laws for
player commits and internal events. It is deliberately not called an EVM
artifact: byte selectors, serialization, expression lowering, arithmetic,
gas/reverts, and entropy realization remain explicit subsequent passes.

`Machine.Contract.WireCodec` adds serialization as its own certified pass. It
maps the configured typed transaction sum to an arbitrary wire carrier, may
reject malformed inputs, and must round-trip every encoded call. Wire
validation and execution have the same success boundary, while encoded player
and internal calls retain their exact machine-step laws. More strongly, every
arbitrary wire input accepted over reachable encoded storage is reconstructed
as some valid semantic command, so its complete successor law remains inside
the canonical reachable-state image. The included identity codec is
proof-facing only; an EVM backend must supply concrete selector, address, and
word encodings.

`Machine.Contract.Blockchain.StochasticContract` then separates caller-free
message data from blockchain-supplied call context. The configured adapter uses
only `sender`; height, slot, origin, contract address, balances, and transferred
amount are semantically inert until dedicated timing, payment, or entropy
passes consume them. Successful calls carry an exact law over successor state
and an ordered outbound-action trace, matching the essential shape of
ConCert-style receive semantics; the current Vegas adapter proves that trace is
empty. This boundary intentionally remains stochastic. A deterministic
`receive` function can only be produced after chance is refined to an oracle or
chain entropy protocol. ConCertLean's current Lean/toolchain revision also
differs from this project's, so it is a grounding interface rather than a
direct package dependency today.

Blockchain-facing receive results distinguish successful stochastic execution
from reversion. Selector/arity/word decoding failures are `malformed`; decoded
calls that fail authentication or game validation are `rejected`. This is not
yet a gas or rollback semantics, but failure is no longer represented as an
unclassified missing value.

`Machine.Contract.Blockchain.EntropyRealization` states the next required
certificate without selecting an entropy mechanism: deterministic receive plus
an assumed finite entropy law must push forward to exactly the stochastic
contract result law. The included semantic realization is proof-facing only.
For a real chain, unpredictability, bias resistance, liveness, and the claimed
seed distribution remain assumptions to discharge. In particular, one uniform
256-bit seed cannot exactly realize every rational table unless its masses have
compatible denominators; rejection or a richer protocol may be necessary.

`Machine.Contract.Blockchain.UniformEntropyRealization` specializes that
obligation to one fixed positive finite seed cardinality with a uniform law.
It records exact pushforward equality and separately exposes whether the seed
cardinality divides the 256-bit word space. There is intentionally no generic
constructor from `RationalLaw`: GameTheory provides uniform finite laws and
pushforward algebra, but not a constructive denominator-clearing partition for
arbitrary exact rational tables. That sampler, plus unpredictability and
bias-resistance assumptions, is still required.

`Machine.Contract.OraclePolicy` and `OracleCalldata` provide the classical
trusted-oracle alternative. Every evaluated `RationalLaw` exposes its exact
law on retained table indices. An authenticated oracle callback carries one
such index, and contract execution deterministically reads the corresponding
value and updates canonical storage. Fixing the oracle's behavioral policy to
the index law is proved to induce exactly the original `Machine.step` law,
both on graph configurations and encoded storage. The contract cannot verify
a frequency claim from a single response; exact sampling, non-withholding, and
unpredictability are assumptions of this trusted role. An asynchronous
`OracleProtocol` then splits sampling into a deterministic request and
callback: the request changes only pending metadata and emits one ordered
oracle action, while the matching callback clears the lock and performs the
sample update. Under the fixed oracle policy the callback law is exactly the
encoded `Machine.step` law. Calls are locked during the pending phase; fairness,
response timing, and visibility of the pending signal remain explicit
classical-runtime assumptions rather than secure-compilation conclusions.

`Machine.Contract.ClassicalContract` completes the deterministic typed
contract surface. Player commitments and reveals use direct deterministic
executors, samples use the locked request/callback protocol, reverts retain the
existing atomic rollback semantics, and terminal readout still reconstructs an
actual source payoff. `ClassicalCompiler.Backend` is the checked-source assembly
point: given storage, identities, trigger policies, and a trusted oracle, it
produces this deterministic contract and its source terminal-execution
certificate. This is the ordinary compiler endpoint, not a claim that public
calldata hides commitments or that runtime-only signals preserve strategies.

`Machine.Contract.IdealVisibility` makes that qualification formal. It decodes
contract storage but exposes only the event graph's source public view and each
player's source private view; raw sealed words and the oracle pending marker are
excluded. Idle encoding and the request/waiting phase are proved to have
exactly the same source observation. The pending marker remains available as a
separately named administrative signal for scheduler proofs. This is an ideal
functionality that a secure backend must implement or refine, not a secrecy
property of ordinary public storage.

`Machine.Contract.FrontierBatch` is the corresponding ideal functionality for
simultaneous strategic rounds. A trusted mediator accepts one legal joint
frontier packet and applies its independent commitments in canonical graph-node
order without exposing intermediate writes. The resulting encoded point-mass
law is proved exactly equal to the source `ExecutionProtocol.step`, and its
ideal public/private observations are exactly the source successor views.
Making this atomic and confidential with public transactions remains a secure-
compilation obligation.

`Machine.Contract.Imperative.ContractIR` begins control-flow lowering without
changing the event bodies. Graph requirements are lowered to physical Boolean
storage checks using the certified layout: replay prevention first, then one
completion-slot check per prerequisite. Its generic short-circuit runner
retains the successful prefix and first failed check, so ordering is already an
explicit operational observation rather than an implicit implementation
accident. When the physical completion reader agrees with encoded semantic
state, acceptance is proved exactly equivalent to `EventGraph.Ready`. A later
gas or revert pass must state whether it preserves, coarsens, or exposes that
observation. Successful bodies are also ordered explicitly: realize the
retained typed event computation, write its physical output slot, then mark the
distinct completion slot. Expression lowering, a concrete gas schedule, and
rollback remain later passes; the following instrumentation accounts only for
check costs.

`Machine.Contract.Gas` decorates the ordered check result with an abstract
per-check cost. Rejected calls pay for the successful prefix and first failed
check; successful calls pay for every check. Erasing gas recovers the exact
unmetered first-failure result, and unit costs are proved equal to the runner's
checked-count observation. This is an instrumentation boundary, not an EVM gas
schedule; body costs, refunds, memory expansion, and out-of-gas behavior remain
unmodeled.

`Machine.Contract.Transaction` adds atomic settlement. A success commits its
state and ordered outbound actions; a revert restores the pre-call state and
emits no actions. Settlement is proved to commute with entropy realization, so
determinization cannot silently change rollback behavior. Receipts, nested-call
semantics, and transaction scheduling are still absent.

`Machine.Contract.EVM.MessageABI` adds a 32-bit selector and fixed argument
ordering without yet adding byte serialization. Player calls are framed as
`[player, node, value]` and internal calls as `[node]`; unknown selectors,
wrong arities, unknown players, and out-of-range nodes reject. The matching-
pennies configuration uses 256-bit role and node codecs and proves its node
count fits in one word. Accepted arbitrary framed input still reconstructs an
exact semantic machine transition.

`Machine.Contract.EVM.ByteCalldata` supplies the next framing pass as a
dependently byte-aligned bitstring. It emits and parses the two fixed ABI
shapes—36 bytes for internal calls and 100 bytes for player calls—using
big-endian selector/word concatenation and exact Ethereum offsets. A separate
lossless argument-word codec connects arbitrary configured storage words to
256-bit EVM words. All other byte lengths reject, serialization round-trips,
and every accepted hostile byte string over reachable storage remains a valid
semantic command. Function selectors are still configured values rather than
Keccak-derived signatures.

The deterministic classical endpoint has its own complete EVM framing rather
than reusing that earlier two-entry stochastic ABI.
`Machine.Contract.EVM.ClassicalABI` assigns four pairwise-distinct selectors to
player commit, reveal, sample request, and oracle callback, with argument shapes
`[player,node,value]`, `[node]`, `[node]`, and `[node,choice]`.
`ClassicalABI.encodeBytes/decodeBytes` realizes the corresponding 100-, 36-,
36-, and 68-byte Ethereum layouts, proves lossless round trips, and rejects all
other byte lengths, selectors, arities, or undecodable words before typed
validation. Callback indices are unsigned 256-bit words; compiling a retained
table index to a word exposes the necessary `< 2^256` proof obligation.

`ClassicalCompiler.EVMByteBackend` is the checked-source assembly point for
that concrete boundary. Given the classical deployment choices, selectors,
player/value codecs, and the node-count capacity proof, it produces one
`EVMByteArtifact` packaged as a deterministic contract over raw byte calldata
and blockchain caller context.

`Machine.Contract.EVM.RuntimeImage` is the first actual runtime-code layer.
It gives the required EVM operations their concrete opcode bytes and proves
that emission has the computed byte length. Four independently compiled
classical handler fragments are linked behind a 64-byte selector dispatcher;
unknown selectors revert, handler entry offsets are computed from emitted
prefix sizes, and the complete image must fit the dispatcher's 32-bit jump
addresses. Assembly and bytecode are derived from the certified handlers, so
the size certificate cannot describe different caller-supplied bytes. No
complete generated-handler refinement theorem currently connects their
execution back to `receive`; the structural readiness and state-write
fragments have executable instruction-level proofs.

`Machine.Contract.EVM.DeploymentImage` adds actual creation bytecode. Its
constructor emits `SSTORE` only for nonzero cells in the finite initial layout,
copies the appended runtime into memory, and returns it. The runtime offset is
computed from the emitted initialization prefix, while both that offset and
the runtime length carry the bounds needed by their `PUSH4` operands.
`Machine.Contract.EVM.ExecutionState` gives the emitted instruction subset an
executable gas-free EVM semantics with byte program counters, `JUMPDEST`
validation, zero-padded calldata, caller/address/value context, total storage,
byte memory, logs, return data, revert data, and constructor `CODECOPY` over
the actual deployment bytes. Kernel-checked tests execute selector rejection
and constructor runtime return. The remaining validation task is a decoder or
external-EVM correspondence theorem for opcode bytes, followed by generated
handler refinement; gas and transaction scheduling are deliberately separate.
`PushData` stores a width-bounded semantic word and derives its big-endian
payload bytes, preventing instruction semantics and emitted immediates from
being configured independently.

`ClassicalCompiler.EVMRefinement.BooleanCompilationCorrect` states the exact
ordinary correctness theorem: canonical total storage must represent typed
protocol state, anonymous logs must represent the ordered oracle requests,
reverts must roll back, creation must install and return the selected image,
and every runtime call must match the deterministic byte-calldata artifact.
Successful deployment compilation is already proved to retain precisely the
selected runtime, canonical slot count, and compiled initial storage. The
remaining instruction simulation is explicit in this proposition rather than
being assumed by the compiler.

`Machine.Contract.EVM.ClassicalStorageLayout` supplies the corresponding
account-state representation. EVM's total zero-default storage cannot directly
represent the earlier sparse field map, so each graph field has a distinct
value cell and presence bit; completion bits and the oracle pending flag/node
occupy separate certified cells. The layout is collision-free, total-storage
encoding round-trips for every classical snapshot, and the deployed storage
decodes to exactly the compiled source initial snapshot. `EVMByteBackend` also
requires a lossless 160-bit address codec, making `CALLER` authentication a
concrete code-generation input instead of an abstract-address assumption.

`Machine.Contract.EVM.ClassicalContractIR` then routes every graph node to its
deterministic handler inventory: commits to the player entry point, reveals to
the reveal entry point, and samples to both request and callback entry points.
Replay prevention and prerequisites are concrete reads of the new completion
cells, in stable order, and are proved to accept an encoded account state
exactly when the source graph node is ready. Each successful action's value,
presence, and completion cells are also proved pairwise distinct. Typed event
code is retained for the remaining expression-specific lowering.

`Machine.Contract.EVM.LocalAssembly` adds handler-local labels without making
jump addresses an unchecked renderer concern. `JUMP`/`JUMPI` targets resolve
only after handler base offsets are known, missing labels reject, and
resolution is proved to preserve byte length before the whole image's 32-bit
bound is applied. Resolution distributes over fragment concatenation, and an
embedded straight-line assembly fragment is proved to remain exact at the byte
offset of its symbolic prefix. The structural handler code generator emits full
256-bit storage keys, `SLOAD` readiness checks with conditional rejection, and
ordered value/presence/completion `SSTORE`s. The supported Boolean expression
fragment first lowers to a proof-carrying Boolean-only IR, then emits
straight-line stack code. Its branchless conditional circuit evaluates pure
branches and selects canonically without exposing the choice through control
flow. The byte-offset execution layer proves prefix fetching and code-fragment
composition, and the
resolved readiness sequence is proved to fall through without side effects
when its canonical storage facts hold. Source graph readiness supplies those
facts and the required non-wrapping key bounds for every generated check. The
expression compiler is proved to push exactly the encoded source value under a
stable read precondition. Fixed calldata and total-storage loads satisfy that
contract when their keys are representable and the addressed words are
canonical. The retained guard adapter is instantiated against an explicit
action-calldata/stored-binding invariant. The resolved action-write sequence
is proved to consume its result and perform the three exact, ordered,
non-wrapping storage updates under the same certified layout bound.

`ClassicalCompiler.EVMByteBackend.compileBooleanDeployment?` is the complete
trusted-oracle Boolean source-to-creation-bytecode endpoint. It supports the
concrete Boolean `simpleExpr` fragment (variables, constants, equality,
conjunction, negation, and conditionals), exact retained Boolean probability
tables, and conditional distributions. Player and reveal handlers authenticate
and update storage; sample requests lock the contract and emit the node as an
anonymous 32-byte log; callbacks authenticate the configured oracle, validate
the unique pending node and table index, realize the selected value, clear the
lock, and complete the graph action. Its representation certificate requires
the configured storage and wire codecs to encode and decode Booleans exactly
as EVM zero and one. Unsupported expressions, noncanonical representations,
tables larger than the callback word, missing labels, or oversized images do
not compile. The no-sample runtime and deployment endpoints remain as smaller
specializations; the test suite takes an empty checked source program to a
190-byte runtime and a 211-byte creation image. VM-level semantic correctness
is not yet proved.

The generic classical deterministic artifact also exposes caller-free
messages. As at the byte ABI, the authenticated identity is attached solely
from the blockchain call context's `sender`; a message cannot assert its own
player or oracle caller address.

This step projection is intentionally not called game preservation. A pass
that adds observations, scheduling choices, timing, or adversarial behavior
must also prove the relevant information or strategic theorem.
`Runtime.DeviationAdequacy` is one narrow such criterion: target strategies are
back-translated one unilateral deviation at a time, which is sufficient to
preserve and reflect Nash at compiled profiles. It is not a general
secure-compilation theorem.

`Runtime.TrustedRoleAdequacy` permits the target game to add an injectively
separate oracle, batcher, or scheduler role. Its compiled strategy is fixed
across source profiles, utilities and laws are decoded exactly for real
players, and Nash is preserved and reflected when deviations quantify only
over those real players. `Runtime.KnownMediator` supplies a canonical proved
witness: the added mediator's complete contingent strategy is exactly
`source.form.play`, so externalizing stochastic play to a player with a known
strategy is classically exact. A concrete callback/batching trace must still
be proved to implement that mediator strategy; malicious mediator behavior is
outside this classical theorem.

`Runtime.Implementation` is only the terminal special case where the runtime
has exactly the source strategy carrier and decoded outcome-law equality holds
for every profile. It derives deviation adequacy automatically. It must not be
used to skip intermediate scheduler or information proofs.

`Scheduled.Equilibrium` proves a concrete strategic-preservation result for
the graph-derived serializer. For every behavioral scheduler observing the
public graph history, compiled source behavioral play has the same complete
terminal-state distribution, and source Nash equilibrium is equivalent to
Nash for the original runtime players against all behavioral deviations.
Players may condition their deviations on observed orders; scheduler utility
and scheduler optimality are irrelevant. The proof reconstructs runtime
information from the canonical source player's compact information, then
predraws only scheduler randomness. Honest opponents remain unchanged.

The distributional statement is stronger than Nash preservation: every
unilateral behavioral runtime deviation induces a finite mixture of source
deviation terminal-state laws against the same opponents. Thus every source
upper bound on expected terminal loss is preserved and reflected, even when
the loss measures harm to an honest player and the adversary has no rationality
assumption. Approximate Nash equilibria are preserved and reflected with
exactly the same ε. For randomized schedulers the mixture witness is
profile-local; a uniform opponent-independent translator is not claimed.

`VegasTests/MatchingPenniesEquilibrium.lean` proves the payoff table of the
compiled hidden-choice game, including its automatic reveals, constructs its
fair-coin behavioral Nash equilibrium, and transports it through the actual
serializer for every behavioral public-data scheduler. With one fair player,
an arbitrary unilateral runtime adversary leaves both expected payoffs exactly
zero. This is a concrete honest-player guarantee, not just a conditional
equilibrium-equivalence instantiation.

This result concerns the modeled serializer, not public-chain execution.
The scheduler cannot inspect sealed values or current simultaneous submissions,
and utilities of original players depend only on the settled graph state.
The unilateral results do not establish coordinated-coalition security.
The theorem does not model censorship, transaction timing, gas, external
utility, or cryptographic realization of the sealed values.

## Strategic runtime boundaries

Two additional runtime models give proved limits rather than assumed
preservation obligations:

- `Scheduled.PublicSubmission` executes two irreversible public Boolean
  submissions in scheduler-selected order. The later player observes the
  earlier value and can force matching-pennies payoff +1. No target profile
  preserving its source payoff zero is Nash; approximate preservation requires
  payoff error + equilibrium slack at least 1. No player-deviation adequacy
  certificate into this fixed runtime exists from a source game with a
  zero-payoff Nash equilibrium, regardless of the compiler or decoder.
- `Runtime.SelectiveAbort` adds a final decision to complete or abort after
  observing one's prospective utility. Its exact optimal value is
  `E[max(source payoff, abort payoff)]`. The full Nash criterion includes
  changes to both the source strategy and the randomized refusal rule.
  `VegasTests/RuntimeBoundaries.lean` proves that the compiled matching-pennies
  fair equilibrium survives this pass exactly when the designated player's
  net abort payoff is at most −1. A refund payoff of zero gives a deviation
  worth +1/2 instead of zero.

The public-submission result changes the information available before choosing;
it does not refute the atomic-frontier serializer theorem. The refusal result
assumes a final informed veto with specified terminal abort payoffs. Neither is
an impossibility theorem for arbitrary blockchain protocols. The net-utility
threshold is not a verified deposit, funding, or timeout implementation.

## Path to a blockchain backend

An EVM-class compiler can grow as a sequence like this:

1. lower the `Machine.Contract.Manifest` code and logical slots to a backend
   expression and physical storage IR;
2. lower the executable logical request validator to a
   dependency-respecting scheduler or callable-node ABI over decoded target
   state;
3. choose storage layout, role authentication, calldata, receipts, and revert
   behavior;
4. refine semantic sealed values to commitments and reveal verification;
5. implement chance with an oracle, VRF, multi-party protocol, or another
   mechanism whose actual law and adversarial assumptions are stated;
6. add time, nonparticipation, abort/timeout, and settlement behavior;
7. lower the concrete contract IR to deployable EVM creation/runtime bytecode;
8. prove the emitted instruction and transaction traces refine the classical
   receive relation through the preceding layers.

The repository provides the first machine IR, composable operational
projection, an exact terminal source-payoff certificate, certified logical
contract inventory/layout/storage/state/call boundaries, a finite 256-bit
Boolean storage codec, physical ordered-check/action-body IR, abstract check
gas and rollback projections, certified fixed-shape EVM byte calldata, a
complete deterministic typed contract under trusted oracle/scheduler roles,
an ideal observation/atomic-frontier boundary, a lossless total EVM storage
layout, an EVM opcode emitter, four-entry runtime linker, deployable constructor,
and unilateral strategic certificates for same-player and fixed-trusted-role
targets, plus a complete deterministic four-entry EVM byte-calldata artifact
and a trusted-oracle Boolean source-to-EVM backend. It does not yet have a codec
and expression compiler for other source types, reified restricted trigger
policies, a concrete transaction scheduler, cryptographic commitment
refinement, exact untrusted on-chain chance implementation, timeout/abort game
semantics, an external-EVM correspondence theorem, or an end-to-end bytecode
refinement theorem.
The source-star theorem is about possible terminal runs and payoff equality; it
does not equate probability laws, intermediate information histories,
schedules, or target strategy spaces. Those are VegasCore gaps, not features
supplied by GameTheory.

## Game semantics

The canonical strategic denotation is GameTheory's
`ExecutionProtocol + InformationModel`, packaged as a FOSG. It is not a MAID.
State-dependent guards determine native legal menus, simultaneous ready
commitments form one joint frontier action, chance is a `FinDist` transition,
and policies depend only on a player's information state.

`Vegas.Game` adds terminal utility and a proved finite horizon. Its pure,
behavioral, and mixed-pure forms are direct GameTheory views. Vegas does not
define competing strategy, deviation, equilibrium, or history types.

GameTheory's opponent-preserving Kuhn laws are packaged in
`Vegas.Game.Kuhn` as deviation-adequacy certificates in both directions between
behavioral policies and mixed pure policies. The compiled information model
proves perfect recall. With finite source domains, a locally full-support policy
enumerates a finite counterfactual site cover, yielding Nash preservation and
reflection at the translated profiles without requiring the entire information
carrier to be finite.

The information state retains the latest public/private graph snapshot plus the
player's own earlier decision snapshots and actions. It deliberately does not
retain unrelated transition ordering. Menu adequacy, policy inhabitation, and
perfect recall are proved.

## Source language

The typed core has four protocol constructors:

- `ret`: terminate with public-state payoff expressions;
- `sample`: draw a public value from an exact finite probability law;
- `commit`: let a player choose a sealed value satisfying a guard over that
  player's view;
- `reveal`: publish a previously sealed value.

Visibility is carried in the context type. A commit guard cannot read data its
owner cannot observe, and terminal payoff expressions cannot mention sealed
state. `WFProgram` proves fresh bindings, reveal completeness, and live guards.

The language does not yet express deposits, transfers, participant addresses,
timeouts, aborts, or failure to reveal. A blockchain backend cannot silently
invent those behaviors and still claim exact game preservation.

## Probability

There is one semantic probability type: GameTheory's `FinDist`.
`RationalLaw` is exact source syntax for a normalized finite table of
nonnegative rational masses. `IExpr.evalLaw` makes that table the executable
distribution interface, and `EventDist.evalLaw` carries it into graph-local
code. The compiler proves exact table equality before denoting it as
`FinDist`; repeated entries combine in the denotation, which works over
arbitrary value carriers.

Subprobability is unnecessary for the checked language because every compiled
game has a uniform finite horizon. Divergence would require a separate language
feature and semantic design.

Exact source probabilities do create a backend obligation. Common blockchain
entropy constructions can be manipulable or biased, and modulo reduction is
not in general an exact implementation of a rational law. Any approximation or
trust assumption must be represented explicitly rather than hidden by code
generation.

## GameTheory boundary

GameTheory supplies the canonical probability, utility, deviation,
equilibrium, informed-protocol, FOSG, behavioral/mixed, unilateral Kuhn,
assessment, backward, and FOSG-to-EFG machinery used here. The unilateral Kuhn
results live on the underlying `InformationModel`; Vegas uses them directly
rather than waiting for an additional FOSG convenience wrapper.

Secure compilation, scheduler hyperproperties, strong linearizability, and
adversarial runtime refinement are runtime-specific and have no general
GameTheory abstraction. Also, GameTheory's fixed-domain MAID surface cannot
directly represent Vegas's guarded state-dependent menus without a strategic
encoding theorem. Its probability library has uniform finite laws but no
constructive exact-uniform-seed realization theorem for rational finite laws;
Vegas currently exposes that missing compiler certificate explicitly.

VegasCore owns the latter boundary and must add only the certificate justified
by each lowering pass.

## Build

```text
lake --wfail build
```

The public roots are `Vegas`, `Vegas.Core`, `Vegas.EventGraph`,
`Vegas.Language`, `Vegas.Compile`, `Vegas.Machine`, `Vegas.Game`,
`Vegas.Game.Kuhn`, `Vegas.Runtime`, and `Vegas.Scheduled`.
