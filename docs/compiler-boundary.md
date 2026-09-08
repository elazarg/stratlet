# Minimal core, rich frontend, and runtime refinement

Status: frontend integration contract with checked core/graph examples, not
an implemented general frontend bridge. The proved boundary is in
[runtime-models.md](runtime-models.md). The [compilation design](compilation-design.md)
owns the tower architecture; this document specifies the rich-frontend/minimal-core
edge. The [implementation plan](ledger-expansion-plan.md) makes public-message
execution the next runtime target, independently of frontend integration.
The checked one-shot representation comparisons and their limitations are recorded
in [runtime-models.md](runtime-models.md#failure-observations-checked-one-shot-comparisons).
Those kernel comparisons are not an implementation of failure handling. The
separate core probe below establishes syntax, guard, execution, and view facts,
not their full strategic composition.

The [quitting compilation contract](quitting-compilation-contract.md) fixes
the key ownership rule: source quitting is already defined. Accounting for
runtime refusals, invalid requests, and missed deadlines is the compiler's
obligation, not a reason to weaken the programmer-facing source discipline.

## One small language boundary

Kotlin Vegas owns the programmer-facing language. VegasCore is its intended
small semantic compilation target, not a second implementation of that
language. No Kotlin AST, macro system, handler syntax, or duplicate surface
typechecker belongs in the core. The existing Lean `VegasLang` convenience
layer is not a commitment to reproduce the Kotlin language.

`VegasLang.lower` is an intrinsically typed translation into `VegasCore`: its
result is well typed by construction, administrative lets are substituted,
and each surface yield becomes a nullable commitment followed by a reveal.
This does not admit the result as a `WFProgram`; the caller must separately
provide the global scope, freshness, reveal-completeness, and legality evidence
required there. Nor does the translation currently have an operational-law or
unilateral-strategy-preservation theorem.

Core admission uses `Legal` from `Vegas/Core/Obligations.lean`: each commitment
guard must admit an action in every environment of its declared visible type,
including environments unreachable during execution. A frontend checker must
establish this condition, not only reachable-state progress. The Lean payout
evaluator in `Vegas/Foundation/Payoff.lean` sums duplicate entries for a player
and assigns zero to omitted players. Any frontend with a different payout-list
discipline must account for that difference at the translation boundary.

```text
Kotlin Vegas program
  -> Kotlin checking and rich-language lowering             [frontend owner]
  -> one checked core artifact                              [integration boundary]
  -> graph -> public-message protocol -> runtime refinements [compiler + runtimes]
       each stage has native execution and game semantics
       each edge proves its claimed strategic correspondence
  -> generated deployment                                  [selected backend]
```

This is the intended architecture, not the current Kotlin execution path.
Analysis at each stage uses that stage's native semantics. Compiler proofs
relate those games to the independent meaning of the checked core artifact.
A source map or matching artifact hash records provenance but
does not prove frontend correctness or backend correctness.

| Owner | Owns | Does not acquire |
| --- | --- | --- |
| Kotlin Vegas | syntax, types, handler policy, elaboration, lowering, source diagnostics | an unchecked claim that its output matches the Lean game |
| VegasCore | minimal typed core, independent source and graph/game interpretations, core compilation proofs | rich surface syntax or language-specific ledger semantics |
| Frontend integration | reading/checking core artifacts; later validation of Kotlin lowering | a second implementation of the entire Vegas frontend |
| Generic runtime libraries | commands, local observations, operational and strategic comparisons | Vegas handlers, auction rules, or a duplicate game evaluator |
| Backend/chain adapters | concrete code, transaction execution, network/consensus realization | authority to change the source game's information or quitting rules |

Physical package extraction follows actual reuse, not this table alone. Keep
Vegas-specific integration tooling on the frontend side where practical;
the core checker understands only the core representation it certifies.

## Current evidence and the expressiveness question

The checked syntax in [Core/Basic.lean](../Vegas/Core/Basic.lean) consists of
`ret`, `sample`, `commit`, and `reveal`. Choices occur at commitments;
disclosure of the stored value is an internal transition. The syntax has a
fixed continuation rather than a general conditional protocol branch. The
compiled graph uses semantic dependencies; textual order alone is not a
barrier. Payoffs read public state.

Kotlin already has source quitting, persistent abandonment, and handler
lowering. Relevant integration surfaces are `vegas.ir.GameIR`,
`vegas.semantics.GameSemantics`, and `vegas.frontend.ToIR` in `../vegas`.
Its EVM lowering consumes a graph after commit/reveal expansion. That is a
different stage from the source-semantic object we need to relate to the core.
Do not import expanded backend commitments as if they were original game
choices, or run commitment elaboration twice.

The candidate semantic representation of disclosure is an optional value:
`some v` denotes opening the earlier binding and `none` denotes quitting.
That is not yet a claim about an equivalent core or wire encoding. In
particular, a cleartext quit signal is not automatically equivalent to a
commitment to `none`, a malformed commitment, or a failed opening. Each has its
own observation time and remaining choices. A candidate fresh optional core
choice must constrain `some v` to match the binding, and locate the choice at
the correct information checkpoint. No syntax extension is adopted here;
proving this representation adequate is work, not a premise supplied by its
option type.

The remaining obligations concern the encoding's strategic semantics and the
hypotheses of existing theorems. `WFProgram` retains `RevealComplete`: every
original sealed binding is opened, not merely an optional public copy.
The graph compiler does not require this condition; it takes `GraphProgram`
with scope/freshness evidence. The current well-formedness documentation also
states that reveal-completeness is not needed for graph progress. That weaker
compiler prerequisite is not a replacement for the checked-source discipline.
Do not drop it to admit an encoding, or disclose the original secret on the
quit branch to satisfy it. `ToEventGraph.compile_guardLive` takes exactly
`GraphProgram` and `Legal`; `Machine.ofCompiled` therefore accepts the probe
without weakening `WFProgram`. The existing nullable-yield lowering and staged
quitting examples are components, not a proof of general handler lowering.

The executable `HiddenReserve.vg` fixture makes the discrepancy concrete:
the seller commits a reserve, observes a buyer bid, and can quit at its later
acceptance decision. The specified handler awards the buyer 200 units.
`GameSemantics` offers the quit transition; `History.quit` retains abandonment
and removes later explicit choices. At subsequent reveal processing, public
quit status does not disclose the old hidden reserve in retained history.
The executable source and its optional-disclosure tests supply this evidence;
it is not a Lean theorem about the Kotlin evaluator.

The existing Lean obstruction is precise: a commitment-preserving encoding
with no reveal site for that binding contradicts
`WFProgram.committed_source_revealed`; `OptionalDisclosure.not_checked`
instantiates this conflict for the proposed optional-copy encoding. This is
not an impossibility theorem for every encoding or coarser outcome comparison.
Adding a final unconditional reveal would change the source's confidentiality
and would still require the adversary to supply that opening at runtime.
The source-resolution integration therefore needs an explicit design decision
about a narrowly scoped conditional-disclosure/control representation. Until
that decision is authorized and checked, the existing core admission and its
theorems remain unchanged.

First try ordinary values, guards, explicit dependencies, and payoff
expressions. A proposed encoding must preserve information and unilateral
choices as well as payouts. Extra dummy moves require an information-local
strategy correspondence; extra disclosure cannot be erased just because the
immediate payout ignores it. A finite payoff table or precommitted complete
strategy is not an adequate encoding if it changes when choices are made or
requires an infeasible runtime protocol.

There are three possible outcomes of the expressiveness check:

1. A faithful encoding exists: implement it in the frontend, with a small
   core-level lemma for its semantic pattern where useful.
2. Only a restricted encoding exists: specify and check the supported fragment;
   unsupported input is rejected, not silently given weaker quitting semantics.
3. A necessary distinction cannot be expressed by the proposed class of
   encodings: state that bounded obstruction precisely. Consider a single
   general control primitive only with a concrete witness, semantics, and an
   audit of affected proofs. Failure of one encoding is not an impossibility
   theorem for the language. No core extension is authorized by default.

### Conditional disclosure design gate

A candidate minimal operation has the following source meaning: at the owner's
current information state, either publish the already-bound value or take the
program's declared quitting continuation while retaining the secret. Success
cannot select another value. Initial-choice quitting and later bound-value
withholding are distinct checkpoints; neither can be moved across intervening
observations without proof. Runtime expiration must implement this source
meaning under stated service/control assumptions, not define it retrospectively.

Two representations need a bounded comparison before changing the core:

- A typed optional-disclosure/disposition operation, with quitting status and
  later forced choices elaborated using ordinary public values and guards.
  This is the smaller candidate. It requires a proof that the forced choices
  can be implemented or eliminated without new strategic freedom, information,
  or cooperation requirements from an abandoned player.
- Typed success/quit continuations with explicit participation/resource
  tracking. This represents control directly but changes the source, compiler,
  and graph semantics more broadly. An active-player type index is one possible
  implementation, not an established necessity.

Either representation must account for each sealed binding by disclosure or
an explicit source-authorized disposition. Merely omitting that binding from
public payout expressions does not discharge the obligation. Persistence of
quitting, handler outcomes, and the decision's information checkpoint need
proof for the concrete lowering. A second later checkpoint of the same owner
is the distinguishing test: quitting must remove subsequent freedom while
preserving prior knowledge and other players' continuations.

The two-checkpoint probe is `VegasTests/PersistentDisclosure.lean`. Its second
guard forces `none` after the first public `none`, and the compiler places that
decision after both the first disposition and the other player's response.
`PersistentDisclosure.source_refusal_persists` proves persistence for
every supported execution of the existing written-order source denotation.
`source_suffix_after_refusal` identifies the entire remaining source law,
including both bindings, independently of the source profile.

`Vegas/Core/ForcedChoice.lean` supplies the reusable source-side certificate:
public expressions select an enabling region and a value, and a proof checks
that the original guard admits exactly that value throughout the region.
It quantifies over all source environments, including unreachable environments
and every assignment of private fields. The certificate removes consultation
of the current choice policy while retaining the original continuation and
source transition. It does not authorize an external actor to register or send
messages as the owner, remove an observable event, or guarantee service.

Thus ordinary guards suffice to remove later freedom in this concrete source
pattern. Implementing the forced steps without the quitter's cooperation and
accounting for the retained original secret remain separate obligations. The
probe still fails `RevealComplete`; no source-admission rule is changed.

The successful-disclosure branch needs a different argument: its uniquely
determined payload can still be private. `PublicForcedChoice` therefore cannot
justify public computation of that payload. Any conditional-disclosure
representation must tie success to the original binding and account for the
timing of status and payload publication. In particular, publishing a success
status before an owner-dependent payload must not introduce an unaccounted
opportunity to withhold after observing another player's reaction.

The existing optional-copy obstruction does not decide between these designs
or prove that all existing-core encodings fail. No broad branch language,
participation index, or weaker well-formedness rule should be implemented
solely on the strength of that obstruction. Choose the smallest representation
that passes the two-checkpoint strategic and resource tests, then audit the
affected source-to-graph and runtime proofs before integration.

## What each certificate would mean

Keep these obligations separate in APIs, tests, and paper claims:

| Obligation | Evidence required | What it does not prove |
| --- | --- | --- |
| Core acceptance | reconstruction of a typed term and its required well-formedness evidence | correspondence with a `.vg` program |
| Analysis correspondence | game interpretation of that exact term; checked export/decoder if using an external analyzer | correctness of an external equilibrium solver |
| Runtime eligibility | decidable structural conditions with a soundness theorem for a named compiler/model | inclusion, funding, or cryptographic security of a real chain |
| Strategic implementation | compiled-play law and arbitrary unilateral-deviation comparison with fixed opponents/environment | equality of all observable traces unless separately proved |
| Frontend correctness | an information- and strategy-respecting relation from Vegas semantics to the emitted core | correctness merely because emitted Lean elaborates |
| Deployment correctness | relation between the certified protocol and the code actually deployed | correctness of Kotlin Solidity/Vyper output from unrelated Lean bytecode lemmas |

Core acceptance and runtime eligibility are distinct. A well-formed game may
not be implementable on a chosen target; hidden guard validation is one
possible reason. An eligibility check lists residual external assumptions
separately from properties it proves. It does not add penalties, knowledge,
environment moves, or a new solution concept to obtain acceptance.

Initially trust Kotlin parsing/lowering and explicitly state that the theorem
starts at emitted core. Reject unsupported constructs rather than claiming
all typechecked Vegas programs are covered. Subsequent translation validation
can reduce the frontend trust boundary one pass at a time. A full frontend
theorem would require a source semantics, but any rich-language formalization
belongs to a separate frontend project, not to the minimal core.

Do not design a general interchange schema yet. After one encoding passes,
use the smallest data-only representation of the existing finite core subset,
or emitted Lean terms checked by the kernel. Include roles, finite value types,
expressions, visibility, dependencies, and payoffs actually needed by the
example. Handler syntax must already be lowered. Check names, scope, types,
and all claimed proof obligations; a backend-provided Boolean is not proof.
Record supported features and the trust boundary without a compatibility layer.

## First bounded step: an optional-disclosure encoding

This is a bounded frontend integration task. Test the strategic abstraction
of quitting before integrating a candidate encoding with Kotlin. It is not
a prerequisite for public-message execution of an already checked core program.

### Compare the representations before identifying them

Specify a tiny finite interaction with the following distinct events and
recipient-local observations. Do not normalize them to `none` on submission:

| Representation | Observation/control that must remain until justified otherwise |
| --- | --- |
| Explicit cleartext quit | visible when delivered; source-defined cessation of later actions |
| Missing commitment | absence only in the observer's local history; expiry or another rule may resolve it |
| Opaque malformed commitment | visible raw submission; invalidity may not be detectable until opening |
| Valid commitment, withheld opening | holder may retain an informed later choice; eventual timeout requires resolution |
| Cryptographically invalid opening | disclosed bytes, failure receipt, retry rights, and exposure before validation |
| Cryptographically valid opening of a nonsense value | successful opening but failed application-domain/guard validation; payload may still be public |

Whether failure is terminal, retryable, or recoverable by a later valid opening
must be specified, not inferred from the word "quit". Identical payouts do not
make these histories strategically identical. A submitter may also use junk
bytes as a public signal. An ideal hiding service hides a valid payload under
its specified interface, not arbitrary adversarial traffic by definition.

The smallest experiment has one submitting player and one responding player
with a choice between the earliest and latest failure signals. Compare early
public quitting with failure recognized only at resolution. Establish a
distinguishing information/strategy behavior, or a proof that the chosen
continuation cannot exploit it; do not assume indistinguishable settlement
implies this result. Then test a barrier variant that fixes the responding
choice before those differing observations can affect it. The barrier variant
is a positive candidate, not an assumed cure for every public signal.

Use existing finite GameTheory protocols, a bounded raw alphabet, and explicit
event order first; no full ledger infrastructure or crypto reduction. Finite
classes of malformed inputs must be named as a restriction, not a proof that
all byte strings behave alike. A later arbitrary-message result must justify
its observational abstraction or quantify over raw messages directly.

The desired compiler result is directional strategic adequacy: compiled play
matches the abstract game, and every admitted runtime unilateral replacement
is represented by an information-local abstract replacement or justified
mixture, against the same opponents and one consistently related environment.
The source quit action must itself have an implementation for the compiled-play
law. Bidirectional equivalence of two runtime representations requires both
directions separately; preserving one equilibrium is weaker than either claim.

Prove this first for the explicitly chosen finite pure-policy class and
declared continuation family. Do not claim all behavioral or computational
strategies without the separate extension. A general all-game compiler must
later discharge the comparison uniformly for every accepted core program.

In the backtranslation, decoding a completed failure to `none` does not permit
the abstract player to choose using future observations. Distinguish a
settlement decoder from an admissible strategy translator. Environment-caused
timeout is not voluntarily chosen quitting just because both decode to `none`.
Costs and publicly visible failure receipts must be retained or explicitly
outside the first theorem's utility/observation scope.

**Immediate deliverable:** one finite separating example or positive comparison
with the exact missing information/control premise identified. If a uniform
equivalence fails, retain the counterexample and seek the weakest useful
compiler eligibility condition; do not add a universal runtime AST to explain
away the failure. This precedes any production encoding change.

The one-shot kernel deliverable is checked in
`Vegas/Runtime/FailureObservation.lean` and `VegasTests/FailureObservation.lean`:
a loss of Nash despite compiled-law equality, a no-mixture-backtranslation
witness, and a generic barrier adequacy construction. Its barrier is part of
the strategy carrier. Concrete event/observation semantics must still justify
using that carrier for an implementation; six failure labels do not do so.

`Vegas/Runtime/ConstantSignal.lean` also proves profile-local preservation when
the extra signal is constant on the unchanged submitter's support, although
target responders may inspect it and submitting deviations may change it.
Its concrete compiler keeps honest responders signal-independent. This yields
exact unilateral laws, approximate Nash equivalence, and adversarial observable
bounds. Strictly dominated quitting supplies the support condition at Boolean
source Nash profiles. Thus the varying-signal counterexample does not rule out
preserving non-quitting equilibria without a response barrier. The same
implementation and information premises still need proof for a public runtime.

### Check one frontend/core encoding against that contract

The finite probes are `VegasTests/OptionalDisclosure.lean` and, in Kotlin,
`src/test/resources/optional-disclosure.vg` with `OptionalDisclosureTest.kt`.
Their exact evidence and remaining differences are recorded in
[runtime-models.md](runtime-models.md#optional-disclosure-core-probe).
They are not yet a matched frontend/core artifact pair: Kotlin also admits
initial and responder quitting, and its fixture has different settlements.
The Kotlin checks compare disclosure checkpoints after a valid binding. The
Lean result additionally proves a full behavioral policy/outcome/payoff
correspondence with the hand-specified `OptionalDisclosure.finiteForm`, and the
sealed-offer instance reaches private requests plus public serialization.
Neither result proves equality with the complete Kotlin game.

Use one tiny, typechecked Kotlin fixture with a hidden Boolean binding, a later
public signal, an optional disclosure decision, and a second player's
subsequent choice with branch-dependent payouts. Check the exact handler form
accepted by the frontend; do not invent new syntax to make the example fit.
Extract finite moves and local observations through the existing semantics.
The signal makes it possible to detect an incorrectly precommitted quit choice.

Try lowering disclosure to a fresh optional core choice constrained to `none` or
`some` of the original value, followed by disclosure of that optional choice.
Leave the original value hidden on quitting. Audit `RevealComplete` separately
from this typed encoding. Prove that any extra commitment/disclosure used by
the encoding meets the observation/strategy contract above; it is not harmless
administrative syntax by assumption. Reuse expression, graph, and game
interfaces; do not introduce a phase-language AST or a general framework for
this probe.

Deliverables, in order:

1. The actual `.vg` fixture and frontend test documenting the optional opening,
   its timing, observations, and payouts. No auction theorem, crypto scheme,
   or ledger implementation is a prerequisite.
2. One checked candidate core term, or a precise distinguishing behavior for
   a failed candidate. Check frontiers rather than assuming written sequencing
   imposes the desired causal order.
3. For a successful candidate, information-local strategy maps and an all-pure-
   profile outcome-law correspondence in the chosen finite model, covering
   unilateral replacements against unchanged opponents. Explain how any dummy
   moves are eliminated. Kotlin differential enumeration is useful evidence,
   not a kernel proof of Kotlin's evaluator; state that trust explicitly.

Explicit negative checks: an accepted opening cannot change the bound Boolean;
the canonical compiled quit need not disclose it; the quit decision can depend
on the later signal; and a source-distinct continuation cannot be collapsed by
the outcome decoder. A malicious failed opening can deliberately leak the
secret: either backtranslate that signaling behavior or reject the claimed
abstraction. Do not assume that all failure traffic is noninformative.
Clarify the frontend's pending-commit validation obligation: refusal cannot
force a secret disclosure merely to validate a quit payout. Reject unsupported
private validation conditions rather than hiding them in a core guard.

The second-checkpoint source and graph probes above constrain the persistent
quitting representation. The executable Kotlin regression is
`PersistentQuitSemanticsTest.kt`: the role quits after a successful commitment,
the opponent acts, and later choices and disclosure cannot revive the quitter.
It tests the frontend's own semantics, not equality with the Lean probe. A
forced administrative source choice is acceptable only with the stated
strategic and information correspondence for its eventual implementation.

Success of the first probe establishes a useful encoding pattern, not general
handler lowering, public-delivery adequacy, or blockchain correctness. Its
consumer is a minimal emitted-core integration. The independent core-to-public-message
compiler slice proceeds under the implementation plan without waiting for it.

## Expand targets, not the source language

A runtime protocol is compiler output with an observation/strategy adapter,
not another user-facing source language. Introduce phase data only when the
first concrete lowering needs it, and derive its game through canonical
GameTheory interfaces. If a richer target exposes a source-inexpressible
choice or signal, reject that compilation or state a weaker theorem; do not
automatically enrich the core with target events.

Each target increment should retain a working smaller instance and close one
specific assumption. The following are checkpoints, not a mandate to build
every layer before obtaining a useful result:

| Target increment | Small useful deliverable | Boundary still open |
| --- | --- | --- |
| Existing resolved windows and serializer | apply existing theorems to the emitted supported core term | public pending requests, inclusion and deadlines |
| Public-delivery slice | one phase with raw attempts, local exposure, inclusion/cutoff and explicit timeout caller; prove or refute its strategic comparison | a general ledger compiler and actual chain service |
| Contract execution | one complete generated path including hostile calls, settlement and reversion | whole backend, fees/external effects outside the path |
| Named transaction/ledger model | code and observations related to ordered transactions; explicit costs and bounded-service premises | realization of those premises by a network/consensus protocol |
| Distributed chain and cryptography | retained observations across reorgs; named service/security realization | only the assumptions explicitly left in the composed theorem |

Do not replace Kotlin's backend wholesale or maintain two production routes
without need. Choose one integration route when the first contract slice is
ready: generate from the checked core through a verified route, or validate
the existing backend's output against the certified protocol. In either case
the final theorem must identify the actual deployed artifact. The existing
Solidity dependency-triggered timeout and shared clock updates are behaviors
to account for, not an abstract guarantee that each deadline settles itself.

At every composition boundary specify: state/outcome projection, retained
local observations, admitted player and environment policies, operational
progress/failure assumptions, strategic deviation coverage, and utility/error
accounting. A state simulation alone is not strategic preservation. Public
traffic must not change the source environment separately for each deviation.

The eventual goal is a closed path from a supported Vegas program to deployed
code on a pinned realistic blockchain model, with explicit frontend, compiler,
execution, consensus, crypto, and economic assumptions. Forks can roll back
state but not an observer's knowledge. Computational crypto needs a
computational comparison, not an unbounded-strategy exact-law claim. These
constraints guide interface choices now; they do not justify building all
those models before the public-message slice exercises their interfaces.
