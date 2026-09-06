# BitML and formal-quant: comparison and reusable lessons

## Scope and evidence

This is a design assessment, not a claim that either external artifact has
been reproduced or incorporated into VegasCore. The inspected revisions are:

| Artifact | Pinned revision | Evidence inspected |
| --- | --- | --- |
| [formal-bitml](https://github.com/omelkonian/formal-bitml/tree/af61b38b908193496ee1d6c9794dad9df7c6a205) | `af61b38` | Symbolic semantics and selected metatheory; Melkonian's 2024 thesis |
| [formal-bitml-to-bitcoin](https://github.com/omelkonian/formal-bitml-to-bitcoin/tree/ca694260eaf047b1dbe7ece9a972b14d5834f0ee) | `ca69426` | Compiler, strategy model, coherence, parsing, and soundness proof sources |
| [formal-quant](https://github.com/roigecode/formal-quant/tree/cc48cd221200d2c78d920a56e638e5d73fe52c51) | `cc48cd2` | Theorem statements, claim boundaries, fixtures, audit scripts, and licenses |

The BitML Agda developments were not rebuilt. The formal-quant source-policy
scanner passed and its stored axiom inventory contains 554 records using only
the three standard Lean axioms; this is not a fresh kernel replay. Its Lean
development and Rust implementation were not rebuilt. An attempted Python
evaluator test run was blocked by Windows platform requirements (`resource`
and symlink privileges); this says nothing about its Lean proofs. A checked-in
release workflow is a reproduction recipe, not evidence of a successful run
for the inspected revision.

## BitML: the closest operational comparison

The symbolic repository and compilation repository are separate. The original
[BitML paper](https://eprint.iacr.org/2018/122.pdf) already supplies adversarial
strategic semantics and a computational soundness theorem for compilation to
Bitcoin. Neither explicitly modeling nonresponse nor relating target behavior
to source behavior is new here. Its theorem and the extent of the Agda
mechanization must be assessed separately.

### Disclosure is a protocol, not just a settlement value

The symbolic model distinguishes a commitment with a valid secret length from
an invalid binding, using `Maybe ℕ`, and represents revealed secrets separately.
Dishonest commitment authorization can introduce an invalid binding; valid
reveal authorization requires a valid one. Stripping hides commitment contents
and validity before revelation. These are useful distinctions for our optional
disclosure experiment, not a proof that every failure can be replaced by one
`none` action. See the symbolic
[inference rules](https://github.com/omelkonian/formal-bitml/blob/af61b38b908193496ee1d6c9794dad9df7c6a205/BitML/Semantics/InferenceRules.agda)
and compiler
[stripping definitions](https://github.com/omelkonian/formal-bitml-to-bitcoin/blob/ca694260eaf047b1dbe7ece9a972b14d5834f0ee/SymbolicModel/Stripping.agda).

Publication of an authorization or opening differs from executing an action:
someone else can subsequently use the published capability while it remains
valid. Withholding one authorization does not permanently remove a participant
from every later decision. A false reveal guard disables a branch; it does not
automatically settle the contract. A timeout enables an alternative branch,
potentially racing with an untimed reveal until the shared output is spent.
Thus neither Vegas's persistent quitting discipline nor a strict expiry cutoff
can be identified with BitML nonresponse without a separate argument. The
thesis discusses these rules on printed pages 72--77 (PDF pages 81--86).

### Service and adversary assumptions matter

In the compiler's
[symbolic strategy model](https://github.com/omelkonian/formal-bitml-to-bitcoin/blob/ca694260eaf047b1dbe7ece9a972b14d5834f0ee/SymbolicModel/Strategy.agda),
honest strategies propose sets of moves and the adversary selects moves after
seeing stripped proposals. Time can advance by a given delay only if every
honest proposal set is empty or permits at least that delay. A pending honest
nondelay action can therefore prevent time from advancing. This is stronger
than eventual inclusion and does not model censorship while the chain clock
continues normally. Its combined adversary also controls dishonest participants;
this is not automatically our fixed-environment unilateral-player comparison.

The computational model's submitted transactions contribute directly to the
extracted blockchain. It is not a separate mempool, proposal, inclusion, fork,
and finality model. See its
[runs](https://github.com/omelkonian/formal-bitml-to-bitcoin/blob/ca694260eaf047b1dbe7ece9a972b14d5834f0ee/ComputationalModel/Run.agda)
and [strategies](https://github.com/omelkonian/formal-bitml-to-bitcoin/blob/ca694260eaf047b1dbe7ece9a972b14d5834f0ee/ComputationalModel/Strategy.agda).
We should borrow explicit capabilities, not silently inherit these service
assumptions as facts about a deployed blockchain.

### Useful proof ideas and cryptographic obligations

Appendix A.8 of the original BitML paper reasons from a longest coherent,
strategy-conforming prefix and then analyzes the next computational step.
This is relevant prior art for first-unmatched-step reasoning. Persistence of
published honest authorizations/openings supports particular cases; it is not
a theorem equating all modes of quitting. A small provenance/persistence lemma
for an actually published capability is a useful next operational lemma.

Appendix A.7 also treats copied/related commitments in the Odds--Evens example.
Hiding and binding alone should not be assumed to implement independent source
choices. The construction uses a random-oracle model and restrictions on hash
reuse. The Agda
[coherence hypotheses](https://github.com/omelkonian/formal-bitml-to-bitcoin/blob/ca694260eaf047b1dbe7ece9a972b14d5834f0ee/Coherence/Hypotheses.agda)
make origin and uniqueness conditions explicit. Our future commitment-service
interface must state the relevant malicious-input and related-value guarantees.
The inspected Vegas backend already domain-separates commitments by action,
contract, role, and actor; this comparison does not establish a backend attack,
nor is domain separation itself a cryptographic reduction.

BitML's public reveal guards refer to secrets revealed in the same atomic
branch (thesis printed page 54, PDF page 63). For Vegas, publicly executable
validation is a candidate target-eligibility condition, not a reason to add
BitML constructs to the minimal core language.

### What is and is not mechanized

The thesis explicitly states on printed page 185 (PDF page 194) that run
translation has only partial cases, the strategy-level proof is postulated,
and probabilistic and complexity aspects are omitted in favor of idealized
cryptographic assumptions. The pinned
[computational soundness module](https://github.com/omelkonian/formal-bitml-to-bitcoin/blob/ca694260eaf047b1dbe7ece9a972b14d5834f0ee/SecureCompilation/ComputationalSoundness.agda)
permits unsolved metas, postulates the adversary translation, and contains
unfinished conformance cases. Strategy translation and parsing also contain
postulates. This is substantial operational and compiler work, not a closed
mechanization of the original computational soundness theorem.

There is a further specification caution: the pinned symbolic strategy file's
live persistence condition asks for transition existence, while future
membership in the proposal set is commented out. The intended thesis condition
and the actual checked condition should therefore not be cited interchangeably.
These limits belong in our internal comparison; the paper needs only the
accurate scope distinction, not an inventory of unfinished external proofs.

No license file or applicable license notice was found in the inspected BitML
repositories. Resolve reuse permission before copying or translating source.
The immediate plan is independent implementation of the small relevant ideas,
with scholarly attribution, not importing their code.

## formal-quant: useful assurance engineering, different theorem

The main
[continuous harness theorem](https://github.com/roigecode/formal-quant/blob/cc48cd221200d2c78d920a56e638e5d73fe52c51/theory/VGate/Finance/ContinuousFoundationalHarness.lean#L1452)
concerns valid finite traces from an exact genesis: invariants and producing-event
witnesses for dispatch and rejection. It is a sequential, atomic reference
model with stated signature/snapshot trust. It is not an equilibrium,
compiler-refinement, deployed-runtime, concurrent-execution, or liveness theorem.

FinCore's
[gate equivalence](https://github.com/roigecode/formal-quant/blob/cc48cd221200d2c78d920a56e638e5d73fe52c51/theory/VGate/FinCore/Gate.lean#L329)
checks an effect-free typed expression against a nonempty, root-owned finite
scenario family. Exhaustiveness is relative to that family, not the real
financial world. The separate Rust evaluator and shared fixtures do not supply
a refinement proof. These distinctions are substantially explicit in the
project's own documentation; we should preserve them when comparing results.

Three patterns are worth adapting:

1. **Generated cross-language semantic fixtures.** The
   [v3 interoperability suite](https://github.com/roigecode/formal-quant/blob/cc48cd221200d2c78d920a56e638e5d73fe52c51/interop/pretrade-v3/README.md)
   exports 11 closed Lean traces with events, receipts, and successor states;
   the Rust consumer replays them and regeneration is checked byte-for-byte.
   Our first concrete disclosure/core slice should similarly expose local
   observations, available choices, acceptance/rejection, and settlements to
   Kotlin tests. Do not erase distinct failures before proving their abstraction.
2. **Canonical artifact identity.** Its
   [codec results](https://github.com/roigecode/formal-quant/blob/cc48cd221200d2c78d920a56e638e5d73fe52c51/theory/VGate/FinCore/Canonical.lean#L932)
   separate round-trip/injectivity from semantic preservation. Adopt this
   separation after a concrete Vegas slice fixes the minimal interchange schema;
   do not introduce a second DSL or finance-specific authority framework.
3. **Release proof replay.** Its
   [reproduction](https://github.com/roigecode/formal-quant/blob/cc48cd221200d2c78d920a56e638e5d73fe52c51/scripts/reproduce-foundational.sh)
   and [leanchecker evidence](https://github.com/roigecode/formal-quant/blob/cc48cd221200d2c78d920a56e638e5d73fe52c51/scripts/run-leanchecker-evidence.sh)
   scripts supplement ordinary builds. A fresh release replay and exported exact
   declaration signatures would strengthen our existing paper-claim and axiom
   audits. Neither checks that English prose expresses the intended mathematics.

Fail-closed safety must not be imported as strategic neutrality: rejection can
change information, available choices, fees, and incentives. An invariant under
arbitrary proposals likewise does not imply scheduler irrelevance. Its atomic
race examples are useful assumption tests, not proofs of a concurrent runtime.

The inspected license distinguishes Apache-2.0 software from CC-BY-4.0 research
prose. Preserve the applicable attribution and pinned provenance if material is
reused. No external code has been copied as part of this comparison.

## Next bounded decisions

Keep [the expansion plan](ledger-expansion-plan.md) as the execution order:

- Connect the checked one-shot failure/constant-signal kernels to one actual
  optional-disclosure core encoding, retaining raw protocol observations.
- Test the reveal/timeout race and copied/related-commitment assumptions before
  committing to a general public-delivery interface.
- Generate semantic fixtures when that first slice exists; classify their
  agreement as implementation evidence, not a refinement theorem.
- Prove authorization provenance/persistence only for concrete published
  capabilities. Keep clock progress and inclusion assumptions separate.

Neither comparison establishes a new novelty claim for VegasCore. BitML is
substantive prior art for the intended runtime expansion; formal-quant supplies
engineering patterns rather than a competing strategic-compilation theorem.
Our research contribution still depends on constructing and proving the
information-local compiler comparison for a useful public-interaction fragment.
