# Source quitting and runtime failure

Status: compiler-boundary design, not a proved frontend or cryptographic
realization theorem. Implemented results are in [runtime-models.md](runtime-models.md).
This contract constrains the [paper completion gate](paper-scope.md).

## Ownership

The programmer specifies a game in which quitting already has a meaning.
The frontend's types, handlers, and semantics determine its consequences,
visibility, and effect on later participation. A runtime does not acquire the
right to change that meaning by implementing commitments with messages,
timeouts, or cryptographic checks.

| Boundary | Obligation |
| --- | --- |
| Programmer-facing source | Quitting is defined and subsequent uses respect its consequences. |
| Frontend lowering | The semantic artifact preserves source information, choices, and settlement, including quitting. |
| Runtime compilation | Every admitted implementation strategy is accounted for relative to that same source game and the guarantee being claimed. |

No rich handler syntax or second Vegas typechecker belongs in VegasCore.
Runtime failure modes are not new source constructors. Failure to implement a
source game on a particular target is a compiler eligibility or realization
failure, not permission to silently modify the game.

## Existing code and boundaries

In `../vegas`, `TypeChecker.kt` assigns optional types for explicit null
handlers; non-null handlers, including the implicit burn default, provide
other quitting settlements. It also tracks unrevealed commitments along the
syntactic continuation and rejects a terminal continuation with pending ones.
These are complementary checks, not a requirement that quitting physically
recover a secret from an uncooperative owner.

`semantics/Semantics.kt` supplies quit moves for strategic roles and suppresses
explicit choices after abandonment. `semantics/History.kt` makes `Quit`
visible and retains past observations. Source quitting is therefore not just
a terminal payoff label or a general nullable value: its information and
persistence are part of the semantics to preserve.

The typechecker contains a TODO about validating pending commitments after
burn/split quitting. That comment does not establish either the intended rule
or a soundness bug. Audit actual handler lowering and deferred guards against
source semantics before changing anything. Forcing an adversary to reveal is
not a valid implementation of quitting. The file's introductory no-handler
optionality comment also disagrees with its implemented implicit-burn default;
use executable behavior and tests as evidence, not that summary comment.

In Lean, `RevealComplete` is a syntactic eventual-opening discipline on the
minimal core. It is retained in `WFProgram`. It does not prove correspondence
with Kotlin handlers or completeness of cryptographic failure handling.
`GraphProgram` and `Machine.ofCompiled` already support lower-level graph
construction with weaker prerequisites. An implementation graph may retain
auxiliary secrets, but freshness and liveness alone do not certify it as a
faithful implementation of a checked source game.

## Classify executions, not just error codes

A realization relates runtime states to source states at decision checkpoints.
The relation records the bound value, public and private information, unresolved
obligations, abandonment state, and settlement. Several runtime steps may
implement one source step; administrative steps may be erased.

The following are proof cases, not universal classifications of every backend:

| Runtime behavior | Required accounting |
| --- | --- |
| Valid opening | The corresponding source disclosure and continuation. |
| Explicit refusal | Source quitting at the matching information checkpoint, if refusal is final there. |
| No opening by the deadline | The specified source quit/settlement only under proved delivery and attribution conditions. |
| Invalid opening or malformed request | Rejection and retry, final failure, or another transition according to the actual protocol. An invalid attempt is not automatically quitting. |
| A commitment with no valid opening | An adversarial strategy whose later resolution, observations, and settlement must be compared with source strategies. |
| Censorship of an honest request | An environmental influence, not a unilateral deviation by that honest player. |

An administrative step can leak a signal to future strategies. A state
simulation and equal final balances therefore do not suffice. Retry rights,
information gained before deciding, failure visibility, and later participation
must enter the strategic comparison. A malformed initial commitment may defer
public failure until a later checkpoint, unlike cleartext source quitting.

A private source guard need not be publicly checkable at submission time.
With deferred validation, include invalid commitments until their actual
resolution; do not assume the ideal source guard excludes those runtime
actions. Validating a guarded optional copy is itself a realization obligation,
not a cryptographic primitive already provided by the core.

## Strategic certificate

Let `S` be the unchanged source game and `T_e` the target under a fixed admitted
environment policy `e`. Let `C` translate strategies using their legal information
and `D` project outcomes. The strong exact target is:

1. For every source profile `s`, the law of `D(T_e(C(s)))` equals `S(s)`.
2. For every original player `i` and target replacement `t_i`, a legal source
   replacement, or an explicitly permitted mixture of source replacements,
   gives the same decoded law against the unchanged opponents `s_-i`.
3. The utilities used by the theorem agree through `D`.

`Runtime.DeviationAdequacy` uses a single backtranslation map independent of
the opponent profile. Concrete request-window certificates also support finite
mixtures. Prefer the uniform form when provable; a profile-specific witness is
not the stronger API. Backtranslation must use source information, not the full
runtime state or future observations. It need not identify every runtime error
with one source action at the instant the error occurs.

Quantify over admitted environments without giving the scheduler a utility or
requiring it to respect player equilibrium. Keep the environment fixed between
honest and deviating target comparisons. Censorship-induced quitting does not
by itself supply the honest law or preserve unchanged opponents. Prove a
sufficient delivery condition, establish a different stated guarantee, or
reject that target claim.

Name the deviation class: unilateral Nash preservation is not a coalition
theorem. An honest recipient's guarantee against an arbitrary sender uses the
sender-replacement law and the recipient's source guarantee, without assuming
the sender is rational.

If runtime information prevents exact all-profile comparison, an
equilibrium-local or utility-bound theorem can still suffice. `ConstantSignal`
provides one bounded example. Strictly dominated source quitting alone is not
a general theorem for arbitrary leakage, retries, or later reactions. State
the weaker certificate and its premises; leave the source language unchanged.

Termination and costs belong to this boundary too. Finite private windows
supply bounded resolution in their model. Public delivery needs its own
progress assumptions or accounting for nontermination. Fees and time-dependent
utilities cannot be erased if the claimed source utilities include them.

## Minimal implementation sequence

The finite semantic comparison and runtime composition in steps 2--3 are
checked by `DisclosureCorrespondence`, `DisclosurePayoff`, and
`SealedOfferRuntime`. They retain the restricted, non-frontend boundary below.
The remaining realization work is step 4, not a change to source admission.

1. Keep the source language and `WFProgram` admission fixed. Use the existing
   lower-level graph boundary for encoding experiments.
2. Finish one optional-disclosure comparison: initial binding, public chance,
   source disclosure/quitting, public resolution, and a recipient response.
   Identify full information states and policies, including off-path histories
   and administrative choices. Justify auxiliary hidden bindings by that proof.
3. Compose with the existing runtime certificate without changing payoffs or
   opponents. The Kotlin fixture has additional initial/reply quitting and
   different settlements; include them or retain a restricted, non-frontend result.
4. Add one concrete runtime failure realization with a complete transition
   classification and a named delivery/cryptographic model. Reuse generic
   strategic interfaces rather than adding Vegas-specific failure syntax.

The optional-copy probe is not a checked `WFProgram`, a Kotlin lowering theorem,
or a verified commitment implementation. If a richer source feature cannot be
faithfully encoded in the current checked core subset, that integration gate
remains open. Reclassifying the probe as well-formed would not close it.
