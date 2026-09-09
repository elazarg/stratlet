# Source strategic correspondence

## End-to-end statement

The starting game is `sourceGameForm program.core.prog program.core.env`,
defined independently by structural recursion on `VegasCore`. The target is
the actual compiled request/scheduled protocol, not a second interpretation
defined to call the source evaluator.

The checked correspondence supplies playerwise strategy compilation, a
terminal outcome decoder, and two laws:

1. Every compiled profile has the source profile's decoded outcome law.
2. Every unilateral target deviation has the law of a source deviation, or a
   finite mixture of source deviations, against unchanged
   source opponents.

No utility restriction is needed to state these laws. Utilities over decoded
outcomes then give equilibrium and adversarial-bound corollaries. Additional
trace utilities retain the separate incentive obligations of the runtime theory.

## Checked interfaces

- `Vegas/Core/Strategy.lean`: written-order source policies and finite-law
  interpreter; source support implies `SmallStep.Star`. Policies receive only
  their declared source-visible environment. `Legal` supplies inhabitants.
- `Vegas/Compile/FieldMap.lean`: allocated fields distinguish source variables,
  through initial allocation and compiler extensions.
- `Vegas/Compile/DecisionSite.lean`: structural source decisions locate their
  exact compiled rows; every newly compiled commitment comes from such a site.
- `Vegas/Compile/SourceOrder.lean`: field coverage for arbitrary checked initial
  contexts and compiler extensions; earlier same-owner commitments occur in a
  later decision's declared reads.
- `Vegas/Compile/SourceView.lean`: the declared read environment of a compiled
  commitment is equivalent to its source-visible environment.
- `Vegas/Compile/SourceLaw.lean`: source and declared-read decision kernels
  translate in both directions with exact guarded-law round trips. Agreement
  on a player's visible fields suffices; unrelated sealed fields need not
  already have been written by a parallel execution.
- `Vegas/EventGraph/SourceOrder.lean`: a ready commitment cannot be bypassed by
  a source-later sample or reveal. A later commitment reading its output
  cannot already have completed either.
- `Vegas/EventGraph/Information.lean`: immutable-store extension and recovery
  lemmas; equal completed-node sets and complete visible stores determine the
  current local snapshot. This theorem does not reconstruct remembered history.

## Established whole-program chain

`Compile.SourcePolicy` compiles source decisions into declared-read commitment
kernels and back-translates arbitrary native behavioral policies. The checked
information-locality theorems show that a native decision at an active source
node depends only on the corresponding source view. Compilation and
back-translation commute with unilateral profile updates.

`EventGraph.KernelExecution` executes the actual sample, reveal, and guarded
commit kernels. The commutation, order, product, frontier, and behavioral
modules prove that declared-read laws are invariant under other simultaneously
ready writes, legal node orders have the same law, frontier execution is their
independent product, and native behavioral execution has the canonical
node-order law.

`Compile.SourceExecution` couples each actual graph write to the written-order
source environment. `SourceExecutionGraph`, `SourceExecutionLaw`, and
`SourceExecutionOutcome` prove its graph marginal, source marginal, terminal
decoder identity, and concrete initial-state law. Consequently
`Vegas.ToEventGraph.sourceNativeOutcomeSimulation` is an unrestricted
`OutcomeSimulationOn`: every compiled source profile and every unilateral
native behavioral replacement has exactly the decoded law of its corresponding
source profile or back-translated source replacement.

The scheduled layer preserves honest source laws for every behavioral
scheduler. An arbitrary order-aware player deviation is represented by a
finite mixture of unilateral source-policy deviations against the same honest
opponents. This yields exact source Nash equivalence and observable bounds.
The mixture is profile- and horizon-specific, so it is not falsely presented
as a single uniform `OutcomeSimulationOn` back-translation.

## Scheduling and correlated recommendations

There is no checked compiler counterexample establishing that the admitted
public scheduler breaks correlated equilibrium. Legal graph frontiers require
every active player to supply all ready owned commitments; omission cannot be
used to encode a secret in the canonical graph's checkpoint timing.

`Vegas/Runtime/Correlated.lean` proves that a profile-independent unrestricted
outcome simulation preserves both CE and CCE. CCE is also reflected at compiled
recommendation laws; the CE reflection theorem additionally uses a left inverse
for strategy compilation. `Vegas/Game/SourceCorrelated.lean` instantiates CE
preservation and CCE equivalence for the independent source and native games.
These are not scheduled compiler instances.

The behavioral-scheduler certificate constructs its finite mixture separately
for a fixed deviated profile. CE requires a recommendation-local translation;
profile-local mixture existence alone does not supply it. Thus the checked
scheduled result is a Nash/bound guarantee, not a claimed CE impossibility or
a universal CE transport instance.

## Public-message application

`ApplicationPlan.service_source_public_law` connects the same independent
written-order source denotation to the public-message application. Its
reference execution uses the original source profile's lifted player policies,
the image's serial service, and the image's invocation list. The law observes
completion together with the executable public-terminal readout; it equates
that distribution with successful completion and the source terminal public
projection. It does not reconstruct sealed terminal values from public storage.

The structural backend plan, initial controller-read publicity, and earlier
binding origins are explicit premises. They do not weaken source
well-formedness or assert that every checked source admits this backend plan.
`ForwardCheckpoint` retains an actual run of the original profile and proves
service alignment, cache freshness, exact source-prefix refinement, and
accepted bindings throughout the induction. Source environments and compiler
cursors occur only in these proofs, not as runtime-policy inputs.

This forward law is independent of the source-to-private-request deviation
theorem above. Public-message deviation simulation, including completion or
source-level resolution of silence and malformed commitments under an admitted
service, remains open. A missing or rejected submission can stall the serial
reference execution; its service theorem is not a fairness or timeout theorem.
