# Source strategic correspondence

## Required end-to-end statement

The starting game is `sourceGameForm program.core.prog program.core.env`,
defined independently by structural recursion on `VegasCore`. The target is
the actual compiled request/scheduled protocol, not a second interpretation
defined to call the source evaluator.

A complete theorem needs playerwise strategy compilation, a terminal outcome
decoder, and two laws:

1. Every compiled profile has the source profile's decoded outcome law.
2. Every unilateral target deviation has the law of a source deviation, or an
   appropriately uniform mixture of source deviations, against unchanged
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

## Remaining whole-program proof

Node-local kernels are not the graph game's full strategies. A graph policy
receives `PlayerInformation`, including prior own decisions and snapshots.
The source bridge must establish that this information, at a given source
decision, is determined by the source view. Immutable source bindings retain
past public values and own choices; field coverage and deterministic legal
checkpoints are the relevant invariants. A proof about declared `choiceReads`
alone does not discharge this obligation.

After that information correspondence, a law-level linearization must relate
the graph's legal simultaneous frontiers and internal execution to the
written-order evaluator. Fixed-value store confluence and terminal support
adequacy do not prove this probability-law equality. The strategy maps must
commute with unilateral replacement, so the law result also applies to
deviations. Only then can it compose with the existing graph-to-runtime
certificates to establish the requested source-to-runtime theorem.

`WFProgram.game` currently denotes the compiled graph game. Its existing
runtime theorems therefore do not by themselves establish this independent
source theorem.

## Scheduling and correlated recommendations

There is no checked compiler counterexample establishing that the admitted
public scheduler breaks correlated equilibrium. Legal graph frontiers require
every active player to supply all ready owned commitments; omission cannot be
used to encode a secret in the canonical graph's checkpoint timing.

`Vegas/Runtime/Correlated.lean` proves that a profile-independent unrestricted
outcome simulation preserves both CE and CCE. CCE is also reflected at compiled
recommendation laws; the CE reflection theorem additionally uses a left inverse
for strategy compilation. These are generic certificate consequences, not a
scheduled compiler instance.

The behavioral-scheduler Nash certificate constructs a mixture separately for
a fixed deviated profile. CE requires a recommendation-local translation;
profile-local existence alone does not supply it. A fixed known deterministic
public-history scheduler is a candidate for the stronger certificate because
its orders can be replayed. A randomized scheduler needs a uniform independent
seed construction across recommendation profiles. Neither the missing
certificate nor the presence of an independent signal is an impossibility
proof. A compiler switch should expose proved guarantees of its actual modes,
not encode an unproved claim that parallelization necessarily destroys CE.
