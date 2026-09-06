/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile
import Vegas.EventGraph
import Vegas.Game.Kuhn
import Vegas.Machine
import Vegas.Machine.Contract.SimpleEVMExprCorrect
import Vegas.Runtime
import Vegas.Scheduled

/-!
# General paper-facing claims

The root `Paper.lean` audit target imports this module and adds the concrete
case studies. General compiler theorems remain independent of those examples.
Statements are restated here so that their hypotheses and conclusions can be
audited; proofs delegate to the modules that own the results.

The build checks the statements and pins their axioms. The paper-claim checker
requires a mapping for every numbered theorem and explicitly tagged prose
claim in the active paper. Agreement between mathematical prose and Lean still
requires review: a matching declaration name is not a proof of that agreement.

Two conventions, both load-bearing:

* Statements are spelled out rather than abbreviated behind a definition, even
  where that makes them long.  A reader auditing the paper should not have to
  trust that some `Adequate P` abbreviation says what its name suggests.
* Delegations are one-liners.  If an entry ever needs real proof work, that
  work belongs in the module that owns the concept, not here.
-/

namespace Vegas

namespace Paper

open GameTheory
open GameTheory.Math.Probability
open EventGraph

/-! ## Source adequacy -/

/-- **Source-payoff adequacy** (paper: `thm:source-adequacy`).

Every terminal reachable machine state of a checked program reconstructs a
terminal source environment that the source program can actually reach, and in
which the compiled payoff code and the original source payoff expressions
evaluate to the same vector. -/
theorem source_payoff_adequacy
    {Player : Type} [DecidableEq Player] {L : IExpr}
    (source : WFProgram Player L)
    (state : (Machine.compile source).State)
    (hterminal : (Machine.compile source).terminal state) :
    ∃ terminalEnv :
        VEnv L (ToEventGraph.compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env,
          cont := source.core.prog }
        { ctx := (ToEventGraph.compile source.core).terminalCtx,
          env := terminalEnv,
          cont := .ret
            (ToEventGraph.compile source.core).sourcePayoffs } ∧
      evalPayoffs? (Machine.compile source).payoffs state.1.store =
        some (evalPayoffs
          (ToEventGraph.compile source.core).sourcePayoffs terminalEnv) :=
  Machine.compile_sourceStar source state hterminal

/-! ## Event-graph structure -/

/-- **Schedule confluence** (paper: `thm:confluence`, fixed-result schedules).

Completing a fixed assignment of node values along two orderings of the same
duplicate-free node list reaches the same configuration: independent events
commute, so the reached state depends on *which* nodes ran, not on the order
they ran in. -/
theorem schedule_confluence
    {Player : Type} [DecidableEq Player] {L : IExpr}
    {G : Graph Player L} (cfg : Config G)
    (value : Fin G.nodeCount → TypedValue L)
    {left right : List (Fin G.nodeCount)}
    (hperm : List.Perm left right) (hnodup : left.Nodup) :
    cfg.scheduleComplete value left = cfg.scheduleComplete value right :=
  Config.scheduleComplete_perm cfg value hperm hnodup

/-- Graph observations agree at equal completed-node cuts with fixed values.
This does not identify checkpoints that have completed different node sets. -/
theorem schedule_observation_confluence
    {Player : Type} [DecidableEq Player] {L : IExpr}
    {G : Graph Player L} (cfg : Config G) (who : Player)
    (value : Fin G.nodeCount → TypedValue L)
    {left right : List (Fin G.nodeCount)}
    (hperm : List.Perm left right) (hnodup : left.Nodup) :
    (publicObserve G (cfg.scheduleComplete value left),
        observe G (cfg.scheduleComplete value left) who) =
      (publicObserve G (cfg.scheduleComplete value right),
        observe G (cfg.scheduleComplete value right) who) :=
  congrArg (fun state => (publicObserve G state, observe G state who))
    (Config.scheduleComplete_perm cfg value hperm hnodup)

/-- **Local execution diamond** (paper: `thm:confluence`). Both orders have
supported continuations to equal configurations, not merely equal raw writes. -/
theorem execution_diamond
    {Player : Type} [DecidableEq Player] {L : IExpr}
    {G : Graph Player L} (hwf : G.WF) {cfg leftNext rightNext : Config G}
    (left right : AvailableEvent G cfg) (hne : left.node ≠ right.node)
    (hleft : leftNext ∈ (stepAvailableEvent G cfg left).support)
    (hright : rightNext ∈ (stepAvailableEvent G cfg right).support) :
    ∃ rightAfterLeft : AvailableEvent G leftNext,
      ∃ leftAfterRight : AvailableEvent G rightNext,
        ∃ finalLeft finalRight : Config G,
          finalLeft ∈ (stepAvailableEvent G leftNext rightAfterLeft).support ∧
          finalRight ∈ (stepAvailableEvent G rightNext leftAfterRight).support ∧
          finalLeft = finalRight :=
  supported_available_events_diamond hwf left right hne hleft hright

/-- **What a commit writes does not depend on the configuration**
(paper: `thm:write-determinacy`).

Two availability witnesses for the same commit action, at two arbitrary
configurations, write the same typed value.

This is the operational content behind `schedule_confluence`, and it is what
that theorem needs in order to say anything about execution. Permutation
invariance holds of a *fixed* assignment of node values; using it on a real
round requires that the round have a fixed assignment, which is not automatic.
`CommitAvailable` is `Nonempty (CommitStep ..)`, the protocol layer picks a
witness with `Classical.choice`, and the proposition it picks from mentions the
configuration — so a priori the value written at a node could depend on which
peers ran first, and reordering would not be a permutation of one assignment at
all.

It cannot. A step's row is pinned by `row_get`, its guard by `sem_eq` given the
row, and its value by `value_ok` given the guard: reading the committed value at
the guard's type is a function, not a choice. The configuration appears only in
`ready`, `env` and `guard_ok` — in *whether* the step exists, never in what it
writes. So the noncomputable selection is a selection among witnesses that all
agree on the one thing the semantics reads off them. -/
theorem commit_writes_are_configuration_independent
    {Player : Type} [DecidableEq Player] {L : IExpr}
    {G : EventGraph.Graph Player L} {left right : EventGraph.Config G}
    {who : Player} {action : EventGraph.CommitAction G who}
    (stepLeft : EventGraph.CommitStep G left who action)
    (stepRight : EventGraph.CommitStep G right who action) :
    (⟨stepLeft.guard.ty, stepLeft.value⟩ : EventGraph.TypedValue L) =
      ⟨stepRight.guard.ty, stepRight.value⟩ :=
  EventGraph.CommitStep.written_eq stepLeft stepRight

/-- **A legal packet determines what each node receives**
(paper: `thm:packet-determinacy`).

Two coordinates of a legal frontier packet cannot disagree at a node, because
they cannot both write one: a commit node names its owner, and
`FrontierAction.Available` forces a player to leave `none` at every node outside
its own ready frontier.

This is the packet-level half of write determinacy, and
`commit_writes_are_configuration_independent` is the configuration-level half.
Together they say the write at a node is a function of the packet alone: not of
which coordinate is consulted, and not of which peers have already run. That is
what upgrades `schedule_confluence` from a statement about a fixed assignment
into a statement about a round. -/
theorem legal_packet_determines_each_write
    {Player : Type} [DecidableEq Player] {L : IExpr}
    {G : EventGraph.Graph Player L} {cfg : EventGraph.Config G}
    {joint : ∀ who, Option (EventGraph.FrontierAction G who)}
    (hlegal : ∀ who action, joint who = some action →
      EventGraph.FrontierAction.Available G cfg who action)
    {node : Fin G.nodeCount} {whoLeft whoRight : Player}
    {actionLeft : EventGraph.FrontierAction G whoLeft}
    {actionRight : EventGraph.FrontierAction G whoRight}
    {valueLeft valueRight : L.Val (G.nodeRow node).ty}
    (hactionLeft : joint whoLeft = some actionLeft)
    (hactionRight : joint whoRight = some actionRight)
    (hvalueLeft : actionLeft.value? node = some valueLeft)
    (hvalueRight : actionRight.value? node = some valueRight) :
    valueLeft = valueRight :=
  EventGraph.FrontierAction.legal_write_unique hlegal
    hactionLeft hactionRight hvalueLeft hvalueRight

/-- **Commit–reveal barrier** (paper: `thm:fence`).

A reveal node is ordered behind every source-earlier commit: such a commit is
a graph prerequisite of the reveal, so a ready reveal has all of them already
completed.

Deliberately graph-local.  It asserts nothing about cryptographic hiding, does
not force a reveal transaction to be sent, and does not suppress target-only
timing information. -/
theorem commit_reveal_barrier
    {Player : Type} [DecidableEq Player] {L : IExpr}
    (G : Graph Player L)
    {node prior : Fin G.nodeCount}
    {event priorEvent : EventNode Player L} {source : Nat}
    {who : Player} {guard : EventGuard L}
    (hnode : G.nodes[node]? = some event)
    (hprior : G.nodes[prior]? = some priorEvent)
    (hlt : (prior : Nat) < (node : Nat))
    (hreveal : event.sem = .reveal source)
    (hcommit : priorEvent.sem = .commit who guard) :
    prior ∈ G.prereqs node :=
  G.prior_commit_mem_prereqs_of_reveal hnode hprior hlt hreveal hcommit

/-- **Ready reveals have completed their commitment fence** (paper: `thm:fence`). -/
theorem ready_reveal_fence
    {Player : Type} [DecidableEq Player] {L : IExpr}
    (G : Graph Player L) (cfg : Config G) {node prior : Fin G.nodeCount}
    {event priorEvent : EventNode Player L} {source : Nat}
    {who : Player} {guard : EventGuard L}
    (hnode : G.nodes[node]? = some event) (hprior : G.nodes[prior]? = some priorEvent)
    (hlt : (prior : Nat) < (node : Nat)) (hreveal : event.sem = .reveal source)
    (hcommit : priorEvent.sem = .commit who guard) (hready : Ready G cfg node) :
    prior ∈ cfg.done :=
  hready.2 (G.prior_commit_mem_prereqs_of_reveal hnode hprior hlt hreveal hcommit)

/-! ## Scheduling discipline

The compiler's choice of checkpoint policy is what decides whether the realized
order is a strategic degree of freedom.  These two entries are a genuine
separation, not a restatement: the sequential policy determines the
completed-node trajectory, and the permissive one provably does not. -/

/-- **The sequential schedule carries no information.**

Under `sequentialCheckpointPolicy`, checkpoints that have completed the same
nodes advance to checkpoints that have completed the same nodes — across
different runs and whatever values the players and nature wrote.  So the
completed-node trajectory is a function of the graph alone, and a target
strategy has no scheduler choice to condition on.

Scope, stated precisely because it is easy to overstate: this is a theorem
about `CheckpointPolicy`, and the compiled game is currently built by
`toExecutionProtocol`, which does **not** consume a checkpoint policy.  So this
does not yet license the order-free `PublicObservation` used by
`Machine.Program.observation`; connecting the two is open work. -/
theorem sequential_schedule_determined
    {Player : Type} [DecidableEq Player] {L : IExpr}
    {G : Graph Player L}
    {srcLeft srcRight dstLeft dstRight : ReachableConfig G}
    (hsrc : srcLeft.1.done = srcRight.1.done)
    (hleft : (sequentialCheckpointPolicy G).allowed srcLeft dstLeft)
    (hright : (sequentialCheckpointPolicy G).allowed srcRight dstRight) :
    dstLeft.1.done = dstRight.1.done :=
  sequentialCheckpointPolicy_done_congr hsrc hleft hright

/-- **The permissive schedule does not.**

Wherever two distinct nodes are simultaneously ready,
`primitiveDownsetCheckpointPolicy` allows two checkpoints from one source whose
completed-node sets differ.  Under that policy the realized order is a real
scheduler choice, and on a public runtime it is observable — which is what
enlarges the target strategy carrier beyond `Info → Action`. -/
theorem permissive_schedule_not_determined
    {Player : Type} [DecidableEq Player] {L : IExpr}
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    {src : ReachableConfig G} {left right : Fin G.nodeCount}
    (hne : left ≠ right)
    (hleft : Ready G src.1 left) (hright : Ready G src.1 right) :
    ∃ dstLeft dstRight : ReachableConfig G,
      (primitiveDownsetCheckpointPolicy G).allowed src dstLeft ∧
        (primitiveDownsetCheckpointPolicy G).allowed src dstRight ∧
          dstLeft.1.done ≠ dstRight.1.done :=
  primitiveDownsetCheckpointPolicy_done_not_determined hwf hguards hne
    hleft hright

/-! ## Code generation -/

/-- **Word code generation is correct.**

Compiled word-expression code pushes exactly the value its IR denotes and
leaves the rest of the stack untouched, for any variable-loading fragment that
is itself correct.

The arithmetic here is the machine's, not an idealization: `Val .word` is
`BitVec 256`, its `+`, `-` and `*` wrap modulo `2 ^ 256`, and the proof runs
against the executable interpreter `stepInstruction`.  In particular the
operand-order discipline is discharged rather than assumed — `SUB` reads its
minuend from the top of the stack, so `compile` emits its operands in the
opposite order from `ADD`, and the composition lemmas fix that per operation. -/
theorem word_codegen_correct
    {Γ : CtxSimple}
    (pre : Machine.Contract.EVM.BoolExprPrecondition)
    (maxStack : Nat)
    (variableCode : Machine.Contract.EVM.VariableCode Γ)
    (env : PlainEnv Γ)
    (hvariable :
      Machine.Contract.EVM.VariableCodeCorrect pre env variableCode)
    (source : Expr Γ .word) (code : Machine.Contract.EVM.Assembly)
    (hcompile :
      Machine.Contract.EVM.compileWordExpr? maxStack variableCode source
        = some code) :
    Machine.Contract.EVM.WordExprCorrect pre (evalExpr source env) code :=
  Machine.Contract.EVM.compileWordExpr?_correct pre maxStack variableCode env
    hvariable source code hcompile

/-- **Boolean guard code generation is correct.**

Whenever `compileBoolExpr?` accepts a source Boolean expression, the assembly it
emits pushes exactly that expression's canonical Boolean word.

This is the statement that matters for commit guards, since a guard is what a
player's proposed action is checked against.  It now covers guards that compare
*word arithmetic* — `x + y < z`, `x * y = z` — not only Boolean connectives,
because `BoolExprIR` carries `wordEqual` and `wordLess` over `WordExprIR`.

`VariableCodeCorrect` is one hypothesis for both types: a loading fragment must
push `encodeSimpleValue τ` of the variable's value, which is `encodeBool` at
`.bool` and the identity at `.word`. -/
theorem guard_codegen_correct
    {Γ : CtxSimple}
    (pre : Machine.Contract.EVM.BoolExprPrecondition)
    (maxStack : Nat)
    (variableCode : Machine.Contract.EVM.VariableCode Γ)
    (env : PlainEnv Γ)
    (hvariable :
      Machine.Contract.EVM.VariableCodeCorrect pre env variableCode)
    (source : Expr Γ .bool) (code : Machine.Contract.EVM.Assembly)
    (hcompile :
      Machine.Contract.EVM.compileBoolExpr? maxStack variableCode source
        = some code) :
    Machine.Contract.EVM.BoolExprCorrect pre (evalExpr source env) code :=
  Machine.Contract.EVM.compileBoolExpr?_correct pre variableCode env
    hvariable source code maxStack hcompile

/-! ## Game extraction

The strategic object a checked program denotes, and the two structural facts
every downstream equilibrium result depends on.  Both were claimed in prose
before being listed here, which is exactly the failure this file exists to
prevent. -/

/-- **Compiled information has perfect recall** (paper: `thm:perfect-recall`).

A player's information state remembers its own earlier information and actions,
while abstracting from event ordering that does not concern it.

This is the hypothesis the Kuhn correspondence below runs on: without it
behavioral and mixed presentations are not interchangeable, and the Nash
transport in `kuhn_behavioral_to_mixedPure` does not hold. -/
theorem compiled_perfect_recall
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (program : WFProgram Player L) :
    (Machine.compile program).information.PerfectRecall :=
  (Machine.compile program).perfectRecall

/-- **Compiled execution has a bounded horizon** (paper: `thm:bounded`).

The graph's node count bounds every strategy's play length uniformly. Finiteness
here is structural rather than assumed: a Vegas program is a finite graph, and
each step strictly grows the completed set.

Boundedness is what makes the extracted game a *finite* object, so the
equilibrium notions below are the finite ones. -/
theorem compiled_bounded_horizon
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (program : WFProgram Player L) :
    (Machine.compile program).execution.BoundedHorizon
      (Machine.compile program).graph.nodeCount :=
  (Machine.compile program).boundedHorizon

/-- **The extracted arena is a bounded stochastic game** (paper: `thm:arena`).

The `Game` a checked program denotes carries its own horizon proof, so the
strategic view is bounded by construction rather than by a side condition a
consumer must re-establish.

Note what this is not. The arena is *defined* as a first-order stochastic game
in `Vegas.Game`; there is no separate proved translation from a native frontier
game into the FOSG interface, and prose describing one would be wrong. The
FOSG-to-extensive-form results the paper leans on are `GameTheory`'s, not this
development's, and belong to that library in any attribution. -/
theorem extracted_arena_is_bounded
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (program : WFProgram Player L) [FiniteDomains program] :
    program.game.arena.execution.BoundedHorizon program.game.horizon :=
  program.game.bounded

/-! ## Strategy presentations -/

/-- **Frontier Kuhn correspondence, behavioral to mixed-pure**
(paper: `thm:kuhn`).

Every checked finite-domain program has a deviation-adequacy certificate from
its behavioral frontier game to its mixed-pure frontier game: a profile
translation preserving outcome laws, together with a back-translation matching
every unilateral target replacement. -/
theorem kuhn_behavioral_to_mixedPure
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (program : WFProgram Player L) [FiniteDomains program] :
    Nonempty
      (Runtime.DeviationAdequacy program.game.behavioral
        program.game.mixedPure) :=
  ⟨program.behavioralToMixedPureAdequacy⟩

/-- **Frontier Kuhn correspondence, mixed-pure to behavioral**
(paper: `thm:kuhn`, converse direction). -/
theorem kuhn_mixedPure_to_behavioral
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (program : WFProgram Player L) [FiniteDomains program] :
    Nonempty
      (Runtime.DeviationAdequacy program.game.mixedPure
        program.game.behavioral) :=
  ⟨program.mixedPureToBehavioralAdequacy⟩

/-- **A compiled strategic round is atomic** (paper: `thm:atomic`).

At a strategic checkpoint with no ready internal work, the round's successor is
a point mass determined by the joint packet alone. The whole frontier is applied
as one action.

This is what the compiler does *instead of* serializing, and it is the reason
the scheduling results below apply to it only vacuously. There is no scheduler
coordinate in this protocol to enforce, restrict, or reason about: a schedule is
not chosen, so it cannot be observed, and no strategy can condition on one. That
is strictly stronger observationally than
`enforced_schedule_removes_order_choice`, which neutralizes an existing
scheduling coordinate.

The canonical node order inside `applyFrontier` is therefore an implementation
detail rather than a semantic commitment — it is invisible at this interface,
which exposes only the packet and the resulting configuration.

What this does **not** say is that a serialized runtime is equivalent.  The
graph-derived serializers below make that comparison precise: a permissive one
publishes a genuine scheduler choice, while a fixed-order one removes that choice.
Neither fact alone is an equilibrium-equivalence theorem. -/
theorem compiled_round_is_atomic
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (G : EventGraph.Graph Player L) (hwf : G.WF) (hguards : EventGraph.GuardLive G)
    (state : EventGraph.ReachableConfig G)
    (legal : { joint : ∀ who, Option (EventGraph.FrontierAction G who) //
      (EventGraph.toExecutionProtocol G hwf hguards).Legal state joint })
    (noInternal : EventGraph.readyInternalNodes G state.1 = ∅) :
    (EventGraph.toExecutionProtocol G hwf hguards).step state legal =
      FinDist.pure (EventGraph.applyFrontier G hwf state legal.1) :=
  EventGraph.toExecutionProtocol_step_eq_pure_applyFrontier
    G hwf hguards state legal noInternal

/-- **One compiled graph, with atomic and serialized runtime disciplines**
(paper: `thm:two-runtimes`).

For the same well-formed live graph, the compiled protocol resolves a strategic
round as a point mass determined by the joint packet.  The permissive serializer
accepts every duplicate-free ordering of the players active at that public
view, executes automatic internal events to a stable checkpoint, and has a real
scheduler choice whenever two such orders are exhibited.  Its player effects
are proved to commute.  The fixed-order serializer filters the public activity
test and sorts by a backend-supplied `LinearOrder`; that policy is executable
and the resulting scheduler is proved enforcing.

The menu cannot be a function of the public view alone: a player's legal
frontier is fixed by its own observation, which includes values sealed to it,
while `publicObserve` sees only unowned fields. The scheduled model therefore
uses the player's private observation for its action menu, while the scheduler
may inspect the complete public observation but no sealed value or same-round
submission.

The scheduler coordinate is operational machinery, not an additional member of
the source game's equilibrium population.  Its observation is recoverable from
every player's observation (`compiled_scheduler_has_no_extra_information`).
The separate signal theorems quantify over every deviation of the original
players, including arbitrary deviations conditioned on an independent signal.
They do not by themselves interpret an executing public-history scheduler. -/
theorem compiled_runtime_scheduling_boundary
    {Player : Type} [Fintype Player] [LinearOrder Player] {L : IExpr}
    (G : EventGraph.Graph Player L) (hwf : G.WF) (hguards : EventGraph.GuardLive G)
    {seen : EventGraph.PublicObservation G} {left right : List Player}
    (hleft : left ∈ (Compiled.serializedSystem G hwf hguards).schedules seen)
    (hright : right ∈ (Compiled.serializedSystem G hwf hguards).schedules seen)
    (hne : left ≠ right) :
    (∀ (state : EventGraph.ReachableConfig G)
        (legal : { joint : ∀ who, Option (EventGraph.FrontierAction G who) //
          (EventGraph.toExecutionProtocol G hwf hguards).Legal state joint }),
        EventGraph.readyInternalNodes G state.1 = ∅ →
          (EventGraph.toExecutionProtocol G hwf hguards).step state legal =
            FinDist.pure (EventGraph.applyFrontier G hwf state legal.1)) ∧
      (∀ (state : (Compiled.serializedSystem G hwf hguards).State)
          (legal : { joint //
            (Compiled.serializedSystem G hwf hguards).toExecutionProtocol.Legal
              state joint })
          (next : (Compiled.serializedSystem G hwf hguards).State),
        next ∈ ((Compiled.serializedSystem G hwf hguards).toExecutionProtocol.step
            state legal).support →
          EventGraph.readyInternalNodes G next.base.1 = ∅) ∧
      ¬ (Compiled.serializedSystem G hwf hguards).EnforcesOrder ∧
      (Compiled.fixedSerializedSystem G hwf hguards).EnforcesOrder :=
  ⟨fun state legal noInternal =>
      EventGraph.toExecutionProtocol_step_eq_pure_applyFrontier
        G hwf hguards state legal noInternal,
    fun state legal _next hnext =>
      Compiled.serializedSystem_step_support_no_internal
        G hwf hguards state legal hnext,
    Compiled.serializedSystem_not_enforcesOrder G hwf hguards
      hleft hright hne,
    Compiled.fixedSerializedSystem_enforcesOrder G hwf hguards⟩

/-- **The compiled scheduler has no information unavailable to a player.**

The scheduler sees exactly `publicObserve`.  Every original player's local
observation contains that same value as its first component, so scheduling may
use all observable game data without becoming a channel for sealed data.  This
is a pre-round statement: simultaneous player submissions are not an input to
the scheduler observation. -/
theorem compiled_scheduler_has_no_extra_information
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (G : EventGraph.Graph Player L) (hwf : G.WF)
    (hguards : EventGraph.GuardLive G) :
    (Compiled.serializedSystem G hwf hguards).SchedulerHasNoExtraInformation :=
  Compiled.serializedSystem_schedulerHasNoExtraInformation G hwf hguards

/-- **The scheduler's complete information is player-computable.**

The state-level projection above extends through every runtime trace.  An
original player's perfect-recall information determines the scheduler's
current public observation, every earlier public observation and order, and
the scheduler's own remembered choices.  Thus its order cannot transmit a
private state fact: there is none in its information state. -/
theorem compiled_scheduler_information_is_player_computable
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (G : EventGraph.Graph Player L) (hwf : G.WF)
    (hguards : EventGraph.GuardLive G) (who : Player)
    {state : (Compiled.serializedSystem G hwf hguards).toExecutionProtocol.State}
    (trace : GameTheory.Protocol.ExecutionProtocol.Trace
      (Compiled.serializedSystem G hwf hguards).toExecutionProtocol state) :
    (Compiled.serializedSystem G hwf hguards).schedulerInfoFromPlayer
        (fun seen : EventGraph.PublicObservation G ×
          EventGraph.Observation G who => seen.1)
        ((Compiled.serializedSystem G hwf hguards).revealingSignals.infoOf
          (.player who) trace) =
      (Compiled.serializedSystem G hwf hguards).revealingSignals.infoOf
        (.scheduler : Participant Player) trace :=
  Compiled.serializedSystem_schedulerInfo_eq_fromPlayer
    G hwf hguards who trace

/-- **Permissive serialization preserves the compiled graph's base effect.**

All accepted orders of a legal player frontier reach the same law over settled
reachable graph configurations.  The theorem deliberately forgets the public
schedule log, which still distinguishes different orders. -/
theorem compiled_permissive_effects_commute
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (G : EventGraph.Graph Player L) (hwf : G.WF)
    (hguards : EventGraph.GuardLive G) :
    (Compiled.serializedSystem G hwf hguards).EffectsCommute :=
  Compiled.serializedSystem_effectsCommute G hwf hguards

/-- **Every accepted serialized round implements the atomic source round.**

This is stronger than pairwise scheduler confluence. For a source-legal joint
frontier, the runtime's chosen player order reaches exactly `applyFrontier`, not
merely an order-independent target state. Resolving the runtime round then
applies the same automatic closure to that exact source successor. Each step of
that closure is itself an ordinary source-protocol internal transition
(`Compiled.settleInternal_succ_eq_source_step`). -/
theorem compiled_serialized_round_implements_atomic
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (G : EventGraph.Graph Player L) (hwf : G.WF)
    (hguards : EventGraph.GuardLive G)
    (state : EventGraph.ReachableConfig G)
    (joint : ∀ who, Option (EventGraph.FrontierAction G who))
    (hlegal : (EventGraph.toExecutionProtocol G hwf hguards).Legal state joint)
    {order : List Player}
    (horder : order ∈
      (Compiled.serializedSystem G hwf hguards).schedules
        (EventGraph.publicObserve G state.1)) :
    Compiled.applySerializedOrder joint order state =
        EventGraph.applyFrontier G hwf state joint ∧
      (Compiled.serializedSystem G hwf hguards).resolveOrder
          ((Compiled.serializedSystem G hwf hguards).withSchedule order joint)
          order state =
        (Compiled.serializedSystem G hwf hguards).settle
          (EventGraph.applyFrontier G hwf state joint) :=
  ⟨Compiled.applySerializedOrder_eq_applyFrontier
      G hwf hguards state joint hlegal horder,
    Compiled.serializedSystem_resolveOrder_eq_settle_atomicFrontier
      G hwf hguards state joint hlegal horder⟩

/-- **With fixed-order serialization, player submissions determine the step.**

For the fixed-order serializer of a compiled graph, two legal joint submissions
that agree on every original player's action induce exactly the same successor
law.  This is stronger than base-state commutation: the public schedule log is
equal as well, because the scheduler has only one accepted order. -/
theorem compiled_fixed_order_step_determined_by_players
    {Player : Type} [Fintype Player] [LinearOrder Player] {L : IExpr}
    (G : EventGraph.Graph Player L) (hwf : G.WF)
    (hguards : EventGraph.GuardLive G)
    {state : (Compiled.fixedSerializedSystem G hwf hguards).State}
    {left right : { joint //
      (Compiled.fixedSerializedSystem G hwf hguards).toExecutionProtocol.Legal
        state joint }}
    (hplayers : ∀ who,
      left.1 (.player who) = right.1 (.player who)) :
    (Compiled.fixedSerializedSystem G hwf hguards).toExecutionProtocol.step
        state left =
      (Compiled.fixedSerializedSystem G hwf hguards).toExecutionProtocol.step
        state right :=
  Compiled.fixedSerializedSystem_step_determined_by_players
    G hwf hguards hplayers

/-- **Player deviation adequacy preserves and reflects Nash under every fixed
adversarial scheduler.**

The target protocol may contain a scheduler coordinate with arbitrary strategy
and utility types.  Adequacy constrains neither: it fixes that coordinate and
requires exact outcome-law back-translation only for deviations by original
players.  The equivalence therefore covers every technically available player
deviation without treating implementation machinery as part of the equilibrium
population. -/
theorem player_deviation_adequacy_nash_equivalence
    {Player : Type} [DecidableEq Player]
    {source : UtilityGame Player}
    {target : UtilityGame (Participant Player)}
    {Considered : (who : Player) →
      target.form.sig.Strategy (.player who) → Prop}
    (adequacy : Scheduled.PlayerDeviationAdequacyOn
      source target Considered)
    (scheduler : target.form.sig.Strategy
      (.scheduler : Participant Player))
    (profile : Profile source.form.sig) :
    Scheduled.IsPlayerNashAgainst target Considered
        (adequacy.compileProfile scheduler profile) ↔
      IsNash source.form (euPreference source.utility) profile :=
  adequacy.isPlayerNashAgainst_compileProfile_iff scheduler profile

/-- **An independent schedule signal preserves Nash equilibrium among the
original players, even against arbitrary signal-aware deviations.**

The scheduler signal and scheduler utility are arbitrary.  Target players have
the strictly richer strategy type `Signal → source strategy`, so a dishonest
player may condition on the schedule.  For each fixed adversarial signal that
plan back-translates to its value at the signal.  Because player utility ignores
the signal, player-only Nash in the implementation is equivalent to source
Nash.  No equilibrium or incentive claim is made about the scheduler. -/
theorem independent_schedule_signal_preserves_player_nash
    {Player : Type} [DecidableEq Player]
    (source : UtilityGame Player) (Signal : Type)
    (schedulerUtility : Signal × source.form.sig.Outcome → ℝ)
    (signal : Signal) (profile : Profile source.form.sig) :
    Scheduled.IsPlayerNash
        (Scheduled.IndependentSignal.game source Signal schedulerUtility)
        ((Scheduled.IndependentSignal.playerDeviationAdequacy
          source Signal schedulerUtility).compileProfile signal profile) ↔
      IsNash source.form (euPreference source.utility) profile :=
  Scheduled.IndependentSignal.isPlayerNash_iff
    source Signal schedulerUtility signal profile

/-- **Random independent schedule signals also preserve and reflect player
Nash.** A target deviation may choose a different complete source strategy for
every signal. Its expected payoff is an average of ordinary source-deviation
payoffs, so no exact single-strategy law back-translation is needed. -/
theorem random_independent_schedule_signal_preserves_player_nash
    {Player : Type} [DecidableEq Player]
    (source : UtilityGame Player) (Signal : Type)
    (schedulerUtility : Signal × source.form.sig.Outcome → ℝ)
    (signalLaw : FinDist Signal) (profile : Profile source.form.sig) :
    Scheduled.IsPlayerNash
        (Scheduled.RandomIndependentSignal.game
          source Signal schedulerUtility)
        (Scheduled.RandomIndependentSignal.compiledProfile
          source Signal signalLaw profile) ↔
      IsNash source.form (euPreference source.utility) profile :=
  Scheduled.RandomIndependentSignal.isPlayerNash_iff
    source Signal schedulerUtility signalLaw profile

/-- **A fixed public-information scheduler adds no distinctions between
order-blind histories.** Replay executes the scheduler on the player's
order-free observation history, reconstructing its previous choices. Both
traces may contain arbitrary player deviations and chance outcomes. -/
theorem public_scheduler_adds_no_history_information
    {Player : Type} (sys : ScheduledSystem Player) (who : Player)
    (scheduler : sys.revealingInformation.Policy .scheduler)
    (project : sys.Obs who → sys.SchedulerView)
    (hproject : ∀ state, project (sys.obs state who) = sys.schedulerView state)
    {first second : sys.toExecutionProtocol.State}
    (left : sys.toExecutionProtocol.Trace first)
    (right : sys.toExecutionProtocol.Trace second)
    (hleft : sys.SchedulerFollows scheduler left)
    (hright : sys.SchedulerFollows scheduler right) :
    sys.revealingSignals.infoOf (.player who) left =
        sys.revealingSignals.infoOf (.player who) right ↔
      sys.blindSignals.infoOf (.player who) left =
        sys.blindSignals.infoOf (.player who) right :=
  sys.revealing_info_eq_iff_blind_info_eq scheduler project hproject left right hleft hright

/-- **Order-blind replay preserves the full execution law under a fixed
public-information scheduler.** Every original player may use an arbitrary
behavioral policy. The translated policy simulates the scheduler locally,
independently of opponents' policies. The order-blind model retains the full
observation history. For compiled graph games,
`compiled_compact_information_sufficient` connects it to compact source information. -/
theorem public_scheduler_replay_preserves_behavioral_law
    {Player : Type} [Fintype Player] (sys : ScheduledSystem Player)
    (scheduler : sys.revealingInformation.Policy .scheduler)
    (project : (who : Player) → sys.Obs who → sys.SchedulerView)
    (hproject : ∀ state who, project who (sys.obs state who) = sys.schedulerView state)
    (profile : (who : Participant Player) → sys.revealingInformation.BehavioralPolicy who)
    (hscheduler : profile .scheduler = scheduler.toBehavioral)
    (fuel : Nat) :
    sys.revealingInformation.runBehavioral profile fuel =
      sys.revealingInformation.runBehavioral
        (sys.replayBehavioralProfile scheduler project profile) fuel :=
  sys.runBehavioral_replay scheduler project hproject profile hscheduler fuel

/-- **Randomly selected, actually executing public-history scheduler
policies also permit exact replay.** The policy-selection randomness is
independent of subsequent player/chance draws, not the realized orders.
Translated players may use the selected policy as an independent seed. -/
theorem random_public_scheduler_replay_preserves_law
    {Player : Type} [Fintype Player] (sys : ScheduledSystem Player)
    (schedulers : FinDist (sys.revealingInformation.Policy .scheduler))
    (project : (who : Player) → sys.Obs who → sys.SchedulerView)
    (hproject : ∀ state who, project who (sys.obs state who) = sys.schedulerView state)
    (profile : (who : Participant Player) → sys.revealingInformation.BehavioralPolicy who)
    (fuel : Nat) :
    (schedulers.bind fun scheduler => sys.revealingInformation.runBehavioral
      (sys.fixScheduler scheduler profile) fuel) =
        schedulers.bind fun scheduler => sys.revealingInformation.runBehavioral
          (sys.replayBehavioralProfile scheduler project profile) fuel :=
  sys.runMixedScheduler_replay schedulers project hproject profile fuel

/-- **The compiler-derived serializer is an actual finite informed game.**

Its scheduler sees the public graph observation but no sealed values or
same-round submissions; the published order remains in the history;
original-player utility reads only the settled graph state; every participant
has perfect recall; and every strategy profile terminates within the graph-node
horizon. The final two conjuncts are the compiler-specific confluence theorem
for every accepted order and the proof that the scheduler sees no state
information unavailable to an original player. -/
theorem compiled_serialized_game_wellFormed
    {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
    (program : Machine.Program Player L)
    (schedulerUtility : program.serializedArena.History → ℝ) :
    program.serializedArena.information.PerfectRecall ∧
      (program.serializedGame schedulerUtility).arena.execution.BoundedHorizon
        program.graph.nodeCount ∧
      program.serializedSystem.EffectsCommute ∧
      program.serializedSystem.SchedulerHasNoExtraInformation :=
  ⟨program.serializedPerfectRecall,
    program.serializedBoundedHorizon schedulerUtility,
    Compiled.serializedSystem_effectsCommute
      program.graph program.graphWF program.guardLive,
    Compiled.serializedSystem_schedulerHasNoExtraInformation
      program.graph program.graphWF program.guardLive⟩

/-- **Every serialized history has a source history with the same state,
erased player information, and original-player payoff.** This quantifies over
all legal traces, not only honest or equilibrium play. It is a trace theorem,
not a profile-consistent back-translation of arbitrary runtime strategies. -/
theorem compiled_serialized_history_has_source
    {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
    (program : Machine.Program Player L)
    (target : program.serializedArena.History)
    (schedulerUtility : program.serializedArena.History → ℝ) :
    ∃ source : program.execution.History,
      source.state = target.state.base ∧
      (∀ who, program.information.infoOf who source.trace =
        program.eraseSerializedPlayerInformation who
          (program.serializedArena.information.infoOf (.player who) target.trace)) ∧
      ∀ who, program.utility source who =
        program.serializedUtility schedulerUtility target (.player who) :=
  program.serializedHistory_has_source target schedulerUtility

/-- **Exact one-round law on state and all players' source information.**
Automatic runtime settlement expands into actual atomic source histories,
with the same probability law after erasing runtime ordering. This applies
to every legal joint submission, including every accepted scheduler order. -/
theorem compiled_serialized_round_information_law
    {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
    (program : Machine.Program Player L)
    (source : program.execution.History) (log : List (List Player))
    (trace : program.serializedArena.execution.Trace ⟨source.state, log⟩)
    (hinfo : ∀ who, program.information.infoOf who source.trace =
      program.eraseSerializedPlayerInformation who
        (program.serializedArena.information.infoOf (.player who) trace))
    (command : {joint // program.serializedArena.execution.Legal
      ⟨source.state, log⟩ joint}) :
    (program.expandRound source (fun who => command.1 (.player who))
        (program.serializedPlayers_legal command)).map program.historySummary =
      ((program.serializedArena.execution.step ⟨source.state, log⟩ command).bindOnSupport
        fun _ realized => FinDist.pure
          ((⟨⟨source.state, log⟩, trace⟩ : program.serializedArena.History).extend
            command.2 realized)).map program.serializedHistorySummary :=
  program.expandRound_map_summary source log trace hinfo command

/-- **The history expansion also matches a round of actual behavioral play.**
Both players and scheduler may use arbitrary runtime-information-local
randomized policies. The expanded source law still uses the runtime's joint
submission law; no source-profile back-translation is asserted here. -/
theorem compiled_serialized_behavioral_round_expands
    {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
    (program : Machine.Program Player L)
    (source : program.execution.History) (log : List (List Player))
    (trace : program.serializedArena.execution.Trace ⟨source.state, log⟩)
    (hinfo : ∀ who, program.information.infoOf who source.trace =
      program.eraseSerializedPlayerInformation who
        (program.serializedArena.information.infoOf (.player who) trace))
    (policies : (who : Participant Player) →
      program.serializedArena.information.BehavioralPolicy who)
    (hterm : ¬ program.serializedArena.execution.terminal ⟨source.state, log⟩) :
    (program.serializedArena.information.runBehavioralFrom policies 1
        ⟨⟨source.state, log⟩, trace⟩).map program.serializedHistorySummary =
      ((program.serializedArena.information.behavioralJoint policies trace hterm).bind
        fun command => program.expandRound source
          (fun who => command.1 (.player who))
          (program.serializedPlayers_legal command)).map program.historySummary :=
  program.serializedBehavioralRound_expands source log trace hinfo policies hterm

/-- **Compact source information is sufficient for runtime order-free recall.**
This holds on all legal runtime histories, without choosing opponents' policies
or strengthening the canonical source information model. -/
theorem compiled_compact_information_sufficient
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (program : Machine.Program Player L) (who : Player)
    {left right : program.serializedArena.execution.State}
    (first : program.serializedArena.execution.Trace left)
    (second : program.serializedArena.execution.Trace right)
    (hcompact : program.eraseSerializedPlayerInformation who
        (program.serializedArena.information.infoOf (.player who) first) =
      program.eraseSerializedPlayerInformation who
        (program.serializedArena.information.infoOf (.player who) second)) :
    program.serializedSystem.blindSignals.infoOf (.player who) first =
      program.serializedSystem.blindSignals.infoOf (.player who) second :=
  program.serializedBlindInfo_eq_of_compact_eq who first second hcompact

/-- **Complete terminal-state law of the actual serialized implementation.**
The scheduler can randomize and react to public observations. No realized-order
independence hypothesis or finite-domain hypothesis is needed. -/
theorem compiled_serialized_behavioral_law
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (program : Machine.Program Player L)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) :
    (program.serializedArena.information.runBehavioral
      (program.compileSerializedBehavioralProfile scheduler profile) program.graph.nodeCount).map
        (fun history => history.state.base) =
      (program.information.runBehavioral profile program.graph.nodeCount).map
        GameTheory.Protocol.ExecutionProtocol.History.state :=
  program.runBehavioral_compileSerialized scheduler profile

/-- **Behavioral Nash equivalence from the canonical graph game to the actual
publicly serialized game.** Deviations range over all behavioral runtime player
policies, including order-aware policies. The scheduler is an arbitrary
behavioral environment, not an equilibrium player. Its private random choices
are not shared with honest players, and its utility is unconstrained. -/
theorem compiled_serialized_nash_iff
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (program : Machine.Program Player L)
    (schedulerUtility : program.serializedArena.History → ℝ)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) :
    Scheduled.IsPlayerNash (program.serializedGame schedulerUtility).behavioral
      (program.compileSerializedBehavioralProfile scheduler profile) ↔
    GameTheory.IsNash program.game.behavioral.form
      (GameTheory.euPreference program.game.behavioral.utility) profile :=
  program.isPlayerNash_compileSerialized_iff schedulerUtility scheduler profile

/-- **Distributional unilateral-adversary preservation.** Every behavioral
runtime deviation has a terminal-state law equal to a finite mixture of source
deviations against exactly the same compiled opponents. The mixture is local
to this profile and horizon, not a uniform randomized-scheduler translator. -/
theorem compiled_serialized_deviation_law
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (program : Machine.Program Player L)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) (who : Player)
    (replacement : program.serializedArena.information.BehavioralPolicy (.player who)) :
    ∃ replacements : FinDist (program.information.BehavioralPolicy who),
      (program.serializedArena.information.runBehavioral
        (Function.update (program.compileSerializedBehavioralProfile scheduler profile)
          (.player who) replacement) program.graph.nodeCount).map
            (fun history => history.state.base) =
      replacements.bind fun alternative =>
        (program.information.runBehavioral (Function.update profile who alternative)
          program.graph.nodeCount).map GameTheory.Protocol.ExecutionProtocol.History.state :=
  program.serializedDeviation_eq_sourceMixture scheduler profile who replacement

/-- **Exact preservation of unilateral adversarial loss bounds.** The loss is
any real-valued terminal-state observable, including harm to an honest player.
No equilibrium, rationality, or existence of a best response is assumed. -/
theorem compiled_serialized_loss_bound_iff
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (program : Machine.Program Player L)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) (who : Player)
    (loss : program.State → ℝ) (bound : ℝ) :
    (∀ replacement : program.serializedArena.information.BehavioralPolicy (.player who),
      (program.serializedArena.information.runBehavioral
        (Function.update (program.compileSerializedBehavioralProfile scheduler profile)
          (.player who) replacement) program.graph.nodeCount).expect
            (fun history => loss history.state.base) ≤ bound) ↔
    (∀ alternative : program.information.BehavioralPolicy who,
      (program.information.runBehavioral (Function.update profile who alternative)
        program.graph.nodeCount).expect (fun history => loss history.state) ≤ bound) :=
  program.serializedDeviation_expect_bound_iff scheduler profile who loss bound

/-- **Approximate Nash equivalence without error inflation.** Only original
players are tested; scheduling is an arbitrary public-data environment. -/
theorem compiled_serialized_approximate_nash_iff
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (program : Machine.Program Player L)
    (schedulerUtility : program.serializedArena.History → ℝ)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) (ε : ℝ) :
    (∀ who replacement,
      GameTheory.expectedUtility (program.serializedGame schedulerUtility).behavioral.utility
        (.player who) ((program.serializedGame schedulerUtility).behavioral.form.play
          (GameTheory.Profile.update (program.compileSerializedBehavioralProfile scheduler profile)
            (.player who) replacement)) ≤
      GameTheory.expectedUtility (program.serializedGame schedulerUtility).behavioral.utility
        (.player who) ((program.serializedGame schedulerUtility).behavioral.form.play
          (program.compileSerializedBehavioralProfile scheduler profile)) + ε) ↔
    GameTheory.IsεNash program.game.behavioral.form program.game.behavioral.utility ε profile :=
  program.serialized_approximate_nash_iff schedulerUtility scheduler profile ε

/-! ## Runtime obstructions -/

/-- **The second submitter's winning deviation** (paper: `thm:public-submission`). -/
theorem public_submission_winning_deviation
    (schedulerUtility : Scheduled.PublicSubmission.Values → ℝ)
    (profile : Profile Scheduled.PublicSubmission.signature) (first : Fin 2)
    (horder : profile .scheduler = FinDist.pure first) :
    expectedUtility (Scheduled.PublicSubmission.game schedulerUtility).utility
      (.player (Scheduled.PublicSubmission.other first))
      ((Scheduled.PublicSubmission.game schedulerUtility).form.play
        (Profile.update profile (.player (Scheduled.PublicSubmission.other first))
          (Scheduled.PublicSubmission.winningPolicy
            (Scheduled.PublicSubmission.other first)))) = 1 :=
  Scheduled.PublicSubmission.winning_deviation schedulerUtility profile first horder

/-- **Zero payoff is not Nash for the second submitter** (paper: `thm:public-submission`). -/
theorem public_submission_not_nash
    (schedulerUtility : Scheduled.PublicSubmission.Values → ℝ)
    (profile : Profile Scheduled.PublicSubmission.signature) (first : Fin 2)
    (horder : profile .scheduler = FinDist.pure first)
    (hpayoff : expectedUtility (Scheduled.PublicSubmission.game schedulerUtility).utility
      (.player (Scheduled.PublicSubmission.other first))
      ((Scheduled.PublicSubmission.game schedulerUtility).form.play profile) = 0) :
    ¬ Scheduled.IsPlayerNash (Scheduled.PublicSubmission.game schedulerUtility) profile :=
  Scheduled.PublicSubmission.not_nash_of_zero_payoff schedulerUtility profile first horder hpayoff

/-- **Public sequential submission cannot implement a zero-payoff Nash
equilibrium.** In this two-bit runtime the later player sees the earlier
irreversible value before choosing. No compiler or decoder can supply an
unrestricted player-deviation adequacy certificate for the stated source game. -/
theorem public_submission_no_adequacy
    (source : GameTheory.UtilityGame (Fin 2)) (profile : GameTheory.Profile source.form.sig)
    (hnash : GameTheory.IsNash source.form (GameTheory.euPreference source.utility) profile)
    (hzero : ∀ who, GameTheory.expectedUtility source.utility who (source.form.play profile) = 0)
    (schedulerUtility : Scheduled.PublicSubmission.Values → ℝ) :
    ¬ Nonempty (Scheduled.PlayerDeviationAdequacy source
      (Scheduled.PublicSubmission.game schedulerUtility)) :=
  Scheduled.PublicSubmission.no_adequacy_of_zero_equilibrium source profile hnash hzero
    schedulerUtility

/-- **Quantitative, compiler-independent obstruction.** Any runtime profile
which is an ε equilibrium for the players and retains the second player's
source payoff zero up to an upper error δ must satisfy δ + ε ≥ 1. -/
theorem public_submission_approximation_lower_bound
    (schedulerUtility : Scheduled.PublicSubmission.Values → ℝ)
    (profile : GameTheory.Profile Scheduled.PublicSubmission.signature)
    (first : Fin 2) (δ ε : ℝ)
    (horder : profile .scheduler = FinDist.pure first)
    (hpayoff : GameTheory.expectedUtility
      (Scheduled.PublicSubmission.game schedulerUtility).utility
      (.player (Scheduled.PublicSubmission.other first))
      ((Scheduled.PublicSubmission.game schedulerUtility).form.play profile) ≤ δ)
    (hequilibrium : ∀ who replacement,
      GameTheory.expectedUtility (Scheduled.PublicSubmission.game schedulerUtility).utility
        (.player who) ((Scheduled.PublicSubmission.game schedulerUtility).form.play
          (GameTheory.Profile.update profile (.player who) replacement)) ≤
      GameTheory.expectedUtility (Scheduled.PublicSubmission.game schedulerUtility).utility
        (.player who) ((Scheduled.PublicSubmission.game schedulerUtility).form.play profile) + ε) :
    1 ≤ δ + ε :=
  Scheduled.PublicSubmission.approximation_lower_bound schedulerUtility profile first δ ε
    horder hpayoff hequilibrium

/-- **Exact optimal value of an informed final veto.** For fixed source
choices, every randomized refusal rule is bounded by the expectation of the
prospective payoff clipped from below at the abort payoff, and this bound is attained. -/
theorem selective_abort_value_bound_iff
    {Player : Type} [DecidableEq Player] (source : GameTheory.UtilityGame Player)
    (profile : GameTheory.Profile source.form.sig) (last : Player)
    (abortPayoff : Player → ℝ) (bound : ℝ) :
    (∀ rule, GameTheory.expectedUtility
      (Runtime.SelectiveAbort.game source last abortPayoff).utility
      last ((Runtime.SelectiveAbort.game source last abortPayoff).form.play
        (Runtime.SelectiveAbort.withRule source profile last rule)) ≤ bound) ↔
    (source.form.play profile).expect
      (fun outcome => max (source.utility outcome last) (abortPayoff last)) ≤ bound :=
  Runtime.SelectiveAbort.all_rules_bound_iff source profile last abortPayoff bound

/-- **Exact support boundary for informed refusal alone.** Completion is
optimal precisely when abort pays no more than every supported prospective
payoff. The player's source strategy is held fixed in this statement. -/
theorem selective_abort_support_iff
    {Player : Type} [DecidableEq Player] (source : GameTheory.UtilityGame Player)
    (profile : GameTheory.Profile source.form.sig) (last : Player)
    (abortPayoff : Player → ℝ) :
    (∀ rule, GameTheory.expectedUtility
      (Runtime.SelectiveAbort.game source last abortPayoff).utility
      last ((Runtime.SelectiveAbort.game source last abortPayoff).form.play
        (Runtime.SelectiveAbort.withRule source profile last rule)) ≤
      GameTheory.expectedUtility source.utility last (source.form.play profile)) ↔
    ∀ outcome ∈ (source.form.play profile).support,
      abortPayoff last ≤ source.utility outcome last :=
  Runtime.SelectiveAbort.no_profitable_refusal_iff source profile last abortPayoff

/-- **Exact full Nash criterion for the final-veto pass.** The additional
inequality quantifies over every upstream source-strategy replacement by the
designated player, as well as accounting for its optimal randomized refusal. -/
theorem selective_abort_nash_iff
    {Player : Type} [DecidableEq Player] (source : GameTheory.UtilityGame Player)
    (profile : GameTheory.Profile source.form.sig) (last : Player)
    (abortPayoff : Player → ℝ) :
    GameTheory.IsNash (Runtime.SelectiveAbort.game source last abortPayoff).form
      (GameTheory.euPreference (Runtime.SelectiveAbort.game source last abortPayoff).utility)
      (Runtime.SelectiveAbort.compileProfile source profile) ↔
    GameTheory.IsNash source.form (GameTheory.euPreference source.utility) profile ∧
      ∀ replacement : source.form.sig.Strategy last,
        (source.form.play (GameTheory.Profile.update profile last replacement)).expect
          (fun outcome => max (source.utility outcome last) (abortPayoff last)) ≤
            GameTheory.expectedUtility source.utility last (source.form.play profile) :=
  Runtime.SelectiveAbort.nash_compile_iff source profile last abortPayoff

/-- **Refusal under partial information.** The quitter's optimal expected
value clips the conditional expected continuation payoff, not its realized
value. The observation-dependent abort payoff is available at the decision. -/
theorem observed_abort_value_bound_iff
    {Outcome Info : Type*} (law : FinDist Outcome) (observe : Outcome → Info)
    (completePayoff : Outcome → ℝ) (abortPayoff : Info → ℝ) (bound : ℝ) :
    (∀ rule : Info → FinDist Bool,
      Runtime.ObservedAbort.value law observe completePayoff abortPayoff rule ≤ bound) ↔
    (law.map observe).expect (fun info =>
      max ((law.condOnFibre observe info).expect completePayoff) (abortPayoff info)) ≤ bound :=
  Runtime.ObservedAbort.all_rules_bound_iff law observe completePayoff abortPayoff bound

/-- **Deterministic attainment** (paper: `thm:observed-quitting`). Complete
exactly when the conditional continuation payoff weakly exceeds the exit payoff. -/
theorem observed_abort_optimal_rule
    {Outcome Info : Type*} (law : FinDist Outcome) (observe : Outcome → Info)
    (completePayoff : Outcome → ℝ) (abortPayoff : Info → ℝ) :
    Runtime.ObservedAbort.value law observe completePayoff abortPayoff
      (fun info => FinDist.pure
        (decide (abortPayoff info ≤ (law.condOnFibre observe info).expect completePayoff))) =
      (law.map observe).expect (fun info =>
        max ((law.condOnFibre observe info).expect completePayoff) (abortPayoff info)) :=
  Runtime.ObservedAbort.optimal_value law observe completePayoff abortPayoff

/-- **Exact information-level exit condition.** Completing is optimal against
all randomized refusal rules precisely at the supported information values
where its conditional expected payoff is at least the exit payoff. -/
theorem observed_abort_support_iff
    {Outcome Info : Type*} (law : FinDist Outcome) (observe : Outcome → Info)
    (completePayoff : Outcome → ℝ) (abortPayoff : Info → ℝ) :
    (∀ rule : Info → FinDist Bool,
      Runtime.ObservedAbort.value law observe completePayoff abortPayoff rule ≤
        law.expect completePayoff) ↔
    ∀ info ∈ (law.map observe).support,
      abortPayoff info ≤ (law.condOnFibre observe info).expect completePayoff :=
  Runtime.ObservedAbort.no_profitable_refusal_iff law observe completePayoff abortPayoff

/-- **The value of exit is monotone in information.** The abort payoffs are
held fixed as the quitter learns a refinement of its original observation. -/
theorem observed_abort_information_mono
    {Outcome Fine Info : Type*} (law : FinDist Outcome)
    (observe : Outcome → Fine) (forget : Fine → Info)
    (completePayoff : Outcome → ℝ) (abortPayoff : Info → ℝ) :
    (law.map (forget ∘ observe)).expect (fun info =>
      max ((law.condOnFibre (forget ∘ observe) info).expect completePayoff) (abortPayoff info)) ≤
    (law.map observe).expect (fun info =>
      max ((law.condOnFibre observe info).expect completePayoff) (abortPayoff (forget info))) :=
  Runtime.ObservedAbort.envelope_mono_information law observe forget completePayoff abortPayoff

/-- **A causal realization of the exit decision.** If the outcome observation
is already determined at the checkpoint, deciding before sampling the future
continuation has the same complete settlement/abort law for every local rule. -/
theorem observed_abort_causal_law
    {Checkpoint Outcome Info : Type*} (checkpoints : FinDist Checkpoint)
    (continuation : Checkpoint → FinDist Outcome) (checkpointObserve : Checkpoint → Info)
    (observe : Outcome → Info) (rule : Info → FinDist Bool)
    (hobserve : ∀ checkpoint ∈ checkpoints.support,
      ∀ outcome ∈ (continuation checkpoint).support,
        observe outcome = checkpointObserve checkpoint) :
    Runtime.ObservedAbort.run (checkpoints.bind continuation) observe rule =
      checkpoints.bind fun checkpoint => (rule (checkpointObserve checkpoint)).bind fun complete =>
        if complete then (continuation checkpoint).map Sum.inl
        else FinDist.pure (Sum.inr (checkpointObserve checkpoint)) :=
  Runtime.ObservedAbort.run_causal checkpoints continuation checkpointObserve observe rule hobserve

/-- **Completion-equilibrium criterion for a source game with quitting.**
Here `source` denotes the normal-completion restriction; `Game.game` is the
full game including the specified quit decision. Every upstream deviation
induces its own conditional law. This is a mechanism-design criterion, not a
requirement that compilers remove profitable source-level quit strategies. -/
theorem observed_abort_nash_iff
    {Player Info : Type} [DecidableEq Player] (source : GameTheory.UtilityGame Player)
    (observe : source.form.sig.Outcome → Info) (profile : GameTheory.Profile source.form.sig)
    (last : Player) (abortPayoff : Info → Player → ℝ) :
    GameTheory.IsNash (Runtime.ObservedAbort.Game.game source observe last abortPayoff).form
      (GameTheory.euPreference
        (Runtime.ObservedAbort.Game.game source observe last abortPayoff).utility)
      (Runtime.ObservedAbort.Game.compileProfile source profile) ↔
    GameTheory.IsNash source.form (GameTheory.euPreference source.utility) profile ∧
      ∀ replacement : source.form.sig.Strategy last,
        let law := source.form.play (GameTheory.Profile.update profile last replacement)
        (law.map observe).expect (fun info =>
          max ((law.condOnFibre observe info).expect (fun outcome => source.utility outcome last))
            (abortPayoff info last)) ≤
              GameTheory.expectedUtility source.utility last (source.form.play profile) :=
  Runtime.ObservedAbort.Game.nash_compile_iff source observe profile last abortPayoff

/-- **Every observation-local quit rule has a delivered-request implementation.** -/
theorem disclosure_window_rule_exact {Info Request : Type}
    (gate : Runtime.DisclosureWindow.Gate Info Request) (slots : Nat)
    (rule : Runtime.ObservedAbort.Rule Info) :
    Runtime.DisclosureWindow.effectiveRule gate (slots + 1)
      (Runtime.DisclosureWindow.compileRule gate rule) = rule :=
  Runtime.DisclosureWindow.effectiveRule_compileRule gate slots rule

/-- **Arbitrary request histories preserve the exact quitting Nash criterion.**
    Delivery, deadline progress, and fixed information are part of this target model. -/
theorem disclosure_window_nash_iff
    {Player Info Request : Type} [DecidableEq Player] (source : GameTheory.UtilityGame Player)
    (observe : source.form.sig.Outcome → Info) (profile : GameTheory.Profile source.form.sig)
    (last : Player) (abortPayoff : Info → Player → ℝ)
    (gate : Runtime.DisclosureWindow.Gate Info Request) (slots : Nat) :
    GameTheory.IsNash
      (Runtime.DisclosureWindow.Game.game source observe last abortPayoff gate (slots + 1)).form
      (GameTheory.euPreference
        (Runtime.DisclosureWindow.Game.game
          source observe last abortPayoff gate (slots + 1)).utility)
      ((Runtime.DisclosureWindow.Game.adequacy
          source observe last abortPayoff gate slots).compileProfile
        (Runtime.ObservedAbort.Game.compileProfile source profile)) ↔
    GameTheory.IsNash source.form (GameTheory.euPreference source.utility) profile ∧
      ∀ replacement : source.form.sig.Strategy last,
        let law := source.form.play (GameTheory.Profile.update profile last replacement)
        (law.map observe).expect (fun info =>
          max ((law.condOnFibre observe info).expect (fun outcome => source.utility outcome last))
            (abortPayoff info last)) ≤
              GameTheory.expectedUtility source.utility last (source.form.play profile) :=
  Runtime.DisclosureWindow.Game.nash_compile_iff source observe profile last abortPayoff gate slots

/-- A nonempty bounded window is uniformly deviation-adequate for the full
source game with quitting, including its complete tagged outcome law. This
holds for arbitrary games and quit payoffs, even when quitting is profitable. -/
theorem disclosure_window_adequacy
    {Player Info Request : Type} [DecidableEq Player] (source : UtilityGame Player)
    (observe : source.form.sig.Outcome → Info) (last : Player)
    (abortPayoff : Info → Player → ℝ)
    (gate : Runtime.DisclosureWindow.Gate Info Request) (slots : Nat) :
    Nonempty (Runtime.DeviationAdequacy
      (Runtime.ObservedAbort.Game.game source observe last abortPayoff)
      (Runtime.DisclosureWindow.Game.game source observe last abortPayoff gate (slots + 1))) :=
  ⟨Runtime.DisclosureWindow.Game.adequacy source observe last abortPayoff gate slots⟩

theorem observed_abort_no_information
    {Outcome : Type*} (law : FinDist Outcome) (utility : Outcome → ℝ) (abortValue : ℝ) :
    Runtime.ObservedAbort.envelope law (fun _ => ()) utility (fun _ => abortValue) =
      max (law.expect utility) abortValue :=
  Runtime.ObservedAbort.envelope_no_information law utility abortValue

theorem observed_abort_payoff_information
    {Outcome : Type*} (law : FinDist Outcome) (utility : Outcome → ℝ) (abortValue : ℝ) :
    Runtime.ObservedAbort.envelope law utility utility (fun _ => abortValue) =
      law.expect (fun outcome => max (utility outcome) abortValue) :=
  Runtime.ObservedAbort.envelope_payoff_information law utility abortValue

/-! ## Profile-local extra observations -/

/-- Exact unilateral laws for the constant-signal one-shot model. -/
theorem constant_signal_deviation_law
    {Value Signal Action : Type} (observe : Value → Signal)
    (profile : Profile (Runtime.ConstantSignal.sourceSignature Value Action)) (signal : Signal)
    (hconstant : ∀ value ∈ (profile false).support, observe value = signal)
    (who : Bool)
    (replacement : (Runtime.ConstantSignal.targetSignature Value Signal Action).Strategy who) :
    Runtime.ConstantSignal.targetPlay observe
        (Profile.update (Runtime.ConstantSignal.compileProfile profile) who replacement) =
      Runtime.FailureObservation.play id
        (Profile.update profile who
          (Runtime.ConstantSignal.backtranslate signal who replacement)) :=
  Runtime.ConstantSignal.deviation_law observe profile signal hconstant who replacement

/-- Same-error approximate Nash at constant-signal profiles, not all profiles. -/
theorem constant_signal_approximate_nash_iff
    {Value Signal Action : Type} (observe : Value → Signal)
    (utility : Value × Action → Bool → ℝ)
    (profile : Profile (Runtime.ConstantSignal.sourceSignature Value Action)) (signal : Signal)
    (hconstant : ∀ value ∈ (profile false).support, observe value = signal) (ε : ℝ) :
    IsεNash (Runtime.ConstantSignal.targetGame observe utility).form utility ε
        (Runtime.ConstantSignal.compileProfile profile) ↔
      IsεNash (Runtime.FailureObservation.game (Raw := Value) id utility).form utility ε profile :=
  Runtime.ConstantSignal.approximate_nash_iff observe utility profile signal hconstant ε

/-- Pointwise strict dominance of the Boolean quit action supplies the
constant-signal premise at every source Nash profile. -/
theorem constant_signal_dominated_quit
    {Action : Type} (utility : Bool × Action → Bool → ℝ)
    (hdominates : ∀ action, utility (true, action) false < utility (false, action) false)
    (profile : Profile (Runtime.ConstantSignal.sourceSignature Bool Action))
    (hnash : IsNash (Runtime.FailureObservation.game (Raw := Bool) id utility).form
      (euPreference utility) profile) :
    IsNash (Runtime.ConstantSignal.targetGame id utility).form (euPreference utility)
      (Runtime.ConstantSignal.compileProfile profile) :=
  Runtime.ConstantSignal.nash_preserved_of_dominated_quit utility hdominates profile hnash

/-- info: 'Vegas.Paper.constant_signal_deviation_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.constant_signal_deviation_law

/-- info: 'Vegas.Paper.constant_signal_approximate_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.constant_signal_approximate_nash_iff

/-- info: 'Vegas.Paper.constant_signal_dominated_quit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.constant_signal_dominated_quit

/-! ## Scheduling -/

/-- **Confluence of effects is not invisibility of order.**

Two joint submissions scheduling different orders induce different successor
laws, *whatever the underlying state machine does* — in particular even when the
two orders have identical effects, so the underlying state law is
schedule-invariant.

A schedule-invariance result about a state machine constrains what the machine
computes; it says nothing about what a participant observes. Only a statement
about the protocol state does, and that requires the realized order to be part
of that state rather than quotiented out of it.

`Vegas.coin_step_ne` witnesses that this is not vacuous, in the most extreme
case available: a system in which every action is the identity, so effects
commute maximally, and two schedules remain distinguishable.

Scope. The order published here is the *settled* one, common knowledge once a
round is on chain — the reading a public signal carries in an information model.
In-flight submissions are visible to some observers but are **not** common
knowledge, so they cannot be modelled as a public signal at all, and this
development assumes no participant observes a submission before it is applied.
Front-running is outside the model. -/
theorem schedule_is_observable
    {ι : Type} (sys : ScheduledSystem ι)
    {state : sys.State}
    {left right : { joint // sys.toExecutionProtocol.Legal state joint }}
    (horder : sys.scheduledOrder left.1 ≠ sys.scheduledOrder right.1) :
    sys.toExecutionProtocol.step state left ≠
      sys.toExecutionProtocol.step state right :=
  sys.step_ne_of_order_ne horder

/-- **The order-oblivious deviation class is proper.**

A policy is *order-oblivious* when the schedule cannot change what it does. That
restricts what a participant reads, never what it can express, so the class
contains every policy a schedule-free source could offer
(`liftPolicy_orderOblivious`).

It is nonetheless a proper subclass. `Vegas.coinOrderAware` acts differently at
two histories that agree on every public view and differ only in how a round was
ordered, over a system whose actions are all the identity.

This proves observability, not strategic failure. The compiled scheduler is
allowed to observe public game data. Independent-signal Nash preservation is
proved separately; using it for this runtime still requires a causal
back-translation of order-history-aware player policies. -/
theorem order_aware_deviations_exist (i : Fin 2) :
    ¬ Vegas.coinSystem.OrderOblivious (Vegas.coinOrderAware i) :=
  Vegas.coinOrderAware_not_orderOblivious i

/-- **An order-enforcing runtime removes operational scheduling choice.**

Two legal joint submissions agreeing on every player's submission induce the
same successor law, whatever the scheduling coordinate contains. Thus a runtime
accepting one order per view exposes no operational ordering choice. This is
stronger than player-equilibrium preservation needs, but useful when developers
also want identical public traces.

Enforcement is a dial, not a default. `schedules` is a field of the system, so
an artifact is permissive or enforcing by construction and `EnforcesOrder` is a
hypothesis here rather than a standing assumption. A developer wanting no
order-sensitive guarantee keeps the permissive runtime's parallelism and this
result simply does not apply; one who wants the guarantee pays for exactly it.

Scope: enforcement removes *order* as a channel, not every channel. Timing —
block height, elapsed time, who was slow — remains public and is not modelled
here at all, and in-flight visibility is excluded by a separate assumption. -/
theorem enforced_schedule_removes_order_choice
    {ι : Type} (sys : ScheduledSystem ι) (henforce : sys.EnforcesOrder)
    {state : sys.State}
    {left right : { joint // sys.toExecutionProtocol.Legal state joint }}
    (hplayers : ∀ i, left.1 (.player i) = right.1 (.player i)) :
    sys.toExecutionProtocol.step state left =
      sys.toExecutionProtocol.step state right :=
  sys.step_eq_of_enforcesOrder henforce hplayers

/-- **Commuting effects make the schedule irrelevant to underlying state.**

Two legal joint submissions agreeing on every player's submission reach the same
law over *underlying states*, whatever the scheduler submitted — provided every
order the runtime accepts has the same effect.

This is the cheaper of two operational disciplines. Enforcement removes the
order choice; commutation leaves it visible but proves that it cannot alter the
underlying state. Strategic preservation additionally needs player utility to
factor through that state and signal-conditioned player deviations to erase to
source deviations. The fixed and random signal theorems supply the elementary
averaging argument. For an executing public-history scheduler, one must also
construct a source policy for each fixed scheduler random seed, consistently
across source information sets. Public data is allowed; current simultaneous
submissions remain outside the scheduler's observation.

What it buys is strictly less than enforcement, and the gap is the point.
Enforcement determines the whole successor law, log included, so no observation
separates two schedules. Commutation determines only the base state: the log
still differs, so a payoff that reads the log still sees a difference.
Payoff-irrelevance is therefore commutation *plus* a schedule-blind game, and
that second half is a condition on the game, not on the runtime.

Neither discipline covers a scheduler that reacts to what it is ordering. Both
quantify over a fixed joint submission, which is this model's standing
assumption that the scheduler commits without seeing the round's submissions.
Front-running is a different system, not a corner of this one. -/
theorem commuting_effects_make_order_state_irrelevant
    {ι : Type} (sys : ScheduledSystem ι) (hcommute : sys.EffectsCommute)
    {state : sys.State}
    {left right : { joint // sys.toExecutionProtocol.Legal state joint }}
    (hplayers : ∀ i, left.1 (.player i) = right.1 (.player i)) :
    (sys.toExecutionProtocol.step state left).map ScheduledSystem.State.base =
      (sys.toExecutionProtocol.step state right).map ScheduledSystem.State.base :=
  sys.step_base_eq_of_effectsCommute hcommute hplayers

/-- **The permissive tier is inhabited: order can be available, observable, and
still useless.**

For a runtime where two players each add to a running total and either order is
accepted: the runtime does *not* enforce an order; the two schedules are
genuinely distinguishable, inducing different successor laws because the log
records which happened; and the laws over totals nevertheless coincide.

All three at once is the claim. A developer who does not care about order keeps
the parallelism, an order-aware deviation remains expressible against them, and
a payoff reading the total is untouched by it. The witness is not degenerate:
the total genuinely moves, so commutation here is a fact about addition rather
than about nothing happening. -/
theorem order_available_observable_and_useless :
    ¬ counterSystem.EnforcesOrder ∧
      ∀ state : counterSystem.State,
        counterSystem.toExecutionProtocol.step state (counterZeroFirst state) ≠
            counterSystem.toExecutionProtocol.step state (counterOneFirst state) ∧
          (counterSystem.toExecutionProtocol.step state
              (counterZeroFirst state)).map ScheduledSystem.State.base =
            (counterSystem.toExecutionProtocol.step state
              (counterOneFirst state)).map ScheduledSystem.State.base :=
  ⟨counter_not_enforcesOrder,
    fun state => ⟨counter_step_ne state, counter_step_base_eq state⟩⟩

/-- **And the permissive tier has a boundary.**

For a runtime where one player doubles a total and another adds to it, the two
accepted orders reach different totals, so `EffectsCommute` fails. The
hypothesis of `commuting_effects_make_order_state_irrelevant` is therefore a
real restriction rather than something every system satisfies, and a system in
this shape — two pending operations whose order changes the result, which is the
shape a public runtime actually has — is one where a preservation claim must pay
for `EnforcesOrder` instead of arguing that order does not matter. -/
theorem commutation_is_a_real_restriction : ¬ raceSystem.EffectsCommute :=
  race_not_effectsCommute

/-- **The protocol layer forbids sending nothing at all.**

At a legal joint submission every *active* player has submitted something:
`IsLegalJoint` reads `none` as "not active", so abstention is legal exactly when
a participant has nothing to do.

This is not a prohibition on declining. Declining, in Vegas, is a null *value*
rather than an absent submission: a surface `yield` lowers to a nullable sealed
commitment whose guard accepts `none` unconditionally, so `some Option.none` is
a legal submission, and the continuation — typed at `option b` and eliminated by
`isNone`/`getD` — must say what happens when a player takes it. The two are easy
to conflate because both are spelled `none`, and they are different: the second
is a transaction the program sees.

What the condition rules out is sending nothing whatsoever, which no public
runtime can prevent. The claim is recorded because it marks exactly where the
model is stronger than the runtime it describes. -/
theorem active_participation_is_forced
    {ι : Type} (sys : ScheduledSystem ι) {state : sys.State}
    (joint : { joint // sys.toExecutionProtocol.Legal state joint })
    (i : ι) (hactive : sys.active state.base i) :
    ∃ action, joint.1 (.player i) = some action := by
  have hlegal := joint.2.2 (.player i)
  cases hjoint : joint.1 (.player i) with
  | none => rw [hjoint] at hlegal; exact absurd hactive hlegal
  | some action => exact ⟨action, rfl⟩

/-- **Silence is inert, sometimes available, and not universally so.**

Three things at once.  If every player is silent, the player-controlled phase
leaves the state where it was in every order; a system's separate automatic
settlement phase may still run.  This schedule-independence needs no
`EffectsCommute`, since inert actions commute with everything. The running-total
runtime affords silence. The doubling-and-adding one does not, every action
there moving the total, so `AllowsSilence` is a real hypothesis rather than
something every system satisfies.

Silence is the residual gap left by the source language's own way of declining.
A `yield`'s null submission is a transaction: the program sees it, continues,
and can slash a deposit on the spot. Silence is not, and `silence_inert` is why:
the player-controlled phase cannot attribute a state change to a silent player,
so a protocol wanting to charge for it must measure elapsed time. That is what a
timeout is for, and why the deposit story needs a mechanism rather than a rule
saying players must reveal.

Not shown here: that silence fails to pay. That is a statement about payoffs,
which live a layer above this one. -/
theorem silence_is_inert_available_and_not_universal :
    (∀ {ι : Type} (sys : ScheduledSystem ι) (hsilent : sys.AllowsSilence)
        (order proposed : sys.Order) (state : sys.Base),
      sys.applyOrder (hsilent.allSilent proposed) order state = FinDist.pure state) ∧
    Nonempty counterSystem.AllowsSilence ∧ IsEmpty raceSystem.AllowsSilence :=
  ⟨fun _ hsilent order proposed state => hsilent.applyOrder_silent order proposed state,
    ⟨counter_allowsSilence⟩, race_no_silence⟩

/-- **Declining and silence are different, and ordered.**

Every runtime affording silence affords declining, by forgetting that the
submission was inert. The converse fails: the doubling-and-adding runtime lets a
player submit — every action is accepted — while no action there is inert, so
nobody can vanish without trace.

The two were conflated in this development because both wanted the spelling
`none`, and the error was not caught by types. They now have names.
*Declining* is `declineValue`, the null value a player submits to a nullable
commitment: `Expr.nullableCommitGuard` accepts it whatever the environment, the
continuation is typed at `option b` and must handle it, and the program may
charge for it on the spot. *Silence* is sending nothing, which
`active_participation_is_forced` shows the protocol layer forbids and no public
runtime can.

The gap between them is the room a protocol has to charge for declining, and it
is why a deposit is slashable against a decline directly but against silence
only through a timeout. -/
theorem declining_is_weaker_than_silence :
    (∀ (ι : Type) (sys : ScheduledSystem ι),
        sys.AllowsSilence → Nonempty sys.AllowsDeclining) ∧
      Nonempty raceSystem.AllowsDeclining ∧ IsEmpty raceSystem.AllowsSilence :=
  ⟨fun _ _ hsilent => ⟨hsilent.toAllowsDeclining⟩,
    ⟨race_allowsDeclining⟩, race_no_silence⟩

/-- **A nullable commitment can never be declined illegally.**

Whatever the environment, some submission satisfies the guard — namely
`declineValue`. So a surface `yield` is a form a player can never be stuck on,
and declining is a *source* strategy needing no back-translation.

The contrast is `commit`, whose payload `CommitPayloadTy` restricts to
non-nullable types: that form obliges a player to act, and its satisfiability is
an obligation discharged elsewhere rather than a theorem about the form. -/
theorem declining_is_always_live
    {P : Type} [DecidableEq P] {Γ : VCtx P simpleExpr}
    {x : VarId} {b : BaseTy} [DefaultVal b]
    (R : Expr ((x, b) :: eraseVCtx Γ) .bool) :
    ∀ env : Env Val (eraseVCtx Γ),
      ∃ a : Val (.option b),
        Vegas.evalGuard (Player := P) (L := simpleExpr)
          (Expr.nullableCommitGuard R) a env = true :=
  nullableCommitGuard_satisfiable R

/-! ## Deviation adequacy -/

/-- **Utility preservation at compiled profiles** (paper: `lem:expected-utility`,
first equation). -/
theorem utility_preservation_honest
    {Player : Type} [DecidableEq Player]
    {source target : UtilityGame Player}
    (adequacy : Runtime.DeviationAdequacy source target)
    (profile : Profile source.form.sig) (who : Player) :
    expectedUtility target.utility who
        (target.form.play (adequacy.compileProfile profile)) =
      expectedUtility source.utility who (source.form.play profile) :=
  adequacy.expectedUtility_compileProfile profile who

/-- **Utility preservation under unilateral target deviation**
(paper: `lem:expected-utility`, second equation).

`replacement` ranges over the *whole* target strategy type, not only over
strategies in the image of `compileStrategy`.  That is what makes the
back-translation obligation non-vacuous. -/
theorem utility_preservation_deviation
    {Player : Type} [DecidableEq Player]
    {source target : UtilityGame Player}
    (adequacy : Runtime.DeviationAdequacy source target)
    (profile : Profile source.form.sig) (who : Player)
    (replacement : target.form.sig.Strategy who) :
    expectedUtility target.utility who
        (target.form.play
          (Profile.update (adequacy.compileProfile profile) who replacement)) =
      expectedUtility source.utility who
        (source.form.play
          (Profile.update profile who
            (adequacy.backtranslateStrategy who replacement))) :=
  adequacy.expectedUtility_deviation profile who replacement trivial

/-- **Nash equivalence relative to a deviation class.**

A compiled profile withstands every *considered* target deviation exactly when
the source profile withstands every source deviation.  The class is a parameter,
so the same theorem covers both tiers the development cares about: the honest
tier, where a player reads only what the source made visible, and the robust
tier below, where a player may read anything the target exposes.

Because `Considered` appears in the statement, a result about the honest tier
cannot be misread as a result about all strategies. -/
theorem nash_equivalence_against
    {Player : Type} [DecidableEq Player]
    {source target : UtilityGame Player}
    {Considered : (who : Player) → target.form.sig.Strategy who → Prop}
    (adequacy : Runtime.DeviationAdequacyOn source target Considered)
    (profile : Profile source.form.sig) :
    Runtime.IsNashAgainst target Considered (adequacy.compileProfile profile) ↔
      IsNash source.form (euPreference source.utility) profile :=
  adequacy.isNashAgainst_compileProfile_iff profile

/-- **Nash equivalence** (paper: `thm:nash-equivalence`).

A compiled profile is a target Nash equilibrium exactly when the source profile
is a source Nash equilibrium.  Preservation *and* reflection, at compiled
profiles, for every player of the shared player type — there is no restriction
to a subset of "joined" players. -/
theorem nash_equivalence
    {Player : Type} [DecidableEq Player]
    {source target : UtilityGame Player}
    (adequacy : Runtime.DeviationAdequacy source target)
    (profile : Profile source.form.sig) :
    IsNash target.form (euPreference target.utility)
        (adequacy.compileProfile profile) ↔
      IsNash source.form (euPreference source.utility) profile :=
  adequacy.isNash_compileProfile_iff profile


/-! ## The compilation result, in one statement -/

/-- **What compiling a checked finite-domain Vegas program buys**
(paper: `thm:main`).

One statement, with every hypothesis visible, for the results the paper's main
claim is assembled from:

1. *Source-payoff adequacy.* Every terminal reachable machine state
   reconstructs a terminal source environment the program can actually reach, in
   which the compiled payoff code and the source payoff expressions agree.
2. *Perfect recall.* A player's compiled information remembers its own earlier
   information and actions.
3. *Bounded horizon.* The graph's node count bounds every strategy's play
   length, so the extracted game is finite by construction.
4. *Kuhn correspondence, both directions.* The behavioral and mixed-pure
   presentations of the frontier game are mutually deviation-adequate, so their
   outcome laws and Nash equilibria correspond.

Read what the hypotheses are, and are not. `source` is a `WFProgram`: a
proof-carrying program, not the output of a checker run on surface syntax --
there is no raw-syntax-to-`WFProgram` proof-producing pass, so "checked" here
means "accompanied by a proof", and calling the Lean side an executable checker
would be wrong. `FiniteDomains` is what makes the Kuhn conjuncts available.

Read the conclusions the same way. (1) is *support-level and one-way*: every
terminal target execution has a source counterpart with the same payoff. It is
not equality of probabilistic laws, and there is no converse here. (4) relates
two presentations of the *same* compiled game to each other; it is not a
statement relating source strategies to target strategies. Separately,
`compiled_serialized_nash_iff` relates the canonical atomic behavioral game to
the actual serialized behavioral game, for every public-data behavioral
scheduler. Compact information sufficiency, scheduler replay, full terminal
laws, and scheduler-only predrawing discharge the concrete proof obligations.
There is no separate strategy game for the pre-compilation raw program and no
strategic-preservation theorem to a generated contract game.
An EVM theorem must additionally define the target game and
show that ordering, inclusion, timing, and visibility satisfy the required
utility factorization and player-deviation back-translation. -/
theorem compilation_summary
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (source : WFProgram Player L) [FiniteDomains source] :
    (∀ (state : (Machine.compile source).State),
        (Machine.compile source).terminal state →
          ∃ terminalEnv :
              VEnv L (ToEventGraph.compile source.core).terminalCtx,
            SmallStep.Star
              { ctx := source.core.Γ, env := source.core.env,
                cont := source.core.prog }
              { ctx := (ToEventGraph.compile source.core).terminalCtx,
                env := terminalEnv,
                cont := .ret
                  (ToEventGraph.compile source.core).sourcePayoffs } ∧
            evalPayoffs? (Machine.compile source).payoffs state.1.store =
              some (evalPayoffs
                (ToEventGraph.compile source.core).sourcePayoffs terminalEnv)) ∧
      (Machine.compile source).information.PerfectRecall ∧
      (Machine.compile source).execution.BoundedHorizon
        (Machine.compile source).graph.nodeCount ∧
      Nonempty (Runtime.DeviationAdequacy source.game.behavioral
        source.game.mixedPure) ∧
      Nonempty (Runtime.DeviationAdequacy source.game.mixedPure
        source.game.behavioral) :=
  ⟨fun state hterminal => Machine.compile_sourceStar source state hterminal,
    (Machine.compile source).perfectRecall,
    (Machine.compile source).boundedHorizon,
    ⟨source.behavioralToMixedPureAdequacy⟩,
    ⟨source.mixedPureToBehavioralAdequacy⟩⟩

/-! ## Trusted base

Every claim above must rest on Lean's three standard axioms and nothing else.
These pins are the guard: `#print axioms` emits an info message, and
`#guard_msgs` turns a *different* message into a build error.  If a claim ever
acquires `sorryAx`, a `native_decide` kernel extension, or a bespoke axiom, the
build fails here rather than silently widening what the paper is trusting.

`whitespace := lax` because `#print axioms` wraps its list across lines. -/

/-- info: 'Vegas.Paper.source_payoff_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_payoff_adequacy

/-- info: 'Vegas.Paper.schedule_confluence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.schedule_confluence

/-- info: 'Vegas.Paper.legal_packet_determines_each_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.legal_packet_determines_each_write

/-- info: 'Vegas.Paper.commit_writes_are_configuration_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.commit_writes_are_configuration_independent

/-- info: 'Vegas.Paper.commit_reveal_barrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.commit_reveal_barrier

/-- info: 'Vegas.Paper.sequential_schedule_determined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sequential_schedule_determined

/-- info: 'Vegas.Paper.permissive_schedule_not_determined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.permissive_schedule_not_determined

/-- info: 'Vegas.Paper.kuhn_behavioral_to_mixedPure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.kuhn_behavioral_to_mixedPure

/-- info: 'Vegas.Paper.compiled_perfect_recall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_perfect_recall

/-- info: 'Vegas.Paper.compiled_bounded_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_bounded_horizon

/-- info: 'Vegas.Paper.extracted_arena_is_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.extracted_arena_is_bounded

/-- info: 'Vegas.Paper.kuhn_mixedPure_to_behavioral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.kuhn_mixedPure_to_behavioral

/-- info: 'Vegas.Paper.compiled_round_is_atomic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_round_is_atomic

/-- info: 'Vegas.Paper.compiled_runtime_scheduling_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_runtime_scheduling_boundary

/-- info: 'Vegas.Paper.compiled_scheduler_has_no_extra_information' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_scheduler_has_no_extra_information

/-- info: 'Vegas.Paper.compiled_scheduler_information_is_player_computable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_scheduler_information_is_player_computable

/-- info: 'Vegas.Paper.compiled_permissive_effects_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_permissive_effects_commute

/-- info: 'Vegas.Paper.compiled_serialized_round_implements_atomic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_serialized_round_implements_atomic

/-- info: 'Vegas.Paper.compiled_fixed_order_step_determined_by_players' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_fixed_order_step_determined_by_players

/-- info: 'Vegas.Paper.player_deviation_adequacy_nash_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.player_deviation_adequacy_nash_equivalence

/-- info: 'Vegas.Paper.independent_schedule_signal_preserves_player_nash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.independent_schedule_signal_preserves_player_nash

/-- info: 'Vegas.Paper.random_independent_schedule_signal_preserves_player_nash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.random_independent_schedule_signal_preserves_player_nash

/-- info: 'Vegas.Paper.public_scheduler_adds_no_history_information' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.public_scheduler_adds_no_history_information

/-- info: 'Vegas.Paper.public_scheduler_replay_preserves_behavioral_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.public_scheduler_replay_preserves_behavioral_law

/-- info: 'Vegas.Paper.random_public_scheduler_replay_preserves_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.random_public_scheduler_replay_preserves_law

/-- info: 'Vegas.Paper.compiled_serialized_game_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_serialized_game_wellFormed

/-- info: 'Vegas.Paper.compiled_serialized_history_has_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_serialized_history_has_source

/-- info: 'Vegas.Paper.compiled_serialized_round_information_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_serialized_round_information_law

/-- info: 'Vegas.Paper.compiled_serialized_behavioral_round_expands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_serialized_behavioral_round_expands

/-- info: 'Vegas.Paper.compiled_compact_information_sufficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_compact_information_sufficient

/-- info: 'Vegas.Paper.compiled_serialized_behavioral_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_serialized_behavioral_law

/-- info: 'Vegas.Paper.compiled_serialized_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_serialized_nash_iff

/-- info: 'Vegas.Paper.compiled_serialized_deviation_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_serialized_deviation_law

/-- info: 'Vegas.Paper.compiled_serialized_loss_bound_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_serialized_loss_bound_iff

/-- info: 'Vegas.Paper.compiled_serialized_approximate_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_serialized_approximate_nash_iff

/-- info: 'Vegas.Paper.public_submission_no_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.public_submission_no_adequacy

/-- info: 'Vegas.Paper.public_submission_approximation_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.public_submission_approximation_lower_bound

/-- info: 'Vegas.Paper.selective_abort_value_bound_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.selective_abort_value_bound_iff

/-- info: 'Vegas.Paper.selective_abort_support_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.selective_abort_support_iff

/-- info: 'Vegas.Paper.selective_abort_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.selective_abort_nash_iff

/-- info: 'Vegas.Paper.observed_abort_value_bound_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.observed_abort_value_bound_iff

/-- info: 'Vegas.Paper.observed_abort_support_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.observed_abort_support_iff

/-- info: 'Vegas.Paper.observed_abort_information_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.observed_abort_information_mono

/-- info: 'Vegas.Paper.observed_abort_causal_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.observed_abort_causal_law

/-- info: 'Vegas.Paper.observed_abort_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.observed_abort_nash_iff

/-- info: 'Vegas.Paper.disclosure_window_rule_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.disclosure_window_rule_exact

/-- info: 'Vegas.Paper.disclosure_window_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.disclosure_window_nash_iff

/-- info: 'Vegas.Paper.utility_preservation_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.utility_preservation_honest

/-- info: 'Vegas.Paper.utility_preservation_deviation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.utility_preservation_deviation

/-- info: 'Vegas.Paper.nash_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.nash_equivalence

/-- info: 'Vegas.Paper.compilation_summary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compilation_summary

/-- info: 'Vegas.Paper.nash_equivalence_against' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.nash_equivalence_against

/-- info: 'Vegas.Paper.word_codegen_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.word_codegen_correct

/-- info: 'Vegas.Paper.guard_codegen_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.guard_codegen_correct

/-- info: 'Vegas.Paper.schedule_is_observable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.schedule_is_observable

/-- info: 'Vegas.Paper.order_aware_deviations_exist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.order_aware_deviations_exist

/-- info: 'Vegas.Paper.enforced_schedule_removes_order_choice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.enforced_schedule_removes_order_choice

/-- info: 'Vegas.Paper.commuting_effects_make_order_state_irrelevant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.commuting_effects_make_order_state_irrelevant

/-- info: 'Vegas.Paper.order_available_observable_and_useless' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.order_available_observable_and_useless

/-- info: 'Vegas.Paper.commutation_is_a_real_restriction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.commutation_is_a_real_restriction

/-- info: 'Vegas.Paper.active_participation_is_forced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.active_participation_is_forced

/-- info: 'Vegas.Paper.silence_is_inert_available_and_not_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.silence_is_inert_available_and_not_universal

/-- info: 'Vegas.Paper.declining_is_weaker_than_silence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.declining_is_weaker_than_silence

/-- info: 'Vegas.Paper.declining_is_always_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.declining_is_always_live

/-- info: 'Vegas.Paper.execution_diamond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.execution_diamond

/-- info: 'Vegas.Paper.public_submission_winning_deviation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.public_submission_winning_deviation

/-- info: 'Vegas.Paper.public_submission_not_nash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.public_submission_not_nash

/-- info: 'Vegas.Paper.observed_abort_optimal_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.observed_abort_optimal_rule

/-- info: 'Vegas.Paper.schedule_observation_confluence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.schedule_observation_confluence

/-- info: 'Vegas.Paper.ready_reveal_fence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.ready_reveal_fence

/-- info: 'Vegas.Paper.disclosure_window_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.disclosure_window_adequacy

/-- info: 'Vegas.Paper.observed_abort_no_information' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.observed_abort_no_information

/-- info: 'Vegas.Paper.observed_abort_payoff_information' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.observed_abort_payoff_information

/-! ## Whole-protocol request compilation -/

theorem request_compiler_law {Player : Type}
    {E : GameTheory.Protocol.ExecutionProtocol Player}
    (M : GameTheory.Protocol.InformationModel E) (recall : M.PerfectRecall)
    {Request : Player → Type} (interface : Runtime.RequestCompiler.Interface M Request)
    (horizon : Nat) (utility : E.History → Player → ℝ)
    (profile : (who : Player) → Runtime.RequestCompiler.Policy M (Request := Request) who) :
    ((Runtime.RequestCompiler.targetGame M interface horizon utility).form.play profile).map
        Prod.fst =
      (Runtime.RequestCompiler.sourceGame M horizon utility).form.play
        (fun who => Runtime.RequestCompiler.backtranslate M interface who (profile who)) :=
  Runtime.RequestCompiler.play_law M interface recall horizon utility profile

theorem request_compiler_mixed_law {Player : Type} [Fintype Player]
    {E : GameTheory.Protocol.ExecutionProtocol Player}
    (M : GameTheory.Protocol.InformationModel E) (recall : M.PerfectRecall)
    {Request : Player → Type} (interface : Runtime.RequestCompiler.Interface M Request)
    (horizon : Nat) (utility : E.History → Player → ℝ)
    (profile : (who : Player) → FinDist
      (Runtime.RequestCompiler.Policy M (Request := Request) who)) :
    ((Runtime.RequestCompiler.targetGame M interface horizon utility).mixed.form.play profile).map
        Prod.fst =
      (Runtime.RequestCompiler.sourceGame M horizon utility).mixed.form.play
        (fun who => (profile who).map (Runtime.RequestCompiler.backtranslate M interface who)) :=
  Runtime.RequestCompiler.mixed_play_law M interface recall horizon utility profile

theorem request_compiler_silence {Player : Type}
    {E : GameTheory.Protocol.ExecutionProtocol Player}
    (M : GameTheory.Protocol.InformationModel E) (recall : M.PerfectRecall)
    {Request : Player → Type} (interface : Runtime.RequestCompiler.Interface M Request)
    (horizon : Nat) (utility : E.History → Player → ℝ) :
    ((Runtime.RequestCompiler.targetGame M interface horizon utility).form.play
      (fun _ _ _ _ => none)).map Prod.fst =
    (Runtime.RequestCompiler.sourceGame M horizon utility).form.play
      (fun who => (interface.gate who).timeoutAction) :=
  Runtime.RequestCompiler.silence_law M interface recall horizon utility

theorem checked_request_nash_iff {Player : Type} [Fintype Player] [DecidableEq Player]
    {L : IExpr} (source : WFProgram Player L) [FiniteDomains source]
    {Request : Player → Type}
    (interface : Runtime.RequestCompiler.Interface source.game.arena.information Request)
    (profile : Profile source.game.behavioral.form.sig) :
    IsNash (source.requestGame interface).form
      (euPreference (source.requestGame interface).utility)
      ((source.behavioralRequestAdequacy interface).compileProfile profile) ↔
    IsNash source.game.behavioral.form (euPreference source.game.behavioral.utility) profile :=
  source.request_nash_iff interface profile

/-- info: 'Vegas.Paper.request_compiler_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.request_compiler_law

/-- info: 'Vegas.Paper.request_compiler_mixed_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.request_compiler_mixed_law

/-- info: 'Vegas.Paper.request_compiler_silence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.request_compiler_silence

/-- info: 'Vegas.Paper.checked_request_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.checked_request_nash_iff

/-! ## Private windows composed with the public serializer -/

theorem scheduled_request_honest_law
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (source : WFProgram Player L) [FiniteDomains source] {Request : Participant Player → Type}
    (interface : Runtime.RequestCompiler.Interface
      (Machine.compile source).serializedArena.information Request)
    (schedulerUtility : (Machine.compile source).serializedArena.History → ℝ)
    (scheduler : (Machine.compile source).serializedArena.information.BehavioralPolicy .scheduler)
    (profile : Profile source.game.behavioral.form.sig) :
    ((source.serializedRequestGame interface schedulerUtility).form.play
      (source.compileSerializedRequestProfile interface schedulerUtility scheduler profile)).map
        (fun state => state.1.state.base) =
    ((Machine.compile source).information.runBehavioral profile
      (Machine.compile source).graph.nodeCount).map
        GameTheory.Protocol.ExecutionProtocol.History.state :=
  source.serialized_request_honest_law interface schedulerUtility scheduler profile

theorem scheduled_request_deviation_law
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (source : WFProgram Player L) [FiniteDomains source] {Request : Participant Player → Type}
    (interface : Runtime.RequestCompiler.Interface
      (Machine.compile source).serializedArena.information Request)
    (schedulerUtility : (Machine.compile source).serializedArena.History → ℝ)
    (scheduler : (Machine.compile source).serializedArena.information.BehavioralPolicy .scheduler)
    (profile : Profile source.game.behavioral.form.sig) (who : Player)
    (replacement : (source.serializedRequestGame interface schedulerUtility).form.sig.Strategy
      (.player who)) :
    ∃ alternatives : FinDist ((Machine.compile source).information.BehavioralPolicy who),
      ((source.serializedRequestGame interface schedulerUtility).form.play
        (Profile.update
          (source.compileSerializedRequestProfile interface schedulerUtility scheduler profile)
          (.player who) replacement)).map (fun state => state.1.state.base) =
      alternatives.bind fun alternative =>
        ((Machine.compile source).information.runBehavioral
          (Function.update profile who alternative) (Machine.compile source).graph.nodeCount).map
            GameTheory.Protocol.ExecutionProtocol.History.state :=
  source.serialized_request_deviation_law
    interface schedulerUtility scheduler profile who replacement

theorem scheduled_request_nash_iff
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (source : WFProgram Player L) [FiniteDomains source] {Request : Participant Player → Type}
    (interface : Runtime.RequestCompiler.Interface
      (Machine.compile source).serializedArena.information Request)
    (schedulerUtility : (Machine.compile source).serializedArena.History → ℝ)
    (scheduler : (Machine.compile source).serializedArena.information.BehavioralPolicy .scheduler)
    (profile : Profile source.game.behavioral.form.sig) :
    Scheduled.IsPlayerNash (source.serializedRequestGame interface schedulerUtility)
      (source.compileSerializedRequestProfile interface schedulerUtility scheduler profile) ↔
    IsNash source.game.behavioral.form (euPreference source.game.behavioral.utility) profile :=
  source.serialized_request_nash_iff interface schedulerUtility scheduler profile

theorem scheduled_request_approximate_nash_iff
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (source : WFProgram Player L) [FiniteDomains source] {Request : Participant Player → Type}
    (interface : Runtime.RequestCompiler.Interface
      (Machine.compile source).serializedArena.information Request)
    (schedulerUtility : (Machine.compile source).serializedArena.History → ℝ)
    (scheduler : (Machine.compile source).serializedArena.information.BehavioralPolicy .scheduler)
    (profile : Profile source.game.behavioral.form.sig) (ε : ℝ) :
    (∀ who replacement,
      expectedUtility (source.serializedRequestGame interface schedulerUtility).utility
        (.player who) ((source.serializedRequestGame interface schedulerUtility).form.play
          (Profile.update
            (source.compileSerializedRequestProfile interface schedulerUtility scheduler profile)
            (.player who) replacement)) ≤
      expectedUtility (source.serializedRequestGame interface schedulerUtility).utility
        (.player who) ((source.serializedRequestGame interface schedulerUtility).form.play
          (source.compileSerializedRequestProfile
            interface schedulerUtility scheduler profile)) + ε) ↔
    IsεNash source.game.behavioral.form source.game.behavioral.utility ε profile :=
  source.serialized_request_approximate_nash_iff interface schedulerUtility scheduler profile ε

/-- info: 'Vegas.Paper.scheduled_request_honest_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.scheduled_request_honest_law

/-- info: 'Vegas.Paper.scheduled_request_deviation_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.scheduled_request_deviation_law

/-- info: 'Vegas.Paper.scheduled_request_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.scheduled_request_nash_iff

/-- info: 'Vegas.Paper.scheduled_request_approximate_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.scheduled_request_approximate_nash_iff

end Paper

end Vegas
