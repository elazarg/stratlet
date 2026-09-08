/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourcePolicy
import Vegas.EventGraph.KernelSupport

/-! # Coupled written-order source and graph execution -/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem typedValue_eq_cast {left right : L.Ty} (h : left = right)
    (value : L.Val left) :
    (⟨left, value⟩ : TypedValue L) = ⟨right, cast (congrArg L.Val h) value⟩ := by
  cases h
  rfl

/-- The node appended by the next source instruction, viewed in the final
compiled graph. -/
structure CompiledNext {Γ : VCtx P L} (state : BuildState P L Γ)
    (result : BuildResult P L) (event : EventNode P L) where
  node : Fin result.graph.nodeCount
  index : (node : Nat) = state.nodes.length
  row : result.graph.nodes[node]? = some event

/-- A one-node extension that remains a prefix of the terminal compiler state
has a canonical next node in the final graph. -/
def compiledNext {Γ : VCtx P L} (state : BuildState P L Γ)
    (result : BuildResult P L) (event : EventNode P L)
    (hprefix : state.nodes ++ [event] <+: result.nodes) :
    CompiledNext state result event := by
  have hlt : state.nodes.length < result.nodes.length := by
    rcases hprefix with ⟨suffix, hsuffix⟩
    rw [← hsuffix]
    simp
  let node : Fin result.graph.nodeCount :=
    ⟨state.nodes.length, by
      simpa [BuildResult.graph, Graph.nodeCount] using hlt⟩
  refine ⟨node, rfl, ?_⟩
  change result.nodes[state.nodes.length]? = some event
  rcases hprefix with ⟨suffix, hsuffix⟩
  rw [← hsuffix]
  simp

theorem CompiledNext.nodeRow_eq {Γ : VCtx P L} {state : BuildState P L Γ}
    {result : BuildResult P L} {event : EventNode P L}
    (next : CompiledNext state result event) :
    result.graph.nodeRow next.node = event :=
  Option.some.inj ((result.graph.nodes_get?_nodeRow next.node).symm.trans next.row)

theorem CompiledNext.nodeTarget_eq {Γ : VCtx P L} {state : BuildState P L Γ}
    {result : BuildResult P L} {event : EventNode P L}
    (next : CompiledNext state result event)
    (hinitial : result.initialFields = state.initialFields) :
    result.graph.nodeTarget next.node = state.nextField := by
  simp [Graph.nodeTarget, BuildState.nextField, BuildState.nextNode,
    next.index, BuildResult.graph, hinitial]

/-- A source environment coupled to an actual reachable configuration of the
final compiled graph at an intermediate compiler state. -/
structure CoupledState {Γ : VCtx P L} (G : Graph P L)
    (state : BuildState P L Γ) where
  graph : ReachableConfig G
  source : VEnv L Γ
  agrees : state.Agrees graph.1.store source

/-- Exactly the compiler prefix already traversed in written source order has
been completed. -/
def CoupledState.CompletedPrefix {Γ : VCtx P L} {G : Graph P L}
    {state : BuildState P L Γ} (current : CoupledState G state) : Prop :=
  ∀ node : Fin G.nodeCount,
    node ∈ current.graph.1.done ↔ (node : Nat) < state.nodes.length

/-- A coupled execution positioned exactly at the next source instruction. -/
structure CoupledAt {Γ : VCtx P L} (G : Graph P L)
    (state : BuildState P L Γ) where
  current : CoupledState G state
  completedPrefix : current.CompletedPrefix

/-- The next compiler-allocated node is ready once precisely the preceding
written-order prefix is complete. -/
theorem CoupledState.nextReady {Γ : VCtx P L} {G : Graph P L}
    {state : BuildState P L Γ} (current : CoupledState G state)
    (hprefix : current.CompletedPrefix)
    (node : Fin G.nodeCount) (hnode : (node : Nat) = state.nodes.length) :
    Ready G current.graph.1 node := by
  refine ⟨?_, ?_⟩
  · rw [hprefix node, hnode]
    exact Nat.lt_irrefl _
  · intro prior hprior
    rw [hprefix prior]
    rw [← hnode]
    exact G.prereq_lt hprior

/-- Complete the actual primitive write for the next compiler field and
extend the coupled source environment by the same value. -/
def CoupledState.completeCons {Γ : VCtx P L} {G : Graph P L}
    {state : BuildState P L Γ} {name : VarId} {bindTy : BindTy P L}
    (added : BuildState P L ((name, bindTy) :: Γ))
    (current : CoupledState G state) (node : Fin G.nodeCount)
    (write : PolicyWrite current.graph node)
    (value : L.Val bindTy.base)
    (hwritten : write.written = { ty := bindTy.base, value := value })
    (htarget : G.nodeTarget node = state.nextField)
    (hhere : added.fieldOf (VHasVar.here (x := name) (τ := bindTy)) =
      state.nextField)
    (hthere : ∀ {query queryTy} (h : VHasVar Γ query queryTy),
      added.fieldOf (VHasVar.there h) = state.fieldOf h) :
    CoupledState G added := by
  let nextConfig := current.graph.1.completeNode write.event.node write.written
  have hreachable : Reachable G nextConfig :=
    .step current.graph.2 write.event write.supported
  refine
    { graph := ⟨nextConfig, hreachable⟩
      source := current.source.cons value
      agrees := ?_ }
  intro query queryTy h
  cases h with
  | here =>
      simp [nextConfig, Config.completeNode, hhere, ← htarget,
        write.event_node, hwritten, Store.getAs, Store.set_eq,
        TypedValue.as?]
  | there old =>
      rw [hthere old]
      have hne : state.fieldOf old ≠ G.nodeTarget node := by
        rw [htarget]
        exact Nat.ne_of_lt (state.fieldOf_lt old)
      simpa [nextConfig, Config.completeNode, write.event_node,
        Store.getAs_set_ne _ hne write.written] using current.agrees old

/-- Completing the next written-order node advances the exact completed
prefix by one. -/
theorem CoupledState.completeCons_completedPrefix
    {Γ : VCtx P L} {G : Graph P L} {state : BuildState P L Γ}
    {name : VarId} {bindTy : BindTy P L}
    (added : BuildState P L ((name, bindTy) :: Γ))
    (current : CoupledState G state) (hprefix : current.CompletedPrefix)
    (node : Fin G.nodeCount) (hnode : (node : Nat) = state.nodes.length)
    (write : PolicyWrite current.graph node)
    (value : L.Val bindTy.base)
    (hwritten : write.written = { ty := bindTy.base, value := value })
    (htarget : G.nodeTarget node = state.nextField)
    (hhere : added.fieldOf (VHasVar.here (x := name) (τ := bindTy)) =
      state.nextField)
    (hthere : ∀ {query queryTy} (h : VHasVar Γ query queryTy),
      added.fieldOf (VHasVar.there h) = state.fieldOf h)
    (hnodes : added.nodes.length = state.nodes.length + 1) :
    CoupledState.CompletedPrefix
      (current.completeCons added node write value hwritten htarget hhere hthere) := by
  intro other
  change other ∈ insert write.event.node current.graph.1.done ↔
    (other : Nat) < added.nodes.length
  rw [write.event_node, Finset.mem_insert, hprefix other, hnodes]
  simp only [Fin.ext_iff]
  omega

/-- Package agreement and completed-prefix preservation for one source-order
write, ready for structural recursion on the source continuation. -/
def CoupledAt.completeCons
    {Γ : VCtx P L} {G : Graph P L} {state : BuildState P L Γ}
    {name : VarId} {bindTy : BindTy P L}
    (added : BuildState P L ((name, bindTy) :: Γ))
    (current : CoupledAt G state) (node : Fin G.nodeCount)
    (hnode : (node : Nat) = state.nodes.length)
    (write : PolicyWrite current.current.graph node)
    (value : L.Val bindTy.base)
    (hwritten : write.written = { ty := bindTy.base, value := value })
    (htarget : G.nodeTarget node = state.nextField)
    (hhere : added.fieldOf (VHasVar.here (x := name) (τ := bindTy)) =
      state.nextField)
    (hthere : ∀ {query queryTy} (h : VHasVar Γ query queryTy),
      added.fieldOf (VHasVar.there h) = state.fieldOf h)
    (hnodes : added.nodes.length = state.nodes.length + 1) :
    CoupledAt G added :=
  ⟨current.current.completeCons added node write value hwritten htarget hhere hthere,
    current.current.completeCons_completedPrefix added current.completedPrefix node hnode
      write value hwritten htarget hhere hthere hnodes⟩

/-- Agreement preservation for an appended source sample. -/
def CoupledState.completeSample {Γ : VCtx P L} {G : Graph P L}
    {state : BuildState P L Γ} {name : VarId} {ty : L.Ty}
    (dist : L.DistExpr (erasePubVCtx Γ) ty) (fresh : Fresh name Γ)
    (current : CoupledState G state) (node : Fin G.nodeCount)
    (write : PolicyWrite current.graph node) (value : L.Val ty)
    (hwritten : write.written = { ty := ty, value := value })
    (htarget : G.nodeTarget node = state.nextField) :
    CoupledState G (state.addSampleEvent name dist fresh).1 :=
  current.completeCons _ node write value hwritten htarget
    (BuildState.addSampleEvent_fieldOf_here state name dist fresh)
    (BuildState.addSampleEvent_fieldOf_there state name dist fresh)

/-- Agreement preservation for an appended source commitment. -/
def CoupledState.completeCommit {Γ : VCtx P L} {G : Graph P L}
    {state : BuildState P L Γ} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (fresh : Fresh name Γ) (current : CoupledState G state)
    (node : Fin G.nodeCount) (write : PolicyWrite current.graph node)
    (value : L.Val ty)
    (hwritten : write.written = { ty := ty, value := value })
    (htarget : G.nodeTarget node = state.nextField) :
    CoupledState G (state.addCommitEvent name who guard fresh).1 :=
  current.completeCons _ node write value hwritten htarget
    (BuildState.addCommitEvent_fieldOf_here state name who guard fresh)
    (BuildState.addCommitEvent_fieldOf_there state name who guard fresh)

/-- Agreement preservation for an appended source reveal. -/
def CoupledState.completeReveal {Γ : VCtx P L} {G : Graph P L}
    {state : BuildState P L Γ} {name sourceName : VarId} {who : P} {ty : L.Ty}
    (source : VHasVar Γ sourceName (.sealed who ty)) (fresh : Fresh name Γ)
    (current : CoupledState G state) (node : Fin G.nodeCount)
    (write : PolicyWrite current.graph node)
    (hwritten : write.written =
      (⟨ty, @VEnv.get P L Γ sourceName (.sealed who ty)
        current.source source⟩ : TypedValue L))
    (htarget : G.nodeTarget node = state.nextField) :
    CoupledState G (state.addRevealEvent name who source fresh).1 :=
  current.completeCons (bindTy := .pub ty) _ node write
    (@VEnv.get P L Γ sourceName (.sealed who ty) current.source source)
    hwritten htarget
    (BuildState.addRevealEvent_fieldOf_here state name who source fresh)
    (BuildState.addRevealEvent_fieldOf_there state name who source fresh)

/-- Execute a source sample at its actual next compiled node. -/
def coupledSampleStep [Fintype P] {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (tail : VegasCore P L ((name, .pub ty) :: Γ))
    (fresh : FreshBindings (.sample name dist tail))
    (state : BuildState P L Γ)
    (policies : CommitPolicyProfile (compileCore (.sample name dist tail) fresh state).graph)
    (hguards : GuardLive (compileCore (.sample name dist tail) fresh state).graph)
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state) :
    FinDist (CoupledAt (compileCore (.sample name dist tail) fresh state).graph
      (state.addSampleEvent name dist fresh.1).1) := by
  let added := state.addSampleEvent name dist fresh.1
  let result := compileCore (.sample name dist tail) fresh state
  let event := state.sampleEvent dist
  have hprefix : state.nodes ++ [event] <+: result.nodes := by
    change state.nodes ++ [event] <+: (compileCore tail fresh.2 added.1).nodes
    simpa [added, event, BuildState.sampleEvent] using
      compileCore_nodes_prefix tail fresh.2 added.1
  let next := compiledNext state result event hprefix
  have hready := current.current.nextReady current.completedPrefix next.node next.index
  exact (policyValueLaw result.graphWF hguards policies current.current.graph next.node
    hready).bindOnSupport fun write hwrite => by
      have hrow := next.nodeRow_eq
      have hty : (result.graph.nodeRow next.node).ty = ty := by
        simpa [event, BuildState.sampleEvent, eventDistOf] using
          congrArg EventNode.ty hrow
      let value := EventGraph.PolicyWrite.nodeValue result.graphWF hguards policies
        current.current.graph next.node hready write hwrite
      have hwritten := EventGraph.PolicyWrite.written_eq_nodeValue result.graphWF hguards
        policies current.current.graph next.node hready write hwrite
      have htyped : write.written = (⟨ty, cast (congrArg L.Val hty) value⟩ : TypedValue L) := by
        exact hwritten.trans (typedValue_eq_cast hty value)
      exact FinDist.pure (current.completeCons added.1 next.node next.index write
        (cast (congrArg L.Val hty) value) htyped
        (next.nodeTarget_eq (compileCore_initialFields _ fresh state))
        (BuildState.addSampleEvent_fieldOf_here state name dist fresh.1)
        (BuildState.addSampleEvent_fieldOf_there state name dist fresh.1)
        (by simp [added]))

/-- Execute a source commitment at its actual next compiled node. -/
def coupledCommitStep [Fintype P] {Γ : VCtx P L} {name : VarId} {who : P}
    {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fresh : FreshBindings (.commit name who guard tail))
    (state : BuildState P L Γ)
    (policies : CommitPolicyProfile (compileCore (.commit name who guard tail) fresh state).graph)
    (hguards : GuardLive (compileCore (.commit name who guard tail) fresh state).graph)
    (current : CoupledAt (compileCore (.commit name who guard tail) fresh state).graph state) :
    FinDist (CoupledAt (compileCore (.commit name who guard tail) fresh state).graph
      (state.addCommitEvent name who guard fresh.1).1) := by
  let added := state.addCommitEvent name who guard fresh.1
  let result := compileCore (.commit name who guard tail) fresh state
  let event := state.commitEvent who guard
  have hprefix : state.nodes ++ [event] <+: result.nodes := by
    change state.nodes ++ [event] <+: (compileCore tail fresh.2 added.1).nodes
    simpa [added, event, BuildState.commitEvent] using
      compileCore_nodes_prefix tail fresh.2 added.1
  let next := compiledNext state result event hprefix
  have hready := current.current.nextReady current.completedPrefix next.node next.index
  exact (policyValueLaw result.graphWF hguards policies current.current.graph next.node
    hready).bindOnSupport fun write hwrite => by
      have hrow := next.nodeRow_eq
      have hty : (result.graph.nodeRow next.node).ty = ty := by
        simpa [event, BuildState.commitEvent, eventGuardOf] using
          congrArg EventNode.ty hrow
      let value := EventGraph.PolicyWrite.nodeValue result.graphWF hguards policies
        current.current.graph next.node hready write hwrite
      have hwritten := EventGraph.PolicyWrite.written_eq_nodeValue result.graphWF hguards
        policies current.current.graph next.node hready write hwrite
      have htyped : write.written =
          (⟨ty, cast (congrArg L.Val hty) value⟩ : TypedValue L) :=
        hwritten.trans (typedValue_eq_cast hty value)
      exact FinDist.pure (current.completeCons added.1 next.node next.index write
        (cast (congrArg L.Val hty) value) htyped
        (next.nodeTarget_eq (compileCore_initialFields _ fresh state))
        (BuildState.addCommitEvent_fieldOf_here state name who guard fresh.1)
        (BuildState.addCommitEvent_fieldOf_there state name who guard fresh.1)
        (by simp [added]))

/-- Execute a source reveal at its actual deterministic compiled node. -/
def coupledRevealStep [Fintype P] {Γ : VCtx P L} {name sourceName : VarId}
    {who : P} {ty : L.Ty} (source : VHasVar Γ sourceName (.sealed who ty))
    (tail : VegasCore P L ((name, .pub ty) :: Γ))
    (fresh : FreshBindings (.reveal name who sourceName source tail))
    (state : BuildState P L Γ)
    (policies : CommitPolicyProfile
      (compileCore (.reveal name who sourceName source tail) fresh state).graph)
    (hguards : GuardLive
      (compileCore (.reveal name who sourceName source tail) fresh state).graph)
    (current : CoupledAt
      (compileCore (.reveal name who sourceName source tail) fresh state).graph state) :
    FinDist (CoupledAt
      (compileCore (.reveal name who sourceName source tail) fresh state).graph
      (state.addRevealEvent name who source fresh.1).1) := by
  let added := state.addRevealEvent name who source fresh.1
  let result := compileCore (.reveal name who sourceName source tail) fresh state
  let event := state.revealEvent who source
  let sourceValue : L.Val ty :=
    @VEnv.get P L Γ sourceName (.sealed who ty) current.current.source source
  have hprefix : state.nodes ++ [event] <+: result.nodes := by
    change state.nodes ++ [event] <+: (compileCore tail fresh.2 added.1).nodes
    simpa [added, event, BuildState.revealEvent] using
      compileCore_nodes_prefix tail fresh.2 added.1
  let next := compiledNext state result event hprefix
  have hready := current.current.nextReady current.completedPrefix next.node next.index
  exact (policyValueLaw result.graphWF hguards policies current.current.graph next.node
    hready).bindOnSupport fun write hwrite => by
      have hmapped : write.written ∈
          ((policyValueLaw result.graphWF hguards policies current.current.graph next.node
            hready).map PolicyWrite.written).support := by
        rw [FinDist.support_map]
        exact ⟨write, hwrite, rfl⟩
      have hsource : Store.getAs current.current.graph.1.store
          (state.fieldOf source) ty = some sourceValue :=
        current.current.agrees source
      have hreveal := map_written_policyValueLaw_of_reveal result.graphWF hguards policies
        current.current.graph next.node hready event (state.fieldOf source) next.row rfl
        sourceValue (by
          simpa [event, BuildState.revealEvent] using hsource)
      rw [hreveal, FinDist.mem_support_pure] at hmapped
      exact FinDist.pure
        ⟨current.current.completeReveal (source := source) fresh.1 next.node write
            (by simpa [event, BuildState.revealEvent] using hmapped)
            (next.nodeTarget_eq (compileCore_initialFields _ fresh state)),
          current.current.completeCons_completedPrefix (bindTy := .pub ty) added.1
            current.completedPrefix
            next.node next.index write sourceValue
            (by simpa [event, BuildState.revealEvent] using hmapped)
            (next.nodeTarget_eq (compileCore_initialFields _ fresh state))
            (BuildState.addRevealEvent_fieldOf_here state name who source fresh.1)
            (BuildState.addRevealEvent_fieldOf_there state name who source fresh.1)
            (by simp [added])⟩

/-- Execute every source instruction in written order through the actual
compiled graph kernels, retaining source/store agreement at every prefix. -/
def runCoupledSource [Fintype P] :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
    (fresh : FreshBindings prog) → (state : BuildState P L Γ) →
    (policies : CommitPolicyProfile (compileCore prog fresh state).graph) →
    GuardLive (compileCore prog fresh state).graph →
    CoupledAt (compileCore prog fresh state).graph state →
    FinDist (CoupledAt (compileCore prog fresh state).graph
      (compileCore prog fresh state).terminalState)
  | _, .ret _, _, _, _policies, _hguards, current => FinDist.pure current
  | _, .sample name dist tail, fresh, state, policies, hguards, current =>
      let added := state.addSampleEvent name dist fresh.1
      (coupledSampleStep dist tail fresh state policies hguards current).bind fun next =>
        runCoupledSource tail fresh.2 added.1 policies hguards next
  | _, .commit name who guard tail, fresh, state, policies, hguards, current =>
      let added := state.addCommitEvent name who guard fresh.1
      (coupledCommitStep guard tail fresh state policies hguards current).bind fun next =>
        runCoupledSource tail fresh.2 added.1 policies hguards next
  | _, .reveal name who _sourceName source tail, fresh, state, policies, hguards, current =>
      let added := state.addRevealEvent name who source fresh.1
      (coupledRevealStep source tail fresh state policies hguards current).bind fun next =>
        runCoupledSource tail fresh.2 added.1 policies hguards next

/-- The initial compiler state and graph configuration form the empty coupled
prefix whenever their stores agree on the source input. -/
def initialCoupledAt {Γ : VCtx P L} {G : Graph P L}
    (state : BuildState P L Γ) (env : VEnv L Γ)
    (hagrees : state.Agrees (Config.initial G).store env)
    (hempty : state.nodes = []) : CoupledAt G state := by
  refine ⟨⟨⟨Config.initial G, .initial⟩, env, hagrees⟩, ?_⟩
  intro node
  simp [Config.initial, hempty]

end Vegas.ToEventGraph
