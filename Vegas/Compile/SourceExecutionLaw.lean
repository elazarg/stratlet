/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceExecution
import Vegas.Compile.SourceOutcome

/-! # Probability law of coupled source execution -/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Once the typed-written marginal is identified, support inversion recovers
the corresponding statically typed value law exactly. -/
theorem policyNodeValueLaw_eq {G : Graph P L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (state : ReachableConfig G) (node : Fin G.nodeCount)
    (hready : Ready G state.1 node)
    (expected : FinDist (L.Val (G.nodeRow node).ty))
    (hwritten :
      (policyValueLaw hwf hguards policies state node hready).map
          PolicyWrite.written =
        expected.map (G.nodeTypedValue node)) :
    (policyValueLaw hwf hguards policies state node hready).bindOnSupport
        (fun write hmem => FinDist.pure
          (EventGraph.PolicyWrite.nodeValue hwf hguards policies state node hready
            write hmem)) = expected := by
  apply FinDist.map_injective (f := G.nodeTypedValue node)
    (fun left right heq => by simpa [Graph.nodeTypedValue] using heq)
  exact (EventGraph.PolicyWrite.map_nodeValue_bindOnSupport
    hwf hguards policies state node hready).trans hwritten

omit [Fintype P] in
/-- A supported write whose source extension uses precisely its written value
has the source marginal prescribed by the typed write law. -/
private theorem map_supported_source_cons
    {Γ : VCtx P L} {name : VarId} {binding : BindTy P L}
    {G : Graph P L} {state : BuildState P L Γ}
    (added : BuildState P L ((name, binding) :: Γ))
    (current : CoupledAt G state) (node : Fin G.nodeCount)
    (law : FinDist (PolicyWrite current.current.graph node))
    (advance : ∀ write ∈ law.support, CoupledAt G added)
    (value : ∀ write ∈ law.support, L.Val binding.base)
    (hsource : ∀ write hwrite,
      (advance write hwrite).current.source = current.current.source.cons (value write hwrite))
    (hwritten : ∀ write hwrite,
      write.written = (⟨binding.base, value write hwrite⟩ : TypedValue L))
    (expected : FinDist (L.Val binding.base))
    (hlaw : law.map PolicyWrite.written =
      expected.map fun value => (⟨binding.base, value⟩ : TypedValue L)) :
    (law.bindOnSupport fun write hwrite => FinDist.pure (advance write hwrite)).map
        (fun next => next.current.source) =
      expected.map (fun value => current.current.source.cons value) := by
  have hvalues : (law.bindOnSupport fun write hwrite =>
      FinDist.pure (value write hwrite)) = expected := by
    apply FinDist.map_injective (f := fun value => (⟨binding.base, value⟩ : TypedValue L))
      (fun left right heq => by simpa using heq)
    rw [FinDist.map_bindOnSupport]
    calc
      _ = law.bind (fun write => FinDist.pure write.written) := by
        apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
        intro write hwrite
        simp [hwritten write hwrite]
      _ = _ := by rw [← FinDist.map_eq_bind]; exact hlaw
  rw [← hvalues, FinDist.map_bindOnSupport, FinDist.map_bindOnSupport]
  apply FinDist.bindOnSupport_congr
  intro write hwrite
  simp [hsource write hwrite]

omit [Fintype P] [DecidableEq P] in
private theorem typedValue_cast {left right : L.Ty} (h : left = right)
    (value : L.Val left) :
    (⟨left, value⟩ : TypedValue L) = ⟨right, cast (congrArg L.Val h) value⟩ := by
  cases h
  rfl

theorem coupledSampleStep_source {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (tail : VegasCore P L ((name, .pub ty) :: Γ))
    (fresh : FreshBindings (.sample name dist tail))
    (state : BuildState P L Γ)
    (policies : CommitPolicyProfile (compileCore (.sample name dist tail) fresh state).graph)
    (hguards : GuardLive (compileCore (.sample name dist tail) fresh state).graph)
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state) :
    (coupledSampleStep dist tail fresh state policies hguards current).map
        (fun next => next.current.source) =
      (L.evalDist dist current.current.source.eraseSampleEnv).map
        (fun value => current.current.source.cons value) := by
  let result := compileCore (.sample name dist tail) fresh state
  have hprefix : state.nodes ++ [state.sampleEvent dist] <+: result.nodes := by
    exact compileCore_nodes_prefix tail fresh.2 (state.addSampleEvent name dist fresh.1).1
  let next := compiledNext state result (state.sampleEvent dist) hprefix
  have hty : (result.graph.nodeRow next.node).ty = ty :=
    congrArg EventNode.ty next.nodeRow_eq
  unfold coupledSampleStep
  dsimp only
  apply map_supported_source_cons
  · intro write hwrite
    rfl
  · intro write hwrite
    exact (PolicyWrite.written_eq_nodeValue _ _ _ _ _ _ write hwrite).trans
      (typedValue_cast hty _)
  · obtain ⟨reads, hreads, _⟩ := eventDistOf_readEnv_agrees_sourceEnvOfStore
      state dist current.current.graph.1.store
      (BuildState.Agrees.available current.current.agrees)
    have hlaw := map_written_policyValueLaw_of_sample result.graphWF hguards policies
      current.current.graph next.node
      (current.current.nextReady current.completedPrefix next.node next.index)
      (state.sampleEvent dist) (eventDistOf state dist) next.row rfl reads hreads
    change (policyValueLaw result.graphWF hguards policies current.current.graph next.node _).map
      PolicyWrite.written = _
    rw [hlaw]
    rw [eventDistOf_eval_eq_source state dist _ _ current.current.agrees reads hreads]
    rfl

omit [Fintype P] in
/-- Every source decision occurrence has exactly its compiled source kernel. -/
def SourcePolicyMatches {Γ : VCtx P L} (prog : VegasCore P L Γ)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (policies : CommitPolicyProfile (compileCore prog fresh state).graph)
    (profile : SourceBehavioralProfile prog) : Prop :=
  ∀ (who : P) {Δ : VCtx P L} {name : VarId} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool)
    (site : SourceDecisionSite who prog Δ name ty guard)
    (node : Fin (compileCore prog fresh state).graph.nodeCount)
    (_hindex : (node : Nat) = (decisionSiteState site fresh state).nodes.length)
    (_hrow : (compileCore prog fresh state).graph.nodes[node]? =
      some ((decisionSiteState site fresh state).commitEvent who guard))
    (hsem : ((compileCore prog fresh state).graph.nodeRow node).sem =
      .commit who (eventGuardOf (decisionSiteState site fresh state) who guard))
    (reads : ReadEnv L (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads),
    policies who node (eventGuardOf (decisionSiteState site fresh state) who guard) hsem reads =
      compileSourceDecision (decisionSiteState site fresh state) who guard (profile who site) reads

theorem coupledCommitStep_source {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fresh : FreshBindings (.commit name who guard tail))
    (state : BuildState P L Γ)
    (policies : CommitPolicyProfile (compileCore (.commit name who guard tail) fresh state).graph)
    (hguards : GuardLive (compileCore (.commit name who guard tail) fresh state).graph)
    (profile : SourceBehavioralProfile (.commit name who guard tail))
    (hmatch : SourcePolicyMatches (.commit name who guard tail) fresh state policies profile)
    (current : CoupledAt (compileCore (.commit name who guard tail) fresh state).graph state) :
    (coupledCommitStep guard tail fresh state policies hguards current).map
        (fun next => next.current.source) =
      (profile who (.here guard tail) ((current.current.source.toView who).eraseEnv)).map
        (fun choice => current.current.source.cons choice.1) := by
  let result := compileCore (.commit name who guard tail) fresh state
  have hprefix : state.nodes ++ [state.commitEvent who guard] <+: result.nodes := by
    exact compileCore_nodes_prefix tail fresh.2 (state.addCommitEvent name who guard fresh.1).1
  let next := compiledNext state result (state.commitEvent who guard) hprefix
  have hty : (result.graph.nodeRow next.node).ty = ty :=
    congrArg EventNode.ty next.nodeRow_eq
  have hsem : (result.graph.nodeRow next.node).sem =
      .commit who (eventGuardOf state who guard) :=
    congrArg EventNode.sem next.nodeRow_eq
  unfold coupledCommitStep
  dsimp only
  have hfactor := FinDist.map_comp
    (fun (value : L.Val ty) =>
      (current.current.source.cons value : VEnv L ((name, .sealed who ty) :: Γ)))
    Subtype.val
    (profile who (.here guard tail) ((current.current.source.toView who).eraseEnv))
  refine Eq.trans ?_ hfactor
  apply map_supported_source_cons
  · intro write hwrite
    rfl
  · intro write hwrite
    exact (PolicyWrite.written_eq_nodeValue _ _ _ _ _ _ write hwrite).trans
      (typedValue_cast hty _)
  · obtain ⟨reads, hreads⟩ := eventGuardOf_readEnv_of_sourceStoreAvailable
      state who guard current.current.graph.1.store
      (BuildState.Agrees.available current.current.agrees)
    have hlaw := map_written_policyValueLaw_of_commitKernel result.graphWF hguards policies
      current.current.graph next.node
      (current.current.nextReady current.completedPrefix next.node next.index)
      who (eventGuardOf state who guard) hsem reads hreads
    change (policyValueLaw result.graphWF hguards policies current.current.graph next.node _).map
      PolicyWrite.written = _
    refine hlaw.trans ?_
    have hkernel : policies who next.node (eventGuardOf state who guard) hsem reads =
        compileSourceDecision state who guard (profile who (.here guard tail)) reads :=
      hmatch who guard (.here guard tail) next.node next.index next.row hsem reads
    refine (congrArg (fun law => law.map
      (fun value => (⟨ty, value.1⟩ : TypedValue L))) hkernel).trans ?_
    have hdecision := compileSourceDecision_law state who guard
      (profile who (.here guard tail)) _ _
      (BuildState.Agrees.view current.current.agrees who) reads hreads
    have hmapped := congrArg (fun law => law.map
      (fun value => (⟨ty, value⟩ : TypedValue L))) hdecision
    simpa only [FinDist.map_comp, Function.comp_def, eventGuardOf, BindTy.base] using hmapped

theorem coupledRevealStep_source {Γ : VCtx P L} {name sourceName : VarId}
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
    (coupledRevealStep source tail fresh state policies hguards current).map
        (fun next => next.current.source) =
      FinDist.pure ((current.current.source.cons
        (@VEnv.get P L Γ sourceName (.sealed who ty) current.current.source source)) :
          VEnv L ((name, .pub ty) :: Γ)) := by
  unfold coupledRevealStep
  dsimp only
  apply FinDist.map_bindOnSupport_const
  intro write hwrite
  rw [FinDist.map_pure]
  rfl

/-- The source marginal of the actual coupled graph-kernel execution is the
independent written-order source denotation. -/
theorem runCoupledSource_source :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
    (fresh : FreshBindings prog) → (state : BuildState P L Γ) →
    (policies : CommitPolicyProfile (compileCore prog fresh state).graph) →
    (hguards : GuardLive (compileCore prog fresh state).graph) →
    (profile : SourceBehavioralProfile prog) →
    SourcePolicyMatches prog fresh state policies profile →
    (current : CoupledAt (compileCore prog fresh state).graph state) →
    (runCoupledSource prog fresh state policies hguards current).map
        (fun final => cast (congrArg (VEnv L)
          (compileCore_terminalCtx_eq_sourceTerminalCtx prog fresh state)) final.current.source) =
      denoteSource prog profile current.current.source
  | _, .ret _, _, _, _, _, _, _, _ => by
      simp [runCoupledSource, denoteSource]
  | _, .sample name dist tail, fresh, state, policies, hguards, profile, hmatch, current => by
      let added := (state.addSampleEvent name dist fresh.1).1
      have htail : SourcePolicyMatches tail fresh.2 added policies profile.afterSample := by
        intro who Δ x ty guard site node hindex hrow hsem reads
        exact hmatch who guard (.sample site) node hindex hrow hsem reads
      calc
        _ = (coupledSampleStep dist tail fresh state policies hguards current).bind
            (fun next => denoteSource tail profile.afterSample next.current.source) := by
          rw [runCoupledSource, FinDist.map_bind]
          apply FinDist.bind_congr
          intro next _
          exact runCoupledSource_source tail fresh.2 added policies hguards
            profile.afterSample htail next
        _ = _ := by
          have hm := congrArg (fun law => law.bind (denoteSource tail profile.afterSample))
            (coupledSampleStep_source dist tail fresh state policies hguards current)
          simpa only [FinDist.bind_map, denoteSource] using hm
  | _, .commit name who guard tail, fresh, state, policies, hguards, profile, hmatch, current => by
      let added := (state.addCommitEvent name who guard fresh.1).1
      have htail : SourcePolicyMatches tail fresh.2 added policies profile.afterCommit := by
        intro actor Δ x ty innerGuard site node hindex hrow hsem reads
        exact hmatch actor innerGuard (.commit site) node hindex hrow hsem reads
      calc
        _ = (coupledCommitStep guard tail fresh state policies hguards current).bind
            (fun next => denoteSource tail profile.afterCommit next.current.source) := by
          rw [runCoupledSource, FinDist.map_bind]
          apply FinDist.bind_congr
          intro next _
          exact runCoupledSource_source tail fresh.2 added policies hguards
            profile.afterCommit htail next
        _ = _ := by
          have hm := congrArg (fun law => law.bind (denoteSource tail profile.afterCommit))
            (coupledCommitStep_source guard tail fresh state policies hguards
              profile hmatch current)
          simpa only [FinDist.bind_map, denoteSource] using hm
  | _, .reveal name who _ source tail, fresh, state, policies, hguards,
      profile, hmatch, current => by
      let added := (state.addRevealEvent name who source fresh.1).1
      have htail : SourcePolicyMatches tail fresh.2 added policies profile.afterReveal := by
        intro actor Δ x ty guard site node hindex hrow hsem reads
        exact hmatch actor guard (.reveal site) node hindex hrow hsem reads
      calc
        _ = (coupledRevealStep source tail fresh state policies hguards current).bind
            (fun next => denoteSource tail profile.afterReveal next.current.source) := by
          rw [runCoupledSource, FinDist.map_bind]
          apply FinDist.bind_congr
          intro next _
          exact runCoupledSource_source tail fresh.2 added policies hguards
            profile.afterReveal htail next
        _ = _ := by
          have hm := congrArg (fun law => law.bind (denoteSource tail profile.afterReveal))
            (coupledRevealStep_source source tail fresh state policies hguards current)
          simpa only [FinDist.bind_map, FinDist.pure_bind, denoteSource] using hm

omit [Fintype P] in
/-- The compiler-produced profile satisfies the decision-site invariant. -/
theorem compileSourcePolicy_matches {Γ : VCtx P L} (prog : VegasCore P L Γ)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (hempty : state.nodes = []) (profile : SourceBehavioralProfile prog) :
    SourcePolicyMatches prog fresh state
      (fun who => compileSourcePolicy prog fresh state hempty who (profile who)) profile := by
  intro who Δ name ty guard site node hindex hrow hsem reads
  exact compileSourcePolicy_at prog fresh state hempty who (profile who)
    guard site node hindex hrow hsem reads

/-- Compiling a complete source profile and executing the actual graph kernels
preserves the independent source outcome law. -/
theorem runCoupledSource_compileSourcePolicy_source {Γ : VCtx P L}
    (prog : VegasCore P L Γ) (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (hempty : state.nodes = []) (hguards : GuardLive (compileCore prog fresh state).graph)
    (profile : SourceBehavioralProfile prog)
    (current : CoupledAt (compileCore prog fresh state).graph state) :
    (runCoupledSource prog fresh state
      (fun who => compileSourcePolicy prog fresh state hempty who (profile who))
      hguards current).map
        (fun final => cast (congrArg (VEnv L)
          (compileCore_terminalCtx_eq_sourceTerminalCtx prog fresh state)) final.current.source) =
      denoteSource prog profile current.current.source :=
  runCoupledSource_source prog fresh state _ hguards profile
    (compileSourcePolicy_matches prog fresh state hempty profile) current

end Vegas.ToEventGraph
