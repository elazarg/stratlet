/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Compiler
import Vegas.Core.SmallStep
import Vegas.EventGraph.Execution

/-!
# Source support adequacy

This module relates a terminal reachable compiled event-graph store back to the
written-order, support-level source semantics.  Probability weights remain in
the event graph and informed-protocol denotations; `SmallStep.Star` records
exactly that the reconstructed draws and choices form a possible source run.
-/

noncomputable section

namespace Vegas

namespace ToEventGraph

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem compiledHead_semantic
    {Γ : VCtx P L} (state : BuildState P L Γ)
    (result : BuildResult P L) (event : EventNode P L)
    (hprefix : state.nodes ++ [event] <+: result.nodes)
    (cfg : Config result.graph) (reachable : Reachable result.graph cfg)
    (terminal : Terminal result.graph cfg) :
    ∃ node : Fin result.graph.nodeCount,
      (node : Nat) = state.nodes.length ∧
      result.graph.nodes[node]? = some event ∧
      NodeValueValid result.graph cfg node := by
  have hnodeLt : state.nodes.length < result.nodes.length := by
    rcases hprefix with ⟨suffix, hsuffix⟩
    rw [← hsuffix]
    simp
  let node : Fin result.graph.nodeCount :=
    ⟨state.nodes.length, by
      simpa [BuildResult.graph, Graph.nodeCount] using hnodeLt⟩
  have hrow : result.graph.nodes[(node : Nat)]? = some event := by
    change result.nodes[(node : Nat)]? = some event
    rcases hprefix with ⟨suffix, hsuffix⟩
    rw [← hsuffix]
    simp [node]
  exact
    ⟨node, rfl, hrow,
      reachable_validDoneValues result.graphWF reachable node (terminal node)⟩

/-- Compiling a suffix only appends graph nodes. -/
theorem compileCore_nodes_prefix :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
      (fresh : FreshBindings prog) → (state : BuildState P L Γ) →
      state.nodes <+: (compileCore prog fresh state).nodes
  | _, .ret _payoffs, _fresh, state => List.prefix_refl state.nodes
  | _, .sample name dist tail, fresh, state => by
      let added := state.addSampleEvent name dist fresh.1
      have hadded : state.nodes <+: added.1.nodes := by
        rw [show added.1.nodes =
            state.nodes ++ [state.sampleEvent dist] by
          exact BuildState.addSampleEvent_nodes state name dist fresh.1]
        exact state.nodes.prefix_append _
      exact hadded.trans (compileCore_nodes_prefix tail fresh.2 added.1)
  | _, .commit name who guard tail, fresh, state => by
      let added := state.addCommitEvent name who guard fresh.1
      have hadded : state.nodes <+: added.1.nodes := by
        rw [show added.1.nodes =
            state.nodes ++ [state.commitEvent who guard] by
          exact BuildState.addCommitEvent_nodes
            state name who guard fresh.1]
        exact state.nodes.prefix_append _
      exact hadded.trans (compileCore_nodes_prefix tail fresh.2 added.1)
  | _, .reveal (b := ty) name who source sourceProof tail,
      fresh, state => by
      let added := state.addRevealEvent name who sourceProof fresh.1
      have hadded : state.nodes <+: added.1.nodes := by
        rw [show added.1.nodes =
            state.nodes ++ [state.revealEvent who sourceProof] by
          exact BuildState.addRevealEvent_nodes
            state name who sourceProof fresh.1]
        exact state.nodes.prefix_append _
      exact hadded.trans (compileCore_nodes_prefix tail fresh.2 added.1)

/-- Lookup inside a node prefix is unchanged in the compiled suffix result. -/
theorem compileCore_nodes_get?_of_lt
    {Γ : VCtx P L} (prog : VegasCore P L Γ)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    {node : Nat} (hlt : node < state.nodes.length) :
    (compileCore prog fresh state).nodes[node]? = state.nodes[node]? := by
  rcases compileCore_nodes_prefix prog fresh state with ⟨suffix, hsuffix⟩
  rw [← hsuffix, List.getElem?_append_left hlt]

/-- Reconstructing an environment from reads already known to equal a given
environment returns that environment. -/
theorem sourceEnvOfStore_eq_of_get
    {Γ : VCtx P L}
    (state : BuildState P L Γ) (store : Store L)
    (available :
      ∀ {name bindTy} (h : VHasVar Γ name bindTy),
        ∃ value,
          Store.getAs store (state.fieldOf h) bindTy.base = some value)
    (env : VEnv L Γ)
    (hagrees :
      ∀ {name bindTy} (h : VHasVar Γ name bindTy),
        Store.getAs store (state.fieldOf h) bindTy.base =
          some (env.get h)) :
    sourceEnvOfStore state store available = env := by
  funext name bindTy h
  have hsource := sourceEnvOfStore_get state store available h
  exact Option.some.inj (hsource.symm.trans (hagrees h))

/-- The initial compiler field map reads back the source environment used to
construct it. -/
theorem initialState_getAs :
    {Γ : VCtx P L} → (env : VEnv L Γ) → (wctx : WFCtx Γ) →
      ∀ {name bindTy} (h : VHasVar Γ name bindTy),
        Store.getAs
          (({ initialFields := (initialState Γ env wctx).initialFields,
               nodes := [] } : Graph P L).initialStore)
          ((initialState Γ env wctx).fieldOf h) bindTy.base =
            some (env.get h)
  | [], _env, _wctx, _name, _bindTy, h => nomatch h
  | (headName, headTy) :: Γ, env, wctx, name, bindTy, h => by
      let tail := initialState Γ (VEnv.tail env) (WFCtx.tail wctx)
      let value : L.Val headTy.base := env.get VHasVar.here
      let field : InitialField P L :=
        { ty := headTy.base, owner := headTy.owner, value := value }
      cases h with
      | here =>
          let graph : Graph P L :=
            { initialFields := tail.initialFields ++ [field], nodes := [] }
          have hfield :
              graph.field? tail.initialFields.length =
                some
                  { ty := headTy.base, owner := headTy.owner,
                    source := .initial value } := by
            simp [graph, Graph.field?, field]
          change Store.getAs graph.initialStore tail.initialFields.length
              headTy.base = some value
          have hstore :
              graph.initialStore tail.initialFields.length =
                some { ty := headTy.base, value := value } := by
            unfold Graph.initialStore
            rw [hfield]
            rfl
          unfold Store.getAs
          rw [hstore]
          simp [TypedValue.as?]
      | there htail =>
          have ih := initialState_getAs (VEnv.tail env)
            (WFCtx.tail wctx) htail
          let oldGraph : Graph P L :=
            { initialFields := tail.initialFields, nodes := [] }
          let graph : Graph P L :=
            { initialFields := tail.initialFields ++ [field], nodes := [] }
          have hfield :
              graph.field? (tail.fieldOf htail) =
                oldGraph.field? (tail.fieldOf htail) := by
            have hold := tail.fieldOf_lt htail
            simp [graph, oldGraph, Graph.field?, hold,
              List.getElem?_append_left]
            omega
          change Store.getAs graph.initialStore (tail.fieldOf htail)
              bindTy.base = some (env.get (VHasVar.there htail))
          change Store.getAs oldGraph.initialStore (tail.fieldOf htail)
              bindTy.base = some ((VEnv.tail env).get htail) at ih
          have hstore :
              graph.initialStore (tail.fieldOf htail) =
                oldGraph.initialStore (tail.fieldOf htail) := by
            unfold Graph.initialStore
            rw [hfield]
          unfold Store.getAs at ih ⊢
          rw [hstore]
          exact ih

/-- A terminal reachable execution of a compiled suffix reconstructs an actual
written-order source run from any source environment agreeing with the
compiler state's field map. -/
theorem compileCore_sourceStar :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
      (fresh : FreshBindings prog) → (state : BuildState P L Γ) →
      (cfg : Config (compileCore prog fresh state).graph) →
      Reachable (compileCore prog fresh state).graph cfg →
      Terminal (compileCore prog fresh state).graph cfg →
      (sourceEnv : VEnv L Γ) →
      (∀ {name bindTy} (h : VHasVar Γ name bindTy),
        Store.getAs cfg.store (state.fieldOf h) bindTy.base =
          some (sourceEnv.get h)) →
      ∃ terminalEnv :
          VEnv L (compileCore prog fresh state).terminalCtx,
        SmallStep.Star
          { ctx := Γ, env := sourceEnv, cont := prog }
          { ctx := (compileCore prog fresh state).terminalCtx,
            env := terminalEnv,
            cont := .ret (compileCore prog fresh state).sourcePayoffs } ∧
        evalPayoffs? (compileCore prog fresh state).payoffs cfg.store =
          some (evalPayoffs
            (compileCore prog fresh state).sourcePayoffs terminalEnv)
  | Γ, .ret payoffs, _fresh, state, cfg, _reachable, _terminal,
      sourceEnv, hagrees => by
      let available :
          ∀ {name bindTy} (h : VHasVar Γ name bindTy),
            ∃ value,
              Store.getAs cfg.store (state.fieldOf h) bindTy.base =
                some value :=
        fun h => ⟨sourceEnv.get h, hagrees h⟩
      have henv :
          sourceEnvOfStore state cfg.store available = sourceEnv :=
        sourceEnvOfStore_eq_of_get state cfg.store available sourceEnv hagrees
      refine ⟨sourceEnv, SmallStep.Star.refl _, ?_⟩
      have hpayoff :=
        evalPayoffs?_compilePayoffs_eq_sourceEnvOfStore
          state payoffs cfg.store available
      simpa [compileCore, henv] using hpayoff
  | Γ, .sample (b := ty) name dist tail, fresh, state, cfg,
      reachable, terminal,
      sourceEnv, hagrees => by
      let event : EventNode P L := state.sampleEvent dist
      let added := state.addSampleEvent name dist fresh.1
      let result := compileCore tail fresh.2 added.1
      have hprefix : added.1.nodes <+: result.nodes :=
        compileCore_nodes_prefix tail fresh.2 added.1
      have hheadPrefix : state.nodes ++ [event] <+: result.nodes := by
        simpa [added, event] using hprefix
      rcases compiledHead_semantic state result event hheadPrefix cfg reachable terminal with
        ⟨node, hnode, hrow, row, hrow', hsem⟩
      have : row = event := Option.some.inj (hrow'.symm.trans hrow)
      subst row
      dsimp [event, BuildState.sampleEvent] at hsem
      rcases hsem with ⟨value, htarget, readEnv, hreadEnv, hsupport⟩
      change L.Val ty at value
      change Store.getAs cfg.store (result.graph.nodeTarget node) ty =
        some value at htarget
      let available :
          ∀ {query queryTy} (h : VHasVar Γ query queryTy),
            ∃ value,
              Store.getAs cfg.store (state.fieldOf h) queryTy.base =
                some value :=
        fun h => ⟨sourceEnv.get h, hagrees h⟩
      have henv :
          sourceEnvOfStore state cfg.store available = sourceEnv :=
        sourceEnvOfStore_eq_of_get state cfg.store available sourceEnv hagrees
      have hreadAgrees :
          ∀ {depName depTy}
            (hvar : HasVar (erasePubVCtx Γ) depName depTy)
            (hmem : depName ∈ L.distDeps dist),
            sourceValuePub state readEnv hvar
                (distReadRefs_mem state dist hvar hmem) =
              VEnv.erasePubEnv
                (sourceEnvOfStore state cfg.store available)
                depName depTy hvar :=
        eventDistOf_readEnv_agrees_sourceEnvOfStore_of_readEnv
          state dist cfg.store available readEnv hreadEnv
      have heval :
          (eventDistOf state dist).eval readEnv =
            L.evalDist dist sourceEnv.eraseSampleEnv := by
        apply eventDistOf_eval_eq_eval
        intro depName depTy hvar hmem
        have hread := hreadAgrees hvar hmem
        rw [henv] at hread
        simpa [VEnv.eraseSampleEnv] using hread
      have hsourceSupport :
          value ∈ (L.evalDist dist sourceEnv.eraseSampleEnv).support := by
        rw [← heval]
        exact hsupport
      have htargetField :
          result.graph.nodeTarget node = added.1.fieldOf VHasVar.here := by
        simp [result, BuildResult.graph, Graph.nodeTarget, hnode, added,
          BuildState.nextField, BuildState.nextNode,
          compileCore_initialFields]
      let nextEnv : VEnv L ((name, .pub ty) :: Γ) :=
        VEnv.cons value sourceEnv
      have hnextAgrees :
          ∀ {query queryTy}
            (h : VHasVar ((name, .pub ty) :: Γ)
              query queryTy),
            Store.getAs cfg.store (added.1.fieldOf h) queryTy.base =
              some (nextEnv.get h) := by
        intro query queryTy h
        cases h with
        | here =>
            simpa [nextEnv, htargetField] using htarget
        | there htail =>
            simpa [nextEnv, added] using hagrees htail
      rcases
          compileCore_sourceStar tail fresh.2 added.1 cfg reachable terminal
            nextEnv hnextAgrees with
        ⟨terminalEnv, htailStar, hpayoff⟩
      have hhead :
          SmallStep
            { ctx := Γ, env := sourceEnv,
              cont := .sample name dist tail }
            { ctx := (name, .pub ty) :: Γ,
              env := nextEnv, cont := tail } := by
        exact SmallStep.sample dist tail value hsourceSupport
      exact
        ⟨terminalEnv,
          (SmallStep.Star.single hhead).trans htailStar,
          hpayoff⟩
  | Γ, .commit (b := ty) name who guard tail, fresh, state, cfg,
      reachable, terminal,
      sourceEnv, hagrees => by
      let event : EventNode P L := state.commitEvent who guard
      let added := state.addCommitEvent name who guard fresh.1
      let result := compileCore tail fresh.2 added.1
      have hprefix : added.1.nodes <+: result.nodes :=
        compileCore_nodes_prefix tail fresh.2 added.1
      have hheadPrefix : state.nodes ++ [event] <+: result.nodes := by
        simpa [added, event] using hprefix
      rcases compiledHead_semantic state result event hheadPrefix cfg reachable terminal with
        ⟨node, hnode, hrow, row, hrow', hsem⟩
      have : row = event := Option.some.inj (hrow'.symm.trans hrow)
      subst row
      dsimp [event, BuildState.commitEvent] at hsem
      rcases hsem with ⟨value, htarget, readEnv, hreadEnv, hguard⟩
      change L.Val ty at value
      change Store.getAs cfg.store (result.graph.nodeTarget node) ty =
        some value at htarget
      let available :
          ∀ {query queryTy} (h : VHasVar Γ query queryTy),
            ∃ value,
              Store.getAs cfg.store (state.fieldOf h) queryTy.base =
                some value :=
        fun h => ⟨sourceEnv.get h, hagrees h⟩
      have henv :
          sourceEnvOfStore state cfg.store available = sourceEnv :=
        sourceEnvOfStore_eq_of_get state cfg.store available sourceEnv hagrees
      have hview :=
        viewEnvOfReadEnv_eq_eraseEnv_sourceEnvOfStore
          state who cfg.store available readEnv hreadEnv
      have hsourceGuard :
          evalGuard guard value ((sourceEnv.toView who).eraseEnv) = true := by
        rw [henv] at hview
        rw [← hview]
        exact (eventGuardOf_eval_eq_eval
          state who guard value readEnv).symm.trans hguard
      have htargetField :
          result.graph.nodeTarget node = added.1.fieldOf VHasVar.here := by
        simp [result, BuildResult.graph, Graph.nodeTarget, hnode, added,
          BuildState.nextField, BuildState.nextNode,
          compileCore_initialFields]
      let nextEnv :
          VEnv L ((name, .sealed who ty) :: Γ) :=
        VEnv.cons value sourceEnv
      have hnextAgrees :
          ∀ {query queryTy}
            (h : VHasVar ((name, .sealed who ty) :: Γ) query queryTy),
            Store.getAs cfg.store (added.1.fieldOf h) queryTy.base =
              some (nextEnv.get h) := by
        intro query queryTy h
        cases h with
        | here =>
            simpa [nextEnv, htargetField] using htarget
        | there htail =>
            simpa [nextEnv, added] using hagrees htail
      rcases
          compileCore_sourceStar tail fresh.2 added.1 cfg reachable terminal
            nextEnv hnextAgrees with
        ⟨terminalEnv, htailStar, hpayoff⟩
      have hhead :
          SmallStep
            { ctx := Γ, env := sourceEnv,
              cont := .commit name who guard tail }
            { ctx := (name, .sealed who ty) :: Γ,
              env := nextEnv, cont := tail } := by
        exact SmallStep.commit guard tail value hsourceGuard
      exact
        ⟨terminalEnv,
          (SmallStep.Star.single hhead).trans htailStar,
          hpayoff⟩
  | Γ, .reveal (b := ty) name who source sourceProof tail,
      fresh, state, cfg, reachable, terminal, sourceEnv, hagrees => by
      let event : EventNode P L := state.revealEvent who sourceProof
      let added := state.addRevealEvent name who sourceProof fresh.1
      let result := compileCore tail fresh.2 added.1
      have hprefix : added.1.nodes <+: result.nodes :=
        compileCore_nodes_prefix tail fresh.2 added.1
      have hheadPrefix : state.nodes ++ [event] <+: result.nodes := by
        simpa [added, event] using hprefix
      rcases compiledHead_semantic state result event hheadPrefix cfg reachable terminal with
        ⟨node, hnode, hrow, row, hrow', hsem⟩
      have : row = event := Option.some.inj (hrow'.symm.trans hrow)
      subst row
      dsimp [event, BuildState.revealEvent] at hsem
      rcases hsem with ⟨value, htarget, hsource⟩
      let sourceValue : L.Val ty :=
        @VEnv.get P L Γ source (.sealed who ty) sourceEnv sourceProof
      have hsourceValue : value = sourceValue :=
        Option.some.inj (hsource.symm.trans (hagrees sourceProof))
      have htargetField :
          result.graph.nodeTarget node = added.1.fieldOf VHasVar.here := by
        simp [result, BuildResult.graph, Graph.nodeTarget, hnode, added,
          BuildState.nextField, BuildState.nextNode,
          compileCore_initialFields]
      let nextEnv : VEnv L ((name, .pub ty) :: Γ) :=
        VEnv.cons sourceValue sourceEnv
      have hnextAgrees :
          ∀ {query queryTy}
            (h : VHasVar ((name, .pub ty) :: Γ)
              query queryTy),
            Store.getAs cfg.store (added.1.fieldOf h) queryTy.base =
              some (nextEnv.get h) := by
        intro query queryTy h
        cases h with
        | here =>
            simpa [nextEnv, htargetField, hsourceValue] using htarget
        | there htail =>
            simpa [nextEnv, added] using hagrees htail
      rcases
          compileCore_sourceStar tail fresh.2 added.1 cfg reachable terminal
            nextEnv hnextAgrees with
        ⟨terminalEnv, htailStar, hpayoff⟩
      have hhead :
          SmallStep
            { ctx := Γ, env := sourceEnv,
              cont := .reveal name who source sourceProof tail }
            { ctx := (name, .pub ty) :: Γ,
              env := nextEnv, cont := tail } := by
        exact SmallStep.reveal sourceProof tail
      exact
        ⟨terminalEnv,
          (SmallStep.Star.single hhead).trans htailStar,
          hpayoff⟩

/-- Every terminal reachable event-graph execution of a compiled source program
is the image of a possible written-order source run with the same terminal
payoff. -/
theorem compile_sourceStar
    (source : GraphProgram P L)
    (cfg : Config (compile source).graph)
    (reachable : Reachable (compile source).graph cfg)
    (terminal : Terminal (compile source).graph cfg) :
    ∃ terminalEnv : VEnv L (compile source).terminalCtx,
      SmallStep.Star
        { ctx := source.Γ, env := source.env, cont := source.prog }
        { ctx := (compile source).terminalCtx,
          env := terminalEnv,
          cont := .ret (compile source).sourcePayoffs } ∧
      evalPayoffs? (compile source).payoffs cfg.store =
        some (evalPayoffs (compile source).sourcePayoffs terminalEnv) := by
  let initial := initialState source.Γ source.env source.wctx
  let state := BuildState.fromInitial initial
  have hagrees :
      ∀ {name bindTy} (h : VHasVar source.Γ name bindTy),
        Store.getAs cfg.store (state.fieldOf h) bindTy.base =
          some (source.env.get h) := by
    intro name bindTy h
    have hfieldLt :
        state.fieldOf h < (compile source).graph.initialFields.length := by
      have hlt := initial.fieldOf_lt h
      have hinitial :=
        compileCore_initialFields source.prog source.fresh state
      simpa [compile, state, BuildResult.graph] using
        (show state.fieldOf h <
            (compileCore source.prog source.fresh state).initialFields.length by
          rw [hinitial]
          exact hlt)
    have hreachable :
        Store.getAs cfg.store (state.fieldOf h) bindTy.base =
          Store.getAs (compile source).graph.initialStore
            (state.fieldOf h) bindTy.base :=
      reachable_getAs_of_initial_field
        (ty := bindTy.base) reachable hfieldLt
    let initialGraph : Graph P L :=
      { initialFields := initial.initialFields, nodes := [] }
    have hstateField : state.fieldOf h = initial.fieldOf h := rfl
    have hcompiledInitial :
        (compile source).graph.initialFields = initial.initialFields := by
      change
        (compileCore source.prog source.fresh state).initialFields =
          initial.initialFields
      exact
        (compileCore_initialFields source.prog source.fresh state).trans rfl
    have hfield :
        (compile source).graph.field? (initial.fieldOf h) =
          initialGraph.field? (initial.fieldOf h) := by
      have hlt := initial.fieldOf_lt h
      unfold Graph.field?
      rw [hcompiledInitial]
      simp [initialGraph, hlt]
    have hstore :
        (compile source).graph.initialStore (initial.fieldOf h) =
          initialGraph.initialStore (initial.fieldOf h) := by
      unfold Graph.initialStore
      exact congrArg
        (fun field =>
          match field with
          | none => none
          | some spec => spec.initialValue?) hfield
    calc
      Store.getAs cfg.store (state.fieldOf h) bindTy.base =
          Store.getAs (compile source).graph.initialStore
            (state.fieldOf h) bindTy.base := hreachable
      _ = Store.getAs initialGraph.initialStore
            (initial.fieldOf h) bindTy.base := by
          rw [hstateField]
          unfold Store.getAs
          rw [hstore]
      _ = some (source.env.get h) := by
          exact initialState_getAs source.env source.wctx h
  exact compileCore_sourceStar source.prog source.fresh state cfg
    reachable terminal source.env hagrees

end ToEventGraph

end Vegas
