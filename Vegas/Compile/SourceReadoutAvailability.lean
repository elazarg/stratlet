/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageReadoutAvailability
import Vegas.Compile.ApplicationImageController
import Vegas.Compile.ApplicationPolicyProvenance

/-! # Availability of generated source-decision readouts

Graph readiness at a compiled source decision, native coverage, and typed
registration provenance suffice for the executable owner-local loader to
recover its complete declared choice footprint. Initial sealed provisioning
remains explicit: every initial field in that footprint must be public.
-/

noncomputable section

namespace Vegas.SourceDecisionSite

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A ready compiled source decision has an executable owner-local readout.
The graph configuration and its store occur only in the proof; the loader
itself consumes native public memory and the owner's command history. -/
theorem ownerReadout?_of_ready
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (image : ApplicationImage P L)
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (native : ApplicationImage.State P L) (hview : view.application = native.memory)
    (cfg : Config (compileCore prog fresh state).graph) (hrefines : native.Refines cfg)
    (hcovers : native.memory.Covers
      (compileCore prog fresh state).graph.initialFields.length)
    (hbindings : image.RegisteredBindings who
      (fun slot typed => ∃ spec : FieldSpec P L,
        (compileCore prog fresh state).graph.field? slot = some spec ∧
          typed.ty = spec.ty) history native)
    (hready : Ready (compileCore prog fresh state).graph cfg
      (site.compiledNode fresh state))
    (hinitial : ∀ ref ∈
        (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads,
      ∀ spec, (compileCore prog fresh state).graph.field? ref.field = some spec →
        ∀ value, spec.source = .initial value → spec.owner = none) :
    ∃ reads : ReadEnv L
        (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads,
      image.ownerReadout? who
        (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads
        history view = some reads := by
  let G := (compileCore prog fresh state).graph
  let event := (decisionSiteState site fresh state).commitEvent who guard
  have hrow : G.nodes[(site.compiledNode fresh state)]? = some event := by
    rcases decisionSite_compiledRow site fresh state with ⟨node, hnode, hnodeRow⟩
    have hnodeEq : node = site.compiledNode fresh state := by
      apply Fin.ext
      exact hnode
    simpa only [G, event, hnodeEq] using hnodeRow
  have hwf : G.WF := (compileCore prog fresh state).graphWF
  have hnodeWF := hwf (site.compiledNode fresh state) event hrow
  have hsem : event.sem =
      .commit who (eventGuardOf (decisionSiteState site fresh state) who guard) := rfl
  have hcoherent : StoreCoherent G cfg :=
    reachable_storeCoherent hwf hrefines.reachable
  obtain ⟨reads, hreads⟩ := hcoherent.readEnvOfReady hwf hrow hready
    (refs := (eventGuardOf
      (decisionSiteState site fresh state) who guard).choiceReads)
    (by
      intro ref href
      rw [hsem]
      exact Finset.mem_image.mpr ⟨ref, href, rfl⟩)
    (by
      intro ref href
      unfold Graph.nodeWFAt at hnodeWF
      rw [hsem] at hnodeWF
      obtain ⟨spec, hfield, htype, _⟩ := hnodeWF.2.2.2 ref href
      exact ⟨spec, hfield, htype⟩)
  refine ⟨reads, ?_⟩
  exact image.ownerReadout?_of_graph_reads who history view native hview cfg
    hrefines hcovers hbindings _ (by
      intro ref href
      unfold Graph.nodeWFAt at hnodeWF
      rw [hsem] at hnodeWF
      exact hnodeWF.2.2.2 ref href) hinitial reads hreads

/-- Under source-view agreement, the available native readout reconstructs
exactly the choosing owner's source-visible environment. -/
theorem ownerReadout?_of_ready_source_view
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (image : ApplicationImage P L)
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (native : ApplicationImage.State P L) (hview : view.application = native.memory)
    (cfg : Config (compileCore prog fresh state).graph) (hrefines : native.Refines cfg)
    (hcovers : native.memory.Covers
      (compileCore prog fresh state).graph.initialFields.length)
    (hbindings : image.RegisteredBindings who
      (fun slot typed => ∃ spec : FieldSpec P L,
        (compileCore prog fresh state).graph.field? slot = some spec ∧
          typed.ty = spec.ty) history native)
    (hready : Ready (compileCore prog fresh state).graph cfg
      (site.compiledNode fresh state))
    (hinitial : ∀ ref ∈
        (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads,
      ∀ spec, (compileCore prog fresh state).graph.field? ref.field = some spec →
        ∀ value, spec.source = .initial value → spec.owner = none)
    (env : VEnv L Δ)
    (hagrees : (decisionSiteState site fresh state).ViewAgrees who cfg.store env) :
    ∃ reads : ReadEnv L
        (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads,
      image.ownerReadout? who
          (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads
          history view = some reads ∧
        viewEnvOfReadEnv (decisionSiteState site fresh state) who reads =
          (env.toView who).eraseEnv := by
  obtain ⟨reads, hreadout⟩ := site.ownerReadout?_of_ready fresh state image
    history view native hview cfg hrefines hcovers hbindings hready hinitial
  refine ⟨reads, hreadout, ?_⟩
  exact viewEnvOfReadEnv_eq_sourceView (decisionSiteState site fresh state)
    who cfg.store env hagrees reads
    (site.ownerReadout?_graph_reads fresh state image history view native hview
      cfg hrefines hbindings.registrationMatches reads hreadout)

end Vegas.SourceDecisionSite

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Along an arbitrary supported execution from canonical public-memory
initialization, a ready source decision owned by the lifted player has an
actual executable local readout. Opposing policies, the environment, and the
schedule remain unrestricted. -/
theorem runPolicies_ownerReadout?_of_ready
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) (profile : SourceBehavioralProfile prog)
    (who : P) (players : P → (plan.image deadlineOf).application.PlayerPolicy)
    (hwho : players who = plan.liftProfile deadlineOf profile who)
    (environment : (plan.image deadlineOf).application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (next : (plan.image deadlineOf).application.PolicyExecution)
    (hnext : next ∈ ((plan.image deadlineOf).application.runPolicies
      players environment schedule
      (PolicyExecution.initial (plan.image deadlineOf).application
        (MessageApplication.State.initial (plan.image deadlineOf).application
          (ApplicationImage.State.initial
            (ApplicationImage.Memory.initial
              (compileCore prog fresh state).graph))))).support)
    {Δ : VCtx P L} {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (cfg : Config (compileCore prog fresh state).graph)
    (hrefines : next.native.application.Refines cfg)
    (hready : Ready (compileCore prog fresh state).graph cfg
      (site.compiledNode fresh state))
    (hinitial : ∀ ref ∈
        (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads,
      ∀ spec, (compileCore prog fresh state).graph.field? ref.field = some spec →
        ∀ value, spec.source = .initial value → spec.owner = none) :
    ∃ reads : ReadEnv L
        (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads,
      (plan.image deadlineOf).ownerReadout? who
          (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads
          (next.principalHistory who)
          (MessageApplication.State.observe (plan.image deadlineOf).application
            next.native who) = some reads := by
  have hcovers : next.native.application.memory.Covers
      (compileCore prog fresh state).graph.initialFields.length := by
    simpa only [BuildResult.graph, compileCore_initialFields] using
      plan.runPolicies_memory_covers deadlineOf players environment schedule next hnext
  have hbindings := plan.runPolicies_lifted_registeredBindings deadlineOf profile
    who players hwho environment
    (ApplicationImage.Memory.initial (compileCore prog fresh state).graph)
    (by intro field; rfl) schedule next hnext
  exact site.ownerReadout?_of_ready fresh state (plan.image deadlineOf)
    (next.principalHistory who)
    (MessageApplication.State.observe (plan.image deadlineOf).application next.native who)
    next.native.application
    rfl cfg hrefines hcovers hbindings hready hinitial

end Vegas.ApplicationPlan

/-- info: 'Vegas.SourceDecisionSite.ownerReadout?_of_ready' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.ownerReadout?_of_ready

/-- info: 'Vegas.SourceDecisionSite.ownerReadout?_of_ready_source_view' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.ownerReadout?_of_ready_source_view

/-- info: 'Vegas.ApplicationPlan.runPolicies_ownerReadout?_of_ready' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.runPolicies_ownerReadout?_of_ready
