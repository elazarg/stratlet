/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationGuardSoundness
import Vegas.Compile.ApplicationImageRefinement

/-!
# Resolving generated opaque bindings in the source graph

At a ready generated binding instruction, the represented graph has a legal
commit step.  A well-typed private preparation determines its value; absent or
ill-typed preparation leaves the value proof-only.  The latter case uses source
legality only to inhabit the source type, while the backend's unrestricted
guard certificate makes that value legal at the concurrent graph readout.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace SourceDecisionSite

/-- A ready generated opaque binding has a legal graph commit step. Any value
recoverable from the canonical private preparation is the value selected by
that step; no recoverability premise is imposed. -/
theorem binding_resolution_step
    {Γ Δ : VCtx P L} {prog : VegasCore P L Γ} {who : P} {name : VarId}
    {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (build : BuildState P L Γ)
    (initial : VEnv L Γ) (legal : Legal prog)
    (unrestricted : UnrestrictedBinding guard)
    (native : ApplicationImage.State P L)
    (cfg : Config (compileCore prog fresh build).graph)
    (hrep : native.memory.Represents cfg)
    (hreachable : Reachable (compileCore prog fresh build).graph cfg)
    (sourceSlot : Nat) (handle : CommitmentHandle P Nat)
    (hhandle : handle = (who, sourceSlot))
    (hnotDone : native.memory.done
      (site.bindingCode fresh build sourceSlot).node = false)
    (hrequires : (site.bindingCode fresh build sourceSlot).requires.all
      native.memory.done = true) :
    ∃ value : L.Val ty,
      Nonempty (CommitStep (compileCore prog fresh build).graph cfg who
        ⟨site.compiledNode fresh build, ⟨ty, value⟩⟩) ∧
      ∀ recovered,
        (native.prepared.lookup handle).bind (fun typed => typed.as? ty) =
          some recovered →
        recovered = value := by
  subst handle
  let graph := (compileCore prog fresh build).graph
  let node := site.compiledNode fresh build
  let siteState := decisionSiteState site fresh build
  let compiledGuard := eventGuardOf siteState who guard
  have hrow : graph.nodes[node]? = some (siteState.commitEvent who guard) := by
    rcases decisionSite_compiledRow site fresh build with
      ⟨located, hlocated, hrow⟩
    have heq : located = node := by
      apply Fin.ext
      exact hlocated
    subst located
    exact hrow
  have hready : Ready graph cfg node := by
    constructor
    · intro hdone
      have hnativeDone := (hrep.completed node).2 hdone
      change native.memory.done node.val = false at hnotDone
      rw [hnotDone] at hnativeDone
      contradiction
    · intro prior hprior
      apply (hrep.completed prior).1
      apply List.all_eq_true.mp hrequires prior.val
      change prior.val ∈ graph.messagePrerequisites node
      exact (graph.mem_messagePrerequisites node prior).2 hprior
  have hcoherent : StoreCoherent graph cfg :=
    reachable_storeCoherent (compileCore prog fresh build).graphWF hreachable
  have hnodeWF := (compileCore prog fresh build).graphWF node
    (siteState.commitEvent who guard) hrow
  have hguardSem :
      (siteState.commitEvent who guard).sem = .commit who compiledGuard := rfl
  have hexReads := hcoherent.readEnvOfReady
    (compileCore prog fresh build).graphWF hrow hready
    (refs := compiledGuard.choiceReads)
    (by
      intro ref href
      rw [hguardSem]
      exact Finset.mem_image.mpr ⟨ref, href, rfl⟩)
    (by
      intro ref href
      unfold Graph.nodeWFAt at hnodeWF
      rw [hguardSem] at hnodeWF
      rcases hnodeWF.2.2.2 ref href with ⟨spec, hfield, htype, _⟩
      exact ⟨spec, hfield, htype⟩)
  obtain ⟨reads, hreads⟩ := hexReads
  obtain ⟨baseline⟩ := site.context_nonempty initial legal
  let fallback : L.Val ty :=
    Classical.choose
      (site.satisfiable legal ((baseline.toView who).eraseEnv))
  let recovered := (native.prepared.lookup (who, sourceSlot)).bind
    (fun typed => typed.as? ty)
  let value : L.Val ty := recovered.getD fallback
  have hguard : compiledGuard.eval value reads = true :=
    site.unrestricted_guard_eval fresh build initial legal unrestricted reads value
  refine ⟨value, ⟨?_⟩, ?_⟩
  · exact
      { row := siteState.commitEvent who guard
        guard := compiledGuard
        row_get := hrow
        sem_eq := rfl
        ready := hready
        value := value
        value_ok := by
          have hguardType : compiledGuard.ty = ty := rfl
          simp [TypedValue.as?, hguardType]
        env := reads
        env_ok := hreads
        guard_ok := hguard }
  · intro decoded hdecoded
    change recovered = some decoded at hdecoded
    simp [value, hdecoded]

end SourceDecisionSite

end Vegas

/-- info: 'Vegas.SourceDecisionSite.binding_resolution_step' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.binding_resolution_step
