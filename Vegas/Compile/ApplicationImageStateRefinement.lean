/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.BindingImageRefinement
import Vegas.EventGraph.Confluence

/-! # Binding provenance in public-application refinement

The graph configuration is proof-only. Each accepted handle refers to a
present sealed graph field owned by that principal. A recoverable frozen value
agrees with the graph value; absent or ill-typed frozen values impose no value
equation. This permits unopenable bindings without fabricating a native secret.
-/

namespace Vegas.ApplicationImage

open EventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr} {G : Graph P L}

/-- Accepted handles and their possibly unopenable snapshots agree with
present, privately owned fields in the represented graph state. -/
def State.BindingsRepresent (state : State P L) (cfg : Config G) : Prop :=
  ∀ field handle, state.memory.accepted field = some handle →
    ∃ (spec : FieldSpec P L) (value : L.Val spec.ty),
      G.field? field = some spec ∧ spec.owner = some handle.1 ∧
      Store.getAs cfg.store field spec.ty = some value ∧
      ∀ recovered, (state.frozen field).bind (fun typed => typed.as? spec.ty) =
        some recovered → recovered = value

/-- Completing a previously unfinished node cannot overwrite an earlier
represented binding: that binding already has a typed value in the graph. -/
theorem State.BindingsRepresent.completeNode
    {state : State P L} {cfg : Config G}
    (hbindings : state.BindingsRepresent cfg) (hreachable : Reachable G cfg)
    (node : Fin G.nodeCount) (hnode : node ∉ cfg.done) (written : TypedValue L) :
    state.BindingsRepresent (cfg.completeNode node written) := by
  intro field handle haccepted
  obtain ⟨spec, value, hfield, howner, hvalue, hfrozen⟩ := hbindings field handle haccepted
  have hne : field ≠ G.nodeTarget node := by
    intro heq
    rw [heq, reachable_getAs_nodeTarget_eq_none hreachable node hnode spec.ty] at hvalue
    contradiction
  refine ⟨spec, value, hfield, howner, ?_, hfrozen⟩
  simpa [Config.completeNode, Store.getAs, Store.set, hne] using hvalue

/-- A batch of fresh graph writes preserves every existing accepted binding.
The nodes need only be unfinished at the original checkpoint; no hidden source
context or intermediate runtime observation is required. -/
theorem State.BindingsRepresent.completeNodes
    {state : State P L} {cfg : Config G}
    (hbindings : state.BindingsRepresent cfg) (hreachable : Reachable G cfg)
    (steps : List (Fin G.nodeCount × TypedValue L))
    (hfresh : ∀ step ∈ steps, step.1 ∉ cfg.done) :
    state.BindingsRepresent (cfg.completeNodes steps) := by
  intro field handle haccepted
  obtain ⟨spec, value, hfield, howner, hvalue, hfrozen⟩ := hbindings field handle haccepted
  refine ⟨spec, value, hfield, howner, ?_, hfrozen⟩
  rw [cfg.completeNodes_getAs_of_not_targets steps]
  · exact hvalue
  · intro step hstep heq
    rw [heq, reachable_getAs_nodeTarget_eq_none hreachable step.1
      (hfresh step hstep) spec.ty] at hvalue
    contradiction

/-- Completing a pair of fresh nodes changes no previously accepted binding. -/
theorem State.BindingsRepresent.completePair
    {state : State P L} {cfg : Config G}
    (hbindings : state.BindingsRepresent cfg) (hreachable : Reachable G cfg)
    (choice publication : Fin G.nodeCount) (written : TypedValue L)
    (hchoice : choice ∉ cfg.done) (hpublication : publication ∉ cfg.done) :
    state.BindingsRepresent
      ((cfg.completeNode choice written).completeNode publication written) := by
  apply hbindings.completeNodes hreachable [(choice, written), (publication, written)]
  intro step hstep
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hstep
  rcases hstep with rfl | rfl
  · exact hchoice
  · exact hpublication

/-- A typed accepted snapshot is recorded with the value written by its graph
commit. Unopenable snapshots impose no equation and remain permitted. -/
theorem State.BindingsRepresent.bind
    {state : State P L} {cfg : Config G}
    (hbindings : state.BindingsRepresent cfg) (hreachable : Reachable G cfg)
    (hwf : G.WF) (code : BindingCode P) (node : Fin G.nodeCount)
    (hfieldTarget : code.sourceField = G.nodeTarget node)
    (handle : CommitmentHandle P Nat) (howner : handle.1 = code.owner)
    (written : TypedValue L)
    (hstep : CommitStep G cfg code.owner ⟨node, written⟩)
    (hsnapshot : ∀ recovered,
      (state.prepared.lookup handle).bind (fun typed => typed.as? written.ty) = some recovered →
        recovered = written.value) :
    (state.bind code handle).BindingsRepresent (cfg.completeNode node written) := by
  have hnodeWF := hwf node hstep.row hstep.row_get
  unfold Graph.nodeWFAt at hnodeWF
  rw [hstep.sem_eq] at hnodeWF
  have hty : hstep.row.ty = written.ty :=
    hnodeWF.2.1.trans (congrArg TypedValue.ty hstep.written_eq_action)
  let spec : FieldSpec P L :=
    { ty := written.ty, owner := some code.owner, source := .event node }
  have hfield : G.field? code.sourceField = some spec := by
    rw [hfieldTarget, G.field?_nodeTarget hstep.row_get, hty, hnodeWF.2.2.1]
  have hprior := hbindings.completeNode hreachable node hstep.ready.1 written
  intro field accepted haccepted
  by_cases heq : field = code.sourceField
  · subst field
    have heqHandle : handle = accepted := by
      simpa [State.bind] using haccepted
    subst accepted
    refine ⟨spec, written.value, hfield, ?_, ?_, ?_⟩
    · simpa only [spec] using congrArg some howner.symm
    · simp [spec, hfieldTarget, Config.completeNode, Store.getAs, TypedValue.as?]
    · simpa [State.bind, spec] using hsnapshot
  · have haccepted : state.memory.accepted field = some accepted := by
      simpa only [State.bind, if_neg heq] using haccepted
    simpa only [State.bind, if_neg heq] using hprior field accepted haccepted

/-- Public storage, reachability, and accepted private-binding provenance are
separate components of the proof-facing runtime relation. -/
structure State.Refines (state : State P L) (cfg : Config G) : Prop where
  memory : state.memory.Represents cfg
  reachable : Reachable G cfg
  bindings : state.BindingsRepresent cfg

/-- Empty commitment-service initialization refines the original graph
initialization. This is safety only: it does not provision sealed initial inputs
or prove that their future publication instructions can become ready. -/
theorem State.initial_refines (graph : Graph P L) :
    (State.initial (Memory.initial graph)).Refines (Config.initial graph) := by
  refine ⟨Memory.initial_represents graph, Reachable.initial, ?_⟩
  intro field handle haccepted
  cases haccepted

/-- Private preparation leaves the represented graph checkpoint unchanged. -/
theorem State.Refines.register {state : State P L} {cfg : Config G}
    (hrefines : state.Refines cfg) (who : P) (slot : Nat) (value : TypedValue L) :
    (state.register who slot value).Refines cfg :=
  ⟨hrefines.memory, hrefines.reachable, hrefines.bindings⟩

/-- Advancing the public clock changes no source field or binding witness. -/
theorem State.Refines.advance {state : State P L} {cfg : Config G}
    (hrefines : state.Refines cfg) (clock : Nat) :
    (state.advance clock).Refines cfg :=
  ⟨⟨hrefines.memory.completed, hrefines.memory.outside, hrefines.memory.stored,
      hrefines.memory.publicFields⟩, hrefines.reachable, hrefines.bindings⟩

/-- Binding admission preserves the complete relation, including the accepted
snapshot's connection to the source field. -/
theorem State.Refines.bind {state : State P L} {cfg : Config G}
    (hrefines : state.Refines cfg) (hwf : G.WF)
    (code : BindingCode P) (node : Fin G.nodeCount)
    (hnode : code.node = node.val) (hfield : code.sourceField = G.nodeTarget node)
    (handle : CommitmentHandle P Nat) (howner : handle.1 = code.owner)
    (written : TypedValue L)
    (hstep : CommitStep G cfg code.owner ⟨node, written⟩)
    (hsnapshot : ∀ recovered,
      (state.prepared.lookup handle).bind (fun typed => typed.as? written.ty) = some recovered →
        recovered = written.value) :
    (state.bind code handle).Refines (cfg.completeNode node written) := by
  obtain ⟨hmemory, hreachable⟩ := state.bind_reachable_represents cfg hrefines.memory
    hwf hrefines.reachable code node hnode handle written hstep
  exact ⟨hmemory, hreachable, hrefines.bindings.bind hrefines.reachable hwf code node
    hfield handle howner written hstep hsnapshot⟩

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.State.Refines.bind' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.State.Refines.bind
