/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageCoverage
import Vegas.Compile.ApplicationImageProvenance

/-! # Availability of owner-local application readouts

Completed-field coverage and typed registration provenance make represented
source inputs available to the executable local loader. The graph state is
used only in the proof; the loader consumes native public memory and the
player's own command history.

Initial fields in the requested footprint are required to be public. Sealed
initial inputs need a separate provisioning construction; initial graph-store
membership alone does not put them in a player's native local memory.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A present source-visible value is recoverable locally. Completed event
fields use native coverage and typed cache provenance; initial fields use
the stated public-input condition. -/
theorem ownerReadStore_getAs_of_visible
    (image : ApplicationImage P L) (who : P)
    (history : List image.application.PlayerEntry) (native : State P L)
    {G : Graph P L} (cfg : Config G) (hrefines : native.Refines cfg)
    (hcovers : native.memory.Covers G.initialFields.length)
    (hbindings : image.RegisteredBindings who
      (fun slot typed => ∃ spec : FieldSpec P L,
        G.field? slot = some spec ∧ typed.ty = spec.ty) history native)
    (ref : FieldRef L) (spec : FieldSpec P L)
    (hfield : G.field? ref.field = some spec) (htype : spec.ty = ref.ty)
    (hvisible : spec.owner = none ∨ spec.owner = some who)
    (hinitial : ∀ value, spec.source = .initial value → spec.owner = none)
    (value : L.Val ref.ty)
    (hgraph : Store.getAs cfg.store ref.field ref.ty = some value) :
    Store.getAs (image.ownerReadStore who history native.memory)
      ref.field ref.ty = some value := by
  cases hstored : native.memory.store ref.field with
  | some typed =>
      have hrepresented := hrefines.memory.stored ref.field typed hstored
      simpa only [Store.getAs, ownerReadStore, hstored, hrepresented] using hgraph
  | none =>
      have hnotPublic : spec.owner ≠ none := by
        intro hpublic
        have heq := hrefines.memory.publicFields ref ⟨spec, hfield, htype, hpublic⟩
        simp only [Store.getAs, hstored] at heq
        change none = Store.getAs cfg.store ref.field ref.ty at heq
        rw [← heq] at hgraph
        contradiction
      have howner : spec.owner = some who := hvisible.resolve_left hnotPublic
      have haccepted : native.memory.accepted ref.field = some (who, ref.field) := by
        cases hsource : spec.source with
        | initial input => exact False.elim (hnotPublic (hinitial input hsource))
        | event writer =>
            have htarget := G.field_eq_nodeTarget_of_event_source hfield hsource
            obtain ⟨event, hevent⟩ := G.node_get_of_field_event_source hfield hsource
            let node : Fin G.nodeCount := ⟨writer, (List.getElem?_eq_some_iff.mp hevent).1⟩
            have hdone : node ∈ cfg.done := by
              by_contra hnotDone
              have habsent := reachable_getAs_nodeTarget_eq_none
                hrefines.reachable node hnotDone ref.ty
              rw [htarget, habsent] at hgraph
              contradiction
            have hcovered := hcovers writer ((hrefines.memory.completed node).mpr hdone)
            change (native.memory.store (G.nodeTarget writer)).isSome ∨
              ∃ owner, native.memory.accepted (G.nodeTarget writer) =
                some (owner, G.nodeTarget writer) at hcovered
            rw [← htarget, hstored] at hcovered
            obtain ⟨owner, haccepted⟩ := hcovered.resolve_left (by simp)
            obtain ⟨actual, bound, hactual, hactualOwner, _⟩ :=
              hrefines.bindings ref.field (owner, ref.field) haccepted
            have hspec : actual = spec := Option.some.inj (hactual.symm.trans hfield)
            subst actual
            have heq : owner = who := Option.some.inj (hactualOwner.symm.trans howner)
            simpa only [heq] using haccepted
      obtain ⟨typed, hcache, _, actual, hactual, htyped⟩ :=
        hbindings ref.field (who, ref.field) haccepted rfl
      have hspec : actual = spec := Option.some.inj (hactual.symm.trans hfield)
      subst actual
      have hlocal : (Store.getAs (image.ownerReadStore who history native.memory)
          ref.field ref.ty).isSome := by
        simp [Store.getAs, ownerReadStore, hstored, haccepted, hcache,
          TypedValue.as?, htyped.trans htype]
      obtain ⟨recovered, hrecovered⟩ := Option.isSome_iff_exists.mp hlocal
      have hrepresented := image.ownerReadStore_getAs who history native cfg hrefines
        hbindings.registrationMatches ref spec hfield htype recovered hrecovered
      have heq := Option.some.inj (hrepresented.symm.trans hgraph)
      exact hrecovered.trans (congrArg some heq)

/-- Every available graph read footprint visible to the owner is accepted by
the executable local loader with exactly the same values. Native availability
is a conclusion, not a supplied readout-success assumption. -/
theorem ownerReadout?_of_graph_reads
    (image : ApplicationImage P L) (who : P)
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (native : State P L) (hview : view.application = native.memory)
    {G : Graph P L} (cfg : Config G) (hrefines : native.Refines cfg)
    (hcovers : native.memory.Covers G.initialFields.length)
    (hbindings : image.RegisteredBindings who
      (fun slot typed => ∃ spec : FieldSpec P L,
        G.field? slot = some spec ∧ typed.ty = spec.ty) history native)
    (refs : Finset (FieldRef L))
    (hvisible : ∀ ref ∈ refs, G.fieldRefVisibleTo who ref)
    (hinitial : ∀ ref ∈ refs, ∀ spec, G.field? ref.field = some spec →
      ∀ value, spec.source = .initial value → spec.owner = none)
    (reads : ReadEnv L refs)
    (hreads : ReadEnv.ofStore? cfg.store refs = some reads) :
    image.ownerReadout? who refs history view = some reads := by
  unfold ownerReadout?
  rw [hview]
  apply ReadEnv.ofStoreExec?_eq_some_of_ofStore?_eq_some
  apply ReadEnv.ofStore?_eq_of_getAs_eq hreads
  intro ref href
  obtain ⟨spec, hfield, htype, howner⟩ := hvisible ref href
  have hgraph := ReadEnv.ofStore?_read hreads href
  exact hgraph.trans (image.ownerReadStore_getAs_of_visible who history native cfg
    hrefines hcovers hbindings ref spec hfield htype howner
    (hinitial ref href spec hfield) (reads.read ref href) hgraph).symm

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.ownerReadout?_of_graph_reads' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.ownerReadout?_of_graph_reads
