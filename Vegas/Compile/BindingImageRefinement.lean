/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageRefinement
import Vegas.EventGraph.HistoryInformation

/-! # Opaque-binding image refinement

Binding admission changes public completion metadata but does not expose its
sealed value. A proof-only graph configuration records the value selected by a
certified graph commitment; no source environment is runtime data here.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr} {G : Graph P L}

/-- Admitting an opaque binding and completing its aligned ghost graph commit
preserve public-memory representation and graph reachability. The application
does not store the sealed output publicly; reachability and coherence show
that no old public store value can occupy the unfinished output field. -/
theorem State.bind_reachable_represents
    (state : State P L) (cfg : Config G)
    (hrep : state.memory.Represents cfg) (hwf : G.WF)
    (hreachable : Reachable G cfg)
    (code : BindingCode P) (node : Fin G.nodeCount)
    (hnode : code.node = node.val) (handle : CommitmentHandle P Nat)
    (written : TypedValue L)
    (hstep : CommitStep G cfg code.owner ⟨node, written⟩) :
    (state.bind code handle).memory.Represents
        (cfg.completeNode node written) ∧
      Reachable G (cfg.completeNode node written) := by
  have hrepresentation : (state.bind code handle).memory.Represents
      (cfg.completeNode node written) := by
    constructor
    · intro query
      simp only [State.bind, Config.completeNode, Bool.or_eq_true, beq_iff_eq,
        hnode, Finset.mem_insert, hrep.completed]
      rw [Fin.val_injective.eq_iff]
    · intro query houtside
      have hne : query ≠ node.val := by omega
      simp [State.bind, hnode, hne, hrep.outside query houtside]
    · intro field oldValue hstored
      by_cases hfield : field = G.nodeTarget node
      · subst field
        have hghost : cfg.store (G.nodeTarget node) = some oldValue :=
          hrep.stored (G.nodeTarget node) oldValue hstored
        have hpresent : Store.getAs cfg.store (G.nodeTarget node) oldValue.ty =
            some oldValue.value := by
          simp [Store.getAs, hghost, TypedValue.as?]
        have habsent := reachable_getAs_nodeTarget_eq_none hreachable node
          hstep.ready.1 oldValue.ty
        rw [habsent] at hpresent
        contradiction
      · simpa [State.bind, Config.completeNode, Store.set, hfield] using
          hrep.stored field oldValue hstored
    · intro ref href
      have hprivate : (G.nodeRow node).owner = some code.owner := by
        have hnodeWF := hwf node hstep.row hstep.row_get
        unfold Graph.nodeWFAt at hnodeWF
        rw [hstep.sem_eq] at hnodeWF
        have hrow : hstep.row = G.nodeRow node := by
          have hcanonical := G.nodes_get?_nodeRow node
          exact Option.some.inj (hstep.row_get.symm.trans hcanonical)
        simpa [hrow] using hnodeWF.2.2.1
      have hne : ref.field ≠ G.nodeTarget node := by
        intro hfield
        rcases href with ⟨spec, href, hty, howner⟩
        have htarget := G.field?_nodeTarget (G.nodes_get?_nodeRow node)
        rw [hfield, htarget] at href
        have hspec := Option.some.inj href
        have : (G.nodeRow node).owner = none := by
          rw [← howner]
          exact congrArg FieldSpec.owner hspec
        rw [hprivate] at this
        contradiction
      change Store.getAs state.memory.store ref.field ref.ty =
        Store.getAs (Store.set cfg.store (G.nodeTarget node) written)
          ref.field ref.ty
      rw [Store.getAs_set_ne cfg.store hne written ref.ty]
      exact hrep.publicFields ref href
  refine ⟨hrepresentation, ?_⟩
  apply Reachable.step hreachable
    (.commit code.owner ⟨node, written⟩ hstep)
  change cfg.completeNode node written ∈
    (FinDist.pure (cfg.completeNode node
      ⟨hstep.guard.ty, hstep.value⟩)).support
  rw [FinDist.mem_support_pure]
  exact congrArg (cfg.completeNode node) hstep.written_eq_action.symm

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.State.bind_reachable_represents' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.State.bind_reachable_represents
