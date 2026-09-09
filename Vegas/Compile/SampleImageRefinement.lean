/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageStateRefinement

/-!
# Chance-instruction refinement

A generated chance instruction evaluates the graph row's retained exact law
from the same public reads as the represented graph configuration. Each draw
performs the corresponding single graph sample step and preserves public
memory and accepted-binding refinement. No source environment or alternate
runner is involved.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr} {G : Graph P L}

/-- One aligned chance write preserves public-memory representation. -/
theorem Memory.Represents.sample
    {memory : Memory P L} {cfg : Config G}
    (hrep : memory.Represents cfg) (code : SampleCode L)
    (node : Fin G.nodeCount) (hnode : code.node = node.val)
    (houtput : code.outputField = G.nodeTarget node)
    (value : L.Val code.dist.ty) :
    ({ memory with
      store := memory.store.set code.outputField ⟨code.dist.ty, value⟩
      done query := query == code.node || memory.done query }).Represents
      (cfg.completeNode node ⟨code.dist.ty, value⟩) := by
  constructor
  · intro query
    simp only [Config.completeNode, Bool.or_eq_true, beq_iff_eq, hnode,
      Finset.mem_insert, hrep.completed]
    rw [Fin.val_injective.eq_iff]
  · intro query houtside
    have hne : query ≠ node.val := by omega
    simp [hnode, hne, hrep.outside query houtside]
  · intro field stored hstored
    by_cases hfield : field = G.nodeTarget node
    · subst field
      simpa [Config.completeNode, Store.set, houtput] using hstored
    · have horiginal : memory.store field = some stored := by
        simpa [Store.set, houtput, hfield] using hstored
      simpa [Config.completeNode, Store.set, hfield] using
        hrep.stored field stored horiginal
  · intro ref href
    by_cases hfield : ref.field = G.nodeTarget node
    · simp [Config.completeNode, Store.getAs, Store.set, houtput, hfield]
    · simpa [Config.completeNode, Store.getAs, Store.set, houtput, hfield] using
        hrep.publicFields ref href

/-- One supported draw of an aligned graph sample preserves the complete
application refinement relation. -/
theorem State.Refines.sample
    {state : State P L} {cfg : Config G}
    (hrefines : state.Refines cfg)
    (code : SampleCode L) (node : Fin G.nodeCount)
    (hnode : code.node = node.val)
    (houtput : code.outputField = G.nodeTarget node)
    (row : EventNode P L)
    (hrow : G.nodes[node]? = some row)
    (hsem : row.sem = .sample code.dist)
    (hready : Ready G cfg node)
    (reads : ReadEnv L code.dist.reads)
    (hreads : ReadEnv.ofStore? cfg.store code.dist.reads = some reads)
    (value : L.Val code.dist.ty)
    (hvalue : value ∈ (code.dist.eval reads).support) :
    (state.sample code value).Refines
      (cfg.completeNode node ⟨code.dist.ty, value⟩) := by
  let step : InternalStep G cfg ⟨node⟩ :=
    .sample row code.dist hrow hsem hready reads hreads
  have hreachable :
      Reachable G (cfg.completeNode node ⟨code.dist.ty, value⟩) := by
    apply Reachable.step hrefines.reachable (.internal ⟨node⟩ step)
    change cfg.completeNode node ⟨code.dist.ty, value⟩ ∈
      ((code.dist.eval reads).map fun chosen =>
        cfg.completeNode node ⟨code.dist.ty, chosen⟩).support
    rw [FinDist.support_map]
    exact ⟨value, hvalue, rfl⟩
  exact
    ⟨hrefines.memory.sample code node hnode houtput value,
      hreachable,
      hrefines.bindings.completeNode hrefines.reachable node hready.1
        ⟨code.dist.ty, value⟩⟩

/-- At an aligned ready sample instruction, the native kernel is exactly the
graph distribution law, and every supported native result refines its matching
one-step graph result. -/
theorem sample_law_refines
    (image : ApplicationImage P L) (state : State P L) (cfg : Config G)
    (hrefines : state.Refines cfg) (hwf : G.WF)
    (address : Nat) (code : SampleCode L)
    (hcode : image.lookup address = some (.sample code))
    (node : Fin G.nodeCount) (hnode : code.node = node.val)
    (houtput : code.outputField = G.nodeTarget node)
    (hrequiresCode : code.requires = G.messagePrerequisites node)
    (row : EventNode P L) (hrow : G.nodes[node]? = some row)
    (hsem : row.sem = .sample code.dist)
    (hnotDone : state.memory.done code.node = false)
    (hrequires : code.requires.all state.memory.done = true) :
    ∃ reads : ReadEnv L code.dist.reads,
      ReadEnv.ofStore? cfg.store code.dist.reads = some reads ∧
      ReadEnv.ofStoreExec? state.memory.store code.dist.reads = some reads ∧
      image.sample state address =
        (code.dist.eval reads).map (state.sample code) ∧
      ∀ value, value ∈ (code.dist.eval reads).support →
        (state.sample code value).Refines
          (cfg.completeNode node ⟨code.dist.ty, value⟩) := by
  have hready : Ready G cfg node := by
    constructor
    · intro hdone
      have hnativeDone := (hrefines.memory.completed node).2 hdone
      rw [← hnode, hnotDone] at hnativeDone
      contradiction
    · intro prior hprior
      apply (hrefines.memory.completed prior).1
      apply List.all_eq_true.mp hrequires prior.val
      rw [hrequiresCode]
      exact (G.mem_messagePrerequisites node prior).2 hprior
  have hnodeWF := hwf node row hrow
  have hpublic : ∀ ref, ref ∈ code.dist.reads → G.fieldRefPublic ref := by
    intro ref href
    unfold Graph.nodeWFAt at hnodeWF
    rw [hsem] at hnodeWF
    exact hnodeWF.2.2.2 ref href
  have hcoherent : StoreCoherent G cfg :=
    reachable_storeCoherent hwf hrefines.reachable
  obtain ⟨reads, hreads⟩ := hcoherent.readEnvOfReady hwf hrow hready
    (refs := code.dist.reads)
    (by
      intro ref href
      rw [hsem]
      exact Finset.mem_image.mpr ⟨ref, href, rfl⟩)
    (by
      intro ref href
      rcases hpublic ref href with ⟨spec, hfield, htype, _⟩
      exact ⟨spec, hfield, htype⟩)
  have hnativeReads :
      ReadEnv.ofStoreExec? state.memory.store code.dist.reads = some reads :=
    ReadEnv.ofStoreExec?_eq_some_of_ofStore?_eq_some
      (ReadEnv.ofStore?_eq_of_getAs_eq hreads (by
      intro ref href
      exact (hrefines.memory.publicFields ref (hpublic ref href)).symm))
  refine ⟨reads, hreads, hnativeReads,
    image.sample_law state address code hcode hnotDone hrequires reads hnativeReads, ?_⟩
  intro value hvalue
  exact hrefines.sample code node hnode houtput row hrow hsem hready reads
    hreads value hvalue

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.State.Refines.sample' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.State.Refines.sample

/-- info: 'Vegas.ApplicationImage.sample_law_refines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.sample_law_refines
