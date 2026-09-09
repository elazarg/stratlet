/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicChoiceImage

/-! # Public-memory refinement for generated application instructions

The represented graph state is proof-only. Public memory may omit sealed
values, including values of completed opaque commitments in a future image
extension. Values it does contain must agree with the represented store, and
all public graph fields have matching typed readouts. This relation does not
claim that the public memory reveals precisely the source observations.
-/

namespace Vegas.ApplicationImage

open EventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr} {G : Graph P L}

/-- Operational public memory represents completion and available values;
it does not provide the compiler's proof-only hidden source witnesses. -/
structure Memory.Represents (memory : Memory L) (cfg : Config G) : Prop where
  completed : ∀ node : Fin G.nodeCount,
    memory.done node.val = true ↔ node ∈ cfg.done
  outside : ∀ node, G.nodeCount ≤ node → memory.done node = false
  stored : ∀ field value, memory.store field = some value → cfg.store field = some value
  publicFields : ∀ ref, G.fieldRefPublic ref →
    Store.getAs memory.store ref.field ref.ty = Store.getAs cfg.store ref.field ref.ty

/-- The generated public initialization represents the complete initial graph
state without exposing its sealed initial values. -/
theorem Memory.initial_represents (graph : Graph P L) :
    (Memory.initial graph).Represents (Config.initial graph) := by
  constructor
  · intro node
    simp [Memory.initial, Config.initial]
  · intro node _
    rfl
  · intro field value hstored
    simp only [Memory.initial] at hstored
    split at hstored
    · exact hstored
    · cases hstored
  · intro ref href
    rcases href with ⟨spec, hfield, _, howner⟩
    simp [Memory.initial, Store.getAs, Config.initial, hfield, howner]

/-- Completing a generated pair preserves the common memory relation. Field
and node addresses must come from the represented graph; arbitrary hand-written
images are not granted an allocation or coherence guarantee. -/
theorem Memory.Represents.publish {memory : Memory L} {cfg : Config G}
    (hrep : memory.Represents cfg) (code : PublicChoiceCode P L)
    (choice publication : Fin G.nodeCount)
    (hchoice : code.endpoint.choiceNode = choice.val)
    (hpublication : code.endpoint.publicationNode = publication.val)
    (hchoiceField : code.choiceField = G.nodeTarget choice)
    (hpublicationField : code.publicationField = G.nodeTarget publication)
    (value : L.Val code.guard.ty) :
    (memory.publish code value).Represents
      ((cfg.completeNode choice ⟨code.guard.ty, value⟩).completeNode
        publication ⟨code.guard.ty, value⟩) := by
  constructor
  · intro node
    simp only [Memory.publish, Config.completeNode, Bool.or_eq_true,
      beq_iff_eq, hchoice, hpublication, Finset.mem_insert, hrep.completed]
    rw [Fin.val_injective.eq_iff, Fin.val_injective.eq_iff]
    tauto
  · intro node hnode
    have hneChoice : node ≠ choice.val := by omega
    have hnePublication : node ≠ publication.val := by omega
    simp [Memory.publish, hchoice, hpublication, hneChoice, hnePublication,
      hrep.outside node hnode]
  · intro field stored hstored
    by_cases hpub : field = G.nodeTarget publication
    · subst field
      simpa [Memory.publish, Config.completeNode, hpublicationField] using hstored
    · by_cases hchoose : field = G.nodeTarget choice
      · subst field
        simpa [Memory.publish, Config.completeNode, hchoiceField, hpublicationField,
          Store.set, hpub] using hstored
      · have horiginal : memory.store field = some stored := by
          simpa [Memory.publish, hchoiceField, hpublicationField, Store.set, hpub,
            hchoose] using hstored
        simpa [Config.completeNode, Store.set, hpub, hchoose] using
          hrep.stored field stored horiginal
  · intro ref href
    by_cases hpub : ref.field = G.nodeTarget publication
    · simp [Memory.publish, Config.completeNode, hpublicationField, hpub, Store.getAs]
    · by_cases hchoose : ref.field = G.nodeTarget choice
      · simp [Memory.publish, Config.completeNode, hchoiceField, hpublicationField,
          Store.getAs, Store.set, hchoose]
      · simpa [Memory.publish, Config.completeNode, hchoiceField, hpublicationField,
          Store.getAs, Store.set, hpub, hchoose] using hrep.publicFields ref href

/-- A legal generated inclusion preserves public-memory representation and
advances the represented graph by its certified choice/reveal macro. This
provides the postcondition needed by a following generated instruction. -/
theorem include_source_choice_represents
    {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (image : ApplicationImage P L) (site : PublicChoiceSite prog)
    (fresh : FreshBindings prog) (state : ToEventGraph.BuildState P L Γ)
    (cfg : Config (ToEventGraph.compileCore prog fresh state).graph)
    (env : VEnv L site.context) (execution : image.application.State)
    (hrep : execution.application.Represents cfg)
    (heligible : site.PubliclyValidatable fresh state)
    (hagrees : (site.siteState fresh state).Agrees cfg.store env)
    (hreachable : Reachable (ToEventGraph.compileCore prog fresh state).graph cfg)
    (hready : (site.runtimeSite fresh state).ready execution.application.done = true)
    (address serial : Nat)
    (hcode : image.lookup address = some (site.code fresh state))
    (value : L.Val site.ty)
    (hlookup : execution.pool.lookup (site.owner, serial) =
      some ⟨(site.owner, serial), .choice address ⟨site.ty, value⟩⟩)
    (hlegal : evalGuard site.guard value ((env.toView site.owner).eraseEnv) = true) :
    (image.application.includePending execution (site.owner, serial)).application.Represents
        (site.completePublication fresh state cfg value) ∧
      Reachable (ToEventGraph.compileCore prog fresh state).graph
        (site.completePublication fresh state cfg value) := by
  have hincluded := image.include_source_choice site fresh state cfg.store env execution
    heligible hagrees hrep.publicFields hready address serial hcode value hlookup hlegal
  rw [hincluded.1]
  constructor
  · exact hrep.publish (site.code fresh state)
      (site.choiceNode fresh state) (site.publicationNode fresh state) rfl rfl rfl rfl value
  · exact site.completePublication_reachable fresh state cfg env hagrees
      execution.application.done hrep.completed hready value hlegal hreachable

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.include_source_choice_represents' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.include_source_choice_represents
