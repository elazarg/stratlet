/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ConditionalImage
import Vegas.Compile.PublicChoiceImage
import Vegas.Compile.SampleImage
import Vegas.Compile.SourceExecution

/-! # Structural derivations for public-application generation

A derivation consumes the existing source and its accounting plan. It selects
implemented instructions and checks their backend conditions; it adds neither
source syntax nor an evaluator. Every constructor consumes one source node or
one adjacent pair. There are no cases that discard a sample or a literal reveal.

Opaque bindings require an unrestricted original guard because the current
binding instruction does not validate that guard. Slots use the source-field
allocation. Conditional deadlines are supplied separately by publication node.
Conditional endpoints can discharge an original binding or publish a later
copy of a retained binding. Both use the same source guard certificate; only
their accounting derivations differ.
Initial sealed-input provisioning and whole-program strategy correspondence are
separate from this code-generation derivation.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Backend admissibility of an unvalidated opaque binding. This is stronger
than the source's nonempty-menu requirement and does not change source WF. -/
def UnrestrictedBinding {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool) : Prop :=
  ∀ (env : VEnv L Γ) (value : L.Val ty),
    evalGuard guard value ((env.toView who).eraseEnv) = true

/-- A code-generation derivation over the unchanged accounting tree. Its
indices retain the exact source, freshness proof, and compiler cursor. -/
inductive ApplicationPlan :
    {Γ : VCtx P L} → {pending : Finset VarId} → {prog : VegasCore P L Γ} →
      (accounted : CommitmentAccounting pending prog) → FreshBindings prog →
        BuildState P L Γ → Type where
  | ret {Γ : VCtx P L} {pending : Finset VarId}
      {payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)}
      (empty : pending = ∅) (fresh : FreshBindings (.ret payoffs))
      (state : BuildState P L Γ) :
      ApplicationPlan (.ret empty) fresh state
  | sample {Γ : VCtx P L} {pending : Finset VarId} {name : VarId} {ty : L.Ty}
      {dist : L.DistExpr (erasePubVCtx Γ) ty}
      {tail : VegasCore P L ((name, .pub ty) :: Γ)}
      {accounted : CommitmentAccounting pending tail}
      {fresh : FreshBindings (.sample name dist tail)} {state : BuildState P L Γ}
      (next : ApplicationPlan accounted fresh.2
        (state.addSampleEvent name dist fresh.1).1) :
      ApplicationPlan (.sample accounted) fresh state
  | binding {Γ : VCtx P L} {pending : Finset VarId} {name : VarId} {who : P}
      {ty : L.Ty} {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
      {tail : VegasCore P L ((name, .sealed who ty) :: Γ)}
      {newName : name ∉ pending} {accounted : CommitmentAccounting (insert name pending) tail}
      {fresh : FreshBindings (.commit name who guard tail)} {state : BuildState P L Γ}
      (unrestricted : UnrestrictedBinding guard)
      (next : ApplicationPlan accounted fresh.2
        (state.addCommitEvent name who guard fresh.1).1) :
      ApplicationPlan (.commit newName accounted) fresh state
  | publicChoice {Γ : VCtx P L} {pending : Finset VarId} {name publicName : VarId}
      {who : P} {ty : L.Ty}
      {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
      {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
      {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
      {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
      {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
      {state : BuildState P L Γ}
      (publicGuard : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
        fresh state)
      (next : ApplicationPlan accounted fresh.2.2
        (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1) :
      ApplicationPlan (.commit newName (.reveal unresolved accounted)) fresh state
  | conditional {Γ : VCtx P L} {pending : Finset VarId} {name publicName : VarId}
      {who : P} {ty : L.Ty}
      {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
      {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
      {spec : ConditionalOpening guard} {unresolved : spec.source ∈ pending}
      {newName : name ∉ pending}
      {accounted : CommitmentAccounting (pending.erase spec.source) tail}
      {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
      {state : BuildState P L Γ}
      (publicGuard : ConditionalPublicationSite.PubliclyValidatable
        (ConditionalPublicationSite.atHead name publicName who guard tail spec) fresh state)
      (next : ApplicationPlan accounted fresh.2.2
        (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1) :
      ApplicationPlan (.opening spec unresolved newName accounted) fresh state
  /-- A conditional endpoint for a copy with its own accounting discharge. -/
  | conditionalCopy {Γ : VCtx P L} {pending : Finset VarId} {name publicName : VarId}
      {who : P} {ty : L.Ty}
      {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
      {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
      (spec : ConditionalOpening guard)
      {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
      {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
      {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
      {state : BuildState P L Γ}
      (publicGuard : ConditionalPublicationSite.PubliclyValidatable
        (ConditionalPublicationSite.atHead name publicName who guard tail spec) fresh state)
      (next : ApplicationPlan accounted fresh.2.2
        (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1) :
      ApplicationPlan (.commit newName (.reveal unresolved accounted)) fresh state

namespace ApplicationPlan

/-- The next source sample, viewed at its canonical node in the final compiled
graph.  This is a head-occurrence helper, not a source evaluator. -/
noncomputable def headSampleCode
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    {dist : L.DistExpr (erasePubVCtx Γ) ty}
    {tail : VegasCore P L ((name, .pub ty) :: Γ)}
    (fresh : FreshBindings (.sample name dist tail)) (state : BuildState P L Γ) :
    SampleCode L := by
  let result := compileCore (.sample name dist tail) fresh state
  let event := state.sampleEvent dist
  have hprefix : state.nodes ++ [event] <+: result.nodes := by
    change state.nodes ++ [state.sampleEvent dist] <+:
      (compileCore tail fresh.2 (state.addSampleEvent name dist fresh.1).1).nodes
    simpa only [BuildState.addSampleEvent_nodes] using
      compileCore_nodes_prefix tail fresh.2 (state.addSampleEvent name dist fresh.1).1
  let next := compiledNext state result event hprefix
  exact result.graph.sampleCode next.node (eventDistOf state dist)

@[simp] theorem headSampleCode_node
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    {dist : L.DistExpr (erasePubVCtx Γ) ty}
    {tail : VegasCore P L ((name, .pub ty) :: Γ)}
    (fresh : FreshBindings (.sample name dist tail)) (state : BuildState P L Γ) :
    (headSampleCode fresh state).node = state.nodes.length := rfl

@[simp] theorem headSampleCode_dist
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    {dist : L.DistExpr (erasePubVCtx Γ) ty}
    {tail : VegasCore P L ((name, .pub ty) :: Γ)}
    (fresh : FreshBindings (.sample name dist tail)) (state : BuildState P L Γ) :
    (headSampleCode fresh state).dist = eventDistOf state dist := rfl

@[simp] theorem headSampleCode_outputField
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    {dist : L.DistExpr (erasePubVCtx Γ) ty}
    {tail : VegasCore P L ((name, .pub ty) :: Γ)}
    (fresh : FreshBindings (.sample name dist tail)) (state : BuildState P L Γ) :
    (headSampleCode fresh state).outputField = state.nextField := by
  simp [headSampleCode, Graph.sampleCode, Graph.nodeTarget, BuildResult.graph,
    compileCore_initialFields, compiledNext, BuildState.nextField, BuildState.nextNode]

/-- The emitted prerequisite list is exactly the final graph's list at the
source sample's canonical node. -/
theorem headSampleCode_requires
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    {dist : L.DistExpr (erasePubVCtx Γ) ty}
    {tail : VegasCore P L ((name, .pub ty) :: Γ)}
    (fresh : FreshBindings (.sample name dist tail)) (state : BuildState P L Γ)
    (node : Fin (compileCore (.sample name dist tail) fresh state).graph.nodeCount)
    (hnode : node.val = state.nodes.length) :
    (headSampleCode fresh state).requires =
      (compileCore (.sample name dist tail) fresh state).graph.messagePrerequisites node := by
  unfold headSampleCode
  dsimp only [Graph.sampleCode]
  congr 1
  apply Fin.ext
  exact hnode.symm

/-- Emit directly into the shared application instruction set. Code generation
uses the source allocation for both binding fields and private service slots. -/
def instructions (deadlineOf : Nat → Nat) :
    {Γ : VCtx P L} → {pending : Finset VarId} → {prog : VegasCore P L Γ} →
      {accounted : CommitmentAccounting pending prog} → {fresh : FreshBindings prog} →
      {state : BuildState P L Γ} → ApplicationPlan accounted fresh state →
        List (ApplicationInstruction P L)
  | _, _, _, _, _, _, .ret _ _ _ => []
  | _, _, _, _, _, _,
      .sample (pending := pending) (name := name) (dist := dist) (tail := tail)
        (accounted := accounted)
        (fresh := fresh) (state := state) next =>
      .sample (headSampleCode (P := P) fresh state) ::
        instructions deadlineOf next
  | _, _, _, _, _, _,
      .binding (name := name) (who := who) (guard := guard) (tail := tail)
        (fresh := fresh) (state := state) _ next =>
      let site : SourceDecisionSite who (.commit name who guard tail) _ name _ guard :=
        .here guard tail
      .bind (site.bindingCode fresh state state.nextField) :: instructions deadlineOf next
  | _, _, _, _, _, _,
      .publicChoice (name := name) (publicName := publicName) (who := who)
        (guard := guard) (tail := tail) (fresh := fresh) (state := state) _ next =>
      .publicChoice ((PublicChoiceSite.atHead name publicName who guard tail).code fresh state) ::
        instructions deadlineOf next
  | _, _, _, _, _, _,
      .conditional (name := name) (publicName := publicName) (who := who)
        (guard := guard) (tail := tail) (spec := spec)
        (fresh := fresh) (state := state) _ next =>
      let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
      .conditional (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))) :: instructions deadlineOf next
  | _, _, _, _, _, _,
      .conditionalCopy (name := name) (publicName := publicName) (who := who)
        (guard := guard) (tail := tail) (fresh := fresh) (state := state) spec _ next =>
      let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
      .conditional (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))) :: instructions deadlineOf next

/-- The application image is generated from the complete derivation, rather
than an externally supplied list of selected source occurrences. -/
def image {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) : ApplicationImage P L :=
  ⟨plan.instructions deadlineOf⟩

end ApplicationPlan

end Vegas
