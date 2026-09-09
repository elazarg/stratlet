/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ConditionalSourceCoupling
import Interaction.MessageApplicationPolicies

/-! # Permissionless conditional-expiration continuations

An overdue generated conditional publication accepts an expiry packet from any
sender.  Inclusion follows the shared message-policy runner, records its public
history and trace, and realizes the source-certified decline branch.  This is a
local source-support result, not a service, progress theorem, or equality with a
source behavioral profile.
-/

noncomputable section

namespace Vegas.ConditionalPublicationSite

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Including an actual pending expiry packet at an overdue generated endpoint
records the exact shared environment step and continues the source through its
certified decline value.  The sender is unrestricted; no opening snapshot,
source readout, or source-profile premise is needed. -/
theorem expiry_include_source_coupling
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (spec : ConditionalOpening guard)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ) (sourceSlot deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (image : ApplicationImage P L)
    (execution included : image.application.PolicyExecution)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (haccepted : execution.native.application.memory.accepted
      (build.fieldOf spec.binding) = some (who, sourceSlot))
    (hoverdue : deadline < execution.native.application.memory.clock)
    (address : Nat)
    (hcode : image.lookup address = some (.conditional
      ((atHead name publicName who guard tail spec).code fresh build sourceSlot deadline)))
    (id : MessageId P)
    (hlookup : execution.native.pool.lookup id = some
      ⟨id, .conditional address .expire⟩)
    (hincluded : included ∈
      (image.application.environmentPolicyStep execution (.include id)).support) :
    let chosen := spec.encoding.symm none
    included.native = image.application.includePending execution.native id ∧
      included.environmentHistory = execution.environmentHistory ++
        [⟨State.environmentView image.application execution.native, .include id⟩] ∧
      included.nativeTrace = execution.nativeTrace ++ [.include id] ∧
      ∃ next : CoupledAt
          (compileCore (.commit name who guard (.reveal publicName who name .here tail))
            fresh build).graph
          (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
            publicName who .here fresh.2.1).1,
        next.current.source = (current.current.source.cons chosen).cons chosen ∧
          included.native.application.Refines next.current.graph.1 := by
  dsimp only
  let site := atHead name publicName who guard tail spec
  let code := site.code fresh build sourceSlot deadline
  let chosen := spec.encoding.symm none
  have hready := ready_at_source_prefix guard tail spec fresh build sourceSlot deadline current
    execution.native.application hrefines haccepted
  have hresolve : code.endpoint.resolve?
      execution.native.application.memory.clock
      (execution.native.application.verify code)
      (execution.native.application.memory.accepted code.sourceField)
      execution.native.application.memory.done
      (code.canOpen execution.native.application.memory.store)
      ⟨id, .expire⟩ = some none := by
    apply (code.endpoint.resolve_expire
      execution.native.application.memory.clock
      (execution.native.application.verify code)
      (execution.native.application.memory.accepted code.sourceField)
      execution.native.application.memory.done
      (code.canOpen execution.native.application.memory.store)
      ⟨id, .expire⟩ rfl).2
    exact ⟨hready, hoverdue⟩
  have hhandle : image.handle execution.native.application
      ⟨id, .conditional address .expire⟩ =
      some (execution.native.application.publishConditional code none) := by
    rw [image.handle_conditional execution.native.application address code hcode id
      .expire .expire rfl, hresolve, Option.map_some]
  have hnative := image.include_accepted execution.native id
    ⟨id, .conditional address .expire⟩
    (execution.native.application.publishConditional code none) hlookup hhandle
  simp only [MessageApplication.environmentPolicyStep,
    EnvironmentPolicyCommand.toAction, MessageApplication.advance,
    MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hincluded
  subst included
  refine ⟨rfl, rfl, rfl, ?_⟩
  obtain ⟨next, hsource, hgraph⟩ :=
    PublicChoiceSite.source_successor guard tail fresh build current chosen
      (spec.decline_legal current.current.source)
  let G := (compileCore (.commit name who guard (.reveal publicName who name .here tail))
    fresh build).graph
  let choice := site.choice.choiceNode fresh build
  let publication := site.choice.publicationNode fresh build
  have hpublic := PublicChoiceSite.ready_at_source_prefix guard tail fresh build current
    execution.native.application.memory.done hrefines.memory.completed
  have hnodes := G.publicChoice_ready current.current.graph.1 who choice publication
    execution.native.application.memory.done hrefines.memory.completed hpublic
  have hmemory := execution.native.application.publishConditional_represents
    current.current.graph.1 hrefines.memory code choice publication rfl rfl rfl rfl none
  change (execution.native.application.publishConditional code none).memory.Represents
    ((current.current.graph.1.completeNode choice ⟨ty, chosen⟩).completeNode publication
      ⟨ty, chosen⟩) at hmemory
  have hbindings := hrefines.bindings.completePair hrefines.reachable choice publication
    ⟨ty, chosen⟩ hnodes.1.1 hnodes.2.1
  have hnextRefines :
      (execution.native.application.publishConditional code none).Refines
        next.current.graph.1 := by
    refine ⟨?_, next.current.graph.2, ?_⟩
    · rw [hgraph]
      exact hmemory
    · rw [hgraph]
      exact hbindings
  refine ⟨next, hsource, ?_⟩
  have happlication :
      (image.application.includePending execution.native id).application =
        execution.native.application.publishConditional code none := hnative.1
  rw [happlication]
  exact hnextRefines

end Vegas.ConditionalPublicationSite

/-- info: 'Vegas.ConditionalPublicationSite.expiry_include_source_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ConditionalPublicationSite.expiry_include_source_coupling
