/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ConditionalImageController
import Vegas.Compile.ConditionalSourceCoupling
import Vegas.Compile.ApplicationImageReadout
import Interaction.MessagePoolFreshness

/-! # Exact execution of a generated conditional-publication phase

One owner invocation submits the source-profile choice and one environment
invocation includes that fresh envelope.  The theorem retains the complete
shared policy execution.  Its snapshot premise is branch-local: decline needs
no recoverable commitment value, while an opening needs its claimed value in
the accepted frozen snapshot.
-/

noncomputable section

namespace Vegas.ConditionalPublicationSite

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Exact two-invocation source law for one generated conditional opening or
decline.  The environment premise is only the local inclusion action and makes
no general scheduling or progress assertion. -/
theorem conditional_phase_source_law
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
    (sourcePolicy :
      (visible : Env L.Val (eraseVCtx (viewVCtx who Γ))) →
        FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (execution : image.application.PolicyExecution)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (heligible : (atHead name publicName who guard tail spec).PubliclyValidatable fresh build)
    (haccepted : execution.native.application.memory.accepted (build.fieldOf spec.binding) =
      some (who, sourceSlot))
    (hcode : image.lookup
        ((atHead name publicName who guard tail spec).code fresh build
          sourceSlot deadline).endpoint.publicationNode = some (.conditional
      ((atHead name publicName who guard tail spec).code fresh build sourceSlot deadline)))
    (reads : ReadEnv L (eventGuardOf build who guard).choiceReads)
    (hpolicy : ∀ history,
      players who history
          (MessageApplication.State.observe image.application execution.native who) =
        ((atHead name publicName who guard tail spec).imageController fresh build
          sourceSlot deadline image
          (image.ownerReadout? who (eventGuardOf build who guard).choiceReads)
          sourcePolicy (fun _ _ => false)).policy image.application history
            (MessageApplication.State.observe image.application execution.native who))
    (henvironment : ∀ chosen ∈
        (sourcePolicy ((current.current.source.toView who).eraseEnv)).support,
      ∀ submitted ∈ (image.application.playerStep who execution
        (.submit ((ApplicationImage.conditionalTransport spec.secretTy).encode
          (((atHead name publicName who guard tail spec).code fresh build sourceSlot
            deadline).endpoint.publicationNode,
            ((atHead name publicName who guard tail spec).runtimeSite fresh build
              sourceSlot deadline).requestPayload (spec.encoding chosen.1))))).support,
      environment submitted.environmentHistory
          (MessageApplication.State.environmentView image.application submitted.native) =
        FinDist.pure (.include (who, execution.native.pool.nextSerial who)))
    (hlookupFresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none)
    (hcache : ChoiceEncoding.cachedValue image.application
      (((atHead name publicName who guard tail spec).choiceEncoding fresh build
        sourceSlot deadline (ApplicationImage.conditionalTransport spec.secretTy)).submission
          image.application)
      (execution.principalHistory who) = none)
    (hreadout : image.ownerReadout? who (eventGuardOf build who guard).choiceReads
      (execution.principalHistory who)
      (MessageApplication.State.observe image.application execution.native who) = some reads)
    (hreads : ReadEnv.ofStore? current.current.graph.1.store
      (eventGuardOf build who guard).choiceReads = some reads)
    (hfrozen : ∀ chosen ∈
        (sourcePolicy ((current.current.source.toView who).eraseEnv)).support,
      ∀ value, spec.encoding chosen.1 = some value →
        (execution.native.application.frozen (build.fieldOf spec.binding)).bind
          (fun typed => typed.as? spec.secretTy) = some value) :
    let site := atHead name publicName who guard tail spec
    let code := site.code fresh build sourceSlot deadline
    let id := (who, execution.native.pool.nextSerial who)
    (image.application.runPolicies players environment [.player who, .environment] execution =
      (sourcePolicy ((current.current.source.toView who).eraseEnv)).bind fun chosen =>
        (image.application.playerStep who execution
          (.submit ((ApplicationImage.conditionalTransport spec.secretTy).encode
            (code.endpoint.publicationNode,
              code.endpoint.requestPayload (spec.encoding chosen.1))))).bind
            fun submitted => image.application.environmentPolicyStep submitted (.include id)) ∧
    ∀ chosen ∈ (sourcePolicy ((current.current.source.toView who).eraseEnv)).support,
      ∀ submitted ∈ (image.application.playerStep who execution
        (.submit ((ApplicationImage.conditionalTransport spec.secretTy).encode
          (code.endpoint.publicationNode,
            code.endpoint.requestPayload (spec.encoding chosen.1))))).support,
      ∀ included ∈
        (image.application.environmentPolicyStep submitted (.include id)).support,
      ∃ next : CoupledAt
          (compileCore (.commit name who guard (.reveal publicName who name .here tail))
            fresh build).graph
          (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
            publicName who .here fresh.2.1).1,
        next.current.source = (current.current.source.cons chosen.1).cons chosen.1 ∧
          included.native.application.Refines next.current.graph.1 := by
  dsimp only
  let site := atHead name publicName who guard tail spec
  let code := site.code fresh build sourceSlot deadline
  let id := (who, execution.native.pool.nextSerial who)
  have hready := ready_at_source_prefix guard tail spec fresh build sourceSlot deadline current
    execution.native.application hrefines haccepted
  have hresolved : execution.native.application.memory.done code.endpoint.publicationNode =
      false := by
    simp only [ConditionalPublication.ready, Bool.and_eq_true, Bool.not_eq_true'] at hready
    exact hready.1.2
  have hfirst := site.imageController_first_submission_source_law fresh build sourceSlot
    deadline image (image.ownerReadout? who (eventGuardOf build who guard).choiceReads)
    sourcePolicy (fun _ _ => false) (execution.principalHistory who)
    (MessageApplication.State.observe image.application execution.native who)
    current.current.graph.1.store current.current.source reads hresolved hcache hready hreadout
    (BuildState.Agrees.view current.current.agrees who) hreads
  constructor
  · simp only [MessageApplication.runPolicies, MessageApplication.invoke]
    rw [hpolicy, hfirst, FinDist.bind_map, FinDist.bind_bind]
    apply FinDist.bind_congr
    intro chosen hchosen
    apply FinDist.bind_congr
    intro submitted hsubmitted
    rw [henvironment chosen hchosen submitted hsubmitted]
    simp only [FinDist.pure_bind]
    exact FinDist.bind_pure _
  · intro chosen hchosen submitted hsubmitted included hincluded
    have hnative : submitted.native ∈
          ((image.application.playerStep who execution
            (.submit ((ApplicationImage.conditionalTransport spec.secretTy).encode
              (code.endpoint.publicationNode,
                code.endpoint.requestPayload (spec.encoding chosen.1))))).map
              PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨submitted, hsubmitted, rfl⟩
    rw [image.application.playerStep_native] at hnative
    simp only [PlayerCommand.toAction, MessageApplication.step,
      FinDist.mem_support_pure] at hnative
    have hpayload :
        (ApplicationImage.conditionalTransport spec.secretTy).encode
            (code.endpoint.publicationNode,
              code.endpoint.requestPayload (Value := L.Val spec.secretTy)
                (spec.encoding chosen.1)) =
          .conditional code.endpoint.publicationNode
            (code.requestPayload (spec.encoding chosen.1)) := by
      cases hresult : spec.encoding chosen.1 <;> rfl
    have hlookup : submitted.native.pool.lookup id = some
        ⟨id, .conditional code.endpoint.publicationNode
          (code.requestPayload (spec.encoding chosen.1))⟩ := by
      rw [hnative, ← hpayload]
      exact execution.native.pool.lookup_submit_fresh who _ hlookupFresh
    have happlication : submitted.native.application = execution.native.application := by
      simpa using congrArg MessageApplication.State.application hnative
    have hincludedNative : included.native =
        image.application.includePending submitted.native id := by
      simp only [MessageApplication.environmentPolicyStep,
        EnvironmentPolicyCommand.toAction, MessageApplication.advance,
        MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hincluded
      exact congrArg PolicyExecution.native hincluded
    obtain ⟨next, hsource, hrefinesNext⟩ := include_source_coupling guard tail spec fresh
      build sourceSlot deadline current image submitted.native (happlication.symm ▸ hrefines)
      heligible (happlication.symm ▸ haccepted) code.endpoint.publicationNode
      (execution.native.pool.nextSerial who) hcode chosen.1 hlookup chosen.2 (by
        intro value hvalue
        rw [happlication]
        exact hfrozen chosen hchosen value hvalue)
    exact ⟨next, hsource, hincludedNative.symm ▸ hrefinesNext⟩

end Vegas.ConditionalPublicationSite

/-- info: 'Vegas.ConditionalPublicationSite.conditional_phase_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ConditionalPublicationSite.conditional_phase_source_law
