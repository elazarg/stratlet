/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageController
import Interaction.MessagePoolFreshness

/-! # Runtime execution of generated public-choice phases

A lifted reference strategy samples the source decision kernel on its first
ready invocation. If the following environment invocation selects the
freshly allocated envelope, the shared message runner performs the generated
publication transaction. The theorem covers this two-invocation phase;
strategy lifting and the service premise are analysis data for the open protocol.
-/

noncomputable section

namespace Vegas.PublicChoiceSite

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {prog : VegasCore P L Γ}

/-- The exact two-invocation law for a first generated public-choice
submission followed by service of its freshly allocated envelope.  The
right-hand side retains the complete policy execution: both histories,
receipts, the native trace, and all message-pool effects.

The second conjunct certifies that the selected inclusion succeeds, has the
exact generated public-memory update, and realizes the adjacent source
choice/reveal steps.  Absence of the newly allocated id is the phase boundary
needed to identify the appended envelope; unrelated pending traffic remains
allowed and the premise is not a restriction on the raw application handler. -/
theorem publicChoice_phase_source_law
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (build : BuildState P L Γ) (image : ApplicationImage P L)
    (readout? : List image.application.PlayerEntry → image.application.View →
      Option (site.ChoiceReads fresh build))
    (sourcePolicy :
      (visible : Env L.Val (eraseVCtx (viewVCtx site.owner site.context))) →
        FinDist { value : L.Val site.ty //
          evalGuard site.guard value visible = true })
    (retry : List image.application.PlayerEntry → image.application.View → Bool)
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (execution : image.application.PolicyExecution)
    (representedStore : Store L) (env : VEnv L site.context)
    (reads : site.ChoiceReads fresh build)
    (hpolicy : players site.owner (execution.principalHistory site.owner)
      (MessageApplication.State.observe image.application execution.native site.owner) =
        (site.imageController fresh build image readout? sourcePolicy retry).policy
          image.application (execution.principalHistory site.owner)
          (MessageApplication.State.observe image.application execution.native site.owner))
    (henvironment : ∀ chosen ∈
        (sourcePolicy ((env.toView site.owner).eraseEnv)).support,
      ∀ submitted ∈ (image.application.playerStep site.owner execution
        (.submit ((ApplicationImage.choiceEncoding
          (site.runtimeSite fresh build).publicationNode site.ty).encode chosen.1))).support,
      environment submitted.environmentHistory
          (MessageApplication.State.environmentView image.application submitted.native) =
        FinDist.pure (.include
          (site.owner, execution.native.pool.nextSerial site.owner)))
    (hlookupFresh : execution.native.pool.lookup
      (site.owner, execution.native.pool.nextSerial site.owner) = none)
    (heligible : site.PubliclyValidatable fresh build)
    (hagrees : (site.siteState fresh build).Agrees representedStore env)
    (hpublicStore : ∀ ref,
      (compileCore prog fresh build).graph.fieldRefPublic ref →
        Store.getAs execution.native.application.memory.store ref.field ref.ty =
          Store.getAs representedStore ref.field ref.ty)
    (hcode : image.lookup (site.runtimeSite fresh build).publicationNode =
      some (.publicChoice (site.code fresh build)))
    (hready : (site.runtimeSite fresh build).ready
      execution.native.application.memory.done = true)
    (hcache : ((ApplicationImage.choiceEncoding
        (site.runtimeSite fresh build).publicationNode site.ty).submission
          image.application).cachedValue image.application
            (execution.principalHistory site.owner) = none)
    (hreadout : readout? (execution.principalHistory site.owner)
      (MessageApplication.State.observe image.application execution.native site.owner) =
        some reads)
    (hreads : ReadEnv.ofStore? representedStore
      (site.compiledGuard fresh build).choiceReads = some reads) :
    let encoding := ApplicationImage.choiceEncoding (P := P)
      (site.runtimeSite fresh build).publicationNode site.ty
    let id := (site.owner, execution.native.pool.nextSerial site.owner)
    (image.application.runPolicies players environment
        [.player site.owner, .environment] execution =
      (sourcePolicy ((env.toView site.owner).eraseEnv)).bind fun chosen =>
        (image.application.playerStep site.owner execution
          (.submit (encoding.encode chosen.1))).bind fun submitted =>
            image.application.environmentPolicyStep submitted (.include id)) ∧
    ∀ chosen ∈ (sourcePolicy ((env.toView site.owner).eraseEnv)).support,
      ∀ submitted ∈ (image.application.playerStep site.owner execution
        (.submit (encoding.encode chosen.1))).support,
      let next := image.application.includePending submitted.native id
      next.application =
          execution.native.application.publish (site.code fresh build) chosen.1 ∧
        next.receipts = submitted.native.receipts ++ [(id, true)] ∧
        next.pool.ledger = submitted.native.pool.ledger ++
          [⟨id, encoding.encode chosen.1⟩] ∧
        next.pool.sent = submitted.native.pool.sent ∧
        next.pool.inbox = submitted.native.pool.inbox ∧
        SmallStep.Star
          ⟨site.context, env,
            .commit site.choiceName site.owner site.guard site.decision.continuation⟩
          ⟨(site.publicName, .pub site.ty) ::
              (site.choiceName, .sealed site.owner site.ty) :: site.context,
            (env.cons chosen.1).cons chosen.1, site.tail⟩ := by
  dsimp only
  have hresolved : execution.native.application.memory.done
      (site.runtimeSite fresh build).publicationNode = false := by
    have hparts := hready
    simp only [PublicChoice.ready, Bool.and_eq_true, Bool.not_eq_true'] at hparts
    exact hparts.1.2
  have hsource :
      (site.imageController fresh build image readout? sourcePolicy retry).policy
          image.application (execution.principalHistory site.owner)
          (MessageApplication.State.observe image.application execution.native site.owner) =
        (sourcePolicy ((env.toView site.owner).eraseEnv)).map fun choice =>
          .submit ((ApplicationImage.choiceEncoding
            (site.runtimeSite fresh build).publicationNode site.ty).encode choice.1) := by
    exact site.controller_first_submission_source_law fresh build
      image.application
      (ApplicationImage.choiceEncoding
        (site.runtimeSite fresh build).publicationNode site.ty)
      (fun view => view.application.done) readout? sourcePolicy retry
      (execution.principalHistory site.owner)
      (MessageApplication.State.observe image.application execution.native site.owner)
      representedStore env reads hresolved hcache hready hreadout
      (hagrees.view site.owner) hreads
  constructor
  · simp only [MessageApplication.runPolicies, MessageApplication.invoke]
    rw [hpolicy, hsource, FinDist.bind_map, FinDist.bind_bind]
    apply FinDist.bind_congr
    intro chosen hchosen
    apply FinDist.bind_congr
    intro submitted hsubmitted
    rw [henvironment chosen hchosen submitted hsubmitted]
    simp only [FinDist.pure_bind]
    exact FinDist.bind_pure _
  · intro chosen hchosen submitted hsubmitted
    have hnative : submitted.native ∈
        ((image.application.playerStep site.owner execution
          (.submit ((ApplicationImage.choiceEncoding
            (site.runtimeSite fresh build).publicationNode site.ty).encode chosen.1))).map
              PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨submitted, hsubmitted, rfl⟩
    rw [image.application.playerStep_native] at hnative
    simp only [PlayerCommand.toAction, MessageApplication.step,
      FinDist.mem_support_pure] at hnative
    have happ : submitted.native.application = execution.native.application := by
      rw [hnative]
    have hlookup : submitted.native.pool.lookup
        (site.owner, execution.native.pool.nextSerial site.owner) =
      some ⟨(site.owner, execution.native.pool.nextSerial site.owner),
        (ApplicationImage.choiceEncoding
          (site.runtimeSite fresh build).publicationNode site.ty).encode chosen.1⟩ := by
      rw [hnative]
      exact execution.native.pool.lookup_submit_fresh site.owner _ hlookupFresh
    have hpublicSubmitted : ∀ ref,
        (compileCore prog fresh build).graph.fieldRefPublic ref →
          Store.getAs submitted.native.application.memory.store ref.field ref.ty =
            Store.getAs representedStore ref.field ref.ty := by
      simpa only [happ] using hpublicStore
    have hreadySubmitted : (site.runtimeSite fresh build).ready
        submitted.native.application.memory.done = true := by
      simpa only [happ] using hready
    have hhandle := (site.image_encoded_accepts_iff fresh build image
      submitted.native.application representedStore env heligible hagrees
      hpublicSubmitted hreadySubmitted hcode
      (execution.native.pool.nextSerial site.owner) chosen.1).2 chosen.2
    have hincluded := image.include_accepted submitted.native
      (site.owner, execution.native.pool.nextSerial site.owner)
      ⟨(site.owner, execution.native.pool.nextSerial site.owner),
        (ApplicationImage.choiceEncoding
          (site.runtimeSite fresh build).publicationNode site.ty).encode chosen.1⟩
      (submitted.native.application.publish (site.code fresh build) chosen.1)
      hlookup hhandle
    refine ⟨?_, hincluded.2.1, hincluded.2.2.1, hincluded.2.2.2.1,
      hincluded.2.2.2.2, site.completePublication_source_steps env chosen.1 chosen.2⟩
    exact hincluded.1.trans (congrArg
      (fun runtime => runtime.publish (site.code fresh build) chosen.1) happ)

end Vegas.PublicChoiceSite

/-- info: 'Vegas.PublicChoiceSite.publicChoice_phase_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PublicChoiceSite.publicChoice_phase_source_law
