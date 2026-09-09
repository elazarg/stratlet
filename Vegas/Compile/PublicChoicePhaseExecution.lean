/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicChoiceImageExecution
import Vegas.Compile.PublicChoiceSourceCoupling
import Vegas.Compile.ApplicationImageReadout
import Interaction.MessagePoolFreshness

/-! # Exact execution of a generated public-choice phase

One owner invocation submits the source-profile choice and one environment
invocation includes its fresh envelope.  This head-specific theorem combines
the general controller execution law with the coupled source successor, so
every supported included branch retains both the full native execution and an
exact written-order source checkpoint.
-/

noncomputable section

namespace Vegas.PublicChoiceSite

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Exact two-invocation source law for a generated adjacent public choice.
The environment premise is only the local fresh-envelope service action; it
does not assert fairness or progress outside this phase. -/
theorem publicChoice_head_phase_source_law
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ)
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
    (heligible : (atHead name publicName who guard tail).PubliclyValidatable fresh build)
    (hcode : image.lookup
        ((atHead name publicName who guard tail).runtimeSite fresh build).publicationNode =
      some (.publicChoice ((atHead name publicName who guard tail).code fresh build)))
    (reads : ReadEnv L (eventGuardOf build who guard).choiceReads)
    (hpolicy : ∀ history,
      players who history
          (MessageApplication.State.observe image.application execution.native who) =
        ((atHead name publicName who guard tail).imageController fresh build image
          (image.ownerReadout? who (eventGuardOf build who guard).choiceReads)
          sourcePolicy (fun _ _ => false)).policy image.application history
            (MessageApplication.State.observe image.application execution.native who))
    (henvironment : ∀ chosen ∈
        (sourcePolicy ((current.current.source.toView who).eraseEnv)).support,
      ∀ submitted ∈ (image.application.playerStep who execution
        (.submit ((ApplicationImage.choiceEncoding
          ((atHead name publicName who guard tail).runtimeSite fresh build).publicationNode
            ty).encode chosen.1))).support,
      environment submitted.environmentHistory
          (MessageApplication.State.environmentView image.application submitted.native) =
        FinDist.pure (.include (who, execution.native.pool.nextSerial who)))
    (hlookupFresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none)
    (hcache : ChoiceEncoding.cachedValue image.application
      ((ApplicationImage.choiceEncoding
        ((atHead name publicName who guard tail).runtimeSite fresh build).publicationNode
        ty).submission image.application)
      (execution.principalHistory who) = none)
    (hreadout : image.ownerReadout? who (eventGuardOf build who guard).choiceReads
      (execution.principalHistory who)
      (MessageApplication.State.observe image.application execution.native who) = some reads)
    (hreads : ReadEnv.ofStore? current.current.graph.1.store
      (eventGuardOf build who guard).choiceReads = some reads) :
    let site := atHead name publicName who guard tail
    let code := site.code fresh build
    let encoding := ApplicationImage.choiceEncoding (P := P)
      code.endpoint.publicationNode ty
    let id := (who, execution.native.pool.nextSerial who)
    (image.application.runPolicies players environment [.player who, .environment] execution =
      (sourcePolicy ((current.current.source.toView who).eraseEnv)).bind fun chosen =>
        (image.application.playerStep who execution
          (.submit (encoding.encode chosen.1))).bind fun submitted =>
            image.application.environmentPolicyStep submitted (.include id)) ∧
    ∀ chosen ∈ (sourcePolicy ((current.current.source.toView who).eraseEnv)).support,
      ∀ submitted ∈ (image.application.playerStep who execution
        (.submit (encoding.encode chosen.1))).support,
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
  let site := atHead name publicName who guard tail
  let code := site.code fresh build
  let encoding := ApplicationImage.choiceEncoding (P := P)
    code.endpoint.publicationNode ty
  let id := (who, execution.native.pool.nextSerial who)
  have hready := ready_at_source_prefix guard tail fresh build current
    execution.native.application.memory.done hrefines.memory.completed
  have hphase := site.publicChoice_phase_source_law fresh build image
    (image.ownerReadout? who (eventGuardOf build who guard).choiceReads)
    sourcePolicy (fun _ _ => false) players environment execution
    current.current.graph.1.store current.current.source reads (hpolicy _)
    henvironment hlookupFresh heligible current.current.agrees
    hrefines.memory.publicFields hcode hready hcache hreadout hreads
  constructor
  · exact hphase.1
  · intro chosen hchosen submitted hsubmitted included hincluded
    have hnative : submitted.native ∈
        ((image.application.playerStep who execution
          (.submit (encoding.encode chosen.1))).map PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨submitted, hsubmitted, rfl⟩
    rw [image.application.playerStep_native] at hnative
    simp only [PlayerCommand.toAction, MessageApplication.step,
      FinDist.mem_support_pure] at hnative
    have hlookupEncoded : submitted.native.pool.lookup id =
        some ⟨id, encoding.encode chosen.1⟩ := by
      rw [hnative]
      exact execution.native.pool.lookup_submit_fresh who _ hlookupFresh
    have hlookup : submitted.native.pool.lookup id =
        some ⟨id, .choice code.endpoint.publicationNode ⟨ty, chosen.1⟩⟩ := by
      simpa only [encoding, ApplicationImage.choiceEncoding] using hlookupEncoded
    have happlication : submitted.native.application = execution.native.application := by
      simpa using congrArg MessageApplication.State.application hnative
    have hincludedNative : included.native =
        image.application.includePending submitted.native id := by
      simp only [MessageApplication.environmentPolicyStep,
        EnvironmentPolicyCommand.toAction, MessageApplication.advance,
        MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hincluded
      exact congrArg PolicyExecution.native hincluded
    obtain ⟨next, hsource, hrefinesNext⟩ := include_source_coupling guard tail fresh
      build current image submitted.native (happlication.symm ▸ hrefines) heligible
      code.endpoint.publicationNode (execution.native.pool.nextSerial who) hcode
      chosen.1 hlookup chosen.2
    exact ⟨next, hsource, hincludedNative.symm ▸ hrefinesNext⟩

end Vegas.PublicChoiceSite

/-- info: 'Vegas.PublicChoiceSite.publicChoice_head_phase_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PublicChoiceSite.publicChoice_head_phase_source_law
