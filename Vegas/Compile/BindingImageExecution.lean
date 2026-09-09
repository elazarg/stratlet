/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.BindingImageController

/-! # Actual execution of source-generated binding policies

Two consecutive owner invocations sample a source decision into local ideal
commitment preparation and submit its opaque handle. The law retains the full
execution, including both histories and the native trace. Inclusion is a
separate environment action; these two invocations do not assume its progress.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem registration_preserves_observation
    (image : ApplicationImage P L) (who observer : P) (slot : Nat)
    (value : TypedValue L) (execution next : image.application.PolicyExecution)
    (hnext : next ∈ (image.application.playerStep who execution
      (.privateCommand (.register slot value))).support) :
    MessageApplication.State.observe image.application next.native observer =
      MessageApplication.State.observe image.application execution.native observer := by
  simp only [MessageApplication.playerStep, PlayerCommand.toAction,
    MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hnext
  subst next
  rfl

namespace SourceDecisionSite

variable {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
variable {name : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}

/-- Actual registration records the first value without changing any public
view. The next invocation submits the handle, without another source draw. -/
theorem bindingPolicy_after_registration
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (build : BuildState P L Γ)
    (image : ApplicationImage P L)
    (sourcePolicy : (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
      FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (execution next : image.application.PolicyExecution) (value : L.Val ty)
    (hcache : image.registrationCache (site.compiledField fresh build)
      (execution.principalHistory who) = none)
    (hresolved : (site.bindingCode fresh build (site.compiledField fresh build)).resolved
      execution.native.application.memory = false)
    (hready : (site.bindingCode fresh build (site.compiledField fresh build)).requires.all
      execution.native.application.memory.done = true)
    (hsubmitted : ChoiceEncoding.cachedValue image.application
      ((site.bindingCode fresh build (site.compiledField fresh build)).encoding.submission
        image.application) (execution.principalHistory who) = none)
    (hnext : next ∈ (image.application.playerStep who execution
      (.privateCommand (.register (site.compiledField fresh build) ⟨ty, value⟩))).support) :
    site.bindingPolicy fresh build image sourcePolicy (next.principalHistory who)
        (MessageApplication.State.observe image.application next.native who) =
      FinDist.pure (.submit (.binding
        (site.bindingCode fresh build (site.compiledField fresh build)).node
        (who, site.compiledField fresh build))) := by
  have hhistory := image.application.playerStep_history_self who execution
    (.privateCommand (.register (site.compiledField fresh build) ⟨ty, value⟩)) next hnext
  rw [registration_preserves_observation image who who _ _ execution next hnext]
  apply site.bindingPolicy_registered fresh build image sourcePolicy _ _ value
  · rw [hhistory]
    exact ChoiceEncoding.cachedValue_append_encoded_of_none image.application
      ((ApplicationImage.registrationEncoding (site.compiledField fresh build)).privateCommand
        image.application) _ _ ⟨ty, value⟩ hcache
  · exact hresolved
  · exact hready
  · rw [hhistory, ChoiceEncoding.cachedValue_append_of_none _ _ _ _ hsubmitted]
    simp

/-- The full law of two consecutive owner invocations: one source-kernel
sample is registered and its canonical handle is then submitted. This is an
equality of complete policy executions, not only a value-cache marginal. -/
theorem bindingPolicy_two_invocations_source_law
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (build : BuildState P L Γ)
    (image : ApplicationImage P L)
    (sourcePolicy : (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
      FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (execution : image.application.PolicyExecution)
    (hpolicy : players who = site.bindingPolicy fresh build image sourcePolicy)
    (env : VEnv L Δ)
    (reads : ReadEnv L (eventGuardOf (decisionSiteState site fresh build) who guard).choiceReads)
    (hresolved : (site.bindingCode fresh build (site.compiledField fresh build)).resolved
      execution.native.application.memory = false)
    (hready : (site.bindingCode fresh build (site.compiledField fresh build)).requires.all
      execution.native.application.memory.done = true)
    (hcache : image.registrationCache (site.compiledField fresh build)
      (execution.principalHistory who) = none)
    (hsubmitted : ChoiceEncoding.cachedValue image.application
      ((site.bindingCode fresh build (site.compiledField fresh build)).encoding.submission
        image.application) (execution.principalHistory who) = none)
    (hreadout : image.ownerReadout? who
      (eventGuardOf (decisionSiteState site fresh build) who guard).choiceReads
        (execution.principalHistory who)
        (MessageApplication.State.observe image.application execution.native who) = some reads)
    (hview : viewEnvOfReadEnv (decisionSiteState site fresh build) who reads =
      (env.toView who).eraseEnv) :
    image.application.runPolicies players environment [.player who, .player who] execution =
      (sourcePolicy ((env.toView who).eraseEnv)).bind fun chosen =>
        (image.application.playerStep who execution
          (.privateCommand (.register (site.compiledField fresh build) ⟨ty, chosen.1⟩))).bind
            fun registered => image.application.playerStep who registered
              (.submit (.binding
                (site.bindingCode fresh build (site.compiledField fresh build)).node
                (who, site.compiledField fresh build))) := by
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, hpolicy]
  rw [site.bindingPolicy_first_registration_source_law fresh build image sourcePolicy
    _ _ env reads hresolved hready hcache hreadout hview, FinDist.bind_map,
    FinDist.bind_bind]
  apply FinDist.bind_congr
  intro chosen _
  apply FinDist.bind_congr
  intro registered hregistered
  rw [site.bindingPolicy_after_registration fresh build image sourcePolicy execution
    registered chosen.1 hcache hresolved hready hsubmitted hregistered]
  simp

end SourceDecisionSite

end Vegas

/-- info: 'Vegas.SourceDecisionSite.bindingPolicy_two_invocations_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.bindingPolicy_two_invocations_source_law
