/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.ChoiceControllerHistory
import Vegas.Compile.DecisionSite
import Vegas.Compile.SourceLaw

/-! # Message controllers for source decision occurrences

This adapter supplies the source decision kernel to a generic sample-once
controller. The caller chooses the concrete command encoding and executable
readout; public submission and private registration are separate clients.
-/

noncomputable section

namespace Vegas.SourceDecisionSite

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
variable {name : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}

abbrev ChoiceReads (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ) :=
  ReadEnv L (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads

def controller (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (app : MessageApplication P)
    (encoding : ChoiceEncoding (L.Val ty) app.PlayerCommand)
    (ready resolved : app.View → Bool)
    (readout? : List app.PlayerEntry → app.View → Option (ChoiceReads site fresh state))
    (sourcePolicy :
      (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
        FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (retry : List app.PlayerEntry → app.View → Bool) :
    ChoiceController app (L.Val ty) (ChoiceReads site fresh state) where
  codec := encoding
  ready := ready
  resolved := resolved
  readout? := readout?
  kernel := fun reads =>
    (compileSourceDecision (decisionSiteState site fresh state) who guard
      sourcePolicy reads).map Subtype.val
  retry := retry

theorem controller_first_emission_source_law
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (app : MessageApplication P)
    (encoding : ChoiceEncoding (L.Val ty) app.PlayerCommand)
    (ready resolved : app.View → Bool)
    (readout? : List app.PlayerEntry → app.View → Option (ChoiceReads site fresh state))
    (sourcePolicy :
      (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
        FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (retry : List app.PlayerEntry → app.View → Bool)
    (history : List app.PlayerEntry) (view : app.View)
    (representedStore : Store L) (env : VEnv L Δ)
    (reads : ChoiceReads site fresh state)
    (hresolved : resolved view = false)
    (hcache : encoding.cachedValue app history = none)
    (hready : ready view = true)
    (hreadout : readout? history view = some reads)
    (hagrees : (decisionSiteState site fresh state).ViewAgrees
      who representedStore env)
    (hreads : ReadEnv.ofStore? representedStore
      (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads =
        some reads) :
    (site.controller fresh state app encoding ready resolved readout?
        sourcePolicy retry).policy app history view =
      (sourcePolicy ((env.toView who).eraseEnv)).map
        fun choice => encoding.encode choice.1 := by
  let adapted := site.controller fresh state app encoding ready resolved
    readout? sourcePolicy retry
  calc
    adapted.policy app history view =
        (adapted.kernel reads).map encoding.encode :=
      adapted.policy_of_uncached_ready app history view reads
        hresolved hcache hready hreadout
    _ = (sourcePolicy ((env.toView who).eraseEnv)).map
        fun choice => encoding.encode choice.1 := by
      have hlaw := compileSourceDecision_law
        (decisionSiteState site fresh state) who guard sourcePolicy
        representedStore env hagrees reads hreads
      have hmapped := congrArg (FinDist.map encoding.encode) hlaw
      simpa only [adapted, controller, FinDist.map_comp, Function.comp_def] using hmapped

theorem controller_first_invoke_source_law
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (app : MessageApplication P)
    (encoding : ChoiceEncoding (L.Val ty) app.PlayerCommand)
    (ready resolved : app.View → Bool)
    (readout? : List app.PlayerEntry → app.View → Option (ChoiceReads site fresh state))
    (sourcePolicy :
      (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
        FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (retry : List app.PlayerEntry → app.View → Bool)
    (players : P → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (execution : app.PolicyExecution) (representedStore : Store L) (env : VEnv L Δ)
    (reads : ChoiceReads site fresh state)
    (hpolicy : players who (execution.principalHistory who)
      (State.observe app execution.native who) =
        (site.controller fresh state app encoding ready resolved readout?
          sourcePolicy retry).policy app (execution.principalHistory who)
            (State.observe app execution.native who))
    (hresolved : resolved (State.observe app execution.native who) = false)
    (hcache : encoding.cachedValue app (execution.principalHistory who) = none)
    (hready : ready (State.observe app execution.native who) = true)
    (hreadout : readout? (execution.principalHistory who)
      (State.observe app execution.native who) = some reads)
    (hagrees : (decisionSiteState site fresh state).ViewAgrees
      who representedStore env)
    (hreads : ReadEnv.ofStore? representedStore
      (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads =
        some reads) :
    app.invoke players environment execution (.player who) =
      (sourcePolicy ((env.toView who).eraseEnv)).bind fun choice =>
        app.playerStep who execution (encoding.encode choice.1) := by
  let adapted := site.controller fresh state app encoding ready resolved
    readout? sourcePolicy retry
  rw [adapted.invoke_uncached_ready app who players environment execution reads
    hpolicy hresolved hcache hready hreadout]
  have hlaw := compileSourceDecision_law
    (decisionSiteState site fresh state) who guard sourcePolicy
    representedStore env hagrees reads hreads
  change (((compileSourceDecision (decisionSiteState site fresh state) who guard
    sourcePolicy reads).map Subtype.val).bind fun value =>
      app.playerStep who execution (encoding.encode value)) = _
  rw [hlaw, FinDist.bind_map]

end Vegas.SourceDecisionSite
