/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPlan
import Vegas.Core.SourceContext
import Vegas.Foundation.ViewExtension

/-! # Source guard certificates at concurrent graph checkpoints

A checked source program supplies a proof-only inhabitant of every decision
context. Replacing its visible part with a node's actual declared reads lets
the existing source certificates apply without assuming that unrelated source
fields have already been executed in the graph.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- An unrestricted source binding accepts every value under every declared
graph readout. Source legality supplies hidden context inhabitants, not a
restriction on the actual graph schedule. -/
theorem SourceDecisionSite.unrestricted_guard_eval
    {Γ Δ : VCtx P L} {prog : VegasCore P L Γ} {who : P} {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (initial : VEnv L Γ) (legal : Legal prog)
    (unrestricted : UnrestrictedBinding guard)
    (reads : ReadEnv L (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads)
    (value : L.Val ty) :
    (eventGuardOf (decisionSiteState site fresh state) who guard).eval value reads = true := by
  obtain ⟨baseline⟩ := site.context_nonempty initial legal
  obtain ⟨env, hview⟩ := VEnv.exists_toView_eq who baseline
    ((decisionSiteState site fresh state).wctx.viewVCtx)
    (visibleEnvOfReadEnv (decisionSiteState site fresh state) who reads)
  have hlegal := unrestricted env value
  rw [hview, visibleEnvOfReadEnv_erase] at hlegal
  exact (eventGuardOf_eval_eq_eval _ who guard value reads).trans hlegal

/-- Decline is graph-legal at every possible declared readout of the source
opening site, including concurrent checkpoints with unrelated hidden fields
still absent. No registered or recoverable native binding is required. -/
theorem CommitmentAccounting.OpeningSite.decline_guard_eval
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} (site : accounted.OpeningSite)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (initial : VEnv L Γ) (legal : Legal prog)
    (reads : ReadEnv L (site.compiledGuard fresh state).choiceReads) :
    (site.compiledGuard fresh state).eval (site.data.specification.encoding.symm none) reads =
      true := by
  obtain ⟨baseline⟩ := site.data.decision.context_nonempty initial legal
  obtain ⟨env, hview⟩ := VEnv.exists_toView_eq site.data.owner baseline
    ((decisionSiteState site.data.decision fresh state).wctx.viewVCtx)
    (visibleEnvOfReadEnv (decisionSiteState site.data.decision fresh state) site.data.owner reads)
  have hlegal := site.data.specification.decline_legal env
  rw [hview, visibleEnvOfReadEnv_erase] at hlegal
  exact (eventGuardOf_eval_eq_eval _ site.data.owner site.data.guard _ reads).trans hlegal

end Vegas

/-- info: 'Vegas.SourceDecisionSite.unrestricted_guard_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.unrestricted_guard_eval

/-- info: 'Vegas.CommitmentAccounting.OpeningSite.decline_guard_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.CommitmentAccounting.OpeningSite.decline_guard_eval
