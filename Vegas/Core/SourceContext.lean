/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Strategy

/-!
# Source decision contexts are inhabited

For a legal straight-line source program, an initial full environment extends
to a full environment at every syntactic source decision site.  The witness is
ghost state only: samples choose an element of the normalized distribution's
support, commitments choose a guard-legal value, and reveals copy their source
value.  No event-graph schedule or native evaluator is involved.
-/

noncomputable section

namespace Vegas

namespace SourceDecisionSite

/-- Every decision-site context in a legal source program has a full
environment, provided the program's initial context does. -/
theorem context_nonempty {P : Type} [DecidableEq P] {L : IExpr}
    {Γ Δ : VCtx P L} {prog : VegasCore P L Γ} {who : P} {x : VarId}
    {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ x b guard)
    (initial : VEnv L Γ) (legal : Legal prog) :
    Nonempty (VEnv L Δ) := by
  induction site with
  | here =>
      exact ⟨initial⟩
  | @sample Γ sampleName sampleTy dist tail Δ x b guard site ih =>
      let law := L.evalDist dist initial.eraseSampleEnv
      let value : L.Val sampleTy := law.support_nonempty.choose
      exact ih (VEnv.cons value initial) legal
  | @commit Γ commitName actor commitTy commitGuard tail Δ x b guard site ih =>
      obtain ⟨value, _⟩ := legal.1 (initial.toView actor).eraseEnv
      exact ih (VEnv.cons value initial) legal.2
  | @reveal Γ publicName actor sealedName revealTy source tail Δ x b guard site ih =>
      exact ih
        (VEnv.cons (initial sealedName (.sealed actor revealTy) source) initial)
        legal

end SourceDecisionSite

end Vegas

/-- info: 'Vegas.SourceDecisionSite.context_nonempty' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.context_nonempty
