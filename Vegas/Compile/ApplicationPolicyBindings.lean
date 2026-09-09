/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicy

/-! # Binding provenance for lifted source profiles

The proof-level strategy lifting can submit an opaque binding only on behalf
of the principal whose policy is being invoked, and only after that policy's
local history records a private registration at the submitted slot. This is a
property of the reference lifting, not generated player software or a
restriction on arbitrary runtime strategies.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem binding_submission_has_registration
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (image : ApplicationImage P L)
    (sourcePolicy : (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
      FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (address : Nat) (handle : CommitmentHandle P Nat)
    (hcommand : .submit (.binding address handle) ∈
      (site.bindingPolicy fresh state image sourcePolicy history view).support) :
    handle.1 = who ∧ ∃ value : TypedValue L,
      image.registrationCache handle.2 history = some value := by
  cases hcache : image.registrationCache (site.compiledField fresh state) history with
  | none =>
      let controller := site.registrationController fresh state image sourcePolicy
      have hsupported : .submit (.binding address handle) ∈
          (controller.policy image.application history view).support := by
        simpa only [Vegas.SourceDecisionSite.bindingPolicy, hcache] using hcommand
      exact False.elim (controller.not_supported_of_decode_none image.application history view
        (.submit (.binding address handle)) (by simp) rfl hsupported)
  | some registered =>
      rcases site.bindingPolicy_supported_command fresh state image sourcePolicy
          history view (.submit (.binding address handle)) hcommand with
        hwait | hregister | hbinding
      · cases hwait
      · obtain ⟨value, hvalue⟩ := hregister
        cases hvalue
      · cases hbinding
        exact ⟨rfl, ⟨registered, hcache⟩⟩

/-- Any opaque binding packet supported by the structural source-profile
lifting is authenticated as the invoked principal and refers to a slot whose
first private registration is already present in that principal's history. -/
theorem liftProfileIn_binding_submission
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (profile : SourceBehavioralProfile prog) (player : P)
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (address : Nat) (handle : CommitmentHandle P Nat)
    (hcommand : .submit (.binding address handle) ∈
      (plan.liftProfileIn image deadlineOf profile player history view).support) :
    handle.1 = player ∧ ∃ value : TypedValue L,
      image.registrationCache handle.2 history = some value := by
  induction plan generalizing player with
  | ret => simp [liftProfileIn] at hcommand
  | sample next ih =>
      simp only [liftProfileIn] at hcommand
      split at hcommand
      · exact ih profile.afterSample player hcommand
      · simp at hcommand
  | binding unrestricted next ih =>
      simp only [liftProfileIn] at hcommand
      split at hcommand
      · exact ih profile.afterCommit player hcommand
      · split at hcommand
        · rename_i howner
          subst player
          exact binding_submission_has_registration
            _ _ _ _ _ _ _ _ _ hcommand
        · simp at hcommand
  | publicChoice publicGuard next ih
  | conditional publicGuard next ih
  | conditionalCopy specification publicGuard next ih =>
      simp only [liftProfileIn] at hcommand
      split at hcommand
      · exact ih profile.afterCommit.afterReveal player hcommand
      · split at hcommand
        · exact False.elim (ChoiceController.not_supported_of_decode_none
            _ _ history view (.submit (.binding address handle)) (by simp) rfl hcommand)
        · simp at hcommand

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.liftProfileIn_binding_submission' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.liftProfileIn_binding_submission
