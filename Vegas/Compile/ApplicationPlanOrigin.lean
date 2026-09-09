/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPlanCoverage

/-! # Source origins of dispatched application instructions

Every instruction emitted by a structural plan retains its occurrence in the
original source, its generated code, and its backend eligibility proof. This
recovers evidence erased from the executable image without assuming a runtime
simulation or restricting the incoming message alphabet.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Source occurrence and eligibility evidence for one generated instruction.
The occurrence refers to the original program, not an unrelated source term
with a coincidentally matching instruction address. -/
inductive Origin {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    (accounted : CommitmentAccounting pending prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (deadlineOf : Nat → Nat) :
    ApplicationInstruction P L → Prop where
  | binding {Δ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
      {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
      (site : SourceDecisionSite who prog Δ name ty guard)
      (unrestricted : UnrestrictedBinding guard) :
      Origin accounted fresh state deadlineOf
        (.bind (site.bindingCode fresh state (decisionSiteState site fresh state).nextField))
  | publicChoice (site : PublicChoiceSite prog)
      (publicGuard : site.PubliclyValidatable fresh state) :
      Origin accounted fresh state deadlineOf (.publicChoice (site.code fresh state))
  | conditional (site : accounted.OpeningSite)
      (publicGuard : site.PubliclyValidatable fresh state) :
      Origin accounted fresh state deadlineOf
        (.conditional (site.code fresh state (site.sourceField fresh state)
          (deadlineOf (site.publicationNode fresh state))))

/-- Membership in an emitted image recovers the original source occurrence
and the certificate checked by the corresponding plan constructor. -/
theorem instructions_origin
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) :
    ∀ instruction ∈ plan.instructions deadlineOf,
      Origin accounted fresh state deadlineOf instruction := by
  induction plan with
  | ret => simp [instructions]
  | @binding Γ pending name who ty guard tail newName accounted fresh state unrestricted next ih =>
      intro instruction hmem
      simp only [instructions, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact .binding (.here _ _) unrestricted
      · cases ih instruction htail with
        | binding site unrestricted => exact .binding (.commit site) unrestricted
        | publicChoice site publicGuard =>
            exact Origin.publicChoice (accounted := .commit newName accounted)
              (fresh := fresh) (state := state) (deadlineOf := deadlineOf)
              { site with decision := .commit site.decision
                          adjacent := by simpa only [SourceDecisionSite.continuation]
                            using site.adjacent } (by
                simpa only [PublicChoiceSite.PubliclyValidatable, PublicChoiceSite.compiledGuard,
                  PublicChoiceSite.siteState, decisionSiteState, compileCore] using publicGuard)
        | conditional site publicGuard => exact .conditional (.commit site) publicGuard
  | @publicChoice Γ pending name publicName who ty guard tail newName unresolved
      accounted fresh state publicGuard next ih =>
      intro instruction hmem
      simp only [instructions, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact .publicChoice _ publicGuard
      · cases ih instruction htail with
        | binding site unrestricted => exact .binding (.commit (.reveal site)) unrestricted
        | publicChoice site publicGuard =>
            exact Origin.publicChoice (accounted := .commit newName (.reveal unresolved accounted))
              (fresh := fresh) (state := state) (deadlineOf := deadlineOf)
              { site with decision := .commit (.reveal site.decision)
                          adjacent := by simpa only [SourceDecisionSite.continuation]
                            using site.adjacent } (by
                simpa only [PublicChoiceSite.PubliclyValidatable, PublicChoiceSite.compiledGuard,
                  PublicChoiceSite.siteState, decisionSiteState, compileCore] using publicGuard)
        | conditional site publicGuard => exact .conditional (.commit (.reveal site)) publicGuard
  | @conditional Γ pending name publicName who ty guard tail spec unresolved newName
      accounted fresh state publicGuard next ih =>
      intro instruction hmem
      simp only [instructions, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact .conditional _ publicGuard
      · cases ih instruction htail with
        | binding site unrestricted => exact .binding (.commit (.reveal site)) unrestricted
        | publicChoice site publicGuard =>
            exact Origin.publicChoice (accounted := .opening spec unresolved newName accounted)
              (fresh := fresh) (state := state) (deadlineOf := deadlineOf)
              { site with decision := .commit (.reveal site.decision)
                          adjacent := by simpa only [SourceDecisionSite.continuation]
                            using site.adjacent } (by
                simpa only [PublicChoiceSite.PubliclyValidatable, PublicChoiceSite.compiledGuard,
                  PublicChoiceSite.siteState, decisionSiteState, compileCore] using publicGuard)
        | conditional site publicGuard => exact .conditional (.openingTail site) publicGuard

/-- Successful lookup in a generated image identifies certified source code.
The address is arbitrary: callers need not assume an instruction selected from
the source, or restrict raw packets to generated ones. -/
theorem origin_of_lookup
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) (address : Nat) (instruction : ApplicationInstruction P L)
    (hlookup : (plan.image deadlineOf).lookup address = some instruction) :
    Origin accounted fresh state deadlineOf instruction := by
  apply plan.instructions_origin deadlineOf instruction
  exact List.mem_of_find?_eq_some hlookup

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.origin_of_lookup' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.origin_of_lookup
