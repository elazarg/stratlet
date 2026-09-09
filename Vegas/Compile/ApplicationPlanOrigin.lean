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
inductive Origin {Γ : VCtx P L} (prog : VegasCore P L Γ) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (deadlineOf : Nat → Nat) :
    ApplicationInstruction P L → Prop where
  | sample {code : SampleCode L}
      (node : Fin (compileCore prog fresh state).graph.nodeCount)
      (dist : EventDist L)
      (hsem : ((compileCore prog fresh state).graph.nodeRow node).sem = .sample dist)
      (hcode : code = (compileCore prog fresh state).graph.sampleCode node dist) :
      Origin prog fresh state deadlineOf (.sample code)
  | binding {Δ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
      {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
      (site : SourceDecisionSite who prog Δ name ty guard)
      (unrestricted : UnrestrictedBinding guard) :
      Origin prog fresh state deadlineOf
        (.bind (site.bindingCode fresh state (decisionSiteState site fresh state).nextField))
  | publicChoice (site : PublicChoiceSite prog)
      (publicGuard : site.PubliclyValidatable fresh state) :
      Origin prog fresh state deadlineOf (.publicChoice (site.code fresh state))
  | conditional (site : ConditionalPublicationSite prog)
      (publicGuard : site.PubliclyValidatable fresh state) :
      Origin prog fresh state deadlineOf
        (.conditional (site.code fresh state (site.sourceField fresh state)
          (deadlineOf (site.choice.publicationNode fresh state))))
/-- Source origins survive an earlier adjacent commitment/publication pair.
This transport is independent of how accounting discharged that pair. -/
private theorem Origin.beforePair
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
    {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
    {state : BuildState P L Γ} {deadlineOf : Nat → Nat}
    {instruction : ApplicationInstruction P L}
    (origin : Origin tail fresh.2.2
      (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
        publicName who .here fresh.2.1).1 deadlineOf instruction) :
    Origin (.commit name who guard (.reveal publicName who name .here tail))
      fresh state deadlineOf instruction := by
  cases origin with
  | sample node dist hsem hcode => exact .sample node dist hsem hcode
  | binding site unrestricted => exact .binding (.commit (.reveal site)) unrestricted
  | publicChoice site publicGuard =>
      exact Origin.publicChoice
        (prog := .commit name who guard (.reveal publicName who name .here tail))
        (fresh := fresh) (state := state) (deadlineOf := deadlineOf)
        { site with decision := .commit (.reveal site.decision)
                    adjacent := by simpa only [SourceDecisionSite.continuation]
                      using site.adjacent } (by
          simpa only [PublicChoiceSite.PubliclyValidatable, PublicChoiceSite.compiledGuard,
            PublicChoiceSite.siteState, decisionSiteState, compileCore] using publicGuard)
  | conditional site publicGuard =>
      exact Origin.conditional
        (prog := .commit name who guard (.reveal publicName who name .here tail))
        (fresh := fresh) (state := state) (deadlineOf := deadlineOf)
        { choice :=
            { site.choice with
              decision := .commit (.reveal site.choice.decision)
              adjacent := by simpa only [SourceDecisionSite.continuation]
                using site.choice.adjacent }
          specification := site.specification } (by
          simpa only [ConditionalPublicationSite.PubliclyValidatable,
            ConditionalPublicationSite.sourceRef, ConditionalPublicationSite.sourceField,
            PublicChoiceSite.compiledGuard, PublicChoiceSite.siteState,
            decisionSiteState, compileCore] using publicGuard)
/-- Membership in an emitted image recovers the original source occurrence
and the certificate checked by the corresponding plan constructor. -/
theorem instructions_origin
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) :
    ∀ instruction ∈ plan.instructions deadlineOf,
      Origin prog fresh state deadlineOf instruction := by
  induction plan with
  | ret => simp [instructions]
  | @sample Γ pending name ty dist tail accounted fresh state next ih =>
      intro instruction hmem
      simp only [instructions, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · let result := compileCore (.sample name dist tail) fresh state
        let event := state.sampleEvent dist
        have hprefix : state.nodes ++ [event] <+: result.nodes := by
          change state.nodes ++ [state.sampleEvent dist] <+:
            (compileCore tail fresh.2 (state.addSampleEvent name dist fresh.1).1).nodes
          simpa only [BuildState.addSampleEvent_nodes] using
            compileCore_nodes_prefix tail fresh.2
              (state.addSampleEvent name dist fresh.1).1
        let compiled := compiledNext state result event hprefix
        apply Origin.sample compiled.node (eventDistOf state dist)
        · rw [compiled.nodeRow_eq]
        · rfl
      · cases ih instruction htail with
        | sample node dist hsem hcode => exact .sample node dist hsem hcode
        | binding site unrestricted => exact .binding (.sample site) unrestricted
        | publicChoice site publicGuard =>
            exact Origin.publicChoice (prog := .sample name dist tail)
              (fresh := fresh) (state := state) (deadlineOf := deadlineOf)
              { site with decision := .sample site.decision } (by
                simpa only [PublicChoiceSite.PubliclyValidatable,
                  PublicChoiceSite.compiledGuard, PublicChoiceSite.siteState,
                  decisionSiteState, compileCore] using publicGuard)
        | conditional site publicGuard =>
            exact Origin.conditional
              (prog := .sample name dist tail)
              (fresh := fresh) (state := state) (deadlineOf := deadlineOf)
              { choice :=
                  { site.choice with
                    decision := .sample site.choice.decision
                    adjacent := by simpa only [SourceDecisionSite.continuation]
                      using site.choice.adjacent }
                specification := site.specification } (by
                simpa only [ConditionalPublicationSite.PubliclyValidatable,
                  ConditionalPublicationSite.sourceRef, ConditionalPublicationSite.sourceField,
                  PublicChoiceSite.compiledGuard, PublicChoiceSite.siteState,
                  decisionSiteState, compileCore] using publicGuard)
  | @binding Γ pending name who ty guard tail newName accounted fresh state unrestricted next ih =>
      intro instruction hmem
      simp only [instructions, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact .binding (.here _ _) unrestricted
      · cases ih instruction htail with
        | sample node dist hsem hcode => exact .sample node dist hsem hcode
        | binding site unrestricted => exact .binding (.commit site) unrestricted
        | publicChoice site publicGuard =>
            exact Origin.publicChoice (prog := .commit name who guard tail)
              (fresh := fresh) (state := state) (deadlineOf := deadlineOf)
              { site with decision := .commit site.decision
                          adjacent := by simpa only [SourceDecisionSite.continuation]
                            using site.adjacent } (by
                simpa only [PublicChoiceSite.PubliclyValidatable, PublicChoiceSite.compiledGuard,
                  PublicChoiceSite.siteState, decisionSiteState, compileCore] using publicGuard)
        | conditional site publicGuard =>
            exact Origin.conditional
              (prog := .commit name who guard tail)
              (fresh := fresh) (state := state) (deadlineOf := deadlineOf)
              { choice :=
                  { site.choice with
                    decision := .commit site.choice.decision
                    adjacent := by simpa only [SourceDecisionSite.continuation]
                      using site.choice.adjacent }
                specification := site.specification } (by
                simpa only [ConditionalPublicationSite.PubliclyValidatable,
                  ConditionalPublicationSite.sourceRef, ConditionalPublicationSite.sourceField,
                  PublicChoiceSite.compiledGuard, PublicChoiceSite.siteState,
                  decisionSiteState, compileCore] using publicGuard)
  | @publicChoice Γ pending name publicName who ty guard tail newName unresolved
      accounted fresh state publicGuard next ih =>
      intro instruction hmem
      simp only [instructions, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact .publicChoice _ publicGuard
      · exact (ih instruction htail).beforePair
  | @conditional Γ pending name publicName who ty guard tail spec unresolved newName
      accounted fresh state publicGuard next ih =>
      intro instruction hmem
      simp only [instructions, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact .conditional _ publicGuard
      · exact (ih instruction htail).beforePair
  | @conditionalCopy Γ pending name publicName who ty guard tail spec newName unresolved
      accounted fresh state publicGuard next ih =>
      intro instruction hmem
      simp only [instructions, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact .conditional _ publicGuard
      · exact (ih instruction htail).beforePair

/-- Successful lookup in a generated image identifies certified source code.
The address is arbitrary: callers need not assume an instruction selected from
the source, or restrict raw packets to generated ones. -/
theorem origin_of_lookup
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) (address : Nat) (instruction : ApplicationInstruction P L)
    (hlookup : (plan.image deadlineOf).lookup address = some instruction) :
    Origin prog fresh state deadlineOf instruction := by
  apply plan.instructions_origin deadlineOf instruction
  exact List.mem_of_find?_eq_some hlookup

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.origin_of_lookup' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.origin_of_lookup
