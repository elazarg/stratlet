/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicy

/-! # Player-locality of source-profile lifting

The reference policy lifted for one principal depends only on that principal's
source behavioral policy. Policies assigned to other principals cannot affect
its command law. This is a coordinatewise proof-level property; it creates no
client artifact, restricts no runtime strategy, and asserts no outcome-level
strategic correspondence.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Replacing every other coordinate of a source profile leaves the selected
principal's generated application policy unchanged. -/
theorem liftProfileIn_eq_of_sourcePolicy_eq
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (first second : SourceBehavioralProfile prog) (player : P)
    (hpolicy : ∀ {Δ x b guard}
      (site : SourceDecisionSite player prog Δ x b guard) (visible),
      first player site visible = second player site visible) :
    plan.liftProfileIn image deadlineOf first player =
      plan.liftProfileIn image deadlineOf second player := by
  induction plan generalizing player with
  | ret => rfl
  | sample next ih =>
      funext history view
      simp only [liftProfileIn]
      split
      · have htail : ∀ {Δ x b guard}
            (site : SourceDecisionSite player _ Δ x b guard) (visible),
            first.afterSample player site visible =
              second.afterSample player site visible := by
          intro Δ x b guard site visible
          exact hpolicy (.sample site) visible
        exact congrFun (congrFun (ih first.afterSample second.afterSample player htail)
          history) view
      · rfl
  | binding unrestricted next ih =>
      funext history view
      simp only [liftProfileIn]
      split
      · have htail : ∀ {Δ x b nextGuard}
            (site : SourceDecisionSite player _ Δ x b nextGuard) (visible),
            first.afterCommit player site visible =
              second.afterCommit player site visible := by
          intro Δ x b nextGuard site visible
          exact hpolicy (.commit site) visible
        exact congrFun (congrFun (ih first.afterCommit second.afterCommit player htail)
          history) view
      · split
        · rename_i howner
          have hcoordinate : @first player = @second player := by
            funext Δ x b guard site visible
            exact hpolicy site visible
          subst player
          rw [hcoordinate]
        · rfl
  | publicChoice publicGuard next ih | conditional publicGuard next ih
  | conditionalCopy specification publicGuard next ih =>
      funext history view
      simp only [liftProfileIn]
      split
      · have htail : ∀ {Δ x b nextGuard}
            (site : SourceDecisionSite player _ Δ x b nextGuard) (visible),
            first.afterCommit.afterReveal player site visible =
              second.afterCommit.afterReveal player site visible := by
          intro Δ x b nextGuard site visible
          exact hpolicy (.commit (.reveal site)) visible
        exact congrFun (congrFun
          (ih first.afterCommit.afterReveal second.afterCommit.afterReveal player htail)
          history) view
      · split
        · rename_i howner
          have hcoordinate : @first player = @second player := by
            funext Δ x b guard site visible
            exact hpolicy site visible
          subst player
          rw [hcoordinate]
        · rfl

/-- The canonical generated policies inherit coordinatewise source-profile
locality from the ambient-image worker. -/
theorem liftProfile_eq_of_sourcePolicy_eq
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) (first second : SourceBehavioralProfile prog)
    (player : P) (hpolicy : ∀ {Δ x b guard}
      (site : SourceDecisionSite player prog Δ x b guard) (visible),
      first player site visible = second player site visible) :
    plan.liftProfile deadlineOf first player = plan.liftProfile deadlineOf second player :=
  plan.liftProfileIn_eq_of_sourcePolicy_eq (plan.image deadlineOf) deadlineOf
    first second player hpolicy

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.liftProfileIn_eq_of_sourcePolicy_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.liftProfileIn_eq_of_sourcePolicy_eq

/-- info: 'Vegas.ApplicationPlan.liftProfile_eq_of_sourcePolicy_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.liftProfile_eq_of_sourcePolicy_eq
