/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPlan

/-! # Public initial inputs used by generated controllers

Canonical application initialization has no owner-private cache for source
initial fields.  This proof-side certificate therefore requires only the
initial fields actually read by generated player controllers to be public.
It is backend eligibility, not source well-formedness, and is not retained in
the emitted runtime instruction image.
-/

noncomputable section

namespace Vegas.ToEventGraph.BuildResult

open Vegas.EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The exact initial-field premise consumed by source controller readout for
one compiled dependency footprint. -/
def InitialReadsPublic (result : BuildResult P L) (reads : Finset (FieldRef L)) : Prop :=
  ∀ ref ∈ reads, ∀ spec, result.graph.field? ref.field = some spec →
    ∀ value, spec.source = .initial value → spec.owner = none

/-- A stronger, convenient condition saying that every initial field in the
compiled graph is public. -/
def AllInitialFieldsPublic (result : BuildResult P L) : Prop :=
  ∀ field spec, result.graph.field? field = some spec →
    ∀ value, spec.source = .initial value → spec.owner = none

theorem AllInitialFieldsPublic.reads
    {result : BuildResult P L} (hall : result.AllInitialFieldsPublic)
    (reads : Finset (FieldRef L)) : result.InitialReadsPublic reads := by
  intro ref _ spec hfield value hinitial
  exact hall ref.field spec hfield value hinitial

/-- Public ownership in the actual initial-field list is sufficient. Fields
allocated by events cannot satisfy the initial-source premise. -/
theorem allInitialFieldsPublic_of_owners (result : BuildResult P L)
    (hpublic : ∀ initial ∈ result.initialFields, initial.owner = none) :
    result.AllInitialFieldsPublic := by
  intro field spec hfield value hinitial
  unfold Graph.field? at hfield
  split at hfield
  · cases hget : result.graph.initialFields[field]? with
    | none => simp only [hget, reduceCtorEq] at hfield
    | some initial =>
        simp only [hget, Option.some.injEq] at hfield
        subst spec
        exact hpublic initial (List.mem_of_getElem? hget)
  · cases hget : result.graph.nodes[field - result.graph.initialFields.length]? with
    | none => simp only [hget, reduceCtorEq] at hfield
    | some event =>
        simp only [hget, Option.some.injEq] at hfield
        subst spec
        cases hinitial

end Vegas.ToEventGraph.BuildResult

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every source decision implemented by a player controller reads only
public initial fields.  Samples already use a public source context and add no
player-controller obligation. -/
def InitialControllerReadsPublic :
    {Γ : VCtx P L} → {pending : Finset VarId} → {prog : VegasCore P L Γ} →
      {accounted : CommitmentAccounting pending prog} → {fresh : FreshBindings prog} →
      {state : BuildState P L Γ} → ApplicationPlan accounted fresh state → Prop
  | _, _, _, _, _, _, .ret _ _ _ => True
  | _, _, _, _, _, _, .sample next => next.InitialControllerReadsPublic
  | _, _, _, _, _, _,
      .binding (name := name) (who := who) (guard := guard) (tail := tail)
        (fresh := fresh) (state := state) _ next =>
      (compileCore (.commit name who guard tail) fresh state).InitialReadsPublic
          (eventGuardOf state who guard).choiceReads ∧
        next.InitialControllerReadsPublic
  | _, _, _, _, _, _,
      .publicChoice (name := name) (publicName := publicName) (who := who)
        (guard := guard) (tail := tail) (fresh := fresh) (state := state) _ next =>
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh state).InitialReadsPublic (eventGuardOf state who guard).choiceReads ∧
        next.InitialControllerReadsPublic
  | _, _, _, _, _, _,
      .conditional (name := name) (publicName := publicName) (who := who)
        (guard := guard) (tail := tail) (fresh := fresh) (state := state) _ next =>
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh state).InitialReadsPublic (eventGuardOf state who guard).choiceReads ∧
        next.InitialControllerReadsPublic
  | _, _, _, _, _, _,
      .conditionalCopy (name := name) (publicName := publicName) (who := who)
        (guard := guard) (tail := tail) (fresh := fresh) (state := state) _ _ next =>
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh state).InitialReadsPublic (eventGuardOf state who guard).choiceReads ∧
        next.InitialControllerReadsPublic

/-- Public ownership of every initial graph field discharges the smaller
controller-footprint certificate for any application plan. -/
theorem initialControllerReadsPublic_of_allInitialFieldsPublic
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (hall : (compileCore prog fresh state).AllInitialFieldsPublic) :
    plan.InitialControllerReadsPublic := by
  revert hall
  induction plan with
  | ret => intro _; trivial
  | sample next ih => intro hall; exact ih hall
  | binding unrestricted next ih =>
      intro hall
      exact ⟨hall.reads _, ih hall⟩
  | publicChoice publicGuard next ih =>
      intro hall
      exact ⟨hall.reads _, ih hall⟩
  | conditional publicGuard next ih =>
      intro hall
      exact ⟨hall.reads _, ih hall⟩
  | conditionalCopy spec publicGuard next ih =>
      intro hall
      exact ⟨hall.reads _, ih hall⟩

end Vegas.ApplicationPlan

/--
info: 'Vegas.ApplicationPlan.initialControllerReadsPublic_of_allInitialFieldsPublic'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.initialControllerReadsPublic_of_allInitialFieldsPublic
