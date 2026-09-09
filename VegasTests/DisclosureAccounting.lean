/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Accounting
import VegasTests.OptionalDisclosure
import VegasTests.PersistentDisclosure

/-! # Accounting plans for conditional-disclosure examples

These plans supply checked admission for existing source syntax. Implementing
their optional decisions by runtime timeouts requires a separate correspondence.
-/

noncomputable section

namespace VegasTests.DisclosureAccounting

open Vegas

def optionalSpec : ConditionalOpening
    (Γ := OptionalDisclosure.OpeningContext) (copyName := 4)
    (who := (0 : TestPlayer)) (copyTy := .option .bool)
    OptionalDisclosure.openingGuard where
  secretTy := .bool
  source := 0
  binding := .there (.there (.there .here))
  encoding := Equiv.refl (Option Bool)
  sound := by
    intro env chosen hlegal
    change (if chosen.isNone then true else decide
      (chosen = some (env.get (.there (.there (.there .here)))))) = true at hlegal
    cases chosen <;> simp_all
  decline_legal := by
    intro env
    rfl

def optionalPlanWithPayoffs
    (payouts : List (TestPlayer × Expr OptionalDisclosure.PayoffContext .int)) :
    CommitmentAccounting ∅ (OptionalDisclosure.coreWithPayoffs payouts) := by
  unfold OptionalDisclosure.coreWithPayoffs
  apply CommitmentAccounting.commit (by simp)
  apply CommitmentAccounting.commit (by simp)
  apply CommitmentAccounting.reveal (by simp)
  apply CommitmentAccounting.sample
  apply CommitmentAccounting.opening optionalSpec (by simp [optionalSpec]) (by simp)
  change CommitmentAccounting ∅ _
  apply CommitmentAccounting.commit (by simp)
  apply CommitmentAccounting.reveal (by simp)
  exact CommitmentAccounting.ret (by simp)

def optionalPlan : CommitmentAccounting ∅ OptionalDisclosure.core :=
  optionalPlanWithPayoffs [(0, OptionalDisclosure.payoff)]

def persistentFirstSpec : ConditionalOpening
    (Γ := PersistentDisclosure.FirstContext) (copyName := 4)
    (who := (0 : PersistentDisclosure.Player)) (copyTy := .option .bool)
    PersistentDisclosure.firstGuard where
  secretTy := .bool
  source := 0
  binding := .there (.there (.there .here))
  encoding := Equiv.refl (Option Bool)
  sound := by
    intro env chosen hlegal
    change (if chosen.isNone then true else decide
      (chosen = some (env.get (.there (.there (.there .here)))))) = true at hlegal
    cases chosen <;> simp_all
  decline_legal := by
    intro env
    rfl

def persistentPlan :
    CommitmentAccounting ∅ PersistentDisclosure.core := by
  unfold PersistentDisclosure.core
  apply CommitmentAccounting.commit (by simp)
  apply CommitmentAccounting.commit (by simp)
  apply CommitmentAccounting.reveal (by simp)
  apply CommitmentAccounting.sample
  apply CommitmentAccounting.opening persistentFirstSpec
    (by simp [persistentFirstSpec]) (by simp)
  change CommitmentAccounting ∅ _
  apply CommitmentAccounting.commit (by simp)
  apply CommitmentAccounting.reveal (by simp)
  apply CommitmentAccounting.commit (by simp)
  apply CommitmentAccounting.reveal (by simp)
  exact CommitmentAccounting.ret (by simp)

def optionalChecked : WFProgram TestPlayer simpleExpr where
  core := OptionalDisclosure.source
  accounted := optionalPlan
  legal := OptionalDisclosure.legal

def persistentChecked : WFProgram PersistentDisclosure.Player simpleExpr where
  core := PersistentDisclosure.source
  accounted := persistentPlan
  legal := PersistentDisclosure.legal

/-- A pending sealed binding cannot disappear at return without either a
literal reveal or a certified disposition. -/
theorem unresolved_return_rejected :
    ¬Nonempty (CommitmentAccounting {0}
      (.ret [] : VegasCore TestPlayer simpleExpr
        [(0, .sealed (0 : TestPlayer) .bool)])) := by
  rintro ⟨plan⟩
  have hempty := plan.pending_empty_at_return
  simp at hempty

def unresolvedSource : GraphProgram TestPlayer simpleExpr where
  Γ := [(0, .sealed (0 : TestPlayer) .bool)]
  prog := .ret []
  env := (VEnv.empty simpleExpr).cons false
  wctx := by simp [WFCtx]
  fresh := by simp [FreshBindings]

theorem unresolved_source_not_checked :
    ¬∃ checked : WFProgram TestPlayer simpleExpr,
      checked.core = unresolvedSource := by
  rintro ⟨checked, hcore⟩
  have haccounted := checked.accounted
  rw [hcore] at haccounted
  exact unresolved_return_rejected ⟨haccounted⟩

/-- The certificate cannot validate publication of the opposite Boolean as a
successful opening of its named source. -/
theorem wrong_successful_copy_rejected
    (env : VEnv simpleExpr OptionalDisclosure.OpeningContext) :
    evalGuard OptionalDisclosure.openingGuard
      (some (!(env.get optionalSpec.binding))) ((env.toView 0).eraseEnv) ≠ true := by
  intro hlegal
  rcases optionalSpec.sound env _ hlegal with hnone | hsame
  · change some (Bool.not (env.get optionalSpec.binding)) = none at hnone
    contradiction
  · have hsame' :
        (some (Bool.not (env.get optionalSpec.binding)) : Option Bool) =
          some (env.get optionalSpec.binding) := hsame
    have hvalue := Option.some.inj hsame'
    exact (Bool.not_ne_self _ hvalue)

theorem optional_original_disposed :
    0 ∈ optionalPlan.dispositions := by
  change 0 ∈ ({0} : Finset VarId)
  simp

theorem persistent_original_disposed_once :
    persistentPlan.dispositions = {0} := by
  change ({0} : Finset VarId) = {0}
  rfl

theorem optional_publication_site :
    optionalPlan.publicationSites = [(0, 5)] := by
  change [(0, 5)] = [(0, 5)]
  rfl

theorem persistent_publication_site :
    persistentPlan.publicationSites = [(0, 5)] := by
  change [(0, 5)] = [(0, 5)]
  rfl

/-- The later optional value is an ordinary commit/reveal after the original
binding has already been resolved by the first certified disposition. -/
theorem persistent_later_copy_literal :
    8 ∈ RevealedSources PersistentDisclosure.core ∧
      8 ∉ persistentPlan.dispositions := by
  constructor
  · decide
  · change 8 ∉ ({0} : Finset VarId)
    simp

/-- info: 'VegasTests.DisclosureAccounting.optionalPlan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms optionalPlan

/-- info: 'VegasTests.DisclosureAccounting.persistentPlan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms persistentPlan

end VegasTests.DisclosureAccounting
