/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicyBindings
import Vegas.Compile.ApplicationImageProvenance

/-! # Binding provenance under a lifted player strategy

One player's structurally lifted source policy suffices to maintain agreement
between its recorded private registrations and accepted native snapshots.
All other players and the environment may use arbitrary runtime strategies.
This proves a premise of the native-to-source readout law throughout actual
execution; successful loading and source-state correspondence remain separate.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- From empty preparation and message histories, a single lifted player
maintains its accepted-binding provenance through every supported run.
This requires no fairness, deadline protection, restrictions on opponents,
or source-matching readout supplied as a hypothesis. -/
theorem runPolicies_lifted_registeredBindings
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) (profile : SourceBehavioralProfile prog)
    (owner : P) (players : P → (plan.image deadlineOf).application.PlayerPolicy)
    (howner : players owner = plan.liftProfile deadlineOf profile owner)
    (environment : (plan.image deadlineOf).application.EnvironmentPolicy)
    (memory : ApplicationImage.Memory P L)
    (hempty : ∀ field, memory.accepted field = none)
    (schedule : List (@Invocation P))
    (next : (plan.image deadlineOf).application.PolicyExecution)
    (hnext : next ∈ ((plan.image deadlineOf).application.runPolicies players environment schedule
      (PolicyExecution.initial (plan.image deadlineOf).application
        (MessageApplication.State.initial (plan.image deadlineOf).application
          (ApplicationImage.State.initial memory)))).support) :
    (plan.image deadlineOf).RegisteredBindings owner (next.principalHistory owner)
      next.native.application := by
  apply (plan.image deadlineOf).runPolicies_registeredBindings_of_registered_submissions
    memory hempty owner players environment ?_ schedule next hnext
  intro history view address handle hcommand
  rw [howner] at hcommand
  exact plan.liftProfileIn_binding_submission (plan.image deadlineOf) deadlineOf
    profile owner history view address handle hcommand

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.runPolicies_lifted_registeredBindings' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.runPolicies_lifted_registeredBindings
