/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicy
import Interaction.ChoiceControllerHistory

/-! # Fresh caches for remaining generated instructions

The source-ordered reference policy samples a decision only when its generated
instruction has no recognized command in the owner's retained history.  This
module records that local operational condition for every instruction still
present in an application plan.  It does not assert progress, source/runtime
correspondence, or any restriction on arbitrary runtime policies.

The condition is phrased over emitted instructions.  Consequently conditional
publication uses the exact deadline-bearing endpoint emitted by the plan,
while cache recognition remains restricted to voluntary source choices and
rejects expiration traffic.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace ApplicationInstruction

/-- A player command is outside every cache used by this instruction.  Only
the instruction owner can change its relevant history, so commands by other
principals require no decoding condition. -/
def RejectsCommand (image : ApplicationImage P L) (who : P)
    (command : image.application.PlayerCommand) :
    ApplicationInstruction P L → Prop
  | .sample _ => True
  | .bind code => who = code.owner →
      (((ApplicationImage.registrationEncoding code.sourceSlot).privateCommand
          image.application).decode command = none ∧
        (code.encoding.submission image.application).decode command = none)
  | .publicChoice code => who = code.endpoint.owner →
      ((ApplicationImage.choiceEncoding (P := P)
        code.endpoint.publicationNode code.guard.ty).submission
          image.application).decode command = none
  | .conditional code => who = code.endpoint.owner →
      (((((code.endpoint.addressedChoiceEncoding
          (Value := L.Val code.secretTy)).reindex code.encoding).trans
        (ApplicationImage.conditionalTransport (P := P) code.secretTy)).submission
          image.application).decode command = none)

/-- No command already recorded in the relevant owner's history can supply
the sample-once choice for this generated instruction.  A binding has two
distinct caches: its private registration and its public handle submission.
Chance instructions have no player-side cache. -/
def CacheEmpty (image : ApplicationImage P L)
    (execution : image.application.PolicyExecution) :
    ApplicationInstruction P L → Prop
  | .sample _ => True
  | .bind code =>
      image.registrationCache code.sourceSlot
          (execution.principalHistory code.owner) = none ∧
        (code.encoding.submission image.application).cachedValue
          image.application (execution.principalHistory code.owner) = none
  | .publicChoice code =>
      let encoding :=
        (ApplicationImage.choiceEncoding (P := P)
          code.endpoint.publicationNode code.guard.ty).submission image.application
      encoding.cachedValue image.application
        (execution.principalHistory code.endpoint.owner) = none
  | .conditional code =>
      let encoding :=
        (((code.endpoint.addressedChoiceEncoding
            (Value := L.Val code.secretTy)).reindex code.encoding).trans
          (ApplicationImage.conditionalTransport (P := P) code.secretTy)).submission
            image.application
      encoding.cachedValue image.application
        (execution.principalHistory code.endpoint.owner) = none

/-- Empty principal histories contain no cached choice for any instruction. -/
theorem cacheEmpty_of_empty_histories
    (image : ApplicationImage P L)
    (execution : image.application.PolicyExecution)
    (hempty : ∀ who, execution.principalHistory who = [])
    (instruction : ApplicationInstruction P L) :
    instruction.CacheEmpty image execution := by
  cases instruction <;>
    simp [CacheEmpty, hempty, ApplicationImage.registrationCache]

/-- A supported player step preserves one instruction's empty caches when
the appended command is outside their decoding domains. -/
theorem cacheEmpty_playerStep
    (image : ApplicationImage P L)
    (instruction : ApplicationInstruction P L)
    (who : P) (execution : image.application.PolicyExecution)
    (command : image.application.PlayerCommand)
    (next : image.application.PolicyExecution)
    (hnext : next ∈
      (image.application.playerStep who execution command).support)
    (hfresh : instruction.CacheEmpty image execution)
    (hreject : instruction.RejectsCommand image who command) :
    instruction.CacheEmpty image next := by
  cases instruction with
  | sample code => trivial
  | bind code =>
      by_cases howner : who = code.owner
      · subst who
        have hhistory := image.application.playerStep_history_self
          code.owner execution command next hnext
        obtain ⟨hregister, hsubmit⟩ := hfresh
        obtain ⟨hrejectRegister, hrejectSubmit⟩ := hreject rfl
        constructor
        · unfold ApplicationImage.registrationCache at hregister ⊢
          rw [hhistory]
          exact
            ((ApplicationImage.registrationEncoding code.sourceSlot).privateCommand
              image.application).cachedValue_append_unrecognized
                image.application _ _ _ hregister hrejectRegister
        · rw [hhistory]
          exact (code.encoding.submission image.application).cachedValue_append_unrecognized
            image.application _ _ _ hsubmit hrejectSubmit
      · have hhistory := image.application.playerStep_other_history
          who code.owner (Ne.symm howner) execution command next hnext
        simpa [CacheEmpty, hhistory] using hfresh
  | publicChoice code =>
      by_cases howner : who = code.endpoint.owner
      · subst who
        have hhistory := image.application.playerStep_history_self
          code.endpoint.owner execution command next hnext
        rw [CacheEmpty, hhistory]
        exact ((ApplicationImage.choiceEncoding (P := P)
          code.endpoint.publicationNode code.guard.ty).submission
            image.application).cachedValue_append_unrecognized
              image.application _ _ _ hfresh (hreject rfl)
      · have hhistory := image.application.playerStep_other_history
          who code.endpoint.owner (Ne.symm howner) execution command next hnext
        simpa [CacheEmpty, hhistory] using hfresh
  | conditional code =>
      by_cases howner : who = code.endpoint.owner
      · subst who
        have hhistory := image.application.playerStep_history_self
          code.endpoint.owner execution command next hnext
        rw [CacheEmpty, hhistory]
        exact
          ((((code.endpoint.addressedChoiceEncoding
            (Value := L.Val code.secretTy)).reindex code.encoding).trans
              (ApplicationImage.conditionalTransport (P := P) code.secretTy)).submission
                image.application).cachedValue_append_unrecognized
                  image.application _ _ _ hfresh (hreject rfl)
      · have hhistory := image.application.playerStep_other_history
          who code.endpoint.owner (Ne.symm howner) execution command next hnext
        simpa [CacheEmpty, hhistory] using hfresh

/-- Environment steps preserve one instruction's cache freshness because
they do not append to any principal history. -/
theorem cacheEmpty_environmentPolicyStep
    (image : ApplicationImage P L)
    (instruction : ApplicationInstruction P L)
    (execution : image.application.PolicyExecution)
    (command : image.application.EnvironmentPolicyCommand)
    (next : image.application.PolicyExecution)
    (hnext : next ∈
      (image.application.environmentPolicyStep execution command).support)
    (hfresh : instruction.CacheEmpty image execution) :
    instruction.CacheEmpty image next := by
  have hhistory := image.application.environmentStep_principalHistory
    execution command next hnext
  cases instruction <;> simp_all [CacheEmpty]

end ApplicationInstruction

namespace ApplicationPlan

/-- Every instruction in the unexecuted plan suffix has a fresh player-side
sample cache.  Using the emitted instruction list makes this definition follow
the compiler's actual endpoint addresses, binding slots, and deadlines. -/
def RemainingCachesEmpty
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ}
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    (plan : ApplicationPlan accounted fresh state)
    (execution : image.application.PolicyExecution) : Prop :=
  (plan.instructions deadlineOf).Forall
    (ApplicationInstruction.CacheEmpty image execution)

/-- Canonical empty player histories make every cache in the remaining plan
fresh, independently of native application state and environment history. -/
theorem remainingCachesEmpty_of_empty_histories
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ}
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    (plan : ApplicationPlan accounted fresh state)
    (execution : image.application.PolicyExecution)
    (hempty : ∀ who, execution.principalHistory who = []) :
    plan.RemainingCachesEmpty image deadlineOf execution := by
  unfold RemainingCachesEmpty
  apply List.forall_iff_forall_mem.mpr
  intro instruction _hinstruction
  exact instruction.cacheEmpty_of_empty_histories image execution hempty

/-- A supported environment step preserves freshness of every remaining
instruction cache. -/
theorem remainingCachesEmpty_environmentPolicyStep
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ}
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    (plan : ApplicationPlan accounted fresh state)
    (execution : image.application.PolicyExecution)
    (command : image.application.EnvironmentPolicyCommand)
    (next : image.application.PolicyExecution)
    (hnext : next ∈
      (image.application.environmentPolicyStep execution command).support)
    (hfresh : plan.RemainingCachesEmpty image deadlineOf execution) :
    plan.RemainingCachesEmpty image deadlineOf next := by
  unfold RemainingCachesEmpty at hfresh ⊢
  apply List.forall_iff_forall_mem.mpr
  intro instruction hinstruction
  exact instruction.cacheEmpty_environmentPolicyStep image execution command next
    hnext ((List.forall_iff_forall_mem.mp hfresh) instruction hinstruction)

/-- A supported player step preserves every remaining cache when its appended
command is rejected by each remaining instruction's exact decoder. -/
theorem remainingCachesEmpty_playerStep
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ}
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    (plan : ApplicationPlan accounted fresh state)
    (who : P) (execution : image.application.PolicyExecution)
    (command : image.application.PlayerCommand)
    (next : image.application.PolicyExecution)
    (hnext : next ∈
      (image.application.playerStep who execution command).support)
    (hfresh : plan.RemainingCachesEmpty image deadlineOf execution)
    (hreject : ∀ instruction ∈ plan.instructions deadlineOf,
      instruction.RejectsCommand image who command) :
    plan.RemainingCachesEmpty image deadlineOf next := by
  unfold RemainingCachesEmpty at hfresh ⊢
  apply List.forall_iff_forall_mem.mpr
  intro instruction hinstruction
  exact instruction.cacheEmpty_playerStep image who execution command next hnext
    ((List.forall_iff_forall_mem.mp hfresh) instruction hinstruction)
    (hreject instruction hinstruction)

end ApplicationPlan

end Vegas

/-- info: 'Vegas.ApplicationPlan.remainingCachesEmpty_environmentPolicyStep' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.remainingCachesEmpty_environmentPolicyStep

/-- info: 'Vegas.ApplicationPlan.remainingCachesEmpty_playerStep' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.remainingCachesEmpty_playerStep
