/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.Imperative

/-!
# Check-level gas instrumentation

This pass adds one observation to ordered imperative checking: an abstract
natural-number charge for every check actually evaluated. It is deliberately
parameterized by a cost model and does not claim to be an EVM gas schedule.

Metering is defined as a decoration of the established first-failure result.
Erasing the charge is therefore proved to recover exactly the unmetered result,
including its successful prefix and first failed check.
-/

namespace Vegas.Machine.Contract.Gas

open Imperative

/-- Abstract cost assigned to evaluating one lowered check. -/
structure CheckCostModel (Check : Type) where
  cost : Check → Nat

namespace CheckCostModel

/-- Unit-cost model, useful when only the number of evaluated checks matters.
-/
def uniform (Check : Type) : CheckCostModel Check where
  cost := fun _ => 1

end CheckCostModel

/-- First-failure result decorated with the total charge of the evaluated
prefix, including the failed check on rejection. -/
inductive MeteredCheckResult (Check : Type) where
  | accepted (passed : List Check) (gasUsed : Nat)
  | rejected (passed : List Check) (failed : Check) (gasUsed : Nat)

namespace MeteredCheckResult

/-- Forget only the gas observation. -/
def erase {Check : Type} : MeteredCheckResult Check → CheckResult Check
  | .accepted passed _ => .accepted passed
  | .rejected passed failed _ => .rejected passed failed

/-- Total abstract gas charged by the check runner. -/
def gasUsed {Check : Type} : MeteredCheckResult Check → Nat
  | .accepted _ gas => gas
  | .rejected _ _ gas => gas

/-- Acceptance projection inherited from the unmetered result. -/
def succeeded {Check : Type} (result : MeteredCheckResult Check) : Bool :=
  result.erase.succeeded

end MeteredCheckResult

/-- Decorate an unmetered first-failure result with exactly the costs of the
checks it evaluated. -/
def meter {Check : Type} (costs : CheckCostModel Check) :
    CheckResult Check → MeteredCheckResult Check
  | .accepted passed =>
      .accepted passed ((passed.map costs.cost).sum)
  | .rejected passed failed =>
      .rejected passed failed ((passed.map costs.cost).sum + costs.cost failed)

/-- Run ordered checks and add the cost observation as a separate pass. -/
def runChecks {Check : Type} (costs : CheckCostModel Check)
    (evaluate : Check → Bool) (checks : List Check) :
    MeteredCheckResult Check :=
  meter costs (Imperative.runChecks evaluate checks)

/-- Gas instrumentation erases to exactly the established ordered runner. -/
@[simp] theorem erase_runChecks {Check : Type}
    (costs : CheckCostModel Check) (evaluate : Check → Bool)
    (checks : List Check) :
    (runChecks costs evaluate checks).erase =
      Imperative.runChecks evaluate checks := by
  unfold runChecks
  cases Imperative.runChecks evaluate checks <;> rfl

/-- Gas instrumentation cannot change acceptance. -/
theorem runChecks_succeeded {Check : Type}
    (costs : CheckCostModel Check) (evaluate : Check → Bool)
    (checks : List Check) :
    (runChecks costs evaluate checks).succeeded =
      Imperative.evaluateAll evaluate checks := by
  rw [MeteredCheckResult.succeeded, erase_runChecks,
    Imperative.runChecks_succeeded]

/-- Under the unit-cost model, gas is exactly the number of checks evaluated.
-/
theorem uniform_gasUsed_eq_checkedCount {Check : Type}
    (result : CheckResult Check) :
    (meter (CheckCostModel.uniform Check) result).gasUsed =
      result.checkedCount := by
  cases result <;> simp [meter, CheckCostModel.uniform,
    MeteredCheckResult.gasUsed, CheckResult.checkedCount]

end Vegas.Machine.Contract.Gas
