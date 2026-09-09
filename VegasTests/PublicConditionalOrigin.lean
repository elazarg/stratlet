/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationBindingOrigins
import Vegas.Compile.ApplicationPlan
import Vegas.Core.ExprSimple

/-! # Binding-origin failure after a generated public choice

This checked source is accepted by the currently separate public-choice and
conditional-copy plan constructors.  Its image has no binding instruction:
publishing the first choice writes the source value but does not synthesize the
ideal handle required by the later commitment-backed conditional endpoint.
-/

noncomputable section

namespace VegasTests.PublicConditionalOrigin

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction

abbrev Player := Fin 1
abbrev FirstContext : VCtx Player simpleExpr :=
  [(1, .pub .bool), (0, .sealed 0 .bool)]

def optionalGuard :
    Expr ((2, .option .bool) :: eraseVCtx (viewVCtx (0 : Player) FirstContext)) .bool :=
  .ite (.isNone (.var 2 .here)) (.constBool true)
    (.eq (.var 2 .here) (.some (.var 0 (.there (.there .here)))))

def terminal : VegasCore Player simpleExpr
    ([(3, .pub (.option .bool)), (2, .sealed 0 (.option .bool))] ++ FirstContext) :=
  .ret []

def firstTail : VegasCore Player simpleExpr FirstContext :=
  .commit 2 0 optionalGuard (.reveal 3 0 2 .here terminal)

def core : VegasCore Player simpleExpr [] :=
  .commit 0 0 (.constBool true) (.reveal 1 0 0 .here firstTail)

def source : GraphProgram Player simpleExpr where
  Γ := []
  prog := core
  env := VEnv.empty simpleExpr
  wctx := by simp [WFCtx]
  fresh := by simp [core, firstTail, terminal, FreshBindings, Fresh]

def checked : WFProgram Player simpleExpr where
  core := source
  accounted := CommitmentAccounting.ofRevealComplete core source.fresh []
    (by simp) (by decide)
  legal := by
    change Legal core
    unfold core firstTail
    constructor
    · intro _
      exact ⟨false, rfl⟩
    · constructor
      · intro env
        exact ⟨none, rfl⟩
      · trivial

def specification : ConditionalOpening
    (P := Player) (L := simpleExpr) (Γ := FirstContext)
    (copyName := 2) (who := 0) (copyTy := .option .bool) optionalGuard where
  secretTy := .bool
  source := 0
  binding := .there .here
  encoding := Equiv.refl (Option Bool)
  sound := by
    intro env chosen hlegal
    change (if chosen.isNone then true else
      decide (chosen = some (env.get (.there .here)))) = true at hlegal
    cases chosen <;> simp_all
  decline_legal := by
    intro env
    rfl

def compilerInitial : BuildState Player simpleExpr [] :=
  BuildState.fromInitial (initialState source.Γ source.env source.wctx)

def plan : ApplicationPlan checked.accounted source.fresh compilerInitial := by
  apply ApplicationPlan.publicChoice
  · intro ref href
    change ref ∈ (∅ : Finset (FieldRef simpleExpr)) at href
    simp at href
  apply ApplicationPlan.conditionalCopy specification
  · intro ref href
    left
    change ref ∈ ({({ field := 0, ty := .bool } : FieldRef simpleExpr)} :
      Finset (FieldRef simpleExpr)) at href
    change ref = ({ field := 0, ty := .bool } : FieldRef simpleExpr)
    simpa using href
  apply ApplicationPlan.ret

def image : ApplicationImage Player simpleExpr := plan.image (fun _ => 10)

theorem generated_image_has_no_binding_origins : ¬ image.HasBindingOrigins := by
  simp [image, ApplicationPlan.image, ApplicationImage.HasBindingOrigins,
    ApplicationImage.HasBindingOriginsFrom, plan, ApplicationPlan.instructions]

def beforeConditional : BuildState Player simpleExpr FirstContext :=
  (((compilerInitial.addCommitEvent (actionName := 0) (actionTy := BaseTy.bool)
    0 0 (.constBool true) source.fresh.1).1).addRevealEvent
      1 0 .here source.fresh.2.1).1

def conditionalSite : ConditionalPublicationSite firstTail := by
  unfold firstTail
  exact ConditionalPublicationSite.atHead 2 3 0 optionalGuard terminal specification

def conditionalCode : ConditionalCode Player simpleExpr :=
  conditionalSite.code source.fresh.2.2 beforeConditional 0 10

theorem image_lookup_conditional :
    image.lookup 3 = some (.conditional conditionalCode) := rfl

def initialExecution : image.application.State :=
  MessageApplication.State.initial image.application
    (ApplicationImage.State.initial (ApplicationImage.Memory.initial (compile source).graph))

def submitted : image.application.State :=
  { initialExecution with
    pool := (initialExecution.pool.submit 0 (.choice 1 ⟨.bool, true⟩)).2 }

def included : image.application.State := image.application.includePending submitted (0, 0)

theorem public_value_without_accepted_handle :
    Store.getAs included.application.memory.store conditionalCode.sourceField .bool =
        some true ∧
      included.application.memory.accepted conditionalCode.sourceField = none := by
  decide

theorem conditional_not_ready_after_public_inclusion :
    conditionalCode.endpoint.ready
      (included.application.memory.accepted conditionalCode.sourceField)
      included.application.memory.done = false := by
  decide

end VegasTests.PublicConditionalOrigin

/-- info: 'VegasTests.PublicConditionalOrigin.generated_image_has_no_binding_origins'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PublicConditionalOrigin.generated_image_has_no_binding_origins

/-- info: 'VegasTests.PublicConditionalOrigin.conditional_not_ready_after_public_inclusion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PublicConditionalOrigin.conditional_not_ready_after_public_inclusion
