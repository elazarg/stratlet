/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Basic

/-! # Dependency-local public guard validation

Public choice endpoints evaluate only the stored variables that occur in the
compiled guard expression.  The proposed action is supplied directly and is
not read from the store.  This footprint is intentionally smaller than an
`EventGuard`'s `choiceReads`, which describes all information available to the
choosing player and may include private values irrelevant to validation.
-/

namespace Vegas.EventGraph

variable {L : IExpr} {actionTy : L.Ty}

private def storedDependencyRefsFrom (code : GuardCode L actionTy) :
    (context : Ctx L.Ty) →
      ({name : VarId} → {ty : L.Ty} →
        HasVar context name ty → HasVar code.Context name ty) →
      Finset (FieldRef L)
  | [], _ => ∅
  | (name, _ty) :: tail, embed =>
      let rest := storedDependencyRefsFrom code tail (fun binding => embed (.there binding))
      if name ∈ L.exprDeps code.expr then
        insert (code.ref (embed .here)) rest
      else
        rest

/-- Actual stored field references needed to execute the retained guard code.
The action variable at the head of the expression context is not a field. -/
def GuardCode.storedDependencyRefs (code : GuardCode L actionTy) :
    Finset (FieldRef L) :=
  storedDependencyRefsFrom code code.Context (fun binding => binding)

private theorem storedDependencyRef_mem_from (code : GuardCode L actionTy)
    (context : Ctx L.Ty)
    (embed : {name : VarId} → {ty : L.Ty} →
      HasVar context name ty → HasVar code.Context name ty)
    {name : VarId} {ty : L.Ty} (binding : HasVar context name ty)
    (hdependency : name ∈ L.exprDeps code.expr) :
    code.ref (embed binding) ∈ storedDependencyRefsFrom code context embed := by
  induction binding with
  | here => simp [storedDependencyRefsFrom, hdependency]
  | there binding ih =>
      simp only [storedDependencyRefsFrom]
      split
      · exact Finset.mem_insert_of_mem
          (ih (fun inner => embed (.there inner)) hdependency)
      · exact ih (fun inner => embed (.there inner)) hdependency

theorem GuardCode.storedDependencyRef_mem (code : GuardCode L actionTy)
    {name : VarId} {ty : L.Ty} (binding : HasVar code.Context name ty)
    (hdependency : name ∈ L.exprDeps code.expr) :
    code.ref binding ∈ code.storedDependencyRefs := by
  exact storedDependencyRef_mem_from code code.Context (fun inner => inner)
    binding hdependency

private theorem storedDependencyRefsFrom_eq_empty (code : GuardCode L actionTy)
    (context : Ctx L.Ty)
    (embed : {name : VarId} → {ty : L.Ty} →
      HasVar context name ty → HasVar code.Context name ty)
    (hdependencies : L.exprDeps code.expr = ∅) :
    storedDependencyRefsFrom code context embed = ∅ := by
  induction context with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨name, ty⟩
      simp [storedDependencyRefsFrom, hdependencies,
        ih (fun binding => embed (.there binding))]

theorem GuardCode.storedDependencyRefs_eq_empty (code : GuardCode L actionTy)
    (hdependencies : L.exprDeps code.expr = ∅) :
    code.storedDependencyRefs = ∅ := by
  exact storedDependencyRefsFrom_eq_empty code code.Context (fun binding => binding)
    hdependencies

private theorem storedDependencyRefsFrom_subset (guard : EventGuard L)
    (context : Ctx L.Ty)
    (embed : {name : VarId} → {ty : L.Ty} →
      HasVar context name ty → HasVar guard.code.Context name ty) :
    storedDependencyRefsFrom guard.code context embed ⊆ guard.choiceReads := by
  induction context with
  | nil => simp [storedDependencyRefsFrom]
  | cons head tail ih =>
      rcases head with ⟨name, ty⟩
      simp only [storedDependencyRefsFrom]
      split
      · apply Finset.insert_subset
        · exact guard.read_mem (embed .here)
        · exact ih (fun binding => embed (.there binding))
      · exact ih (fun binding => embed (.there binding))

theorem EventGuard.storedDependencyRefs_subset (guard : EventGuard L) :
    guard.code.storedDependencyRefs ⊆ guard.choiceReads := by
  exact storedDependencyRefsFrom_subset guard guard.code.Context (fun binding => binding)

/-- The dependency-local validation footprint of a compiled guard. -/
def EventGuard.validationReads (guard : EventGuard L) : Finset (FieldRef L) :=
  guard.code.storedDependencyRefs

theorem EventGuard.validationDependency_mem (guard : EventGuard L)
    {name : VarId} {ty : L.Ty} (binding : HasVar guard.code.Context name ty)
    (hdependency : name ∈ L.exprDeps guard.code.expr) :
    guard.code.ref binding ∈ guard.validationReads :=
  guard.code.storedDependencyRef_mem binding hdependency

theorem EventGuard.validationReads_subset_choiceReads (guard : EventGuard L) :
    guard.validationReads ⊆ guard.choiceReads :=
  guard.storedDependencyRefs_subset

/-- Eligibility for using the raw validator with a genuinely public runtime
store.  Generation of a dependency footprint does not assert this property. -/
def EventGuard.PubliclyValidatable {Player : Type} [DecidableEq Player]
    (guard : EventGuard L)
    (graph : Graph Player L) : Prop :=
  ∀ ref, ref ∈ guard.validationReads → graph.fieldRefPublic ref

/-- Agreement on all public graph fields specializes to the exact dependency
footprint of a publicly validatable guard. -/
theorem EventGuard.validationReads_agree_of_publiclyValidatable
    {Player : Type} [DecidableEq Player]
    (guard : EventGuard L) (graph : Graph Player L) (left right : Store L)
    (hvalid : guard.PubliclyValidatable graph)
    (hagrees : ∀ ref, graph.fieldRefPublic ref →
      Store.getAs left ref.field ref.ty = Store.getAs right ref.field ref.ty) :
    ∀ ref (_href : ref ∈ guard.validationReads),
      Store.getAs left ref.field ref.ty = Store.getAs right ref.field ref.ty := by
  intro ref href
  exact hagrees ref (hvalid ref href)

/-- Evaluate retained guard code from only its public stored dependencies. -/
def EventGuard.evalValidation (guard : EventGuard L) (action : L.Val guard.ty)
    (reads : ReadEnv L guard.validationReads) : Bool :=
  L.toBool <| L.evalDeps guard.code.expr fun _name _ty binding dependency =>
    match binding with
    | .here => action
    | .there stored => reads.read (guard.code.ref stored)
        (guard.validationDependency_mem stored dependency)

/-- Missing public reads reject the request.  No source environment or graph
configuration is consulted by this executable validator. -/
def EventGuard.validate (guard : EventGuard L) (store : Store L)
    (action : L.Val guard.ty) : Bool :=
  match ReadEnv.ofStoreExec? store guard.validationReads with
  | none => false
  | some reads => guard.evalValidation action reads

private theorem EventGuard.evalValidation_eq_eval (guard : EventGuard L)
    (action : L.Val guard.ty) (publicReads : ReadEnv L guard.validationReads)
    (choiceReads : ReadEnv L guard.choiceReads)
    (hagrees : ∀ {name : VarId} {ty : L.Ty}
      (binding : HasVar guard.code.Context name ty)
      (hdependency : name ∈ L.exprDeps guard.code.expr),
      publicReads.read (guard.code.ref binding)
          (guard.validationDependency_mem binding hdependency) =
        choiceReads.read (guard.code.ref binding) (guard.read_mem binding)) :
    guard.evalValidation action publicReads = guard.eval action choiceReads := by
  unfold EventGuard.evalValidation EventGuard.eval
  rw [← L.evalDeps_eq_eval guard.code.expr
    (Env.cons action fun _name _ty binding =>
      choiceReads.read (guard.code.ref binding) (guard.read_mem binding))]
  congr 2
  funext name ty binding hdependency
  cases binding with
  | here => rfl
  | there stored => exact hagrees stored hdependency

/-- The generated validator agrees with ordinary graph guard evaluation when
the supplied public store contains the same values on every syntactic guard
dependency.  Values in `choiceReads` outside that footprint are irrelevant. -/
theorem EventGuard.validate_eq_eval (guard : EventGuard L)
    (store : Store L) (action : L.Val guard.ty)
    (choiceReads : ReadEnv L guard.choiceReads)
    (hagrees : ∀ ref (href : ref ∈ guard.validationReads),
      Store.getAs store ref.field ref.ty =
        some (choiceReads.read ref (guard.validationReads_subset_choiceReads href))) :
    guard.validate store action = guard.eval action choiceReads := by
  have available : ∀ ref, ref ∈ guard.validationReads →
      (Store.getAs store ref.field ref.ty).isSome := by
    intro ref href
    rw [hagrees ref href]
    rfl
  unfold EventGuard.validate ReadEnv.ofStoreExec?
  rw [dif_pos available]
  apply guard.evalValidation_eq_eval action
  intro name ty binding hdependency
  have href := guard.validationDependency_mem binding hdependency
  have hpublic := ReadEnv.getAs_ofStoreChecked store guard.validationReads available href
  rw [hagrees _ href] at hpublic
  exact Option.some.inj hpublic.symm

theorem EventGuard.validationReads_eq_empty (guard : EventGuard L)
    (hdependencies : L.exprDeps guard.code.expr = ∅) :
    guard.validationReads = ∅ :=
  guard.code.storedDependencyRefs_eq_empty hdependencies

end Vegas.EventGraph
