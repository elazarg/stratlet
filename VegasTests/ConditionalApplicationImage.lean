/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ConditionalImage
import Vegas.Compile.ApplicationImageBindings
import Vegas.Compile.ApplicationPlanAllocation
import VegasTests.Game

/-! # Generated conditional application image

A three-node checked source supplies both the opaque binding instruction and
its accounted conditional publication instruction.  The examples below use the
shared message runner; source configuration is used only to generate code and
state correctness evidence.
-/

noncomputable section

namespace VegasTests.ConditionalApplicationImage

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  GameTheory.Math.Probability

abbrev Player := Fin 2
abbrev OpeningContext : VCtx Player simpleExpr := [(0, .sealed 0 .bool)]

def openingGuard :
    Expr ((1, .option .bool) :: eraseVCtx (viewVCtx (0 : Player) OpeningContext)) .bool :=
  .ite (.isNone (.var 1 .here)) (.constBool true)
    (.eq (.var 1 .here) (.some (.var 0 (.there .here))))

def tail : VegasCore Player simpleExpr
    [(2, .pub (.option .bool)), (1, .sealed 0 (.option .bool)),
      (0, .sealed 0 .bool)] :=
  .ret []

def core : VegasCore Player simpleExpr [] :=
  .commit 0 0 (.constBool true)
    (.commit 1 0 openingGuard (.reveal 2 0 1 .here tail))

def source : GraphProgram Player simpleExpr where
  Γ := []
  prog := core
  env := VEnv.empty simpleExpr
  wctx := by simp
  fresh := by simp [core, tail, FreshBindings, Fresh]

def specification : ConditionalOpening
    (Γ := OpeningContext) (copyName := 1) (who := (0 : Player))
    (copyTy := .option .bool) openingGuard where
  secretTy := .bool
  source := 0
  binding := .here
  encoding := Equiv.refl (Option Bool)
  sound := by
    intro env chosen hlegal
    change (if chosen.isNone then true else decide (chosen = some (env.get .here))) = true at hlegal
    cases chosen <;> simp_all
  decline_legal := by intro env; rfl

def plan : CommitmentAccounting ∅ core := by
  unfold core
  apply CommitmentAccounting.commit (by simp)
  apply CommitmentAccounting.opening specification (by simp [specification]) (by simp)
  change CommitmentAccounting ∅ _
  exact CommitmentAccounting.ret (by simp)

def checked : WFProgram Player simpleExpr where
  core := source
  accounted := plan
  legal := by
    unfold source core
    constructor
    · intro _
      exact ⟨false, rfl⟩
    · constructor
      · intro _
        exact ⟨none, rfl⟩
      · trivial

def initialSite : SourceDecisionSite (0 : Player) core [] 0 .bool (.constBool true) :=
  .here _ _

def openingSite : CommitmentAccounting.OpeningSite plan := by
  unfold plan
  apply CommitmentAccounting.OpeningSite.commit
  apply CommitmentAccounting.OpeningSite.here

def compilerInitial : BuildState Player simpleExpr source.Γ :=
  BuildState.fromInitial (initialState source.Γ source.env source.wctx)

theorem opening_publicly_validatable :
    openingSite.PubliclyValidatable source.fresh compilerInitial := by
  intro ref href
  left
  change ref ∈ ({({ field := 0, ty := .bool } : FieldRef simpleExpr)} :
    Finset (FieldRef simpleExpr)) at href
  have hsource : openingSite.sourceRef source.fresh compilerInitial =
      ({ field := 0, ty := .bool } : FieldRef simpleExpr) := rfl
  rw [hsource]
  simpa using href

def guardedOriginal :
    Expr ((0, .bool) :: ([] : CtxSimple)) .bool :=
  .var 0 .here

/-- The source remains valid, but the current opaque-binding backend cannot
admit a guard that rejects some initial values. -/
theorem guarded_original_not_unrestricted :
    ¬UnrestrictedBinding (Γ := ([] : VCtx Player simpleExpr))
      (name := 0) (who := (0 : Player)) (ty := .bool) guardedOriginal := by
  intro unrestricted
  have hrejected := unrestricted (VEnv.empty simpleExpr) false
  change false = true at hrejected
  contradiction

def bindingCode : BindingCode Player :=
  initialSite.bindingCode source.fresh compilerInitial 0

def conditionalCode (deadline : Nat) : ConditionalCode Player simpleExpr :=
  openingSite.code source.fresh compilerInitial 0 deadline

def applicationPlan : ApplicationPlan plan source.fresh compilerInitial := by
  apply ApplicationPlan.binding
  · intro _ _
    rfl
  apply ApplicationPlan.conditional
  · exact opening_publicly_validatable
  apply ApplicationPlan.ret

def image (deadline : Nat) : ApplicationImage Player simpleExpr :=
  applicationPlan.image (fun _ => deadline)

@[simp] theorem image_lookup_binding (deadline : Nat) :
    (image deadline).lookup bindingCode.node = some (.bind bindingCode) := by
  change (applicationPlan.image (fun _ => deadline)).lookup
    ((ApplicationInstruction.bind bindingCode : ApplicationInstruction Player simpleExpr).address) =
      some (.bind bindingCode)
  apply applicationPlan.image_lookup_of_mem (fun _ => deadline)
  change _ ∈ [_ , _]
  apply List.mem_cons.mpr
  left
  rfl

@[simp] theorem image_lookup_conditional (deadline : Nat) :
    (image deadline).lookup (conditionalCode deadline).endpoint.publicationNode =
      some (.conditional (conditionalCode deadline)) := by
  change (applicationPlan.image (fun _ => deadline)).lookup
    (ApplicationInstruction.conditional (conditionalCode deadline)).address =
      some (.conditional (conditionalCode deadline))
  apply applicationPlan.image_lookup_of_mem (fun _ => deadline)
  change _ ∈ [_ , _]
  apply List.mem_cons.mpr
  right
  apply List.mem_singleton.mpr
  rfl

theorem generated_full_node_coverage (deadline : Nat) :
    (applicationPlan.instructions (fun _ => deadline)).flatMap
        ApplicationInstruction.coveredNodes = List.range 3 := by
  have hcoverage := applicationPlan.coveredNodes_eq_range (fun _ => deadline)
  change _ = List.range 3 at hcoverage
  change List.range 0 ++ _ = List.range 3 at hcoverage
  simpa only [List.range_zero, List.nil_append] using hcoverage

/-- The binding owns its private field; the conditional pair allocates fresh
copy/publication fields instead of reallocating the original source field. -/
theorem generated_full_field_allocation (deadline : Nat) :
    (applicationPlan.instructions (fun _ => deadline)).flatMap
        ApplicationInstruction.allocatedFields = [0, 1, 2] := by
  rw [applicationPlan.allocatedFields_eq_map, generated_full_node_coverage]
  rfl

abbrev compiled := compileCore source.prog source.fresh compilerInitial

def initialMemory : ApplicationImage.Memory Player simpleExpr :=
  ApplicationImage.Memory.initial compiled.graph

def initialNative : ApplicationImage.State Player simpleExpr :=
  ApplicationImage.State.initial initialMemory

def initialExecution (deadline : Nat) : (image deadline).application.State :=
  MessageApplication.State.initial (image deadline).application initialNative

def bindingPayload : ApplicationImage.Payload Player simpleExpr :=
  .binding bindingCode.node (0, 0)

def openingPayload (value : Bool) : ApplicationImage.Payload Player simpleExpr :=
  .conditional (conditionalCode 10).endpoint.publicationNode
    (.opening (0, 0) ⟨.bool, value⟩)

def declinePayload : ApplicationImage.Payload Player simpleExpr :=
  .conditional (conditionalCode 10).endpoint.publicationNode .decline

def expiryPayload : ApplicationImage.Payload Player simpleExpr :=
  .conditional (conditionalCode 10).endpoint.publicationNode .expire

def honestActions (secret : Bool) : List (image 10).application.Action :=
  [.privateCommand 0 (.register 0 ⟨.bool, secret⟩),
    .submit 0 bindingPayload, .include (0, 0),
    .submit 0 (openingPayload secret), .include (0, 1)]

/-- The generated image uses the compiler's three consecutive nodes and the
original source field. These equations are allocation checks, not handwritten
runtime metadata. -/
theorem generated_addresses :
    bindingCode.node = 0 ∧ bindingCode.sourceField = 0 ∧
      (conditionalCode 10).endpoint.choiceNode = 1 ∧
      (conditionalCode 10).endpoint.publicationNode = 2 := by
  decide

@[simp] theorem binding_node : bindingCode.node = 0 := rfl
@[simp] theorem binding_field : bindingCode.sourceField = 0 := rfl
@[simp] theorem conditional_choice_node (deadline : Nat) :
    (conditionalCode deadline).endpoint.choiceNode = 1 := rfl
@[simp] theorem conditional_publication_node (deadline : Nat) :
    (conditionalCode deadline).endpoint.publicationNode = 2 := rfl
@[simp] theorem conditional_requires (deadline : Nat) :
    (conditionalCode deadline).endpoint.requires = [0, 0] := rfl

/-- Actual shared-run execution publishes only the encoded optional result.
The retained original remains absent from public storage. -/
theorem honest_run (secret : Bool) :
    ((image 10).application.run (honestActions secret) (initialExecution 10)).map
      (fun execution =>
        (Store.getAs (L := simpleExpr) execution.application.memory.store 0 .bool,
          Store.getAs (L := simpleExpr) execution.application.memory.store 1 (.option .bool),
          Store.getAs (L := simpleExpr) execution.application.memory.store 2 (.option .bool),
          execution.receipts)) =
      FinDist.pure (none, some (some secret), some (some secret),
        [((0, 0), true), ((0, 1), true)]) := by
  simp only [honestActions, MessageApplication.run_cons, MessageApplication.run_nil,
    MessageApplication.step, FinDist.pure_bind, FinDist.map_pure]
  cases secret <;> rfl

/-- Opaque admission has the same public result whether preparation exists or
not. The private snapshot alone records openability. -/
theorem binding_has_no_validity_oracle (secret : Bool) :
    let registered := initialNative.register 0 0 ⟨.bool, secret⟩
    let absent := initialNative
    let left := (image 10).handle registered ⟨(0, 0), bindingPayload⟩
    let right := (image 10).handle absent ⟨(0, 0), bindingPayload⟩
    left.map (fun state => state.memory) = right.map (fun state => state.memory) ∧
      left.bind (fun state => state.frozen 0) = some ⟨.bool, secret⟩ ∧
      right.bind (fun state => state.frozen 0) = none := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply (image 10).binding_public_effect_eq
      (initialNative.register 0 0 ⟨.bool, secret⟩) initialNative
      (ApplicationImage.State.register_memory initialNative 0 0 ⟨.bool, secret⟩)
      bindingCode.node bindingCode (image_lookup_binding 10) (0, 0) (0, 0)
  · cases secret <;> rfl
  · rfl

/-- Registering after acceptance cannot repair an absent acceptance snapshot;
the opening is published to the ledger with a failed receipt. -/
theorem late_registration_does_not_resurrect (secret : Bool) :
    let actions : List (image 10).application.Action :=
      [.submit 0 bindingPayload, .include (0, 0),
        .privateCommand 0 (.register 0 ⟨.bool, secret⟩),
        .submit 0 (openingPayload secret), .include (0, 1)]
    ((image 10).application.run actions (initialExecution 10)).map
      (fun execution =>
        (execution.application.memory.accepted 0,
          execution.application.frozen 0,
          Store.getAs (L := simpleExpr) execution.application.memory.store 2 (.option .bool),
          execution.receipts)) =
      FinDist.pure (some (0, 0), none, none,
        [((0, 0), true), ((0, 1), false)]) := by
  dsimp only
  simp only [MessageApplication.run_cons, MessageApplication.run_nil,
    MessageApplication.step, FinDist.pure_bind, FinDist.map_pure]
  cases secret <;> rfl

/-- A wrong-typed private preparation remains opaque at binding inclusion. Its
acceptance snapshot cannot validate a later well-typed Boolean opening. -/
theorem wrong_typed_registration_is_unopenable (secret : Bool) :
    let actions : List (image 10).application.Action :=
      [.privateCommand 0 (.register 0 ⟨.option .bool, some secret⟩),
        .submit 0 bindingPayload, .include (0, 0),
        .submit 0 (openingPayload secret), .include (0, 1)]
    ((image 10).application.run actions (initialExecution 10)).map
      (fun execution =>
        (execution.application.memory.accepted 0,
          Store.getAs (L := simpleExpr) execution.application.memory.store 2 (.option .bool),
          execution.receipts)) =
      FinDist.pure (some (0, 0), none,
        [((0, 0), true), ((0, 1), false)]) := by
  dsimp only
  simp only [MessageApplication.run_cons, MessageApplication.run_nil,
    MessageApplication.step, FinDist.pure_bind, FinDist.map_pure]
  cases secret <;> rfl

/-- Decline and overdue permissionless expiry both publish the certificate's
encoded `none`; expiration is enabled only after explicit clock advancement. -/
theorem decline_and_expiry_settle_none :
    let actionPrefix : List (image 10).application.Action :=
      [.submit 0 bindingPayload, .include (0, 0)]
    let decline := actionPrefix ++ [.submit 0 declinePayload, .include (0, 1)]
    let expire := actionPrefix ++ [.environment (.advance 11),
      .submit 1 expiryPayload, .include (1, 0)]
    (((image 10).application.run decline (initialExecution 10)).map
        (fun execution => Store.getAs (L := simpleExpr)
          execution.application.memory.store 2 (.option .bool)),
      ((image 10).application.run expire (initialExecution 10)).map
        (fun execution => Store.getAs (L := simpleExpr)
          execution.application.memory.store 2 (.option .bool))) =
      (FinDist.pure (some none), FinDist.pure (some none)) := by
  dsimp only
  simp only [List.cons_append, List.nil_append,
    MessageApplication.run_cons, MessageApplication.run_nil,
    MessageApplication.step, FinDist.pure_bind, FinDist.map_pure]
  apply Prod.ext
  · rfl
  · simp only [ApplicationImage.application, ApplicationImage.State.advance,
      FinDist.map_pure, FinDist.pure_bind, MessageApplication.run_cons,
      MessageApplication.run_nil, MessageApplication.step]
    rfl

def readyState (secret : Bool) : ApplicationImage.State Player simpleExpr :=
  (initialNative.register 0 0 ⟨.bool, secret⟩).bind bindingCode (0, 0)

/-- Authentication, dynamic typing, binding verification, and payload form are
independent rejection boundaries at the generated conditional instruction. -/
theorem malformed_openings_rejected (secret : Bool) :
    (image 10).handle (readyState secret)
        ⟨(1, 0), .conditional 2 (.opening (0, 0) ⟨.bool, secret⟩)⟩ = none ∧
      (image 10).handle (readyState secret)
        ⟨(0, 0), .conditional 2 (.opening (0, 0) ⟨.option .bool, some secret⟩)⟩ = none ∧
      (image 10).handle (readyState secret)
        ⟨(0, 0), .conditional 2 (.opening (0, 0) ⟨.bool, !secret⟩)⟩ = none ∧
      (image 10).handle (readyState secret)
        ⟨(0, 0), .conditional 2 (.cleartext ⟨.bool, secret⟩)⟩ = none := by
  cases secret <;> decide

/-- Replaying the already accepted opening creates real traffic and a failed
receipt, but cannot execute the completed endpoint again. -/
theorem replay_cannot_rerun (secret : Bool) :
    let actions := honestActions secret ++
      [.replay 0 (0, 1), .include (0, 1)]
    ((image 10).application.run actions (initialExecution 10)).map
      (fun execution =>
        (Store.getAs (L := simpleExpr) execution.application.memory.store 2 (.option .bool),
          execution.receipts)) =
      FinDist.pure (some (some secret),
        [((0, 0), true), ((0, 1), true), ((0, 1), false)]) := by
  dsimp only
  simp only [honestActions, List.cons_append, List.nil_append,
    MessageApplication.run_cons, MessageApplication.run_nil,
    MessageApplication.step, FinDist.pure_bind, FinDist.map_pure]
  cases secret <;> rfl

end VegasTests.ConditionalApplicationImage
