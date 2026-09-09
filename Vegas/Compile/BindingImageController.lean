/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageReadout
import Vegas.Compile.ConditionalImage
import Interaction.ChoiceControllerHistory

/-! # Source-generated registration and binding policies

A source binding is implemented by two owner invocations: a private
registration, then a public handle submission. Both phases use the shared
sample-once controller. The registration cache stores the first raw typed
package; a wrong-typed earlier registration prevents a new sample rather than
being skipped. Source environments are proof data, never policy inputs.

The policy emits one binding packet and then waits for its inclusion. Delivery,
inclusion, and deadline protection are separate service assumptions. Binding
admission does not validate the source guard: application-plan eligibility
still requires an unrestricted original binding for arbitrary deviations.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem ChoiceController.supported_wait_or_safe
    {Principal Value Input : Type} {app : MessageApplication Principal}
    (controller : ChoiceController app Value Input)
    (safe : app.PlayerCommand → Prop)
    (history : List app.PlayerEntry) (view : app.View)
    (command : app.PlayerCommand)
    (hretry : controller.retry history view = false)
    (hkernel : ∀ input value, value ∈ (controller.kernel input).support →
      safe (controller.codec.encode value))
    (hcommand : command ∈ (controller.policy app history view).support) :
    command = .wait ∨ safe command := by
  unfold ChoiceController.policy at hcommand
  split at hcommand
  · exact Or.inl (FinDist.mem_support_pure.mp hcommand)
  · split at hcommand
    · simp only [hretry, Bool.and_false, Bool.false_eq_true, if_false,
        FinDist.mem_support_pure] at hcommand
      exact Or.inl hcommand
    · split at hcommand
      · split at hcommand
        · rw [FinDist.support_map] at hcommand
          obtain ⟨value, hvalue, rfl⟩ := hcommand
          exact Or.inr (hkernel _ value hvalue)
        · exact Or.inl (FinDist.mem_support_pure.mp hcommand)
      · exact Or.inl (FinDist.mem_support_pure.mp hcommand)

namespace BindingCode

/-- The unique opaque binding packet for this instruction. -/
def encoding (code : BindingCode P) : ChoiceEncoding Unit (ApplicationImage.Payload P L) where
  encode _ := .binding code.node (code.owner, code.sourceSlot)
  decode
    | .binding address handle =>
        if address = code.node ∧ handle = (code.owner, code.sourceSlot) then some () else none
    | _ => none
  decode_encode _ := by simp
  decode_sound wire value hdecode := by
    cases value
    cases wire with
    | binding address handle =>
        simp only at hdecode
        split at hdecode
        · rename_i hpacket
          rcases hpacket with ⟨rfl, rfl⟩
          rfl
        · cases hdecode
    | _ => cases hdecode

/-- A binding is resolved when its field has an accepted handle or its node
is already complete. Neither phase may act after resolution. -/
def resolved (code : BindingCode P) (memory : ApplicationImage.Memory P L) : Bool :=
  (memory.accepted code.sourceField).isSome || memory.done code.node

/-- Submit the handle only after this owner's history records a correctly
typed private registration. The value itself is absent from the packet. -/
def submissionController (code : BindingCode P) (image : ApplicationImage P L) (ty : L.Ty) :
    ChoiceController image.application Unit Unit where
  codec := code.encoding.submission image.application
  ready view := code.requires.all view.application.done
  resolved view := code.resolved view.application
  readout? history _ :=
    ((image.registrationCache code.sourceSlot history).bind (fun value => value.as? ty)).map
      (fun _ => ())
  kernel _ := FinDist.pure ()
  retry _ _ := false

/-- Once a registration is recorded, a ready unsubmitted binding emits its
canonical handle. No source resampling or readout reconstruction occurs here. -/
theorem submissionController_registered
    (code : BindingCode P) (image : ApplicationImage P L) (ty : L.Ty)
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (value : L.Val ty)
    (hregistered : image.registrationCache code.sourceSlot history = some ⟨ty, value⟩)
    (hresolved : code.resolved view.application = false)
    (hready : code.requires.all view.application.done = true)
    (hsubmitted : (code.encoding.submission image.application).cachedValue
      image.application history = none) :
    (code.submissionController image ty).policy image.application history view =
      FinDist.pure (.submit (.binding code.node (code.owner, code.sourceSlot))) := by
  rw [(code.submissionController image ty).policy_of_uncached_ready
    image.application history view () hresolved hsubmitted hready]
  · change (FinDist.pure ()).map _ = _
    rw [FinDist.map_pure]
    rfl
  · simp [submissionController, hregistered, TypedValue.as?]

end BindingCode

namespace SourceDecisionSite

variable {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
variable {name : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}

/-- The source field allocated to a decision, also used as its private service
slot by the structural application compiler. -/
def compiledField (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (build : BuildState P L Γ) : Nat :=
  (decisionSiteState site fresh build).nextField

/-- Source-field allocation and binding-handler allocation coincide. -/
theorem bindingCode_sourceField (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (build : BuildState P L Γ) (slot : Nat) :
    (site.bindingCode fresh build slot).sourceField = site.compiledField fresh build := by
  simp [bindingCode, compiledNode, compiledField, Graph.nodeTarget, BuildResult.graph,
    compileCore_initialFields, BuildState.nextField, BuildState.nextNode,
    decisionSiteState_initialFields]

/-- Sample the source kernel into the first raw registration package at this
slot. All source-visible reads come from the observation-local image loader. -/
def registrationController (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (build : BuildState P L Γ)
    (image : ApplicationImage P L)
    (sourcePolicy : (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
      FinDist { value : L.Val ty // evalGuard guard value visible = true }) :
    ChoiceController image.application (TypedValue L)
      (ReadEnv L (eventGuardOf (decisionSiteState site fresh build) who guard).choiceReads) where
  codec := (ApplicationImage.registrationEncoding
    (site.compiledField fresh build)).privateCommand image.application
  ready view := (site.bindingCode fresh build
    (site.compiledField fresh build)).requires.all view.application.done
  resolved view := (site.bindingCode fresh build
    (site.compiledField fresh build)).resolved view.application
  readout? := image.ownerReadout? who
    (eventGuardOf (decisionSiteState site fresh build) who guard).choiceReads
  kernel reads :=
    ((compileSourceDecision (decisionSiteState site fresh build) who guard sourcePolicy reads).map
      Subtype.val).map (TypedValue.mk ty)
  retry _ _ := false

/-- Generated two-phase binding policy. Any prior registration selects the
submission phase, including a wrong-typed first package, which then waits.
It never replaces or skips that first registration. -/
def bindingPolicy (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (build : BuildState P L Γ)
    (image : ApplicationImage P L)
    (sourcePolicy : (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
      FinDist { value : L.Val ty // evalGuard guard value visible = true }) :
    image.application.PlayerPolicy := fun history view =>
  match image.registrationCache (site.compiledField fresh build) history with
  | none => (site.registrationController fresh build image sourcePolicy).policy
      image.application history view
  | some _ => ((site.bindingCode fresh build
      (site.compiledField fresh build)).submissionController image ty).policy
        image.application history view

/-- The first phase has exactly the source kernel's law and emits only an
authenticated private registration, not a public cleartext choice. -/
theorem bindingPolicy_first_registration_source_law
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (build : BuildState P L Γ)
    (image : ApplicationImage P L)
    (sourcePolicy : (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
      FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (env : VEnv L Δ)
    (reads : ReadEnv L (eventGuardOf (decisionSiteState site fresh build) who guard).choiceReads)
    (hresolved : (site.bindingCode fresh build
      (site.compiledField fresh build)).resolved view.application = false)
    (hready : (site.bindingCode fresh build
      (site.compiledField fresh build)).requires.all view.application.done = true)
    (hcache : image.registrationCache (site.compiledField fresh build) history = none)
    (hreadout : image.ownerReadout? who
      (eventGuardOf (decisionSiteState site fresh build) who guard).choiceReads
        history view = some reads)
    (hview : viewEnvOfReadEnv (decisionSiteState site fresh build) who reads =
      (env.toView who).eraseEnv) :
    site.bindingPolicy fresh build image sourcePolicy history view =
      (sourcePolicy ((env.toView who).eraseEnv)).map fun chosen =>
        .privateCommand (.register (site.compiledField fresh build) ⟨ty, chosen.1⟩) := by
  simp only [bindingPolicy, hcache]
  rw [(site.registrationController fresh build image sourcePolicy).policy_of_uncached_ready
    image.application history view reads hresolved hcache hready hreadout]
  simp only [registrationController, compileSourceDecision, FinDist.map_comp,
    Function.comp_def, ChoiceEncoding.privateCommand, ApplicationImage.registrationEncoding]
  rw [hview]

/-- The second phase sends the same canonical handle for every correctly typed
cached value. It does not consult the source kernel again. -/
theorem bindingPolicy_registered
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (build : BuildState P L Γ)
    (image : ApplicationImage P L)
    (sourcePolicy : (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
      FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (value : L.Val ty)
    (hregistered : image.registrationCache (site.compiledField fresh build) history =
      some ⟨ty, value⟩)
    (hresolved : (site.bindingCode fresh build
      (site.compiledField fresh build)).resolved view.application = false)
    (hready : (site.bindingCode fresh build
      (site.compiledField fresh build)).requires.all view.application.done = true)
    (hsubmitted : ChoiceEncoding.cachedValue image.application
      ((site.bindingCode fresh build (site.compiledField fresh build)).encoding.submission
        image.application) history = none) :
    site.bindingPolicy fresh build image sourcePolicy history view =
      FinDist.pure (.submit (.binding
        (site.bindingCode fresh build (site.compiledField fresh build)).node
        (who, site.compiledField fresh build))) := by
  simp only [bindingPolicy, hregistered]
  exact (site.bindingCode fresh build
    (site.compiledField fresh build)).submissionController_registered image ty history view
      value hregistered hresolved hready hsubmitted

/-- Every command emitted by the generated two-phase policy is either a wait,
a correctly typed private registration at the compiler-derived slot, or the
single canonical opaque binding packet. In particular it never emits public
cleartext choice or conditional-publication traffic. -/
theorem bindingPolicy_supported_command
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (build : BuildState P L Γ)
    (image : ApplicationImage P L)
    (sourcePolicy : (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
      FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (history : List image.application.PlayerEntry)
    (view : image.application.View) (command : image.application.PlayerCommand)
    (hcommand : command ∈
      (site.bindingPolicy fresh build image sourcePolicy history view).support) :
    command = .wait ∨
      (∃ value : L.Val ty, command = .privateCommand (.register
        (site.compiledField fresh build) ⟨ty, value⟩)) ∨
      command = .submit (.binding
        (site.bindingCode fresh build (site.compiledField fresh build)).node
        (who, site.compiledField fresh build)) := by
  cases hcache : image.registrationCache (site.compiledField fresh build) history with
  | none =>
      have hsafe := ChoiceController.supported_wait_or_safe
        (site.registrationController fresh build image sourcePolicy)
        (fun command => ∃ value : L.Val ty, command = .privateCommand (.register
          (site.compiledField fresh build) ⟨ty, value⟩))
        history view command rfl (by
          intro reads typed htyped
          simp only [registrationController, FinDist.support_map, Set.mem_image] at htyped
          obtain ⟨value, hvalue, rfl⟩ := htyped
          obtain ⟨chosen, _, rfl⟩ := hvalue
          exact ⟨chosen.1, rfl⟩) (by
          simpa only [bindingPolicy, hcache] using hcommand)
      rcases hsafe with hwait | hregister
      · exact Or.inl hwait
      · exact Or.inr (Or.inl hregister)
  | some registered =>
      have hsafe := ChoiceController.supported_wait_or_safe
        ((site.bindingCode fresh build
          (site.compiledField fresh build)).submissionController image ty)
        (fun command => command = .submit (.binding
          (site.bindingCode fresh build (site.compiledField fresh build)).node
          (who, site.compiledField fresh build)))
        history view command rfl (by
          intro input value hvalue
          have hunit : value = () := Subsingleton.elim _ _
          subst value
          rfl) (by
          simpa only [bindingPolicy, hcache] using hcommand)
      rcases hsafe with hwait | hbinding
      · exact Or.inl hwait
      · exact Or.inr (Or.inr hbinding)

/-- A wrong-typed first raw registration is sticky policy memory. The binding
phase cannot decode it and waits rather than drawing another source value. -/
theorem bindingPolicy_wrong_typed_registration_waits
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (build : BuildState P L Γ)
    (image : ApplicationImage P L)
    (sourcePolicy : (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
      FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (history : List image.application.PlayerEntry)
    (view : image.application.View) (typed : TypedValue L)
    (hcache : image.registrationCache (site.compiledField fresh build) history =
      some typed)
    (hwrong : typed.as? ty = none) :
    site.bindingPolicy fresh build image sourcePolicy history view =
      FinDist.pure .wait := by
  simp only [bindingPolicy, hcache]
  have hslot : (site.bindingCode fresh build
      (site.compiledField fresh build)).sourceSlot =
        site.compiledField fresh build := rfl
  let controller := (site.bindingCode fresh build
    (site.compiledField fresh build)).submissionController image ty
  by_cases hresolved : controller.resolved view = true
  · exact controller.policy_of_resolved image.application history view hresolved
  · have hresolved' : controller.resolved view = false := Bool.eq_false_of_not_eq_true hresolved
    cases hsubmitted : controller.codec.cachedValue image.application history with
    | some submitted =>
        rw [controller.policy_of_cached image.application history view submitted
          hresolved' hsubmitted]
        simp [controller, BindingCode.submissionController]
    | none =>
        have hreadout : controller.readout? history view = none := by
          simp [controller, BindingCode.submissionController, hslot, hcache, hwrong]
        cases hready : controller.ready view with
        | false =>
            exact controller.policy_of_uncached_not_ready image.application history view
              hresolved' hsubmitted hready
        | true =>
            exact controller.policy_of_uncached_no_readout image.application history view
              hresolved' hsubmitted hready hreadout

/-- Once history contains both a registration and the exact binding packet,
the generated policy waits. The explicit registration premise excludes
incompatible histories that could not arise from this two-phase policy. -/
theorem bindingPolicy_submitted_waits
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (build : BuildState P L Γ)
    (image : ApplicationImage P L)
    (sourcePolicy : (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
      FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (history : List image.application.PlayerEntry)
    (view : image.application.View) (registered : TypedValue L)
    (hregistered : image.registrationCache (site.compiledField fresh build) history =
      some registered)
    (hsubmitted : ChoiceEncoding.cachedValue image.application
      ((site.bindingCode fresh build (site.compiledField fresh build)).encoding.submission
        image.application) history = some ()) :
    site.bindingPolicy fresh build image sourcePolicy history view =
      FinDist.pure .wait := by
  simp [bindingPolicy, hregistered, ChoiceController.policy,
    BindingCode.submissionController, hsubmitted]

end SourceDecisionSite

end Vegas

/-- info: 'Vegas.SourceDecisionSite.bindingPolicy_first_registration_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.bindingPolicy_first_registration_source_law

/-- info: 'Vegas.SourceDecisionSite.bindingPolicy_supported_command' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.bindingPolicy_supported_command
