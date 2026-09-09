/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageBindings
import Vegas.Compile.ApplicationImageRegistration

/-! # Binding inclusion with registration provenance

An actual pending canonical binding packet snapshots the owner's already
recorded private registration.  The result below starts at shared message
inclusion, rather than a hand-written application-state update, and then
retains the cache and accepted snapshot across arbitrary policy continuation.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem canonical_binding_handler
    (image : ApplicationImage P L) (state : State P L)
    (address : Nat) (code : BindingCode P)
    (hcode : image.lookup address = some (.bind code))
    (id : MessageId P) (hsender : id.1 = code.owner)
    (haccepted : state.memory.accepted code.sourceField = none)
    (hnotDone : state.memory.done code.node = false)
    (hrequires : code.requires.all state.memory.done = true) :
    image.handle state
        ⟨id, .binding address (code.owner, code.sourceSlot)⟩ =
      some (state.bind code (code.owner, code.sourceSlot)) := by
  rw [image.handle_binding state address code hcode id
    (code.owner, code.sourceSlot)]
  simp [hsender, haccepted, hnotDone, hrequires]

/-- Including an actual pending authenticated canonical binding packet takes
the generated binding branch, preserves global registration consistency, and
installs the already cached value as the accepted frozen snapshot. -/
theorem includePending_binding_cachedSnapshot
    (image : ApplicationImage P L)
    (execution : image.application.PolicyExecution)
    (address : Nat) (code : BindingCode P)
    (hcode : image.lookup address = some (.bind code))
    (id : MessageId P)
    (value : TypedValue L)
    (hconsistent : image.RegistrationConsistent execution)
    (hcache : image.registrationCache code.sourceSlot
      (execution.principalHistory code.owner) = some value)
    (hlookup : execution.native.pool.lookup id =
      some ⟨id, .binding address (code.owner, code.sourceSlot)⟩)
    (hsender : id.1 = code.owner)
    (haccepted : execution.native.application.memory.accepted
      code.sourceField = none)
    (hnotDone : execution.native.application.memory.done code.node = false)
    (hrequires : code.requires.all
      execution.native.application.memory.done = true) :
    let included := image.application.includePending execution.native id
    let includedExecution : image.application.PolicyExecution :=
      { execution with native := included }
    included.application = execution.native.application.bind code
        (code.owner, code.sourceSlot) ∧
      image.RegistrationConsistent includedExecution ∧
      image.registrationCache code.sourceSlot
          (includedExecution.principalHistory code.owner) = some value ∧
      AcceptedSnapshot code.sourceField (code.owner, code.sourceSlot)
        (some value) included.application := by
  dsimp only
  have hhandler := canonical_binding_handler image execution.native.application
    address code hcode id hsender haccepted hnotDone hrequires
  have hincluded := image.application.includePending_accept execution.native id
    ⟨id, .binding address (code.owner, code.sourceSlot)⟩
    (execution.native.application.bind code (code.owner, code.sourceSlot))
    hlookup hhandler
  have hprepared : execution.native.application.prepared.lookup
      (code.owner, code.sourceSlot) = some value :=
    (hconsistent code.owner code.sourceSlot).symm.trans hcache
  constructor
  · rw [hincluded]
  constructor
  · intro who slot
    rw [hincluded]
    simpa only [State.bind] using hconsistent who slot
  constructor
  · exact hcache
  · rw [hincluded]
    constructor <;> simp [State.bind, hprepared]

/-- The actual environment-policy inclusion step records its observation and
native action while installing the cached accepted snapshot. -/
theorem environmentPolicyStep_include_binding_cachedSnapshot
    (image : ApplicationImage P L)
    (execution : image.application.PolicyExecution)
    (address : Nat) (code : BindingCode P)
    (hcode : image.lookup address = some (.bind code))
    (id : MessageId P)
    (value : TypedValue L)
    (hconsistent : image.RegistrationConsistent execution)
    (hcache : image.registrationCache code.sourceSlot
      (execution.principalHistory code.owner) = some value)
    (hlookup : execution.native.pool.lookup id =
      some ⟨id, .binding address (code.owner, code.sourceSlot)⟩)
    (hsender : id.1 = code.owner)
    (haccepted : execution.native.application.memory.accepted
      code.sourceField = none)
    (hnotDone : execution.native.application.memory.done code.node = false)
    (hrequires : code.requires.all
      execution.native.application.memory.done = true)
    (included : image.application.PolicyExecution)
    (hincluded : included ∈
      (image.application.environmentPolicyStep execution (.include id)).support) :
    included.native.application = execution.native.application.bind code
        (code.owner, code.sourceSlot) ∧
      image.RegistrationConsistent included ∧
      image.registrationCache code.sourceSlot
          (included.principalHistory code.owner) = some value ∧
      AcceptedSnapshot code.sourceField (code.owner, code.sourceSlot)
          (some value) included.native.application ∧
      included.environmentHistory = execution.environmentHistory ++
        [⟨State.environmentView image.application execution.native, .include id⟩] ∧
      included.nativeTrace = execution.nativeTrace ++ [.include id] := by
  simp only [MessageApplication.environmentPolicyStep,
    EnvironmentPolicyCommand.toAction, MessageApplication.advance,
    MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hincluded
  subst included
  have hstate := image.includePending_binding_cachedSnapshot execution address
    code hcode id value hconsistent hcache hlookup hsender haccepted hnotDone
    hrequires
  exact ⟨hstate.1, hstate.2.1, hstate.2.2.1, hstate.2.2.2, rfl, rfl⟩

/-- After an actual recorded environment-policy binding inclusion, arbitrary
later policies preserve the registration invariant, the owner's first cached
value, and the exact accepted snapshot. No progress premise is used. -/
theorem runPolicies_binding_cachedSnapshot
    (image : ApplicationImage P L)
    (execution included : image.application.PolicyExecution)
    (address : Nat) (code : BindingCode P)
    (hcode : image.lookup address = some (.bind code))
    (id : MessageId P)
    (value : TypedValue L)
    (hconsistent : image.RegistrationConsistent execution)
    (hcache : image.registrationCache code.sourceSlot
      (execution.principalHistory code.owner) = some value)
    (hlookup : execution.native.pool.lookup id =
      some ⟨id, .binding address (code.owner, code.sourceSlot)⟩)
    (hsender : id.1 = code.owner)
    (haccepted : execution.native.application.memory.accepted
      code.sourceField = none)
    (hnotDone : execution.native.application.memory.done code.node = false)
    (hrequires : code.requires.all
      execution.native.application.memory.done = true)
    (hincluded : included ∈
      (image.application.environmentPolicyStep execution (.include id)).support)
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (next : image.application.PolicyExecution)
    (hnext : next ∈ (image.application.runPolicies players environment schedule
      included).support) :
    image.RegistrationConsistent next ∧
      image.registrationCache code.sourceSlot
          (next.principalHistory code.owner) = some value ∧
      AcceptedSnapshot code.sourceField (code.owner, code.sourceSlot)
        (some value) next.native.application := by
  have hbinding := image.environmentPolicyStep_include_binding_cachedSnapshot
    execution address code hcode id value hconsistent hcache hlookup hsender
    haccepted hnotDone hrequires included hincluded
  rcases hbinding with
    ⟨_, hincludedConsistent, hincludedCache, hincludedSnapshot, _, _⟩
  constructor
  · exact image.runPolicies_registrationConsistent players environment schedule
      included next hincludedConsistent hnext
  constructor
  · unfold registrationCache at hincludedCache ⊢
    exact ChoiceEncoding.runPolicies_cachedValue_of_some image.application
      ((registrationEncoding code.sourceSlot).privateCommand image.application)
      code.owner players environment schedule included next value
      hincludedCache hnext
  · exact image.runPolicies_acceptedSnapshot code.sourceField
      (code.owner, code.sourceSlot) (some value) players environment schedule
      included next hincludedSnapshot hnext

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.includePending_binding_cachedSnapshot' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.includePending_binding_cachedSnapshot

/-- info:
'Vegas.ApplicationImage.environmentPolicyStep_include_binding_cachedSnapshot' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.environmentPolicyStep_include_binding_cachedSnapshot

/-- info: 'Vegas.ApplicationImage.runPolicies_binding_cachedSnapshot' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.runPolicies_binding_cachedSnapshot
