/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageReadout
import Vegas.Compile.ConditionalImageController
import VegasTests.GeneratedPersistentDisclosure
import Mathlib.Tactic.IntervalCases

/-! # Owner-local controller for a repeated conditional publication

The generated second controller reads every source-visible binding, including
the resolved first copy, from public memory and the original registration
cache. The local laws quantify arbitrary histories with the stated cache
contents; they do not assert that every such history is a reachable execution.
Whole-program controller dispatch and service composition are separate.
-/

noncomputable section

namespace VegasTests.GeneratedPersistentDisclosureController

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure
open VegasTests.GeneratedPersistentDisclosure

abbrev SecondDecision :=
  (visible : Env simpleExpr.Val
    (eraseVCtx (viewVCtx secondSite.choice.owner secondSite.choice.context))) →
      FinDist { value : simpleExpr.Val secondSite.choice.ty //
        evalGuard secondSite.choice.guard value visible = true }

def secondReadout? := image.ownerReadout? (0 : TestPlayer)
  (secondSite.choice.compiledGuard source.fresh.2.2.2.2.2.2.2.2 beforeSecond).choiceReads

def secondController (policy : SecondDecision) :=
  secondSite.imageController source.fresh.2.2.2.2.2.2.2.2 beforeSecond 0 10 image
    secondReadout? policy (fun _ _ => false)

/-- The slot/endpoint distinction is operational: private preparation uses
slot zero, whereas the later public choice is cached at endpoint nine. -/
def secondEncoding :=
  (secondSite.choiceEncoding source.fresh.2.2.2.2.2.2.2.2 beforeSecond 0 10
    (ApplicationImage.conditionalTransport secondSite.specification.secretTy)).submission
      image.application

/-- The first publication's traffic cannot occupy the second endpoint's cache,
even though both openings name the same original binding. -/
theorem first_opening_not_second_choice (secret : Bool) :
    secondEncoding.decode
      (.submit (.conditional 5 (.opening (0, 0) ⟨.bool, secret⟩))) = none := rfl

private def publicFields (signal : Bool) (first : Option Bool) : Store simpleExpr
  | 1 | 2 | 6 | 7 => some ⟨.bool, false⟩
  | 3 => some ⟨.bool, signal⟩
  | 4 | 5 => some ⟨.option .bool, first⟩
  | _ => none

private theorem stored_of_getAs {store : Store simpleExpr} {field : Nat}
    {ty : BaseTy} {value : simpleExpr.Val ty}
    (hget : Store.getAs store field ty = some value) :
    store field = some ⟨ty, value⟩ := by
  cases hstored : store field with
  | none => simp [Store.getAs, hstored] at hget
  | some typed =>
      exact congrArg some (typed.eq_mk_of_as?_eq_some ty value
        (by simpa only [Store.getAs, hstored] using hget))

private theorem readStore_view_agrees
    (history : List image.application.PlayerEntry)
    (memory : ApplicationImage.Memory TestPlayer simpleExpr)
    (secret signal : Bool) (first : Option Bool)
    (hcache : image.registrationCache 0 history = some ⟨.bool, secret⟩)
    (haccepted : memory.accepted 0 = some (0, 0))
    (hfields : ∀ field : Fin 8, memory.store field = publicFields signal first field) :
    beforeSecond.ViewAgrees 0 (image.ownerReadStore 0 history memory)
      (secondEnv secret signal first false) := by
  have hget (field : Nat) (hlt : field < 8) : image.ownerReadStore 0 history memory field =
      (publicFields signal first).set 0 ⟨.bool, secret⟩ field := by
    unfold ApplicationImage.ownerReadStore
    rw [hfields ⟨field, hlt⟩]
    interval_cases field <;>
      simp [publicFields, haccepted, hcache, Store.set]
  have h0 := hget 0 (by decide)
  have h1 := hget 1 (by decide)
  have h2 := hget 2 (by decide)
  have h3 := hget 3 (by decide)
  have h4 := hget 4 (by decide)
  have h5 := hget 5 (by decide)
  have h7 := hget 7 (by decide)
  intro name bindTy binding
  rcases binding with _ | binding
  · change Store.getAs (image.ownerReadStore 0 history memory) 7 .bool = some false
    simp [Store.getAs, h7, Store.set, publicFields, TypedValue.as?]
  rcases binding with _ | binding
  · change Store.getAs (image.ownerReadStore 0 history memory) 5 (.option .bool) = some first
    simp [Store.getAs, h5, Store.set, publicFields, TypedValue.as?]
  rcases binding with _ | binding
  · change Store.getAs (image.ownerReadStore 0 history memory) 4 (.option .bool) = some first
    simp [Store.getAs, h4, Store.set, publicFields, TypedValue.as?]
  rcases binding with _ | binding
  · change Store.getAs (image.ownerReadStore 0 history memory) 3 .bool = some signal
    simp [Store.getAs, h3, Store.set, publicFields, TypedValue.as?]
  rcases binding with _ | binding
  · change Store.getAs (image.ownerReadStore 0 history memory) 2 .bool = some false
    simp [Store.getAs, h2, Store.set, publicFields, TypedValue.as?]
  rcases binding with _ | binding
  · change Store.getAs (image.ownerReadStore 0 history memory) 1 .bool = some false
    simp [Store.getAs, h1, Store.set, publicFields, TypedValue.as?]
  rcases binding with _ | binding
  · change Store.getAs (image.ownerReadStore 0 history memory) 0 .bool = some secret
    simp [Store.getAs, h0, Store.set, TypedValue.as?]
  cases binding

private theorem source_law
    (policy : SecondDecision) (history : List image.application.PlayerEntry)
    (native : image.application.State) (secret signal : Bool) (first : Option Bool)
    (hcache : image.registrationCache 0 history = some ⟨.bool, secret⟩)
    (hsecond : secondEncoding.cachedValue image.application history = none)
    (haccepted : native.application.memory.accepted 0 = some (0, 0))
    (hfields : ∀ field : Fin 8,
      native.application.memory.store field = publicFields signal first field)
    (hready : secondCode.endpoint.ready
      (native.application.memory.accepted 0) native.application.memory.done = true)
    (hresolved : native.application.memory.done 9 = false) :
    (secondController policy).policy image.application history
        (MessageApplication.State.observe image.application native 0) =
      (policy (((secondEnv secret signal first false).toView 0).eraseEnv)).map
        fun choice => .submit
          ((ApplicationImage.conditionalTransport secondSite.specification.secretTy).encode
            (9, secondCode.endpoint.requestPayload
              (secondSite.specification.encoding choice.1))) := by
  let store := image.ownerReadStore 0 history native.application.memory
  have hagrees : beforeSecond.ViewAgrees 0 store (secondEnv secret signal first false) :=
    readStore_view_agrees history native.application.memory secret signal first
      hcache haccepted hfields
  have available : ∀ ref, ref ∈ visibleFieldRefs beforeSecond 0 →
      ∃ value, Store.getAs store ref.field ref.ty = some value := by
    apply fieldRefsOfCtx_store_available
    intro name bindTy binding
    exact ⟨_, hagrees binding⟩
  let reads := ReadEnv.ofStore store (visibleFieldRefs beforeSecond 0) available
  have hreads : ReadEnv.ofStore? store (visibleFieldRefs beforeSecond 0) = some reads := by
    unfold ReadEnv.ofStore?
    rw [dif_pos available]
  have hreadout : secondReadout? history
      (MessageApplication.State.observe image.application native 0) = some reads :=
    ReadEnv.ofStoreExec?_eq_some_of_ofStore?_eq_some hreads
  exact secondSite.imageController_first_submission_source_law
    source.fresh.2.2.2.2.2.2.2.2 beforeSecond 0 10 image secondReadout?
    policy (fun _ _ => false) history _ store (secondEnv secret signal first false) reads
    hresolved hsecond hready hreadout hagrees hreads

/-- At the generated execution's opened checkpoint, the next submission has
exactly the arbitrary randomized source decision law. The only history
premises are the retained original registration and an uncached second site. -/
theorem after_opening_first_submission_source_law
    (secret signal : Bool) (policy : SecondDecision)
    (history : List image.application.PlayerEntry)
    (hcache : image.registrationCache 0 history = some ⟨.bool, secret⟩)
    (hsecond : secondEncoding.cachedValue image.application history = none) :
    (secondController policy).policy image.application history
        (MessageApplication.State.observe image.application
          (afterFirstOpening secret signal) 0) =
      (policy (((secondEnv secret signal (some secret) false).toView 0).eraseEnv)).map
        fun choice => .submit
          ((ApplicationImage.conditionalTransport secondSite.specification.secretTy).encode
            (9, secondCode.endpoint.requestPayload
              (secondSite.specification.encoding choice.1))) := by
  apply source_law policy history _ secret signal (some secret) hcache hsecond
  · cases secret <;> cases signal <;> decide +kernel
  · intro field
    fin_cases field
    · apply Option.isNone_iff_eq_none.mp
      cases secret <;> cases signal <;> decide +kernel
    all_goals apply stored_of_getAs; cases secret <;> cases signal <;> decide +kernel
  · cases secret <;> cases signal <;> decide +kernel
  · cases secret <;> cases signal <;> decide +kernel

/-- A publicly resolved decline, not a cached attempted opening, supplies the
earlier choice to the second source kernel. This holds for all histories with
the two stated cache contents. -/
theorem after_refusal_first_submission_source_law
    (secret signal : Bool) (policy : SecondDecision)
    (history : List image.application.PlayerEntry)
    (hcache : image.registrationCache 0 history = some ⟨.bool, secret⟩)
    (hsecond : secondEncoding.cachedValue image.application history = none) :
    (secondController policy).policy image.application history
        (MessageApplication.State.observe image.application
          (afterFirstRefusal secret signal) 0) =
      (policy (((secondEnv secret signal none false).toView 0).eraseEnv)).map
        fun choice => .submit
          ((ApplicationImage.conditionalTransport secondSite.specification.secretTy).encode
            (9, secondCode.endpoint.requestPayload
              (secondSite.specification.encoding choice.1))) := by
  apply source_law policy history _ secret signal none hcache hsecond
  · cases secret <;> cases signal <;> decide +kernel
  · intro field
    fin_cases field
    · apply Option.isNone_iff_eq_none.mp
      cases secret <;> cases signal <;> decide +kernel
    all_goals apply stored_of_getAs; cases secret <;> cases signal <;> decide +kernel
  · cases secret <;> cases signal <;> decide +kernel
  · cases secret <;> cases signal <;> decide +kernel

/-- Once sampled at endpoint nine, the second decision is never sampled again,
regardless of later polling, public state, or other traffic. -/
theorem secondController_recorded
    (policy : SecondDecision) (history : List image.application.PlayerEntry)
    (view : image.application.View) (value : Option Bool)
    (hcache : secondEncoding.cachedValue image.application history = some value) :
    (secondController policy).policy image.application history view = FinDist.pure .wait := by
  cases hresolved : (secondController policy).resolved view with
  | true => exact (secondController policy).policy_of_resolved _ _ _ hresolved
  | false =>
      rw [(secondController policy).policy_of_cached _ _ _ value hresolved hcache]
      simp [secondController, ConditionalPublicationSite.imageController,
        ConditionalPublicationSite.controller]

/-- The source guard forces decline after the first site's decline. Every
compiled source kernel therefore emits decline, independently of its other
preferences or randomization. -/
theorem after_refusal_only_decline
    (secret signal : Bool) (policy : SecondDecision)
    (history : List image.application.PlayerEntry)
    (hcache : image.registrationCache 0 history = some ⟨.bool, secret⟩)
    (hsecond : secondEncoding.cachedValue image.application history = none) :
    (secondController policy).policy image.application history
        (MessageApplication.State.observe image.application
          (afterFirstRefusal secret signal) 0) =
      FinDist.pure (.submit (.conditional 9 .decline)) := by
  rw [after_refusal_first_submission_source_law secret signal policy history hcache hsecond]
  let decision := policy (((secondEnv secret signal none false).toView 0).eraseEnv)
  change decision.map _ = _
  trans decision.map (fun _ => .submit (.conditional 9 .decline))
  · apply congrArg (fun choose => decision.map choose)
    funext chosen
    have hnone : chosen.1 = none :=
      refusal_forces_later_refusal secret signal false chosen.1 chosen.2
    apply congrArg PlayerCommand.submit
    rw [hnone]
    rfl
  · exact FinDist.map_const _ _

end VegasTests.GeneratedPersistentDisclosureController

/-- info: 'VegasTests.GeneratedPersistentDisclosureController.after_opening_first_submission_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.GeneratedPersistentDisclosureController.after_opening_first_submission_source_law

/-- info: 'VegasTests.GeneratedPersistentDisclosureController.after_refusal_first_submission_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.GeneratedPersistentDisclosureController.after_refusal_first_submission_source_law
