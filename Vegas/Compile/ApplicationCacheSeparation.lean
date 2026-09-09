/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicyFreshness
import Vegas.Compile.ApplicationPlanAllocation

/-! # Separation of generated player-command caches

Commands emitted for the current source instruction cannot populate a later
instruction's sample-once cache.  Public submissions are separated by their
generated instruction address.  Private registrations need the additional
compiler fact that two binding instructions use distinct allocated slots.

A conditional instruction deliberately has no registration cache: reuse of an
earlier binding's source slot is therefore allowed.  Its cache recognizes only
voluntary, endpoint-addressed submissions and rejects expiration traffic.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace ApplicationInstruction

private inductive CacheTag where
  | registration (slot : Nat)
  | submission (address : Nat)
  deriving DecidableEq

private def commandCacheTag? (image : ApplicationImage P L) :
    image.application.PlayerCommand → Option CacheTag
  | .privateCommand (.register slot _) => some (.registration slot)
  | .submit (.choice address _) => some (.submission address)
  | .submit (.binding address _) => some (.submission address)
  | .submit (.conditional address _) => some (.submission address)
  | .submit (.malformed _) | .replay _ | .wait => none

private theorem tag_of_decode_ne_none
    {Value : Type} (image : ApplicationImage P L)
    (encoding : ChoiceEncoding Value image.application.PlayerCommand)
    (tag : CacheTag)
    (htag : ∀ value, commandCacheTag? image (encoding.encode value) = some tag)
    (command : image.application.PlayerCommand)
    (hdecode : encoding.decode command ≠ none) :
    commandCacheTag? image command = some tag := by
  cases hdecoded : encoding.decode command with
  | none => exact False.elim (hdecode hdecoded)
  | some value =>
      rw [encoding.decode_sound command value hdecoded]
      exact htag value

private theorem decode_eq_none_of_tag_ne
    {Value : Type} (image : ApplicationImage P L)
    (encoding : ChoiceEncoding Value image.application.PlayerCommand)
    (tag actual : CacheTag)
    (htag : ∀ value, commandCacheTag? image (encoding.encode value) = some tag)
    (command : image.application.PlayerCommand)
    (hactual : commandCacheTag? image command = some actual)
    (hne : actual ≠ tag) :
    encoding.decode command = none := by
  cases hdecoded : encoding.decode command with
  | none => rfl
  | some value =>
      have htarget := tag_of_decode_ne_none image encoding tag htag command (by
        intro hnone
        rw [hnone] at hdecoded
        contradiction)
      rw [hactual] at htarget
      exact False.elim (hne (Option.some.inj htarget))

private theorem registrationEncoding_tag (image : ApplicationImage P L)
    (slot : Nat) (value : TypedValue L) :
    commandCacheTag? image
        (((ApplicationImage.registrationEncoding slot).privateCommand
          image.application).encode value) =
      some (.registration slot) := rfl

private theorem bindingEncoding_tag (image : ApplicationImage P L)
    (code : BindingCode P) (value : Unit) :
    commandCacheTag? image
        ((code.encoding.submission image.application).encode value) =
      some (.submission code.node) := by
  cases value
  rfl

private theorem publicChoiceEncoding_tag (image : ApplicationImage P L)
    (code : PublicChoiceCode P L) (value : L.Val code.guard.ty) :
    commandCacheTag? image
        (((ApplicationImage.choiceEncoding (P := P)
          code.endpoint.publicationNode code.guard.ty).submission
            image.application).encode value) =
      some (.submission code.endpoint.publicationNode) := rfl

private def conditionalCommandEncoding (image : ApplicationImage P L)
    (code : ConditionalCode P L) :
    ChoiceEncoding (L.Val code.guard.ty) image.application.PlayerCommand :=
  ((code.endpoint.addressedChoiceEncoding
      (Value := L.Val code.secretTy)).reindex code.encoding)
    |> (·.trans (ApplicationImage.conditionalTransport (P := P) code.secretTy))
    |> (·.submission image.application)

private theorem conditionalEncoding_tag (image : ApplicationImage P L)
    (code : ConditionalCode P L) (value : L.Val code.guard.ty) :
    commandCacheTag? image
        ((conditionalCommandEncoding image code).encode value) =
      some (.submission code.endpoint.publicationNode) := by
  change commandCacheTag? image
      (.submit ((ApplicationImage.conditionalTransport (P := P) code.secretTy).encode
        (code.endpoint.publicationNode,
          code.endpoint.requestPayload (code.encoding value)))) =
    some (.submission code.endpoint.publicationNode)
  cases code.encoding value <;> rfl

/-- A command recognized by a generated binding instruction's cache is
rejected by a distinct later instruction. Submission addresses separate every
public cache. A slot inequality is needed only when the later instruction is
also a binding, because only bindings recognize private registrations. -/
theorem rejectsCommand_of_binding
    (image : ApplicationImage P L) (first : BindingCode P)
    (later : ApplicationInstruction P L)
    (who : P) (command : image.application.PlayerCommand)
    (haddress : first.node ≠ later.address)
    (hslots : ∀ second : BindingCode P, later = .bind second →
      first.sourceSlot ≠ second.sourceSlot)
    (hhead : command = .wait ∨
      ¬ (ApplicationInstruction.bind first).RejectsCommand image who command) :
    later.RejectsCommand image who command := by
  rcases hhead with rfl | hrecognized
  · cases later <;> simp [RejectsCommand]
  · have howner : who = first.owner := by
      by_contra hne
      exact hrecognized (by simp [RejectsCommand, hne])
    subst who
    let registration :=
      (ApplicationImage.registrationEncoding first.sourceSlot).privateCommand
        image.application
    let submission := first.encoding.submission image.application
    have hrecognizedCache : registration.decode command ≠ none ∨
        submission.decode command ≠ none := by
      by_cases hregistration : registration.decode command = none
      · exact Or.inr fun hsubmission => hrecognized
          (by simpa [RejectsCommand, registration, submission] using
            And.intro hregistration hsubmission)
      · exact Or.inl hregistration
    cases later with
    | sample code => trivial
    | bind second =>
        intro _
        let laterRegistration :=
          (ApplicationImage.registrationEncoding second.sourceSlot).privateCommand
            image.application
        let laterSubmission := second.encoding.submission image.application
        rcases hrecognizedCache with hregistration | hsubmission
        · have htag := tag_of_decode_ne_none image registration
              (.registration first.sourceSlot)
              (by intro value; exact registrationEncoding_tag image first.sourceSlot value)
              command hregistration
          constructor
          · exact decode_eq_none_of_tag_ne image laterRegistration
              (.registration second.sourceSlot) (.registration first.sourceSlot)
              (by intro value; exact registrationEncoding_tag image second.sourceSlot value)
              command htag (by
                intro heq
                exact (hslots second rfl) (CacheTag.registration.inj heq))
          · exact decode_eq_none_of_tag_ne image laterSubmission
              (.submission second.node) (.registration first.sourceSlot)
              (by intro value; exact bindingEncoding_tag image second value)
              command htag (by simp)
        · have htag := tag_of_decode_ne_none image submission
              (.submission first.node)
              (by intro value; exact bindingEncoding_tag image first value)
              command hsubmission
          constructor
          · exact decode_eq_none_of_tag_ne image laterRegistration
              (.registration second.sourceSlot) (.submission first.node)
              (by intro value; exact registrationEncoding_tag image second.sourceSlot value)
              command htag (by simp)
          · exact decode_eq_none_of_tag_ne image laterSubmission
              (.submission second.node) (.submission first.node)
              (by intro value; exact bindingEncoding_tag image second value)
              command htag (by
                intro heq
                exact haddress (CacheTag.submission.inj heq))
    | publicChoice second =>
        intro _
        let laterEncoding :=
          (ApplicationImage.choiceEncoding (P := P)
            second.endpoint.publicationNode second.guard.ty).submission
              image.application
        rcases hrecognizedCache with hregistration | hsubmission
        · have htag := tag_of_decode_ne_none image registration
              (.registration first.sourceSlot)
              (by intro value; exact registrationEncoding_tag image first.sourceSlot value)
              command hregistration
          exact decode_eq_none_of_tag_ne image laterEncoding
            (.submission second.endpoint.publicationNode)
            (.registration first.sourceSlot)
            (by intro value; exact publicChoiceEncoding_tag image second value)
            command htag (by simp)
        · have htag := tag_of_decode_ne_none image submission
              (.submission first.node)
              (by intro value; exact bindingEncoding_tag image first value)
              command hsubmission
          exact decode_eq_none_of_tag_ne image laterEncoding
            (.submission second.endpoint.publicationNode) (.submission first.node)
            (by intro value; exact publicChoiceEncoding_tag image second value)
            command htag (by
              intro heq
              exact haddress (CacheTag.submission.inj heq))
    | conditional second =>
        intro _
        let laterEncoding := conditionalCommandEncoding image second
        rcases hrecognizedCache with hregistration | hsubmission
        · have htag := tag_of_decode_ne_none image registration
              (.registration first.sourceSlot)
              (by intro value; exact registrationEncoding_tag image first.sourceSlot value)
              command hregistration
          exact decode_eq_none_of_tag_ne image laterEncoding
            (.submission second.endpoint.publicationNode)
            (.registration first.sourceSlot)
            (by intro value; exact conditionalEncoding_tag image second value)
            command htag (by simp)
        · have htag := tag_of_decode_ne_none image submission
              (.submission first.node)
              (by intro value; exact bindingEncoding_tag image first value)
              command hsubmission
          exact decode_eq_none_of_tag_ne image laterEncoding
            (.submission second.endpoint.publicationNode) (.submission first.node)
            (by intro value; exact conditionalEncoding_tag image second value)
            command htag (by
              intro heq
              exact haddress (CacheTag.submission.inj heq))

/-- A wait or a submission recognized at one generated address is rejected by
every instruction at a distinct address. Binding registration caches are also
unaffected because the command is public. -/
private theorem rejectsCommand_of_submissionTag
    (image : ApplicationImage P L) (address : Nat)
    (later : ApplicationInstruction P L)
    (who : P) (command : image.application.PlayerCommand)
    (haddress : address ≠ later.address)
    (hhead : command = .wait ∨
      commandCacheTag? image command = some (.submission address)) :
    later.RejectsCommand image who command := by
  rcases hhead with rfl | htag
  · cases later <;> simp [RejectsCommand]
  · cases later with
    | sample code => trivial
    | bind second =>
        intro _
        constructor
        · exact decode_eq_none_of_tag_ne image
            ((ApplicationImage.registrationEncoding second.sourceSlot).privateCommand
              image.application)
            (.registration second.sourceSlot) (.submission address)
            (by intro value; exact registrationEncoding_tag image second.sourceSlot value)
            command htag (by simp)
        · exact decode_eq_none_of_tag_ne image
            (second.encoding.submission image.application)
            (.submission second.node) (.submission address)
            (by intro value; exact bindingEncoding_tag image second value)
            command htag (by
              intro heq
              exact haddress (CacheTag.submission.inj heq))
    | publicChoice second =>
        intro _
        exact decode_eq_none_of_tag_ne image
          ((ApplicationImage.choiceEncoding (P := P)
            second.endpoint.publicationNode second.guard.ty).submission image.application)
          (.submission second.endpoint.publicationNode) (.submission address)
          (by intro value; exact publicChoiceEncoding_tag image second value)
          command htag (by
            intro heq
            exact haddress (CacheTag.submission.inj heq))
    | conditional second =>
        intro _
        exact decode_eq_none_of_tag_ne image (conditionalCommandEncoding image second)
          (.submission second.endpoint.publicationNode) (.submission address)
          (by intro value; exact conditionalEncoding_tag image second value)
          command htag (by
            intro heq
            exact haddress (CacheTag.submission.inj heq))

/-- A command recognized by one ordinary public-choice instruction cannot
populate the cache of an instruction at another generated address. -/
theorem rejectsCommand_of_publicChoice
    (image : ApplicationImage P L) (first : PublicChoiceCode P L)
    (later : ApplicationInstruction P L)
    (who : P) (command : image.application.PlayerCommand)
    (haddress : first.endpoint.publicationNode ≠ later.address)
    (hhead : command = .wait ∨
      ¬ (ApplicationInstruction.publicChoice first).RejectsCommand image who command) :
    later.RejectsCommand image who command := by
  apply rejectsCommand_of_submissionTag image first.endpoint.publicationNode later who command
    haddress
  rcases hhead with hwait | hrecognized
  · exact Or.inl hwait
  · right
    let encoding :=
      (ApplicationImage.choiceEncoding (P := P)
        first.endpoint.publicationNode first.guard.ty).submission image.application
    have hdecode : encoding.decode command ≠ none := by
      intro hnone
      apply hrecognized
      intro _
      exact hnone
    exact tag_of_decode_ne_none image encoding (.submission first.endpoint.publicationNode)
      (by intro value; exact publicChoiceEncoding_tag image first value) command hdecode

/-- A command recognized by one conditional-publication instruction cannot
populate the cache of an instruction at another generated address. The source
slot is intentionally absent from the separation premise. -/
theorem rejectsCommand_of_conditional
    (image : ApplicationImage P L) (first : ConditionalCode P L)
    (later : ApplicationInstruction P L)
    (who : P) (command : image.application.PlayerCommand)
    (haddress : first.endpoint.publicationNode ≠ later.address)
    (hhead : command = .wait ∨
      ¬ (ApplicationInstruction.conditional first).RejectsCommand image who command) :
    later.RejectsCommand image who command := by
  apply rejectsCommand_of_submissionTag image first.endpoint.publicationNode later who command
    haddress
  rcases hhead with hwait | hrecognized
  · exact Or.inl hwait
  · right
    let encoding := conditionalCommandEncoding image first
    have hdecode : encoding.decode command ≠ none := by
      intro hnone
      apply hrecognized
      intro _
      exact hnone
    exact tag_of_decode_ne_none image encoding (.submission first.endpoint.publicationNode)
      (by intro value; exact conditionalEncoding_tag image first value) command hdecode

end ApplicationInstruction

namespace ApplicationPlan

/-- Either phase of the generated head-binding controller is outside every
cache in the remaining plan. Distinct public addresses follow from node
coverage; distinct private registration slots follow from field allocation.
The ambient image is arbitrary because cache separation concerns command
encodings, not handler behavior. -/
theorem bindingPolicy_rejects_next
    {Γ : VCtx P L} {pending : Finset VarId} {name : VarId} {who : P}
    {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((name, .sealed who ty) :: Γ)}
    {newName : name ∉ pending}
    {accounted : CommitmentAccounting (insert name pending) tail}
    {fresh : FreshBindings (.commit name who guard tail)}
    {state : BuildState P L Γ}
    (unrestricted : UnrestrictedBinding guard)
    (next : ApplicationPlan accounted fresh.2
      (state.addCommitEvent name who guard fresh.1).1)
    (deadlineOf : Nat → Nat) (image : ApplicationImage P L)
    (sourcePolicy : (visible : Env L.Val (eraseVCtx (viewVCtx who Γ))) →
      GameTheory.Math.Probability.FinDist
        { value : L.Val ty // evalGuard guard value visible = true })
    (history : List image.application.PlayerEntry)
    (view : image.application.View) (command : image.application.PlayerCommand)
    (hcommand : command ∈
      ((.here guard tail : SourceDecisionSite who
        (.commit name who guard tail) Γ name ty guard).bindingPolicy
          fresh state image sourcePolicy history view).support)
    (later : ApplicationInstruction P L)
    (hlater : later ∈ next.instructions deadlineOf) :
    later.RejectsCommand image who command := by
  let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
    .here guard tail
  let code := site.bindingCode fresh state (site.compiledField fresh state)
  let plan : ApplicationPlan (.commit newName accounted) fresh state :=
    .binding unrestricted next
  have hheadMem : ApplicationInstruction.bind code ∈ plan.instructions deadlineOf := by
    simp [plan, code, site, instructions, SourceDecisionSite.compiledField,
      decisionSiteState]
  have hlaterMem : later ∈ plan.instructions deadlineOf := by
    simp [plan, instructions, hlater]
  have haddress : code.node ≠ later.address := by
    have hnodup := plan.instructionAddresses_nodup deadlineOf
    rw [show plan.instructions deadlineOf = .bind code :: next.instructions deadlineOf by
      simp [plan, code, site, instructions, SourceDecisionSite.compiledField,
        decisionSiteState]] at hnodup
    have hnotMem := (List.nodup_cons.mp hnodup).1
    intro heq
    apply hnotMem
    exact List.mem_map.mpr ⟨later, hlater, heq.symm⟩
  have hslots : ∀ second : BindingCode P, later = .bind second →
      code.sourceSlot ≠ second.sourceSlot := by
    intro second hlaterEq
    have hsecondMem : ApplicationInstruction.bind second ∈ plan.instructions deadlineOf := by
      rw [hlaterEq] at hlaterMem
      exact hlaterMem
    have hcodeAllocated := plan.instructions_allocated deadlineOf (.bind code) hheadMem
    have hsecondAllocated := plan.instructions_allocated deadlineOf (.bind second) hsecondMem
    have hnodup := plan.allocatedFields_nodup deadlineOf
    rw [show plan.instructions deadlineOf = .bind code :: next.instructions deadlineOf by
      simp [plan, code, site, instructions, SourceDecisionSite.compiledField,
        decisionSiteState]] at hnodup
    simp only [List.flatMap_cons, ApplicationInstruction.allocatedFields,
      List.singleton_append] at hnodup
    have hnotMem := (List.nodup_cons.mp hnodup).1
    intro hslot
    apply hnotMem
    apply List.mem_flatMap.mpr
    refine ⟨.bind second, ?_, ?_⟩
    · rw [hlaterEq] at hlater
      exact hlater
    · have hfield : code.sourceField = second.sourceField :=
        hcodeAllocated.2.symm.trans (hslot.trans hsecondAllocated.2)
      simp [ApplicationInstruction.allocatedFields, hfield]
  apply ApplicationInstruction.rejectsCommand_of_binding image code later who command
    haddress hslots
  change command ∈
    (site.bindingPolicy fresh state image sourcePolicy history view).support at hcommand
  have hsupported := site.bindingPolicy_supported_command fresh state image sourcePolicy
    history view command hcommand
  rcases hsupported with hwait | hregistration | hbinding
  · exact Or.inl hwait
  · right
    obtain ⟨value, rfl⟩ := hregistration
    simp [ApplicationInstruction.RejectsCommand, code, site,
      ApplicationImage.registrationEncoding, SourceDecisionSite.bindingCode,
      SourceDecisionSite.compiledField, decisionSiteState]
  · right
    rw [hbinding]
    simp [ApplicationInstruction.RejectsCommand, code, site, BindingCode.encoding,
      SourceDecisionSite.bindingCode, SourceDecisionSite.compiledField,
      decisionSiteState]

/-- While the generated binding head is unresolved, the structural profile
lifting dispatches the owner exactly to that head's two-phase binding policy.
This is a local reduction of the existing runner policy, not a new evaluator. -/
theorem liftProfileIn_binding_unresolved
    {Γ : VCtx P L} {pending : Finset VarId} {name : VarId} {who : P}
    {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((name, .sealed who ty) :: Γ)}
    {newName : name ∉ pending}
    {accounted : CommitmentAccounting (insert name pending) tail}
    {fresh : FreshBindings (.commit name who guard tail)}
    {state : BuildState P L Γ}
    (unrestricted : UnrestrictedBinding guard)
    (next : ApplicationPlan accounted fresh.2
      (state.addCommitEvent name who guard fresh.1).1)
    (deadlineOf : Nat → Nat) (image : ApplicationImage P L)
    (profile : SourceBehavioralProfile (.commit name who guard tail))
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (hunresolved : view.application.done state.nodes.length = false) :
    let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
      .here guard tail
    ((ApplicationPlan.binding (newName := newName) (fresh := fresh) unrestricted next).liftProfileIn
      image deadlineOf profile who history view) =
        site.bindingPolicy fresh state image (profile who site) history view := by
  simp [liftProfileIn, hunresolved]

/-- An actual supported player step of the generated head-binding controller
preserves freshness of every cache in the remaining source plan. -/
theorem bindingPolicy_preserves_nextCaches
    {Γ : VCtx P L} {pending : Finset VarId} {name : VarId} {who : P}
    {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((name, .sealed who ty) :: Γ)}
    {newName : name ∉ pending}
    {accounted : CommitmentAccounting (insert name pending) tail}
    {fresh : FreshBindings (.commit name who guard tail)}
    {state : BuildState P L Γ}
    (unrestricted : UnrestrictedBinding guard)
    (next : ApplicationPlan accounted fresh.2
      (state.addCommitEvent name who guard fresh.1).1)
    (deadlineOf : Nat → Nat) (image : ApplicationImage P L)
    (sourcePolicy : (visible : Env L.Val (eraseVCtx (viewVCtx who Γ))) →
      GameTheory.Math.Probability.FinDist
        { value : L.Val ty // evalGuard guard value visible = true })
    (execution nextExecution : image.application.PolicyExecution)
    (command : image.application.PlayerCommand)
    (hcommand : command ∈
      ((.here guard tail : SourceDecisionSite who
        (.commit name who guard tail) Γ name ty guard).bindingPolicy
          fresh state image sourcePolicy (execution.principalHistory who)
            (State.observe image.application execution.native who)).support)
    (hstep : nextExecution ∈
      (image.application.playerStep who execution command).support)
    (hfresh : next.RemainingCachesEmpty image deadlineOf execution) :
    next.RemainingCachesEmpty image deadlineOf nextExecution := by
  apply next.remainingCachesEmpty_playerStep image deadlineOf who execution command
    nextExecution hstep hfresh
  intro instruction hinstruction
  exact bindingPolicy_rejects_next (newName := newName) unrestricted next deadlineOf image
    sourcePolicy
    (execution.principalHistory who) (State.observe image.application execution.native who)
    command hcommand instruction hinstruction

end ApplicationPlan

end Vegas

/-- info: 'Vegas.ApplicationInstruction.rejectsCommand_of_binding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationInstruction.rejectsCommand_of_binding

/-- info: 'Vegas.ApplicationInstruction.rejectsCommand_of_publicChoice' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationInstruction.rejectsCommand_of_publicChoice

/-- info: 'Vegas.ApplicationInstruction.rejectsCommand_of_conditional' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationInstruction.rejectsCommand_of_conditional

/-- info: 'Vegas.ApplicationPlan.bindingPolicy_rejects_next' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.bindingPolicy_rejects_next

/-- info: 'Vegas.ApplicationPlan.liftProfileIn_binding_unresolved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.liftProfileIn_binding_unresolved

/-- info: 'Vegas.ApplicationPlan.bindingPolicy_preserves_nextCaches' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.bindingPolicy_preserves_nextCaches
