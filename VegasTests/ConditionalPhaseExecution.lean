/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ConditionalPhaseExecution
import Vegas.Compile.ConditionalSnapshot
import Vegas.Compile.SourceReadoutAvailability
import VegasTests.ConditionalSourceCoupling

/-! # Conditional phase after a real binding prefix

The execution below carries the actual private registration, public binding
submission, and binding inclusion histories.  The conditional controller is
therefore tested against its real cache and readout, not a fabricated view.
-/

noncomputable section

namespace VegasTests.ConditionalPhaseExecution

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.ConditionalApplicationImage
open VegasTests.ConditionalSourceCoupling

def initial : (image 10).application.PolicyExecution :=
  PolicyExecution.initial (image 10).application (initialExecution 10)

def registered (secret : Bool) : (image 10).application.PolicyExecution :=
  { initial with
    native := { initial.native with
      application := initial.native.application.register 0 0 ⟨.bool, secret⟩ }
    principalHistory := fun who => if who = 0 then
      [⟨MessageApplication.State.observe (image 10).application initial.native 0,
        .privateCommand (.register 0 ⟨.bool, secret⟩)⟩] else []
    nativeTrace := [.privateCommand 0 (.register 0 ⟨.bool, secret⟩)] }

def submitted (secret : Bool) : (image 10).application.PolicyExecution :=
  { registered secret with
    native := { (registered secret).native with
      pool := ((registered secret).native.pool.submit 0 bindingPayload).2 }
    principalHistory := fun who => if who = 0 then
      (registered secret).principalHistory 0 ++
        [⟨MessageApplication.State.observe (image 10).application
          (registered secret).native 0, .submit bindingPayload⟩]
      else (registered secret).principalHistory who
    nativeTrace := (registered secret).nativeTrace ++ [.submit 0 bindingPayload] }

def boundExecution (secret : Bool) : (image 10).application.PolicyExecution :=
  { submitted secret with
    native := (image 10).application.includePending (submitted secret).native (0, 0)
    environmentHistory :=
      [⟨MessageApplication.State.environmentView (image 10).application
        (submitted secret).native, .include (0, 0)⟩]
    nativeTrace := (submitted secret).nativeTrace ++ [.include (0, 0)] }

def prefixPlayers (secret : Bool) : Fin 2 → (image 10).application.PlayerPolicy :=
  fun who history _ => if who = 0 then match history.length with
    | 0 => FinDist.pure (.privateCommand (.register 0 ⟨.bool, secret⟩))
    | 1 => FinDist.pure (.submit bindingPayload)
    | _ => FinDist.pure .wait
  else FinDist.pure .wait

def includeBinding : (image 10).application.EnvironmentPolicy :=
  fun _ _ => FinDist.pure (.include (0, 0))

/-- The checkpoint used by the conditional phase is produced by the shared
policy runner, including its real owner and environment histories. -/
theorem real_binding_prefix (secret : Bool) :
    (image 10).application.runPolicies (prefixPlayers secret) includeBinding
      [.player 0, .player 0, .environment] initial = FinDist.pure (boundExecution secret) := by
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, prefixPlayers,
    includeBinding, initial, PolicyExecution.initial, List.length_nil,
    List.nil_append, List.length_cons, if_pos, FinDist.pure_bind,
    PlayerCommand.toAction, EnvironmentPolicyCommand.toAction,
    MessageApplication.playerStep, MessageApplication.environmentPolicyStep,
    MessageApplication.advance, MessageApplication.step]
  rfl

def conditionalSourcePolicy (openValue : Bool)
    (visible : Env simpleExpr.Val (eraseVCtx (viewVCtx (0 : Fin 2) OpeningContext))) :
    FinDist { value : Option Bool // evalGuard openingGuard value visible = true } :=
  if openValue then
    FinDist.pure ⟨some (visible.get .here), by
      change decide (some (visible.get .here) = some (visible.get .here)) = true
      simp⟩
  else FinDist.pure ⟨none, rfl⟩

def conditionalPlayers (openValue : Bool) :
    Fin 2 → (image 10).application.PlayerPolicy :=
  fun who => if who = 0 then
    (conditionalSite.imageController source.fresh compilerInitial 0 10 (image 10)
      ((image 10).ownerReadout? 0
        (conditionalSite.choice.compiledGuard source.fresh compilerInitial).choiceReads)
      (conditionalSourcePolicy openValue) (fun _ _ => false)).policy (image 10).application
  else fun _ _ => FinDist.pure .wait

def includeConditional : (image 10).application.EnvironmentPolicy :=
  fun _ _ => FinDist.pure (.include (0, 1))

/-- The phase theorem is instantiated from the real binding prefix.  Both the
exact policy law and every support-wise source successor are obtained without
assuming a loader result, cache state, readiness, or snapshot correspondence. -/
theorem real_conditional_phase (secret openValue : Bool) :
    ∃ current : CoupledAt ConditionalApplicationImage.compiled.graph boundBuild,
      current.current.source = source.env.cons secret ∧
      let code := conditionalCode 10
      let execution := boundExecution secret
      let id := ((0 : Fin 2), execution.native.pool.nextSerial 0)
      ((image 10).application.runPolicies (conditionalPlayers openValue)
          includeConditional [.player 0, .environment] execution =
        (conditionalSourcePolicy openValue
          ((current.current.source.toView 0).eraseEnv)).bind fun chosen =>
          ((image 10).application.playerStep 0 execution
            (.submit ((ApplicationImage.conditionalTransport
              (P := Fin 2) (L := simpleExpr) .bool).encode
              (code.endpoint.publicationNode,
                code.endpoint.requestPayload chosen.1)))).bind fun submitted =>
            (image 10).application.environmentPolicyStep submitted (.include id)) ∧
      ∀ chosen ∈ (conditionalSourcePolicy openValue
          ((current.current.source.toView 0).eraseEnv)).support,
        ∀ submitted ∈ ((image 10).application.playerStep 0 execution
          (.submit ((ApplicationImage.conditionalTransport
            (P := Fin 2) (L := simpleExpr) .bool).encode
            (code.endpoint.publicationNode,
              code.endpoint.requestPayload chosen.1)))).support,
        ∀ included ∈ ((image 10).application.environmentPolicyStep submitted
          (.include id)).support,
        ∃ next : CoupledAt ConditionalApplicationImage.compiled.graph finalBuild,
          next.current.source = (current.current.source.cons chosen.1).cons chosen.1 ∧
            included.native.application.Refines next.current.graph.1 := by
  obtain ⟨current, hsource, hrefines, hsnapshot⟩ := bound_source_successor secret
  let view := MessageApplication.State.observe (image 10).application
    (boundExecution secret).native 0
  have hsome : ((image 10).ownerReadout? 0
      (conditionalSite.choice.compiledGuard source.fresh compilerInitial).choiceReads
      ((boundExecution secret).principalHistory 0) view).isSome := by
    cases secret <;> decide
  obtain ⟨reads, hreadout⟩ := Option.isSome_iff_exists.mp hsome
  have hmatches : (image 10).RegistrationMatches 0
      ((boundExecution secret).principalHistory 0)
      (boundExecution secret).native.application := by
    intro field value _hprivate _haccepted hcache
    by_cases hfield : field = 0
    · subst field
      have hvalue : (⟨.bool, secret⟩ : TypedValue simpleExpr) = value :=
        Option.some.inj hcache
      exact hsnapshot.2.trans (congrArg some hvalue)
    · have hempty : (image 10).registrationCache field
          ((boundExecution secret).principalHistory 0) = none := by
        simp [ApplicationImage.registrationCache, boundExecution, submitted, registered,
          initial, ApplicationImage.registrationEncoding, Ne.symm hfield]
      rw [hempty] at hcache
      contradiction
  have hreads := conditionalSite.choice.decision.ownerReadout?_graph_reads source.fresh
    compilerInitial (image 10) ((boundExecution secret).principalHistory 0) view
    (boundExecution secret).native.application rfl current.current.graph.1 hrefines
    hmatches reads hreadout
  have hphase := ConditionalPublicationSite.conditional_phase_source_law
    (P := Fin 2) (L := simpleExpr) (Γ := OpeningContext)
    (name := 1) (publicName := 2) (who := 0) (ty := .option .bool)
    openingGuard tail specification source.fresh.2 boundBuild 0 10 current (image 10)
    (conditionalSourcePolicy openValue) (conditionalPlayers openValue) includeConditional
    (boundExecution secret) hrefines opening_publicly_validatable hsnapshot.1
    (image_lookup_conditional 10) reads (by
      intro history
      simp only [conditionalPlayers]
      rfl)
    (by intro chosen hchosen submitted hsubmitted; rfl) (by rfl) (by
      cases secret <;> rfl) hreadout hreads (by
        intro chosen hchosen value hvalue
        have heq := specification.successful_value_eq_binding
          current.current.source chosen.1 value chosen.2 hvalue
        rw [hsource] at heq
        change value = secret at heq
        rw [heq]
        change ((bound secret).application.frozen 0).bind
          (fun typed => typed.as? (L := simpleExpr) .bool) = some secret
        rw [hsnapshot.2]
        rfl)
  exact ⟨current, hsource, hphase⟩

end VegasTests.ConditionalPhaseExecution

/--
info: 'VegasTests.ConditionalPhaseExecution.real_binding_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalPhaseExecution.real_binding_prefix

/--
info: 'VegasTests.ConditionalPhaseExecution.real_conditional_phase' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalPhaseExecution.real_conditional_phase
