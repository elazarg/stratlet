/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.BindingImageExecution
import Vegas.Compile.ApplicationImageBindingInclusion
import VegasTests.GeneratedPersistentDisclosure

/-! # Randomized binding through a generated public-message application

The first decision of the persistent-disclosure source is sampled by its
generated controller. Two owner invocations and a specified inclusion produce
the source distribution of accepted snapshots. No private value is submitted
to the message pool. This is a prefix law, not whole-program settlement or
strategic preservation.
-/

noncomputable section

namespace VegasTests.GeneratedBindingPolicy

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure
open VegasTests.GeneratedPersistentDisclosure

def site : SourceDecisionSite (P := TestPlayer) (L := simpleExpr)
    0 source.prog [] 0 .bool (.constBool true) := .here _ _

def code := site.bindingCode source.fresh compilerInitial
  (site.compiledField source.fresh compilerInitial)

def sourcePolicy (law : FinDist Bool)
    (visible : Env simpleExpr.Val (eraseVCtx (viewVCtx (0 : TestPlayer) []))) :
    FinDist { value : simpleExpr.Val .bool //
      evalGuard (L := simpleExpr) (Γ := ([] : VCtx TestPlayer simpleExpr)) (b := BaseTy.bool)
        (.constBool true (Γ := [(0, .bool)])) value visible = true } :=
  law.map fun value => ⟨value, rfl⟩

def players (law : FinDist Bool) : TestPlayer → image.application.PlayerPolicy :=
  fun who => if who = 0 then site.bindingPolicy source.fresh compilerInitial image
    (sourcePolicy law) else fun _ _ => FinDist.pure .wait

def environment : image.application.EnvironmentPolicy :=
  fun _ _ => FinDist.pure (.include (0, 0))

def initial : image.application.PolicyExecution :=
  PolicyExecution.initial image.application initialExecution

def registered (secret : Bool) : image.application.PolicyExecution :=
  { initial with
    native := { initial.native with
      application := initial.native.application.register 0 0 ⟨.bool, secret⟩ }
    principalHistory := fun who => if who = 0 then
      [⟨MessageApplication.State.observe image.application initial.native 0,
        .privateCommand (.register 0 ⟨.bool, secret⟩)⟩] else []
    nativeTrace := [.privateCommand 0 (.register 0 ⟨.bool, secret⟩)] }

def submitted (secret : Bool) : image.application.PolicyExecution :=
  { registered secret with
    native := { (registered secret).native with pool :=
      ((registered secret).native.pool.submit 0 (.binding 0 (0, 0))).2 }
    principalHistory := fun who => if who = 0 then
      (registered secret).principalHistory 0 ++
        [⟨MessageApplication.State.observe image.application (registered secret).native 0,
          .submit (.binding 0 (0, 0))⟩]
      else (registered secret).principalHistory who
    nativeTrace := (registered secret).nativeTrace ++ [.submit 0 (.binding 0 (0, 0))] }

def included (secret : Bool) : image.application.PolicyExecution :=
  { submitted secret with
    native := image.application.includePending (submitted secret).native (0, 0)
    environmentHistory :=
      [⟨MessageApplication.State.environmentView image.application (submitted secret).native,
        .include (0, 0)⟩]
    nativeTrace := (submitted secret).nativeTrace ++ [.include (0, 0)] }

private theorem initial_readout : ∃ reads,
    image.ownerReadout? (0 : TestPlayer)
        (eventGuardOf (decisionSiteState site source.fresh compilerInitial)
          0 (.constBool true (Γ := [(0, .bool)]))).choiceReads
        (initial.principalHistory 0)
        (MessageApplication.State.observe image.application initial.native 0) = some reads ∧
      viewEnvOfReadEnv (decisionSiteState site source.fresh compilerInitial) 0 reads =
        (source.env.toView 0).eraseEnv := by
  have havailable : ∀ ref, ref ∈ visibleFieldRefs compilerInitial 0 →
      ∃ value, Store.getAs
        (image.ownerReadStore 0 (initial.principalHistory 0) initial.native.application.memory)
        ref.field ref.ty = some value := by
    intro ref href
    change ref ∈ (∅ : Finset (FieldRef simpleExpr)) at href
    exact False.elim (Finset.notMem_empty ref href)
  let reads := ReadEnv.ofStore _ _ havailable
  have hreads : ReadEnv.ofStore?
      (image.ownerReadStore 0 (initial.principalHistory 0) initial.native.application.memory)
      (visibleFieldRefs compilerInitial 0) = some reads := by
    unfold ReadEnv.ofStore?
    rw [dif_pos havailable]
  refine ⟨reads, ReadEnv.ofStoreExec?_eq_some_of_ofStore?_eq_some hreads, ?_⟩
  apply viewEnvOfReadEnv_eq_sourceView compilerInitial 0 _ source.env _ reads hreads
  intro name bindTy binding
  cases binding

/-- The actual generated prefix leaves one opaque packet pending while
retaining the sampled source value in private preparation and owner history. -/
theorem binding_submission_source_law (law : FinDist Bool) :
    image.application.runPolicies (players law) environment
      [.player 0, .player 0] initial = law.map submitted := by
  obtain ⟨reads, hreadout, hview⟩ := initial_readout
  rw [site.bindingPolicy_two_invocations_source_law source.fresh compilerInitial
    image (sourcePolicy law) (players law) environment initial (by simp [players])
    source.env reads (by rfl) (by rfl) (by rfl) (by rfl) hreadout hview]
  simp only [sourcePolicy, FinDist.bind_map]
  rw [FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro secret _
  simp only [MessageApplication.playerStep, PlayerCommand.toAction,
    MessageApplication.advance, MessageApplication.step, FinDist.pure_bind]
  rfl

/-- The complete three-invocation execution law retains the original draw
through actual private preparation, public submission, and recorded inclusion. -/
theorem binding_source_law (law : FinDist Bool) :
    image.application.runPolicies (players law) environment
      [.player 0, .player 0, .environment] initial = law.map included := by
  rw [show ([.player 0, .player 0, .environment] : List (@Invocation TestPlayer)) =
    [.player 0, .player 0] ++ [.environment] from rfl,
    MessageApplication.runPolicies_append, binding_submission_source_law, FinDist.bind_map,
    FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro secret _
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, environment,
    MessageApplication.environmentPolicyStep, EnvironmentPolicyCommand.toAction,
    MessageApplication.advance, MessageApplication.step, FinDist.pure_bind]
  rfl

private theorem image_lookup_binding : image.lookup 0 = some (.bind code) := by
  have hmem : (ApplicationInstruction.bind code) ∈
      applicationPlan.instructions (fun _ => 10) := by
    change _ ∈ [ApplicationInstruction.bind code, _, _, _, _, _]
    simp
  exact applicationPlan.image_lookup_of_mem (fun _ => 10) _ hmem

private theorem submitted_consistent (secret : Bool) :
    image.RegistrationConsistent (submitted secret) := by
  have hstep : submitted secret ∈ (image.application.runPolicies
      (players (FinDist.pure secret)) environment [.player 0, .player 0] initial).support := by
    rw [binding_submission_source_law, FinDist.map_pure]
    exact FinDist.mem_support_pure.mpr rfl
  exact image.runPolicies_registrationConsistent _ _ _ initial _
    (fun _ _ => rfl) hstep

/-- Inclusion freezes the actual cached draw, not an independently supplied
source witness. The command and environment histories belong to that run. -/
theorem included_snapshot (secret : Bool) :
    ApplicationImage.AcceptedSnapshot (L := simpleExpr) 0 (0, 0) (some ⟨.bool, secret⟩)
      (included secret).native.application := by
  have hcache : image.registrationCache 0
      ((submitted secret).principalHistory 0) = some ⟨.bool, secret⟩ := by
    simp [submitted, registered, ApplicationImage.registrationCache,
      ChoiceEncoding.privateCommand,
      ApplicationImage.registrationEncoding]
  have hstep : included secret ∈
      (image.application.environmentPolicyStep (submitted secret) (.include (0, 0))).support := by
    simp only [MessageApplication.environmentPolicyStep, EnvironmentPolicyCommand.toAction,
      MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
      FinDist.mem_support_pure]
    rfl
  exact (image.environmentPolicyStep_include_binding_cachedSnapshot (submitted secret)
    0 code image_lookup_binding (0, 0) ⟨.bool, secret⟩ (submitted_consistent secret)
    hcache (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (included secret) hstep).2.2.2.1

/-- The accepted snapshot has exactly the arbitrary randomized source law. -/
theorem binding_snapshot_law (law : FinDist Bool) :
    (image.application.runPolicies (players law) environment
      [.player 0, .player 0, .environment] initial).map
        (fun execution => execution.native.application.frozen 0) =
      law.map (fun secret => some (⟨.bool, secret⟩ : TypedValue simpleExpr)) := by
  rw [binding_source_law, FinDist.map_comp]
  exact FinDist.map_congr_of_eq_on_support (fun secret _ => (included_snapshot secret).2)

/-- Before inclusion the environment already sees the complete pending pool;
the generated binding packet is independent of the privately registered bit. -/
theorem submitted_environmentView (secret : Bool) :
    MessageApplication.State.environmentView image.application (submitted secret).native =
      MessageApplication.State.environmentView image.application (submitted false).native := by
  rfl

theorem binding_pending_environment_law (law : FinDist Bool) :
    (image.application.runPolicies (players law) environment
      [.player 0, .player 0] initial).map
        (fun execution => MessageApplication.State.environmentView image.application
          execution.native) =
      FinDist.pure (MessageApplication.State.environmentView image.application
        (submitted false).native) := by
  rw [binding_submission_source_law, FinDist.map_comp]
  have heq : (fun secret => MessageApplication.State.environmentView image.application
      (submitted secret).native) = fun _ : Bool =>
        MessageApplication.State.environmentView image.application (submitted false).native :=
    funext submitted_environmentView
  change law.map (fun secret => MessageApplication.State.environmentView image.application
    (submitted secret).native) = _
  rw [heq, FinDist.map_const]

/-- Even the environment's full pool view after binding inclusion contains
only the canonical handle. Its observation is independent of the sampled bit. -/
theorem included_environmentView (secret : Bool) :
    MessageApplication.State.environmentView image.application (included secret).native =
      MessageApplication.State.environmentView image.application (included false).native := by
  rfl

/-- Arbitrary source randomization changes the hidden accepted snapshot but
not the environment observation at this binding checkpoint. -/
theorem binding_environment_law (law : FinDist Bool) :
    (image.application.runPolicies (players law) environment
      [.player 0, .player 0, .environment] initial).map
        (fun execution => MessageApplication.State.environmentView image.application
          execution.native) =
      FinDist.pure (MessageApplication.State.environmentView image.application
        (included false).native) := by
  rw [binding_source_law, FinDist.map_comp]
  have heq : (fun secret => MessageApplication.State.environmentView image.application
      (included secret).native) = fun _ : Bool =>
        MessageApplication.State.environmentView image.application (included false).native :=
    funext included_environmentView
  change law.map (fun secret => MessageApplication.State.environmentView image.application
    (included secret).native) = _
  rw [heq, FinDist.map_const]

end VegasTests.GeneratedBindingPolicy

/-- info: 'VegasTests.GeneratedBindingPolicy.binding_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedBindingPolicy.binding_source_law

/-- info: 'VegasTests.GeneratedBindingPolicy.binding_snapshot_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedBindingPolicy.binding_snapshot_law

/-- info: 'VegasTests.GeneratedBindingPolicy.binding_pending_environment_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedBindingPolicy.binding_pending_environment_law
