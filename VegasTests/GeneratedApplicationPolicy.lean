/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicy
import VegasTests.GeneratedBindingPolicy

/-! # Multistage execution of a structurally lifted source profile

The application plan supplies both the open protocol and the reference
strategy lifting. The latter is proof data, not emitted player software.
These prefix laws use arbitrary whole-source behavioral profiles and actual
message-application invocations under a specified inclusion/chance service.
-/

noncomputable section

namespace VegasTests.GeneratedApplicationPolicy

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure
open VegasTests.GeneratedPersistentDisclosure
open VegasTests.GeneratedBindingPolicy (site initial registered submitted included)

def initialLaw (profile : SourceBehavioralProfile source.prog) : FinDist Bool :=
  (profile 0 site ((source.env.toView 0).eraseEnv)).map Subtype.val

/-- A concrete service script, independent of source choices. It includes
the binding, includes the forced public marker, then invokes public chance. -/
def service : image.application.EnvironmentPolicy := fun history _ =>
  FinDist.pure (match history.length with
    | 0 => .include (0, 0)
    | 1 => .include (0, 1)
    | _ => .application (.sample 3))

private theorem initial_lift (profile : SourceBehavioralProfile source.prog)
    (history : List image.application.PlayerEntry) :
    applicationPlan.liftProfile (fun _ => 10) profile 0 history
        (MessageApplication.State.observe image.application initial.native 0) =
      site.bindingPolicy source.fresh compilerInitial image (profile 0 site) history
        (MessageApplication.State.observe image.application initial.native 0) := by
  rfl

/-- A full source profile, lifted structurally, has the source first-choice
law through actual preparation and pending-message submission. -/
theorem binding_submission_law (profile : SourceBehavioralProfile source.prog) :
    image.application.runPolicies (applicationPlan.liftProfile (fun _ => 10) profile) service
      [.player 0, .player 0] initial = (initialLaw profile).map submitted := by
  obtain ⟨reads, hreadout, hview⟩ := GeneratedBindingPolicy.initial_readout
  rw [site.bindingPolicy_two_invocations_source_law source.fresh compilerInitial
    image (profile 0 site) (applicationPlan.liftProfile (fun _ => 10) profile) service initial
    (initial_lift profile) source.env reads (by rfl) (by rfl) (by rfl) (by rfl) hreadout hview]
  rw [initialLaw, FinDist.map_comp, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro chosen _
  simp only [MessageApplication.playerStep, PlayerCommand.toAction,
    MessageApplication.advance, MessageApplication.step, FinDist.pure_bind]
  rfl

theorem binding_law (profile : SourceBehavioralProfile source.prog) :
    image.application.runPolicies (applicationPlan.liftProfile (fun _ => 10) profile) service
      [.player 0, .player 0, .environment] initial = (initialLaw profile).map included := by
  rw [show ([.player 0, .player 0, .environment] : List (@Invocation TestPlayer)) =
    [.player 0, .player 0] ++ [.environment] from rfl,
    MessageApplication.runPolicies_append, binding_submission_law, FinDist.bind_map,
    FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro secret _
  have hlength : (submitted secret).environmentHistory.length = 0 := rfl
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, service,
    hlength,
    MessageApplication.environmentPolicyStep, EnvironmentPolicyCommand.toAction,
    MessageApplication.advance, MessageApplication.step, FinDist.pure_bind]
  rfl

def markerSite : PublicChoiceSite site.continuation :=
  PublicChoiceSite.atHead (P := TestPlayer) (L := simpleExpr)
    (Γ := [(0, .sealed 0 .bool)]) (ty := .bool) 1 2 0 (.notBool (.var 1 .here)) _

def markerBuild := (compilerInitial.addCommitEvent (actionName := 0) (actionTy := BaseTy.bool)
  0 0 (.constBool true) source.fresh.1).1

private def markerPolicy (profile : SourceBehavioralProfile source.prog) :=
  markerSite.imageController source.fresh.2 markerBuild image
    (image.ownerReadout? 0 (markerSite.compiledGuard source.fresh.2 markerBuild).choiceReads)
    (profile.afterCommit 0 markerSite.decision) (fun _ _ => false)

private theorem after_binding_lift (profile : SourceBehavioralProfile source.prog)
    (secret : Bool) :
    applicationPlan.liftProfile (fun _ => 10) profile 0 ((included secret).principalHistory 0)
        (MessageApplication.State.observe image.application (included secret).native 0) =
      (markerPolicy profile).policy image.application ((included secret).principalHistory 0)
        (MessageApplication.State.observe image.application (included secret).native 0) := by
  rfl

private theorem marker_readout (secret : Bool) :
    ∃ reads, image.ownerReadout? 0
      (markerSite.compiledGuard source.fresh.2 markerBuild).choiceReads
      ((included secret).principalHistory 0)
      (MessageApplication.State.observe image.application (included secret).native 0) =
        some reads := by
  apply Option.isSome_iff_exists.mp
  cases secret <;> decide

/-- The next reference move is the source's forced marker choice. No new
phase policy is installed after binding; the same lifted profile selects it. -/
theorem after_binding_marker (profile : SourceBehavioralProfile source.prog) (secret : Bool) :
    applicationPlan.liftProfile (fun _ => 10) profile 0 ((included secret).principalHistory 0)
        (MessageApplication.State.observe image.application (included secret).native 0) =
      FinDist.pure (.submit (.choice 2 ⟨.bool, false⟩)) := by
  rw [after_binding_lift]
  obtain ⟨reads, hreads⟩ := marker_readout secret
  rw [(markerPolicy profile).policy_of_uncached_ready image.application
    ((included secret).principalHistory 0)
    (MessageApplication.State.observe image.application (included secret).native 0) reads
    (by rfl) (by rfl) (by rfl) hreads]
  let visible := viewEnvOfReadEnv markerBuild 0 reads
  have hvalue (chosen : { value : simpleExpr.Val markerSite.ty //
      evalGuard markerSite.guard value visible = true }) : chosen.1 = false := by
    have hlegal := chosen.2
    change (!chosen.1) = true at hlegal
    simpa only [Bool.not_eq_true'] using hlegal
  have hforced : profile.afterCommit 0 markerSite.decision visible =
      FinDist.pure ⟨false, by rfl⟩ := by
    let : Subsingleton { value : simpleExpr.Val markerSite.ty //
        evalGuard markerSite.guard value visible = true } :=
      ⟨fun left right => Subtype.ext ((hvalue left).trans (hvalue right).symm)⟩
    exact FinDist.eq_pure_of_subsingleton _ _
  change ((compileSourceDecision markerBuild 0 markerSite.guard
    (profile.afterCommit 0 markerSite.decision) reads).map Subtype.val).map _ = _
  simp only [compileSourceDecision]
  dsimp only [visible] at hforced
  rw [hforced]
  simp only [FinDist.map_pure]
  rfl

def markerSubmitted (secret : Bool) : image.application.PolicyExecution :=
  { included secret with
    native := { (included secret).native with pool :=
      ((included secret).native.pool.submit 0 (.choice 2 ⟨.bool, false⟩)).2 }
    principalHistory := fun who => if who = 0 then
      (included secret).principalHistory 0 ++
        [⟨MessageApplication.State.observe image.application (included secret).native 0,
          .submit (.choice 2 ⟨.bool, false⟩)⟩]
      else (included secret).principalHistory who
    nativeTrace := (included secret).nativeTrace ++ [.submit 0 (.choice 2 ⟨.bool, false⟩)] }

def beforeChance (secret : Bool) : image.application.PolicyExecution :=
  { markerSubmitted secret with
    native := image.application.includePending (markerSubmitted secret).native (0, 1)
    environmentHistory := (markerSubmitted secret).environmentHistory ++
      [⟨MessageApplication.State.environmentView image.application (markerSubmitted secret).native,
        .include (0, 1)⟩]
    nativeTrace := (markerSubmitted secret).nativeTrace ++ [.include (0, 1)] }

/-- Both actual inclusions succeeded, and the marker's value is publicly
stored before chance. A rejected but recorded submission would not suffice. -/
theorem beforeChance_marker_accepted (secret : Bool) :
    (beforeChance secret).native.receipts = [((0, 0), true), ((0, 1), true)] ∧
      Store.getAs (beforeChance secret).native.application.memory.store 2 .bool = some false ∧
      (beforeChance secret).native.application.memory.done 2 = true := by
  exact ⟨rfl, rfl, rfl⟩

private theorem marker_suffix_law (profile : SourceBehavioralProfile source.prog) (secret : Bool) :
    image.application.runPolicies (applicationPlan.liftProfile (fun _ => 10) profile) service
      [.player 0, .environment] (included secret) = FinDist.pure (beforeChance secret) := by
  have hlength : (included secret).environmentHistory.length = 1 := rfl
  simp only [MessageApplication.runPolicies, MessageApplication.invoke]
  rw [after_binding_marker]
  simp only [FinDist.pure_bind, MessageApplication.playerStep, PlayerCommand.toAction,
    MessageApplication.advance, MessageApplication.step]
  simp only [FinDist.pure_bind, service, hlength, MessageApplication.environmentPolicyStep,
    EnvironmentPolicyCommand.toAction, MessageApplication.advance, MessageApplication.step]
  rfl

/-- The same structurally lifted source profile executes both binding and
the following guarded public choice, with the exact initial source law. -/
theorem before_chance_law (profile : SourceBehavioralProfile source.prog) :
    image.application.runPolicies (applicationPlan.liftProfile (fun _ => 10) profile) service
      [.player 0, .player 0, .environment, .player 0, .environment] initial =
      (initialLaw profile).map beforeChance := by
  rw [show ([.player 0, .player 0, .environment, .player 0, .environment] :
      List (@Invocation TestPlayer)) =
    [.player 0, .player 0, .environment] ++ [.player 0, .environment] from rfl,
    MessageApplication.runPolicies_append, binding_law, FinDist.bind_map, FinDist.map_eq_bind]
  exact FinDist.bind_congr (fun secret _ => marker_suffix_law profile secret)

/-- Public completion, not the cached submission, determines advancement.
At the chance boundary every player's lifted policy waits. -/
theorem before_chance_waits (profile : SourceBehavioralProfile source.prog)
    (secret : Bool) (player : TestPlayer) :
    applicationPlan.liftProfile (fun _ => 10) profile player
        ((beforeChance secret).principalHistory player)
        (MessageApplication.State.observe image.application (beforeChance secret).native player) =
      FinDist.pure .wait := by
  rfl

def afterChance (secret signal : Bool) : image.application.PolicyExecution :=
  { beforeChance secret with
    native := { (beforeChance secret).native with application :=
      (beforeChance secret).native.application.sample signalCode signal }
    environmentHistory := (beforeChance secret).environmentHistory ++
      [⟨MessageApplication.State.environmentView image.application (beforeChance secret).native,
        .application (.sample 3)⟩]
    nativeTrace := (beforeChance secret).nativeTrace ++ [.environment (.sample 3)] }

private theorem chance_suffix_law (profile : SourceBehavioralProfile source.prog) (secret : Bool) :
    image.application.runPolicies (applicationPlan.liftProfile (fun _ => 10) profile) service
      [.environment] (beforeChance secret) = fairCoin.denote.map (afterChance secret) := by
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, FinDist.bind_pure]
  change (FinDist.pure
    (.application (.sample 3) : image.application.EnvironmentPolicyCommand)).bind _ = _
  simp only [FinDist.pure_bind, MessageApplication.environmentPolicyStep,
    EnvironmentPolicyCommand.toAction, MessageApplication.advance, MessageApplication.step,
    FinDist.bind_map, FinDist.bind_bind]
  change (image.sample (checkpoint secret).application 3).bind _ = _
  rw [checkpoint_sample_law, FinDist.bind_map, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro signal _
  rfl

/-- Binding, guarded publication, and actual application chance compose under
one lifted whole-source profile. Both random draws retain their exact laws. -/
theorem through_chance_law (profile : SourceBehavioralProfile source.prog) :
    image.application.runPolicies (applicationPlan.liftProfile (fun _ => 10) profile) service
      [.player 0, .player 0, .environment, .player 0, .environment, .environment] initial =
      (initialLaw profile).bind (fun secret => fairCoin.denote.map (afterChance secret)) := by
  rw [show ([.player 0, .player 0, .environment, .player 0, .environment, .environment] :
      List (@Invocation TestPlayer)) =
    [.player 0, .player 0, .environment, .player 0, .environment] ++ [.environment] from rfl,
    MessageApplication.runPolicies_append, before_chance_law, FinDist.bind_map]
  exact FinDist.bind_congr (fun secret _ => chance_suffix_law profile secret)

/-- Analysis readout: the hidden accepted binding and the public chance value.
The first component is not added to any runtime observation. -/
def bindingAndSignal (execution : image.application.PolicyExecution) :
    Option Bool × Option Bool :=
  (Store.getAs execution.native.application.frozen 0 .bool,
    Store.getAs execution.native.application.memory.store 3 .bool)

theorem through_chance_values_law (profile : SourceBehavioralProfile source.prog) :
    (image.application.runPolicies (applicationPlan.liftProfile (fun _ => 10) profile) service
      [.player 0, .player 0, .environment, .player 0, .environment, .environment] initial).map
        bindingAndSignal =
      (initialLaw profile).bind (fun secret =>
        fairCoin.denote.map (fun signal => (some secret, some signal))) := by
  rw [through_chance_law, FinDist.map_bind]
  apply FinDist.bind_congr
  intro secret _
  rw [FinDist.map_comp]
  rfl

end VegasTests.GeneratedApplicationPolicy

/-- info: 'VegasTests.GeneratedApplicationPolicy.before_chance_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedApplicationPolicy.before_chance_law

/-- info: 'VegasTests.GeneratedApplicationPolicy.through_chance_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedApplicationPolicy.through_chance_law

/-- info: 'VegasTests.GeneratedApplicationPolicy.through_chance_values_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedApplicationPolicy.through_chance_values_law
