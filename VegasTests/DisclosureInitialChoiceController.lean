/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceChoiceController
import VegasTests.DisclosureApplication
import VegasTests.DisclosureSourcePolicies

/-! # Source-generated initial private choice controller

The checked source's first decision is encoded as authenticated private
registration at slot zero. Opaque binding remains a later public phase.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability

def initialGuard : Expr
    ((0, .bool) :: eraseVCtx (viewVCtx (0 : TestPlayer)
      ([] : VCtx TestPlayer simpleExpr))) .bool := .constBool true

def initialSite : SourceDecisionSite (0 : TestPlayer) source.prog [] 0 .bool
    initialGuard := by
  unfold source core coreWithPayoffs
  exact .here _ _

def compilerInitial : BuildState TestPlayer simpleExpr source.Γ :=
  BuildState.fromInitial (initialState source.Γ source.env source.wctx)

abbrev InitialDecision :=
  (visible : Env simpleExpr.Val
    (eraseVCtx (viewVCtx (0 : TestPlayer) ([] : VCtx TestPlayer simpleExpr)))) →
    FinDist { value : simpleExpr.Val .bool //
      evalGuard initialGuard value visible = true }

def pureInitialDecision (secret : Bool) : InitialDecision :=
  fun _ => FinDist.pure ⟨secret, rfl⟩

theorem pureProfile_initial_decision (secret : Bool)
    (complete : Bool → Bool → Bool) (response : Bool → Option Bool → Bool) :
    SourcePolicies.pureProfile [(0, payoff)] secret complete response 0 initialSite =
      pureInitialDecision secret := by
  rfl

/-- Slot zero is part of the private command's endpoint identity. -/
def initialChoiceEncoding : MessageApplication.ChoiceEncoding Bool (Nat × Bool) where
  encode value := (0, value)
  decode command := if command.1 = 0 then some command.2 else none
  decode_encode := by intro value; rfl
  decode_sound := by
    intro command value hdecode
    rcases command with ⟨slot, actual⟩
    simp only at hdecode
    split at hdecode
    · rename_i hslot
      subst slot
      simp only [Option.some.injEq] at hdecode
      subst actual
      rfl
    · contradiction

def initialCommandEncoding (window : Nat) :
    MessageApplication.ChoiceEncoding Bool (application window).PlayerCommand :=
  initialChoiceEncoding.privateCommand (application window)

def initialCachedValue (window : Nat)
    (history : List (application window).PlayerEntry) : Option Bool :=
  (initialCommandEncoding window).cachedValue (application window) history

private theorem initialReadsAvailable : ∀ ref,
    ref ∈ (eventGuardOf (decisionSiteState initialSite source.fresh compilerInitial)
      0 initialGuard).choiceReads →
      ∃ value, Store.getAs graph.initialStore ref.field ref.ty = some value := by
  intro ref href
  change ref ∈ visibleFieldRefs
    (decisionSiteState initialSite source.fresh compilerInitial) 0 at href
  have hempty : (visibleFieldRefs
      (decisionSiteState initialSite source.fresh compilerInitial) 0) = ∅ := rfl
  rw [hempty] at href
  simp at href

private def initialReads : initialSite.ChoiceReads source.fresh compilerInitial :=
  ReadEnv.ofStore graph.initialStore _ initialReadsAvailable

private theorem initialReads_eq : ReadEnv.ofStore? graph.initialStore
    (eventGuardOf (decisionSiteState initialSite source.fresh compilerInitial)
      0 initialGuard).choiceReads = some initialReads := by
  unfold ReadEnv.ofStore?
  rw [dif_pos initialReadsAvailable]
  apply congrArg some
  apply ReadEnv.ext
  intro ref href
  change ref ∈ visibleFieldRefs
    (decisionSiteState initialSite source.fresh compilerInitial) 0 at href
  have hempty : visibleFieldRefs
      (decisionSiteState initialSite source.fresh compilerInitial) 0 = ∅ := rfl
  rw [hempty] at href
  simp at href

def initialChoiceController (window : Nat) (decision : InitialDecision) :
    (application window).ChoiceController Bool
      (initialSite.ChoiceReads source.fresh compilerInitial) :=
  initialSite.controller source.fresh compilerInitial (application window)
    (initialCommandEncoding window) (fun _ => true) (fun view => view.application.accepted.isSome)
    (fun _ _ => some initialReads) decision (fun _ _ => false)

theorem initialChoiceController_first_private (window : Nat)
    (decision : InitialDecision) (history : List (application window).PlayerEntry)
    (view : (application window).View)
    (haccepted : view.application.accepted = none)
    (hcache : initialCachedValue window history = none) :
    (initialChoiceController window decision).policy (application window) history view =
      (decision (VEnv.empty simpleExpr).eraseEnv).map fun chosen =>
        .privateCommand (0, chosen.1) := by
  have hagrees : (decisionSiteState initialSite source.fresh compilerInitial).ViewAgrees
      0 graph.initialStore (VEnv.empty simpleExpr) := by
    intro name ty binding
    cases binding
  apply initialSite.controller_first_emission_source_law source.fresh compilerInitial
    (application window) (initialCommandEncoding window) (fun _ => true)
    (fun current => current.application.accepted.isSome)
    (fun _ _ => some initialReads) decision (fun _ _ => false) history view
    graph.initialStore (VEnv.empty simpleExpr) initialReads
  · simp [haccepted]
  · exact hcache
  · rfl
  · rfl
  · exact hagrees
  · exact initialReads_eq

theorem initialChoiceController_cached_wait (window : Nat)
    (decision : InitialDecision) (history : List (application window).PlayerEntry)
    (view : (application window).View) (secret : Bool)
    (haccepted : view.application.accepted = none)
    (hcache : initialCachedValue window history = some secret) :
    (initialChoiceController window decision).policy (application window) history view =
      FinDist.pure .wait := by
  rw [(initialChoiceController window decision).policy_of_cached
    (application window) history view secret (by
      change view.application.accepted.isSome = false
      simp [haccepted]) hcache]
  rfl

theorem initialChoiceController_resolved_wait (window : Nat)
    (decision : InitialDecision) (history : List (application window).PlayerEntry)
    (view : (application window).View)
    (haccepted : view.application.accepted.isSome = true) :
    (initialChoiceController window decision).policy (application window) history view =
      FinDist.pure .wait := by
  exact (initialChoiceController window decision).policy_of_resolved
    (application window) history view haccepted

def initialPlayers (window : Nat) (decision : InitialDecision) :
    TestPlayer → (application window).PlayerPolicy := fun _ =>
  (initialChoiceController window decision).policy (application window)

private def initialEnvironment (window : Nat) : (application window).EnvironmentPolicy :=
  fun _ _ => FinDist.pure .wait

def initialExecution (window : Nat) : (application window).PolicyExecution :=
  PolicyExecution.initial (application window) (initial window)

def initialRegistrationObservation (window : Nat)
    (execution : (application window).PolicyExecution) :
    Option Bool × Option Bool × List (Message TestPlayer (application window).Payload) :=
  (execution.native.application.service.lookup (0, 0),
    initialCachedValue window (execution.principalHistory 0),
    execution.native.pool.pending)

/-- The actual first private invocation jointly records the same source draw
in the ideal service and own command history, without public traffic. -/
theorem initial_registration_source_law (window : Nat) (decision : InitialDecision) :
    ((application window).invoke (initialPlayers window decision)
        (initialEnvironment window) (initialExecution window) (.player 0)).map
          (initialRegistrationObservation window) =
      (decision (VEnv.empty simpleExpr).eraseEnv).map fun chosen =>
        (some chosen.1, some chosen.1, []) := by
  have hagrees : (decisionSiteState initialSite source.fresh compilerInitial).ViewAgrees
      0 graph.initialStore (VEnv.empty simpleExpr) := by
    intro name ty binding
    cases binding
  have hinvoke := initialSite.controller_first_invoke_source_law source.fresh
    compilerInitial (application window) (initialCommandEncoding window)
    (fun _ => true) (fun view => view.application.accepted.isSome)
    (fun _ _ => some initialReads) decision (fun _ _ => false)
    (initialPlayers window decision) (initialEnvironment window)
    (initialExecution window) graph.initialStore (VEnv.empty simpleExpr)
    initialReads rfl rfl rfl rfl rfl hagrees initialReads_eq
  rw [hinvoke, FinDist.map_bind]
  apply FinDist.bind_congr
  intro chosen _
  simp [MessageApplication.playerStep, MessageApplication.advance,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step,
    initialRegistrationObservation, initialExecution, initialCachedValue,
    initialCommandEncoding, initialChoiceEncoding, application, initial, empty,
    privateStep, IdealCommitments.sealValue, IdealCommitments.lookup,
    ChoiceEncoding.privateCommand, PolicyExecution.initial, State.initial,
    MessagePool.empty, IdealCommitments.empty]

theorem pure_initial_registration_source_law (window : Nat) (secret : Bool) :
    ((application window).invoke (initialPlayers window (pureInitialDecision secret))
        (initialEnvironment window) (initialExecution window) (.player 0)).map
          (initialRegistrationObservation window) =
      FinDist.pure (some secret, some secret, []) := by
  rw [initial_registration_source_law]
  simp [pureInitialDecision]

end VegasTests.OptionalDisclosure.DisclosureState
