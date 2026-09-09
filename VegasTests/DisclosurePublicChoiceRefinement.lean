/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicChoiceExecution
import VegasTests.DisclosureApplicationSource

/-! # Refinement of the disclosure responder endpoint

Acceptance by the native response handler is acceptance by the public-choice
endpoint generated from the source occurrence.  Consequently it performs the
same adjacent source commit/reveal and the same two-node graph macro as the
decoded native update.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Vegas EventGraph Interaction

private theorem response_checkpoint_agrees (state : DisclosureState)
    (hready : state.responseReady = true) :
    (responseOccurrence.siteState source.fresh responseCompilerInitial).Agrees
      state.decodedConfig.store
      (responseEnv state.data.secret state.data.signal state.data.opening) := by
  have hpublication := responseReady_publication state hready
  have hready' := hready
  simp only [responseReady, PublicChoice.ready, Bool.and_eq_true,
    Bool.not_eq_true', List.all_eq_true] at hready'
  have hresponse : state.response.isSome = false := by
    simpa [done] using hready'.1
  have hphase : state.phase = 6 := by
    simp [phase, hpublication, hresponse]
  rw [decodedConfig, hphase]
  intro name ty binding
  cases binding with
  | here => rfl
  | there binding =>
    cases binding with
    | here => rfl
    | there binding =>
      cases binding with
      | here => rfl
      | there binding =>
        cases binding with
        | here => rfl
        | there binding =>
          cases binding with
          | here => rfl
          | there binding =>
            cases binding with
            | here => rfl
            | there binding => cases binding

private theorem response_validator_source (state : DisclosureState)
    (hready : state.responseReady = true) (value : Bool) :
    responseValidator value =
      evalGuard responseOccurrence.guard value
        (((responseEnv state.data.secret state.data.signal state.data.opening).toView
          responseOccurrence.owner).eraseEnv) := by
  apply responseOccurrence.validator_source source.fresh responseCompilerInitial
    state.decodedConfig.store (fun _ => none)
    (responseEnv state.data.secret state.data.signal state.data.opening)
    (response_checkpoint_agrees state hready)
  intro ref href
  change ref ∈ responseGuard.validationReads at href
  rw [responseGuard_no_reads] at href
  exact False.elim (Finset.notMem_empty _ href)

private theorem response_macro_eq (state : DisclosureState) (value : Bool)
    (hready : state.responseReady = true) :
    responseOccurrence.completePublication source.fresh responseCompilerInitial
        state.decodedConfig value =
      ({ state with response := some value } : DisclosureState).decodedConfig := by
  have hpublication := responseReady_publication state hready
  have hready' := hready
  simp only [responseReady, PublicChoice.ready, Bool.and_eq_true,
    Bool.not_eq_true', List.all_eq_true] at hready'
  have hresponse : state.response.isSome = false := by
    simpa [done] using hready'.1
  have hphase : state.phase = 6 := by
    simp [phase, hpublication, hresponse]
  rw [decodedConfig, hphase]
  change ((cfg state.data 6).completeNode (node 6) ⟨.bool, value⟩).completeNode
      (node 7) ⟨.bool, value⟩ = _
  let updated : RunData := { state.data with response := value }
  have hprefix : cfg state.data 6 = cfg updated 6 := by rfl
  rw [hprefix]
  calc
    _ = (cfg updated 7).completeNode (node 7) ⟨.bool, value⟩ := by
      exact congrArg (fun config => config.completeNode (node 7) ⟨.bool, value⟩)
        (cfg_succ updated 6).symm
    _ = cfg updated 8 := (cfg_succ updated 7).symm
    _ = ({ state with response := some value } : DisclosureState).decodedConfig := by
      have hdata : ({ state with response := some value } : DisclosureState).data =
          updated := by rfl
      have hnextPhase :
          ({ state with response := some value } : DisclosureState).phase = 8 := by
        simp [phase]
      rw [decodedConfig, hnextPhase, hdata]

/-- The native handler delegates both acceptance and rejection to the generated
endpoint and records precisely its accepted value. -/
theorem respond_handle (window : Nat) (state : DisclosureState)
    (id : MessageId TestPlayer) (value : Bool) :
    handle window state ⟨id, .respond value⟩ =
      (responseEndpoint.resolve? state.done responseValidator ⟨id, value⟩).map
        (fun chosen => { state with response := some chosen }) := rfl

/-- A successful native response is exactly an acceptance by the generated
public-choice endpoint, with no independently constructed response witness. -/
theorem respond_acceptance (window : Nat) (state next : DisclosureState)
    (id : MessageId TestPlayer) (value : Bool)
    (hhandle : handle window state ⟨id, .respond value⟩ = some next) :
    responseEndpoint.resolve? state.done responseValidator ⟨id, value⟩ = some value ∧
      next = { state with response := some value } := by
  simp only [handle] at hhandle
  cases hresolve : responseEndpoint.resolve? state.done responseValidator ⟨id, value⟩ with
  | none => simp [hresolve] at hhandle
  | some chosen =>
      have hchosen : chosen = value := by
        have haccepted := (responseEndpoint.resolve_iff state.done responseValidator
          ⟨id, value⟩ chosen).mp hresolve
        exact haccepted.2.2.2.symm
      subst chosen
      have hnext : next = { state with response := some value } := by
        simpa only [hresolve, Option.map_some, Option.some.injEq] using hhandle.symm
      exact ⟨rfl, hnext⟩

/-- Native response acceptance performs the actual responder choice and its
adjacent public reveal in the written disclosure source. -/
theorem respond_source_steps (window : Nat) (state next : DisclosureState)
    (id : MessageId TestPlayer) (value : Bool)
    (hhandle : handle window state ⟨id, .respond value⟩ = some next) :
    SmallStep.Star
      ⟨responseOccurrence.context,
        responseEnv state.data.secret state.data.signal state.data.opening,
        .commit responseOccurrence.choiceName responseOccurrence.owner
          responseOccurrence.guard responseOccurrence.decision.continuation⟩
      ⟨(responseOccurrence.publicName, .pub responseOccurrence.ty) ::
          (responseOccurrence.choiceName,
            .sealed responseOccurrence.owner responseOccurrence.ty) ::
            responseOccurrence.context,
        ((responseEnv state.data.secret state.data.signal state.data.opening).cons
          value).cons value,
        responseOccurrence.tail⟩ := by
  have hresolve := (respond_acceptance window state next id value hhandle).1
  have hready :=
    ((responseEndpoint.resolve_iff state.done responseValidator ⟨id, value⟩ value).mp
      hresolve).1
  exact responseOccurrence.runtime_resolution_source_steps source.fresh
    responseCompilerInitial
    (responseEnv state.data.secret state.data.signal state.data.opening)
    state.done responseValidator ⟨id, value⟩ value
    (fun chosen hvalid => (response_validator_source state hready chosen).symm.trans hvalid)
    hresolve

/-- The exact generated graph macro of an accepted native response is the
decoded configuration of the native handler result, and is reachable. -/
theorem respond_graph_refinement (window : Nat) (state next : DisclosureState)
    (id : MessageId TestPlayer) (value : Bool)
    (hinvariant : Invariant state)
    (hhandle : handle window state ⟨id, .respond value⟩ = some next) :
    responseOccurrence.completePublication source.fresh responseCompilerInitial
        state.decodedConfig value = next.decodedConfig ∧
      Reachable graph next.decodedConfig := by
  obtain ⟨hresolve, rfl⟩ := respond_acceptance window state next id value hhandle
  have hready :=
    ((responseEndpoint.resolve_iff state.done responseValidator ⟨id, value⟩ value).mp
      hresolve).1
  have hmacro := response_macro_eq state value hready
  refine ⟨hmacro, ?_⟩
  rw [← hmacro]
  exact responseOccurrence.runtime_resolution_reachable source.fresh
    responseCompilerInitial state.decodedConfig
    (responseEnv state.data.secret state.data.signal state.data.opening)
    (response_checkpoint_agrees state hready)
    state.done responseValidator ⟨id, value⟩
    (done_iff_decodedConfig_done state hinvariant)
    (fun chosen hvalid => (response_validator_source state hready chosen).symm.trans hvalid)
    value hresolve
    (decodedConfig_reachable state hinvariant)

end VegasTests.OptionalDisclosure.DisclosureState

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.respond_source_steps'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.respond_source_steps

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.respond_graph_refinement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.respond_graph_refinement
