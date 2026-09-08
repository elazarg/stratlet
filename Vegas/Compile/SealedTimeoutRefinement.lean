/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SealedRefinement
import Vegas.Compile.SourceAdequacy
import Interaction.SealedTimeoutLaws

/-! # Timed sealed execution refines graph prefixes

The proof projects only the ideal service and accepted application events.
Its proof-only empty-pool snapshot is not an observation or strategy
equivalence. Expiration stutters this graph projection.
-/

namespace Vegas.EventGraph.SealedFragment

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

private def snapshot (application : SealedTimeout.Application Player (L.Val ty)) :
    SealedProgram.State Player (L.Val ty) :=
  { service := application.service
    pool := MessagePool.empty Player (SealedProgram.Payload Player (L.Val ty))
    events := application.events }

private theorem handle_refines_timed (supported : SealedFragment G ty)
    (timed : SealedTimeout Player) (heq : timed.program = supported.compile)
    (now : Nat) (application next : SealedTimeout.Application Player (L.Val ty))
    (cfg : Config G)
    (hdecode : G.decodeSealedFrom ty application.service (Config.initial G)
      application.events = some cfg)
    (hnodup : (application.events.map SealedProgram.Event.node).Nodup)
    (message : Message Player (SealedTimeout.Payload Player (L.Val ty)))
    (hhandle : timed.handle now application message = some next) :
    ∃ result : Config G,
      G.decodeSealedFrom ty next.service (Config.initial G) next.events = some result ∧
      (result = cfg ∨ ∃ event : AvailableEvent G cfg,
        result ∈ (stepAvailableEvent G cfg event).support) := by
  cases hpayload : message.payload with
  | expire =>
      refine ⟨cfg, ?_, Or.inl rfl⟩
      have hsame := SealedTimeout.handle_expire_updates_only_resolution timed now
        application next message hpayload hhandle
      rw [hsame.1, hsame.2.1]
      exact hdecode
  | protocol payload =>
      have hordinary : SealedProgram.handle supported.compile (snapshot application)
          ⟨message.id, payload⟩ = snapshot next := by
        simp only [SealedTimeout.handle, hpayload] at hhandle
        rw [heq] at hhandle
        split at hhandle <;> try contradiction
        cases hvalid : supported.compile.validateMessage? application.service
            application.events ⟨message.id, payload⟩ with
        | none =>
            rw [hvalid] at hhandle
            contradiction
        | some event =>
            rw [hvalid] at hhandle
            cases hhandle
            simp [snapshot, SealedProgram.handle, hvalid]
      obtain ⟨result, hresult, hstep⟩ := supported.handle_refines
        (snapshot application) cfg hdecode hnodup ⟨message.id, payload⟩
      rw [hordinary] at hresult
      exact ⟨result, hresult, hstep⟩

private theorem handle_nodup_timed (timed : SealedTimeout Player) (now : Nat)
    (application next : SealedTimeout.Application Player (L.Val ty))
    (message : Message Player (SealedTimeout.Payload Player (L.Val ty)))
    (hnodup : (application.events.map SealedProgram.Event.node).Nodup)
    (hhandle : timed.handle now application message = some next) :
    (next.events.map SealedProgram.Event.node).Nodup := by
  cases hpayload : message.payload with
  | expire =>
      rw [(SealedTimeout.handle_expire_updates_only_resolution timed now application next
        message hpayload hhandle).2.1]
      exact hnodup
  | protocol payload =>
      simp only [SealedTimeout.handle, hpayload] at hhandle
      split at hhandle <;> try contradiction
      cases hvalid : timed.program.validateMessage? application.service application.events
          ⟨message.id, payload⟩ with
      | none =>
          rw [hvalid] at hhandle
          contradiction
      | some event =>
          rw [hvalid] at hhandle
          cases hhandle
          have hresult := SealedProgram.handle_eventNodes_nodup timed.program
            (snapshot application) ⟨message.id, payload⟩
            (by simpa [snapshot] using hnodup)
          simpa [snapshot, SealedProgram.handle, hvalid] using hresult

theorem sealed_timeout_run_refines (supported : SealedFragment G ty)
    (openingNode deadline : Nat)
    (actions : List (SealedTimeout.Action Player (L.Val ty))) :
    let timed : SealedTimeout Player := ⟨supported.compile, openingNode, deadline⟩
    ∃ result : Config G,
      G.decodeSealedFrom ty
        (timed.run (SealedTimeout.State.empty Player (L.Val ty)) actions).application.service
        (Config.initial G)
        (timed.run (SealedTimeout.State.empty Player (L.Val ty)) actions).application.events =
          some result ∧
      Reachable G result := by
  let timed : SealedTimeout Player := ⟨supported.compile, openingNode, deadline⟩
  suffices ∀ state cfg,
      G.decodeSealedFrom ty state.application.service (Config.initial G)
        state.application.events = some cfg →
      (state.application.events.map SealedProgram.Event.node).Nodup → Reachable G cfg →
      ∃ result,
        G.decodeSealedFrom ty (timed.run state actions).application.service (Config.initial G)
          (timed.run state actions).application.events = some result ∧ Reachable G result by
    exact this _ (Config.initial G) rfl List.nodup_nil Reachable.initial
  intro state cfg hdecode hnodup hreachable
  induction actions generalizing state cfg with
  | nil => exact ⟨cfg, hdecode, hreachable⟩
  | cons action rest ih =>
      let stepped := timed.step state action
      have hstep : ∃ next, G.decodeSealedFrom ty stepped.application.service (Config.initial G)
          stepped.application.events = some next ∧
          (next = cfg ∨ ∃ event : AvailableEvent G cfg,
            next ∈ (stepAvailableEvent G cfg event).support) := by
        cases action with
        | register owner slot value =>
            refine ⟨cfg, ?_, Or.inl rfl⟩
            exact Graph.decodeSealedFrom_of_lookup_extension ty state.application.service
              (state.application.service.sealValue owner slot value).state
              (fun handle stored hstored => IdealCommitments.lookup_sealValue_of_eq_some
                state.application.service owner slot value handle stored hstored)
              (Config.initial G) cfg state.application.events hdecode
        | submit =>
            exact ⟨cfg, by simpa [stepped, SealedTimeout.step] using hdecode, Or.inl rfl⟩
        | replay =>
            exact ⟨cfg, by simpa [stepped, SealedTimeout.step] using hdecode, Or.inl rfl⟩
        | deliver =>
            exact ⟨cfg, by simpa [stepped, SealedTimeout.step] using hdecode, Or.inl rfl⟩
        | advance =>
            exact ⟨cfg, by
              simp only [stepped, SealedTimeout.step]
              split <;> exact hdecode, Or.inl rfl⟩
        | «include» id =>
            cases hlookup : state.pool.lookup id with
            | none => exact ⟨cfg, by simpa [stepped, SealedTimeout.step,
                SealedTimeout.includePending, MessagePool.includeApplication,
                MessagePool.includePending, hlookup, MessagePool.Result.invalid] using hdecode,
                Or.inl rfl⟩
            | some message =>
                cases hhandle : timed.handle state.clock state.application message with
                | none => exact ⟨cfg, by simpa [stepped, SealedTimeout.step,
                    SealedTimeout.includePending, MessagePool.includeApplication,
                    MessagePool.includePending, hlookup, hhandle] using hdecode, Or.inl rfl⟩
                | some next =>
                    simpa [stepped, SealedTimeout.step, SealedTimeout.includePending,
                      MessagePool.includeApplication, MessagePool.includePending, hlookup, hhandle]
                      using handle_refines_timed supported timed rfl state.clock state.application
                        next cfg hdecode hnodup message hhandle
      obtain ⟨next, hnext, htransition⟩ := hstep
      have hnextReachable : Reachable G next := by
        rcases htransition with rfl | ⟨event, hevent⟩
        · exact hreachable
        · exact Reachable.step hreachable event hevent
      have hnextNodup : (stepped.application.events.map SealedProgram.Event.node).Nodup := by
        cases action <;> simp only [stepped, SealedTimeout.step]
        · exact hnodup
        · exact hnodup
        · exact hnodup
        · exact hnodup
        · rename_i id
          cases hlookup : state.pool.lookup id with
          | none => simpa [SealedTimeout.includePending, MessagePool.includeApplication,
              MessagePool.includePending, hlookup, MessagePool.Result.invalid] using hnodup
          | some message =>
              cases hhandle : timed.handle state.clock state.application message with
              | none => simpa [SealedTimeout.includePending, MessagePool.includeApplication,
                  MessagePool.includePending, hlookup, hhandle] using hnodup
              | some next =>
                  simpa [SealedTimeout.includePending, MessagePool.includeApplication,
                    MessagePool.includePending, hlookup, hhandle] using
                    handle_nodup_timed timed state.clock state.application next message
                      hnodup hhandle
        · split <;> exact hnodup
      exact ih stepped next hnext hnextNodup hnextReachable

end Vegas.EventGraph.SealedFragment

namespace Vegas.WFProgram

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}

theorem sealed_timeout_run_source (source : WFProgram Player L) (ty : L.Ty)
    [DecidableEq (L.Val ty)]
    (supported : SealedFragment (ToEventGraph.compile source.core).graph ty)
    (openingNode deadline : Nat)
    (actions : List (SealedTimeout.Action Player (L.Val ty))) :
    let timed : SealedTimeout Player := ⟨supported.compile, openingNode, deadline⟩
    ∃ cfg : Config (ToEventGraph.compile source.core).graph,
      (ToEventGraph.compile source.core).graph.decodeSealedFrom ty
        (timed.run (SealedTimeout.State.empty Player (L.Val ty)) actions).application.service
        (Config.initial (ToEventGraph.compile source.core).graph)
        (timed.run (SealedTimeout.State.empty Player (L.Val ty)) actions).application.events =
          some cfg ∧
      Reachable (ToEventGraph.compile source.core).graph cfg ∧
      (Terminal (ToEventGraph.compile source.core).graph cfg →
        ∃ terminalEnv : VEnv L (ToEventGraph.compile source.core).terminalCtx,
          SmallStep.Star
            { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
            { ctx := (ToEventGraph.compile source.core).terminalCtx,
              env := terminalEnv,
              cont := .ret (ToEventGraph.compile source.core).sourcePayoffs } ∧
          evalPayoffs? (ToEventGraph.compile source.core).payoffs cfg.store =
            some (evalPayoffs (ToEventGraph.compile source.core).sourcePayoffs terminalEnv) ∧
          ∀ {name bindTy}
            (h : VHasVar (ToEventGraph.compile source.core).terminalCtx name bindTy),
            Store.getAs cfg.store
              ((ToEventGraph.compile source.core).terminalState.fieldOf h) bindTy.base =
                some (terminalEnv.get h)) := by
  obtain ⟨cfg, hdecode, hreachable⟩ :=
    supported.sealed_timeout_run_refines openingNode deadline actions
  exact ⟨cfg, hdecode, hreachable,
    fun hterminal => ToEventGraph.compile_sourceStar source.core cfg hreachable hterminal⟩

end Vegas.WFProgram
