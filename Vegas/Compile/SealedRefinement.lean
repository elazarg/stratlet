/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SealedExecution
import Vegas.Compile.SealedDecodeLaws
import Vegas.Compile.SealedRules
import Interaction.SealedProgramLaws
import Interaction.SealedExecutionLaws

/-! # Application handling and primitive graph execution

Successful commitment and opening handlers decode to the graph's actual
primitive transition. Rejected traffic can affect the public ledger without
advancing that graph. The correspondence is operational: it does not erase
the runtime observations or establish a correspondence between strategies.
-/

namespace Vegas.EventGraph.SealedFragment

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Any application message either stutters under decoding or executes one
available primitive graph event. The message need not be compiler-generated.
The distinct-node premise is an application invariant, not a traffic bound. -/
theorem handle_refines (supported : SealedFragment G ty)
    (state : SealedProgram.State Player (L.Val ty)) (cfg : Config G)
    (hdecode : G.decodeSealed ty state = some cfg)
    (hnodup : (state.events.map SealedProgram.Event.node).Nodup)
    (message : Message Player (SealedProgram.Payload Player (L.Val ty))) :
    ∃ next : Config G,
      G.decodeSealed ty (SealedProgram.handle supported.compile state message) = some next ∧
      (next = cfg ∨ ∃ event : AvailableEvent G cfg,
        next ∈ (stepAvailableEvent G cfg event).support) := by
  have hcompleted (node : Fin G.nodeCount) :
      SealedProgram.done state.events node.val = true ↔ node ∈ cfg.done :=
    (Graph.mem_done_decodeSealed ty state cfg hdecode node).symm
  rcases message with ⟨⟨sender, serial⟩, payload⟩
  cases payload with
  | cleartext node value => exact ⟨cfg, hdecode, Or.inl rfl⟩
  | malformed => exact ⟨cfg, hdecode, Or.inl rfl⟩
  | commitment index handle =>
      simp only [SealedProgram.handle]
      split
      next rule hrule =>
        split
        next owner hkind =>
          split
          next hvalid =>
            rcases hvalid with ⟨howner, hhandle, hnotDone, hrequires, hstored⟩
            change sender = owner at howner
            subst sender handle
            rcases supported.ruleAt_commit hrule hkind with ⟨node, guard, rfl, hsem⟩
            have hcanonical : rule = G.sealedRule node :=
              Option.some.inj (hrule.symm.trans (supported.compile_rule node))
            have hready : Ready G cfg node := ready_of_messagePrerequisites
              state.events cfg node hcompleted hnotDone (by
                simpa only [SealedProgram.prerequisitesDone, hcanonical,
                  Graph.sealedRule] using hrequires)
            obtain ⟨value, hvalue⟩ := Option.isSome_iff_exists.mp hstored
            let event : AvailableEvent G cfg := .commit owner ⟨node, ⟨ty, value⟩⟩
              (supported.commitStep cfg node owner guard hsem hready value)
            refine ⟨cfg.completeNode node ⟨ty, value⟩, ?_, Or.inr ⟨event, ?_⟩⟩
            · change G.decodeSealedFrom ty state.service (Config.initial G)
                (state.events ++ [.accepted node.val (owner, node.val)]) = _
              rw [Graph.decodeSealedFrom_append]
              change (G.decodeSealed ty state).bind _ = _
              rw [hdecode]
              simp only [Option.bind_some, Graph.decodeSealedFrom,
                Graph.decodeSealedEvent_accepted, hvalue, Option.map_some]
            · change _ ∈ (stepCommit G cfg _).support
              rw [supported.stepCommit_commitStep]
              exact FinDist.mem_support_pure.mpr rfl
          next => exact ⟨cfg, hdecode, Or.inl rfl⟩
        all_goals exact ⟨cfg, hdecode, Or.inl rfl⟩
      next => exact ⟨cfg, hdecode, Or.inl rfl⟩
  | opening index handle claimed =>
      simp only [SealedProgram.handle]
      split
      next rule hrule =>
        split
        next owner source hkind =>
          split
          next hvalid =>
            rcases hvalid with ⟨howner, hhandle, hnotDone, hrequires, haccepted, hverifies⟩
            change sender = owner at howner
            subst sender handle
            rcases supported.ruleAt_reveal hrule hkind with
              ⟨node, producer, guard, rfl, rfl, hsem, hproducer⟩
            have hcanonical : rule = G.sealedRule node :=
              Option.some.inj (hrule.symm.trans (supported.compile_rule node))
            have hready : Ready G cfg node := ready_of_messagePrerequisites
              state.events cfg node hcompleted hnotDone (by
                simpa only [SealedProgram.prerequisitesDone, hcanonical,
                  Graph.sealedRule] using hrequires)
            have hvalue : state.service.lookup (owner, producer.val) = some claimed :=
              (IdealCommitments.verify_eq_true_iff state.service _).mp hverifies
            have hsource : Store.getAs cfg.store (G.nodeTarget producer) ty = some claimed := by
              rw [(Graph.decodeSealed_accepted_getAs ty state cfg producer
                (owner, producer.val) hnodup
                (SealedProgram.accepted_mem_of_accepted?_eq_some haccepted) hdecode).2]
              exact hvalue
            let event : AvailableEvent G cfg := .internal ⟨node⟩
              (supported.revealStep cfg node (G.nodeTarget producer) hsem hready claimed hsource)
            refine ⟨cfg.completeNode node ⟨ty, claimed⟩, ?_, Or.inr ⟨event, ?_⟩⟩
            · change G.decodeSealedFrom ty state.service (Config.initial G)
                (state.events ++ [.opened node.val claimed]) = _
              rw [Graph.decodeSealedFrom_append]
              change (G.decodeSealed ty state).bind _ = _
              rw [hdecode]
              simp only [Option.bind_some, Graph.decodeSealedFrom, Graph.decodeSealedEvent_opened]
            · change _ ∈ (stepInternal G cfg _).support
              rw [supported.stepInternal_revealStep]
              exact FinDist.mem_support_pure.mpr rfl
          next => exact ⟨cfg, hdecode, Or.inl rfl⟩
        all_goals exact ⟨cfg, hdecode, Or.inl rfl⟩
      next => exact ⟨cfg, hdecode, Or.inl rfl⟩

/-- Inclusion of an arbitrary preexisting message has the same graph-step
guarantee. Publication and rejection are retained in the native state. -/
theorem includePending_refines (supported : SealedFragment G ty)
    (state : SealedProgram.State Player (L.Val ty)) (cfg : Config G)
    (hdecode : G.decodeSealed ty state = some cfg)
    (hnodup : (state.events.map SealedProgram.Event.node).Nodup)
    (id : MessageId Player) :
    ∃ next : Config G,
      G.decodeSealed ty (SealedProgram.includePending supported.compile state id) = some next ∧
      (next = cfg ∨ ∃ event : AvailableEvent G cfg,
        next ∈ (stepAvailableEvent G cfg event).support) := by
  cases hlookup : state.pool.lookup id with
  | none =>
      refine ⟨cfg, ?_, Or.inl rfl⟩
      simpa [SealedProgram.includePending, MessagePool.includePending,
        MessagePool.Result.invalid, hlookup] using hdecode
  | some message =>
      rw [SealedProgram.includePending_of_lookup supported.compile state id message hlookup]
      exact supported.handle_refines
        { state with pool := (state.pool.includePending id).state } cfg hdecode hnodup message

/-- Every native action either stutters or takes a genuine graph step under
decoding. Registration may extend the private table but cannot rewrite a
previously accepted value. -/
theorem step_refines (supported : SealedFragment G ty)
    (state : SealedProgram.State Player (L.Val ty)) (cfg : Config G)
    (hdecode : G.decodeSealed ty state = some cfg)
    (hnodup : (state.events.map SealedProgram.Event.node).Nodup)
    (action : SealedProgram.Action Player (L.Val ty)) :
    ∃ next : Config G,
      G.decodeSealed ty (SealedProgram.step supported.compile state action) = some next ∧
      (next = cfg ∨ ∃ event : AvailableEvent G cfg,
        next ∈ (stepAvailableEvent G cfg event).support) := by
  cases action with
  | register owner slot value =>
      refine ⟨cfg, ?_, Or.inl rfl⟩
      exact Graph.decodeSealedFrom_of_lookup_extension ty state.service
        (state.service.sealValue owner slot value).state
        (fun handle stored hstored =>
          IdealCommitments.lookup_sealValue_of_eq_some state.service owner slot value
            handle stored hstored)
        (Config.initial G) cfg state.events hdecode
  | submit sender payload => exact ⟨cfg, hdecode, Or.inl rfl⟩
  | replay broadcaster id => exact ⟨cfg, hdecode, Or.inl rfl⟩
  | deliver observer id => exact ⟨cfg, hdecode, Or.inl rfl⟩
  | «include» id => exact supported.includePending_refines state cfg hdecode hnodup id

/-- Every finite native action sequence from a represented reachable graph
state decodes to a reachable graph state. No settlement or fairness is assumed. -/
theorem run_refines_from (supported : SealedFragment G ty)
    (state : SealedProgram.State Player (L.Val ty)) (cfg : Config G)
    (hdecode : G.decodeSealed ty state = some cfg)
    (hnodup : (state.events.map SealedProgram.Event.node).Nodup)
    (hreachable : Reachable G cfg)
    (actions : List (SealedProgram.Action Player (L.Val ty))) :
    ∃ result : Config G,
      G.decodeSealed ty (SealedProgram.run supported.compile state actions) = some result ∧
      Reachable G result := by
  induction actions generalizing state cfg with
  | nil => exact ⟨cfg, hdecode, hreachable⟩
  | cons action rest ih =>
      obtain ⟨next, hnext, hstep⟩ := supported.step_refines state cfg hdecode hnodup action
      have hnextReachable : Reachable G next := by
        rcases hstep with rfl | ⟨event, hevent⟩
        · exact hreachable
        · exact Reachable.step hreachable event hevent
      have hnextNodup : ((SealedProgram.step supported.compile state action).events.map
          SealedProgram.Event.node).Nodup := by
        exact SealedProgram.step_eventNodes_nodup supported.compile state action hnodup
      exact ih _ next hnext hnextNodup hnextReachable

/-- Operational prefix preservation for every finite native action sequence
of the compiled fragment, including arbitrary public submissions. The graph
may remain nonterminal if the sequence withholds required commitments or
openings. This statement quantifies over actions, not information-local player
strategies, and therefore does not assert strategic preservation. -/
theorem run_refines (supported : SealedFragment G ty)
    (actions : List (SealedProgram.Action Player (L.Val ty))) :
    ∃ result : Config G,
      G.decodeSealed ty (SealedProgram.run supported.compile
        (SealedProgram.State.empty Player (L.Val ty)) actions) = some result ∧
      Reachable G result :=
  supported.run_refines_from (SealedProgram.State.empty Player (L.Val ty))
    (Config.initial G) rfl (by exact List.nodup_nil) Reachable.initial actions

end Vegas.EventGraph.SealedFragment
