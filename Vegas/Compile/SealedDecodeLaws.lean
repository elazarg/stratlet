/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SealedDecode

/-! # Laws for proof-side sealed-event decoding -/

namespace Vegas.EventGraph.Graph

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}

private theorem decodeSealedEvent_node {G : Graph Player L} (ty : L.Ty)
    (service : IdealCommitments Player Nat (L.Val ty))
    (event : SealedProgram.Event Player (L.Val ty))
    (write : Fin G.nodeCount × TypedValue L)
    (hdecode : G.decodeSealedEvent ty service event = some write) :
    write.1.val = event.node := by
  unfold decodeSealedEvent at hdecode
  split at hdecode
  · cases event with
    | accepted node handle =>
        simp only [Option.map_eq_some_iff] at hdecode
        obtain ⟨value, _, rfl⟩ := hdecode
        rfl
    | opened node value =>
        simp only [Option.some.injEq] at hdecode
        subst write
        rfl
  · simp at hdecode

/-- Successful decoding records exactly the starting completed nodes and the
nodes named by the decoded events. -/
theorem mem_done_decodeSealedFrom {G : Graph Player L} (ty : L.Ty)
    (service : IdealCommitments Player Nat (L.Val ty))
    (cfg result : Config G) (events : List (SealedProgram.Event Player (L.Val ty)))
    (hdecode : G.decodeSealedFrom ty service cfg events = some result)
    (node : Fin G.nodeCount) :
    node ∈ result.done ↔
      node ∈ cfg.done ∨ SealedProgram.done events node.val = true := by
  induction events generalizing cfg with
  | nil =>
      simp only [decodeSealedFrom_nil, Option.some.injEq] at hdecode
      subst result
      simp
  | cons event rest ih =>
      simp only [decodeSealedFrom] at hdecode
      cases hevent : G.decodeSealedEvent ty service event with
      | none => simp [hevent] at hdecode
      | some write =>
          rw [hevent] at hdecode
          simp only [Option.bind_some] at hdecode
          have hwriteNode := decodeSealedEvent_node ty service event write hevent
          rw [ih _ hdecode]
          have heq : node = write.1 ↔ event.node = node.val := by
            constructor
            · intro h
              simpa [h] using hwriteNode.symm
            · intro h
              apply Fin.ext
              omega
          simp only [Config.completeNode, Finset.mem_insert,
            SealedProgram.done, List.any_cons, Bool.or_eq_true,
            beq_iff_eq, heq]
          tauto

/-- Decoding from the initial graph marks precisely the in-range event nodes. -/
theorem mem_done_decodeSealed {G : Graph Player L} (ty : L.Ty)
    (state : SealedProgram.State Player (L.Val ty)) (result : Config G)
    (hdecode : G.decodeSealed ty state = some result)
    (node : Fin G.nodeCount) :
    node ∈ result.done ↔ SealedProgram.done state.events node.val = true := by
  rw [decodeSealed] at hdecode
  simpa [Config.initial] using mem_done_decodeSealedFrom ty state.service (Config.initial G)
    result state.events hdecode node

/-- Decoding events at nodes other than `node` preserves its stored value. -/
theorem getAs_decodeSealedFrom_of_node_not_mem {G : Graph Player L} (ty : L.Ty)
    (service : IdealCommitments Player Nat (L.Val ty))
    (cfg result : Config G) (events : List (SealedProgram.Event Player (L.Val ty)))
    (node : Fin G.nodeCount)
    (hnotmem : node.val ∉ events.map SealedProgram.Event.node)
    (hdecode : G.decodeSealedFrom ty service cfg events = some result) :
    Store.getAs result.store (G.nodeTarget node) ty =
      Store.getAs cfg.store (G.nodeTarget node) ty := by
  induction events generalizing cfg with
  | nil =>
      simp only [decodeSealedFrom_nil, Option.some.injEq] at hdecode
      subst result
      rfl
  | cons event rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at hnotmem
      simp only [decodeSealedFrom] at hdecode
      cases hevent : G.decodeSealedEvent ty service event with
      | none => simp [hevent] at hdecode
      | some write =>
          rw [hevent] at hdecode
          simp only [Option.bind_some] at hdecode
          have hwriteNode := decodeSealedEvent_node ty service event write hevent
          have hne : G.nodeTarget node ≠ G.nodeTarget write.1 := by
            apply Config.nodeTarget_ne_of_ne
            intro heq
            apply hnotmem.1
            rw [← hwriteNode, heq]
          rw [ih (cfg.completeNode write.1 write.2) hnotmem.2 hdecode]
          exact Store.getAs_set_ne cfg.store hne write.2 ty

/-- An accepted event in a node-distinct trace decodes its private value and
that value remains at the producer's graph target. -/
theorem decodeSealedFrom_accepted_getAs {G : Graph Player L} (ty : L.Ty)
    (service : IdealCommitments Player Nat (L.Val ty))
    (cfg result : Config G) (events : List (SealedProgram.Event Player (L.Val ty)))
    (producer : Fin G.nodeCount) (handle : CommitmentHandle Player Nat)
    (hnodup : (events.map SealedProgram.Event.node).Nodup)
    (hmem : SealedProgram.Event.accepted producer.val handle ∈ events)
    (hdecode : G.decodeSealedFrom ty service cfg events = some result) :
    (service.lookup handle).isSome = true ∧
      Store.getAs result.store (G.nodeTarget producer) ty = service.lookup handle := by
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp hmem
  rw [decodeSealedFrom_append] at hdecode
  cases hbefore : G.decodeSealedFrom ty service cfg before with
  | none => simp [hbefore] at hdecode
  | some mid =>
      rw [hbefore] at hdecode
      simp only [Option.bind_some, decodeSealedFrom,
        decodeSealedEvent_accepted] at hdecode
      cases hlookup : service.lookup handle with
      | none => simp [hlookup] at hdecode
      | some value =>
          simp only [hlookup, Option.map_some, Option.bind_some] at hdecode
          have hafter : producer.val ∉ after.map SealedProgram.Event.node := by
            have hall : (before.map SealedProgram.Event.node ++
                producer.val :: after.map SealedProgram.Event.node).Nodup := by
              simpa [SealedProgram.Event.node] using hnodup
            exact (List.nodup_cons.1 (List.nodup_append.1 hall).2.1).1
          constructor
          · simp
          · rw [getAs_decodeSealedFrom_of_node_not_mem ty service
              (mid.completeNode producer ⟨ty, value⟩) result after producer
              hafter hdecode]
            simp [Config.completeNode, Store.getAs, TypedValue.as?]

/-- The accepted-value law specialized to decoding from the initial graph. -/
theorem decodeSealed_accepted_getAs {G : Graph Player L} (ty : L.Ty)
    (state : SealedProgram.State Player (L.Val ty)) (result : Config G)
    (producer : Fin G.nodeCount) (handle : CommitmentHandle Player Nat)
    (hnodup : (state.events.map SealedProgram.Event.node).Nodup)
    (hmem : SealedProgram.Event.accepted producer.val handle ∈ state.events)
    (hdecode : G.decodeSealed ty state = some result) :
    (state.service.lookup handle).isSome = true ∧
      Store.getAs result.store (G.nodeTarget producer) ty =
        state.service.lookup handle := by
  exact decodeSealedFrom_accepted_getAs ty state.service (Config.initial G)
    result state.events producer handle hnodup hmem hdecode

/-- Extending the ideal service without changing any occupied entry preserves
every successful decoding result. -/
theorem decodeSealedFrom_of_lookup_extension {G : Graph Player L} (ty : L.Ty)
    (service extended : IdealCommitments Player Nat (L.Val ty))
    (hlookup : ∀ handle value, service.lookup handle = some value →
      extended.lookup handle = some value)
    (cfg result : Config G) (events : List (SealedProgram.Event Player (L.Val ty)))
    (hdecode : G.decodeSealedFrom ty service cfg events = some result) :
    G.decodeSealedFrom ty extended cfg events = some result := by
  induction events generalizing cfg with
  | nil => exact hdecode
  | cons event rest ih =>
      simp only [decodeSealedFrom] at hdecode ⊢
      cases hevent : G.decodeSealedEvent ty service event with
      | none => simp [hevent] at hdecode
      | some write =>
          rw [hevent] at hdecode
          simp only [Option.bind_some] at hdecode
          have hextended : G.decodeSealedEvent ty extended event = some write := by
            unfold decodeSealedEvent at hevent ⊢
            split at hevent
            · rename_i hnode
              simp only [hnode, dite_true]
              cases event with
              | opened node value => exact hevent
              | accepted node handle =>
                  cases hservice : service.lookup handle with
                  | none => simp [hservice] at hevent
                  | some value =>
                      have hext := hlookup handle value hservice
                      simpa only [hservice, hext, Option.map_some,
                        Option.some.injEq] using hevent
            · simp at hevent
          rw [hextended]
          simp only [Option.bind_some]
          exact ih _ hdecode

end Vegas.EventGraph.Graph
