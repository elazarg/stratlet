/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SealedMessages

/-! # Proof-side decoding of sealed application events

Decoding consults the private ideal commitment table to recover the value of an
accepted commitment. This is an abstraction map, not a player observation or
an operation available to an arbitrary runtime controller. An invalid event
index or missing private entry produces `none`.

The decoder reconstructs graph configurations; legal graph execution is a
separate obligation. In particular, arbitrary lists of decoded writes need
not respect the graph's prerequisites or execute an event only once.
-/

namespace Vegas.EventGraph.Graph

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Interpret a runtime application event as a typed graph write. -/
def decodeSealedEvent (G : Graph Player L) (ty : L.Ty)
    (service : IdealCommitments Player Nat (L.Val ty))
    (event : SealedProgram.Event Player (L.Val ty)) :
    Option (Fin G.nodeCount × TypedValue L) :=
  if hnode : event.node < G.nodeCount then
    match event with
    | .accepted _ handle =>
        (service.lookup handle).map fun value => (⟨_, hnode⟩, ⟨ty, value⟩)
    | .opened _ value => some (⟨_, hnode⟩, ⟨ty, value⟩)
  else none

/-- Decode an event sequence from a specified starting graph configuration. -/
def decodeSealedFrom (G : Graph Player L) (ty : L.Ty)
    (service : IdealCommitments Player Nat (L.Val ty))
    (cfg : Config G) : List (SealedProgram.Event Player (L.Val ty)) → Option (Config G)
  | [] => some cfg
  | event :: rest =>
      (G.decodeSealedEvent ty service event).bind fun write =>
        G.decodeSealedFrom ty service (cfg.completeNode write.1 write.2) rest

/-- The initial graph store is the one emitted by the source compiler. -/
def decodeSealed (G : Graph Player L) (ty : L.Ty)
    (state : SealedProgram.State Player (L.Val ty)) : Option (Config G) :=
  G.decodeSealedFrom ty state.service (Config.initial G) state.events

@[simp] theorem decodeSealedEvent_accepted (G : Graph Player L) (ty : L.Ty)
    (service : IdealCommitments Player Nat (L.Val ty))
    (node : Fin G.nodeCount) (handle : CommitmentHandle Player Nat) :
    G.decodeSealedEvent ty service (.accepted node.val handle) =
      (service.lookup handle).map (fun value => (node, ⟨ty, value⟩)) := by
  simp [decodeSealedEvent, SealedProgram.Event.node, node.isLt]

@[simp] theorem decodeSealedEvent_opened (G : Graph Player L) (ty : L.Ty)
    (service : IdealCommitments Player Nat (L.Val ty))
    (node : Fin G.nodeCount) (value : L.Val ty) :
    G.decodeSealedEvent ty service (.opened node.val value) =
      some (node, ⟨ty, value⟩) := by
  simp [decodeSealedEvent, SealedProgram.Event.node, node.isLt]

@[simp] theorem decodeSealedFrom_nil (G : Graph Player L) (ty : L.Ty)
    (service : IdealCommitments Player Nat (L.Val ty)) (cfg : Config G) :
    G.decodeSealedFrom ty service cfg [] = some cfg := rfl

theorem decodeSealedFrom_append (G : Graph Player L) (ty : L.Ty)
    (service : IdealCommitments Player Nat (L.Val ty)) (cfg : Config G)
    (before after : List (SealedProgram.Event Player (L.Val ty))) :
    G.decodeSealedFrom ty service cfg (before ++ after) =
      (G.decodeSealedFrom ty service cfg before).bind
        (fun mid => G.decodeSealedFrom ty service mid after) := by
  induction before generalizing cfg with
  | nil => rfl
  | cons event rest ih =>
      simp only [List.cons_append, decodeSealedFrom]
      cases G.decodeSealedEvent ty service event with
      | none => rfl
      | some write => exact ih _

/-- Equal application events and private values decode identically regardless
of the pending pool, delivery history, or rejected ledger messages. -/
theorem decodeSealed_eq_of_application_eq (G : Graph Player L) (ty : L.Ty)
    (left right : SealedProgram.State Player (L.Val ty))
    (hservice : left.service = right.service) (hevents : left.events = right.events) :
    G.decodeSealed ty left = G.decodeSealed ty right := by
  simp only [decodeSealed, hservice, hevents]

end Vegas.EventGraph.Graph
