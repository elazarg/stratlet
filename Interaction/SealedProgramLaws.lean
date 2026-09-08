/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedProgram

/-! # Laws for finite sealed-message programs -/

namespace Interaction.SealedProgram

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

/-- A valid commitment message appends exactly its opaque acceptance event. -/
theorem handle_commitment_of_valid [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (state : State Principal Value)
    (owner : Principal) (node serial : Nat) (value : Value) (requires : List Nat)
    (hrule : program.rules[node]? = some { kind := .commit owner, requires })
    (hnotDone : done state.events node = false)
    (hrequires : requires.all (done state.events) = true)
    (hstored : state.service.lookup (owner, node) = some value) :
    handle program state
        ⟨(owner, serial), .commitment node (owner, node)⟩ =
      { state with events := state.events ++ [.accepted node (owner, node)] } := by
  simp [handle, Message.sender, hrule, hnotDone, prerequisitesDone, hrequires, hstored]

/-- A valid claimed opening appends exactly its public opened-value event. -/
theorem handle_opening_of_valid [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (state : State Principal Value)
    (owner : Principal) (source node serial : Nat) (claimed : Value)
    (requires : List Nat)
    (hrule : program.rules[node]? =
      some { kind := .reveal owner source, requires })
    (hnotDone : done state.events node = false)
    (hrequires : requires.all (done state.events) = true)
    (haccepted : accepted? state.events source = some (owner, source))
    (hverifies : state.service.verify ⟨(owner, source), claimed⟩ = true) :
    handle program state
        ⟨(owner, serial), .opening node (owner, source) claimed⟩ =
      { state with events := state.events ++ [.opened node claimed] } := by
  simp [handle, Message.sender, hrule, hnotDone, prerequisitesDone, hrequires,
    haccepted, hverifies]

/-- Application handling never changes the private ideal service. -/
theorem handle_preserves_service [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (state : State Principal Value)
    (message : Message Principal (Payload Principal Value)) :
    (handle program state message).service = state.service := by
  rcases message with ⟨id, payload⟩
  cases payload <;> simp only [handle]
  all_goals split <;> try rfl
  all_goals split <;> try rfl
  all_goals split <;> rfl

/-- Application handling never changes message-pool state. -/
theorem handle_preserves_pool [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (state : State Principal Value)
    (message : Message Principal (Payload Principal Value)) :
    (handle program state message).pool = state.pool := by
  rcases message with ⟨id, payload⟩
  cases payload <;> simp only [handle]
  all_goals split <;> try rfl
  all_goals split <;> try rfl
  all_goals split <;> rfl

/-- When a pending message exists, inclusion is exactly ordinary pool
inclusion followed by the application handler on that preexisting message. -/
theorem includePending_of_lookup [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (state : State Principal Value)
    (id : MessageId Principal) (message : Message Principal (Payload Principal Value))
    (hlookup : state.pool.lookup id = some message) :
    includePending program state id =
      handle program { state with pool := (state.pool.includePending id).state } message := by
  simp [includePending, MessagePool.includePending, hlookup]

/-- A generated opening request certifies all of its public controller checks:
the rule, owner, fresh reveal node, completed prerequisites, and accepted source
handle. -/
theorem openingRequest?_sound [DecidableEq Principal]
    (program : SealedProgram Principal) (events : List (Event Principal Value))
    (owner : Principal) (node source : Nat) (claimed : Value)
    (hrequest : openingRequest? program events owner node claimed =
      some (.opening node (owner, source) claimed)) :
    ∃ requires,
      program.rules[node]? = some { kind := .reveal owner source, requires } ∧
      done events node = false ∧
      requires.all (done events) = true ∧
      accepted? events source = some (owner, source) := by
  unfold openingRequest? at hrequest
  split at hrequest
  next rule hrule =>
    split at hrequest
    next expectedOwner source' hkind =>
      split at hrequest
      next hvalid =>
        simp only [Option.some.injEq, Payload.opening.injEq] at hrequest
        rcases hvalid with ⟨howner, hnotDone, hrequires, haccepted⟩
        have hsource : source' = source := congrArg Prod.snd hrequest.2.1
        subst owner
        subst source
        refine ⟨rule.requires, ?_, hnotDone, ?_, haccepted⟩
        · have hruleShape :
              rule = { kind := .reveal expectedOwner source', requires := rule.requires } := by
            cases rule
            simp_all
          rw [← hruleShape]
          exact hrule
        · exact hrequires
      next => contradiction
    all_goals contradiction
  next => contradiction

/-- A successful accepted-handle query is witnessed by the corresponding
acceptance event in the public application log. -/
theorem accepted_mem_of_accepted?_eq_some
    {events : List (Event Principal Value)} {node : Nat}
    {handle : CommitmentHandle Principal Nat}
    (haccepted : accepted? events node = some handle) :
    Event.accepted node handle ∈ events := by
  rcases List.exists_of_findSome?_eq_some haccepted with ⟨event, hevent, hmatch⟩
  cases event with
  | accepted eventNode eventHandle =>
      simp only at hmatch
      split at hmatch
      · rename_i hnode
        have hhandle := Option.some.inj hmatch
        subst eventNode
        subst eventHandle
        exact hevent
      · contradiction
  | opened eventNode value => simp at hmatch

private theorem eventNodes_nodup_append
    {events : List (Event Principal Value)} {event : Event Principal Value}
    (hnodup : (events.map Event.node).Nodup)
    (hnotDone : done events event.node = false) :
    ((events ++ [event]).map Event.node).Nodup := by
  rw [List.map_append]
  rw [List.nodup_append]
  refine ⟨hnodup, by simp, ?_⟩
  intro node hnode eventNode hevent
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hevent
  subst eventNode
  intro heq
  subst node
  rcases List.mem_map.mp hnode with ⟨prior, hprior, hpriorNode⟩
  have hdone : done events event.node = true := by
    unfold done
    rw [List.any_eq_true]
    exact ⟨prior, hprior, by simpa using hpriorNode⟩
  rw [hnotDone] at hdone
  contradiction

/-- Handling preserves uniqueness of completed application node ids. -/
theorem handle_eventNodes_nodup [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (state : State Principal Value)
    (message : Message Principal (Payload Principal Value))
    (hnodup : (state.events.map Event.node).Nodup) :
    ((handle program state message).events.map Event.node).Nodup := by
  rcases message with ⟨id, payload⟩
  cases payload <;> simp only [handle]
  case commitment =>
    split <;> try exact hnodup
    split <;> try exact hnodup
    split
    · rename_i hvalid
      exact eventNodes_nodup_append hnodup hvalid.2.2.1
    · exact hnodup
  case opening =>
    split <;> try exact hnodup
    split <;> try exact hnodup
    split
    · rename_i hvalid
      exact eventNodes_nodup_append hnodup hvalid.2.2.1
    · exact hnodup
  case cleartext => exact hnodup
  case malformed => exact hnodup

/-- Native inclusion preserves uniqueness of completed application node ids. -/
theorem includePending_eventNodes_nodup [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (state : State Principal Value)
    (id : MessageId Principal) (hnodup : (state.events.map Event.node).Nodup) :
    ((includePending program state id).events.map Event.node).Nodup := by
  unfold includePending
  generalize state.pool.includePending id = included
  cases hmessage : included.message with
  | some message =>
      simp only [hmessage]
      exact handle_eventNodes_nodup program _ message hnodup
  | none =>
      simp only [hmessage]
      exact hnodup

end Interaction.SealedProgram
