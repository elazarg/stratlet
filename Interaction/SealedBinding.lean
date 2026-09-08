/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedPersistence

/-! # Binding invariants for native sealed execution -/

namespace Interaction.SealedProgram

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]
variable {program : SealedProgram Principal} {state : State Principal Value}

/-- Accepted handles match their commit rule's canonical owner/node slot and
have a stored value. Opened values match their reveal rule's source slot.
Occupied slots remain immutable under further native execution. -/
structure BindingInvariant (program : SealedProgram Principal)
    (state : State Principal Value) : Prop where
  accepted : ∀ node handle, .accepted node handle ∈ state.events →
    ∃ owner requires value,
      program.rules[node]? = some { kind := .commit owner, requires } ∧
      handle = (owner, node) ∧ state.service.lookup handle = some value
  opened : ∀ node value, .opened node value ∈ state.events →
    ∃ owner source requires,
      program.rules[node]? = some { kind := .reveal owner source, requires } ∧
      state.service.lookup (owner, source) = some value

omit [DecidableEq Principal] [DecidableEq Value] in
theorem BindingInvariant.empty (program : SealedProgram Principal) :
    BindingInvariant program (State.empty Principal Value) := by
  constructor <;> simp [State.empty]

omit [DecidableEq Principal] [DecidableEq Value] in
private theorem BindingInvariant.copy (invariant : BindingInvariant program state)
    {next : State Principal Value} (hservice : next.service = state.service)
    (hevents : next.events = state.events) : BindingInvariant program next := by
  constructor
  · intro node handle hevent
    rw [hevents] at hevent
    obtain ⟨owner, requires, value, hrule, hhandle, hlookup⟩ :=
      invariant.accepted node handle hevent
    exact ⟨owner, requires, value, hrule, hhandle, by simpa [hservice] using hlookup⟩
  · intro node value hevent
    rw [hevents] at hevent
    obtain ⟨owner, source, requires, hrule, hlookup⟩ :=
      invariant.opened node value hevent
    exact ⟨owner, source, requires, hrule, by simpa [hservice] using hlookup⟩

private theorem BindingInvariant.handle_preserved (invariant : BindingInvariant program state)
    (message : Message Principal (Payload Principal Value)) :
    BindingInvariant program (handle program state message) := by
  rcases message with ⟨id, payload⟩
  cases payload with
  | commitment node commitmentHandle =>
      cases hrule : program.rules[node]? with
      | none => simpa [SealedProgram.handle, SealedProgram.validateMessage?, hrule] using invariant
      | some rule =>
          cases hkind : rule.kind with
          | reveal owner source => simpa [SealedProgram.handle, SealedProgram.validateMessage?, hrule, hkind] using invariant
          | disabled => simpa [SealedProgram.handle, SealedProgram.validateMessage?, hrule, hkind] using invariant
          | commit owner =>
              simp only [SealedProgram.handle, SealedProgram.validateMessage?, hrule, hkind]
              split
              next hvalid =>
                split at hvalid <;> try contradiction
                rename_i hchecks
                cases hvalid
                constructor
                · intro eventNode eventHandle hevent
                  simp only [List.mem_append, List.mem_singleton] at hevent
                  rcases hevent with hevent | hevent
                  · exact invariant.accepted eventNode eventHandle hevent
                  · cases hevent
                    have hoccupied := hchecks.2.2.2.2
                    cases hlookup : state.service.lookup commitmentHandle with
                    | none => simp [hlookup] at hoccupied
                    | some value =>
                        refine ⟨owner, rule.requires, value, ?_, hchecks.2.1, rfl⟩
                        have hruleShape :
                            rule = ({ kind := .commit owner, requires := rule.requires } :
                              SealedRule Principal) := by
                          cases rule
                          simp_all
                        rwa [← hruleShape]
                · intro eventNode value hevent
                  simp only [List.mem_append, List.mem_singleton] at hevent
                  rcases hevent with hevent | hevent
                  · exact invariant.opened eventNode value hevent
                  · contradiction
              next => exact invariant
  | opening node commitmentHandle claimed =>
      cases hrule : program.rules[node]? with
      | none => simpa [SealedProgram.handle, SealedProgram.validateMessage?, hrule] using invariant
      | some rule =>
          cases hkind : rule.kind with
          | commit owner => simpa [SealedProgram.handle, SealedProgram.validateMessage?, hrule, hkind] using invariant
          | disabled => simpa [SealedProgram.handle, SealedProgram.validateMessage?, hrule, hkind] using invariant
          | reveal owner source =>
              simp only [SealedProgram.handle, SealedProgram.validateMessage?, hrule, hkind]
              split
              next hvalid =>
                split at hvalid <;> try contradiction
                rename_i hchecks
                cases hvalid
                constructor
                · intro eventNode eventHandle hevent
                  simp only [List.mem_append, List.mem_singleton] at hevent
                  rcases hevent with hevent | hevent
                  · exact invariant.accepted eventNode eventHandle hevent
                  · contradiction
                · intro eventNode value hevent
                  simp only [List.mem_append, List.mem_singleton] at hevent
                  rcases hevent with hevent | hevent
                  · exact invariant.opened eventNode value hevent
                  · cases hevent
                    refine ⟨owner, source, rule.requires, ?_, ?_⟩
                    · have hruleShape :
                          rule = ({ kind := .reveal owner source, requires := rule.requires } :
                            SealedRule Principal) := by
                        cases rule
                        simp_all
                      rwa [← hruleShape]
                    · have hstored :=
                        (IdealCommitments.verify_eq_true_iff state.service _).mp
                          hchecks.2.2.2.2.2
                      simpa [hchecks.2.1] using hstored
              next => exact invariant
  | cleartext node value => simpa [SealedProgram.handle, SealedProgram.validateMessage?] using invariant
  | malformed => simpa [SealedProgram.handle, SealedProgram.validateMessage?] using invariant

theorem BindingInvariant.step (invariant : BindingInvariant program state)
    (action : Action Principal Value) :
    BindingInvariant program (step program state action) := by
  cases action with
  | register owner slot value =>
      constructor
      · intro node handle hevent
        obtain ⟨eventOwner, requires, stored, hrule, hhandle, hstored⟩ :=
          invariant.accepted node handle hevent
        exact ⟨eventOwner, requires, stored, hrule, hhandle,
          IdealCommitments.lookup_sealValue_of_eq_some
            state.service owner slot value handle stored hstored⟩
      · intro node openedValue hevent
        obtain ⟨eventOwner, source, requires, hrule, hstored⟩ :=
          invariant.opened node openedValue hevent
        exact ⟨eventOwner, source, requires, hrule,
          IdealCommitments.lookup_sealValue_of_eq_some state.service owner slot value
            (eventOwner, source) openedValue hstored⟩
  | submit sender payload => exact invariant.copy rfl rfl
  | replay broadcaster id => exact invariant.copy rfl rfl
  | deliver observer id => exact invariant.copy rfl rfl
  | «include» id =>
      simp only [SealedProgram.step]
      unfold includePending
      generalize hinc : state.pool.includePending id = included
      cases hm : included.message with
      | none =>
          dsimp only
          rw [hm]
          exact invariant.copy rfl rfl
      | some message =>
          dsimp only
          rw [hm]
          have hbase : BindingInvariant program { state with pool := included.state } :=
            invariant.copy rfl rfl
          exact hbase.handle_preserved message

theorem BindingInvariant.run (invariant : BindingInvariant program state)
    (actions : List (Action Principal Value)) :
    BindingInvariant program (run program state actions) := by
  induction actions generalizing state with
  | nil => exact invariant
  | cons action rest ih => exact ih (invariant.step action)

omit [DecidableEq Principal] [DecidableEq Value] in
/-- At a commit node, completion can only be its canonical acceptance event. -/
theorem BindingInvariant.accepted_mem_of_done_commit
    (invariant : BindingInvariant program state) (node : Nat) (owner : Principal)
    (requires : List Nat)
    (hrule : program.rules[node]? = some { kind := .commit owner, requires })
    (hdone : done state.events node = true) :
    .accepted node (owner, node) ∈ state.events := by
  unfold done at hdone
  rw [List.any_eq_true] at hdone
  obtain ⟨event, hevent, hnode⟩ := hdone
  have heq : event.node = node := by simpa using hnode
  cases event with
  | accepted eventNode handle =>
      simp only [Event.node] at heq
      subst eventNode
      obtain ⟨eventOwner, eventRequires, value, heventRule, hhandle, hlookup⟩ :=
        invariant.accepted node handle hevent
      rw [hrule] at heventRule
      simp only [Option.some.injEq, SealedRule.mk.injEq,
        SealedRuleKind.commit.injEq] at heventRule
      have howner : owner = eventOwner := heventRule.1
      subst eventOwner
      subst handle
      exact hevent
  | opened eventNode value =>
      simp only [Event.node] at heq
      subst eventNode
      obtain ⟨eventOwner, source, eventRequires, heventRule, hlookup⟩ :=
        invariant.opened node value hevent
      rw [hrule] at heventRule
      simp at heventRule

omit [DecidableEq Principal] [DecidableEq Value] in
/-- Consequently a completed commit node has an immutable stored value at its
canonical owner/node handle. -/
theorem BindingInvariant.done_commit_lookup
    (invariant : BindingInvariant program state) (node : Nat) (owner : Principal)
    (requires : List Nat)
    (hrule : program.rules[node]? = some { kind := .commit owner, requires })
    (hdone : done state.events node = true) :
    ∃ value, state.service.lookup (owner, node) = some value := by
  have hmem := invariant.accepted_mem_of_done_commit node owner requires hrule hdone
  obtain ⟨eventOwner, eventRequires, value, heventRule, hhandle, hlookup⟩ :=
    invariant.accepted node (owner, node) hmem
  exact ⟨value, hlookup⟩

theorem run_empty_accepted_mem_lookup
    (program : SealedProgram Principal) (actions : List (Action Principal Value))
    (node : Nat) (handle : CommitmentHandle Principal Nat)
    (haccepted : .accepted node handle ∈
      (run program (State.empty Principal Value) actions).events) :
    ∃ value, (run program (State.empty Principal Value) actions).service.lookup handle = some value := by
  obtain ⟨owner, requires, value, hrule, hhandle, hlookup⟩ :=
    ((BindingInvariant.empty program).run actions).accepted node handle haccepted
  exact ⟨value, hlookup⟩

theorem run_empty_accepted?_lookup
    (program : SealedProgram Principal) (actions : List (Action Principal Value))
    (node : Nat) (handle : CommitmentHandle Principal Nat)
    (haccepted : accepted? (run program (State.empty Principal Value) actions).events node =
      some handle) :
    ∃ value, (run program (State.empty Principal Value) actions).service.lookup handle = some value :=
  run_empty_accepted_mem_lookup program actions node handle
    (accepted_mem_of_accepted?_eq_some haccepted)

theorem run_empty_opened_mem_lookup
    (program : SealedProgram Principal) (actions : List (Action Principal Value))
    (node : Nat) (value : Value)
    (hopened : .opened node value ∈
      (run program (State.empty Principal Value) actions).events) :
    ∃ owner source requires,
      program.rules[node]? = some { kind := .reveal owner source, requires } ∧
      (run program (State.empty Principal Value) actions).service.lookup
        (owner, source) = some value :=
  ((BindingInvariant.empty program).run actions).opened node value hopened

end Interaction.SealedProgram
