/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageReplay
import Interaction.SealedExecution
import Interaction.SealedProgramLaws

/-! # Pre-disclosure hiding for the ideal sealed runtime

This file gives a relational, information-theoretic law for the ideal service.
It is deliberately not a cryptographic hiding theorem. Two states may differ in
the values privately registered by one protected principal, but have identical
wire carrier and application state. The carrier invariant rules out an
opening authored by that principal anywhere it can later be delivered, replayed,
or included.
-/

namespace Interaction.SealedProgram

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable {hiddenOwner : Principal}
variable {left right : State Principal Value}
variable {pool : MessagePool Principal (Payload Principal Value)}

/-- The carrier invariant excludes openings authored by the protected
principal. Other payloads, including cleartext, are handled by equality of the
paired carrier states; this predicate alone does not assert their secrecy. -/
def MessageSafe (hiddenOwner : Principal) (message : Message Principal (Payload Principal Value)) :
    Prop :=
  match message.payload with
  | .opening _ _ _ => message.sender ≠ hiddenOwner
  | _ => True

/-- Every message retained by the carrier is safe for pre-disclosure reasoning. -/
def PoolSafe (hiddenOwner : Principal) (pool : MessagePool Principal (Payload Principal Value)) :
    Prop :=
  (∀ message, message ∈ pool.pending → MessageSafe hiddenOwner message) ∧
  (∀ message, message ∈ pool.ledger → MessageSafe hiddenOwner message) ∧
  (∀ who message, message ∈ pool.inbox who → MessageSafe hiddenOwner message) ∧
  (∀ who message, message ∈ pool.sent who → MessageSafe hiddenOwner message)

/-- Services agree away from the protected owner and agree on occupancy
everywhere. Values in occupied protected-owner slots may differ. -/
def ServiceAgreement (hiddenOwner : Principal)
    (left right : IdealCommitments Principal Nat Value) : Prop :=
  (∀ handle, handle.1 ≠ hiddenOwner → left.lookup handle = right.lookup handle) ∧
  (∀ handle, (left.lookup handle).isSome = (right.lookup handle).isSome)

/-- Two raw states have the same wire/application state and differ, if at all,
only in the protected principal's undisclosed registered values. -/
structure HidingRelated (hiddenOwner : Principal) (left right : State Principal Value) : Prop where
  service : ServiceAgreement hiddenOwner left.service right.service
  pool : left.pool = right.pool
  events : left.events = right.events
  safe : PoolSafe hiddenOwner left.pool

theorem HidingRelated.observe_eq (related : HidingRelated hiddenOwner left right)
    (who : Principal) : left.observe who = right.observe who := by
  simp [State.observe, related.pool, related.events]

@[simp] theorem poolSafe_empty (hiddenOwner : Principal) :
    PoolSafe hiddenOwner (MessagePool.empty Principal (Payload Principal Value)) := by
  simp [PoolSafe, MessagePool.empty]

@[simp] theorem serviceAgreement_empty (hiddenOwner : Principal) :
    ServiceAgreement hiddenOwner
      (IdealCommitments.empty : IdealCommitments Principal Nat Value)
      IdealCommitments.empty := by
  simp [ServiceAgreement]

theorem hidingRelated_empty (hiddenOwner : Principal) :
    HidingRelated hiddenOwner (State.empty Principal Value) (State.empty Principal Value) := by
  exact ⟨serviceAgreement_empty hiddenOwner, rfl, rfl, poolSafe_empty hiddenOwner⟩

/-- Registering and submitting the first protected commitment from an empty
state exposes the same handle and carrier state for any two secret values. -/
theorem submitCommit_empty_related [DecidableEq Principal]
    (hiddenOwner : Principal) (slot : Nat) (leftValue rightValue : Value) :
    HidingRelated hiddenOwner
      (submitCommit (State.empty Principal Value) hiddenOwner slot leftValue).2
      (submitCommit (State.empty Principal Value) hiddenOwner slot rightValue).2 := by
  constructor
  · constructor
    · intro handle haway
      dsimp [submitCommit, State.empty, IdealCommitments.sealValue,
        IdealCommitments.empty, IdealCommitments.lookup]
      by_cases heq : handle.1 = hiddenOwner ∧ handle.2 = slot
      · exact False.elim (haway heq.1)
      · simp [heq]
    · intro handle
      dsimp [submitCommit, State.empty, IdealCommitments.sealValue,
        IdealCommitments.empty, IdealCommitments.lookup]
      by_cases heq : handle.1 = hiddenOwner ∧ handle.2 = slot <;> simp [heq]
  · rfl
  · rfl
  · dsimp [submitCommit, State.empty, MessagePool.submit, MessagePool.empty, PoolSafe]
    constructor
    · intro message hmem
      simp only [List.mem_singleton] at hmem
      subst message
      simp [MessageSafe]
    constructor
    · simp
    constructor
    · simp
    · intro who message hmem
      by_cases hwho : who = hiddenOwner
      · subst who
        simp only [if_pos, List.mem_singleton] at hmem
        subst message
        simp [MessageSafe]
      · simp [hwho] at hmem

private theorem serviceAgreement_seal_other [DecidableEq Principal]
    (leftService rightService : IdealCommitments Principal Nat Value)
    (agreement : ServiceAgreement hiddenOwner leftService rightService) (owner : Principal)
    (slot : Nat) (value : Value) (hne : owner ≠ hiddenOwner) :
    ServiceAgreement hiddenOwner
      (leftService.sealValue owner slot value).state
      (rightService.sealValue owner slot value).state := by
  rcases agreement with ⟨haway, hoccupied⟩
  constructor
  · intro handle hhandle
    unfold IdealCommitments.sealValue
    have hslotEq := haway (owner, slot) hne
    change leftService.table owner slot = rightService.table owner slot at hslotEq
    rw [hslotEq]
    split
    · exact haway handle hhandle
    · by_cases heq : handle.1 = owner ∧ handle.2 = slot
      · simp [IdealCommitments.lookup, heq]
      · simp [IdealCommitments.lookup, heq]
        exact haway handle hhandle
  · intro handle
    unfold IdealCommitments.sealValue
    have hslot := hoccupied (owner, slot)
    cases hleft : leftService.table owner slot <;>
      cases hright : rightService.table owner slot <;>
      simp [IdealCommitments.lookup, hleft, hright] at hslot ⊢
    · by_cases heq : handle.1 = owner ∧ handle.2 = slot
      · simp [heq]
      · simpa [heq, IdealCommitments.lookup] using hoccupied handle
    · exact hoccupied handle

private theorem poolSafe_submit [DecidableEq Principal]
    (safe : PoolSafe hiddenOwner pool) (sender : Principal) (payload : Payload Principal Value)
    (hsender : sender ≠ hiddenOwner) :
    PoolSafe hiddenOwner (pool.submit sender payload).2 := by
  rcases safe with ⟨hpending, hledger, hinbox, hsent⟩
  constructor
  · intro message hmem
    simp only [MessagePool.submit, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · exact hpending message hmem
    · cases payload <;> simp [MessageSafe, Message.sender, hsender]
  constructor
  · exact hledger
  constructor
  · exact hinbox
  · intro who message hmem
    simp only [MessagePool.submit] at hmem
    split at hmem
    · rename_i hwho
      subst who
      simp only [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | rfl
      · exact hsent sender message hmem
      · cases payload <;> simp [MessageSafe, Message.sender, hsender]
    · exact hsent who message hmem

private theorem poolSafe_deliver [DecidableEq Principal]
    (safe : PoolSafe hiddenOwner pool) (observer : Principal) (id : MessageId Principal) :
    PoolSafe hiddenOwner (pool.deliver observer id).state := by
  rcases safe with ⟨hpending, hledger, hinbox, hsent⟩
  unfold MessagePool.deliver
  split
  · rename_i message hlookup
    have hmessage : MessageSafe hiddenOwner message :=
      hpending message (List.mem_of_find?_eq_some hlookup)
    exact ⟨hpending, hledger, by
      intro who candidate hmem
      by_cases hwho : who = observer
      · subst who
        simp only [if_pos, List.mem_append, List.mem_singleton] at hmem
        exact hmem.elim (hinbox observer candidate) (fun h => h ▸ hmessage)
      · simp only [if_neg hwho] at hmem
        exact hinbox who candidate hmem, hsent⟩
  · exact ⟨hpending, hledger, hinbox, hsent⟩

private theorem poolSafe_replay [DecidableEq Principal]
    (safe : PoolSafe hiddenOwner pool) (broadcaster : Principal) (id : MessageId Principal) :
    PoolSafe hiddenOwner (pool.replay broadcaster id).state := by
  rcases safe with ⟨hpending, hledger, hinbox, hsent⟩
  unfold MessagePool.replay MessagePool.View.known?
  split
  · rename_i message hknown
    have hmem := List.mem_of_find?_eq_some hknown
    simp only [List.mem_append] at hmem
    have hmessage : MessageSafe hiddenOwner message := by
      rcases hmem with (hsentMem | hinboxMem) | hledgerMem
      · exact hsent broadcaster message hsentMem
      · exact hinbox broadcaster message hinboxMem
      · exact hledger message hledgerMem
    exact ⟨by
      intro candidate hmem
      simp only [List.mem_append, List.mem_singleton] at hmem
      exact hmem.elim (hpending candidate) (fun h => h ▸ hmessage), hledger, hinbox, by
      intro who candidate hmem
      by_cases hwho : who = broadcaster
      · subst who
        simp only [if_pos, List.mem_append, List.mem_singleton] at hmem
        exact hmem.elim (hsent broadcaster candidate) (fun h => h ▸ hmessage)
      · simp only [if_neg hwho] at hmem
        exact hsent who candidate hmem⟩
  · exact ⟨hpending, hledger, hinbox, hsent⟩

private theorem mem_of_mem_removeFirst [DecidableEq Principal]
    (id : MessageId Principal) (candidate : Message Principal (Payload Principal Value))
    (messages : List (Message Principal (Payload Principal Value))) :
    candidate ∈ MessagePool.removeFirst id messages → candidate ∈ messages := by
  induction messages with
  | nil => simp [MessagePool.removeFirst]
  | cons head tail ih =>
      simp only [MessagePool.removeFirst]
      split
      · exact fun h => List.mem_cons_of_mem head h
      · simp only [List.mem_cons]
        exact fun h => h.elim Or.inl (fun ht => Or.inr (ih ht))

private theorem poolSafe_include [DecidableEq Principal]
    (safe : PoolSafe hiddenOwner pool) (id : MessageId Principal) :
    PoolSafe hiddenOwner (pool.includePending id).state := by
  rcases safe with ⟨hpending, hledger, hinbox, hsent⟩
  unfold MessagePool.includePending
  split
  · rename_i message hlookup
    have hmessage := hpending message (List.mem_of_find?_eq_some hlookup)
    exact ⟨by
      intro candidate hmem
      apply hpending candidate
      exact mem_of_mem_removeFirst id candidate pool.pending hmem, by
      intro candidate hmem
      simp only [List.mem_append, List.mem_singleton] at hmem
      exact hmem.elim (hledger candidate) (fun h => h ▸ hmessage), hinbox, hsent⟩
  · exact ⟨hpending, hledger, hinbox, hsent⟩

theorem HidingRelated.register [DecidableEq Principal]
    (related : HidingRelated hiddenOwner left right) (owner : Principal)
    (slot : Nat) (value : Value) (hne : owner ≠ hiddenOwner) :
    HidingRelated hiddenOwner
      { left with service := (left.service.sealValue owner slot value).state }
      { right with service := (right.service.sealValue owner slot value).state } := by
  exact ⟨serviceAgreement_seal_other left.service right.service related.service owner slot value hne,
    related.pool, related.events, related.safe⟩

theorem HidingRelated.submit [DecidableEq Principal]
    (related : HidingRelated hiddenOwner left right) (sender : Principal)
    (payload : Payload Principal Value) (hne : sender ≠ hiddenOwner) :
    HidingRelated hiddenOwner
      { left with pool := (left.pool.submit sender payload).2 }
      { right with pool := (right.pool.submit sender payload).2 } := by
  have hpool : (left.pool.submit sender payload).2 =
      (right.pool.submit sender payload).2 := by rw [related.pool]
  exact ⟨related.service, hpool, related.events,
    poolSafe_submit related.safe sender payload hne⟩

theorem HidingRelated.replay [DecidableEq Principal]
    (related : HidingRelated hiddenOwner left right) (broadcaster : Principal)
    (id : MessageId Principal) :
    HidingRelated hiddenOwner
      { left with pool := (left.pool.replay broadcaster id).state }
      { right with pool := (right.pool.replay broadcaster id).state } := by
  have hpool : (left.pool.replay broadcaster id).state =
      (right.pool.replay broadcaster id).state := by rw [related.pool]
  exact ⟨related.service, hpool, related.events,
    poolSafe_replay related.safe broadcaster id⟩

theorem HidingRelated.deliver [DecidableEq Principal]
    (related : HidingRelated hiddenOwner left right) (observer : Principal)
    (id : MessageId Principal) :
    HidingRelated hiddenOwner
      { left with pool := (left.pool.deliver observer id).state }
      { right with pool := (right.pool.deliver observer id).state } := by
  have hpool : (left.pool.deliver observer id).state =
      (right.pool.deliver observer id).state := by rw [related.pool]
  exact ⟨related.service, hpool, related.events,
    poolSafe_deliver related.safe observer id⟩

private theorem handle_events_eq [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (related : HidingRelated hiddenOwner left right)
    (message : Message Principal (Payload Principal Value))
    (safeMessage : MessageSafe hiddenOwner message) :
    (handle program left message).events = (handle program right message).events := by
  rcases related.service with ⟨haway, hoccupied⟩
  cases message with
  | mk id payload =>
    cases payload with
    | commitment node commitmentHandle =>
        cases hrule : program.rules[node]? with
        | none => simp [handle, hrule, related.events]
        | some rule =>
          cases hkind : rule.kind with
          | commit owner =>
              simp only [handle, hrule, hkind]
              rw [related.events, hoccupied commitmentHandle]
              split
              · rfl
              · exact related.events
          | reveal owner source => simp [handle, hrule, hkind, related.events]
          | disabled => simp [handle, hrule, hkind, related.events]
    | opening node commitmentHandle claimed =>
        have hsender : id.1 ≠ hiddenOwner := safeMessage
        cases hrule : program.rules[node]? with
        | none => simp [handle, hrule, related.events]
        | some rule =>
          cases hkind : rule.kind with
          | commit owner => simp [handle, hrule, hkind, related.events]
          | disabled => simp [handle, hrule, hkind, related.events]
          | reveal owner source =>
            by_cases howner : id.1 = owner
            · have hownerAway : owner ≠ hiddenOwner := by
                intro heq
                exact hsender (howner.trans heq)
              by_cases hhandle : commitmentHandle = (owner, source)
              · have hlookup := haway commitmentHandle (hhandle ▸ hownerAway)
                have hverify : left.service.verify ⟨commitmentHandle, claimed⟩ =
                    right.service.verify ⟨commitmentHandle, claimed⟩ := by
                  simp [IdealCommitments.verify, hlookup]
                simp only [handle, hrule, hkind]
                rw [related.events, hverify]
                split
                · rfl
                · exact related.events
              · simp [handle, hrule, hkind, related.events, hhandle]
            · simp [handle, hrule, hkind, related.events, Message.sender, howner]
    | cleartext node value => simp [handle, related.events]
    | malformed => simp [handle, related.events]

private theorem HidingRelated.handle [DecidableEq Principal] [DecidableEq Value]
    (related : HidingRelated hiddenOwner left right) (program : SealedProgram Principal)
    (message : Message Principal (Payload Principal Value))
    (safeMessage : MessageSafe hiddenOwner message) :
    HidingRelated hiddenOwner (handle program left message) (handle program right message) := by
  refine ⟨?_, ?_, handle_events_eq program related message safeMessage, ?_⟩
  · simpa only [handle_preserves_service] using related.service
  · simpa only [handle_preserves_pool] using related.pool
  · simpa only [handle_preserves_pool] using related.safe

/-- Inclusion may publish and apply a safe preexisting message, but cannot
distinguish the protected principal's registered values. -/
theorem HidingRelated.includePending [DecidableEq Principal] [DecidableEq Value]
    (related : HidingRelated hiddenOwner left right) (program : SealedProgram Principal)
    (id : MessageId Principal) :
    HidingRelated hiddenOwner
      (includePending program left id) (includePending program right id) := by
  cases hleftLookup : left.pool.lookup id with
  | none =>
    have hrightLookup : right.pool.lookup id = none := by
      rw [← related.pool]
      exact hleftLookup
    simp only [SealedProgram.includePending, MessagePool.includePending, hleftLookup,
      hrightLookup, MessagePool.Result.invalid]
    exact related
  | some message =>
    have hrightLookup : right.pool.lookup id = some message := by
      rw [← related.pool]
      exact hleftLookup
    have hmessage : MessageSafe hiddenOwner message :=
      related.safe.1 message (List.mem_of_find?_eq_some hleftLookup)
    have hpool : (left.pool.includePending id).state =
        (right.pool.includePending id).state := by rw [related.pool]
    have includedRelated : HidingRelated hiddenOwner
        { left with pool := (left.pool.includePending id).state }
        { right with pool := (right.pool.includePending id).state } :=
      ⟨related.service, hpool, related.events, poolSafe_include related.safe id⟩
    rw [includePending_of_lookup program left id message hleftLookup,
      includePending_of_lookup program right id message hrightLookup]
    exact includedRelated.handle program message hmessage

/-- Native actions allowed while the protected principal withholds disclosure.
Other principals may submit arbitrary payloads and register arbitrary values;
carrier replay, delivery, and inclusion remain unrestricted. -/
def AllowedBeforeDisclosure (hiddenOwner : Principal) : Action Principal Value → Prop
  | .register owner _ _ => owner ≠ hiddenOwner
  | .submit sender _ => sender ≠ hiddenOwner
  | .replay _ _ => True
  | .deliver _ _ => True
  | .include _ => True

/-- Lockstep execution of any allowed raw action preserves pre-disclosure
hiding. -/
theorem HidingRelated.step [DecidableEq Principal] [DecidableEq Value]
    (related : HidingRelated hiddenOwner left right) (program : SealedProgram Principal)
    (action : Action Principal Value) (allowed : AllowedBeforeDisclosure hiddenOwner action) :
    HidingRelated hiddenOwner (step program left action) (step program right action) := by
  cases action with
  | register owner slot value =>
      simpa [SealedProgram.step] using related.register owner slot value allowed
  | submit sender payload =>
      simpa [SealedProgram.step] using related.submit sender payload allowed
  | replay broadcaster id =>
      simpa [SealedProgram.step] using related.replay broadcaster id
  | deliver observer id =>
      simpa [SealedProgram.step] using related.deliver observer id
  | «include» id =>
      simpa [SealedProgram.step] using related.includePending program id

end Interaction.SealedProgram
