/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageReplay

/-! # Predicates on every message retained by a pool

Delivery, replay, and inclusion move or copy existing messages. They preserve
any predicate that holds throughout the pending inventory, ledger, inboxes,
and sent histories. Submission additionally requires that predicate for the
new message. Application-specific secrecy or validity conditions instantiate
the predicate without giving the pool access to private application state.
-/

namespace Interaction.MessagePool

universe uPrincipal uPayload

variable {Principal : Type uPrincipal} {Payload : Type uPayload}
variable {safe : Message Principal Payload → Prop}
variable {pool : MessagePool Principal Payload}

def Satisfies (safe : Message Principal Payload → Prop)
    (pool : MessagePool Principal Payload) : Prop :=
  (∀ message, message ∈ pool.pending → safe message) ∧
  (∀ message, message ∈ pool.ledger → safe message) ∧
  (∀ who message, message ∈ pool.inbox who → safe message) ∧
  (∀ who message, message ∈ pool.sent who → safe message)

@[simp] theorem Satisfies.empty :
    Satisfies safe (MessagePool.empty Principal Payload) := by
  simp [Satisfies, MessagePool.empty]

theorem Satisfies.submit [DecidableEq Principal] (h : Satisfies safe pool)
    (sender : Principal) (payload : Payload)
    (hnew : safe ⟨(sender, pool.nextSerial sender), payload⟩) :
    Satisfies safe (pool.submit sender payload).2 := by
  rcases h with ⟨hpending, hledger, hinbox, hsent⟩
  constructor
  · intro message hmem
    simp only [MessagePool.submit, List.mem_append, List.mem_singleton] at hmem
    exact hmem.elim (hpending message) (fun heq => heq ▸ hnew)
  exact ⟨hledger, hinbox, by
    intro who message hmem
    simp only [MessagePool.submit] at hmem
    split at hmem
    · rename_i hwho
      subst who
      simp only [List.mem_append, List.mem_singleton] at hmem
      exact hmem.elim (hsent sender message) (fun heq => heq ▸ hnew)
    · exact hsent who message hmem⟩

theorem Satisfies.deliver [DecidableEq Principal] (h : Satisfies safe pool)
    (observer : Principal) (id : MessageId Principal) :
    Satisfies safe (pool.deliver observer id).state := by
  rcases h with ⟨hpending, hledger, hinbox, hsent⟩
  unfold MessagePool.deliver
  split
  · rename_i message hlookup
    have hmessage := hpending message (List.mem_of_find?_eq_some hlookup)
    exact ⟨hpending, hledger, by
      intro who candidate hmem
      by_cases hwho : who = observer
      · subst who
        simp only [if_pos, List.mem_append, List.mem_singleton] at hmem
        exact hmem.elim (hinbox observer candidate) (fun heq => heq ▸ hmessage)
      · simp only [if_neg hwho] at hmem
        exact hinbox who candidate hmem, hsent⟩
  · exact ⟨hpending, hledger, hinbox, hsent⟩

theorem Satisfies.replay [DecidableEq Principal] (h : Satisfies safe pool)
    (broadcaster : Principal) (id : MessageId Principal) :
    Satisfies safe (pool.replay broadcaster id).state := by
  rcases h with ⟨hpending, hledger, hinbox, hsent⟩
  unfold MessagePool.replay MessagePool.View.known?
  split
  · rename_i message hknown
    have hmem := List.mem_of_find?_eq_some hknown
    simp only [List.mem_append] at hmem
    have hmessage : safe message := by
      rcases hmem with (hsentMem | hinboxMem) | hledgerMem
      · exact hsent broadcaster message hsentMem
      · exact hinbox broadcaster message hinboxMem
      · exact hledger message hledgerMem
    exact ⟨by
      intro candidate hmem
      simp only [List.mem_append, List.mem_singleton] at hmem
      exact hmem.elim (hpending candidate) (fun heq => heq ▸ hmessage), hledger, hinbox, by
      intro who candidate hmem
      by_cases hwho : who = broadcaster
      · subst who
        simp only [if_pos, List.mem_append, List.mem_singleton] at hmem
        exact hmem.elim (hsent broadcaster candidate) (fun heq => heq ▸ hmessage)
      · simp only [if_neg hwho] at hmem
        exact hsent who candidate hmem⟩
  · exact ⟨hpending, hledger, hinbox, hsent⟩

private theorem mem_of_mem_removeFirst [DecidableEq Principal]
    (id : MessageId Principal) (candidate : Message Principal Payload)
    (messages : List (Message Principal Payload)) :
    candidate ∈ removeFirst id messages → candidate ∈ messages := by
  induction messages with
  | nil => simp [removeFirst]
  | cons head tail ih =>
      simp only [removeFirst]
      split
      · exact fun h => List.mem_cons_of_mem head h
      · simp only [List.mem_cons]
        exact fun h => h.elim Or.inl (fun ht => Or.inr (ih ht))

theorem Satisfies.includePending [DecidableEq Principal] (h : Satisfies safe pool)
    (id : MessageId Principal) : Satisfies safe (pool.includePending id).state := by
  rcases h with ⟨hpending, hledger, hinbox, hsent⟩
  unfold MessagePool.includePending
  split
  · rename_i message hlookup
    have hmessage := hpending message (List.mem_of_find?_eq_some hlookup)
    exact ⟨by
      intro candidate hmem
      exact hpending candidate (mem_of_mem_removeFirst id candidate pool.pending hmem), by
      intro candidate hmem
      simp only [List.mem_append, List.mem_singleton] at hmem
      exact hmem.elim (hledger candidate) (fun heq => heq ▸ hmessage), hinbox, hsent⟩
  · exact ⟨hpending, hledger, hinbox, hsent⟩

end Interaction.MessagePool
