/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessagePool

/-! # Atomic application inclusion

This runtime-general boundary publishes one existing pending message and then
atomically accepts or rejects its application effect.  Rejection retains the
published message.  There are no fees, callbacks, clocks, rollback branches,
or chain-finality semantics here.
-/

namespace Interaction.MessagePool

universe uPrincipal uPayload uApplication

variable {Principal : Type uPrincipal} {Payload : Type uPayload}
variable {Application : Type uApplication}
variable [DecidableEq Principal]

structure ApplicationResult (Principal : Type uPrincipal) (Payload : Type uPayload)
    (Application : Type uApplication) where
  pool : MessagePool Principal Payload
  application : Application
  receipt : Option Bool

/-- Include a preexisting pending message, then atomically apply its handler.
`some true` records an accepted application update, `some false` records a
published but rejected message, and `none` records a missing message id. -/
def includeApplication (pool : MessagePool Principal Payload) (application : Application)
    (id : MessageId Principal) (handler : Application → Message Principal Payload → Option Application) :
    ApplicationResult Principal Payload Application :=
  let included := pool.includePending id
  match included.message with
  | none => ⟨included.state, application, none⟩
  | some message =>
      match handler application message with
      | some next => ⟨included.state, next, some true⟩
      | none => ⟨included.state, application, some false⟩

/-- Application acceptance or rejection does not change the carrier operation. -/
@[simp] theorem includeApplication_pool
    (pool : MessagePool Principal Payload) (application : Application)
    (id : MessageId Principal) (handler : Application → Message Principal Payload → Option Application) :
    (includeApplication pool application id handler).pool = (pool.includePending id).state := by
  dsimp only [includeApplication]
  split
  · rfl
  · split <;> rfl

@[simp] theorem includeApplication_missing
    (pool : MessagePool Principal Payload) (application : Application)
    (id : MessageId Principal) (handler : Application → Message Principal Payload → Option Application)
    (hmissing : pool.lookup id = none) :
    includeApplication pool application id handler = ⟨pool, application, none⟩ := by
  simp [includeApplication, MessagePool.includePending, hmissing, Result.invalid]

@[simp] theorem includeApplication_accept
    (pool : MessagePool Principal Payload) (application next : Application)
    (id : MessageId Principal) (message : Message Principal Payload)
    (handler : Application → Message Principal Payload → Option Application)
    (hlookup : pool.lookup id = some message)
    (hhandler : handler application message = some next) :
    includeApplication pool application id handler =
      ⟨(pool.includePending id).state, next, some true⟩ := by
  simp [includeApplication, MessagePool.includePending, hlookup, hhandler]

@[simp] theorem includeApplication_reject
    (pool : MessagePool Principal Payload) (application : Application)
    (id : MessageId Principal) (message : Message Principal Payload)
    (handler : Application → Message Principal Payload → Option Application)
    (hlookup : pool.lookup id = some message)
    (hhandler : handler application message = none) :
    includeApplication pool application id handler =
      ⟨(pool.includePending id).state, application, some false⟩ := by
  simp [includeApplication, MessagePool.includePending, hlookup, hhandler]

/-- Rejected application handling does not roll back publication. -/
theorem includeApplication_reject_ledger
    (pool : MessagePool Principal Payload) (application : Application)
    (id : MessageId Principal) (message : Message Principal Payload)
    (handler : Application → Message Principal Payload → Option Application)
    (hlookup : pool.lookup id = some message)
    (hhandler : handler application message = none) :
    (includeApplication pool application id handler).pool.ledger =
      pool.ledger ++ [message] := by
  rw [includeApplication_reject pool application id message handler hlookup hhandler]
  exact include_ledger_of_lookup pool id message hlookup

/-- Inclusion never invokes a sender-local callback or changes sent history. -/
theorem includeApplication_preserves_sent
    (pool : MessagePool Principal Payload) (application : Application)
    (id : MessageId Principal) (handler : Application → Message Principal Payload → Option Application)
    (who : Principal) :
    (includeApplication pool application id handler).pool.sent who = pool.sent who := by
  rw [includeApplication_pool]
  exact include_preserves_sent pool id who

/-- Inclusion likewise preserves every recipient inbox. -/
theorem includeApplication_preserves_inbox
    (pool : MessagePool Principal Payload) (application : Application)
    (id : MessageId Principal) (handler : Application → Message Principal Payload → Option Application)
    (who : Principal) :
    (includeApplication pool application id handler).pool.inbox who = pool.inbox who := by
  rw [includeApplication_pool]
  exact include_preserves_inbox pool id who

end Interaction.MessagePool
