/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageInvariant
import Interaction.MessagePoolFreshness

/-! # Sender-local message counter invariants

Every envelope retained by a well-counted pool has a serial strictly below
the current counter of its stated sender. Submission establishes this fact for
the newly allocated identifier and advances only that sender's counter;
delivery, replay, and inclusion merely move or copy already retained messages.
-/

namespace Interaction.MessagePool

universe uPrincipal uPayload

variable {Principal : Type uPrincipal} {Payload : Type uPayload}
variable [DecidableEq Principal]

/-- Every retained envelope predates the next serial of its stated sender. -/
def SerialsBeforeNext (pool : MessagePool Principal Payload) : Prop :=
  pool.Satisfies fun message => message.id.2 < pool.nextSerial message.id.1

omit [DecidableEq Principal] in
@[simp] theorem SerialsBeforeNext.empty :
    SerialsBeforeNext (MessagePool.empty Principal Payload) := by
  simp [SerialsBeforeNext]

/-- Submission never decreases any principal's next serial. -/
theorem nextSerial_le_submit (pool : MessagePool Principal Payload)
    (sender who : Principal) (payload : Payload) :
    pool.nextSerial who ≤ (pool.submit sender payload).2.nextSerial who := by
  by_cases hwho : who = sender
  · subst who
    simp [MessagePool.submit]
  · simp [MessagePool.submit, hwho]

@[simp] theorem deliver_nextSerial (pool : MessagePool Principal Payload)
    (observer : Principal) (id : MessageId Principal) (who : Principal) :
    (pool.deliver observer id).state.nextSerial who = pool.nextSerial who := by
  unfold MessagePool.deliver
  split <;> rfl

@[simp] theorem replay_nextSerial (pool : MessagePool Principal Payload)
    (broadcaster : Principal) (id : MessageId Principal) (who : Principal) :
    (pool.replay broadcaster id).state.nextSerial who = pool.nextSerial who := by
  unfold MessagePool.replay
  split <;> rfl

/-- Submitting a fresh envelope preserves the strict serial bound on every
retained copy. -/
theorem SerialsBeforeNext.submit {pool : MessagePool Principal Payload}
    (hserials : pool.SerialsBeforeNext) (sender : Principal) (payload : Payload) :
    (pool.submit sender payload).2.SerialsBeforeNext := by
  let submitted := (pool.submit sender payload).2
  have hold : pool.Satisfies fun message =>
      message.id.2 < submitted.nextSerial message.id.1 := by
    apply Satisfies.mono hserials
    intro message hmessage
    exact Nat.lt_of_lt_of_le hmessage
      (nextSerial_le_submit pool sender message.id.1 payload)
  unfold SerialsBeforeNext
  apply hold.submit sender payload
  simp [submitted, MessagePool.submit]

/-- Delivery preserves the counter invariant. -/
theorem SerialsBeforeNext.deliver {pool : MessagePool Principal Payload}
    (hserials : pool.SerialsBeforeNext) (observer : Principal)
    (id : MessageId Principal) :
    (pool.deliver observer id).state.SerialsBeforeNext := by
  unfold SerialsBeforeNext at hserials ⊢
  simpa only [deliver_nextSerial] using hserials.deliver observer id

/-- Replay preserves the counter invariant because it copies a known retained
envelope without changing any sender's allocation counter. -/
theorem SerialsBeforeNext.replay {pool : MessagePool Principal Payload}
    (hserials : pool.SerialsBeforeNext) (broadcaster : Principal)
    (id : MessageId Principal) :
    (pool.replay broadcaster id).state.SerialsBeforeNext := by
  unfold SerialsBeforeNext at hserials ⊢
  simpa only [replay_nextSerial] using hserials.replay broadcaster id

/-- Inclusion preserves the counter invariant while moving the selected
pending envelope to the ledger. -/
theorem SerialsBeforeNext.includePending
    {pool : MessagePool Principal Payload}
    (hserials : pool.SerialsBeforeNext) (id : MessageId Principal) :
    (pool.includePending id).state.SerialsBeforeNext := by
  unfold SerialsBeforeNext at hserials ⊢
  simpa only [include_preserves_nextSerial] using hserials.includePending id

/-- The current next serial cannot already identify a pending envelope. -/
theorem SerialsBeforeNext.lookup_nextSerial_eq_none
    {pool : MessagePool Principal Payload}
    (hserials : pool.SerialsBeforeNext) (who : Principal) :
    pool.lookup (who, pool.nextSerial who) = none := by
  change pool.pending.find?
    (fun message => message.id = (who, pool.nextSerial who)) = none
  apply List.find?_eq_none.mpr
  intro message hmem hmatch
  have heq : message.id = (who, pool.nextSerial who) := of_decide_eq_true hmatch
  have hbound := hserials.1 message hmem
  change message.id.2 < pool.nextSerial message.id.1 at hbound
  rw [heq] at hbound
  exact Nat.lt_irrefl _ hbound

/-- In a well-counted pool, submission's canonical identifier is fresh
without an additional local absence premise. -/
theorem SerialsBeforeNext.lookup_submit
    {pool : MessagePool Principal Payload}
    (hserials : pool.SerialsBeforeNext) (sender : Principal) (payload : Payload) :
    (pool.submit sender payload).2.lookup (sender, pool.nextSerial sender) =
      some ⟨(sender, pool.nextSerial sender), payload⟩ :=
  lookup_submit_fresh pool sender payload
    (hserials.lookup_nextSerial_eq_none sender)

end Interaction.MessagePool
