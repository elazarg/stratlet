/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessagePool

/-! # Fresh message-pool envelopes

Submission makes the sender's current serial available without requiring the
rest of the pending pool to be empty. The premise is deliberately local to the
new identifier; broader serial-discipline invariants belong to callers that
need to derive it.
-/

namespace Interaction.MessagePool

universe uPrincipal uPayload

variable {Principal : Type uPrincipal} {Payload : Type uPayload}
variable [DecidableEq Principal]

/-- The identifier returned by submission is the sender's pre-submission
serial, independently of unrelated pending traffic. -/
@[simp] theorem submit_id (pool : MessagePool Principal Payload)
    (sender : Principal) (payload : Payload) :
    (pool.submit sender payload).1 = (sender, pool.nextSerial sender) := rfl

/-- If the newly allocated sender-local identifier was absent, submission
makes its exact envelope the lookup result while retaining arbitrary unrelated
pending messages. -/
theorem lookup_submit_fresh (pool : MessagePool Principal Payload)
    (sender : Principal) (payload : Payload)
    (hfresh : pool.lookup (sender, pool.nextSerial sender) = none) :
    (pool.submit sender payload).2.lookup (sender, pool.nextSerial sender) =
      some ⟨(sender, pool.nextSerial sender), payload⟩ := by
  change pool.pending.find?
    (fun message => message.id = (sender, pool.nextSerial sender)) = none at hfresh
  simp [submit, lookup, List.find?_append, hfresh]

end Interaction.MessagePool
