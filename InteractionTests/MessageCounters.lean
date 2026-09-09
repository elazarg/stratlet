/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationCounters
import InteractionTests.MessageApplication

/-! # Message counter regression

A delivered envelope may be replayed into pending without making the author's
current next serial collide with an existing pending identifier.
-/

namespace InteractionTests.MessageApplication

open Interaction GameTheory.Math.Probability

/-- Counter freshness survives the actual native submit, deliver, and replay
action sequence, including both pending copies of the original envelope. -/
theorem replay_run_lookup_nextSerial_eq_none
    (next : MessageApplication.State lottery)
    (hnext : next ∈
      (lottery.run [.submit 0 .lock, .deliver 1 (0, 0), .replay 1 (0, 0)]
        initial).support) :
    next.pool.lookup (0, next.pool.nextSerial 0) = none := by
  have hserials := lottery.run_serialsBeforeNext initial next
    [.submit 0 .lock, .deliver 1 (0, 0), .replay 1 (0, 0)]
    MessagePool.SerialsBeforeNext.empty hnext
  exact hserials.lookup_nextSerial_eq_none 0

end InteractionTests.MessageApplication
