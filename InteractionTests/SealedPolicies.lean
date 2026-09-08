/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedPolicyLaws

/-! # Executable regressions for sealed-message policy scope -/

namespace InteractionTests.SealedPolicies

open Interaction Interaction.SealedProgram

def program : SealedProgram Bool := ⟨[]⟩

def initial : State Bool Bool := State.empty Bool Bool

def afterRegister : PolicyExecution Bool Bool :=
  playerStep program false (PolicyExecution.initial initial) (.register 3 true)

#guard afterRegister.native.service.lookup (false, 3) = some true
#guard match afterRegister.nativeTrace with
  | [.register false 3 true] => true
  | _ => false

def afterSubmit : PolicyExecution Bool Bool :=
  playerStep program false (PolicyExecution.initial initial) (.submit .malformed)

#guard (afterSubmit.native.pool.pending.head?.map Message.sender) = some false
#guard match afterSubmit.nativeTrace with
  | [.submit false .malformed] => true
  | _ => false

/-- A principal cannot replay an envelope before observing it. -/
def afterUnknownReplay : PolicyExecution Bool Bool :=
  playerStep program true afterSubmit (.replay (false, 0))

#guard afterUnknownReplay.native.pool.pending.length = 1
#guard (afterUnknownReplay.native.pool.sent true).length = 0

def deliveredForReplay : PolicyExecution Bool Bool :=
  environmentStep program afterSubmit (.deliver true (false, 0))

/-- After delivery, rebroadcasting succeeds but preserves the envelope's
original author even though the invoked principal is the broadcaster. -/
def afterReplay : PolicyExecution Bool Bool :=
  playerStep program true deliveredForReplay (.replay (false, 0))

#guard afterReplay.native.pool.pending.length = 2
#guard (afterReplay.native.pool.sent true).length = 1
#guard (afterReplay.native.pool.pending.getLast?.map Message.sender) = some false
#guard match afterReplay.nativeTrace.getLast? with
  | some (.replay true (false, 0)) => true
  | _ => false

def afterWait : PolicyExecution Bool Bool :=
  playerStep program false (PolicyExecution.initial initial) .wait

#guard afterWait.native.pool.pending.length = initial.pool.pending.length
#guard afterWait.native.events.length = initial.events.length
#guard afterWait.nativeTrace.length = 0
#guard (afterWait.principalHistory false).length = 1
#guard (afterWait.principalHistory true).length = 0
#guard match (afterWait.principalHistory false).head?.map PlayerEntry.command with
  | some .wait => true
  | _ => false

theorem wait_stutters_native : afterWait.native = initial := rfl

def beforeDelivery : PolicyExecution Bool Bool :=
  playerStep program false (PolicyExecution.initial initial) (.submit .malformed)

def afterDelivery : PolicyExecution Bool Bool :=
  environmentStep program beforeDelivery (.deliver true (false, 0))

#guard (afterDelivery.principalHistory false).length =
  (beforeDelivery.principalHistory false).length
#guard (afterDelivery.principalHistory true).length =
  (beforeDelivery.principalHistory true).length
#guard (beforeDelivery.native.observe true).messages.inbox.length = 0
#guard ((afterDelivery.native.observe true).messages.inbox.head?.map Message.sender) = some false

/-- No value in the disabled command subtype can contain an explicit replay. -/
theorem no_disabled_replay (id : MessageId Bool)
    (command : { command : PlayerCommand Bool Bool // command.allowed false }) :
    command.1 ≠ .replay id := by
  intro heq
  have := command.2
  rw [heq] at this
  simp [PlayerCommand.allowed] at this

end InteractionTests.SealedPolicies
