/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.StoredABI

/-!
# Player-call authentication

This layer adds one concrete concern without changing logical execution: an
injective registry assigns each semantic player a target caller identity, and
a player commit call must come from the identity assigned to its claimed
player.  The combined validator accepts exactly authenticated valid semantic
commands.

Only player-authorized commit calls are covered. Who may trigger internal
sample or reveal actions is a separate policy and remains explicit.
-/

namespace Vegas.Machine.Contract

open EventGraph

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

/-- Collision-free assignment of semantic player roles to target caller
identities such as chain addresses. -/
structure PlayerRegistry (Player Address : Type) where
  address : Player → Address
  injective : Function.Injective address

namespace PlayerRegistry

variable (registry : PlayerRegistry Player Address)

omit [DecidableEq Player] [DecidableEq Address] in
theorem address_eq_iff (left right : Player) :
    registry.address left = registry.address right ↔ left = right := by
  exact registry.injective.eq_iff

end PlayerRegistry

/-- A caller-bearing player commit call before authentication and semantic
validation. Player calls always carry a typed proposed value. -/
structure PlayerCall (Player Address : Type) (L : IExpr) where
  caller : Address
  player : Player
  node : Nat
  value : TypedValue L

namespace PlayerCall

/-- Erase caller metadata to the logical request checked by the machine. -/
def request (call : PlayerCall Player Address L) : Request Player L where
  node := call.node
  authority := .player call.player
  payload := .value call.value

/-- Check that the physical caller owns the claimed semantic player role. -/
def authenticated (registry : PlayerRegistry Player Address)
    (call : PlayerCall Player Address L) : Bool :=
  decide (call.caller = registry.address call.player)

omit [DecidableEq Player] in
@[simp] theorem authenticated_eq_true_iff
    (registry : PlayerRegistry Player Address)
    (call : PlayerCall Player Address L) :
    authenticated registry call = true ↔
      call.caller = registry.address call.player := by
  simp [authenticated]

/-- Authenticate and validate against a reachable semantic machine state. -/
def acceptsState (registry : PlayerRegistry Player Address)
    (state : program.State) (call : PlayerCall Player Address L) : Bool :=
  authenticated registry call && Request.accepts state call.request

theorem acceptsState_eq_true_iff
    (registry : PlayerRegistry Player Address)
    (state : program.State) (call : PlayerCall Player Address L) :
    acceptsState registry state call = true ↔
      call.caller = registry.address call.player ∧
        Request.Represents state call.request := by
  simp [acceptsState, Request.accepts_eq_true_iff]

/-- Authenticate and validate against canonical raw contract storage. -/
def acceptsStore (registry : PlayerRegistry Player Address)
    (codec : StorageCodec program) (store : RawStore codec)
    (call : PlayerCall Player Address L) : Bool :=
  authenticated registry call &&
    Request.acceptsStore (program := program) codec store call.request

/-- On storage encoded from a reachable state, player-call acceptance is
exactly caller ownership together with semantic command validity. -/
theorem acceptsStore_encodeState_eq_true_iff
    (registry : PlayerRegistry Player Address)
    (codec : StorageCodec program) (state : program.State)
    (call : PlayerCall Player Address L) :
    acceptsStore (program := program) registry codec
        (RawStore.encodeState codec state) call = true ↔
      call.caller = registry.address call.player ∧
        Request.Represents state call.request := by
  rw [acceptsStore, Request.acceptsStore_encodeState]
  simp [Request.accepts_eq_true_iff]

end PlayerCall

end Vegas.Machine.Contract
