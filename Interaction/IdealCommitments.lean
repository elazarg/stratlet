/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

/-! # Ideal write-once commitments

This is an ideal hidden write-once functionality with a private registration
interface. A handle contains only an owner and slot, independently of the
registered value. Opening messages carry a claimed value. An operational
adapter must authenticate the opening before checking it against the private
table; exposing the check as an unrestricted oracle would disclose guesses'
correctness before opening.

This model is not software cryptography or deployable public storage. It gives
no liveness, forced-opening, delivery, or release-barrier guarantee.
Its table and verification functions are specification operations. This file
does not define a strategy interface: hiding requires a separate interface
that does not hand these operations or the table to an opponent.
-/

namespace Interaction

universe uPrincipal uSlot uValue

/-- An owner-scoped commitment handle. -/
abbrev CommitmentHandle (Principal : Type uPrincipal) (Slot : Type uSlot) :=
  Principal × Slot

/-- Private ideal storage, indexed by authenticated owner and slot. -/
structure IdealCommitments (Principal : Type uPrincipal) (Slot : Type uSlot)
    (Value : Type uValue) where
  table : Principal → Slot → Option Value

namespace IdealCommitments

variable {Principal : Type uPrincipal} {Slot : Type uSlot} {Value : Type uValue}

/-- The initially empty functionality. -/
def empty : IdealCommitments Principal Slot Value where
  table := fun _ _ => none

/-- Read ideal storage for specification and proof. This is not a public
runtime operation. -/
def lookup (state : IdealCommitments Principal Slot Value)
    (handle : CommitmentHandle Principal Slot) : Option Value :=
  state.table handle.1 handle.2

/-- The result of a private authenticated seal request. -/
structure SealResult where
  accepted : Bool
  state : IdealCommitments Principal Slot Value

/-- Privately register a value once at an authenticated owner-scoped slot. -/
def sealValue (state : IdealCommitments Principal Slot Value)
    [DecidableEq Principal] [DecidableEq Slot]
    (owner : Principal) (slot : Slot) (value : Value) :
    SealResult (Principal := Principal) (Slot := Slot) (Value := Value) :=
  match state.table owner slot with
  | some _ => ⟨false, state⟩
  | none =>
      ⟨true, { table := fun otherOwner otherSlot =>
        if otherOwner = owner ∧ otherSlot = slot then some value
        else state.table otherOwner otherSlot }⟩

/-- A public opening message carries its claimed value. -/
structure Opening where
  handle : CommitmentHandle Principal Slot
  claimed : Value

/-- The ideal service's private-table check for a claimed opening. It does not
authenticate a sender and must only be invoked after an application has checked
the opening message's sender and expected owner/slot. Exposing this Boolean as
an unrestricted pre-opening query oracle would violate the intended hiding. -/
def verify (state : IdealCommitments Principal Slot Value)
    [DecidableEq Value]
    (opening : Opening (Principal := Principal) (Slot := Slot) (Value := Value)) : Bool :=
  state.lookup opening.handle == some opening.claimed

@[simp] theorem lookup_empty (handle : CommitmentHandle Principal Slot) :
    (empty : IdealCommitments Principal Slot Value).lookup handle = none := rfl

/-- The first seal succeeds and stores exactly its private value. -/
theorem seal_first (state : IdealCommitments Principal Slot Value)
    [DecidableEq Principal] [DecidableEq Slot]
    (owner : Principal) (slot : Slot) (value : Value)
    (hempty : state.table owner slot = none) :
    (state.sealValue owner slot value).accepted = true ∧
      (state.sealValue owner slot value).state.lookup (owner, slot) = some value := by
  simp [sealValue, hempty, lookup]

/-- Once occupied, a slot rejects another seal and leaves all state unchanged. -/
theorem seal_occupied (state : IdealCommitments Principal Slot Value)
    [DecidableEq Principal] [DecidableEq Slot]
    (owner : Principal) (slot : Slot) (stored value : Value)
    (hstored : state.table owner slot = some stored) :
    state.sealValue owner slot value = ⟨false, state⟩ := by
  simp [sealValue, hstored]

/-- In particular, a repeated seal cannot overwrite the fixed value. -/
theorem seal_cannot_overwrite (state : IdealCommitments Principal Slot Value)
    [DecidableEq Principal] [DecidableEq Slot]
    (owner : Principal) (slot : Slot) (stored value : Value)
    (hstored : state.table owner slot = some stored) :
    (state.sealValue owner slot value).state.lookup (owner, slot) = some stored := by
  rw [seal_occupied state owner slot stored value hstored]
  exact hstored

/-- A successful first seal leaves every other owner/slot entry unchanged. -/
theorem seal_other (state : IdealCommitments Principal Slot Value)
    [DecidableEq Principal] [DecidableEq Slot]
    (owner otherOwner : Principal) (slot otherSlot : Slot) (value : Value)
    (hempty : state.table owner slot = none)
    (hother : otherOwner ≠ owner ∨ otherSlot ≠ slot) :
    (state.sealValue owner slot value).state.lookup (otherOwner, otherSlot) =
      state.lookup (otherOwner, otherSlot) := by
  rcases hother with howner | hslot
  · simp [sealValue, hempty, lookup, howner]
  · simp [sealValue, hempty, lookup, hslot]

/-- Sealing any slot preserves every value that was already registered,
including values stored at other owner-scoped handles. -/
theorem lookup_sealValue_of_eq_some (state : IdealCommitments Principal Slot Value)
    [DecidableEq Principal] [DecidableEq Slot]
    (owner : Principal) (slot : Slot) (replacement : Value)
    (handle : CommitmentHandle Principal Slot) (stored : Value)
    (hstored : state.lookup handle = some stored) :
    (state.sealValue owner slot replacement).state.lookup handle = some stored := by
  unfold sealValue
  split
  · exact hstored
  · rename_i hempty
    simp only [lookup]
    change state.table handle.1 handle.2 = some stored at hstored
    by_cases hhandle : handle.1 = owner ∧ handle.2 = slot
    · rw [hhandle.1, hhandle.2] at hstored
      have himpossible : (none : Option Value) = some stored := hempty.symm.trans hstored
      contradiction
    · simp [hhandle]
      exact hstored

/-- A claim is accepted exactly when that claimed value is stored at its
owner-scoped handle. -/
theorem verify_eq_true_iff (state : IdealCommitments Principal Slot Value)
    [DecidableEq Value]
    (opening : Opening (Principal := Principal) (Slot := Slot) (Value := Value)) :
    state.verify opening = true ↔
      state.lookup opening.handle = some opening.claimed := by
  simp [verify]

/-- Rejection is the exact complement of successful claimed-value opening. -/
theorem verify_eq_false_iff (state : IdealCommitments Principal Slot Value)
    [DecidableEq Value]
    (opening : Opening (Principal := Principal) (Slot := Slot) (Value := Value)) :
    state.verify opening = false ↔
      state.lookup opening.handle ≠ some opening.claimed := by
  simp [verify]

/-- An accepted claimed opening equals the fixed privately stored value. -/
theorem accepted_opening_eq_stored (state : IdealCommitments Principal Slot Value)
    [DecidableEq Value]
    (handle : CommitmentHandle Principal Slot) (stored claimed : Value)
    (hstored : state.lookup handle = some stored)
    (haccepted : state.verify ⟨handle, claimed⟩ = true) :
    claimed = stored := by
  have hclaimed := (verify_eq_true_iff state ⟨handle, claimed⟩).mp haccepted
  exact Option.some.inj (hclaimed.symm.trans hstored)

/-- A claim of the stored value verifies successfully. -/
theorem verify_stored (state : IdealCommitments Principal Slot Value)
    [DecidableEq Value]
    (handle : CommitmentHandle Principal Slot) (value : Value)
    (hstored : state.lookup handle = some value) :
    state.verify ⟨handle, value⟩ = true :=
  (verify_eq_true_iff state _).mpr hstored

/-- A different claimed value verifies unsuccessfully. -/
theorem verify_other (state : IdealCommitments Principal Slot Value)
    [DecidableEq Value]
    (handle : CommitmentHandle Principal Slot) (stored claimed : Value)
    (hstored : state.lookup handle = some stored) (hne : claimed ≠ stored) :
    state.verify ⟨handle, claimed⟩ = false := by
  apply (verify_eq_false_iff state _).mpr
  intro hclaimed
  exact hne (Option.some.inj (hclaimed.symm.trans hstored))

end IdealCommitments

end Interaction
