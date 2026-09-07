/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract

/-!
# Contract storage layout

A layout assigns each logical manifest slot a bounded physical key and proves
that distinct logical slots cannot collide.  It still says nothing about how a
typed value is encoded in the target word stored at that key.
-/

namespace Vegas.Machine.Contract

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Collision-free bounded physical keys for a contract manifest. -/
structure Layout (program : Program Player L) where
  slotCount : Nat
  address : StorageSlot program → Nat
  address_lt : ∀ slot, address slot < slotCount
  injective : Function.Injective address

namespace Layout

variable (program : Program Player L)

/-- Dense canonical layout: graph values first, then action-completion bits. -/
def canonicalAddress : StorageSlot program → Nat
  | .value field => field
  | .completed node => program.graph.fieldCount + node

theorem canonicalAddress_lt (slot : StorageSlot program) :
    canonicalAddress program slot <
      program.graph.fieldCount + program.graph.nodeCount := by
  cases slot with
  | value field =>
      have hfield := field.isLt
      simp only [canonicalAddress]
      omega
  | completed node =>
      have hnode := node.isLt
      simp only [canonicalAddress]
      omega

theorem canonicalAddress_injective :
    Function.Injective (canonicalAddress program) := by
  intro left right heq
  cases left with
  | value leftField =>
      cases right with
      | value rightField =>
          have hfin : leftField = rightField := by
            apply Fin.ext
            simpa [canonicalAddress] using heq
          cases hfin
          rfl
      | completed rightNode =>
          have hleft := leftField.isLt
          simp [canonicalAddress] at heq
          omega
  | completed leftNode =>
      cases right with
      | value rightField =>
          have hright := rightField.isLt
          simp [canonicalAddress] at heq
          omega
      | completed rightNode =>
          have hfin : leftNode = rightNode := by
            apply Fin.ext
            simp [canonicalAddress] at heq
            omega
          cases hfin
          rfl

/-- The canonical physical layout certificate. -/
def canonical : Layout program where
  slotCount := program.graph.fieldCount + program.graph.nodeCount
  address := canonicalAddress program
  address_lt := canonicalAddress_lt program
  injective := canonicalAddress_injective program

/-- Every bounded canonical key is occupied; the canonical layout has no
padding gaps. -/
theorem canonical_surjective
    (key : Fin (canonical program).slotCount) :
    ∃ slot : StorageSlot program,
      (canonical program).address slot = key := by
  by_cases hvalue : (key : Nat) < program.graph.fieldCount
  · exact ⟨.value ⟨key, hvalue⟩, rfl⟩
  · have hnode :
        (key : Nat) - program.graph.fieldCount <
          program.graph.nodeCount := by
      have hkey := key.isLt
      dsimp [canonical] at hkey
      omega
    refine
      ⟨.completed
          ⟨(key : Nat) - program.graph.fieldCount, hnode⟩,
        ?_⟩
    simp [canonical, canonicalAddress]
    omega

/-- A value slot and completion slot can never alias in the canonical
layout. -/
theorem value_ne_completed
    (field : Fin program.graph.fieldCount)
    (node : Fin program.graph.nodeCount) :
    (canonical program).address (.value field) ≠
      (canonical program).address (.completed node) := by
  intro heq
  have hslots := (canonical program).injective heq
  cases hslots

end Layout

end Vegas.Machine.Contract
