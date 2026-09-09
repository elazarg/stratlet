/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageReadoutAvailability
import VegasTests.DisclosureAccounting

/-! # Initial-input boundary for local readout availability

Public initial inputs are recovered by the general readout theorem. A sealed
initial input has a source value but no native local value under the public-only
initializer, even though refinement, completed-field coverage, and binding
provenance all hold. Provisioning is therefore a real separate obligation.
-/

noncomputable section

namespace VegasTests.ApplicationReadoutAvailability

open Vegas Vegas.EventGraph Interaction

abbrev Player := Fin 2

def graph (owner : Option Player) : Graph Player simpleExpr where
  initialFields := [{ ty := .bool, owner := owner, value := true }]
  nodes := []

def image : ApplicationImage Player simpleExpr := ⟨[]⟩

def native (owner : Option Player) : ApplicationImage.State Player simpleExpr :=
  .initial (.initial (graph owner))

theorem initial_refines (owner : Option Player) :
    (native owner).Refines (Config.initial (graph owner)) :=
  ApplicationImage.State.initial_refines (graph owner)

theorem initial_covers (owner : Option Player) :
    (native owner).memory.Covers (graph owner).initialFields.length :=
  ApplicationImage.Memory.covers_of_done_false _ _ (fun _ => rfl)

theorem initial_registeredBindings (owner : Option Player) :
    image.RegisteredBindings 0
      (fun slot typed => ∃ spec : FieldSpec Player simpleExpr,
        (graph owner).field? slot = some spec ∧ typed.ty = spec.ty) [] (native owner) := by
  intro field handle haccepted
  cases haccepted

/-- The general theorem supplies availability, with no successful local read
assumed in its premises. -/
theorem public_initial_read :
    Store.getAs (image.ownerReadStore 0 [] (native none).memory) 0 .bool = some true := by
  exact image.ownerReadStore_getAs_of_visible 0 [] (native none)
    (Config.initial (graph none)) (initial_refines none) (initial_covers none)
    (initial_registeredBindings none) ⟨0, .bool⟩
    ⟨.bool, none, .initial true⟩ rfl rfl (Or.inl rfl) (fun _ _ => rfl) true (by rfl)

/-- Merely representing a sealed initial source value does not provision it
to the owner's runtime history or public application memory. -/
theorem sealed_initial_read_missing :
    Store.getAs (Config.initial (graph (some 0))).store 0 .bool = some true ∧
      Store.getAs (image.ownerReadStore 0 [] (native (some 0)).memory) 0 .bool = none := by
  exact ⟨rfl, rfl⟩

end VegasTests.ApplicationReadoutAvailability

/-- info: 'VegasTests.ApplicationReadoutAvailability.public_initial_read' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationReadoutAvailability.public_initial_read

/-- info: 'VegasTests.ApplicationReadoutAvailability.sealed_initial_read_missing' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationReadoutAvailability.sealed_initial_read_missing
