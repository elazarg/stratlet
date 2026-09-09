/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationBindingOrigins
import VegasTests.GeneratedPersistentDisclosure

/-! # Binding-origin metadata regressions

The generated persistent-disclosure image has an earlier commitment binding
for each conditional endpoint. Certificate elimination recovers the actual
earlier instruction and its exact compatibility with the endpoint.
-/

noncomputable section

namespace VegasTests.ApplicationBindingOrigins

open Vegas Interaction

open VegasTests.GeneratedPersistentDisclosure

theorem persistent_image_has_binding_origins : image.HasBindingOrigins := by
  decide

/-- The generated later conditional exposes its exact compatible earlier
binding through the reusable certificate elimination API. -/
theorem second_conditional_has_earlier_binding :
    ∃ before binding after,
      image.instructions = before ++ .bind binding :: after ∧
        .conditional secondCode ∈ after ∧ binding.OriginFor secondCode := by
  apply persistent_image_has_binding_origins.origin_of_mem secondCode
  change _ ∈ [_, _, _, _, _, ApplicationInstruction.conditional secondCode]
  simp

end VegasTests.ApplicationBindingOrigins

/-- info: 'VegasTests.ApplicationBindingOrigins.persistent_image_has_binding_origins' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationBindingOrigins.persistent_image_has_binding_origins

/-- info: 'VegasTests.ApplicationBindingOrigins.second_conditional_has_earlier_binding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationBindingOrigins.second_conditional_has_earlier_binding
