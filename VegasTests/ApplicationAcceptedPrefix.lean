/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationAcceptedPrefix
import VegasTests.ConditionalSourceCoupling

/-! # Accepted binding-prefix regression

The generated conditional fixture includes its real pending binding before the
source cursor advances.  The resulting prefix certificate recovers the exact
canonical handle required by the later conditional endpoint.
-/

noncomputable section

namespace VegasTests.ApplicationAcceptedPrefix

open Vegas Interaction
open VegasTests.ConditionalApplicationImage
open VegasTests.ConditionalSourceCoupling

/-- Actual generated binding inclusion establishes the first-node accepted
prefix, rather than merely updating a hand-written application state. -/
theorem accepted_prefix_after_binding (secret : Bool) :
    (image 10).AcceptedBindingPrefix 1 (bound secret).application := by
  obtain ⟨_, _, _, hsnapshot⟩ := bound_source_successor secret
  refine ApplicationImage.AcceptedBindingPrefix.extend applicationPlan
    (fun _ => 10) 0 (bound secret).application bindingCode
    (ApplicationImage.AcceptedBindingPrefix.zero (image 10) (bound secret).application)
    ?_ rfl (some ⟨.bool, secret⟩) hsnapshot
  change _ ∈ [ApplicationInstruction.bind bindingCode, _]
  simp

/-- Static origin metadata plus the dynamic prefix recovers the precise
accepted handle consumed by the generated conditional publication. -/
theorem conditional_handle_after_binding (secret : Bool) :
    (bound secret).application.memory.accepted (conditionalCode 10).sourceField =
      some ((conditionalCode 10).endpoint.owner,
        (conditionalCode 10).endpoint.sourceSlot) := by
  apply (accepted_prefix_after_binding secret).conditionalHandle
  · decide
  · change _ ∈ [_, ApplicationInstruction.conditional (conditionalCode 10)]
    simp
  · rfl

end VegasTests.ApplicationAcceptedPrefix

/-- info: 'VegasTests.ApplicationAcceptedPrefix.accepted_prefix_after_binding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationAcceptedPrefix.accepted_prefix_after_binding

/-- info:
'VegasTests.ApplicationAcceptedPrefix.conditional_handle_after_binding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationAcceptedPrefix.conditional_handle_after_binding
