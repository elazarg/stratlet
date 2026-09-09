/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationCacheSeparation
import VegasTests.GeneratedPersistentDisclosure

/-! # Independent caches for repeated disclosure of one binding

The two generated conditional instructions deliberately share their binding
slot. Their distinct publication addresses keep their voluntary choices apart.
-/

noncomputable section

namespace VegasTests.ApplicationCacheSeparation

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction Interaction.MessageApplication
open VegasTests.PersistentDisclosure VegasTests.GeneratedPersistentDisclosure

private def firstTail : VegasCore TestPlayer simpleExpr ResponseContext :=
  .commit 6 1 (.constBool true) (.reveal 7 1 6 .here secondCore)

private def firstCore : VegasCore TestPlayer simpleExpr FirstContext :=
  .commit 4 0 firstGuard (.reveal 5 0 4 .here firstTail)

private def firstSite : ConditionalPublicationSite firstCore :=
  ConditionalPublicationSite.atHead (P := TestPlayer) (L := simpleExpr)
    (Γ := FirstContext) (ty := BaseTy.option BaseTy.bool)
    4 5 0 firstGuard firstTail DisclosureAccounting.persistentFirstSpec

private def firstCode : ConditionalCode TestPlayer simpleExpr :=
  firstSite.code source.fresh.2.2.2.2 afterSignal 0 10

/-- Both endpoints occur in the same generated artifact and use the same
opaque binding, but have distinct cache addresses. -/
theorem generated_repeated_binding :
    image.lookup 5 = some (.conditional firstCode) ∧
      image.lookup 9 = some (.conditional secondCode) ∧
      firstCode.endpoint.sourceSlot = secondCode.endpoint.sourceSlot ∧
      firstCode.endpoint.publicationNode ≠ secondCode.endpoint.publicationNode := by
  refine ⟨?_, image_lookup_second, rfl, ?_⟩
  · have hmem : ApplicationInstruction.conditional firstCode ∈
        applicationPlan.instructions (fun _ => 10) := by
      change _ ∈ [_, _, _, ApplicationInstruction.conditional firstCode, _, _]
      simp
    exact applicationPlan.image_lookup_of_mem (fun _ => 10) _ hmem
  · decide

/-- Opening and decline at the first endpoint are recognized there, but are
rejected by the second endpoint's cache despite their common binding slot. -/
theorem first_choice_keeps_second_cache_fresh (chosen : Option Bool)
    (execution next : image.application.PolicyExecution)
    (hstep : next ∈ (image.application.playerStep 0 execution
      (.submit (.conditional 5 (firstCode.requestPayload chosen)))).support)
    (hfresh : (ApplicationInstruction.conditional secondCode).CacheEmpty image execution) :
    (ApplicationInstruction.conditional secondCode).CacheEmpty image next := by
  apply ApplicationInstruction.cacheEmpty_playerStep image (.conditional secondCode)
    0 execution _ next hstep hfresh
  apply ApplicationInstruction.rejectsCommand_of_conditional image firstCode
    (.conditional secondCode) 0 _ (by decide)
  right
  intro hreject
  have hdecode := hreject rfl
  cases chosen with
  | none => change some none = none at hdecode; contradiction
  | some value =>
      cases value <;> change some (some _) = none at hdecode <;> contradiction

end VegasTests.ApplicationCacheSeparation

/-- info: 'VegasTests.ApplicationCacheSeparation.first_choice_keeps_second_cache_fresh' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationCacheSeparation.first_choice_keeps_second_cache_fresh
