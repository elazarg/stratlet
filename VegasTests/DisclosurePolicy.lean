/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureSites

/-! # Information-local policy lifting for the finite disclosure process -/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

structure SenderStrategy where
  binding : FinDist Bool
  complete : Bool → Bool → FinDist Bool

abbrev ResponderStrategy := Bool → Option Bool → FinDist Bool

def completionLaw (policy : program.information.BehavioralPolicy 0)
    (secret signal : Bool) : FinDist Bool :=
  (policy (openingInfo secret signal)).map fun choice => (openingValue choice.1).isSome

theorem openingLaw_eq_completionLaw (policy : program.information.BehavioralPolicy 0)
    (secret signal : Bool) :
    openingLaw policy secret signal = (completionLaw policy secret signal).map
      (fun complete => if complete then some secret else none) := by
  unfold openingLaw completionLaw
  rw [FinDist.map_comp]
  apply FinDist.map_congr_of_eq_on_support
  intro choice _
  obtain ⟨complete, rfl⟩ := openingChoiceAt_exhaustive secret signal choice
  change (if complete then some secret else none) =
    if (if complete then some secret else none).isSome then some secret else none
  cases complete <;> rfl

def extractSender (policy : program.information.BehavioralPolicy 0) : SenderStrategy :=
  ⟨bindingLaw policy, completionLaw policy⟩

def liftOpening (rule : Bool → Bool → FinDist Bool) :
    program.information.BehavioralPolicy 0 := by
  classical
  intro info
  let input := decodeOpeningInfo info
  exact if hinfo : openingInfo input.1 input.2 = info then
    hinfo ▸ (rule input.1 input.2).map (openingChoiceAt input.1 input.2)
  else FinDist.pure (program.defaultPureProfile 0 info)

def liftSender (strategy : SenderStrategy) : program.information.BehavioralPolicy 0 := by
  classical
  exact Function.update (liftOpening strategy.complete) bindingInfo
    (strategy.binding.map bindingChoice)

theorem openingInfo_ne_bindingInfo (secret signal : Bool) :
    openingInfo secret signal ≠ bindingInfo := by
  intro heq
  have hlength := congrArg (fun info => info.own.length) heq
  change 2 = 0 at hlength
  contradiction

theorem liftSender_opening (strategy : SenderStrategy) (secret signal : Bool) :
    liftSender strategy (openingInfo secret signal) =
      (strategy.complete secret signal).map (openingChoiceAt secret signal) := by
  classical
  rw [liftSender, Function.update_of_ne (openingInfo_ne_bindingInfo secret signal)]
  unfold liftOpening
  dsimp only
  rw [decode_openingInfo]
  simp

@[simp] theorem bindingLaw_liftSender (strategy : SenderStrategy) :
    bindingLaw (liftSender strategy) = strategy.binding := by
  classical
  simp only [bindingLaw, liftSender, Function.update_self, FinDist.map_comp]
  have hinverse : (fun choice => bindingBit choice.1) ∘ bindingChoice = id :=
    funext bindingBit_action
  rw [hinverse, FinDist.map_id]

@[simp] theorem completionLaw_liftSender (strategy : SenderStrategy) (secret signal : Bool) :
    completionLaw (liftSender strategy) secret signal = strategy.complete secret signal := by
  unfold completionLaw
  rw [liftSender_opening, FinDist.map_comp]
  have hinverse : (fun choice => (openingValue choice.1).isSome) ∘
      openingChoiceAt secret signal = id := by
    funext complete
    change (if complete then some secret else none).isSome = complete
    cases complete <;> rfl
  rw [hinverse, FinDist.map_id]

@[simp] theorem extractSender_lift (strategy : SenderStrategy) :
    extractSender (liftSender strategy) = strategy := by
  have hcomplete : completionLaw (liftSender strategy) = strategy.complete :=
    funext fun secret => funext fun signal => completionLaw_liftSender strategy secret signal
  cases strategy
  simp only [extractSender, bindingLaw_liftSender, hcomplete]

def liftResponder (strategy : ResponderStrategy) : program.information.BehavioralPolicy 1 := by
  classical
  intro info
  let input := decodeResponseInfo info
  exact if hinfo : responseInfo input.1 input.2 = info then
    hinfo ▸ (strategy input.1 input.2).map (responseChoiceAt input.1 input.2)
  else FinDist.pure (program.defaultPureProfile 1 info)

theorem liftResponder_response (strategy : ResponderStrategy) (signal : Bool)
    (opening : Option Bool) :
    liftResponder strategy (responseInfo signal opening) =
      (strategy signal opening).map (responseChoiceAt signal opening) := by
  classical
  unfold liftResponder
  dsimp only
  rw [decode_responseInfo]
  simp

@[simp] theorem responseLaw_liftResponder (strategy : ResponderStrategy) (signal : Bool)
    (opening : Option Bool) : responseLaw (liftResponder strategy) signal opening =
      strategy signal opening := by
  unfold responseLaw
  rw [liftResponder_response, FinDist.map_comp]
  have hinverse : (fun choice => responseBit choice.1) ∘
      responseChoiceAt signal opening = id := funext responseBit_action
  rw [hinverse, FinDist.map_id]

end VegasTests.OptionalDisclosure
