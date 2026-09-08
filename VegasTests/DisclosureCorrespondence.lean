/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosurePolicy

/-! # Full finite disclosure strategy correspondence

The source here is an explicitly defined finite decision process, not the
denotation of the richer Kotlin frontend. Its sender binds a Boolean before
public chance, then chooses whether to disclose that binding. The responder
sees the signal and optional disclosure. The original binding is retained in
the outcome for analysis, not exposed to the responder's policy.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

def Strategy : TestPlayer → Type
  | 0 => SenderStrategy
  | 1 => ResponderStrategy

def compilePolicy : (who : TestPlayer) → Strategy who →
    program.information.BehavioralPolicy who
  | 0 => liftSender
  | 1 => liftResponder

def extractPolicy : (who : TestPlayer) → program.information.BehavioralPolicy who →
    Strategy who
  | 0 => extractSender
  | 1 => responseLaw

@[simp] theorem extract_compile_policy (who : TestPlayer) (strategy : Strategy who) :
    extractPolicy who (compilePolicy who strategy) = strategy := by
  fin_cases who
  · exact extractSender_lift strategy
  · exact funext fun signal => funext fun opening =>
      responseLaw_liftResponder strategy signal opening

def finiteLaw (profile : ∀ who, Strategy who) : FinDist RunData :=
  ((profile 0).binding).bind fun secret =>
    fairCoin.denote.bind fun signal =>
      ((profile 0).complete secret signal).bind fun complete =>
        let opening := if complete then some secret else none
        (profile 1 signal opening).map fun response =>
          ⟨secret, signal, opening, response⟩

def finiteForm : GameForm TestPlayer where
  sig := { Strategy := Strategy, Outcome := RunData }
  play := finiteLaw

def compileProfile (profile : Profile finiteForm.sig) :
    Profile program.boundedGame.behavioral.form.sig := fun who => compilePolicy who (profile who)

def extractProfile (profile : Profile program.boundedGame.behavioral.form.sig) :
    Profile finiteForm.sig := fun who => extractPolicy who (profile who)

@[simp] theorem extract_compile_profile (profile : Profile finiteForm.sig) :
    extractProfile (compileProfile profile) = profile := by
  funext who
  exact extract_compile_policy who (profile who)

/-- Extraction is coordinatewise: replacing one player's entire policy leaves
every opponent's source strategy unchanged. -/
theorem extractProfile_update (profile : Profile program.boundedGame.behavioral.form.sig)
    (who : TestPlayer) (replacement : program.information.BehavioralPolicy who) :
    extractProfile (Profile.update profile who replacement) =
      Profile.update (extractProfile profile) who (extractPolicy who replacement) := by
  funext player
  by_cases heq : player = who
  · subst player
    simp [extractProfile]
  · simp [extractProfile, Profile.update_of_ne, heq]

theorem semanticLaw_eq_finiteLaw (profile : Profile program.boundedGame.behavioral.form.sig) :
    semanticLaw profile = finiteLaw (extractProfile profile) := by
  unfold semanticLaw finiteLaw
  apply congrArg ((bindingLaw (profile 0)).bind)
  funext secret
  apply congrArg fairCoin.denote.bind
  funext signal
  rw [openingLaw_eq_completionLaw, FinDist.bind_map]
  rfl

def decodeConfig (state : Config graph) : RunData where
  secret := (Store.getAs state.store 0 .bool).getD false
  signal := (Store.getAs state.store 3 .bool).getD false
  opening := (Store.getAs state.store 5 (.option .bool)).getD none
  response := (Store.getAs state.store 7 .bool).getD false

@[simp] theorem decodeConfig_cfg (data : RunData) : decodeConfig (cfg data 8) = data := by
  cases data
  rfl

def decodeHistory (history : program.execution.History) : RunData :=
  decodeConfig history.state.1

/-- Exact decoded terminal law for all graph behavioral profiles. This is
stronger than a selected-profile or honest-run equality. -/
theorem all_profile_law (profile : Profile program.boundedGame.behavioral.form.sig) :
    (program.boundedGame.behavioral.form.play profile).map decodeHistory =
      finiteForm.play (extractProfile profile) := by
  have hlaw := congrArg (fun law : FinDist (Config graph) => law.map decodeConfig)
    (terminal_law profile)
  simp only [Machine.Program.terminalStateLaw, FinDist.map_comp, Function.comp_def,
    decodeConfig_cfg, semanticLaw_eq_finiteLaw] at hlaw
  change (program.boundedGame.behavioral.form.play profile).map decodeHistory =
    (finiteLaw (extractProfile profile)).map id at hlaw
  exact hlaw.trans (FinDist.map_id _)

theorem compiled_law (profile : Profile finiteForm.sig) :
    (program.boundedGame.behavioral.form.play (compileProfile profile)).map decodeHistory =
      finiteForm.play profile := by
  rw [all_profile_law, extract_compile_profile]

/-- Every unilateral graph replacement has exactly the law of its finite
source replacement against the same, unchanged opponents. -/
theorem deviation_law (profile : Profile finiteForm.sig) (who : TestPlayer)
    (replacement : program.information.BehavioralPolicy who) :
    (program.boundedGame.behavioral.form.play
      (Profile.update (compileProfile profile) who replacement)).map decodeHistory =
        finiteForm.play (Profile.update profile who (extractPolicy who replacement)) := by
  rw [all_profile_law, extractProfile_update, extract_compile_profile]

/-- The graph policy space may contain extra off-site behavior; lifting the
extracted profile preserves its complete decoded outcome law. -/
theorem outcome_roundtrip (profile : Profile program.boundedGame.behavioral.form.sig) :
    (program.boundedGame.behavioral.form.play (compileProfile (extractProfile profile))).map
        decodeHistory =
      (program.boundedGame.behavioral.form.play profile).map decodeHistory := by
  rw [compiled_law, all_profile_law]

/-- info: 'VegasTests.OptionalDisclosure.all_profile_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.all_profile_law

/-- info: 'VegasTests.OptionalDisclosure.deviation_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.deviation_law

end VegasTests.OptionalDisclosure
