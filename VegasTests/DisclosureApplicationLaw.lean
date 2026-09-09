/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureApplicationExecution
import VegasTests.DisclosureSourcePolicies

/-! # Complete source-generated policy assembly for disclosure

All three strategic decisions in the checked example are projected from one
source behavioral profile into the native owner and responder controllers.
For the specified pure profile and inclusion script, the message-policy game
and independent AST execution have the same terminal-environment law,
including the undisclosed binding. This is a pure benchmark theorem, not a
general compiler result, service guarantee for arbitrary environments, or
simulation of target deviations.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Vegas Interaction GameTheory.Math.Probability

/-- Proof-facing source outcomes retain all terminal bindings. This readout
does not expose the private binding to a runtime policy or settle pending runs. -/
def sourceOutcome? {window : Nat} (execution : (application window).PolicyExecution) :
    Option (VEnv simpleExpr TerminalContext) :=
  (policyData? execution).map fun data =>
    terminalEnv data.secret data.signal data.opening data.response

/-- The actual public-message execution has the independent AST's terminal
environment law under the stated pure policies and inclusion script. -/
theorem honest_source_law (payouts : List (TestPlayer × Expr PayoffContext .int))
    (window : Nat) (secret : Bool) (complete : Bool → Bool → Bool)
    (response : Bool → Option Bool → Bool) :
    (((application window).policyGame honestEnvironment honestSchedule
      (initial window)).play
        (honestPlayers secret complete response)).map
            sourceOutcome? =
      (denoteSource (coreWithPayoffs payouts)
        (SourcePolicies.pureProfile payouts secret complete response)
        (VEnv.empty simpleExpr)).map some := by
  have hlaw := congrArg
    (fun law : FinDist (Option RunData) => law.map
      (Option.map fun data => terminalEnv data.secret data.signal data.opening data.response))
    (honest_policy_data window secret complete response)
  rw [SourcePolicies.pure_law, FinDist.map_comp]
  simp only [FinDist.map_comp, Function.comp_def, Option.map_some] at hlaw
  exact hlaw

/-- The complete generated policy assembly for the checked source has its
source terminal-environment law under the benchmark inclusion script. -/
theorem compiled_source_law (window : Nat) (secret : Bool)
    (complete : Bool → Bool → Bool) (response : Bool → Option Bool → Bool) :
    (((application window).policyGame honestEnvironment honestSchedule
      (initial window)).play
        (compiledPlayers (SourcePolicies.pureProfile
          [(0, payoff)] secret complete response))).map sourceOutcome? =
      (denoteSource source.prog
        (SourcePolicies.pureProfile [(0, payoff)] secret complete response)
        source.env).map some := by
  rw [compiledPlayers_pure]
  exact honest_source_law [(0, payoff)] window secret complete response

/-- Every supported run of these controllers and this inclusion script
settles. This is not termination under arbitrary delivery policies. -/
theorem honest_settles (window : Nat) (secret : Bool)
    (complete : Bool → Bool → Bool) (response : Bool → Option Bool → Bool)
    (next : (application window).PolicyExecution)
    (hnext : next ∈ (((application window).policyGame honestEnvironment honestSchedule
      (initial window)).play (honestPlayers secret complete response)).support) :
    next.native.application.outcome?.isSome = true := by
  have hmem : policyData? next ∈
      ((((application window).policyGame honestEnvironment honestSchedule
        (initial window)).play (honestPlayers secret complete response)).map
          policyData?).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [honest_policy_data window secret complete response, FinDist.support_map] at hmem
  obtain ⟨signal, _, hdata⟩ := hmem
  cases hresult : next.native.application.outcome?.isSome
  · simp [policyData?, hresult] at hdata
  · rfl

/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.honest_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.honest_source_law

/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.compiled_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.compiled_source_law

end VegasTests.OptionalDisclosure.DisclosureState
