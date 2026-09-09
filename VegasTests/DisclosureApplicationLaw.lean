/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureApplicationExecution
import VegasTests.DisclosureSourcePolicies

/-! # Written-source laws through public disclosure execution

The message-policy game and the AST denotation are independent executions.
Their laws agree for the specified pure source policies and inclusion script,
including the undisclosed binding. This instance neither supplies a service
guarantee for arbitrary environments nor simulates arbitrary target deviations.
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

end VegasTests.OptionalDisclosure.DisclosureState
