/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureApplicationInvariant
import VegasTests.DisclosurePayoff
import VegasTests.DisclosureReachability

/-! # Source outcomes of complete public disclosure interactions

The endpoint is the actual written source program, for any public payout list.
Every supported policy execution yielding a completed native outcome has a
source execution with the same hidden binding, public signal, optional opening,
and response. Pending runs remain outside this terminal statement. This is
support correspondence, not equality of laws or strategic backtranslation.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Vegas EventGraph Interaction

theorem decodedConfig_reachable (state : DisclosureState) (hinvariant : Invariant state) :
    Reachable graph state.decodedConfig :=
  cfg_reachable state.data (data_valid state hinvariant) state.phase

/-- The native completion flags and partial outcome readout match the actual
reachable graph prefix under arbitrary player and environment policies. -/
theorem policy_decoded_prefix (window : Nat)
    (players : TestPlayer → (application window).PlayerPolicy)
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (next : (application window).PolicyExecution)
    (hnext : next ∈ (((application window).policyGame environment schedule
      (initial window)).play players).support) :
    Reachable graph next.native.application.decodedConfig ∧
      (∀ index : Fin graph.nodeCount, next.native.application.done index.val = true ↔
        index ∈ next.native.application.decodedConfig.done) ∧
      (next.native.application.outcome?.isSome = true ↔
        Terminal graph next.native.application.decodedConfig) := by
  have hinvariant := policy_invariant window players environment schedule next hnext
  exact ⟨decodedConfig_reachable _ hinvariant,
    done_iff_decodedConfig_done _ hinvariant, outcome_isSome_iff_terminal _ hinvariant⟩

theorem outcome_eq_some_iff (state : DisclosureState)
    (signal : Bool) (opening : Option Bool) (response : Bool) :
    state.outcome? = some (signal, opening, response) ↔
      state.signal = some signal ∧ state.publication = some opening ∧
        state.response = some response := by
  cases hsignal : state.signal <;> cases hpublication : state.publication <;>
    cases hresponse : state.response <;> simp [outcome?, hsignal, hpublication, hresponse]

/-- The completed public readout and retained private binding determine the
actual source execution and compiled payout evaluation. -/
theorem outcome_source (payouts : Payouts) (state : DisclosureState)
    (hinvariant : Invariant state) (signal : Bool) (opening : Option Bool) (response : Bool)
    (houtcome : state.outcome? = some (signal, opening, response)) :
    ∃ secret,
      state.service.lookup (0, 0) = some secret ∧
      state.decodedConfig = cfg ⟨secret, signal, opening, response⟩ 8 ∧
      SmallStep.Star (SourceConfig.initial (coreWithPayoffs payouts))
        ⟨TerminalContext, terminalEnv secret signal opening response, .ret payouts⟩ ∧
      evalPayoffs? (programWithPayoffs payouts).payoffs state.decodedConfig.store =
        some (evalPayoffs payouts (terminalEnv secret signal opening response)) := by
  obtain ⟨hsignal, hpublication, hresponse⟩ :=
    (outcome_eq_some_iff state signal opening response).mp houtcome
  obtain ⟨secret, hstored, hvalid⟩ := hinvariant.2.2.2.2.1 opening hpublication
  have hcfg : state.decodedConfig = cfg ⟨secret, signal, opening, response⟩ 8 := by
    simp [decodedConfig, phase, data, hstored, hsignal, hpublication, hresponse]
  exact ⟨secret, hstored, hcfg, source_execution payouts secret signal opening response hvalid,
    hcfg ▸ cfg_payoff payouts ⟨secret, signal, opening, response⟩⟩

/-- Arbitrary controllers and adaptive environment policies retain terminal
source support through the complete native application, starting from empty. -/
theorem policy_outcome_source (payouts : Payouts) (window : Nat)
    (players : TestPlayer → (application window).PlayerPolicy)
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (next : (application window).PolicyExecution)
    (hnext : next ∈ (((application window).policyGame environment schedule
      (initial window)).play players).support)
    (signal : Bool) (opening : Option Bool) (response : Bool)
    (houtcome : next.native.application.outcome? = some (signal, opening, response)) :
    ∃ secret,
      next.native.application.service.lookup (0, 0) = some secret ∧
      next.native.application.decodedConfig = cfg ⟨secret, signal, opening, response⟩ 8 ∧
      SmallStep.Star (SourceConfig.initial (coreWithPayoffs payouts))
        ⟨TerminalContext, terminalEnv secret signal opening response, .ret payouts⟩ ∧
      evalPayoffs? (programWithPayoffs payouts).payoffs
          next.native.application.decodedConfig.store =
        some (evalPayoffs payouts (terminalEnv secret signal opening response)) := by
  exact outcome_source payouts next.native.application
    (policy_invariant window players environment schedule next hnext)
    signal opening response houtcome

/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.policy_decoded_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.policy_decoded_prefix

/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.policy_outcome_source' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.policy_outcome_source

end VegasTests.OptionalDisclosure.DisclosureState
