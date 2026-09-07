/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureOpening

/-! # The full execution law of the optional-disclosure encoding -/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

theorem terminal_prefix_law (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History) (fuel : Nat) :
    program.terminalStateLaw profile history =
      (program.information.runBehavioralFrom profile fuel history).bind
        (program.terminalStateLaw profile) := by
  calc
    _ = (program.information.runBehavioralFrom profile (program.graph.nodeCount + fuel)
        history).map ExecutionProtocol.History.state :=
      (congrArg (fun law : FinDist program.execution.History =>
        law.map ExecutionProtocol.History.state)
          (program.information.runBehavioralFrom_bound_add profile
            program.boundedHorizon fuel history)).symm
    _ = _ := by
      rw [Nat.add_comm, program.information.runBehavioralFrom_add, FinDist.map_bind]
      rfl

/-- Extracted finite decision process: binding, independent public chance,
informed optional opening, then an informed reply. No runtime policies are
restricted when extracting this law. -/
def semanticLaw (profile : ∀ who, program.information.BehavioralPolicy who) : FinDist RunData :=
  (bindingLaw (profile 0)).bind fun secret =>
    fairCoin.denote.bind fun signal =>
      (openingLaw (profile 0) secret signal).bind fun opening =>
        (responseLaw (profile 1) signal opening).map fun response =>
          ⟨secret, signal, opening, response⟩

/-- The complete terminal configuration law for every behavioral profile,
including combined changes to the binding, informed opening, and reply policies.
Strategy lifting and equivalence with a frontend game are separate obligations. -/
theorem terminal_law (profile : ∀ who, program.information.BehavioralPolicy who) :
    (program.terminalStateLaw profile program.execution.initHistory).map Subtype.val =
      (semanticLaw profile).map (fun data => cfg data 8) := by
  rw [terminal_prefix_law profile program.execution.initHistory 4, FinDist.map_bind]
  let inputs := (bindingLaw (profile 0)).bind fun secret =>
    fairCoin.denote.map (fun signal => (secret, signal))
  have hinputs : (program.information.runBehavioral profile 4).map ownerSummary =
      inputs.map (fun input => checkpointSummary input.1 input.2 3) := by
    simpa only [inputs, FinDist.map_bind, FinDist.map_comp, Function.comp_def] using
      opening_checkpoint_law profile
  calc
    _ = inputs.bind (fun input => (openingLaw (profile 0) input.1 input.2).bind fun opening =>
        (responseLaw (profile 1) input.2 opening).map
          (fun response => cfg ⟨input.1, input.2, opening, response⟩ 8)) := by
      exact FinDist.bind_eq_of_map_eq
        (program.information.runBehavioral profile 4) inputs ownerSummary
        (fun input : Bool × Bool => checkpointSummary input.1 input.2 3) hinputs
        (fun history => (program.terminalStateLaw profile history).map
          (fun state : program.State => state.1))
        (fun input : Bool × Bool => (openingLaw (profile 0) input.1 input.2).bind fun opening =>
          (responseLaw (profile 1) input.2 opening).map
            (fun response => cfg ⟨input.1, input.2, opening, response⟩ 8))
        (fun history _ input _ hsummary =>
          opening_terminal_law profile history input.1 input.2 hsummary)
    _ = _ := by
      simp only [inputs, semanticLaw, FinDist.bind_bind, FinDist.bind_map,
        FinDist.map_bind, FinDist.map_comp, Function.comp_def]

/-- info: 'VegasTests.OptionalDisclosure.terminal_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.terminal_law

end VegasTests.OptionalDisclosure
