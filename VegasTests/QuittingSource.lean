/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.Game

/-!
# A compiled source with an explicit pre-continuation decision checkpoint

A forced-false acknowledgment and its reveal fence the public coin after both
hidden choices. A forced-true completion acknowledgment gates future chance
and disclosure of the original choices. These acknowledgments carry no free
source choice; a runtime may implement their absence by a timeout outcome.

The distribution expressions explicitly retain their marker reads, even
though both conditional branches have the same fair law. Textual sequencing
alone does not impose those dependencies.

This module checks source well-formedness and compiled graph staging.
QuittingStrategy and QuittingEquilibrium prove the complete outcome-law and
Nash correspondence with the smaller kernel, for every behavioral profile.
QuittingCheckpoint identifies the full completion-checkpoint information with
own bit and public coin. QuittingImplementation and QuittingWindow connect
the compiled execution to causal quitting and bounded request histories.
-/

noncomputable section

namespace VegasTests.QuittingSource

open Vegas EventGraph

abbrev PayoffContext : CtxSimple :=
  [(9, .bool), (8, .bool), (7, .bool), (6, .bool), (4, .bool), (3, .bool)]

def same : Expr PayoffContext .bool :=
  .eq (.var 8 (.there .here)) (.var 9 .here)

def signal : Expr PayoffContext .bool :=
  .var 4 (.there (.there (.there (.there .here))))

def future : Expr PayoffContext .bool :=
  .var 7 (.there (.there .here))

def payoff (positive : Bool) : Expr PayoffContext .int :=
  let signed := fun bit => Expr.ite bit (.constInt (if positive then 1 else -1))
    (.constInt (if positive then -1 else 1))
  .addInt (.addInt (signed same) (signed signal)) (signed future)

def core : VegasCore TestPlayer simpleExpr [] :=
  .commit 0 0 (.constBool true)
    (.commit 1 1 (.constBool true)
      (.commit 2 0 (.notBool (.var 2 .here))
        (.reveal 3 0 2 .here
          (.sample 4 (.ite (.var 3 .here)
            (.weighted (b := .bool) fairCoin) (.weighted (b := .bool) fairCoin))
            (.commit 5 0 (.var 5 .here)
              (.reveal 6 0 5 .here
                (.sample 7 (.ite (.var 6 .here)
                  (.weighted (b := .bool) fairCoin) (.weighted (b := .bool) fairCoin))
                  (.reveal 8 0 0
                    (.there (.there (.there (.there (.there (.there (.there .here)))))))
                    (.reveal 9 1 1
                      (.there (.there (.there (.there (.there (.there (.there .here)))))))
                      (.ret [(0, payoff true), (1, payoff false)]))))))))))

def source : WFProgram TestPlayer simpleExpr where
  core :=
    { Γ := []
      prog := core
      env := VEnv.empty simpleExpr
      wctx := by simp
      fresh := by simp [core, FreshBindings, Fresh] }
  reveals := by decide
  legal := by
    unfold core
    constructor
    · intro _; exact ⟨false, rfl⟩
    · constructor
      · intro _; exact ⟨false, rfl⟩
      · constructor
        · intro _; exact ⟨false, rfl⟩
        · constructor
          · intro _; exact ⟨true, rfl⟩
          · trivial

abbrev program := Machine.compile source

instance finiteDomains : FiniteDomains source where
  context := inferInstanceAs (FiniteVCtx ([] : VCtx TestPlayer simpleExpr))
  program :=
    { proof := .commit inferInstance (.commit inferInstance (.commit inferInstance
        (.reveal inferInstance (.sample inferInstance (.commit inferInstance
          (.reveal inferInstance (.sample inferInstance (.reveal inferInstance
            (.reveal inferInstance .ret))))))))) }

theorem perfectRecall : program.information.PerfectRecall := program.perfectRecall

def behavioralMixedAdequacy :
    Runtime.DeviationAdequacy source.game.behavioral source.game.mixedPure :=
  source.behavioralToMixedPureAdequacy

def node (index : Fin 10) : Fin program.graph.nodeCount := index

theorem nodeCount : program.graph.nodeCount = 10 := rfl

theorem initial_choices_independent :
    program.graph.prereqs (node 0) = ∅ ∧ program.graph.prereqs (node 1) = ∅ := by
  decide

/-- The constant acknowledgment's reveal cannot precede either hidden choice. -/
theorem public_marker_fence :
    node 0 ∈ program.graph.prereqs (node 3) ∧
    node 1 ∈ program.graph.prereqs (node 3) ∧
    node 2 ∈ program.graph.prereqs (node 3) := by
  decide

theorem signal_waits_for_marker :
    node 3 ∈ program.graph.prereqs (node 4) := by decide

theorem completion_observes_signal :
    node 4 ∈ program.graph.prereqs (node 5) := by decide

theorem future_waits_for_completion :
    node 5 ∈ program.graph.prereqs (node 6) ∧
    node 6 ∈ program.graph.prereqs (node 7) := by decide

theorem hidden_disclosures_wait_for_completion :
    node 5 ∈ program.graph.prereqs (node 8) ∧
    node 5 ∈ program.graph.prereqs (node 9) := by decide

/-- Initial automatic closure cannot draw either coin in this compiled graph. -/
theorem coins_not_initially_ready :
    ¬ Ready program.graph (Config.initial program.graph) (node 4) ∧
    ¬ Ready program.graph (Config.initial program.graph) (node 7) := by
  constructor
  · intro hready
    have hmem := hready.2 signal_waits_for_marker
    simp [Config.initial] at hmem
  · intro hready
    have hmem := hready.2 future_waits_for_completion.2
    simp [Config.initial] at hmem

/-- info: 'VegasTests.QuittingSource.coins_not_initially_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.QuittingSource.coins_not_initially_ready

/-- info: 'VegasTests.QuittingSource.behavioralMixedAdequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.QuittingSource.behavioralMixedAdequacy

end VegasTests.QuittingSource
