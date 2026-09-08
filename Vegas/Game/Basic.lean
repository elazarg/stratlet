/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Core.Mixed
import GameTheory.Protocol.Strategic
import Vegas.EventGraph.FiniteState
import Vegas.Compile.Machine

/-!
# Bounded Vegas game analyses

This module packages a compiled event graph's finite, informed execution
protocol with real utility on realized histories for bounded analysis. The
execution protocol remains the canonical runtime denotation:
state-dependent legal actions, stochastic transitions, public/private signals,
and information-local policies all remain visible to GameTheory without a
second strategic semantics.

The pure and behavioral strategic forms below are direct views supplied by
GameTheory. Equilibria, deviations, assessments, backward induction, and
language translations are consequently the upstream definitions and theorems.
-/

noncomputable section

namespace Vegas

open GameTheory
open GameTheory.Protocol

universe uPlayer uGame

/-- A bounded utility analysis of one execution and information model.  The
operational and information semantics are the owners; presentation formats are
derived views. `horizon` is proof data, not a stopping rule. -/
structure BoundedGame (Player : Type uPlayer) where
  execution : ExecutionProtocol.{uPlayer, uGame, uGame} Player
  information : InformationModel.{uPlayer, uGame, uGame, uGame, uGame, uGame} execution
  utility : execution.History → Player → ℝ
  horizon : ℕ
  bounded : execution.BoundedHorizon horizon

namespace BoundedGame

variable {Player : Type uPlayer} (G : BoundedGame Player)

/-- Information-local pure policies and their induced history law. -/
@[reducible]
def pureForm : GameForm Player :=
  G.information.toGameForm G.horizon

/-- The pure-policy utility game consumed by GameTheory's ordinary solution
concepts. -/
def pure : UtilityGame Player where
  form := G.pureForm
  utility := G.utility

variable [Fintype Player]

/-- Information-local behavioral policies and their induced history law. -/
@[reducible]
def behavioralForm : GameForm Player :=
  G.information.toBehavioralGameForm G.horizon

/-- The behavioral-policy utility game. This is distinct from static mixing:
behavioral policies draw locally when an information state is consulted. -/
def behavioral : UtilityGame Player where
  form := G.behavioralForm
  utility := G.utility

/-- Static randomization over complete pure information-local policies.  This
is GameTheory's ordinary mixed extension, not behavioral randomization. -/
@[reducible]
def mixedPure : UtilityGame Player :=
  G.pure.mixed

end BoundedGame

namespace Machine.Program

variable {Player : Type} [DecidableEq Player] [Fintype Player]
variable {L : IExpr}

/-- Evaluate the compiled integer payout as a real-valued score. This is the
default monetary utility convention, not a restriction on other valuations.
Nonterminal states have no
source payoff yet and receive zero; the bounded-horizon certificate ensures
that every history produced by either strategic form is terminal by the game
horizon. -/
def payoutUtility (program : Machine.Program Player L) :
    program.State → Player → ℝ :=
  fun state who => by
    classical
    exact
      if program.terminal state then
        match EventGraph.evalPayoffs? program.payoffs state.1.store with
        | some outcome => (outcome who : ℝ)
        | none => 0
      else
        0

/-- The default history valuation uses the integer payout convention. -/
def utility (program : Machine.Program Player L) : program.execution.History → Player → ℝ :=
  fun history => program.payoutUtility history.state

@[simp] theorem utility_of_not_terminal (program : Machine.Program Player L)
    (history : program.execution.History) (who : Player)
    (hterminal : ¬ program.terminal history.state) :
    program.utility history who = 0 := by
  classical
  simp [utility, payoutUtility, hterminal]

/-- Attach an economic interpretation and player utilities to the compiled
execution. Neither the interpretation nor utility is executed by the contract,
and neither changes legal actions, observations, or well-formedness. Utilities
may depend on more than payouts, and need not be integer-valued or linear. -/
def boundedOutcomeGame (program : Machine.Program Player L) {Outcome : Type}
    (observe : program.State → Outcome) (valuation : Outcome → Player → ℝ) :
    BoundedGame Player where
  execution := program.execution
  information := program.information
  utility history who := valuation (observe history.state) who
  horizon := program.graph.nodeCount
  bounded := program.boundedHorizon

/-- Package a live compiled event graph, its observation model, payoff
projection, and uniform termination proof for bounded strategic analysis. -/
def boundedGame (program : Machine.Program Player L) : BoundedGame Player :=
  program.boundedOutcomeGame id program.payoutUtility

end Machine.Program

namespace WFProgram

variable {Player : Type} [DecidableEq Player] [Fintype Player]
variable {L : IExpr}

/-- Compile a checked source program into the compiled graph's bounded
strategic analysis. The independent written-order source semantics remains a
distinct semantic endpoint. -/
def boundedGame (program : WFProgram Player L) : BoundedGame Player :=
  (Machine.compile program).boundedGame

/-- Finite source domains enumerate the canonical execution state without
changing its semantic representation. -/
@[reducible]
noncomputable def stateFintype
    (program : WFProgram Player L) [FiniteDomains program] :
    Fintype program.boundedGame.execution.State := by
  let compiled := ToEventGraph.compile program.core
  letI : ∀ field : Fin compiled.graph.fieldCount,
      Fintype (L.Val (compiled.graph.fieldRow field).ty) :=
    ToEventGraph.compile_fieldFintype program
  exact EventGraph.StateSnapshot.reachableConfigFintype
    compiled.graph compiled.graphWF

/-- Finite source domains enumerate each player's node-typed frontier packet. -/
@[reducible]
noncomputable def actionFintype
    (program : WFProgram Player L) [FiniteDomains program] (who : Player) :
    Fintype (program.boundedGame.execution.Action who) := by
  let compiled := ToEventGraph.compile program.core
  letI : ∀ node : Fin compiled.graph.nodeCount,
      Fintype (L.Val (compiled.graph.nodeRow node).ty) :=
    ToEventGraph.compile_nodeFintype program
  exact EventGraph.FrontierAction.instFintype compiled.graph who

end WFProgram

end Vegas
