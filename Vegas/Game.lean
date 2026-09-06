/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Core.Mixed
import GameTheory.Languages.FOSG
import Vegas.EventGraph.FiniteState
import Vegas.Machine.Program

/-!
# Vegas games

A Vegas game is a finite, informed execution protocol with real utility on
realized histories. The execution protocol is the canonical denotation:
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
open GameTheory.Languages
open GameTheory.Protocol

universe uPlayer uGame

/-- The semantic result of compiling a finite Vegas description. `horizon` is
proof data for the strategic view, not a stopping rule: stopping remains the
execution protocol's `terminal` predicate. -/
structure Game (Player : Type uPlayer) where
  arena : FOSG.Game.{uPlayer, uGame, uGame, uGame, uGame, uGame} Player
  utility : arena.History → Player → ℝ
  horizon : ℕ
  bounded : arena.execution.BoundedHorizon horizon

namespace Game

variable {Player : Type uPlayer} (G : Game Player)

/-- Information-local pure policies and their induced history law. -/
@[reducible]
def pureForm : GameForm Player :=
  G.arena.toGameForm G.horizon

/-- The pure-policy utility game consumed by GameTheory's ordinary solution
concepts. -/
def pure : UtilityGame Player where
  form := G.pureForm
  utility := G.utility

variable [Fintype Player]

/-- Information-local behavioral policies and their induced history law. -/
@[reducible]
def behavioralForm : GameForm Player :=
  G.arena.information.toBehavioralGameForm G.horizon

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

end Game

namespace Machine.Program

variable {Player : Type} [DecidableEq Player] [Fintype Player]
variable {L : IExpr}

/-- The informed stochastic arena presented by a machine program. -/
def arena (program : Machine.Program Player L) : FOSG.Game Player where
  execution := program.execution
  information := program.information

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
def utility (program : Machine.Program Player L) : program.arena.History → Player → ℝ :=
  fun history => program.payoutUtility history.state

@[simp] theorem utility_of_not_terminal (program : Machine.Program Player L)
    (history : program.arena.History) (who : Player)
    (hterminal : ¬ program.terminal history.state) :
    program.utility history who = 0 := by
  classical
  simp [utility, payoutUtility, hterminal]

/-- Attach an economic interpretation and player utilities to the compiled
execution. Neither the interpretation nor utility is executed by the contract,
and neither changes legal actions, observations, or well-formedness. Utilities
may depend on more than payouts, and need not be integer-valued or linear. -/
def outcomeGame (program : Machine.Program Player L) {Outcome : Type}
    (observe : program.State → Outcome) (valuation : Outcome → Player → ℝ) : Game Player where
  arena := program.arena
  utility history who := valuation (observe history.state) who
  horizon := program.graph.nodeCount
  bounded := program.boundedHorizon

/-- A live compiled event graph, its observation model, payoff projection, and
uniform termination proof form one Vegas game. -/
def game (program : Machine.Program Player L) : Game Player :=
  program.outcomeGame id program.payoutUtility

end Machine.Program

namespace WFProgram

variable {Player : Type} [DecidableEq Player] [Fintype Player]
variable {L : IExpr}

/-- Compile a checked source program all the way to its canonical Vegas game. -/
def game (program : WFProgram Player L) : Game Player :=
  (Machine.compile program).game

/-- Finite source domains enumerate the canonical execution state without
changing its semantic representation. -/
@[reducible]
noncomputable def stateFintype
    (program : WFProgram Player L) [FiniteDomains program] :
    Fintype program.game.arena.execution.State := by
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
    Fintype (program.game.arena.execution.Action who) := by
  let compiled := ToEventGraph.compile program.core
  letI : ∀ node : Fin compiled.graph.nodeCount,
      Fintype (L.Val (compiled.graph.nodeRow node).ty) :=
    ToEventGraph.compile_nodeFintype program
  exact EventGraph.FrontierAction.instFintype compiled.graph who

end WFProgram

end Vegas
