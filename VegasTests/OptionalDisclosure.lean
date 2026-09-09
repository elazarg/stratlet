/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.Game

/-!
# An optional opening expressed in the existing core

The original Boolean stays sealed. After a forced marker and public coin,
its owner chooses a fresh optional value constrained to `none` or the original
Boolean. Only this optional copy is revealed, before the other player's reply.
The marker makes the public coin causally later than the initial binding.

This is a concrete encoding probe, not a frontend correctness theorem or a
real commitment protocol. In particular, the private equality guard is ideal.
Strict literal reveal-completeness rejects this term. A separate accounting
certificate can instead record the explicit optional resolution.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph

abbrev OpeningContext : VCtx TestPlayer simpleExpr :=
  [(3, .pub .bool), (2, .pub .bool), (1, .sealed 0 .bool), (0, .sealed 0 .bool)]

def openingGuard :
    Expr ((4, .option .bool) :: eraseVCtx (viewVCtx (0 : TestPlayer) OpeningContext)) .bool :=
  .ite (.isNone (.var 4 .here)) (.constBool true)
    (.eq (.var 4 .here) (.some (.var 0 (.there (.there (.there (.there .here)))))))

abbrev PayoffContext : CtxSimple :=
  [(7, .bool), (5, .option .bool), (3, .bool), (2, .bool)]

def payoff : Expr PayoffContext .int :=
  .ite (.isNone (.var 5 (.there .here))) (.constInt (-1))
    (.ite (.eq (.getD (.var 5 (.there .here)) (.constBool false)) (.var 7 .here))
      (.constInt 1) (.constInt 0))

def coreWithPayoffs (payouts : List (TestPlayer × Expr PayoffContext .int)) :
    VegasCore TestPlayer simpleExpr [] :=
  .commit 0 0 (.constBool true)
    (.commit 1 0 (.notBool (.var 1 .here))
      (.reveal 2 0 1 .here
        (.sample 3 (.ite (.var 2 .here)
          (.weighted (b := .bool) fairCoin) (.weighted (b := .bool) fairCoin))
          (.commit 4 0 openingGuard
            (.reveal 5 0 4 .here
              (.commit 6 1 (.constBool true)
                (.reveal 7 1 6 .here (.ret payouts))))))))

def core : VegasCore TestPlayer simpleExpr [] := coreWithPayoffs [(0, payoff)]

def source : GraphProgram TestPlayer simpleExpr where
  Γ := []
  prog := core
  env := VEnv.empty simpleExpr
  wctx := by simp
  fresh := by simp [core, coreWithPayoffs, FreshBindings, Fresh]

theorem legal : Legal source.prog := by
  unfold source core coreWithPayoffs
  constructor
  · intro _; exact ⟨false, rfl⟩
  · constructor
    · intro _; exact ⟨false, rfl⟩
    · constructor
      · intro _; exact ⟨none, rfl⟩
      · constructor
        · intro _; exact ⟨false, rfl⟩
        · trivial

abbrev compiled := ToEventGraph.compile source

def program : Machine.Program TestPlayer simpleExpr :=
  Machine.ofCompiled compiled (ToEventGraph.compile_guardLive source legal)

theorem not_reveal_complete : ¬ RevealComplete [] core := by decide

/-- The retained original binding has no direct reveal site. -/
theorem original_not_revealed : 0 ∉ RevealedSources core := by decide

theorem opened_sources : RevealedSources core = [1, 4, 6] := by decide

def node (index : Fin 8) : Fin program.graph.nodeCount := index

theorem nodeCount : program.graph.nodeCount = 8 := rfl

theorem binding_before_signal :
    node 0 ∈ program.graph.prereqs (node 2) ∧
    node 2 ∈ program.graph.prereqs (node 3) := by decide

theorem opening_after_signal : node 3 ∈ program.graph.prereqs (node 4) := by decide

theorem response_after_opening : node 5 ∈ program.graph.prereqs (node 6) := by decide

instance fieldCountNeZero : NeZero program.graph.fieldCount := ⟨by decide⟩

/-- No responder decision has the original sealed field in its footprint. -/
theorem original_not_read (index : Fin program.graph.nodeCount) (guard : EventGuard simpleExpr)
    (hsem : program.graph.node? index = some (.commit (1 : TestPlayer) guard)) :
    ({ field := 0, ty := .bool } : FieldRef simpleExpr) ∉ guard.choiceReads := by
  fin_cases index <;> cases hsem
  decide

/-- Graph-level secrecy at every configuration, not just the designated run. -/
theorem original_absent_from_response (cfg : Config program.graph)
    (index : Fin program.graph.nodeCount) :
    (observe program.graph cfg (1 : TestPlayer)).fieldValue? index 0 = none := by
  have hty : (program.graph.fieldRow 0).ty = .bool := rfl
  have hfield : (0 : Fin program.graph.fieldCount).val = 0 := rfl
  cases hnode : program.graph.node? index with
  | none => simp only [observe, hnode]
  | some sem =>
    cases sem with
    | sample dist => simp only [observe, hnode]
    | reveal source => simp only [observe, hnode]
    | commit actor guard =>
      by_cases hactor : actor = (1 : TestPlayer)
      · subst actor
        simp only [observe, hnode, hty, hfield]
        simp [original_not_read index guard hnode]
      · simp only [observe, hnode, dif_neg hactor]

theorem original_absent_from_public (cfg : Config program.graph) :
    (publicObserve program.graph cfg).fieldValue? 0 = none := by
  have howner : (program.graph.fieldRow 0).owner = some (0 : TestPlayer) := rfl
  simp [publicObserve, howner]

def openingEnv (secret signal : Bool) : VEnv simpleExpr OpeningContext :=
  ((((VEnv.empty simpleExpr).cons secret).cons false).cons false).cons signal

theorem opening_guard_iff (secret signal : Bool) (opening : Option Bool) :
    evalGuard (Player := TestPlayer) (L := simpleExpr) openingGuard opening
      ((openingEnv secret signal).toView 0).eraseEnv = true ↔
        opening = none ∨ opening = some secret := by
  cases opening with
  | none => simp [evalGuard, openingGuard, evalExpr]
  | some value =>
    cases secret <;> cases value <;> cases signal <;> decide

theorem quit_legal_after_each_signal (secret signal : Bool) :
    evalGuard (Player := TestPlayer) (L := simpleExpr) openingGuard none
      ((openingEnv secret signal).toView 0).eraseEnv = true :=
  (opening_guard_iff secret signal none).mpr (Or.inl rfl)

theorem changed_opening_rejected (secret signal : Bool) :
    evalGuard (Player := TestPlayer) (L := simpleExpr) openingGuard (some (!secret))
      ((openingEnv secret signal).toView 0).eraseEnv ≠ true := by
  intro h
  have hlegal := (opening_guard_iff secret signal (some (!secret))).mp h
  cases secret <;> simp at hlegal

abbrev ResponseContext : VCtx TestPlayer simpleExpr :=
  (5, .pub (.option .bool)) :: (4, .sealed 0 (.option .bool)) :: OpeningContext

def responseEnv (secret signal : Bool) (opening : Option Bool) :
    VEnv simpleExpr ResponseContext :=
  ((openingEnv secret signal).cons opening).cons opening

/-- The responder's source-visible environment contains the optional copy and
public coin, but neither the original binding nor the owner's private copy. -/
theorem response_view (secret signal : Bool) (opening : Option Bool) :
    ((responseEnv secret signal opening).toView (1 : TestPlayer)).eraseEnv =
      Env.cons (x := 5) opening (Env.cons (x := 3) signal
        (Env.cons (x := 2) false (Env.empty Val))) := by
  funext name ty member
  cases member with
  | here => rfl
  | there member =>
    cases member with
    | here => rfl
    | there member =>
      cases member with
      | here => rfl
      | there member => cases member

theorem response_view_eq_iff (secret otherSecret signal otherSignal : Bool)
    (opening otherOpening : Option Bool) :
    ((responseEnv secret signal opening).toView (1 : TestPlayer)).eraseEnv =
        ((responseEnv otherSecret otherSignal otherOpening).toView (1 : TestPlayer)).eraseEnv ↔
      opening = otherOpening ∧ signal = otherSignal := by
  rw [response_view, response_view]
  constructor
  · intro heq
    exact ⟨congrArg (fun env => env.get .here) heq,
      congrArg (fun env => env.get (.there .here)) heq⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Equal fixed public data give equal responder views. This does not assert
that a player's choice to quit is statistically independent of its secret. -/
theorem quit_response_view_eq (secret otherSecret signal : Bool) :
    ((responseEnv secret signal none).toView (1 : TestPlayer)).eraseEnv =
      ((responseEnv otherSecret signal none).toView (1 : TestPlayer)).eraseEnv :=
  (response_view_eq_iff secret otherSecret signal signal none none).mpr ⟨rfl, rfl⟩

theorem public_signal_distinguishable (secret : Bool) (opening : Option Bool) :
    ((responseEnv secret false opening).toView (1 : TestPlayer)).eraseEnv ≠
      ((responseEnv secret true opening).toView (1 : TestPlayer)).eraseEnv := by
  intro h
  have hsignals := (response_view_eq_iff secret secret false true opening opening).mp h
  exact Bool.false_ne_true hsignals.2

abbrev TerminalContext : VCtx TestPlayer simpleExpr :=
  (7, .pub .bool) :: (6, .sealed 1 .bool) :: ResponseContext

def terminalEnv (secret signal : Bool) (opening : Option Bool) (response : Bool) :
    VEnv simpleExpr TerminalContext :=
  ((responseEnv secret signal opening).cons response).cons response

theorem quit_payoff (secret signal response : Bool) :
    evalPayoffs [(0, payoff)] (terminalEnv secret signal none response) 0 = -1 := rfl

theorem opening_payoff (secret signal response : Bool) :
    evalPayoffs [(0, payoff)] (terminalEnv secret signal (some secret) response) 0 =
      if secret = response then 1 else 0 := by
  cases secret <;> cases response <;> rfl

theorem quitting_and_completion_distinct (secret signal response : Bool) :
    evalPayoffs [(0, payoff)] (terminalEnv secret signal none response) ≠
      evalPayoffs [(0, payoff)] (terminalEnv secret signal (some secret) response) := by
  intro heq
  have hpayoff := congrArg (fun outcome => outcome 0) heq
  rw [quit_payoff, opening_payoff] at hpayoff
  split at hpayoff <;> norm_num at hpayoff

/-- Each permitted opening and arbitrary reply has an actual source execution.
This is support-level execution evidence, not yet a policy-law comparison. -/
theorem source_execution (secret signal : Bool) (opening : Option Bool) (response : Bool)
    (hopening : opening = none ∨ opening = some secret) :
    SmallStep.Star (SourceConfig.initial core)
      ⟨TerminalContext, terminalEnv secret signal opening response, .ret [(0, payoff)]⟩ := by
  unfold SourceConfig.initial core coreWithPayoffs
  refine SmallStep.Star.trans (.single (.commit _ _ secret rfl)) ?_
  refine SmallStep.Star.trans (.single (.commit _ _ false rfl)) ?_
  refine SmallStep.Star.trans (.single (.reveal .here _)) ?_
  refine SmallStep.Star.trans (.single (.sample _ _ signal ?_)) ?_
  · change signal ∈ fairCoin.denote.support
    rw [← GameTheory.Math.Probability.FinDist.prob_pos_iff]
    unfold fairCoin
    rw [RationalLaw.prob_denote]
    dsimp
    rw [Fin.sum_univ_two]
    cases signal <;> norm_num
  refine SmallStep.Star.trans (.single (.commit _ _ opening ?_)) ?_
  · exact (opening_guard_iff secret signal opening).mpr hopening
  refine SmallStep.Star.trans (.single (.reveal .here _)) ?_
  refine SmallStep.Star.trans (.single (.commit _ _ response rfl)) ?_
  exact .single (.reveal .here _)

def signalDependentOpening (secret signal : Bool) : Option Bool :=
  if signal then none else some secret

theorem signal_dependent_execution (secret signal response : Bool) :
    SmallStep.Star (SourceConfig.initial core)
      ⟨TerminalContext, terminalEnv secret signal (signalDependentOpening secret signal) response,
        .ret [(0, payoff)]⟩ := by
  apply source_execution
  cases signal <;> simp [signalDependentOpening]

theorem different_openings_after_signals (secret : Bool) :
    signalDependentOpening secret false ≠ signalDependentOpening secret true := by
  simp [signalDependentOpening]

/-- info: 'VegasTests.OptionalDisclosure.source_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.source_execution

/-- info: 'VegasTests.OptionalDisclosure.original_absent_from_response' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.original_absent_from_response

/-- info: 'VegasTests.OptionalDisclosure.response_view_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.response_view_eq_iff

end VegasTests.OptionalDisclosure
