/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.QuittingStrategy

/-! # Strategic correspondence for the compiled staged source -/

noncomputable section

namespace VegasTests.QuittingSource

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

theorem terminal_payoff (state : program.State) (hterminal : program.terminal state)
    (who : TestPlayer) :
    program.payoutUtility state who = ObservedAbort.utility (decode state.1) who := by
  have reveal_value (index : Fin graph.nodeCount) (source : Nat)
      (hsem : (graph.nodeRow index).sem = .reveal source) :
      Store.getAs state.1.store (graph.nodeTarget index) (graph.nodeRow index).ty =
        Store.getAs state.1.store source (graph.nodeRow index).ty := by
    obtain ⟨row, hrow, hvalid⟩ := reachable_validDoneValues program.graphWF state.2
      index (hterminal index)
    have heq : row = graph.nodeRow index :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow index))
    subst row
    rw [hsem] at hvalid
    obtain ⟨value, htarget, hsource⟩ := hvalid
    exact htarget.trans hsource.symm
  have hleft : readBit state.1 8 = readBit state.1 0 :=
    congrArg (fun value : Option Bool => value.getD false) (reveal_value (node 8) 0 rfl)
  have hright : readBit state.1 9 = readBit state.1 1 :=
    congrArg (fun value : Option Bool => value.getD false) (reveal_value (node 9) 1 rfl)
  let compiled := ToEventGraph.compile source.core
  let available : ∀ {name ty} (binding : VHasVar compiled.terminalCtx name ty),
      ∃ value, Store.getAs state.1.store (compiled.terminalState.fieldOf binding) ty.base =
        some value := fun binding =>
    Machine.sourceBindingsAvailableAtTerminal compiled state hterminal binding
  let env := ToEventGraph.sourceEnvOfStore compiled.terminalState state.1.store available
  have henv : env =
      VEnv.cons (L := simpleExpr) (x := 9) (τ := .pub .bool) (readBit state.1 9)
      (VEnv.cons (L := simpleExpr) (x := 8) (τ := .pub .bool) (readBit state.1 8)
      (VEnv.cons (L := simpleExpr) (x := 7) (τ := .pub .bool) (readBit state.1 7)
      (VEnv.cons (L := simpleExpr) (x := 6) (τ := .pub .bool) (readBit state.1 6)
      (VEnv.cons (L := simpleExpr) (x := 5) (τ := .sealed 0 .bool) (readBit state.1 5)
      (VEnv.cons (L := simpleExpr) (x := 4) (τ := .pub .bool) (readBit state.1 4)
      (VEnv.cons (L := simpleExpr) (x := 3) (τ := .pub .bool) (readBit state.1 3)
      (VEnv.cons (L := simpleExpr) (x := 2) (τ := .sealed 0 .bool) (readBit state.1 2)
      (VEnv.cons (L := simpleExpr) (x := 1) (τ := .sealed 1 .bool) (readBit state.1 1)
      (VEnv.cons (L := simpleExpr) (x := 0) (τ := .sealed 0 .bool) (readBit state.1 0)
        (VEnv.empty simpleExpr)))))))))) := by
    funext name ty binding
    have hget := ToEventGraph.sourceEnvOfStore_get compiled.terminalState
      state.1.store available binding
    cases binding with
    | here => exact (congrArg (Option.getD · false) hget).symm
    | there binding =>
        cases binding with
        | here => exact (congrArg (Option.getD · false) hget).symm
        | there binding =>
            cases binding with
            | here => exact (congrArg (Option.getD · false) hget).symm
            | there binding =>
                cases binding with
                | here => exact (congrArg (Option.getD · false) hget).symm
                | there binding =>
                    cases binding with
                    | here => exact (congrArg (Option.getD · false) hget).symm
                    | there binding =>
                        cases binding with
                        | here => exact (congrArg (Option.getD · false) hget).symm
                        | there binding =>
                            cases binding with
                            | here => exact (congrArg (Option.getD · false) hget).symm
                            | there binding =>
                                cases binding with
                                | here => exact (congrArg (Option.getD · false) hget).symm
                                | there binding =>
                                    cases binding with
                                    | here => exact (congrArg (Option.getD · false) hget).symm
                                    | there binding =>
                                        cases binding with
                                        | here => exact (congrArg (Option.getD · false) hget).symm
                                        | there binding =>
                                            cases binding
  have heval := compiled.evalPayoffs_eq_sourceEnvOfStore state.1.store available
  change evalPayoffs? program.payoffs state.1.store = some (evalPayoffs compiled.sourcePayoffs env)
    at heval
  rw [henv] at heval
  rw [Machine.Program.payoutUtility, if_pos hterminal, heval]
  fin_cases who <;> simp [compiled, source, core, ToEventGraph.compile, ToEventGraph.compileCore,
    evalPayoffs, payoff, same, signal, future, evalExpr, mkPayout, payoffAt,
    VEnv.erasePubEnv, VEnv.get, VEnv.cons, Env.get, Env.cons, ObservedAbort.utility,
    ObservedAbort.sign, decode, hleft, hright]
  split_ifs <;> norm_num

theorem expectedUtility_eq_kernel
    (profile : ∀ who, program.information.BehavioralPolicy who) (who : TestPlayer) :
    expectedUtility program.game.behavioral.utility who
        (program.game.behavioral.form.play profile) =
      expectedUtility ObservedAbort.source.utility who
        (ObservedAbort.source.form.play
          (fun player => extractStrategy player (profile player))) := by
  unfold expectedUtility
  calc
    _ = (program.game.behavioral.form.play profile).expect
        (fun history => ObservedAbort.utility (decode history.state.1) who) := by
      apply FinDist.expect_congr
      intro history hhistory
      exact terminal_payoff history.state
        (Scheduled.runBehavioralFrom_terminal_of_bound program.information profile
          program.boundedHorizon program.execution.initHistory history hhistory) who
    _ = ((program.game.behavioral.form.play profile).map
        (fun history => decode history.state.1)).expect
          (fun outcome => ObservedAbort.utility outcome who) :=
      (FinDist.expect_map (fun history : program.execution.History => decode history.state.1)
        (program.game.behavioral.form.play profile)
        (fun outcome => ObservedAbort.utility outcome who)).symm
    _ = _ := congrArg (fun law => law.expect (fun outcome => ObservedAbort.utility outcome who))
      (decoded_law_eq_kernel profile)

theorem extract_update (profile : ∀ who, program.information.BehavioralPolicy who)
    (who : TestPlayer) (replacement : program.information.BehavioralPolicy who) :
    (fun player => extractStrategy player
      (Profile.update (sig := program.game.behavioral.form.sig) profile who replacement player)) =
      Profile.update (sig := ObservedAbort.signature)
        (fun player => extractStrategy player (profile player)) who
        (extractStrategy who replacement) := by
  funext player
  by_cases heq : player = who
  · subst player
    simp
  · simp [Profile.update, heq]

/-- Nash equilibrium is both preserved and reflected by initial-strategy
extraction; every source replacement has a legal behavioral lift. -/
theorem nash_iff_kernel
    (profile : ∀ who, program.information.BehavioralPolicy who) :
    IsNash program.game.behavioral.form (euPreference program.game.behavioral.utility) profile ↔
      IsNash ObservedAbort.source.form (euPreference ObservedAbort.source.utility)
        (fun who => extractStrategy who (profile who)) := by
  rw [isNash_iff, isNash_iff]
  constructor
  · intro h who replacement
    have hdev := h who (liftStrategy who replacement)
    change expectedUtility _ _ _ ≤ expectedUtility _ _ _ at hdev ⊢
    simpa only [expectedUtility_eq_kernel, extract_update, extract_lift] using hdev
  · intro h who replacement
    have hdev := h who (extractStrategy who replacement)
    change expectedUtility _ _ _ ≤ expectedUtility _ _ _ at hdev ⊢
    simpa only [expectedUtility_eq_kernel, extract_update] using hdev

def fairProfile : ∀ who, program.information.BehavioralPolicy who :=
  fun who => liftStrategy who ObservedAbort.fair

theorem fair_isNash :
    IsNash program.game.behavioral.form
      (euPreference program.game.behavioral.utility) fairProfile := by
  apply (nash_iff_kernel fairProfile).mpr
  have heq : (fun who => extractStrategy who (fairProfile who)) = ObservedAbort.fairProfile := by
    funext who
    exact extract_lift who ObservedAbort.fair
  exact heq.symm ▸ ObservedAbort.fair_isNash

/-- An arbitrary unilateral behavioral adversary changes neither player's
expected payoff against the fair opponent. No adversarial objective is assumed. -/
theorem fair_deviation_payoff (who victim : TestPlayer)
    (replacement : program.information.BehavioralPolicy who) :
    expectedUtility program.game.behavioral.utility victim
      (program.game.behavioral.form.play (Profile.update fairProfile who replacement)) = 0 := by
  rw [expectedUtility_eq_kernel, extract_update]
  have heq : (fun who => extractStrategy who (fairProfile who)) = ObservedAbort.fairProfile := by
    funext player
    exact extract_lift player ObservedAbort.fair
  rw [heq]
  exact ObservedAbort.deviation_zero who victim (extractStrategy who replacement)

theorem fair_serialized_isPlayerNash
    (schedulerUtility : program.serializedArena.History → ℝ)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler) :
    Scheduled.IsPlayerNash (program.serializedGame schedulerUtility).behavioral
      (program.compileSerializedBehavioralProfile scheduler fairProfile) :=
  program.isPlayerNash_compileSerialized_of_isNash
    schedulerUtility scheduler fairProfile fair_isNash

theorem fair_serialized_deviation_payoff
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (who victim : TestPlayer)
    (replacement : program.serializedArena.information.BehavioralPolicy (.player who)) :
    (program.serializedArena.information.runBehavioral
      (Function.update (program.compileSerializedBehavioralProfile scheduler fairProfile)
        (.player who) replacement) graph.nodeCount).expect
          (fun history => program.payoutUtility history.state.base victim) = 0 :=
  program.serializedDeviation_expect_eq scheduler fairProfile who
    (fun state => program.payoutUtility state victim) 0
    (fun alternative => fair_deviation_payoff who victim alternative) replacement

/-- info: 'VegasTests.QuittingSource.decoded_law_eq_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.QuittingSource.decoded_law_eq_kernel

/-- info: 'VegasTests.QuittingSource.nash_iff_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.QuittingSource.nash_iff_kernel

/-- info: 'VegasTests.QuittingSource.fair_serialized_isPlayerNash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.QuittingSource.fair_serialized_isPlayerNash

/-- info: 'VegasTests.QuittingSource.fair_serialized_deviation_payoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.QuittingSource.fair_serialized_deviation_payoff

end VegasTests.QuittingSource
