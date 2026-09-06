/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureCorrespondence

/-! # Compiled public payoffs for the disclosure process

Changing the final payoff expressions leaves the information and execution
graph unchanged. The strategic correspondence therefore applies to every
payoff list in the terminal public context, without replacing the actual
machine utility by an unrelated abstract utility.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

abbrev Payouts := List (TestPlayer × Expr PayoffContext .int)

def sourceWithPayoffs (payouts : Payouts) : GraphProgram TestPlayer simpleExpr where
  Γ := []
  prog := coreWithPayoffs payouts
  env := VEnv.empty simpleExpr
  wctx := by simp
  fresh := by simp [coreWithPayoffs, FreshBindings, Fresh]

theorem legalWithPayoffs (payouts : Payouts) : Legal (sourceWithPayoffs payouts).prog := by
  unfold sourceWithPayoffs coreWithPayoffs
  constructor
  · intro _; exact ⟨false, rfl⟩
  · constructor
    · intro _; exact ⟨false, rfl⟩
    · constructor
      · intro _; exact ⟨none, rfl⟩
      · constructor
        · intro _; exact ⟨false, rfl⟩
        · trivial

def programWithPayoffs (payouts : Payouts) : Machine.Program TestPlayer simpleExpr :=
  Machine.ofCompiled (ToEventGraph.compile (sourceWithPayoffs payouts))
    (ToEventGraph.compile_guardLive _ (legalWithPayoffs payouts))

theorem programWithPayoffs_graph (payouts : Payouts) :
    (programWithPayoffs payouts).graph = graph := rfl

def finiteUtility (payouts : Payouts) (data : RunData) (who : TestPlayer) : ℝ :=
  (evalPayoffs payouts (terminalEnv data.secret data.signal data.opening data.response) who : ℝ)

def finiteGame (payouts : Payouts) : UtilityGame TestPlayer where
  form := finiteForm
  utility := finiteUtility payouts

theorem cfg_payoff (payouts : Payouts) (data : RunData) :
    evalPayoffs? (programWithPayoffs payouts).payoffs (cfg data 8).store =
      some (evalPayoffs payouts
        (terminalEnv data.secret data.signal data.opening data.response)) := by
  let compiled := ToEventGraph.compile (sourceWithPayoffs payouts)
  let env := terminalEnv data.secret data.signal data.opening data.response
  have hstore : ∀ {name ty} (binding : VHasVar compiled.terminalCtx name ty),
      Store.getAs (cfg data 8).store (compiled.terminalState.fieldOf binding) ty.base =
        some (env name ty binding) := by
    intro name ty binding
    cases binding with
    | here => rfl
    | there binding => cases binding with
      | here => rfl
      | there binding => cases binding with
        | here => rfl
        | there binding => cases binding with
          | here => rfl
          | there binding => cases binding with
            | here => rfl
            | there binding => cases binding with
              | here => rfl
              | there binding => cases binding with
                | here => rfl
                | there binding => cases binding with
                  | here => rfl
                  | there binding => cases binding
  let available : ∀ {name ty} (binding : VHasVar compiled.terminalCtx name ty),
      ∃ value, Store.getAs (cfg data 8).store
        (compiled.terminalState.fieldOf binding) ty.base = some value :=
    fun binding => ⟨env _ _ binding, hstore binding⟩
  have henv : ToEventGraph.sourceEnvOfStore compiled.terminalState
      (cfg data 8).store available = env := by
    funext name ty binding
    exact Option.some.inj
      ((ToEventGraph.sourceEnvOfStore_get compiled.terminalState
        (cfg data 8).store available binding).symm.trans (hstore binding))
  have heval := compiled.evalPayoffs_eq_sourceEnvOfStore (cfg data 8).store available
  rw [henv] at heval
  exact heval

theorem settled_payoff_cfg (payouts : Payouts) (data : RunData)
    (state : program.State) (hstate : state.1 = cfg data 8) (who : TestPlayer) :
    (programWithPayoffs payouts).settledPlayerUtility state who =
      finiteUtility payouts data who := by
  have hterminal : (programWithPayoffs payouts).terminal state := by
    change Terminal graph state.1
    rw [hstate, terminal_iff]
  rw [Machine.Program.settledPlayerUtility, if_pos hterminal, hstate, cfg_payoff]
  rfl

/-- The correspondence uses the compiler's actual utility, for arbitrary
public terminal payoff expressions. -/
theorem expectedUtility_eq_finite (payouts : Payouts)
    (profile : Profile program.game.behavioral.form.sig) (who : TestPlayer) :
    expectedUtility (programWithPayoffs payouts).game.behavioral.utility who
        ((programWithPayoffs payouts).game.behavioral.form.play profile) =
      expectedUtility (finiteGame payouts).utility who
        ((finiteGame payouts).form.play (extractProfile profile)) := by
  have hlaw := terminal_law profile
  have hpayoff : ∀ state ∈ (program.terminalStateLaw profile program.execution.initHistory).support,
      (programWithPayoffs payouts).settledPlayerUtility state who =
        finiteUtility payouts (decodeConfig state.1) who := by
    intro state hstate
    have hmem : state.1 ∈
        ((program.terminalStateLaw profile program.execution.initHistory).map
          Subtype.val).support := by
      rw [FinDist.support_map]
      exact ⟨state, hstate, rfl⟩
    rw [hlaw, FinDist.support_map] at hmem
    obtain ⟨data, _, heq⟩ := hmem
    rw [settled_payoff_cfg payouts data state heq.symm, ← heq, decodeConfig_cfg]
  have hstart : expectedUtility (programWithPayoffs payouts).game.behavioral.utility who
      ((programWithPayoffs payouts).game.behavioral.form.play profile) =
      (program.terminalStateLaw profile program.execution.initHistory).expect
        (fun state => (programWithPayoffs payouts).settledPlayerUtility state who) := by
    rw [Machine.Program.terminalStateLaw, FinDist.expect_map]
    rfl
  rw [hstart, FinDist.expect_congr hpayoff]
  calc
    _ = ((program.terminalStateLaw profile program.execution.initHistory).map
        Subtype.val).expect (fun state => finiteUtility payouts (decodeConfig state) who) :=
      (FinDist.expect_map _ _ _).symm
    _ = ((semanticLaw profile).map (fun data => cfg data 8)).expect
        (fun state => finiteUtility payouts (decodeConfig state) who) :=
      congrArg (fun law : FinDist (Config graph) =>
        law.expect (fun state => finiteUtility payouts (decodeConfig state) who)) hlaw
    _ = _ := by
      rw [FinDist.expect_map]
      simp only [decodeConfig_cfg, semanticLaw_eq_finiteLaw]
      rfl

theorem nash_iff_finite (payouts : Payouts)
    (profile : Profile program.game.behavioral.form.sig) :
    IsNash (programWithPayoffs payouts).game.behavioral.form
        (euPreference (programWithPayoffs payouts).game.behavioral.utility) profile ↔
      IsNash (finiteGame payouts).form (euPreference (finiteGame payouts).utility)
        (extractProfile profile) := by
  rw [isNash_iff, isNash_iff]
  constructor
  · intro hnash who replacement
    have hdev := hnash who (compilePolicy who replacement)
    change expectedUtility _ _ _ ≤ expectedUtility _ _ _ at hdev ⊢
    simpa only [expectedUtility_eq_finite, extractProfile_update, extract_compile_policy]
      using hdev
  · intro hnash who replacement
    have hdev := hnash who (extractPolicy who replacement)
    change expectedUtility _ _ _ ≤ expectedUtility _ _ _ at hdev ⊢
    simpa only [expectedUtility_eq_finite, extractProfile_update] using hdev

end VegasTests.OptionalDisclosure
