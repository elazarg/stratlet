/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.QuittingCheckpoint
import Vegas.Runtime.DisclosureWindow

/-! # Causal quitting in the compiled staged game

Execute the compiled prefix, consult the player's complete information state,
and execute the compiled continuation only on completion. The back-translation
uses no opponent strategy and covers every information-local quitting rule.
-/

noncomputable section

namespace VegasTests.QuittingSource

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

abbrev FullInfo := PlayerInformation graph (0 : TestPlayer)

def checkpointSummary (checkpoint : ObservedAbort.Checkpoint) : CheckpointSummary :=
  prefixSummary ((finTwoArrowEquiv Bool).symm checkpoint.1) checkpoint.2 3

theorem checkpoint_summary_law_kernel
    (profile : ∀ who, program.information.BehavioralPolicy who) :
    (program.information.runBehavioral profile 4).map summarize =
      (ObservedAbort.checkpoints (fun who => extractStrategy who (profile who))).map
        checkpointSummary := by
  rw [checkpoint_summary_law, pi_two, FinDist.bind_map]
  simp only [FinDist.product, FinDist.bind_bind, FinDist.bind_map,
    ObservedAbort.checkpoints, FinDist.map_bind, FinDist.map_comp]
  rfl

theorem completionLaw_checkpoint (bits : TestPlayer → Bool) (signal : Bool) :
    completionLaw (prefixCfg bits signal 3) =
      ObservedAbort.continuation ((bits 0, bits 1), signal) := by
  simp [completionLaw, coinLaw, prefixCfg, after_val, Config.completeNode,
    Config.initial, node, nodeCount, readBit, Store.getAs, Store.set,
    nodeTarget, TypedValue.as?, ObservedAbort.continuation]

theorem checkpoint_continuation
    (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History) (checkpoint : ObservedAbort.Checkpoint)
    (hsummary : summarize history = checkpointSummary checkpoint) :
    (program.terminalStateLaw profile history).map (fun state => decode state.1) =
      ObservedAbort.continuation checkpoint := by
  have hstate : history.state.1 =
      prefixCfg ((finTwoArrowEquiv Bool).symm checkpoint.1) checkpoint.2 3 :=
    congrArg Prod.fst hsummary
  rw [terminal_decode_law profile history (by
    rw [hstate]
    simp [ChoicesFixed, prefixCfg, after_val, Config.completeNode])]
  rw [hstate, completionLaw_checkpoint]
  rfl

/-- Actual execution stops before the completion marker. A quit skips the
remaining graph, including the future chance event and the hidden reveals. -/
def compiledQuitPlay (profile : ∀ who, program.information.BehavioralPolicy who)
    (rule : Runtime.ObservedAbort.Rule FullInfo) :
    FinDist (ObservedAbort.Outcome ⊕ ObservedAbort.Info) :=
  (program.information.runBehavioral profile 4).bind fun history =>
    (rule (program.information.infoOf 0 history.trace)).bind fun complete =>
      if complete then (program.terminalStateLaw profile history).map
        (fun state => Sum.inl (decode state.1))
      else FinDist.pure (Sum.inr (decodeInfo (program.information.infoOf 0 history.trace)))

/-- Exact causal law for arbitrary compiled-game behavioral policies and
arbitrary rules on the full checkpoint information, not a restricted projection. -/
theorem compiledQuitPlay_eq
    (profile : ∀ who, program.information.BehavioralPolicy who)
    (rule : Runtime.ObservedAbort.Rule FullInfo) :
    compiledQuitPlay profile rule =
      ObservedAbort.causalPlay (fun who => extractStrategy who (profile who))
        (fun info => rule (encodeInfo info)) := by
  unfold compiledQuitPlay ObservedAbort.causalPlay
  apply FinDist.bind_eq_of_map_eq _ _ summarize checkpointSummary
    (checkpoint_summary_law_kernel profile)
  intro history _ checkpoint _ hsummary
  have hinfo : program.information.infoOf 0 history.trace =
      encodeInfo (ObservedAbort.checkpointObserve checkpoint) := by
    exact (congrArg Prod.snd hsummary).trans
      (prefixInfo_encode ((finTwoArrowEquiv Bool).symm checkpoint.1) checkpoint.2)
  rw [hinfo, decode_encodeInfo]
  apply FinDist.bind_congr
  intro complete _
  cases complete
  · rfl
  · simp only [↓reduceIte]
    exact (FinDist.map_comp _ _ _).symm.trans
      (congrArg (fun law : FinDist ObservedAbort.Outcome =>
        law.map (Sum.inl : ObservedAbort.Outcome → ObservedAbort.Outcome ⊕ ObservedAbort.Info))
        (checkpoint_continuation profile history checkpoint hsummary))

abbrev quitSignature : GameSignature TestPlayer where
  Strategy who := program.information.BehavioralPolicy who × Runtime.ObservedAbort.Rule FullInfo
  Outcome := ObservedAbort.Outcome ⊕ ObservedAbort.Info

def compiledQuitGame (abortPayoff : ObservedAbort.Info → TestPlayer → ℝ) :
    UtilityGame TestPlayer where
  form := ⟨quitSignature, fun profile => compiledQuitPlay (fun who => (profile who).1)
    (profile 0).2⟩
  utility := (Runtime.ObservedAbort.Game.game ObservedAbort.source ObservedAbort.observe
    0 abortPayoff).utility

def compileQuitStrategy (who : TestPlayer)
    (strategy : FinDist Bool × Runtime.ObservedAbort.Rule ObservedAbort.Info) :
    quitSignature.Strategy who :=
  (liftStrategy who strategy.1, fun info => strategy.2 (decodeInfo info))

def backtranslateQuitStrategy (who : TestPlayer) (strategy : quitSignature.Strategy who) :
    FinDist Bool × Runtime.ObservedAbort.Rule ObservedAbort.Info :=
  (extractStrategy who strategy.1, fun info => strategy.2 (encodeInfo info))

@[simp] theorem backtranslate_compile_quit (who : TestPlayer)
    (strategy : FinDist Bool × Runtime.ObservedAbort.Rule ObservedAbort.Info) :
    backtranslateQuitStrategy who (compileQuitStrategy who strategy) = strategy := by
  simp [backtranslateQuitStrategy, compileQuitStrategy]

theorem compiledQuitGame_law (abortPayoff : ObservedAbort.Info → TestPlayer → ℝ)
    (profile : Profile quitSignature) :
    (compiledQuitGame abortPayoff).form.play profile =
      (Runtime.ObservedAbort.Game.game ObservedAbort.source ObservedAbort.observe
        0 abortPayoff).form.play (fun who => backtranslateQuitStrategy who (profile who)) := by
  exact (compiledQuitPlay_eq _ _).trans (ObservedAbort.causal_law _ _).symm

/-- Deviation adequacy for the actual compiled prefix and continuation. The
quitting player may change both its behavioral policy and its full-information rule. -/
def quitAdequacy (abortPayoff : ObservedAbort.Info → TestPlayer → ℝ) :
    Runtime.DeviationAdequacy
      (Runtime.ObservedAbort.Game.game ObservedAbort.source ObservedAbort.observe 0 abortPayoff)
      (compiledQuitGame abortPayoff) where
  compileStrategy := compileQuitStrategy
  backtranslateStrategy := backtranslateQuitStrategy
  decodeOutcome := id
  utility_eq := rfl
  compiled_considered _ _ := trivial
  honest_law profile := by
    simp only [FinDist.map_id, compiledQuitGame_law, backtranslate_compile_quit]
  deviation_law profile who replacement _ := by
    rw [FinDist.map_id, compiledQuitGame_law]
    congr 1
    funext player
    by_cases heq : player = who
    · subst player; simp
    · simp [Profile.update, heq]

theorem compiled_quit_threshold_iff (abortPayoff : ObservedAbort.Info → TestPlayer → ℝ)
    (abortValue : ℝ) (hconstant : ∀ info, abortPayoff info 0 = abortValue) :
    IsNash (compiledQuitGame abortPayoff).form
      (euPreference (compiledQuitGame abortPayoff).utility)
      ((quitAdequacy abortPayoff).compileProfile
        (Runtime.ObservedAbort.Game.compileProfile ObservedAbort.source
          ObservedAbort.fairProfile)) ↔ abortValue ≤ -1 := by
  rw [(quitAdequacy abortPayoff).isNash_compileProfile_iff]
  exact ObservedAbort.abort_threshold_iff abortPayoff abortValue hconstant

/-- info: 'VegasTests.QuittingSource.compiledQuitPlay_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.QuittingSource.compiledQuitPlay_eq

/-- info: 'VegasTests.QuittingSource.quitAdequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.QuittingSource.quitAdequacy

/-- info: 'VegasTests.QuittingSource.compiled_quit_threshold_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.QuittingSource.compiled_quit_threshold_iff

end VegasTests.QuittingSource
