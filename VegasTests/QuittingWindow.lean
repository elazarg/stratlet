/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.QuittingImplementation

/-! # Bounded request execution at the compiled game's checkpoint

The prefix and continuation are the compiled program's executions. The window
allows arbitrary randomized request histories on the complete checkpoint
information. Delivery, finite deadline progress, unchanged information during
the window, and absence of transaction costs are properties of this model.
-/

noncomputable section

namespace VegasTests.QuittingSource

open Vegas GameTheory GameTheory.Math.Probability

variable {Request : Type}

abbrev windowSignature (Request : Type) : GameSignature TestPlayer where
  Strategy who := program.information.BehavioralPolicy who ×
    Runtime.DisclosureWindow.Policy FullInfo Request
  Outcome := ObservedAbort.Outcome ⊕ ObservedAbort.Info

def compiledWindowGame (abortPayoff : ObservedAbort.Info → TestPlayer → ℝ)
    (gate : Runtime.DisclosureWindow.Gate FullInfo Request) (slots : Nat) :
    UtilityGame TestPlayer where
  form := ⟨windowSignature Request, fun profile =>
    compiledQuitPlay (fun who => (profile who).1)
      (Runtime.DisclosureWindow.effectiveRule gate slots (profile 0).2)⟩
  utility := (compiledQuitGame abortPayoff).utility

def compileWindowStrategy (gate : Runtime.DisclosureWindow.Gate FullInfo Request)
    (who : TestPlayer)
    (strategy : FinDist Bool × Runtime.ObservedAbort.Rule ObservedAbort.Info) :
    (windowSignature Request).Strategy who :=
  (liftStrategy who strategy.1,
    Runtime.DisclosureWindow.compileRule gate (fun info => strategy.2 (decodeInfo info)))

def backtranslateWindowStrategy (gate : Runtime.DisclosureWindow.Gate FullInfo Request)
    (slots : Nat) (who : TestPlayer) (strategy : (windowSignature Request).Strategy who) :
    FinDist Bool × Runtime.ObservedAbort.Rule ObservedAbort.Info :=
  (extractStrategy who strategy.1, fun info =>
    Runtime.DisclosureWindow.effectiveRule gate slots strategy.2 (encodeInfo info))

@[simp] theorem backtranslate_compile_window
    (gate : Runtime.DisclosureWindow.Gate FullInfo Request) (slots : Nat) (who : TestPlayer)
    (strategy : FinDist Bool × Runtime.ObservedAbort.Rule ObservedAbort.Info) :
    backtranslateWindowStrategy gate (slots + 1) who
      (compileWindowStrategy gate who strategy) = strategy := by
  simp [backtranslateWindowStrategy, compileWindowStrategy]

/-- Run the actual compiled prefix, execute all requests until acceptance or
timeout, and run the compiled continuation only after acceptance. -/
theorem compiledWindowGame_law (abortPayoff : ObservedAbort.Info → TestPlayer → ℝ)
    (gate : Runtime.DisclosureWindow.Gate FullInfo Request) (slots : Nat)
    (profile : Profile (windowSignature Request)) :
    (compiledWindowGame abortPayoff gate slots).form.play profile =
      (Runtime.ObservedAbort.Game.game ObservedAbort.source ObservedAbort.observe
        0 abortPayoff).form.play
          (fun who => backtranslateWindowStrategy gate slots who (profile who)) := by
  exact (compiledQuitPlay_eq _ _).trans (ObservedAbort.causal_law _ _).symm

/-- Every technically available request policy has one uniform source
deviation. At least one slot is needed to implement the complete action. -/
def windowAdequacy (abortPayoff : ObservedAbort.Info → TestPlayer → ℝ)
    (gate : Runtime.DisclosureWindow.Gate FullInfo Request) (slots : Nat) :
    Runtime.DeviationAdequacy
      (Runtime.ObservedAbort.Game.game ObservedAbort.source ObservedAbort.observe 0 abortPayoff)
      (compiledWindowGame abortPayoff gate (slots + 1)) where
  compileStrategy := compileWindowStrategy gate
  backtranslateStrategy := backtranslateWindowStrategy gate (slots + 1)
  decodeOutcome := id
  utility_eq := rfl
  compiled_considered _ _ := trivial
  honest_law profile := by
    simp only [FinDist.map_id, compiledWindowGame_law, backtranslate_compile_window]
  deviation_law profile who replacement _ := by
    rw [FinDist.map_id, compiledWindowGame_law]
    congr 1
    funext player
    by_cases heq : player = who
    · subst player; simp
    · simp [Profile.update, heq]

/-- Sharp Nash threshold against combined compiled-game and request-history
deviations, with no restriction to policies already shaped like quit rules. -/
theorem compiled_window_threshold_iff (abortPayoff : ObservedAbort.Info → TestPlayer → ℝ)
    (gate : Runtime.DisclosureWindow.Gate FullInfo Request) (slots : Nat)
    (abortValue : ℝ) (hconstant : ∀ info, abortPayoff info 0 = abortValue) :
    IsNash (compiledWindowGame abortPayoff gate (slots + 1)).form
      (euPreference (compiledWindowGame abortPayoff gate (slots + 1)).utility)
      ((windowAdequacy abortPayoff gate slots).compileProfile
        (Runtime.ObservedAbort.Game.compileProfile ObservedAbort.source
          ObservedAbort.fairProfile)) ↔ abortValue ≤ -1 := by
  rw [(windowAdequacy abortPayoff gate slots).isNash_compileProfile_iff]
  exact ObservedAbort.abort_threshold_iff abortPayoff abortValue hconstant

/-- An ideal authenticated opening check. This is not a cryptographic
commitment implementation: the request metadata and stored bit are semantic. -/
def checkpointGate : Runtime.DisclosureWindow.Gate FullInfo (TestPlayer × Bool) where
  accepts info request := decide (request.1 = 0 ∧ request.2 = (decodeInfo info).1)
  validRequest info := (0, (decodeInfo info).1)
  accepts_valid _ := by simp

theorem checkpointGate_wrong_opening (info : FullInfo) :
    checkpointGate.accepts info (0, !(decodeInfo info).1) = false := by
  cases hbit : (decodeInfo info).1 <;> simp [checkpointGate, hbit]

theorem checkpointGate_foreign_caller (info : FullInfo) (bit : Bool) :
    checkpointGate.accepts info (1, bit) = false := by
  simp [checkpointGate]

/-- info: 'VegasTests.QuittingSource.windowAdequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.QuittingSource.windowAdequacy

/-- info: 'VegasTests.QuittingSource.compiled_window_threshold_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.QuittingSource.compiled_window_threshold_iff

end VegasTests.QuittingSource
