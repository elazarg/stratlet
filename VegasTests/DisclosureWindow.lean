/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.DisclosureWindow
import VegasTests.ObservedAbort
import VegasTests.MatchingPenniesEquilibrium

/-! # Authenticated disclosure, rejected requests, and finite timeout -/

noncomputable section

namespace VegasTests.DisclosureWindow

open GameTheory GameTheory.Math.Probability Vegas.Runtime

abbrev Info := ObservedAbort.Info
abbrev Request := ObservedAbort.Player × Bool

/-- Caller identity is authenticated metadata. Validation requires player zero
and the bit it already knows; this is an ideal equality check, not a hash proof. -/
def gate : Vegas.Runtime.DisclosureWindow.Gate Info Request where
  accepts info request := decide (request.1 = 0 ∧ request.2 = info.1)
  validRequest info := (0, info.1)
  accepts_valid _ := by simp

theorem foreign_caller_rejected (info : Info) (bit : Bool) :
    gate.accepts info (1, bit) = false := by simp [gate]

theorem wrong_opening_rejected (info : Info) :
    gate.accepts info (0, !info.1) = false := by
  cases info with
  | mk own signal => cases own <;> simp [gate]

def silent : Vegas.Runtime.DisclosureWindow.Policy Info Request :=
  fun _ _ => FinDist.pure none

theorem silence_times_out (slots : Nat) (info : Info) (history : List (Option Request)) :
    Vegas.Runtime.DisclosureWindow.execute gate silent info slots history = FinDist.pure false := by
  induction slots generalizing history with
  | zero => rfl
  | succ slots ih =>
    simpa [Vegas.Runtime.DisclosureWindow.execute, silent,
      Vegas.Runtime.DisclosureWindow.accepted] using ih (none :: history)

/-- One invalid opening followed by the correct opening. Rejection is not an
immediate quit; the subsequent delivered request may still complete. -/
def retry : Vegas.Runtime.DisclosureWindow.Policy Info Request :=
  fun info history => FinDist.pure (some (0, if history = [] then !info.1 else info.1))

theorem retry_completes (slots : Nat) (info : Info) :
    Vegas.Runtime.DisclosureWindow.effectiveRule gate (slots + 2) retry info =
      FinDist.pure true := by
  cases info with
  | mk own signal =>
    cases own <;>
      simp [Vegas.Runtime.DisclosureWindow.effectiveRule,
        Vegas.Runtime.DisclosureWindow.execute, retry,
        Vegas.Runtime.DisclosureWindow.accepted, gate]

/-- The exact threshold covers arbitrary initial bit distributions and all
randomized, history-dependent request sequences over a nonempty window. -/
theorem multistage_nash_iff (slots : Nat) (abortPayoff : Info → ObservedAbort.Player → ℝ)
    (abortValue : ℝ) (hconstant : ∀ info, abortPayoff info 0 = abortValue) :
    IsNash (Vegas.Runtime.DisclosureWindow.Game.game ObservedAbort.source
      ObservedAbort.observe 0 abortPayoff gate (slots + 1)).form
      (euPreference (Vegas.Runtime.DisclosureWindow.Game.game ObservedAbort.source
        ObservedAbort.observe 0 abortPayoff gate (slots + 1)).utility)
      ((Vegas.Runtime.DisclosureWindow.Game.adequacy ObservedAbort.source
          ObservedAbort.observe 0 abortPayoff gate slots).compileProfile
        (Vegas.Runtime.ObservedAbort.Game.compileProfile ObservedAbort.source
          ObservedAbort.fairProfile)) ↔ abortValue ≤ -1 := by
  rw [(Vegas.Runtime.DisclosureWindow.Game.adequacy ObservedAbort.source
    ObservedAbort.observe 0 abortPayoff gate slots).isNash_compileProfile_iff]
  exact ObservedAbort.abort_threshold_iff abortPayoff abortValue hconstant

/-- This is the causally ordered request/timeout law, with future chance
sampled only after a successful disclosure, for every request policy. -/
theorem multistage_causal (slots : Nat) (profile : Profile ObservedAbort.signature)
    (policy : Vegas.Runtime.DisclosureWindow.Policy Info Request) :
    Vegas.Runtime.DisclosureWindow.play gate slots (ObservedAbort.sourcePlay profile)
      ObservedAbort.observe policy =
      (ObservedAbort.checkpoints profile).bind fun checkpoint =>
        (Vegas.Runtime.DisclosureWindow.execute gate policy
          (ObservedAbort.checkpointObserve checkpoint) slots []).bind fun complete =>
            if complete then (ObservedAbort.continuation checkpoint).map Sum.inl
            else FinDist.pure (Sum.inr (ObservedAbort.checkpointObserve checkpoint)) := by
  rw [Vegas.Runtime.DisclosureWindow.play_eq, ObservedAbort.causal_law]
  rfl

/-- A compiled source game's payoff-informed quit pass also admits the concrete
window implementation. The request is an authenticated completion message;
observing prospective utility remains a separate, explicit model premise. -/
def completionGate : Vegas.Runtime.DisclosureWindow.Gate ℝ Unit where
  accepts _ _ := true
  validRequest _ := ()
  accepts_valid _ := rfl

def compiledGame := MatchingPenniesEquilibrium.program.boundedGame.behavioral

def compiledObservation (history : compiledGame.form.sig.Outcome) : ℝ :=
  compiledGame.utility history 0

def compiledWindowAdequacy (slots : Nat) (abortPayoff : ℝ → VegasTests.TestPlayer → ℝ) :
    DeviationAdequacy
      (Vegas.Runtime.ObservedAbort.Game.game compiledGame compiledObservation 0 abortPayoff)
      (Vegas.Runtime.DisclosureWindow.Game.game compiledGame compiledObservation 0
        abortPayoff completionGate (slots + 1)) :=
  Vegas.Runtime.DisclosureWindow.Game.adequacy compiledGame compiledObservation 0
    abortPayoff completionGate slots

/-- info: 'VegasTests.DisclosureWindow.multistage_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.DisclosureWindow.multistage_nash_iff

/-- info: 'VegasTests.DisclosureWindow.multistage_causal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.DisclosureWindow.multistage_causal

/-- info: 'VegasTests.DisclosureWindow.compiledWindowAdequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.DisclosureWindow.compiledWindowAdequacy

end VegasTests.DisclosureWindow
