/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.ObservedAbort

/-!
# Bounded disclosure windows

A pending disclosure has a fixed observation and finitely many delivery slots.
In each slot the player may submit a request or remain silent. A valid request
completes the window; a rejected request or silence consumes a slot; exhausting
the window aborts. Policies may randomize and remember all their own attempts.

Every such policy induces one observation-local completion rule, and every
rule is implemented by an immediate valid request or silence until timeout.
Consequently the window is deviation-adequate for one observed quit decision.

The slot semantics guarantees delivery and deadline progress. It adds no new
game observations while the window is open and ignores transaction costs.
Cryptographic validity, real-time inclusion, and new public messages must be
justified separately before applying this model to a chain.
-/

noncomputable section

namespace Vegas.Runtime.DisclosureWindow

open GameTheory GameTheory.Math.Probability

variable {Info Request Outcome : Type}

/-- Validation depends only on information the player already has; the player
can construct a valid disclosure from that information. -/
structure Gate (Info Request : Type) where
  accepts : Info → Request → Bool
  validRequest : Info → Request
  accepts_valid : ∀ info, accepts info (validRequest info) = true

abbrev Policy (Info Request : Type) :=
  Info → List (Option Request) → FinDist (Option Request)

def accepted (gate : Gate Info Request) (info : Info) : Option Request → Bool
  | none => false
  | some request => gate.accepts info request

/-- Histories list the player's attempts, newest first. False is timeout,
not a rejected transaction: rejection leaves the window open if slots remain. -/
def execute (gate : Gate Info Request) (policy : Policy Info Request) (info : Info) :
    Nat → List (Option Request) → FinDist Bool
  | 0, _ => FinDist.pure false
  | slots + 1, history => (policy info history).bind fun attempt =>
      if accepted gate info attempt then FinDist.pure true
      else execute gate policy info slots (attempt :: history)

def effectiveRule (gate : Gate Info Request) (slots : Nat)
    (policy : Policy Info Request) : ObservedAbort.Rule Info :=
  fun info => execute gate policy info slots []

/-- The first attempt samples the abstract decision. Choosing to quit means
sending nothing in this and every later slot, not invoking a privileged exit. -/
def compileRule (gate : Gate Info Request) (rule : ObservedAbort.Rule Info) :
    Policy Info Request :=
  fun info history => if history = [] then
    (rule info).map fun complete => if complete then some (gate.validRequest info) else none
  else FinDist.pure none

theorem execute_compileRule_nonempty (gate : Gate Info Request)
    (rule : ObservedAbort.Rule Info) (info : Info) (slots : Nat)
    (history : List (Option Request)) (hne : history ≠ []) :
    execute gate (compileRule gate rule) info slots history = FinDist.pure false := by
  induction slots generalizing history with
  | zero => rfl
  | succ slots ih =>
    simpa [execute, compileRule, hne, accepted] using
      ih (none :: history) (List.cons_ne_nil _ _)

@[simp] theorem effectiveRule_compileRule (gate : Gate Info Request)
    (slots : Nat) (rule : ObservedAbort.Rule Info) :
    effectiveRule gate (slots + 1) (compileRule gate rule) = rule := by
  funext info
  simp only [effectiveRule, execute, compileRule, ↓reduceIte, FinDist.bind_map]
  calc
    _ = (rule info).bind (fun complete => FinDist.pure complete) := by
      apply FinDist.bind_congr
      intro complete _
      cases complete
      · simp only [Bool.false_eq_true, ↓reduceIte, accepted]
        exact execute_compileRule_nonempty gate rule info slots _ (List.cons_ne_nil _ _)
      · simp [accepted, gate.accepts_valid]
    _ = _ := by simp

/-- Arbitrary retries and malformed requests add no completion laws beyond
the single observation-local decision, provided at least one slot remains. -/
theorem effectiveRule_surjective (gate : Gate Info Request) (slots : Nat) :
    Function.Surjective (effectiveRule gate (slots + 1)) :=
  fun rule => ⟨compileRule gate rule, effectiveRule_compileRule gate slots rule⟩

/-- Prospective completion law with concrete request execution. The causal
theorem below moves future continuation sampling after the delivery window. -/
def play (gate : Gate Info Request) (slots : Nat)
    (law : FinDist Outcome) (observe : Outcome → Info)
    (policy : Policy Info Request) : FinDist (Outcome ⊕ Info) :=
  law.bind fun outcome =>
    (execute gate policy (observe outcome) slots []).map fun complete =>
      if complete then Sum.inl outcome else Sum.inr (observe outcome)

theorem play_eq (gate : Gate Info Request) (slots : Nat)
    (law : FinDist Outcome) (observe : Outcome → Info) (policy : Policy Info Request) :
    play gate slots law observe policy =
      ObservedAbort.run law observe (effectiveRule gate slots policy) := rfl

theorem play_causal {Checkpoint : Type} (gate : Gate Info Request) (slots : Nat)
    (checkpoints : FinDist Checkpoint) (continuation : Checkpoint → FinDist Outcome)
    (checkpointObserve : Checkpoint → Info) (observe : Outcome → Info)
    (policy : Policy Info Request)
    (hobserve : ∀ checkpoint ∈ checkpoints.support,
      ∀ outcome ∈ (continuation checkpoint).support,
        observe outcome = checkpointObserve checkpoint) :
    play gate slots (checkpoints.bind continuation) observe policy =
      checkpoints.bind fun checkpoint =>
        (execute gate policy (checkpointObserve checkpoint) slots []).bind fun complete =>
          if complete then (continuation checkpoint).map Sum.inl
          else FinDist.pure (Sum.inr (checkpointObserve checkpoint)) :=
  ObservedAbort.run_causal checkpoints continuation checkpointObserve observe
    (effectiveRule gate slots policy) hobserve

namespace Game

variable {Player : Type} [DecidableEq Player] {S : Type*}

abbrev signature (source : UtilityGame Player) (Info Request : Type) : GameSignature Player where
  Strategy who := source.form.sig.Strategy who × Policy Info Request
  Outcome := source.form.sig.Outcome ⊕ Info

def game (source : UtilityGame Player) (observe : source.form.sig.Outcome → Info)
    (last : Player) (abortPayoff : Info → Player → ℝ)
    (gate : Gate Info Request) (slots : Nat) : UtilityGame Player where
  form := ⟨signature source Info Request, fun profile =>
    play gate slots (source.form.play (fun who => (profile who).1)) observe (profile last).2⟩
  utility := (ObservedAbort.Game.game source observe last abortPayoff).utility

def compileStrategy (gate : Gate Info Request)
    (strategy : S × ObservedAbort.Rule Info) : S × Policy Info Request :=
  ⟨strategy.1, compileRule gate strategy.2⟩

def backtranslateStrategy (gate : Gate Info Request) (slots : Nat)
    (strategy : S × Policy Info Request) : S × ObservedAbort.Rule Info :=
  ⟨strategy.1, effectiveRule gate slots strategy.2⟩

@[simp] theorem backtranslate_compile (gate : Gate Info Request) (slots : Nat)
    (strategy : S × ObservedAbort.Rule Info) :
    backtranslateStrategy gate (slots + 1) (compileStrategy gate strategy) = strategy := by
  simp [backtranslateStrategy, compileStrategy]

/-- A uniform strategy back-translation, independent of opponents and source
profiles, covers every randomized history-dependent request policy. -/
def adequacy (source : UtilityGame Player) (observe : source.form.sig.Outcome → Info)
    (last : Player) (abortPayoff : Info → Player → ℝ)
    (gate : Gate Info Request) (slots : Nat) :
    DeviationAdequacy (ObservedAbort.Game.game source observe last abortPayoff)
      (game source observe last abortPayoff gate (slots + 1)) where
  compileStrategy _ := compileStrategy gate
  backtranslateStrategy _ := backtranslateStrategy gate (slots + 1)
  decodeOutcome := id
  utility_eq := rfl
  compiled_considered _ _ := trivial
  honest_law profile := by
    simp only [game, play_eq, FinDist.map_id, compileStrategy,
      effectiveRule_compileRule, ObservedAbort.Game.game, ObservedAbort.Game.play]
  deviation_law profile who replacement _ := by
    simp only [game, play_eq, FinDist.map_id, ObservedAbort.Game.game,
      ObservedAbort.Game.play]
    have hback :
        (fun player => backtranslateStrategy gate (slots + 1)
          (Profile.update (fun player => compileStrategy gate (profile player))
            who replacement player)) =
        Profile.update profile who (backtranslateStrategy gate (slots + 1) replacement) := by
      funext player
      by_cases heq : player = who
      · subst player; simp
      · simp [Profile.update, heq]
    have hfirst := congrArg (fun p => fun player => (p player).1) hback
    have hlast := congrArg (fun p => (p last).2) hback
    simpa only [backtranslateStrategy] using
      congrArg₂ (fun initial rule => ObservedAbort.run (source.form.play initial) observe rule)
        hfirst hlast

/-- The exact observed-quitting criterion applies to actual finite request
histories, not just strategies already shaped like a Boolean quit rule. -/
theorem nash_compile_iff (source : UtilityGame Player)
    (observe : source.form.sig.Outcome → Info) (profile : Profile source.form.sig)
    (last : Player) (abortPayoff : Info → Player → ℝ)
    (gate : Gate Info Request) (slots : Nat) :
    IsNash (game source observe last abortPayoff gate (slots + 1)).form
      (euPreference (game source observe last abortPayoff gate (slots + 1)).utility)
      ((adequacy source observe last abortPayoff gate slots).compileProfile
        (ObservedAbort.Game.compileProfile source profile)) ↔
    IsNash source.form (euPreference source.utility) profile ∧
      ∀ replacement : source.form.sig.Strategy last,
        ObservedAbort.envelope (source.form.play (Profile.update profile last replacement))
          observe (fun outcome => source.utility outcome last) (fun info => abortPayoff info last) ≤
            expectedUtility source.utility last (source.form.play profile) := by
  rw [(adequacy source observe last abortPayoff gate slots).isNash_compileProfile_iff]
  exact ObservedAbort.Game.nash_compile_iff source observe profile last abortPayoff

end Game

end Vegas.Runtime.DisclosureWindow
