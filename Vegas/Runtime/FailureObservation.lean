/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.DeviationAdequacy

/-!
# Failure representations behind a response barrier

A submitter chooses a raw representation and a responder chooses an action
without seeing that representation. Settlement decodes the raw value. With a
section of the decoder, this one-shot game is deviation-adequate for the game
over decoded values, for arbitrary finite randomized strategies and utilities
of the decoded value and response.

The response barrier is encoded in the strategy carrier, not proved for a
ledger. There are no subsequent choices, fees, retries, or environment ports.
Raw submissions are not restricted to a compiler image. The theorem is not an
identification of public quitting with failed openings before the barrier.
-/

noncomputable section

namespace Vegas.Runtime.FailureObservation

open GameTheory GameTheory.Math.Probability

variable {Raw Value Action : Type}

/-- The full joint law includes the responding action, not just settlement. -/
def responseLaw {Observation : Type} (observe : Raw → Observation)
    (submit : FinDist Raw) (respond : Observation → FinDist Action) :
    FinDist (Raw × Action) :=
  submit.bind fun raw => (respond (observe raw)).map fun action => (raw, action)

/-- A policy can be replaced across an observation abstraction when its actual
action law factors through that abstraction. This is a premise, not a hiding
assumption about arbitrary raw messages. -/
theorem response_law_of_factor {LeftObservation RightObservation : Type}
    (left : Raw → LeftObservation) (right : Raw → RightObservation)
    (leftPolicy : LeftObservation → FinDist Action)
    (rightPolicy : RightObservation → FinDist Action)
    (hfactor : ∀ raw, leftPolicy (left raw) = rightPolicy (right raw))
    (submit : FinDist Raw) :
    responseLaw left submit leftPolicy = responseLaw right submit rightPolicy := by
  unfold responseLaw
  apply FinDist.bind_congr
  intro raw _
  rw [hfactor]

/-- For these fixed policies, equality of the joint law for every submitter
distribution holds exactly when the response laws agree at each raw value.
An outcome decoder that forgets the response would not justify this criterion. -/
theorem response_law_iff_factor {LeftObservation RightObservation : Type}
    (left : Raw → LeftObservation) (right : Raw → RightObservation)
    (leftPolicy : LeftObservation → FinDist Action)
    (rightPolicy : RightObservation → FinDist Action) :
    (∀ submit, responseLaw left submit leftPolicy = responseLaw right submit rightPolicy) ↔
      ∀ raw, leftPolicy (left raw) = rightPolicy (right raw) := by
  constructor
  · intro hlaw raw
    have h := hlaw (FinDist.pure raw)
    simp only [responseLaw, FinDist.pure_bind] at h
    exact FinDist.map_injective (fun _ _ heq => (Prod.mk.inj heq).2) h
  · intro hfactor submit
    exact response_law_of_factor left right leftPolicy rightPolicy hfactor submit

/-- `false` is the submitter and `true` the responder. The responder has no
raw-observation argument because its action is fixed before exposure. -/
abbrev signature (Raw Action Value : Type) : GameSignature Bool where
  Strategy
    | false => FinDist Raw
    | true => FinDist Action
  Outcome := Value × Action

def play (decode : Raw → Value) (profile : Profile (signature Raw Action Value)) :
    FinDist (Value × Action) :=
  (profile false).bind fun raw => (profile true).map fun action => (decode raw, action)

def game (decode : Raw → Value) (utility : Value × Action → Bool → ℝ) :
    UtilityGame Bool where
  form := ⟨signature Raw Action Value, play decode⟩
  utility := utility

/-- Every raw distribution, including distributions outside any canonical
encoding, has the decoded distribution as an opponent-independent replacement. -/
theorem barrier_law (decode : Raw → Value) (submit : FinDist Raw)
    (respond : FinDist Action) :
    submit.bind (fun raw => respond.map fun action => (decode raw, action)) =
      (submit.map decode).bind (fun value => respond.map fun action => (value, action)) := by
  rw [FinDist.bind_map]

def compileStrategy (encode : Value → Raw) :
    (who : Bool) → (signature Value Action Value).Strategy who →
      (signature Raw Action Value).Strategy who
  | false, strategy => strategy.map encode
  | true, strategy => strategy

def backtranslateStrategy (decode : Raw → Value) :
    (who : Bool) → (signature Raw Action Value).Strategy who →
      (signature Value Action Value).Strategy who
  | false, strategy => strategy.map decode
  | true, strategy => strategy

theorem compiled_law (decode : Raw → Value) (encode : Value → Raw)
    (hsection : ∀ value, decode (encode value) = value)
    (profile : Profile (signature Value Action Value)) :
    play decode (fun who => compileStrategy encode who (profile who)) = play id profile := by
  simp [play, compileStrategy, FinDist.bind_map, hsection]

/-- A concrete two-player construction discharges both player-deviation laws.
The result permits all finite randomized raw submissions, not just well-formed
openings. Its utilities cannot distinguish raw failure reasons or costs. -/
def adequacy (decode : Raw → Value) (encode : Value → Raw)
    (hsection : ∀ value, decode (encode value) = value)
    (utility : Value × Action → Bool → ℝ) :
    DeviationAdequacy (game (Raw := Value) id utility) (game decode utility) where
  compileStrategy := compileStrategy encode
  backtranslateStrategy := backtranslateStrategy decode
  decodeOutcome := id
  utility_eq := rfl
  honest_law profile := by
    change (play decode (fun who => compileStrategy encode who (profile who))).map id = _
    rw [FinDist.map_id]
    exact compiled_law decode encode hsection profile
  compiled_considered _ _ := trivial
  deviation_law profile who replacement _ := by
    classical
    cases who <;>
      simp [game, play, Profile.update, compileStrategy, backtranslateStrategy,
        Function.update, FinDist.bind_map, hsection]

/-- info: 'Vegas.Runtime.FailureObservation.response_law_iff_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Runtime.FailureObservation.response_law_iff_factor

/-- info: 'Vegas.Runtime.FailureObservation.adequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Runtime.FailureObservation.adequacy

end Vegas.Runtime.FailureObservation
