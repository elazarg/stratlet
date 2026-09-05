/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Scheduled.Strategic

/-!
# Public sequential submissions

Two players each submit one irreversible Boolean value. The scheduler chooses
who submits first. The second player observes that value before choosing its
own. A player's policy supplies a distribution at each of its three possible
information states: no prior submission, prior `false`, and prior `true`.
The play kernel executes these two submissions in order. Utilities are matching
pennies payoffs on the final values, never payoffs on order or scheduling.

This is a different runtime from the atomic-frontier serializer: later
submissions can respond to earlier values in the same frontier. Neither
censorship nor nontermination is needed for its impossibility result. No
cryptographic commitment phase is present in this model.
-/

noncomputable section

namespace Vegas.Scheduled.PublicSubmission

open GameTheory GameTheory.Math.Probability

abbrev Player := Fin 2
abbrev Policy := Option Bool → FinDist Bool
abbrev Values := Player → Bool

def other (who : Player) : Player := if who = 0 then 1 else 0

theorem other_ne (who : Player) : other who ≠ who := by
  fin_cases who <;> decide

/-- The first and second public writes form the immutable terminal board. -/
def board (first : Player) (left right : Bool) : Values :=
  fun who => if who = first then left else right

abbrev signature : GameSignature (Participant Player) where
  Strategy
    | .scheduler => FinDist Player
    | .player _ => Policy
  Outcome := Values

/-- Each local distribution is sampled when the corresponding submission occurs. -/
def play (profile : Profile signature) : FinDist Values :=
  (profile .scheduler).bind fun first =>
    (profile (.player first) none).bind fun firstBit =>
      (profile (.player (other first)) (some firstBit)).map fun secondBit =>
        board first firstBit secondBit

def utility (values : Values) (who : Player) : ℝ :=
  if who = 0 then (if values 0 = values 1 then 1 else -1)
  else (if values 0 = values 1 then -1 else 1)

def game (schedulerUtility : Values → ℝ) : UtilityGame (Participant Player) where
  form := ⟨signature, play⟩
  utility values
    | .scheduler => schedulerUtility values
    | .player who => utility values who

/-- As second submitter, player zero copies and player one complements. The
first-submitter branch is legal but immaterial to the fixed-order theorem. -/
def winningPolicy (who : Player) : Policy
  | none => FinDist.pure false
  | some bit => FinDist.pure (if who = 0 then bit else !bit)

theorem winning_board (first : Player) (bit : Bool) :
    utility (board first bit (if other first = 0 then bit else !bit)) (other first) = 1 := by
  fin_cases first <;> cases bit <;> norm_num [utility, board, other]

/-- The later submitter can force payoff one against every earlier policy. -/
theorem winning_deviation (schedulerUtility : Values → ℝ)
    (profile : Profile signature) (first : Player)
    (horder : profile .scheduler = FinDist.pure first) :
    expectedUtility (game schedulerUtility).utility (.player (other first))
      ((game schedulerUtility).form.play
        (Profile.update profile (.player (other first)) (winningPolicy (other first)))) = 1 := by
  change (play (Profile.update profile (.player (other first))
    (winningPolicy (other first)))).expect (fun values => utility values (other first)) = 1
  simp [play, Profile.update, horder, Ne.symm (other_ne first), winningPolicy,
    FinDist.expect_bind, winning_board]

/-- A quantitative obstruction applying to *any* runtime profile. Preserving
a second player's source payoff within `error` requires at least `1 - error`
approximate-Nash slack when that source payoff is zero. -/
theorem approximation_lower_bound (schedulerUtility : Values → ℝ)
    (profile : Profile signature) (first : Player) (error ε : ℝ)
    (horder : profile .scheduler = FinDist.pure first)
    (hpayoff : expectedUtility (game schedulerUtility).utility (.player (other first))
      ((game schedulerUtility).form.play profile) ≤ error)
    (hequilibrium : ∀ who replacement,
      expectedUtility (game schedulerUtility).utility (.player who)
        ((game schedulerUtility).form.play (Profile.update profile (.player who) replacement)) ≤
      expectedUtility (game schedulerUtility).utility (.player who)
        ((game schedulerUtility).form.play profile) + ε) :
    1 ≤ error + ε := by
  have hdev := hequilibrium (other first) (winningPolicy (other first))
  rw [winning_deviation schedulerUtility profile first horder] at hdev
  linarith

/-- No profile retaining zero expected payoff for the later submitter is a
player Nash equilibrium. This quantifies over encodings, not just constant policies. -/
theorem not_nash_of_zero_payoff (schedulerUtility : Values → ℝ)
    (profile : Profile signature) (first : Player)
    (horder : profile .scheduler = FinDist.pure first)
    (hpayoff : expectedUtility (game schedulerUtility).utility (.player (other first))
      ((game schedulerUtility).form.play profile) = 0) :
    ¬ IsPlayerNash (game schedulerUtility) profile := by
  intro hnash
  have hdev := hnash (other first) (winningPolicy (other first)) trivial
  rw [winning_deviation schedulerUtility profile first horder, hpayoff] at hdev
  norm_num at hdev

/-- No exact unilateral-deviation adequacy certificate into this public-write
runtime exists for any source game with a zero-payoff Nash equilibrium. The
quantifier includes every strategy compiler and every outcome decoder. -/
theorem no_adequacy_of_zero_equilibrium (source : UtilityGame Player)
    (profile : Profile source.form.sig)
    (hnash : IsNash source.form (euPreference source.utility) profile)
    (hzero : ∀ who, expectedUtility source.utility who (source.form.play profile) = 0)
    (schedulerUtility : Values → ℝ) :
    ¬ Nonempty (PlayerDeviationAdequacy source (game schedulerUtility)) := by
  rintro ⟨adequacy⟩
  let compiled := adequacy.compileProfile (FinDist.pure 0) profile
  have htarget : IsPlayerNash (game schedulerUtility) compiled :=
    (adequacy.isPlayerNash_compileProfile_iff (FinDist.pure 0) profile).mpr hnash
  apply not_nash_of_zero_payoff schedulerUtility compiled 0 rfl _ htarget
  exact (adequacy.expectedUtility_compileProfile (FinDist.pure 0) profile (other 0)).trans
    (hzero _)

end Vegas.Scheduled.PublicSubmission
