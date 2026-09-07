/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.DeviationAdequacy
import Vegas.Scheduled.Basic

/-!
# Strategic adequacy with an adversarial scheduler

`Participant.scheduler` is a coordinate of the execution protocol, not a claim
that the scheduler belongs to the source game's equilibrium population. This
module states the strategic obligation at the right boundary: quantify over an
arbitrary scheduler strategy, but test unilateral deviations only for the
original players.

`PlayerDeviationAdequacyOn` is the scheduler-aware analogue of
`Runtime.DeviationAdequacyOn`. Its back-translation may depend on the fixed
scheduler strategy. This is essential when a target player can condition on a
public schedule signal: after fixing the signal, that contingent target plan is
one ordinary source strategy.

The generic signal constructions handle an independent public signal. Every
target player may choose a complete source strategy as a function of that
signal. If original-player utility ignores the signal, the lifted source Nash
profiles are exactly player-only Nash, for every independent signal law and
arbitrary scheduler utility. No restriction is placed on these signal-aware
deviations.

This averaging result does not itself execute a scheduler policy along game
histories. Applying it to a public-data-dependent scheduler requires a causal
construction of a source strategy for each fixed scheduler random seed. The
executed-policy replay in `Vegas.Scheduled.Replay` supplies this construction
for full order-blind runtime histories, preserving complete behavioral laws.
The atomic history simulation lives in `Vegas.Scheduled.History`. Compact
information sufficiency and complete terminal laws are proved in
`Vegas.Scheduled.Information` and `Vegas.Scheduled.Law`. The actual serializer's
behavioral Nash equivalence, including scheduler-only predrawing, is in
`Vegas.Scheduled.Equilibrium`; it does not rely on the auxiliary signal games.
-/

noncomputable section

namespace Vegas.Participant

/-! These declarations govern games whose player type is `Participant Player`.
The independent-signal constructions below are strategic instances of that
participant-indexed interface; the `Vegas.Scheduled` modules consume them when
reasoning about concrete schedulers. -/

open GameTheory
open GameTheory.Math.Probability

universe uPlayer uSourceStrategy uSourceOutcome uTargetStrategy uTargetOutcome

/-- Nash equilibrium against deviations by the original players only.

The scheduler coordinate remains fixed but arbitrary. `Considered` restricts
the actual players' target strategies exactly as in
`Runtime.DeviationAdequacyOn`; choosing `True` gives the adversarial tier. -/
def IsPlayerNashAgainst
    {Player : Type uPlayer} [DecidableEq Player]
    (target : UtilityGame.{uPlayer, uTargetStrategy, uTargetOutcome}
      (Participant Player))
    (Considered : (who : Player) →
      target.form.sig.Strategy (.player who) → Prop)
    (profile : Profile target.form.sig) : Prop :=
  ∀ who replacement, Considered who replacement →
    expectedUtility target.utility (.player who)
        (target.form.play
          (Profile.update profile (.player who) replacement)) ≤
      expectedUtility target.utility (.player who)
        (target.form.play profile)

/-- Player-only Nash against every technically available target strategy. -/
abbrev IsPlayerNash
    {Player : Type uPlayer} [DecidableEq Player]
    (target : UtilityGame.{uPlayer, uTargetStrategy, uTargetOutcome}
      (Participant Player))
    (profile : Profile target.form.sig) : Prop :=
  IsPlayerNashAgainst target (fun _ _ => True) profile

/-- Strategic adequacy for the original players, uniformly over an adversarial
scheduler.

The target may assign the scheduler any strategy space and any utility. Those
are deliberately absent from the obligations: the scheduler is part of the
implementation environment, not one of the agents whose equilibrium the source
analysis claims to preserve.

The back-translation receives the scheduler strategy. Consequently a target
deviation that conditions on an independent public schedule signal need not be
uniformly representable by one source strategy across all signals; it only has
to become a source strategy after the adversarial signal is fixed. -/
structure PlayerDeviationAdequacyOn
    {Player : Type uPlayer} [DecidableEq Player]
    (source : UtilityGame.{uPlayer, uSourceStrategy, uSourceOutcome} Player)
    (target : UtilityGame.{uPlayer, uTargetStrategy, uTargetOutcome}
      (Participant Player))
    (Considered : (who : Player) →
      target.form.sig.Strategy (.player who) → Prop) where
  compileStrategy :
    (who : Player) → source.form.sig.Strategy who →
      target.form.sig.Strategy (.player who)
  backtranslateStrategy :
    target.form.sig.Strategy (.scheduler : Participant Player) →
      (who : Player) → target.form.sig.Strategy (.player who) →
        source.form.sig.Strategy who
  decodeOutcome : target.form.sig.Outcome → source.form.sig.Outcome
  player_utility_eq :
    ∀ outcome who,
      target.utility outcome (.player who) =
        source.utility (decodeOutcome outcome) who
  honest_law :
    ∀ scheduler profile,
      (target.form.play
        (fun participant =>
          match participant with
          | .scheduler => scheduler
          | .player who => compileStrategy who (profile who))).map
            decodeOutcome =
        source.form.play profile
  compiled_considered :
    ∀ who strategy, Considered who (compileStrategy who strategy)
  deviation_law :
    ∀ scheduler profile who replacement, Considered who replacement →
      (target.form.play
        (Profile.update
          (fun participant =>
            match participant with
            | .scheduler => scheduler
            | .player actor => compileStrategy actor (profile actor))
          (.player who) replacement)).map decodeOutcome =
        source.form.play
          (Profile.update profile who
            (backtranslateStrategy scheduler who replacement))

/-- Adequacy against every strategy available to an original player. -/
abbrev PlayerDeviationAdequacy
    {Player : Type uPlayer} [DecidableEq Player]
    (source : UtilityGame.{uPlayer, uSourceStrategy, uSourceOutcome} Player)
    (target : UtilityGame.{uPlayer, uTargetStrategy, uTargetOutcome}
      (Participant Player)) :=
  PlayerDeviationAdequacyOn source target (fun _ _ => True)

namespace PlayerDeviationAdequacyOn

variable {Player : Type uPlayer} [DecidableEq Player]
variable {source : UtilityGame.{uPlayer, uSourceStrategy, uSourceOutcome} Player}
variable {target : UtilityGame.{uPlayer, uTargetStrategy, uTargetOutcome}
  (Participant Player)}
variable {Considered : (who : Player) →
  target.form.sig.Strategy (.player who) → Prop}
variable (adequacy : PlayerDeviationAdequacyOn source target Considered)

/-- Compile the real players and install an arbitrary scheduler strategy. -/
def compileProfile
    (scheduler : target.form.sig.Strategy
      (.scheduler : Participant Player))
    (profile : Profile source.form.sig) : Profile target.form.sig
  | .scheduler => scheduler
  | .player who => adequacy.compileStrategy who (profile who)

@[simp] theorem compileProfile_scheduler
    (scheduler : target.form.sig.Strategy
      (.scheduler : Participant Player))
    (profile : Profile source.form.sig) :
    adequacy.compileProfile scheduler profile .scheduler = scheduler :=
  rfl

@[simp] theorem compileProfile_player
    (scheduler : target.form.sig.Strategy
      (.scheduler : Participant Player))
    (profile : Profile source.form.sig) (who : Player) :
    adequacy.compileProfile scheduler profile (.player who) =
      adequacy.compileStrategy who (profile who) :=
  rfl

theorem compileProfile_update
    (scheduler : target.form.sig.Strategy
      (.scheduler : Participant Player))
    (profile : Profile source.form.sig) (who : Player)
    (replacement : source.form.sig.Strategy who) :
    Profile.update (adequacy.compileProfile scheduler profile) (.player who)
        (adequacy.compileStrategy who replacement) =
      adequacy.compileProfile scheduler
        (Profile.update profile who replacement) := by
  funext participant
  cases participant with
  | scheduler => simp [compileProfile]
  | player player =>
      by_cases hplayer : player = who
      · subst player
        simp [compileProfile]
      · simp [compileProfile, hplayer]

/-- Honest compiled play has the source expected utility for every real player,
regardless of the scheduler strategy or its utility. -/
theorem expectedUtility_compileProfile
    (scheduler : target.form.sig.Strategy
      (.scheduler : Participant Player))
    (profile : Profile source.form.sig) (who : Player) :
    expectedUtility target.utility (.player who)
        (target.form.play (adequacy.compileProfile scheduler profile)) =
      expectedUtility source.utility who (source.form.play profile) := by
  calc
    expectedUtility target.utility (.player who)
        (target.form.play (adequacy.compileProfile scheduler profile)) =
      (target.form.play (adequacy.compileProfile scheduler profile)).expect
        (fun outcome => source.utility (adequacy.decodeOutcome outcome) who) := by
          unfold expectedUtility
          apply FinDist.expect_congr
          intro outcome _
          exact adequacy.player_utility_eq outcome who
    _ = expectedUtility source.utility who
        ((target.form.play
          (adequacy.compileProfile scheduler profile)).map
            adequacy.decodeOutcome) := by
          exact (expectedUtility_map source.utility who adequacy.decodeOutcome
            (target.form.play
              (adequacy.compileProfile scheduler profile))).symm
    _ = expectedUtility source.utility who (source.form.play profile) := by
          change expectedUtility source.utility who
              ((target.form.play
                (fun participant =>
                  match participant with
                  | .scheduler => scheduler
                  | .player actor =>
                      adequacy.compileStrategy actor (profile actor))).map
                adequacy.decodeOutcome) =
            expectedUtility source.utility who (source.form.play profile)
          rw [adequacy.honest_law]

/-- Every adversarial target deviation by a real player has exactly the source
utility of its scheduler-indexed back-translation. -/
theorem expectedUtility_deviation
    (scheduler : target.form.sig.Strategy
      (.scheduler : Participant Player))
    (profile : Profile source.form.sig) (who : Player)
    (replacement : target.form.sig.Strategy (.player who))
    (hconsidered : Considered who replacement) :
    expectedUtility target.utility (.player who)
        (target.form.play
          (Profile.update (adequacy.compileProfile scheduler profile)
            (.player who) replacement)) =
      expectedUtility source.utility who
        (source.form.play
          (Profile.update profile who
            (adequacy.backtranslateStrategy scheduler who replacement))) := by
  calc
    expectedUtility target.utility (.player who)
        (target.form.play
          (Profile.update (adequacy.compileProfile scheduler profile)
            (.player who) replacement)) =
      (target.form.play
        (Profile.update (adequacy.compileProfile scheduler profile)
          (.player who) replacement)).expect
        (fun outcome => source.utility (adequacy.decodeOutcome outcome) who) := by
          unfold expectedUtility
          apply FinDist.expect_congr
          intro outcome _
          exact adequacy.player_utility_eq outcome who
    _ = expectedUtility source.utility who
        ((target.form.play
          (Profile.update (adequacy.compileProfile scheduler profile)
            (.player who) replacement)).map adequacy.decodeOutcome) := by
          exact (expectedUtility_map source.utility who adequacy.decodeOutcome
            (target.form.play
              (Profile.update (adequacy.compileProfile scheduler profile)
                (.player who) replacement))).symm
    _ = expectedUtility source.utility who
        (source.form.play
          (Profile.update profile who
            (adequacy.backtranslateStrategy scheduler who replacement))) := by
          change expectedUtility source.utility who
              ((target.form.play
                (Profile.update
                  (fun participant =>
                    match participant with
                    | .scheduler => scheduler
                    | .player actor =>
                        adequacy.compileStrategy actor (profile actor))
                  (.player who) replacement)).map adequacy.decodeOutcome) =
            expectedUtility source.utility who
              (source.form.play
                (Profile.update profile who
                  (adequacy.backtranslateStrategy scheduler who replacement)))
          rw [adequacy.deviation_law scheduler profile who replacement hconsidered]

/-- **Player Nash equivalence under an arbitrary scheduler.**

For every fixed scheduler strategy, a compiled profile withstands exactly the
considered deviations of the original players iff the source profile is Nash.
No condition is imposed on scheduler utility or scheduler optimality. -/
theorem isPlayerNashAgainst_compileProfile_iff
    (scheduler : target.form.sig.Strategy
      (.scheduler : Participant Player))
    (profile : Profile source.form.sig) :
    IsPlayerNashAgainst target Considered
        (adequacy.compileProfile scheduler profile) ↔
      IsNash source.form (euPreference source.utility) profile := by
  rw [GameTheory.isNash_iff]
  constructor
  · intro h who replacement
    have htarget := h who (adequacy.compileStrategy who replacement)
      (adequacy.compiled_considered who replacement)
    rw [euPreference_apply]
    rw [adequacy.compileProfile_update] at htarget
    rw [adequacy.expectedUtility_compileProfile,
      adequacy.expectedUtility_compileProfile] at htarget
    exact htarget
  · intro h who replacement hconsidered
    have hsource := h who
      (adequacy.backtranslateStrategy scheduler who replacement)
    rw [euPreference_apply] at hsource
    rw [adequacy.expectedUtility_deviation scheduler profile who replacement
      hconsidered, adequacy.expectedUtility_compileProfile]
    exact hsource

/-- Unrestricted player-only Nash equivalence, uniform in the scheduler. -/
theorem isPlayerNash_compileProfile_iff
    (adequacy : PlayerDeviationAdequacy source target)
    (scheduler : target.form.sig.Strategy
      (.scheduler : Participant Player))
    (profile : Profile source.form.sig) :
    IsPlayerNash target (adequacy.compileProfile scheduler profile) ↔
      IsNash source.form (euPreference source.utility) profile :=
  adequacy.isPlayerNashAgainst_compileProfile_iff scheduler profile

end PlayerDeviationAdequacyOn

/-! ## Independent public signals -/

namespace IndependentSignal

variable {Player : Type uPlayer} [DecidableEq Player]
variable (source : UtilityGame.{uPlayer, uSourceStrategy, uSourceOutcome} Player)
variable (Signal : Type uSourceStrategy)

/-- Add an independently selected public signal. Real players may choose a
complete source strategy separately for every signal value. -/
abbrev signature :
    GameSignature.{uPlayer, uSourceStrategy,
      max uSourceStrategy uSourceOutcome} (Participant Player) where
  Strategy
    | .scheduler => Signal
    | .player who => Signal → source.form.sig.Strategy who
  Outcome := Signal × source.form.sig.Outcome

/-- The source profile selected after the public signal is fixed. -/
def realizedProfile
    (profile : Profile (signature source Signal)) :
    Profile source.form.sig :=
  fun who => profile (.player who) (profile .scheduler)

/-- Install a source profile together with a fixed public signal. -/
def compiledProfile (signal : Signal) (profile : Profile source.form.sig) :
    Profile (signature source Signal)
  | .scheduler => signal
  | .player who => fun _ => profile who

omit [DecidableEq Player] in
@[simp] theorem compiledProfile_scheduler
    (signal : Signal) (profile : Profile source.form.sig) :
    compiledProfile source Signal signal profile .scheduler = signal :=
  rfl

omit [DecidableEq Player] in
@[simp] theorem compiledProfile_player
    (signal : Signal) (profile : Profile source.form.sig) (who : Player) :
    compiledProfile source Signal signal profile (.player who) =
      fun _ => profile who :=
  rfl

omit [DecidableEq Player] in
@[simp] theorem realizedProfile_compiledProfile
    (signal : Signal) (profile : Profile source.form.sig) :
    realizedProfile source Signal
        (compiledProfile source Signal signal profile) = profile := by
  funext who
  rfl

@[simp] theorem compiledProfile_update_scheduler
    (signal : Signal) (profile : Profile source.form.sig) (who : Player)
    (replacement : (signature source Signal).Strategy (.player who)) :
    Profile.update (compiledProfile source Signal signal profile)
        (.player who) replacement .scheduler = signal := by
  rw [Profile.update_of_ne _ _ (by simp)]
  rfl

theorem realizedProfile_update_compiledProfile
    (signal : Signal) (profile : Profile source.form.sig) (who : Player)
    (replacement : (signature source Signal).Strategy (.player who)) :
    realizedProfile source Signal
        (Profile.update (compiledProfile source Signal signal profile)
          (.player who) replacement) =
      Profile.update profile who (replacement signal) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp [realizedProfile]
  · simp [realizedProfile, hplayer]

/-- Play the source game at the signal-indexed player profile and retain the
signal in the target outcome. The source play law never influences the signal. -/
abbrev form : GameForm (Participant Player) where
  sig := signature source Signal
  play profile :=
    (source.form.play (realizedProfile source Signal profile)).map
      (fun outcome => (profile .scheduler, outcome))

/-- Utility for the lifted game. The scheduler's utility is completely
arbitrary; each real player's utility factors only through the source outcome. -/
def utility
    (schedulerUtility : Signal × source.form.sig.Outcome → ℝ) :
    (Signal × source.form.sig.Outcome) → Participant Player → ℝ
  | outcome, .scheduler => schedulerUtility outcome
  | (_, outcome), .player who => source.utility outcome who

/-- The utility game obtained by adjoining an independent public signal. -/
abbrev game
    (schedulerUtility : Signal × source.form.sig.Outcome → ℝ) :
    UtilityGame (Participant Player) where
  form := form source Signal
  utility := utility source Signal schedulerUtility

/-- Compiled source strategies ignore the implementation signal. -/
def compileStrategy
    (schedulerUtility : Signal × source.form.sig.Outcome → ℝ)
    (who : Player) (strategy : source.form.sig.Strategy who) :
    (game source Signal schedulerUtility).form.sig.Strategy (.player who) :=
  fun _ => strategy

/-- Once the adversarial signal is fixed, a signal-contingent target strategy
is one ordinary source strategy. -/
def backtranslateStrategy
    (schedulerUtility : Signal × source.form.sig.Outcome → ℝ)
    (signal : (game source Signal schedulerUtility).form.sig.Strategy
      (.scheduler : Participant Player))
    (who : Player)
    (strategy : (game source Signal schedulerUtility).form.sig.Strategy
      (.player who)) : source.form.sig.Strategy who :=
  strategy signal

/-- The independent-signal lift is adequate against every target strategy of
every real player, for every scheduler choice. -/
def playerDeviationAdequacy
    (schedulerUtility : Signal × source.form.sig.Outcome → ℝ) :
    PlayerDeviationAdequacy source (game source Signal schedulerUtility) where
  compileStrategy := compileStrategy source Signal schedulerUtility
  backtranslateStrategy := backtranslateStrategy source Signal schedulerUtility
  decodeOutcome := Prod.snd
  player_utility_eq := by
    intro outcome who
    rfl
  honest_law := by
    intro signal profile
    change Signal at signal
    change ((source.form.play
      (realizedProfile source Signal
        (compiledProfile source Signal signal profile))).map
          (fun outcome => (signal, outcome))).map Prod.snd =
      source.form.play profile
    rw [realizedProfile_compiledProfile, FinDist.map_comp]
    change (source.form.play profile).map id = source.form.play profile
    exact FinDist.map_id (source.form.play profile)
  compiled_considered := by
    intro _ _
    trivial
  deviation_law := by
    intro signal profile who replacement _
    change Signal at signal
    change (Signal → source.form.sig.Strategy who) at replacement
    change ((source.form.play
      (realizedProfile source Signal
        (Profile.update (compiledProfile source Signal signal profile)
          (.player who) replacement))).map
            (fun outcome => (signal, outcome))).map Prod.snd =
      source.form.play (Profile.update profile who (replacement signal))
    rw [FinDist.map_comp]
    have hforget :
        (Prod.snd ∘ fun outcome : source.form.sig.Outcome =>
          (signal, outcome)) = id := by
      funext outcome
      rfl
    rw [hforget, FinDist.map_id]
    change source.form.play
        (realizedProfile source Signal
          (Profile.update (compiledProfile source Signal signal profile)
            (.player who) replacement)) =
      source.form.play (Profile.update profile who (replacement signal))
    congr 1
    funext player
    unfold realizedProfile
    by_cases hplayer : player = who
    · subst player
      rw [Profile.update_same, Profile.update_same]
      rw [Profile.update_of_ne _ _ (by simp)]
      rw [compiledProfile_scheduler]
    · have hparticipant :
          Participant.player player ≠ Participant.player who :=
        fun heq => hplayer (Participant.player.inj heq)
      rw [Profile.update_of_ne _ _ hparticipant]
      rw [Profile.update_of_ne _ _ hplayer]
      rfl

/-- **An adversarial independent public signal does not alter Nash equilibrium
among the original players.**

The target strategy space is strictly richer: every real player may condition
on the scheduler's signal. Nevertheless, for every scheduler choice and even
for arbitrary scheduler utility, player-only Nash in the lifted implementation
is equivalent to source Nash. -/
theorem isPlayerNash_iff
    (schedulerUtility : Signal × source.form.sig.Outcome → ℝ)
    (signal : Signal) (profile : Profile source.form.sig) :
    IsPlayerNash (game source Signal schedulerUtility)
        ((playerDeviationAdequacy source Signal schedulerUtility).compileProfile
          signal profile) ↔
      IsNash source.form (euPreference source.utility) profile :=
  PlayerDeviationAdequacyOn.isPlayerNash_compileProfile_iff
    (playerDeviationAdequacy source Signal schedulerUtility) signal profile

/-- Forward preservation stated with the adversarial quantifier exposed: one
source Nash profile yields player-only Nash for every scheduler signal. -/
theorem sourceNash_implies_playerNash_forall
    (schedulerUtility : Signal × source.form.sig.Outcome → ℝ)
    (profile : Profile source.form.sig)
    (hnash : IsNash source.form (euPreference source.utility) profile) :
    ∀ signal : Signal,
      IsPlayerNash (game source Signal schedulerUtility)
        ((playerDeviationAdequacy source Signal schedulerUtility).compileProfile
          signal profile) := by
  intro signal
  exact (isPlayerNash_iff source Signal schedulerUtility signal profile).2 hnash

end IndependentSignal

/-! ## Random independent public signals

The exact-law adequacy interface above deliberately back-translates one fixed
signal. A randomized environment need not have one source strategy with the
same complete outcome law as a signal-contingent target strategy. Nash
preservation nevertheless holds: a random signal averages the payoffs of
ordinary source deviations, and no average of non-profitable deviations is
profitable. This is the result needed when the scheduler itself randomizes. -/

namespace RandomIndependentSignal

variable {Player : Type uPlayer}
variable (source : UtilityGame.{uPlayer, uSourceStrategy, uSourceOutcome} Player)
variable (Signal : Type uSourceStrategy)

/-- The scheduler supplies a finite probability law over independent signals;
each original player may choose a complete source strategy for every realized
signal. -/
abbrev signature :
    GameSignature.{uPlayer, uSourceStrategy,
      max uSourceStrategy uSourceOutcome} (Participant Player) where
  Strategy
    | .scheduler => FinDist Signal
    | .player who => Signal → source.form.sig.Strategy who
  Outcome := Signal × source.form.sig.Outcome

def realizedProfile
    (profile : Profile (signature source Signal)) (signal : Signal) :
    Profile source.form.sig :=
  fun who => profile (.player who) signal

/-- Play samples the environment signal first and then runs the source game at
the signal-contingent player profile. The source outcome cannot influence the
already sampled signal. -/
abbrev form : GameForm (Participant Player) where
  sig := signature source Signal
  play profile :=
    (profile .scheduler).bind fun signal =>
      (source.form.play (realizedProfile source Signal profile signal)).map
        (fun outcome => (signal, outcome))

def utility
    (schedulerUtility : Signal × source.form.sig.Outcome → ℝ) :
    (Signal × source.form.sig.Outcome) → Participant Player → ℝ
  | outcome, .scheduler => schedulerUtility outcome
  | (_, outcome), .player who => source.utility outcome who

abbrev game
    (schedulerUtility : Signal × source.form.sig.Outcome → ℝ) :
    UtilityGame (Participant Player) where
  form := form source Signal
  utility := utility source Signal schedulerUtility

/-- Install a source profile whose players ignore the sampled signal. -/
def compiledProfile (signalLaw : FinDist Signal)
    (profile : Profile source.form.sig) :
    Profile (signature source Signal)
  | .scheduler => signalLaw
  | .player who => fun _ => profile who

@[simp] theorem compiledProfile_scheduler (signalLaw : FinDist Signal)
    (profile : Profile source.form.sig) :
    compiledProfile source Signal signalLaw profile .scheduler = signalLaw :=
  rfl

@[simp] theorem realizedProfile_compiledProfile (signalLaw : FinDist Signal)
    (profile : Profile source.form.sig) (signal : Signal) :
    realizedProfile source Signal
        (compiledProfile source Signal signalLaw profile) signal = profile := by
  funext who
  rfl

theorem realizedProfile_update_compiledProfile
    [DecidableEq Player]
    (signalLaw : FinDist Signal) (profile : Profile source.form.sig)
    (who : Player)
    (replacement : Signal → source.form.sig.Strategy who)
    (signal : Signal) :
    realizedProfile source Signal
        (Profile.update (compiledProfile source Signal signalLaw profile)
          (.player who) replacement) signal =
      Profile.update profile who (replacement signal) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp [realizedProfile]
  · have hparticipant :
        Participant.player player ≠ Participant.player who :=
      fun heq => hplayer (Participant.player.inj heq)
    unfold realizedProfile
    rw [Profile.update_of_ne _ _ hparticipant,
      Profile.update_of_ne _ _ hplayer]
    rfl

/-- A real player's target expected utility is the scheduler-law average of
the corresponding signal-contingent source expected utilities. -/
theorem expectedUtility_player
    (schedulerUtility : Signal × source.form.sig.Outcome → ℝ)
    (profile : Profile (signature source Signal)) (who : Player) :
    expectedUtility (utility source Signal schedulerUtility) (.player who)
        ((form source Signal).play profile) =
      (profile .scheduler).expect fun signal =>
        expectedUtility source.utility who
          (source.form.play
            (realizedProfile source Signal profile signal)) := by
  unfold expectedUtility
  rw [FinDist.expect_bind]
  apply FinDist.expect_congr
  intro signal _hsignal
  rw [FinDist.expect_map]
  rfl

/-- Compiled play gives every original player exactly its source expected
utility for every independent signal law. -/
theorem expectedUtility_compiledProfile
    (schedulerUtility : Signal × source.form.sig.Outcome → ℝ)
    (signalLaw : FinDist Signal) (profile : Profile source.form.sig)
    (who : Player) :
    expectedUtility (utility source Signal schedulerUtility) (.player who)
        ((form source Signal).play
          (compiledProfile source Signal signalLaw profile)) =
      expectedUtility source.utility who (source.form.play profile) := by
  rw [expectedUtility_player]
  apply Eq.trans (FinDist.expect_congr fun signal _ => ?_)
    (FinDist.expect_const signalLaw _)
  rw [realizedProfile_compiledProfile]

/-- **Random independent public signals preserve and reflect Nash among the
original players.** Target deviations may be arbitrary signal-contingent
functions, and the scheduler law and scheduler utility are arbitrary. No
source strategy has to reproduce the target's signal/outcome joint law. -/
theorem isPlayerNash_iff
    [DecidableEq Player]
    (schedulerUtility : Signal × source.form.sig.Outcome → ℝ)
    (signalLaw : FinDist Signal) (profile : Profile source.form.sig) :
    IsPlayerNash (game source Signal schedulerUtility)
        (compiledProfile source Signal signalLaw profile) ↔
      IsNash source.form (euPreference source.utility) profile := by
  rw [GameTheory.isNash_iff]
  constructor
  · intro htarget who replacement
    let targetReplacement : Signal → source.form.sig.Strategy who :=
      fun _ => replacement
    have h := htarget who targetReplacement trivial
    rw [euPreference_apply]
    rw [expectedUtility_player source Signal schedulerUtility] at h
    rw [expectedUtility_compiledProfile source Signal schedulerUtility] at h
    have hupdated :
        (Profile.update (compiledProfile source Signal signalLaw profile)
          (.player who) targetReplacement) .scheduler = signalLaw := by
      rw [Profile.update_of_ne _ _ (by simp)]
      rfl
    rw [hupdated] at h
    have hintegrand : (
        fun signal => expectedUtility source.utility who
          (source.form.play
            (realizedProfile source Signal
              (Profile.update
                (compiledProfile source Signal signalLaw profile)
                (.player who) targetReplacement) signal))) =
        fun _ => expectedUtility source.utility who
          (source.form.play (Profile.update profile who replacement)) := by
      funext signal
      rw [realizedProfile_update_compiledProfile]
    rw [hintegrand, FinDist.expect_const] at h
    exact h
  · intro hsource who replacement _
    rw [expectedUtility_player source Signal schedulerUtility]
    rw [expectedUtility_compiledProfile source Signal schedulerUtility]
    have hscheduler :
        (Profile.update (compiledProfile source Signal signalLaw profile)
          (.player who) replacement) .scheduler = signalLaw := by
      rw [Profile.update_of_ne _ _ (by simp)]
      rfl
    rw [hscheduler]
    apply FinDist.expect_le_of_forall
    intro signal _hsignal
    rw [realizedProfile_update_compiledProfile]
    have hdeviation := hsource who (replacement signal)
    rwa [euPreference_apply] at hdeviation

end RandomIndependentSignal

end Vegas.Participant
