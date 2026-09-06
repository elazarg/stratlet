/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Core.Utility

/-!
# Unilateral-deviation adequacy

Exact honest-run outcome equality is not enough when compilation introduces new
strategies.  `DeviationAdequacy` adds the narrow back-translation obligation
needed for Nash preservation: every unilateral target replacement at a
compiled profile must have a source replacement with the same decoded outcome
law.

This is one deliberately small strategic certificate, not a claim to solve
secure compilation in general.  It does not cover coalitions, target context
composition, scheduler hyperproperties, timing, or liveness.  A lowering pass
that introduces one of those surfaces needs a stronger pass-specific theorem.

## What is and is not new here

Relating deviation simulation to equilibrium preservation is not new, and the
claim to make is narrower than that.

Halpern and Pass already relate mediator implementation, deviating machines,
distribution preservation, and equilibrium preservation in a single
game-theoretic framework with costly computation (ICS 2010).  BitML carries a
symbolic strategic model through a computational-soundness argument for
compilation to Bitcoin (Bartoletti and Zunino, CCS 2018), and that compilation
has since been machine-checked in Agda, together with transfer of properties
proved at the contract level down to transactions (Melkonian, Edinburgh, 2024).
That last is the closest existing artifact to what this development attempts and
is the right benchmark for any scope claim made about it.

The two-tier reading here also has a direct analogue.  A *pseudo-Nash*
equilibrium tolerates a deviation whose utility is indistinguishable from the
equilibrium's, and transfers equilibria from ideal cryptography to real
protocols on that basis (arXiv:2506.22089).  That is the same move as the
permissive tier in `Vegas.Scheduled.Basic`, where an order-aware deviation is
available and cannot pay.

What is specific to this definition is that it is exact rather than asymptotic,
finite rather than computational, and mechanized as an interface a compiler pass
must discharge: `Considered` makes the deviation class a parameter, and
`compiled_considered` stops the obligation from being satisfiable by a class too
small to contain the compiled strategies.
-/

noncomputable section

namespace Vegas.Runtime

open GameTheory
open GameTheory.Math.Probability

universe uPlayer uSourceStrategy uSourceOutcome uTargetStrategy uTargetOutcome

/-- A target game is adequate for the unilateral deviations in `Considered`,
at compiled profiles.

`Considered` is the class of target strategies a player is taken to be able to
play.  It is a genuine parameter, and the development uses both extremes:

* `fun _ _ => True` — every technically available target strategy, including
  ones that read target-only information the source never exposed.  This is the
  secure-compilation obligation, and it is what `DeviationAdequacy` abbreviates.
* An *honest* class — strategies that read only what the source made visible,
  so a player who ignores runtime implementation detail stays inside it.  A
  weaker obligation, but one a realistic runtime can actually discharge.

Both tiers are the same theorem at two instantiations, so a result proved for
the honest tier cannot be mistaken for the robust one: the class it quantifies
over is written into its statement.

`compiled_considered` is what keeps the weaker tier from going vacuous.  It
forces `Considered` to contain at least every compiled source strategy, so the
class can restrict what a player *sees*, never what the source itself can
express. -/
structure DeviationAdequacyOn
    {Player : Type uPlayer} [DecidableEq Player]
    (source : UtilityGame.{uPlayer, uSourceStrategy, uSourceOutcome} Player)
    (target : UtilityGame.{uPlayer, uTargetStrategy, uTargetOutcome} Player)
    (Considered : (who : Player) → target.form.sig.Strategy who → Prop) where
  compileStrategy :
    (who : Player) → source.form.sig.Strategy who →
      target.form.sig.Strategy who
  backtranslateStrategy :
    (who : Player) → target.form.sig.Strategy who →
      source.form.sig.Strategy who
  decodeOutcome : target.form.sig.Outcome → source.form.sig.Outcome
  utility_eq :
    target.utility =
      fun outcome who => source.utility (decodeOutcome outcome) who
  honest_law :
    ∀ profile,
      (target.form.play
        (fun who => compileStrategy who (profile who))).map decodeOutcome =
          source.form.play profile
  /-- Every compiled source strategy is itself considered.  Without this the
  restricted tier could be satisfied by an empty class. -/
  compiled_considered :
    ∀ who strategy, Considered who (compileStrategy who strategy)
  deviation_law :
    ∀ profile who replacement, Considered who replacement →
      (target.form.play
        (Profile.update
          (fun player => compileStrategy player (profile player))
          who replacement)).map decodeOutcome =
        source.form.play
          (Profile.update profile who
            (backtranslateStrategy who replacement))

/-- Adequacy against *every* technically available target strategy: the
secure-compilation obligation, with no restriction on what a deviating player
may read. -/
abbrev DeviationAdequacy
    {Player : Type uPlayer} [DecidableEq Player]
    (source : UtilityGame.{uPlayer, uSourceStrategy, uSourceOutcome} Player)
    (target : UtilityGame.{uPlayer, uTargetStrategy, uTargetOutcome} Player) :=
  DeviationAdequacyOn source target (fun _ _ => True)

/-- `profile` is a Nash equilibrium *against the deviations in `Considered`*:
no considered unilateral replacement improves a player's expected utility.

The class is part of the statement, so a result about a restricted class can
never be read as a result about all strategies. -/
def IsNashAgainst {Player : Type uPlayer} [DecidableEq Player]
    (game : UtilityGame.{uPlayer, uTargetStrategy, uTargetOutcome} Player)
    (Considered : (who : Player) → game.form.sig.Strategy who → Prop)
    (profile : Profile game.form.sig) : Prop :=
  ∀ who replacement, Considered who replacement →
    expectedUtility game.utility who
        (game.form.play (Profile.update profile who replacement)) ≤
      expectedUtility game.utility who (game.form.play profile)

/-- Against the unrestricted class, `IsNashAgainst` is ordinary Nash. -/
theorem isNashAgainst_true_iff {Player : Type uPlayer} [DecidableEq Player]
    (game : UtilityGame.{uPlayer, uTargetStrategy, uTargetOutcome} Player)
    (profile : Profile game.form.sig) :
    IsNashAgainst game (fun _ _ => True) profile ↔
      IsNash game.form (euPreference game.utility) profile := by
  rw [GameTheory.isNash_iff]
  constructor
  · intro h who replacement
    rw [euPreference_apply]
    exact h who replacement trivial
  · intro h who replacement _
    have := h who replacement
    rw [euPreference_apply] at this
    exact this

namespace DeviationAdequacyOn

variable {Player : Type uPlayer}
variable [DecidableEq Player]
variable {source : UtilityGame.{uPlayer, uSourceStrategy, uSourceOutcome} Player}
variable {target : UtilityGame.{uPlayer, uTargetStrategy, uTargetOutcome} Player}
variable {Considered : (who : Player) → target.form.sig.Strategy who → Prop}
variable (adequacy : DeviationAdequacyOn source target Considered)

/-- Compile every coordinate of a source profile. -/
def compileProfile (profile : Profile source.form.sig) :
    Profile target.form.sig :=
  fun who => adequacy.compileStrategy who (profile who)

@[simp] theorem compileProfile_apply
    (profile : Profile source.form.sig) (who : Player) :
    adequacy.compileProfile profile who =
      adequacy.compileStrategy who (profile who) :=
  rfl

theorem compileProfile_update
    (profile : Profile source.form.sig) (who : Player)
    (replacement : source.form.sig.Strategy who) :
    Profile.update (adequacy.compileProfile profile) who
        (adequacy.compileStrategy who replacement) =
      adequacy.compileProfile (Profile.update profile who replacement) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp
  · simp [Profile.update_of_ne, hplayer]

/-- Honest compiled profiles have exactly the source expected utility. -/
theorem expectedUtility_compileProfile
    (profile : Profile source.form.sig) (who : Player) :
    expectedUtility target.utility who
        (target.form.play (adequacy.compileProfile profile)) =
      expectedUtility source.utility who (source.form.play profile) := by
  calc
    expectedUtility target.utility who
        (target.form.play (adequacy.compileProfile profile)) =
      expectedUtility
        (fun outcome who => source.utility (adequacy.decodeOutcome outcome) who)
        who (target.form.play (adequacy.compileProfile profile)) := by
          rw [adequacy.utility_eq]
    _ = expectedUtility source.utility who
        ((target.form.play (adequacy.compileProfile profile)).map
          adequacy.decodeOutcome) := by
          rw [expectedUtility_map]
    _ = expectedUtility source.utility who (source.form.play profile) := by
          change
            expectedUtility source.utility who
                ((target.form.play
                  (fun player => adequacy.compileStrategy player (profile player))).map
                    adequacy.decodeOutcome) =
              expectedUtility source.utility who (source.form.play profile)
          rw [adequacy.honest_law]

/-- Every unilateral target deviation at a compiled profile has the expected
utility of its source back-translation. -/
theorem expectedUtility_deviation
    (profile : Profile source.form.sig) (who : Player)
    (replacement : target.form.sig.Strategy who)
    (hconsidered : Considered who replacement) :
    expectedUtility target.utility who
        (target.form.play
          (Profile.update (adequacy.compileProfile profile) who replacement)) =
      expectedUtility source.utility who
        (source.form.play
          (Profile.update profile who
            (adequacy.backtranslateStrategy who replacement))) := by
  calc
    expectedUtility target.utility who
        (target.form.play
          (Profile.update (adequacy.compileProfile profile) who replacement)) =
      expectedUtility
        (fun outcome who => source.utility (adequacy.decodeOutcome outcome) who)
        who
        (target.form.play
          (Profile.update (adequacy.compileProfile profile) who replacement)) := by
            rw [adequacy.utility_eq]
    _ = expectedUtility source.utility who
        ((target.form.play
          (Profile.update (adequacy.compileProfile profile) who replacement)).map
            adequacy.decodeOutcome) := by
            rw [expectedUtility_map]
    _ = expectedUtility source.utility who
        (source.form.play
          (Profile.update profile who
            (adequacy.backtranslateStrategy who replacement))) := by
            change
              expectedUtility source.utility who
                  ((target.form.play
                    (Profile.update
                      (fun player => adequacy.compileStrategy player (profile player))
                      who replacement)).map adequacy.decodeOutcome) =
                expectedUtility source.utility who
                  (source.form.play
                    (Profile.update profile who
                      (adequacy.backtranslateStrategy who replacement)))
            rw [adequacy.deviation_law _ _ _ hconsidered]

/-- **Nash equivalence, relative to a deviation class.**

A compiled profile withstands every *considered* target deviation exactly when
the source profile withstands every source deviation.

Reflection (left to right) is where `compiled_considered` earns its place: it
supplies a considered target witness for an arbitrary source deviation. -/
theorem isNashAgainst_compileProfile_iff
    (profile : Profile source.form.sig) :
    IsNashAgainst target Considered (adequacy.compileProfile profile) ↔
      IsNash source.form (euPreference source.utility) profile := by
  rw [GameTheory.isNash_iff]
  constructor
  · intro h who replacement
    have htarget :=
      h who (adequacy.compileStrategy who replacement)
        (adequacy.compiled_considered who replacement)
    rw [euPreference_apply]
    rw [adequacy.compileProfile_update] at htarget
    rw [adequacy.expectedUtility_compileProfile,
      adequacy.expectedUtility_compileProfile] at htarget
    exact htarget
  · intro h who replacement hconsidered
    have hsource := h who (adequacy.backtranslateStrategy who replacement)
    rw [euPreference_apply] at hsource
    rw [adequacy.expectedUtility_deviation profile who replacement hconsidered,
      adequacy.expectedUtility_compileProfile]
    exact hsource

/-- The certificate is exactly strong enough to preserve and reflect Nash at
compiled profiles.  The unrestricted instance of
`isNashAgainst_compileProfile_iff`. -/
theorem isNash_compileProfile_iff
    (adequacy : DeviationAdequacy source target)
    (profile : Profile source.form.sig) :
    IsNash target.form (euPreference target.utility)
        (adequacy.compileProfile profile) ↔
      IsNash source.form (euPreference source.utility) profile := by
  rw [← isNashAgainst_true_iff]
  exact adequacy.isNashAgainst_compileProfile_iff profile

end DeviationAdequacyOn

namespace DeviationAdequacy

/-- Exact unrestricted deviation certificates compose. A target replacement
is translated through both passes while the other players remain compiled. -/
def trans {Player : Type*} [DecidableEq Player]
    {first second third : UtilityGame Player}
    (left : DeviationAdequacy first second) (right : DeviationAdequacy second third) :
    DeviationAdequacy first third where
  compileStrategy who strategy := right.compileStrategy who (left.compileStrategy who strategy)
  backtranslateStrategy who strategy :=
    left.backtranslateStrategy who (right.backtranslateStrategy who strategy)
  decodeOutcome := left.decodeOutcome ∘ right.decodeOutcome
  utility_eq := by rw [right.utility_eq, left.utility_eq]; rfl
  compiled_considered _ _ := trivial
  honest_law profile := by
    rw [← FinDist.map_comp, right.honest_law, left.honest_law]
  deviation_law profile who replacement _ := by
    rw [← FinDist.map_comp, right.deviation_law _ _ _ trivial,
      left.deviation_law _ _ _ trivial]

end DeviationAdequacy

end Vegas.Runtime
