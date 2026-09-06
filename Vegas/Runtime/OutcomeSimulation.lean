/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Core.Utility

/-! # Utility-independent outcome simulation

The certificate relates game forms, not preferences. Outcomes may be terminal
states, public traces, or economic allocations. The decoder specifies exactly
which target distinctions the source retains. No utility of an adversary is
needed to transport a bound against that adversary's strategies.
-/

noncomputable section

namespace Vegas.Runtime

open GameTheory GameTheory.Math.Probability

universe uPlayer uSourceStrategy uSourceOutcome uTargetStrategy uTargetOutcome

/-- Exact decoded laws, including unilateral replacements at compiled profiles.
The considered class must include every compiled source strategy. -/
structure OutcomeSimulationOn
    {Player : Type uPlayer} [DecidableEq Player]
    (source : GameForm.{uPlayer, uSourceStrategy, uSourceOutcome} Player)
    (target : GameForm.{uPlayer, uTargetStrategy, uTargetOutcome} Player)
    (Considered : (who : Player) → target.sig.Strategy who → Prop) where
  compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who
  backtranslateStrategy : (who : Player) → target.sig.Strategy who → source.sig.Strategy who
  decodeOutcome : target.sig.Outcome → source.sig.Outcome
  honest_law : ∀ profile,
    (target.play (fun who => compileStrategy who (profile who))).map decodeOutcome =
      source.play profile
  compiled_considered : ∀ who strategy, Considered who (compileStrategy who strategy)
  deviation_law : ∀ profile who replacement, Considered who replacement →
    (target.play (Profile.update
      (fun player => compileStrategy player (profile player)) who replacement)).map
        decodeOutcome = source.play
          (Profile.update profile who (backtranslateStrategy who replacement))

namespace OutcomeSimulationOn

variable {Player : Type uPlayer} [DecidableEq Player]
variable {source : GameForm.{uPlayer, uSourceStrategy, uSourceOutcome} Player}
variable {target : GameForm.{uPlayer, uTargetStrategy, uTargetOutcome} Player}
variable {Considered : (who : Player) → target.sig.Strategy who → Prop}
variable (simulation : OutcomeSimulationOn source target Considered)

def compileProfile (profile : Profile source.sig) : Profile target.sig :=
  fun who => simulation.compileStrategy who (profile who)

/-- Every source observable, not just the default payout, has the same
expectation at a compiled profile. -/
theorem expect_compile (profile : Profile source.sig) (value : source.sig.Outcome → ℝ) :
    (target.play (simulation.compileProfile profile)).expect
      (fun outcome => value (simulation.decodeOutcome outcome)) =
        (source.play profile).expect value := by
  rw [← FinDist.expect_map]
  exact congrArg (fun law : FinDist source.sig.Outcome => law.expect value)
    (simulation.honest_law profile)

/-- The observable may value a different player from the deviator. -/
theorem expect_deviation (profile : Profile source.sig) (who : Player)
    (replacement : target.sig.Strategy who) (hconsidered : Considered who replacement)
    (value : source.sig.Outcome → ℝ) :
    (target.play (Profile.update (simulation.compileProfile profile) who replacement)).expect
      (fun outcome => value (simulation.decodeOutcome outcome)) =
        (source.play (Profile.update profile who
          (simulation.backtranslateStrategy who replacement))).expect value := by
  rw [← FinDist.expect_map]
  exact congrArg (fun law : FinDist source.sig.Outcome => law.expect value)
    (simulation.deviation_law profile who replacement hconsidered)

/-- A lower bound against every source replacement survives every considered
target replacement. No hypothesis constrains the deviator's preferences. All
other players remain at the specified compiled profile. -/
theorem guarantee (profile : Profile source.sig) (deviator : Player)
    (value : source.sig.Outcome → ℝ) (bound : ℝ)
    (hbound : ∀ replacement : source.sig.Strategy deviator,
      bound ≤ (source.play (Profile.update profile deviator replacement)).expect value)
    (replacement : target.sig.Strategy deviator)
    (hconsidered : Considered deviator replacement) :
    bound ≤ (target.play
      (Profile.update (simulation.compileProfile profile) deviator replacement)).expect
        (fun outcome => value (simulation.decodeOutcome outcome)) := by
  rw [simulation.expect_deviation profile deviator replacement hconsidered value]
  exact hbound _

end OutcomeSimulationOn

/-- Stronger than unilateral simulation: with designated honest coordinates
fixed, an arbitrary target opponent context is a mixture of source contexts
with those same coordinates fixed. This is an obligation, not an assertion
that every Vegas runtime satisfies it. Correlated adversaries are allowed. -/
structure HonestContextSimulation
    {Player : Type uPlayer}
    (source : GameForm.{uPlayer, uSourceStrategy, uSourceOutcome} Player)
    (target : GameForm.{uPlayer, uTargetStrategy, uTargetOutcome} Player)
    (Honest : Player → Prop) where
  compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who
  decodeOutcome : target.sig.Outcome → source.sig.Outcome
  context_law : ∀ (profile : Profile source.sig) (context : Profile target.sig),
    (∀ who, Honest who → context who = compileStrategy who (profile who)) →
    ∃ contexts : FinDist (Profile source.sig),
      (∀ alternative ∈ contexts.support, ∀ who, Honest who → alternative who = profile who) ∧
      (target.play context).map decodeOutcome = contexts.bind source.play

/-- Protection against an entire opponent context is independent of every
opponent's utility, including utilities on low-level traces. -/
theorem HonestContextSimulation.guarantee
    {Player : Type uPlayer}
    {source : GameForm.{uPlayer, uSourceStrategy, uSourceOutcome} Player}
    {target : GameForm.{uPlayer, uTargetStrategy, uTargetOutcome} Player}
    {Honest : Player → Prop}
    (simulation : HonestContextSimulation source target Honest)
    (profile : Profile source.sig) (value : source.sig.Outcome → ℝ) (bound : ℝ)
    (hbound : ∀ alternative : Profile source.sig,
      (∀ who, Honest who → alternative who = profile who) →
        bound ≤ (source.play alternative).expect value)
    (context : Profile target.sig)
    (hcontext : ∀ who, Honest who →
      context who = simulation.compileStrategy who (profile who)) :
    bound ≤ (target.play context).expect
      (fun outcome => value (simulation.decodeOutcome outcome)) := by
  obtain ⟨contexts, hfixed, hlaw⟩ := simulation.context_law profile context hcontext
  rw [← FinDist.expect_map, hlaw, FinDist.expect_bind]
  calc
    bound = contexts.expect (fun _ => bound) := (FinDist.expect_const _ _).symm
    _ ≤ _ := FinDist.expect_mono fun alternative hmem => hbound alternative (hfixed _ hmem)

end Vegas.Runtime
