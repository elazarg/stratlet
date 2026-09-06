/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.DeviationAdequacy

/-!
# Same-strategy runtime adequacy

A runtime implements a game on an unchanged strategy surface when, for every
source strategy profile, decoding its finite trace law gives exactly the game's
outcome law. This is suitable only after gradual lowering has discharged every
new scheduler, observation, timing, and adversarial choice. It is not a secure
compilation criterion for a pass that introduces new target strategies.
-/

noncomputable section

namespace Vegas.Runtime

open GameTheory
open GameTheory.Math.Probability

universe uPlayer uStrategy uOutcome uTrace

/-- A profile-indexed runtime trace law with an exact semantic decoder. -/
structure Implementation {Player : Type uPlayer}
    (G : GameForm.{uPlayer, uStrategy, uOutcome} Player) where
  Trace : Type uTrace
  run : Profile G.sig → FinDist Trace
  outcome : Trace → G.sig.Outcome
  law_eq : ∀ profile, (run profile).map outcome = G.play profile

namespace Implementation

variable {Player : Type uPlayer}
variable {G : GameForm.{uPlayer, uStrategy, uOutcome} Player}
variable (runtime : Implementation.{uPlayer, uStrategy, uOutcome, uTrace} G)

/-- The runtime viewed as a game form over its concrete traces. -/
@[reducible]
def form : GameForm Player where
  sig := G.sig.mapOutcome runtime.Trace
  play := runtime.run

/-- Semantic utility pulled back to concrete runtime traces. -/
def utility (valuation : G.sig.Outcome → Player → ℝ)
    (trace : runtime.Trace) (who : Player) : ℝ :=
  valuation (runtime.outcome trace) who

/-- The utility game exposed by the concrete trace runner. -/
def game (valuation : G.sig.Outcome → Player → ℝ) : UtilityGame Player where
  form := runtime.form
  utility := runtime.utility valuation

/-- Exact adequacy over an unchanged strategy carrier supplies unilateral
deviation adequacy automatically: every target replacement is already a source
replacement. -/
def simulation [DecidableEq Player] :
    OutcomeSimulationOn G runtime.form (fun _ _ => True) where
  compileStrategy := fun _ strategy => strategy
  backtranslateStrategy := fun _ strategy => strategy
  decodeOutcome := runtime.outcome
  honest_law := runtime.law_eq
  compiled_considered := fun _ _ => trivial
  deviation_law := fun profile who replacement _ =>
    runtime.law_eq (Profile.update profile who replacement)

/-- Any valuation can be attached after the utility-free implementation proof. -/
def deviationAdequacy [DecidableEq Player] (valuation : G.sig.Outcome → Player → ℝ) :
    DeviationAdequacy ⟨G, valuation⟩ (runtime.game valuation) :=
  runtime.simulation.withUtility valuation

/-- Exact decoded trace laws preserve expected utility for every profile. -/
theorem expectedUtility_eq (valuation : G.sig.Outcome → Player → ℝ)
    (profile : Profile G.sig) (who : Player) :
    expectedUtility valuation who (G.play profile) =
      expectedUtility (runtime.utility valuation) who (runtime.run profile) := by
  rw [← runtime.law_eq profile, expectedUtility_map]
  rfl

/-- Consequently the runtime and specification have exactly the same
Nash profiles. The proof covers unilateral deviations because `law_eq` ranges
over every profile, including every updated one. -/
theorem isNash_iff [DecidableEq Player] (valuation : G.sig.Outcome → Player → ℝ)
    (profile : Profile G.sig) :
    IsNash G (euPreference valuation) profile ↔
      IsNash runtime.form (euPreference (runtime.utility valuation)) profile :=
  ((runtime.deviationAdequacy valuation).isNash_compileProfile_iff profile).symm

end Implementation

end Vegas.Runtime
