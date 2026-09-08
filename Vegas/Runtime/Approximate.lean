/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.DeviationAdequacy
import GameTheory.Core.Approximate

/-! # Exact preservation of approximate equilibrium budgets -/

noncomputable section

namespace Vegas.Runtime.DeviationAdequacyOn

open GameTheory

/-- An unrestricted exact deviation certificate preserves and reflects
approximate Nash with the same error budget. -/
theorem isεNash_compileProfile_iff {Player : Type*} [DecidableEq Player]
    {source target : UtilityGame Player} (adequacy : DeviationAdequacy source target)
    (profile : Profile source.form.sig) (ε : ℝ) :
    IsεNash target.form target.utility ε (adequacy.compileProfile profile) ↔
      IsεNash source.form source.utility ε profile := by
  rw [isεNash_iff, isεNash_iff]
  constructor
  · intro h who replacement
    have ht := h who (adequacy.compileStrategy who replacement)
    rw [adequacy.compileProfile_update, adequacy.expectedUtility_compileProfile,
      adequacy.expectedUtility_compileProfile] at ht
    exact ht
  · intro h who replacement
    rw [adequacy.expectedUtility_deviation _ _ _ trivial,
      adequacy.expectedUtility_compileProfile]
    exact h who (adequacy.backtranslateStrategy who replacement)

end Vegas.Runtime.DeviationAdequacyOn
