/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationProfileContinuation
import VegasTests.ConditionalSourceCoupling

/-! # Dispatch after actual binding and disclosure inclusion

The generated source profile remains installed throughout the shared execution.
Exact source-prefix refinement, rather than a replacement policy or an exposed
compiler cursor, supplies the completion facts used by structural dispatch.
-/

noncomputable section

namespace VegasTests.ApplicationProfileContinuation

open Vegas Vegas.ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability
open VegasTests.ConditionalApplicationImage VegasTests.ConditionalSourceCoupling

private def terminalPlan : ApplicationPlan (pending := ∅)
    (CommitmentAccounting.ret (payoffs := []) rfl) source.fresh.2.2.2 finalBuild :=
  .ret rfl _ _

private theorem terminal_continuation (profile : SourceBehavioralProfile source.prog) :
    ApplicationPlan.ProfileContinuation applicationPlan profile terminalPlan
      profile.afterCommit.afterCommit.afterReveal := by
  exact .conditional (.binding .refl)

/-- After either legal voluntary disclosure, every player sees the same
installed profile dispatch to the terminal source continuation. The theorem
uses the actual generated inclusions and works at any clock and local history. -/
theorem published_profile_waits (profile : SourceBehavioralProfile source.prog)
    (secret : Bool) (chosen : Option Bool) (clock : Nat)
    (hchoice : chosen = none ∨ chosen = some secret) (player : Fin 2)
    (history : List (image 10).application.PlayerEntry) :
    applicationPlan.liftProfile (fun _ => 10) profile player history
        (MessageApplication.State.observe (image 10).application
          (published secret chosen clock) player) = FinDist.pure .wait := by
  obtain ⟨current, _, hrefines⟩ := published_source_successor secret chosen clock hchoice
  exact (terminal_continuation profile).liftProfileIn_eq_of_refines
    (image 10) (fun _ => 10) current (published secret chosen clock) hrefines player history

end VegasTests.ApplicationProfileContinuation

/-- info: 'VegasTests.ApplicationProfileContinuation.published_profile_waits' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationProfileContinuation.published_profile_waits
