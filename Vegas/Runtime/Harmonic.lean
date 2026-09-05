/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Protocol.Information

/-! # Distribution-valued invariants of behavioral execution -/

noncomputable section

namespace Vegas.Runtime

open GameTheory.Protocol GameTheory.Math.Probability

/-- A distribution-valued invariant preserved by every legal transition is
preserved by every finite behavioral run. The invariant region may exclude
an initial strategic phase. No restriction is imposed on later policies. -/
theorem runBehavioralFrom_harmonic
    {Player : Type*} [Fintype Player] {E : ExecutionProtocol Player}
    (M : InformationModel E) {Outcome : Type*}
    (region : E.State → Prop) (kernel : E.State → FinDist Outcome)
    (closed : ∀ state command, region state →
      ∀ next ∈ (E.step state command).support, region next)
    (harmonic : ∀ state command, region state →
      (E.step state command).bind kernel = kernel state)
    (profile : ∀ who, M.BehavioralPolicy who) (fuel : Nat)
    (start : E.History) (hstart : region start.state) :
    (M.runBehavioralFrom profile fuel start).bind (fun history => kernel history.state) =
      kernel start.state := by
  induction fuel generalizing start with
  | zero =>
      change (FinDist.pure start).bind _ = _
      exact FinDist.pure_bind _ _
  | succ fuel ih =>
      by_cases hterm : E.terminal start.state
      · rw [M.runBehavioralFrom_of_terminal profile _ hterm, FinDist.pure_bind]
      · rw [M.runBehavioralFrom_succ_of_not_terminal profile fuel hterm, FinDist.bind_bind]
        calc
          _ = (M.behavioralJoint profile start.trace hterm).bind
              (fun _ => kernel start.state) := by
            apply FinDist.bind_congr
            intro command _
            rw [FinDist.bind_bindOnSupport]
            calc
              _ = (E.step start.state command).bind kernel := by
                apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
                intro next hnext
                exact ih (start.extend command.2 hnext) (closed _ _ hstart _ hnext)
              _ = kernel start.state := harmonic _ _ hstart
          _ = kernel start.state := FinDist.bind_const _ _

end Vegas.Runtime
