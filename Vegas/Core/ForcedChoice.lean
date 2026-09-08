/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Strategy

/-! # Publicly determined source choices

A guarded commitment can sometimes be executed without selecting an action
from its owner's policy. This certificate supplies two public expressions:
when the first is true, the second is the unique legal action. The proof must
hold for every environment, including hidden values and unreachable inputs.

The resulting law uses the existing written-order source denotation and keeps
the commitment and its continuation. It does not erase observations, authorize
another principal to send an authenticated message, or prove that a runtime
will execute the step. Those are obligations of the consuming compiler pass.
-/

namespace Vegas

open GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
variable {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}

/-- Public expressions identify a region where a source guard admits exactly
one value. Both the region and its value can be evaluated without private
state; the characterization itself is checked against the full source view. -/
structure PublicForcedChoice
    (guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool) where
  enabled : L.Expr (erasePubVCtx Γ) L.bool
  value : L.Expr (erasePubVCtx Γ) b
  characterizes : ∀ env : VEnv L Γ,
    L.toBool (L.eval enabled env.eraseSampleEnv) = true →
      ∀ chosen : L.Val b,
        evalGuard guard chosen ((env.toView who).eraseEnv) = true ↔
          chosen = L.eval value env.eraseSampleEnv

namespace PublicForcedChoice

/-- The certified action satisfies the original source guard. -/
theorem legal (forced : PublicForcedChoice guard) (env : VEnv L Γ)
    (henabled : L.toBool (L.eval forced.enabled env.eraseSampleEnv) = true) :
    evalGuard guard (L.eval forced.value env.eraseSampleEnv)
      ((env.toView who).eraseEnv) = true :=
  (forced.characterizes env henabled _).mpr rfl

/-- Every legal action, not only a recommended action, is the public value. -/
theorem unique (forced : PublicForcedChoice guard) (env : VEnv L Γ)
    (henabled : L.toBool (L.eval forced.enabled env.eraseSampleEnv) = true)
    (chosen : {v : L.Val b // evalGuard guard v ((env.toView who).eraseEnv) = true}) :
    chosen.1 = L.eval forced.value env.eraseSampleEnv :=
  (forced.characterizes env henabled chosen.1).mp chosen.2

/-- The enable test and value use only the public environment. -/
theorem public_determined (forced : PublicForcedChoice guard)
    (left right : VEnv L Γ) (hpublic : left.eraseSampleEnv = right.eraseSampleEnv) :
    L.toBool (L.eval forced.enabled left.eraseSampleEnv) =
        L.toBool (L.eval forced.enabled right.eraseSampleEnv) ∧
      L.eval forced.value left.eraseSampleEnv = L.eval forced.value right.eraseSampleEnv := by
  rw [hpublic]
  exact ⟨rfl, rfl⟩

/-- Arbitrary randomized source choices collapse to the certified value. -/
theorem law (forced : PublicForcedChoice guard) (env : VEnv L Γ)
    (henabled : L.toBool (L.eval forced.enabled env.eraseSampleEnv) = true)
    (choices : FinDist
      {v : L.Val b // evalGuard guard v ((env.toView who).eraseEnv) = true}) :
    choices = FinDist.pure
      ⟨L.eval forced.value env.eraseSampleEnv, forced.legal env henabled⟩ := by
  let : Subsingleton
      {v : L.Val b // evalGuard guard v ((env.toView who).eraseEnv) = true} :=
    ⟨fun left right => Subtype.ext
      ((forced.unique env henabled left).trans (forced.unique env henabled right).symm)⟩
  exact FinDist.eq_pure_of_subsingleton _ _

/-- Selecting the public value preserves the full terminal environment law
for every source profile, with the original continuation policies unchanged. -/
theorem denoteSource_commit (forced : PublicForcedChoice guard)
    (tail : VegasCore P L ((x, .sealed who b) :: Γ))
    (profile : SourceBehavioralProfile (.commit x who guard tail))
    (env : VEnv L Γ)
    (henabled : L.toBool (L.eval forced.enabled env.eraseSampleEnv) = true) :
    denoteSource (.commit x who guard tail) profile env =
      denoteSource tail profile.afterCommit
        (env.cons (L.eval forced.value env.eraseSampleEnv)) := by
  rw [Vegas.denoteSource_commit,
    forced.law env henabled (profile who (.here guard tail) ((env.toView who).eraseEnv)),
    FinDist.pure_bind]

/-- The policy-independent selection is an actual source transition, not a
new outcome inserted by a decoder. -/
theorem source_step (forced : PublicForcedChoice guard)
    (tail : VegasCore P L ((x, .sealed who b) :: Γ)) (env : VEnv L Γ)
    (henabled : L.toBool (L.eval forced.enabled env.eraseSampleEnv) = true) :
    SmallStep ⟨Γ, env, .commit x who guard tail⟩
      ⟨(x, .sealed who b) :: Γ,
        env.cons (L.eval forced.value env.eraseSampleEnv), tail⟩ :=
  .commit guard tail _ (forced.legal env henabled)

end PublicForcedChoice

end Vegas
