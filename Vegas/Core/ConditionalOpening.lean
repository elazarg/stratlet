/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.SmallStep

/-! # Certificates for optional openings in existing core syntax

These certificates interpret an ordinary guarded commitment as either declining
to open an earlier sealed binding or publishing that binding's value. They do
not add a source constructor, execute a player's action, or give an arbitrary
semantic encoding a backend representation.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr} {Γ : VCtx P L}
variable {copyName : VarId} {who : P} {copyTy : L.Ty}
variable {guard : L.Expr ((copyName, copyTy) :: eraseVCtx (viewVCtx who Γ)) L.bool}

/-- Evidence that the legal values of an ordinary commitment encode only an
explicit decline or the value of one named, same-owner sealed binding. A
decline is required to be legal in every environment, preventing a vacuous
certificate for an empty guard. -/
structure ConditionalOpening
    (guard : L.Expr ((copyName, copyTy) :: eraseVCtx (viewVCtx who Γ)) L.bool) where
  secretTy : L.Ty
  source : VarId
  binding : VHasVar Γ source (.sealed who secretTy)
  encoding : L.Val copyTy ≃ Option (L.Val secretTy)
  sound : ∀ env : VEnv L Γ, ∀ chosen,
    evalGuard guard chosen ((env.toView who).eraseEnv) = true →
      encoding chosen = none ∨ encoding chosen = some (env.get binding)
  decline_legal : ∀ env : VEnv L Γ,
    evalGuard guard (encoding.symm none) ((env.toView who).eraseEnv) = true

namespace ConditionalOpening

/-- An exact description of the two authorized encodings supplies a
`ConditionalOpening`; the `none` branch in particular proves nonvacuity. -/
def of_characterizes (secretTy : L.Ty) (source : VarId)
    (binding : VHasVar Γ source (.sealed who secretTy))
    (encoding : L.Val copyTy ≃ Option (L.Val secretTy))
    (characterizes : ∀ env : VEnv L Γ, ∀ chosen,
      evalGuard guard chosen ((env.toView who).eraseEnv) = true ↔
        encoding chosen = none ∨ encoding chosen = some (env.get binding)) :
    ConditionalOpening guard where
  secretTy := secretTy
  source := source
  binding := binding
  encoding := encoding
  sound env chosen hlegal := (characterizes env chosen).mp hlegal
  decline_legal env := (characterizes env (encoding.symm none)).mpr
    (Or.inl (encoding.apply_symm_apply none))

/-- The distinguished declining value really encodes `none`. -/
@[simp] theorem encode_decline (opening : ConditionalOpening guard) :
    opening.encoding (opening.encoding.symm none) = none :=
  opening.encoding.apply_symm_apply none

/-- There is only one value encoding decline. -/
theorem eq_decline_of_encode_eq_none (opening : ConditionalOpening guard)
    (chosen : L.Val copyTy) (hdecline : opening.encoding chosen = none) :
    chosen = opening.encoding.symm none := by
  apply opening.encoding.injective
  rw [hdecline, opening.encode_decline]

/-- A legal non-declining value encodes the named sealed binding's value. -/
theorem encode_eq_some_binding_of_legal (opening : ConditionalOpening guard)
    (env : VEnv L Γ) (chosen : L.Val copyTy)
    (hlegal : evalGuard guard chosen ((env.toView who).eraseEnv) = true)
    (hnotDecline : opening.encoding chosen ≠ none) :
    opening.encoding chosen = some (env.get opening.binding) := by
  rcases opening.sound env chosen hlegal with hdecline | hsuccess
  · exact False.elim (hnotDecline hdecline)
  · exact hsuccess

/-- Decoding a successful legal value recovers the actual named binding. -/
theorem successful_value_eq_binding (opening : ConditionalOpening guard)
    (env : VEnv L Γ) (chosen : L.Val copyTy) (value : L.Val opening.secretTy)
    (hlegal : evalGuard guard chosen ((env.toView who).eraseEnv) = true)
    (hsuccess : opening.encoding chosen = some value) :
    value = env.get opening.binding := by
  have hnotDecline : opening.encoding chosen ≠ none := by simp [hsuccess]
  rw [opening.encode_eq_some_binding_of_legal env chosen hlegal hnotDecline] at hsuccess
  exact (Option.some.inj hsuccess).symm

/-- Every legal value follows the existing adjacent commit/reveal source
steps, publishing exactly the chosen encoded value. -/
theorem commit_reveal_steps (_opening : ConditionalOpening guard)
    (publicName : VarId)
    (tail : VegasCore P L
      ((publicName, .pub copyTy) :: (copyName, .sealed who copyTy) :: Γ))
    (env : VEnv L Γ) (chosen : L.Val copyTy)
    (hlegal : evalGuard guard chosen ((env.toView who).eraseEnv) = true) :
    SmallStep.Star
      ⟨Γ, env, .commit copyName who guard
        (.reveal publicName who copyName .here tail)⟩
      ⟨(publicName, .pub copyTy) :: (copyName, .sealed who copyTy) :: Γ,
        (env.cons chosen).cons chosen, tail⟩ := by
  exact (SmallStep.Star.single (SmallStep.commit guard _ chosen hlegal)).trans
    (SmallStep.Star.single (SmallStep.reveal .here tail))

/-- Adding the sealed copy and its public alias does not change the original
sealed binding selected by the certificate. -/
@[simp] theorem original_binding_after_commit_reveal
    (opening : ConditionalOpening guard) (publicName : VarId)
    (env : VEnv L Γ) (chosen : L.Val copyTy) :
    ((env.cons chosen).cons chosen).get
      (VHasVar.there (VHasVar.there opening.binding) :
        VHasVar
          ((publicName, .pub copyTy) :: (copyName, .sealed who copyTy) :: Γ)
          opening.source (.sealed who opening.secretTy)) =
      env.get opening.binding := by
  simp

end ConditionalOpening

end Vegas
